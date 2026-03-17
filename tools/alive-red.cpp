// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include "cache/cache.h"
#include "ir/function.h"
#include "ir/globals.h"
#include "ir/state.h"
#include "ir/value.h"
#include "llvm_util/llvm2alive.h"
#include "llvm_util/utils.h"
#include "smt/expr.h"
#include "smt/smt.h"
#include "smt/solver.h"
#include "tools/transform.h"
#include "util/compiler.h"
#include "util/config.h"
#include "util/dataflow.h"
#include "util/parallel.h"
#include "util/stopwatch.h"
#include "util/symexec.h"
#include "util/version.h"

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/TargetParser/Triple.h"

#include <algorithm>
#include <chrono>
#include <format>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <signal.h>
#include <sstream>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

using namespace IR;
using namespace std;
using namespace llvm_util;
using namespace util;
using namespace smt;
using namespace tools;

#define LLVM_ARGS_PREFIX ""
#define ARGS_SRC_TGT
#define ARGS_REFINEMENT
#include "llvm_util/cmd_args_list.h"

namespace {

llvm::cl::opt<string> opt_file(llvm::cl::Positional, llvm::cl::Required,
                               llvm::cl::value_desc("filename"));

llvm::cl::opt<bool> opt_parse_only("parse-only",
  llvm::cl::desc("Parse and convert IR only, skip analysis"),
  llvm::cl::init(false), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<string> opt_parallel("parallel",
  llvm::cl::desc("Parallelization mode. Accepted values:"
                  " unrestricted (no throttling)"
                  ", fifo (use Alive2's job server)"
                  ", null (developer mode)"),
  llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<int> opt_max_subprocesses("max-subprocesses",
  llvm::cl::desc("Maximum children at one time (default=128)"),
  llvm::cl::init(128), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<long> opt_subprocess_timeout("subprocess-timeout",
  llvm::cl::desc("Maximum time, in seconds, that a child process "
                 "will be allowed to execute (default=infinite)"),
  llvm::cl::init(-1), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<bool> opt_type_stats("type-stats",
  llvm::cl::desc("Print instruction type distribution and exit (no SMT)"),
  llvm::cl::init(false), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<bool> opt_dom_stats("dom-stats",
  llvm::cl::desc("Print dominator tree branching stats and exit (no SMT)"),
  llvm::cl::init(false), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<bool> opt_intra_parallel("intra-parallel",
  llvm::cl::desc("Enable intra-function dom-tree parallelism"),
  llvm::cl::init(false), llvm::cl::cat(alive_cmdargs));

llvm::cl::opt<int> opt_max_subtree_procs("max-subtree-processes",
  llvm::cl::desc("Max child processes per function (default=32)"),
  llvm::cl::init(32), llvm::cl::cat(alive_cmdargs));
} // namespace

unique_ptr<Cache> cache;
static unique_ptr<parallel> parallelMgr;

static string read_all_fd(int fd) {
  string result;
  char buf[4096];
  ssize_t n;
  while ((n = read(fd, buf, sizeof(buf))) > 0)
    result.append(buf, n);
  return result;
}
static stringstream parent_ss;
static stringstream collected_output;

static void sigalarm_handler(int) {
  parallelMgr->finishChild(/*is_timeout=*/true);
  _Exit(0);
}

struct refinement_pair {
  static constexpr const char *StatusStr[] = {"SUCCESS", "",        "INVALID",
                                              "SKIP",    "TIMEOUT", "ERROR"};
  static constexpr const char *ALIVE2_TAG = "ALIVE2";

  string fn_name;
  string src_name;
  string tgt_name;
  bool is_universal;
  Result::answer status;
  string reason;
  bool stale = false;

  void write(llvm::json::OStream &J) const {
    J.object([&] {
      J.attribute("tool", ALIVE2_TAG);
      J.attribute("fn", fn_name);
      J.attribute("src", src_name);
      J.attribute("tgt", tgt_name);
      J.attribute("univ", is_universal);
      J.attribute("status", StatusStr[status]);
      J.attribute("reason", reason);
    });
  }
};

static Result::answer statusFromString(const string &s) {
  for (int i = 0; i <= Result::ERROR; ++i) {
    if (s == refinement_pair::StatusStr[i])
      return static_cast<Result::answer>(i);
  }
  return Result::ERROR;
}

static string serialize(const vector<refinement_pair> &pairs) {
  string buf;
  llvm::raw_string_ostream rso(buf);
  llvm::json::OStream J(rso);
  J.array([&] {
    for (auto &p : pairs) {
      J.object([&] {
        J.attribute("fn", p.fn_name);
        J.attribute("src", p.src_name);
        J.attribute("tgt", p.tgt_name);
        J.attribute("univ", p.is_universal);
        J.attribute("status", refinement_pair::StatusStr[p.status]);
        J.attribute("reason", p.reason);
      });
    }
  });
  return buf;
}

static vector<refinement_pair> deserialize(const string &s) {
  vector<refinement_pair> pairs;
  auto parsed = llvm::json::parse(s);
  if (!parsed) {
    llvm::consumeError(parsed.takeError());
    return pairs;
  }
  auto *arr = parsed->getAsArray();
  if (!arr)
    return pairs;
  for (auto &elem : *arr) {
    auto *obj = elem.getAsObject();
    if (!obj)
      continue;
    refinement_pair p{"", "", "", false, Result::ERROR, "", false};
    if (auto v = obj->getString("fn"))
      p.fn_name = v->str();
    if (auto v = obj->getString("src"))
      p.src_name = v->str();
    if (auto v = obj->getString("tgt"))
      p.tgt_name = v->str();
    if (auto v = obj->getBoolean("univ"))
      p.is_universal = *v;
    if (auto v = obj->getString("status"))
      p.status = statusFromString(v->str());
    if (auto v = obj->getString("reason"))
      p.reason = v->str();
    pairs.push_back(std::move(p));
  }
  return pairs;
}

using CandidateMap =
    std::vector<std::map<const Type *, std::vector<const Value *>>>;

expr get_axioms(State &st) {
  return st.getAxioms()();
}

std::pair<expr, expr> get_preconditions(const State &st,
                                        const std::set<smt::expr> &qvars) {
  expr pre_src = st.getPre()();
  expr pre_src_exists = pre_src;
  vector<pair<expr, expr>> repls;
  auto vars_pre = pre_src.vars();
  for (auto &v : qvars) {
    if (vars_pre.count(v))
      repls.emplace_back(v, expr::mkFreshVar("#exists", v));
  }
  if (!repls.empty())
    pre_src_exists = pre_src_exists.subst(repls);

  expr pre_src_forall = pre_src_exists.eq(pre_src) ? true : pre_src;
  expr pre = pre_src_exists && st.getFnPre();
  return {pre, pre_src_forall};
}

class FunctionAnalyzer {
  std::unordered_map<std::string, const Instr *> name_to_inst;
  unsigned unroll_cnt;

  static bool should_skip_instr(const Instr &i) {
    return i.getType().isVoid() || i.isTerminator() ||
          //  dynamic_cast<const Alloc *>(&i) ||
           (i.getName().starts_with("%__constexpr"));
  }

  bool is_unrolled_copy(const string &name) const {
    auto pos = name.rfind('#');
    if (pos == string::npos || pos == 0)
      return false;
    auto suffix = string_view(name).substr(pos + 1);
    if (suffix.empty())
      return false;
    for (char c : suffix)
      if (!isdigit(c))
        return false;
    return stoul(string(suffix)) >= 2;
  }

  // Returns true if something interesting happend, i.e., everything but SAT
  // (UNSAT (refines), TO, INVALID, ...)
  bool check_refinement_inst(const Transform &t, const Value *a,
                             const Value *b, State &st, const Type &type,
                             Result &r) {
    auto *ap = st.at(*a);
    // A is never defined.
    if (!ap)
      return false;

    // B is never defined but A is.
    auto *bp = st.at(*b);
    if (!bp)
      return true;

    auto &val_a = ap->val;
    auto &val_b = bp->val;
    auto dom_a = ap->domain();

    if (val_a.non_poison.isFalse())
      return false;

    auto &uvars = ap->undef_vars;
    auto qvars = st.getQuantVars();
    qvars.insert(ap->undef_vars.begin(), ap->undef_vars.end());
    auto &src_nondet_vars = st.getNondetVars();
    qvars.insert(src_nondet_vars.begin(), src_nondet_vars.end());
    auto &fn_qvars = st.getFnQuantVars();
    qvars.insert(fn_qvars.begin(), fn_qvars.end());

    expr axioms_expr = get_axioms(st);
    auto [pre, pre_src_forall] = get_preconditions(st, qvars);

    Solver s;
    auto [poison_cnstr, value_cnstr] = type.refines(st, st, val_a, val_b);
    expr refines = dom_a && (!value_cnstr || !poison_cnstr);
    expr e = axioms_expr && preprocess(t, qvars, uvars,
                                       pre && pre_src_forall.implies(refines));
    s.add(std::move(e));
    r = s.check(std::format("{} >= {}", a->getName(), b->getName()).c_str());
    if (r.isUnsat()) {
      // Only verify outer loop iterations; inner/nested loop copies
      // (e.g. #1#2) are not checked.
      string base_a(a->getName());
      string base_b(b->getName());
      auto saved = unroll_cnt;
      unroll_cnt = 0;
      for (unsigned iter = 2; iter <= saved; ++iter) {
        string suffix = "#" + to_string(iter);
        auto it_a = name_to_inst.find(base_a + suffix);
        if (it_a == name_to_inst.end()) {
          unroll_cnt = saved;
          return true;
        }
        auto it_b = name_to_inst.find(base_b + suffix);
        const Value *iter_b = (it_b != name_to_inst.end()) ? it_b->second : b;
        Result r_iter;
        if (!check_refinement_inst(t, it_a->second, iter_b, st, type, r_iter)) {
          unroll_cnt = saved;
          return false;
        }
      }
      unroll_cnt = saved;
      return true;
    } else if (r.isError()) {
      cerr << r.getReason() << "\n";
    }

    return false;
  }

  std::optional<expr> check_constant(const Transform &t, const Value *a,
                                     State &st, const Type &type, Result &r) {
    if (type.isAggregateType() || type.isStructType() || type.isPtrType())
      return nullopt;

    auto *ap = st.at(*a);
    // A is never defined - refinement is trivially true
    if (!ap)
      return nullopt;

    auto &val_a = ap->val;
    auto dom_a = ap->domain();

    if (val_a.non_poison.isFalse())
      return false;

    auto &uvars = ap->undef_vars;
    auto qvars = st.getQuantVars();
    // TODO
    qvars.insert(ap->undef_vars.begin(), ap->undef_vars.end());
    auto &src_nondet_vars = st.getNondetVars();
    qvars.insert(src_nondet_vars.begin(), src_nondet_vars.end());

    expr axioms_expr = get_axioms(st);
    auto [pre, pre_src_forall] = get_preconditions(st, qvars);

    auto k = expr::mkFreshVar("k", val_a.value);
    expr eqk = val_a.value == k;
    // expr constant = val_a.non_poison.implies(eqk);
    expr constant = eqk;
    {
    Solver s;

    expr e_const =
        dom_a && axioms_expr &&
        preprocess(t, qvars, uvars, pre && pre_src_forall.implies(constant));
    s.add(std::move(e_const));
    r = s.check("constant");
    }
    if (r.isSat()) {
      const Model &model = r.getModel()/* TODO: complete_model */ */;
      expr candidate_const = model[k];
      Solver s;
      s.add(val_a.value != candidate_const);
      auto check = s.check("check const");
      if (check.isUnsat()) {
        // Only verify outer loop iterations; inner/nested loop copies
        // (e.g. #1#2) are not checked.
        string base_a(a->getName());
        auto saved = unroll_cnt;
        unroll_cnt = 0;
        for (unsigned iter = 2; iter <= saved; ++iter) {
          string suffix = "#" + to_string(iter);
          auto it_a = name_to_inst.find(base_a + suffix);
          if (it_a == name_to_inst.end())
            break;
          Result r_iter;
          auto k_iter = check_constant(t, it_a->second, st, type, r_iter);
          if (!k_iter || !model[k].eq(*k_iter)) {
            unroll_cnt = saved;
            return nullopt;
          }
        }
        unroll_cnt = saved;
        return model[k];
      }
    }
    // No model : UB?
    return nullopt;
  }

public:
  FunctionAnalyzer(unsigned unroll_cnt) : unroll_cnt(unroll_cnt) {}

  std::vector<refinement_pair>
  analyze(llvm::Function &F, llvm::TargetLibraryInfoWrapperPass &TLI) {
    std::vector<refinement_pair> pairs;

  cerr << "[alive-red]   llvm2alive...\n";
  auto f  = llvm2alive(F, TLI.getTLI(F), true);
  auto f2 = llvm2alive(F, TLI.getTLI(F), false);
  if (!f || !f2) { cerr << "[alive-red]   llvm2alive FAILED\n"; return pairs; }

  if (opt_parse_only) return pairs;

  cerr << "[alive-red]   preprocessing...\n";
  Transform t;
  t.src = std::move(*f);
  t.tgt = std::move(*f2);
  t.preprocess();
  t.src.topSort();

  name_to_inst.clear();
  for (auto const &i : t.src.instrs()) {
    name_to_inst[i.getName()] = &i;
  }

  calculateAndInitConstants(t);
  State::resetGlobals();

  cerr << "[alive-red]   sym_exec (" << t.src.getNumBBs() << " BBs)...\n";
  auto state = make_unique<State>(t.src, true);
  sym_exec(*state);
  state->cleanup();
  cerr << "[alive-red]   sym_exec done, building candidates...\n";

  CFG cfg(t.src);
  DomTree dt(t.src, cfg);

  size_t num_blocks = t.src.getNumBBs();

  // "Block" 0 contains the function arguments.
  size_t next_id = 1;
  std::vector<llvm::BitVector> pred_map(num_blocks + 1,
                                        llvm::BitVector(num_blocks + 1));
  std::unordered_map<const BasicBlock *, int> block_to_id;
  std::vector<const BasicBlock *> id_to_block;

  id_to_block.push_back(nullptr);
  for (auto &bb : t.src.getBBs()) {
    pred_map[next_id].set(0);
    pred_map[next_id].set(next_id);
    block_to_id[bb] = next_id++;
    id_to_block.push_back(bb);
  }

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto [src, tgt, _] : cfg) {
      auto &dst = pred_map[block_to_id[&tgt]];
      auto prev = dst;
      dst |= pred_map[block_to_id[&src]];
      if (dst != prev)
        changed = true;
    }
  }

  CandidateMap candidate_bbs(num_blocks + 1);
  for (auto &arg : t.src.getInputs()) {
    candidate_bbs[0][&arg.getType()].push_back(&arg);
  }
  for (auto *gv : t.src.getGlobalVars()) {
    candidate_bbs[0][&gv->getType()].push_back(gv);
  }

  if (opt_type_stats) {
    map<string, unsigned> type_counts;
    unsigned total = 0;
    for (auto &bb : t.src.getBBs()) {
      for (auto &i : bb->instrs()) {
        if (should_skip_instr(i))
          continue;
        if (is_unrolled_copy(i.getName()))
          continue;
        type_counts[i.getType().toString()]++;
        total++;
      }
    }
    cerr << "Function: " << t.src.getName() << "\n";
    cerr << "  Total eligible instructions: " << total << "\n";
    cerr << "  Distinct types: " << type_counts.size() << "\n";
    // Sort by count descending
    vector<pair<string, unsigned>> sorted(type_counts.begin(),
                                          type_counts.end());
    sort(sorted.begin(), sorted.end(),
         [](auto &a, auto &b) { return a.second > b.second; });
    for (auto &[ty, cnt] : sorted) {
      cerr << "    " << ty << ": " << cnt
           << " (" << (cnt * 100 / total) << "%)\n";
    }
    return pairs;
  }

  if (opt_dom_stats) {
    // Build dominator tree children map
    map<const BasicBlock*, vector<const BasicBlock*>> dom_children;
    const BasicBlock *root = t.src.getBBs().front();
    for (auto *bb : t.src.getBBs()) {
      auto *idom = dt.getIDominator(*bb);
      if (idom && idom != bb)
        dom_children[idom].push_back(bb);
    }

    // Count eligible instructions per BB
    map<const BasicBlock*, unsigned> bb_instr_count;
    unsigned total_instrs = 0;
    for (auto *bb : t.src.getBBs()) {
      unsigned cnt = 0;
      for (auto &i : bb->instrs()) {
        if (should_skip_instr(i)) continue;
        if (is_unrolled_copy(i.getName())) continue;
        cnt++;
      }
      bb_instr_count[bb] = cnt;
      total_instrs += cnt;
    }

    // Compute subtree sizes (instructions in subtree rooted at bb)
    map<const BasicBlock*, unsigned> subtree_size;
    // Post-order traversal
    function<unsigned(const BasicBlock*)> compute_subtree;
    compute_subtree = [&](const BasicBlock *bb) -> unsigned {
      unsigned sz = bb_instr_count[bb];
      auto it = dom_children.find(bb);
      if (it != dom_children.end())
        for (auto *child : it->second)
          sz += compute_subtree(child);
      subtree_size[bb] = sz;
      return sz;
    };
    if (root)
      compute_subtree(root);

    // Find all fork points (nodes with >1 children) and their parallelism
    struct ForkPoint {
      string name;
      unsigned num_children;
      unsigned own_instrs;     // sequential prefix (this BB)
      vector<unsigned> child_subtree_sizes;
    };
    vector<ForkPoint> forks;
    unsigned max_parallel_tasks = 0;

    for (auto &[bb, children] : dom_children) {
      if (children.size() > 1) {
        ForkPoint fp;
        fp.name = bb->getName();
        fp.num_children = children.size();
        fp.own_instrs = bb_instr_count[bb];
        for (auto *c : children)
          fp.child_subtree_sizes.push_back(subtree_size[c]);
        sort(fp.child_subtree_sizes.rbegin(), fp.child_subtree_sizes.rend());
        forks.push_back(fp);
        max_parallel_tasks += children.size();
      }
    }

    sort(forks.begin(), forks.end(),
         [](auto &a, auto &b) { return a.num_children > b.num_children; });

    cerr << "Function: " << t.src.getName() << "\n";
    cerr << "  Root: " << (root ? root->getName() : "(none)") << "\n";
    cerr << "  Dom children map entries: " << dom_children.size() << "\n";
    // Count blocks with null idom
    unsigned null_idom = 0;
    for (auto *bb : t.src.getBBs())
      if (!dt.getIDominator(*bb)) null_idom++;
    cerr << "  Blocks with null idom: " << null_idom << "\n";
    cerr << "  Total BBs: " << t.src.getNumBBs() << "\n";
    cerr << "  Total eligible instructions: " << total_instrs << "\n";
    cerr << "  Fork points (dom tree nodes with >1 child): "
         << forks.size() << "\n";
    cerr << "  Total parallel subtrees: " << max_parallel_tasks << "\n";

    // Show top fork points
    unsigned shown = 0;
    for (auto &fp : forks) {
      if (shown++ >= 20) break;
      cerr << "  " << fp.name << ": " << fp.num_children
           << " children, " << fp.own_instrs << " own instrs, subtrees=[";
      for (unsigned i = 0; i < fp.child_subtree_sizes.size() && i < 10; i++) {
        if (i) cerr << ",";
        cerr << fp.child_subtree_sizes[i];
      }
      if (fp.child_subtree_sizes.size() > 10)
        cerr << ",...(" << fp.child_subtree_sizes.size() << " total)";
      cerr << "]\n";
    }

    // Simulate parallelism: at the root fork, what's the max/min subtree?
    if (!forks.empty()) {
      auto &top = forks[0];
      cerr << "\n  Biggest fork: " << top.name << " with "
           << top.num_children << " children\n";
      cerr << "    Largest subtree:  " << top.child_subtree_sizes.front()
           << " instrs (" << (top.child_subtree_sizes.front() * 100 / total_instrs)
           << "% of total)\n";
      cerr << "    Smallest subtree: " << top.child_subtree_sizes.back()
           << " instrs\n";
    }

    // Show where instructions actually live in the dom tree
    // Count instructions on the "spine" (blocks on the longest dom chain)
    // vs branches
    // Top BBs by instruction count
    vector<pair<string, unsigned>> bb_by_count;
    for (auto &[bb, cnt] : bb_instr_count)
      if (cnt > 0)
        bb_by_count.emplace_back(bb->getName(), cnt);
    sort(bb_by_count.begin(), bb_by_count.end(),
         [](auto &a, auto &b) { return a.second > b.second; });

    cerr << "\n  Top BBs by eligible instruction count:\n";
    unsigned shown2 = 0;
    unsigned cumulative = 0;
    for (auto &[name, cnt] : bb_by_count) {
      cumulative += cnt;
      if (shown2++ < 20)
        cerr << "    " << name << ": " << cnt << " instrs (cumul "
             << (cumulative * 100 / total_instrs) << "%)\n";
    }
    cerr << "  Total BBs with instructions: " << bb_by_count.size()
         << " out of " << t.src.getNumBBs() << "\n";

    // Dom tree depth distribution
    map<unsigned, unsigned> depth_instr_count;
    function<void(const BasicBlock*, unsigned)> count_depth;
    count_depth = [&](const BasicBlock *bb, unsigned depth) {
      depth_instr_count[depth] += bb_instr_count[bb];
      auto it = dom_children.find(bb);
      if (it != dom_children.end())
        for (auto *child : it->second)
          count_depth(child, depth + 1);
    };
    if (root)
      count_depth(root, 0);

    cerr << "\n  Instructions by dom tree depth:\n";
    unsigned max_depth = 0;
    for (auto &[d, cnt] : depth_instr_count) {
      if (cnt > 0)
        max_depth = max(max_depth, d);
    }
    for (unsigned d = 0; d <= min(max_depth, 30u); d++) {
      auto it = depth_instr_count.find(d);
      unsigned cnt = (it != depth_instr_count.end()) ? it->second : 0;
      if (cnt > 0)
        cerr << "    depth " << d << ": " << cnt << " instrs\n";
    }
    cerr << "  Max dom tree depth: " << max_depth << "\n";

    // Combined analysis: for the biggest fork, show type breakdown per subtree
    // Find the fork with most children
    const BasicBlock *best_fork = nullptr;
    unsigned best_nchildren = 0;
    for (auto &[bb, children] : dom_children) {
      if (children.size() > best_nchildren) {
        best_nchildren = children.size();
        best_fork = bb;
      }
    }

    if (best_fork) {
      cerr << "\n  Combined dom+type analysis for biggest fork ("
           << best_fork->getName() << ", " << best_nchildren << " children):\n";

      // For each subtree, collect type counts
      function<void(const BasicBlock*, map<string,unsigned>&)> collect_types;
      collect_types = [&](const BasicBlock *bb, map<string,unsigned> &types) {
        for (auto &i : bb->instrs()) {
          if (should_skip_instr(i)) continue;
          if (is_unrolled_copy(i.getName())) continue;
          types[i.getType().toString()]++;
        }
        auto it = dom_children.find(bb);
        if (it != dom_children.end())
          for (auto *child : it->second)
            collect_types(child, types);
      };

      // Show top 10 largest subtrees with their type breakdown
      auto &children = dom_children[best_fork];
      vector<pair<unsigned, const BasicBlock*>> sorted_children;
      for (auto *c : children)
        sorted_children.emplace_back(subtree_size[c], c);
      sort(sorted_children.rbegin(), sorted_children.rend());

      unsigned shown3 = 0;
      for (auto &[sz, child] : sorted_children) {
        if (shown3++ >= 5 || sz == 0) break;
        map<string, unsigned> types;
        collect_types(child, types);
        cerr << "    subtree " << child->getName() << " (" << sz << " instrs): ";
        vector<pair<unsigned, string>> type_list;
        for (auto &[ty, cnt] : types)
          type_list.emplace_back(cnt, ty);
        sort(type_list.rbegin(), type_list.rend());
        for (auto &[cnt, ty] : type_list)
          cerr << ty << "=" << cnt << " ";
        cerr << "\n";
      }

      // What's the effective parallelism with dom+type?
      // For each subtree, the work is split by types, so effective task count
      // = sum of distinct types per subtree
      unsigned total_tasks = 0;
      unsigned max_task_size = 0;
      for (auto *c : children) {
        map<string, unsigned> types;
        collect_types(c, types);
        total_tasks += types.size();
        for (auto &[ty, cnt] : types)
          max_task_size = max(max_task_size, cnt);
      }
      cerr << "\n  Combined parallelism (dom subtrees x types):\n";
      cerr << "    Total tasks: " << total_tasks << "\n";
      cerr << "    Largest single task: " << max_task_size
           << " instrs (" << (max_task_size * 100 / total_instrs) << "% of total)\n";
      cerr << "    Theoretical speedup: ~"
           << total_instrs / max(max_task_size, 1u) << "x\n";
    }

    return pairs;
  }

  // --- process_block: extracted main loop body ---
  auto process_block = [&](const BasicBlock *bb) {
    unsigned bb_id = block_to_id[bb];
    llvm::BitVector &reachable = pred_map[bb_id];
    for (auto &i : bb->instrs()) {
      if (should_skip_instr(i))
        continue;
      if (is_unrolled_copy(i.getName()))
        continue;
      cerr << "[alive-red]     instr: " << i.getName() << " (" << i.getType().toString() << ")\n";
#if 0 // SKIP constant check for speed testing
      Result r_const;
      cerr << "[alive-red]       check_constant..." << std::flush;
      auto t0 = std::chrono::steady_clock::now();
      if (auto k =
              check_constant(t, &i, *state, i.getType(), r_const)) {
        if (i.getType().isFloatType()) {
          auto &fpty = *(i.getType().getAsFloatType());
          auto f = fpty.getFloat(*k);
          if (f.isFPNormal().isTrue())
            k = f.float2Real();
        }

        auto t1 = std::chrono::steady_clock::now();
        cerr << " CONST " << std::chrono::duration_cast<std::chrono::milliseconds>(t1-t0).count() << "ms\n";
        pairs.emplace_back(t.src.getName(), i.getName().substr(1),
                         i.getType().toString() + " " + string(k->numeral_string()),
                         true, r_const.getAnswer(), r_const.getReason());
        continue;
      }
      {
        auto t1 = std::chrono::steady_clock::now();
        cerr << " " << std::chrono::duration_cast<std::chrono::milliseconds>(t1-t0).count() << "ms\n";
      }
#endif
      cerr << "[alive-red]       check_refinement candidates..." << std::flush;
      auto t0 = std::chrono::steady_clock::now();
      bool found = false;
      for (int reachbb_id : reachable.set_bits()) {
        auto &TypeMap = candidate_bbs[reachbb_id];
        auto It = TypeMap.find(&i.getType());
        if (It == TypeMap.end())
          continue;

        auto &candidates = It->second;
        auto *cand_bb = id_to_block[reachbb_id];
        // Universal refinement
        for (auto *tgt : candidates) {
          Result r;
          if (!cand_bb || dt.dominates(cand_bb, bb)) {
            if (check_refinement_inst(t, &i, tgt, *state, i.getType(), r)) {
              found = true;
              pairs.emplace_back(t.src.getName(), i.getName().substr(1), tgt->getName().substr(1),
                                  true, r.getAnswer(), r.getReason());
              break;
            }
          }
        }
      }

      {
        auto t1 = std::chrono::steady_clock::now();
        cerr << " " << std::chrono::duration_cast<std::chrono::milliseconds>(t1-t0).count() << "ms"
             << (found ? " FOUND" : "") << "\n";
      }
      if (!found) {
        candidate_bbs[bb_id][&i.getType()].push_back(&i);
      }
    }
  };

  // --- Dom-tree analysis: find best fork point ---
  map<const BasicBlock*, vector<const BasicBlock*>> dom_children;
  for (auto *bb : t.src.getBBs()) {
    auto *idom = dt.getIDominator(*bb);
    if (idom && idom != bb)
      dom_children[idom].push_back(bb);
  }

  const BasicBlock *fork_point = nullptr;
  unsigned max_children = 0;
  if (opt_intra_parallel) {
    for (auto &[bb, children] : dom_children) {
      if (children.size() > max_children) {
        max_children = children.size();
        fork_point = bb;
      }
    }
    // Not worth forking for tiny fan-outs
    if (max_children < 4)
      fork_point = nullptr;
  }

  if (!fork_point) {
    // Sequential: process all blocks
    unsigned bb_idx = 0;
    for (auto *bb : t.src.getBBs()) {
      cerr << "[alive-red]   block " << (++bb_idx) << "/" << t.src.getNumBBs()
           << " (" << bb->getName() << ")\n";
      process_block(bb);
    }
    cerr << "[alive-red]   done, " << pairs.size() << " pairs found\n";
    return pairs;
  }

  // --- Partition blocks into prefix + subtrees ---
  set<const BasicBlock*> all_subtree_blocks;
  map<const BasicBlock*, vector<const BasicBlock*>> subtree_block_lists;

  for (auto *child : dom_children[fork_point]) {
    vector<const BasicBlock*> blocks;
    function<void(const BasicBlock*)> dfs = [&](const BasicBlock *b) {
      blocks.push_back(b);
      all_subtree_blocks.insert(b);
      auto it = dom_children.find(b);
      if (it != dom_children.end())
        for (auto *c : it->second)
          dfs(c);
    };
    dfs(child);
    subtree_block_lists[child] = std::move(blocks);
  }

  // Prefix = all blocks NOT in any subtree, in topo order
  vector<const BasicBlock*> prefix_blocks;
  for (auto *bb : t.src.getBBs())
    if (!all_subtree_blocks.count(bb))
      prefix_blocks.push_back(bb);

  // --- Process prefix sequentially ---
  for (auto *bb : prefix_blocks)
    process_block(bb);

  // --- Fork per subtree ---
  struct ChildInfo { pid_t pid; int read_fd; };
  vector<ChildInfo> children;
  int active = 0;

  // Helper: reap one finished child and collect its result
  auto reap_one = [&]() {
    int status;
    pid_t done = waitpid(-1, &status, 0);
    if (done <= 0) return;
    for (auto it = children.begin(); it != children.end(); ++it) {
      if (it->pid == done) {
        string data = read_all_fd(it->read_fd);
        close(it->read_fd);
        auto child_pairs = deserialize(data);
        pairs.insert(pairs.end(), child_pairs.begin(), child_pairs.end());
        children.erase(it);
        active--;
        return;
      }
    }
  };

  // Sort subtrees by size descending (schedule big ones first)
  vector<const BasicBlock*> sorted_subtree_roots;
  for (auto *child : dom_children[fork_point])
    sorted_subtree_roots.push_back(child);
  sort(sorted_subtree_roots.begin(), sorted_subtree_roots.end(),
       [&](auto *a, auto *b) {
         return subtree_block_lists[a].size() > subtree_block_lists[b].size();
       });

  // Precompute topo-ordered blocks per subtree
  map<const BasicBlock*, vector<const BasicBlock*>> subtree_topo;
  for (auto *root : sorted_subtree_roots) {
    set<const BasicBlock*> my_set(subtree_block_lists[root].begin(),
                                  subtree_block_lists[root].end());
    vector<const BasicBlock*> topo;
    for (auto *bb : t.src.getBBs())
      if (my_set.count(bb))
        topo.push_back(bb);
    subtree_topo[root] = std::move(topo);
  }

  for (auto *subtree_root : sorted_subtree_roots) {
    auto &topo = subtree_topo[subtree_root];
    if (topo.empty()) continue;

    // Throttle
    while (active >= opt_max_subtree_procs)
      reap_one();

    int pipefd[2];
    if (pipe(pipefd) < 0) {
      perror("pipe");
      // Fall back to sequential for remaining subtrees
      for (auto *bb : topo)
        process_block(bb);
      continue;
    }

    fflush(nullptr);
    pid_t pid = fork();

    if (pid < 0) {
      perror("fork");
      close(pipefd[0]);
      close(pipefd[1]);
      // Fall back to sequential
      for (auto *bb : topo)
        process_block(bb);
      continue;
    }

    if (pid == 0) {
      // CHILD — DO NOT call smt_init.reset()
      close(pipefd[0]);

      vector<refinement_pair> child_pairs;
      // Swap pairs so process_block writes to child_pairs
      pairs.clear();
      for (auto *bb : topo)
        process_block(bb);

      string data = serialize(pairs);
      const char *p = data.c_str();
      size_t remaining = data.size();
      while (remaining > 0) {
        ssize_t n = write(pipefd[1], p, remaining);
        if (n <= 0) break;
        p += n;
        remaining -= n;
      }
      close(pipefd[1]);
      _Exit(0);
    }

    // PARENT
    close(pipefd[1]);
    children.push_back({pid, pipefd[0]});
    active++;
  }

  // Collect remaining children
  while (active > 0)
    reap_one();

  return pairs;
  }
};

int main(int argc, char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::InitLLVM X(argc, argv);
  llvm::EnableDebugBuffering = true;
  llvm::LLVMContext Context;

  llvm::cl::HideUnrelatedOptions(alive_cmdargs);
  llvm::cl::ParseCommandLineOptions(argc, argv, "Semantic GVN Analysis Tool\n");

  cerr << "[alive-red] Parsing input file: " << opt_file.c_str() << "\n";
  auto M = openInputFile(Context, opt_file);
  if (!M.get()) {
    cerr << "Could not read bitcode from '" << opt_file << "'\n";
    return -1;
  }
  cerr << "[alive-red] Module loaded successfully\n";

#define ARGS_MODULE_VAR M
#include "llvm_util/cmd_args_def.h"

  // Initialize parallel manager
  if (opt_parallel == "unrestricted") {
    parallelMgr = make_unique<unrestricted>(opt_max_subprocesses, parent_ss,
                                            collected_output);
  } else if (opt_parallel == "fifo") {
    parallelMgr = make_unique<fifo>(opt_max_subprocesses, parent_ss,
                                    collected_output);
  } else if (opt_parallel == "null") {
    parallelMgr = make_unique<null>(opt_max_subprocesses, parent_ss,
                                    collected_output);
  } else if (!opt_parallel.empty()) {
    cerr << "Unknown parallelization mode: " << opt_parallel << '\n';
    return -1;
  }

  if (parallelMgr) {
    if (!parallelMgr->init()) {
      cerr << "WARNING: Parallel execution unavailable\n";
      parallelMgr.reset();
    }
  }

  cerr << "[alive-red] Verifying module...\n";
  if (llvm::verifyModule(*M.get(), &llvm::errs())) {
    cerr << "Source file is broken\n";
    return -1;
  }
  cerr << "[alive-red] Module verified OK\n";

  auto &DL = M.get()->getDataLayout();
  llvm::Triple targetTriple(M.get()->getTargetTriple());
  llvm::TargetLibraryInfoWrapperPass TLI(targetTriple);

  initializer llvm_util_init(cerr, DL);
  smt::smt_initializer smt_init;

  cerr << "[alive-red] Starting analysis (unroll=" << config::src_unroll_cnt << ")\n";
  FunctionAnalyzer analyzer(config::src_unroll_cnt);
  std::vector<refinement_pair> all_pairs;

  for (auto &F : *M) {
    if (F.isDeclaration())
      continue;
    cerr << "[alive-red] Processing function: " << F.getName().str() << "\n";

    if (parallelMgr) {
      auto [pid, osp, index] = parallelMgr->limitedFork();

      if (pid == -1) {
        perror("fork() failed");
        return -1;
      }

      if (pid != 0) {
        // Parent: leave placeholder for child output
        parent_ss << "include(" << index << ")\n";
        continue;
      }

      // Child process
      if (opt_subprocess_timeout != -1) {
        ENSURE(signal(SIGALRM, sigalarm_handler) == nullptr);
        alarm(opt_subprocess_timeout);
      }

      smt_init.reset();
      auto pairs = analyzer.analyze(F, TLI);

      string serialized = serialize(pairs);
      osp->write(serialized.c_str(), serialized.size());
      *osp << '\n';

      signal(SIGALRM, SIG_IGN);
      parallelMgr->finishChild(/*is_timeout=*/false);
      _Exit(0);
    }

    // Sequential mode
    auto pairs = analyzer.analyze(F, TLI);
    all_pairs.insert(all_pairs.end(), pairs.begin(), pairs.end());
  }

  // Parallel mode: collect results from children
  if (parallelMgr) {
    parallelMgr->finishParent();

    string collected = std::move(collected_output).str();
    istringstream iss(collected);
    string line;
    while (getline(iss, line)) {
      if (line.empty())
        continue;
      auto pairs = deserialize(line);
      all_pairs.insert(all_pairs.end(), pairs.begin(), pairs.end());
    }
  }

  // Output JSON
  if (!opt_outputfile.empty()) {
    std::error_code EC;
    llvm::raw_fd_ostream OS(opt_outputfile, EC);
    if (EC) {
      llvm::errs() << "Error opening output file: " << EC.message() << "\n";
      return -1;
    }

    llvm::json::OStream J(OS, 2);
    J.array([&] {
      for (const auto &P : all_pairs) {
        if (!P.stale)
          P.write(J);
      }
    });
  } else {
    for (auto &P : all_pairs) {
      llvm::outs() << "Pair: " << P.src_name << " -> " << P.tgt_name
                   << " (Universal: " << P.is_universal << ")\n";
    }
  }

  return 0;
}