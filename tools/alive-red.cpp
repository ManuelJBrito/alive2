// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

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
#include <format>
#include <fstream>
#include <iostream>
#include <map>
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
} // namespace

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
           dynamic_cast<const Alloc *>(&i) ||
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
    qvars.insert(ap->undef_vars.begin(), ap->undef_vars.end());
    auto &src_nondet_vars = st.getNondetVars();
    qvars.insert(src_nondet_vars.begin(), src_nondet_vars.end());

    expr axioms_expr = get_axioms(st);
    auto [pre, pre_src_forall] = get_preconditions(st, qvars);

    auto k = expr::mkVar("k", type.getDummyValue(true).value);
    expr eqk = val_a.value == k;
    expr constant = val_a.non_poison.implies(eqk);
    Solver s;

    expr e_const =
        dom_a && axioms_expr &&
        preprocess(t, qvars, uvars, pre && pre_src_forall.implies(constant));
    s.add(std::move(e_const));
    r = s.check("constant");
    if (r.isSat()) {
      const Model &model = r.getModel();
      s.add(!(k == model[k]));
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

  auto f  = llvm2alive(F, TLI.getTLI(F), true);
  auto f2 = llvm2alive(F, TLI.getTLI(F), false);
  if (!f || !f2) return pairs;

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

  auto state = make_unique<State>(t.src, true);
  sym_exec(*state);
  state->cleanup();

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

  for (auto &bb : t.src.getBBs()) {
    unsigned bb_id = block_to_id[bb];
    llvm::BitVector &reachable = pred_map[bb_id];
    for (auto &i : bb->instrs()) {
      if (should_skip_instr(i))
        continue;
      if (is_unrolled_copy(i.getName()))
        continue;
      Result r_const;
      if (auto k =
              check_constant(t, &i, *state, i.getType(), r_const)) {
        if (i.getType().isFloatType()) {
          auto &fpty = *(i.getType().getAsFloatType());
          auto f = fpty.getFloat(*k);
          if (f.isFPNormal().isTrue())
            k = f.float2Real();
        }

        pairs.push_back({t.src.getName(), i.getName(),
                         string(k->numeral_string()), true, r_const.getAnswer(),
                         r_const.getReason()});
        continue;
      }
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
              pairs.emplace_back(t.src.getName(), i.getName(), tgt->getName(),
                                  true, r.getAnswer(), r.getReason());
              break;
            }
          }
        }
      }

      if (!found) {
        candidate_bbs[bb_id][&i.getType()].push_back(&i);
      }
    }
  }
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

  auto M = openInputFile(Context, opt_file);
  if (!M.get()) {
    cerr << "Could not read bitcode from '" << opt_file << "'\n";
    return -1;
  }

#define ARGS_MODULE_VAR M
#include "llvm_util/cmd_args_def.h"

  if (llvm::verifyModule(*M.get(), &llvm::errs())) {
    cerr << "Source file is broken\n";
    return -1;
  }

  auto &DL = M.get()->getDataLayout();
  llvm::Triple targetTriple(M.get()->getTargetTriple());
  llvm::TargetLibraryInfoWrapperPass TLI(targetTriple);

  initializer llvm_util_init(cerr, DL);
  smt::smt_initializer smt_init;

  FunctionAnalyzer analyzer(config::src_unroll_cnt);
  std::vector<refinement_pair> all_pairs;
  for (auto &F : *M) {
    if (F.isDeclaration())
      continue;

    auto pairs = analyzer.analyze(F, TLI);
    all_pairs.insert(all_pairs.end(), pairs.begin(), pairs.end());
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