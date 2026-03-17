// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.
//
// alive-red LLVM pass plugin: runs semantic redundancy analysis after GVN.
// For each function in a predetermined hot-function list, it:
//   1. Converts LLVM IR to Alive2 IR
//   2. Symbolically executes and checks all refinement candidates
//   3. Optionally eliminates redundant instructions
//   4. Writes discovered pairs to a JSON output file

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
#include "util/config.h"
#include "util/dataflow.h"
#include "util/symexec.h"

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Config/llvm-config.h"
#if LLVM_VERSION_MAJOR >= 23
#include "llvm/Plugins/PassPlugin.h"
#else
#include "llvm/Passes/PassPlugin.h"
#endif
#include "llvm/Support/JSON.h"
#include "llvm/Transforms/Utils/Local.h"

#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace IR;
using namespace std;
using namespace llvm_util;
using namespace smt;
using namespace tools;

namespace {

// Configuration via environment variables (cl::opt doesn't work reliably with
// -fpass-plugin because the plugin is loaded after command-line parsing).
//   ALIVE_RED_FUNCTIONS  — file with function names to analyze (one per line)
//   ALIVE_RED_OUTPUT     — JSON output file for discovered pairs
//   ALIVE_RED_ELIMINATE  — "0" to disable elimination (default: enabled)
//
// For opt (where cl::opt works), -mllvm flags are also supported.
llvm::cl::opt<string> OptFunctionsFile("alive-red-functions",
    llvm::cl::desc("File with function names to analyze (one per line)"),
    llvm::cl::init(""));

llvm::cl::opt<string> OptOutputFile("alive-red-output",
    llvm::cl::desc("JSON output file for discovered pairs"),
    llvm::cl::init(""));

llvm::cl::opt<bool> OptEliminate("alive-red-eliminate",
    llvm::cl::desc("Perform redundancy elimination (default: true)"),
    llvm::cl::init(true));

static string getConfigFunctionsFile() {
  if (!OptFunctionsFile.empty()) return OptFunctionsFile;
  if (const char *env = getenv("ALIVE_RED_FUNCTIONS")) return env;
  return "";
}
static string getConfigOutputFile() {
  if (!OptOutputFile.empty()) return OptOutputFile;
  if (const char *env = getenv("ALIVE_RED_OUTPUT")) return env;
  return "";
}
static bool getConfigEliminate() {
  if (const char *env = getenv("ALIVE_RED_ELIMINATE"))
    return string(env) != "0";
  return OptEliminate;
}
static unsigned getConfigUnroll() {
  if (const char *env = getenv("ALIVE_RED_UNROLL"))
    return (unsigned)atoi(env);
  return 2; // default
}

// ---------------------------------------------------------------------------
// refinement_pair — records a discovered semantic refinement
// ---------------------------------------------------------------------------
struct refinement_pair {
  string fn_name;
  string src_name;
  string tgt_name;
  bool is_universal;
  string status;
  string reason;

  void write(llvm::json::OStream &J) const {
    J.object([&] {
      J.attribute("tool", "ALIVE2");
      J.attribute("fn", fn_name);
      J.attribute("src", src_name);
      J.attribute("tgt", tgt_name);
      J.attribute("univ", is_universal);
      J.attribute("status", status);
      J.attribute("reason", reason);
    });
  }
};

// ---------------------------------------------------------------------------
// FunctionAnalyzer — adapted from tools/alive-red.cpp (sequential only)
// ---------------------------------------------------------------------------
class FunctionAnalyzer {
  unordered_map<string, const Instr *> name_to_inst;
  unsigned unroll_cnt;

  static bool should_skip_instr(const Instr &i) {
    return i.getType().isVoid() || i.isTerminator() ||
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

  expr get_axioms(State &st) {
    return st.getAxioms()();
  }

  pair<expr, expr> get_preconditions(const State &st,
                                     const set<smt::expr> &qvars) {
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

  bool check_refinement_inst(const Transform &t, const Value *a,
                             const Value *b, State &st, const Type &type,
                             Result &r) {
    auto *ap = st.at(*a);
    if (!ap)
      return false;

    auto *bp = st.at(*b);
    if (!bp)
      return true;

    auto &val_a = ap->val;
    auto &val_b = bp->val;
    auto dom_a = ap->domain();

    if (val_a.non_poison.isFalse())
      return false;

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
    expr e = axioms_expr && preprocess(t, qvars, ap->undef_vars,
                                       pre && pre_src_forall.implies(refines));
    s.add(move(e));
    r = s.check(format("{} >= {}", a->getName(), b->getName()).c_str());
    if (r.isUnsat()) {
      // Verify across unrolled iterations
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
    }

    return false;
  }

public:
  FunctionAnalyzer(unsigned unroll_cnt) : unroll_cnt(unroll_cnt) {}

  vector<refinement_pair>
  analyze(llvm::Function &F, const llvm::TargetLibraryInfo &TLI) {
    vector<refinement_pair> pairs;

    auto f = llvm2alive(F, TLI, true);
    auto f2 = llvm2alive(F, TLI, false);
    if (!f || !f2) {
      llvm::errs() << "[alive-red-pass] llvm2alive failed for "
                    << F.getName() << "\n";
      return pairs;
    }

    Transform t;
    t.src = move(*f);
    t.tgt = move(*f2);
    t.preprocess();
    t.src.topSort();

    name_to_inst.clear();
    for (auto const &i : t.src.instrs())
      name_to_inst[i.getName()] = &i;

    calculateAndInitConstants(t);
    State::resetGlobals();

    auto state = make_unique<State>(t.src, true);
    util::sym_exec(*state);
    state->cleanup();

    CFG cfg(t.src);
    DomTree dt(t.src, cfg);

    size_t num_blocks = t.src.getNumBBs();

    using CandidateMap =
        vector<map<const Type *, vector<const Value *>>>;

    size_t next_id = 1;
    vector<llvm::BitVector> pred_map(num_blocks + 1,
                                     llvm::BitVector(num_blocks + 1));
    unordered_map<const BasicBlock *, int> block_to_id;
    vector<const BasicBlock *> id_to_block;

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
    for (auto &arg : t.src.getInputs())
      candidate_bbs[0][&arg.getType()].push_back(&arg);
    for (auto *gv : t.src.getGlobalVars())
      candidate_bbs[0][&gv->getType()].push_back(gv);

    // Process all blocks sequentially
    for (auto *bb : t.src.getBBs()) {
      unsigned bb_id = block_to_id[bb];
      llvm::BitVector &reachable = pred_map[bb_id];
      for (auto &i : bb->instrs()) {
        if (should_skip_instr(i))
          continue;
        if (is_unrolled_copy(i.getName()))
          continue;

        bool found = false;
        for (int reachbb_id : reachable.set_bits()) {
          auto &TypeMap = candidate_bbs[reachbb_id];
          auto It = TypeMap.find(&i.getType());
          if (It == TypeMap.end())
            continue;

          auto &candidates = It->second;
          auto *cand_bb = id_to_block[reachbb_id];
          for (auto *tgt : candidates) {
            Result r;
            if (!cand_bb || dt.dominates(cand_bb, bb)) {
              if (check_refinement_inst(t, &i, tgt, *state, i.getType(), r)) {
                found = true;
                pairs.emplace_back(
                    t.src.getName(), i.getName().substr(1),
                    tgt->getName().substr(1), true,
                    r.isUnsat() ? "SUCCESS" : "", r.getReason());
                break;
              }
            }
          }
          if (found)
            break;
        }
        if (!found)
          candidate_bbs[bb_id][&i.getType()].push_back(&i);
      }
    }

    return pairs;
  }
};

// ---------------------------------------------------------------------------
// AliveRedPass — LLVM Module Pass
// ---------------------------------------------------------------------------
struct AliveRedPass : llvm::PassInfoMixin<AliveRedPass> {
  static bool initialized;
  static set<string> hot_functions;
  static vector<refinement_pair> all_pairs;

  static void loadHotFunctions() {
    string fns_file = getConfigFunctionsFile();
    if (fns_file.empty())
      return;
    ifstream ifs(fns_file);
    if (!ifs) {
      llvm::errs() << "[alive-red-pass] cannot open functions file: "
                    << fns_file << "\n";
      return;
    }
    string line;
    while (getline(ifs, line)) {
      // Trim whitespace
      auto start = line.find_first_not_of(" \t\r\n");
      if (start == string::npos)
        continue;
      auto end = line.find_last_not_of(" \t\r\n");
      hot_functions.insert(line.substr(start, end - start + 1));
    }
    llvm::errs() << "[alive-red-pass] loaded " << hot_functions.size()
                 << " hot function names\n";
  }

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &AM) {
    if (!initialized) {
      loadHotFunctions();
      auto &DL = M.getDataLayout();
      static llvm_util::initializer llvm_util_init(cerr, DL);
      initialized = true;
    }

    // If no function list, analyze everything; otherwise filter
    bool filter = !hot_functions.empty();

    auto &FAM =
        AM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();

    smt::smt_initializer smt_init;
    util::config::src_unroll_cnt = getConfigUnroll();
    FunctionAnalyzer analyzer(util::config::src_unroll_cnt);

    bool Changed = false;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;
      if (filter && !hot_functions.count(F.getName().str()))
        continue;

      llvm::errs() << "[alive-red-pass] analyzing: " << F.getName() << "\n";

      auto &TLI = FAM.getResult<llvm::TargetLibraryAnalysis>(F);
      auto pairs = analyzer.analyze(F, TLI);

      llvm::errs() << "[alive-red-pass]   found " << pairs.size()
                    << " pairs\n";

      // Perform elimination
      if (getConfigEliminate() && !pairs.empty()) {
        // Build name → Value map
        llvm::StringMap<llvm::Value *> NameMap;
        for (auto &Arg : F.args()) {
          if (Arg.hasName())
            NameMap[Arg.getName()] = &Arg;
        }
        for (auto &BB : F) {
          for (auto &I : BB) {
            if (I.hasName())
              NameMap[I.getName()] = &I;
          }
        }

        auto &DT = FAM.getResult<llvm::DominatorTreeAnalysis>(F);

        unsigned eliminated = 0;
        for (auto &P : pairs) {
          if (P.status != "SUCCESS")
            continue;

          auto SrcIt = NameMap.find(P.src_name);
          if (SrcIt == NameMap.end())
            continue;
          auto *SrcI = llvm::dyn_cast<llvm::Instruction>(SrcIt->second);
          if (!SrcI)
            continue;

          // Resolve target
          llvm::Value *TgtV = nullptr;
          auto TgtIt = NameMap.find(P.tgt_name);
          if (TgtIt != NameMap.end()) {
            TgtV = TgtIt->second;
          } else {
            // Try constant parsing: "i32 42", "i1 true", etc.
            llvm::StringRef TgtName(P.tgt_name);
            auto [TypeStr, ValStr] = TgtName.split(' ');
            if (!ValStr.empty() && SrcI->getType()->isIntegerTy()) {
              llvm::APInt Val;
              if (!ValStr.getAsInteger(10, Val)) {
                unsigned BitWidth =
                    SrcI->getType()->getIntegerBitWidth();
                TgtV = llvm::ConstantInt::get(SrcI->getType(),
                                              Val.sextOrTrunc(BitWidth));
              }
            }
          }
          if (!TgtV || SrcI == TgtV)
            continue;
          if (SrcI->getType() != TgtV->getType())
            continue;

          // Dominance check
          if (auto *TgtI = llvm::dyn_cast<llvm::Instruction>(TgtV)) {
            if (!DT.dominates(TgtI, SrcI))
              continue;
          }

          SrcI->replaceAllUsesWith(TgtV);
          if (llvm::isInstructionTriviallyDead(SrcI))
            SrcI->eraseFromParent();
          ++eliminated;
          Changed = true;
        }

        if (eliminated > 0)
          llvm::errs() << "[alive-red-pass]   eliminated " << eliminated
                        << " instructions\n";
      }

      all_pairs.insert(all_pairs.end(), pairs.begin(), pairs.end());
    }

    // Write JSON output
    string out_file = getConfigOutputFile();
    if (!out_file.empty() && !all_pairs.empty()) {
      error_code EC;
      llvm::raw_fd_ostream OS(out_file, EC);
      if (EC) {
        llvm::errs() << "[alive-red-pass] error opening output file: "
                      << EC.message() << "\n";
      } else {
        llvm::json::OStream J(OS, 2);
        J.array([&] {
          for (const auto &P : all_pairs)
            P.write(J);
        });
      }
    }

    return Changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

bool AliveRedPass::initialized = false;
set<string> AliveRedPass::hot_functions;
vector<refinement_pair> AliveRedPass::all_pairs;

// Write JSON output at process exit (for function pass path where there's no
// single "end of module" point).
static void writeJsonAtExit() {
  string out_file = getConfigOutputFile();
  if (out_file.empty() || AliveRedPass::all_pairs.empty())
    return;
  error_code EC;
  llvm::raw_fd_ostream OS(out_file, EC);
  if (EC) {
    llvm::errs() << "[alive-red-pass] error opening output file: "
                  << EC.message() << "\n";
    return;
  }
  llvm::json::OStream J(OS, 2);
  J.array([&] {
    for (const auto &P : AliveRedPass::all_pairs)
      P.write(J);
  });
}

// Wrapper: function pass that delegates to the module-level AliveRedPass logic
// but runs per-function at the AfterGVN extension point.
struct AliveRedFunctionPass : llvm::PassInfoMixin<AliveRedFunctionPass> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &FAM) {
    if (!AliveRedPass::initialized) {
      AliveRedPass::loadHotFunctions();
      AliveRedPass::initialized = true;
      atexit(writeJsonAtExit);
      llvm::errs() << "[alive-red-pass] loaded "
                    << AliveRedPass::hot_functions.size()
                    << " hot function names\n";
    }

    if (AliveRedPass::hot_functions.empty())
      return llvm::PreservedAnalyses::all();
    if (!AliveRedPass::hot_functions.count(F.getName().str()))
      return llvm::PreservedAnalyses::all();

    // Initialize SMT/alive2 on first analyzed function
    static unique_ptr<smt::smt_initializer> smt_init;
    static unique_ptr<llvm_util::initializer> llvm_init;
    if (!smt_init) {
      smt_init = make_unique<smt::smt_initializer>();
      llvm_init = make_unique<llvm_util::initializer>(
          cerr, F.getParent()->getDataLayout());
      util::config::src_unroll_cnt = getConfigUnroll();
    }

    llvm::errs() << "[alive-red-pass] analyzing: " << F.getName() << "\n";

    FunctionAnalyzer analyzer(util::config::src_unroll_cnt);
    auto &TLI = FAM.getResult<llvm::TargetLibraryAnalysis>(F);
    auto pairs = analyzer.analyze(F, TLI);

    llvm::errs() << "[alive-red-pass]   found " << pairs.size()
                  << " pairs\n";

    bool Changed = false;
    if (getConfigEliminate() && !pairs.empty()) {
      llvm::StringMap<llvm::Value *> NameMap;
      for (auto &Arg : F.args())
        if (Arg.hasName())
          NameMap[Arg.getName()] = &Arg;
      for (auto &BB : F)
        for (auto &I : BB)
          if (I.hasName())
            NameMap[I.getName()] = &I;

      auto &DT = FAM.getResult<llvm::DominatorTreeAnalysis>(F);

      unsigned eliminated = 0;
      for (auto &P : pairs) {
        if (P.status != "SUCCESS") continue;
        auto SrcIt = NameMap.find(P.src_name);
        if (SrcIt == NameMap.end()) continue;
        auto *SrcI = llvm::dyn_cast<llvm::Instruction>(SrcIt->second);
        if (!SrcI) continue;

        llvm::Value *TgtV = nullptr;
        auto TgtIt = NameMap.find(P.tgt_name);
        if (TgtIt != NameMap.end()) {
          TgtV = TgtIt->second;
        } else {
          llvm::StringRef TgtName(P.tgt_name);
          auto [TypeStr, ValStr] = TgtName.split(' ');
          if (!ValStr.empty() && SrcI->getType()->isIntegerTy()) {
            llvm::APInt Val;
            if (!ValStr.getAsInteger(10, Val)) {
              unsigned BitWidth = SrcI->getType()->getIntegerBitWidth();
              TgtV = llvm::ConstantInt::get(SrcI->getType(),
                                            Val.sextOrTrunc(BitWidth));
            }
          }
        }
        if (!TgtV || SrcI == TgtV) continue;
        if (SrcI->getType() != TgtV->getType()) continue;

        if (auto *TgtI = llvm::dyn_cast<llvm::Instruction>(TgtV))
          if (!DT.dominates(TgtI, SrcI)) continue;

        SrcI->replaceAllUsesWith(TgtV);
        if (llvm::isInstructionTriviallyDead(SrcI))
          SrcI->eraseFromParent();
        ++eliminated;
        Changed = true;
      }

      if (eliminated > 0)
        llvm::errs() << "[alive-red-pass]   eliminated " << eliminated
                      << " instructions\n";
    }

    AliveRedPass::all_pairs.insert(AliveRedPass::all_pairs.end(),
                                   pairs.begin(), pairs.end());

    return Changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
};

} // anonymous namespace

// Plugin entry point
extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "alive-red-pass", "",
          [](llvm::PassBuilder &PB) {
            // For opt: -passes='alive-red'
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                  if (Name != "alive-red")
                    return false;
                  MPM.addPass(AliveRedPass());
                  return true;
                });
#ifdef ALIVE_RED_HAS_AFTER_GVN_EP
            // For clang: auto-register at AfterGVN extension point
            PB.registerAfterGVNEPCallback(
                [](llvm::FunctionPassManager &FPM,
                   llvm::OptimizationLevel Level) {
                  FPM.addPass(AliveRedFunctionPass());
                });
#endif
          }};
}
