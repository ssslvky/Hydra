#include <algorithm>
#include <string>
#include "/home/wzby/llvm-project/llvm/lib/Transforms/Hydra/Analyses/Fitness/Fitness.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstIterator.h"

#include <llvm/IR/LegacyPassManager.h>
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <llvm/Support/CommandLine.h>

using namespace llvm;
using namespace hydra;

char Fitness::ID = 0;

void Fitness::getAnalysisUsage(AnalysisUsage &Info) const {
  Info.addRequired<CallGraphWrapperPass>();
  Info.setPreservesAll();
}

// helper functions for runOnSCC:

static bool hasPointerArgs(const Function &F) {
  return std::any_of(F.arg_begin(), F.arg_end(), [](const Argument &arg) {
    return arg.getType()->isPointerTy();
  });
}

// currently not used...
//
//static bool hasNonConstPointerArgs(const Function &F) {
//  return std::any_of(F.arg_begin(), F.arg_end(), [](const Argument &arg) {
//    return arg.getType()->isPointerTy() && !arg.onlyReadsMemory() &&
//           !arg.hasByValAttr();
//  });
//}

static bool referencesGlobalVariables(const Function &F) {
  return std::any_of(inst_begin(F), inst_end(F), [](const Instruction &I) {
    return std::any_of(I.op_begin(), I.op_end(), [](const Use &U) {
      return isa<GlobalVariable>(U) || isa<GlobalAlias>(U);
    });
  });
}

bool Fitness::callsUnknownFunction(const CallGraphNode &CGN) const {
  dbgs() << "Fitness::callsUnknownFunction()\n";
  CGN.print(dbgs());
  return std::any_of(CGN.begin(), CGN.end(),
                     [this](const CallGraphNode::CallRecord &CR) {
    dbgs() << "Checking another CallRecord\n";
    assert(CR.second);
    auto fun = CR.second->getFunction();
    // if fun is nullptr, it is external
    return (!fun || getFunType(*fun) == FunType::Unknown);
  });
}

bool Fitness::runOnModule(Module &M) {
  dbgs() << "Fitness::runOnModule()\n";
  
  CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();

  CG.print(dbgs());
  
  // initialisation
  for (const Function &F : M) {
    funTypes[&F] =
        (hasPointerArgs(F) || referencesGlobalVariables(F) || F.isVarArg())
            ? FunType::Unknown
            : FunType::Functional;
  }

  // iteration
  bool changesMade;
  do {
    dbgs() << "Doing another iteration.\n";
    changesMade = false;
    for (const auto &p : CG) {
      dbgs() << "Iterating though another CallRecord\n";
      const Function *fun = p.first;
      if (!fun) {
        dbgs() << "Warning: fun == nullptr in Fitness::runOnModule\n";
        continue;
      }
      assert(p.second);
      if (getFunType(*fun) == FunType::Functional &&
          callsUnknownFunction(*p.second)) {
        funTypes[fun] = FunType::Unknown;
        changesMade = true;
      }
    }
  } while (changesMade);

  dbgs() << "Finished iterating.\n";

  return false;
}

void Fitness::releaseMemory() {
  funTypes.clear();
}

static std::string funTypeToString(Fitness::FunType f) {
  switch (f) {
  case Fitness::FunType::Functional:
    return "Functional";
  case Fitness::FunType::Unknown:
    return "Unknown";
  }
}

void Fitness::print(raw_ostream &O, const Module *) const {
  dbgs() << "Fitness::print()\n";
  O << "Printing info for " << funTypes.size() << " functions\n";
  for (auto &pair : funTypes) {
    O << "The function "; 
    O << pair.first->getName();
    O << "() is ";
    O << funTypeToString(pair.second);
    O << "\n";
  }
}

static RegisterPass<Fitness>X("fitness", "Function Fitness for Spawning Analysis", false, true);
/* static cl::opt<bool> RunFitness(
    "can-fitness",
    cl::desc("Can Fitness"),
    cl::init(false), cl::ZeroOrMore);

static void registerFitness(const PassManagerBuilder &Builder,
                                            legacy::PassManagerBase &PM) {
  if (!RunFitness)
    return;
  PM.add(new Fitness());
}

static RegisterStandardPasses RegisterFitness(PassManagerBuilder::EP_EarlyAsPossible,
                                  registerFitness);

INITIALIZE_PASS_BEGIN(Fitness, "fitness",
                      "Can Fitness", true, true);
INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass);
INITIALIZE_PASS_END(Fitness, "fitness",
                      "Can Fitness", true, true);
 */