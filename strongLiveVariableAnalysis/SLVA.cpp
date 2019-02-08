#include <algorithm>
#include <cassert>
#include <iterator>
#include <memory>
#include <utility>
#include <vector>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

namespace {

#define DEBUG_TYPE "slva"

using LiveVar = DenseSet<const Value *>;
class LiveAnalysis {
       private:
	DenseMap<const Instruction *, LiveVar> In, Out;

       public:
	bool run(Function &F) {
		std::vector<const BasicBlock *> workList;
		for (const BasicBlock *BB : depth_first(&F.getEntryBlock())) {
			workList.push_back(BB);
		}
		while (!workList.empty()) {
			LLVM_DEBUG(dbgs() << "Size of worklist is : " << workList.size()
			       << "\n");
			const BasicBlock *BB = workList.back();
			workList.pop_back();
			for (const BasicBlock *Succ : successors(BB)) {
				for (const Value *V :
				     Out[Succ->getTerminator()]) {
					Out[BB->getTerminator()].insert(V);
				}
			}
			for (auto I = BB->rbegin(); I != BB->rend(); I++) {
				const Instruction *Insn = &(*I);
				LLVM_DEBUG(dbgs() << "For instruction " << *Insn << "\n");
				LiveVar gen, kill;
				const Value *LHSVal = dyn_cast<Value>(Insn);
				kill.insert(LHSVal);
				if (Out[Insn].count(LHSVal) == 0) {
					for (auto &op : Insn->operands()) {
						if (Instruction *I =
							dyn_cast<Instruction>(
							    &op))
							gen.insert(op);
					}
				}
				In[Insn] = Out[Insn];
				if (!kill.empty()) {
					LLVM_DEBUG(dbgs() << "Kill set: ");
					for (auto V : kill) {
						LLVM_DEBUG(dbgs() << V->getName() << " ");
						In[Insn].erase(V);
					}
					LLVM_DEBUG(dbgs() << "\n");
				}
				if (!gen.empty()) {
					LLVM_DEBUG(dbgs() << "Gen set: ");
					for (auto V : gen) {
						LLVM_DEBUG(dbgs() << V->getName() << " ");
						In[Insn].insert(V);
					}
					LLVM_DEBUG(dbgs() << "\n");
				}
				kill.clear();
				gen.clear();
			}
			auto FI = BB->begin();
			const Instruction *FInsn = &(*FI);
			bool eq = false;
			if (In[FInsn].size() ==
			    Out[BB->getTerminator()].size()) {
				for (auto I : In[FInsn]) {
					if (Out[BB->getTerminator()].count(I) ==
					    0) {
						eq = false;
						break;
					}
				}
			}
			if (!eq) {
				for (const BasicBlock *Pre : predecessors(BB)) {
					workList.push_back(Pre);
				}
				// put all pre-bb into worklist
			}
		}
		return false;
	}

	bool isLiveBefore(const Instruction *I, const Value *V) {
		return In[I].count(V) != 0;
	}

	bool isLiveAfter(const Instruction *I, const Value *V) {
		return Out[I].count(V) != 0;
	}
};

class SLVAPass : public FunctionPass {
       public:
	static char ID;
	SLVAPass() : FunctionPass(ID) {}

	bool runOnFunction(Function &F) override {
		//		if (skipFunction(F)) return false;
		LiveAnalysis L;
		L.run(F);
		return false;
	}
};
}  // namespace

char SLVAPass::ID = 0;
static RegisterPass<SLVAPass> X(
    "slva",			      // the option name -> -mba
    "Strong live variable analysis",  // option description
    true,			      // true as we don't modify the CFG
    true			      // true if we're writing an analysis
);
/*
static void registerSLVAPass(const PassManagerBuilder &,
			     legacy::PassManagerBase &PM) {
	PM.add(new SLVAPass());
}
static RegisterStandardPasses RegisterMyPass(
    PassManagerBuilder::EP_EarlyAsPossible, registerSLVAPass);
*/
