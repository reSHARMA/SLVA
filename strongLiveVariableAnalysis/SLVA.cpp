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

namespace  {

#define DEBUG_TYPE "slva"

using LiveVar = DenseSet<const Value *>;
class LiveAnalysis {
       public:
	bool run(Function &F) {
		std::vector<const BasicBlock*> workList;
		for (const BasicBlock *BB : depth_first(&F.getEntryBlock())) {
			workList.push_back(BB);
		}
		LLVM_DEBUG(dbgs() << workList.size() << "\n");
		DenseMap<const Instruction *, LiveVar> In, Out;
		while (!workList.empty()) {
			errs() << "Size of worklist is : " << workList.size() << "\n";
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
				errs() << "For instruction " << *Insn << "\n";
				LiveVar gen, kill;
				bool def = true;
				bool strong = false;
				const std::string opcode =
				    Insn->getOpcodeName(Insn->getOpcode());
				std::vector<std::string> noDef = {
				    "ret",	 "br",	  "switch",
				    "indirectbr",  "invoke",      "resume",
				    "unreachable", "cleanupret",  "catchret",
				    "catchpad",    "catchswitch", "alloca",
				    "load"};
				for (auto s : noDef) {
					if (opcode == s) {
						def = false;
					}
				}
				for (int i = 0; i < Insn->getNumOperands();
				     i++) {
					Value *operand = Insn->getOperand(i);
					if (def) {
						// a = b + c;
						if (i == 0) {
							if (Out[Insn].count(
								operand) == 1) {
								strong = true;
							}
							kill.insert(operand);
						} else {
							if (!strong) {
								gen.insert(
								    operand);
							}
						}
					} else {
						// return a;
						gen.insert(operand);
					}
				}
				errs() << "Kill set: ";
				for (auto V : kill) {
					errs() << *V << ", ";
					In[Insn].erase(V);
				}
				errs() << "\n Gen set: ";
				for (auto V : gen) {
					errs() << *V << ", ";
					In[Insn].insert(V);
				}
				errs() << "\n";
				kill.clear();
				gen.clear();
			}
			if (Out[&(*(BB->begin()))] !=
			    Out[&(*(BB->getTerminator()))]) {
				for (const BasicBlock *Pre : predecessors(BB)) {
					workList.push_back(Pre);
				}
				// put all pre-bb into worklist
			}
		}
		return false;
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
}  // namespace llvm

char SLVAPass::ID = 0;
static RegisterPass<SLVAPass>
    X("slva",  // the option name -> -mba
      "Strong live variable analysis", // option description
      true, // true as we don't modify the CFG
      true // true if we're writing an analysis
      );
/*
static void registerSLVAPass(const PassManagerBuilder &,
			     legacy::PassManagerBase &PM) {
	PM.add(new SLVAPass());
}
static RegisterStandardPasses RegisterMyPass(
    PassManagerBuilder::EP_EarlyAsPossible, registerSLVAPass);
*/
