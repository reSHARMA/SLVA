#include <algorithm>
#include <cassert>
#include <iterator>
#include <memory>
#include <utility>
#include <vector>
#include <queue>
#include <bits/stdc++.h>
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

#define DEBUG_TYPE "slva"

using LiveVar = DenseSet<const Value *>;
class LiveAnalysis {
       private:
	DenseMap<const Instruction *, LiveVar> In, Out;
       public:
	bool run(Function &F) {
		std::queue<const BasicBlock *> workList;
		std::vector<const BasicBlock *> work;
		for (const BasicBlock *BB : depth_first(&F.getEntryBlock())) {
			//workList.push(BB);
			work.push_back(BB);
		}
		reverse(work.begin(),work.end());
		for(auto it : work)
		{
			workList.push(it);
			errs()<<it->getName()<<"\n";
		}
		int ctr=0;
		while (!workList.empty()) {
			LLVM_DEBUG(dbgs() << "Size of worklist is : "
					  << workList.size() << "\n");
			const BasicBlock *BB = workList.front();
			ctr++;
			//std::cerr<<workList.size()<<" ********************************************************** "<<ctr<<std::endl;
			workList.pop();
			auto temp = In[&(*BB->begin())];
			for (const BasicBlock *Succ : successors(BB)) {
				for (const Value *V : In[&(*(Succ->begin()))]) {
					Out[BB->getTerminator()].insert(V);
				}
			}
			for (auto I = BB->rbegin(); I != BB->rend(); I++) {
				const Instruction *Insn = &(*I);
				LLVM_DEBUG(dbgs() << "For instruction " << *Insn
						  << "\n");
				LiveVar gen, kill;
				if (I != BB->rbegin()) {
					auto tempI = I;
					tempI--;
					Out[Insn] = In[&*tempI];
				}
				const Value *LHSVal;
				if (isa<StoreInst>(*Insn)) {
					LHSVal = Insn->getOperand(1);
					kill.insert(LHSVal);
				} else {
					LHSVal = dyn_cast<Value>(Insn);
					kill.insert(LHSVal);
				}
				if (isa<StoreInst>(*Insn)) {
					const Value *op = Insn->getOperand(0);
					if (const ConstantInt *CI =
						dyn_cast<ConstantInt>(op)) {
					} else {
						gen.insert(op);
					}
				} else {
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
						LLVM_DEBUG(dbgs()
							   << V->getName()
							   << " ");
						In[Insn].erase(V);
					}
					LLVM_DEBUG(dbgs() << "\n");
				}
				if (!gen.empty() &&
				    (LHSVal->getName() == "" ||
				     isLiveAfter(Insn, LHSVal))) {
					LLVM_DEBUG(dbgs() << "Gen set: ");
					for (auto V : gen) {
						LLVM_DEBUG(dbgs()
							   << V->getName()
							   << " ");
						In[Insn].insert(V);
					}
					LLVM_DEBUG(dbgs() << "\n");
				}
				kill.clear();
				gen.clear();
			}
			auto FI = BB->begin();
			const Instruction *FInsn = &(*FI);
			bool eq = true ;
			if (In[FInsn].size() ==
			    temp.size()) {
				for (auto I : In[FInsn]) {
					if (temp.count(I) ==
					    0) {
						eq = false;
						break;
					}
				}
			}
			if (!eq) {
				workList.push(BB);
				for (const BasicBlock *Pre : predecessors(BB)) {
					workList.push(Pre);
				}
				// put all pre-bb into worklist
			}

	
		}
		if (true) {
			for (Function::iterator b = F.begin(); b != F.end();
			     b++) {
				const BasicBlock *B = &*b;
				for (auto i = B->begin(); i != B->end(); i++) {
					const Instruction *I = &*i;
					for (auto V : In[I]) {
						errs() << V->getName() << " ";
					}
					errs() << "\n" << *I << "\n";
					for (auto V : Out[I]) {
						errs() << V->getName() << " ";
					}
					errs() << "\n";
				}
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
	void pOut(const Instruction *I) {
		errs() << "Out \n";
		for (auto I : Out[I]) {
			errs() << I->getName() << " ";
		}
		errs() << "\n";
	}
	void pIn(const Instruction *I) {
		errs() << "In \n";
		for (auto I : In[I]) {
			errs() << I->getName() << " ";
		}
		errs() << "\n";
	}
	void print(LiveVar jset) {
		for (auto a : jset) {
			errs() << a->getName() << " ";
		}
		errs() << "\n";
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
