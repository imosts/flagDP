//===- MyPass.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "MyPass" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/MyPass/MyPass.h"

#define DEBUG_TYPE "MyPass"
#define INI_TYPE_MEMSET 1
#define INI_TYPE_MEMCPY 2
#define MULTIPTR_OR_NODEPTR 0xC000000000000000
#define MULTIPTR 0x8000000000000000
#define MULTIPTRHEAD 0xFFFF000000000000
#define NODEPTR 0x4000000000000000
#define AND_PTR_VALUE 0x00007FFFFFFFFFFF

//#define DEBUG

using namespace llvm;

namespace {
    struct MyPass : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        bool flag;
        bool need_bb_iter_begin = false;
        bool isIniGloVar = false;
        bool isFunHasNullPtr = false;
        AllocaInst *FunNullPtr = NULL;
        GlobalVariable *GNPtr = NULL;
        
        unsigned ini_type = 0;
        
        MyPass() : FunctionPass(ID) {}
        MyPass(bool flag) : FunctionPass(ID) {
            this->flag = flag;
        }
        
        std::set<StringRef> ValueName;
        std::vector<std::string> varNameList;
        std::vector<std::string> structNameList;
        std::vector<std::string> localFunName;
        std::vector<Value *> structIndexList;
        
        
        bool runOnFunction(Function &F) override {
            Function *tmpF = &F;
            unsigned FAnum = 0;
            isFunHasNullPtr = false;
            
            std::ifstream open_file("localFunName.txt"); // 读取
            while (open_file) {
                std::string line;
                std::getline(open_file, line);
                auto index=std::find(localFunName.begin(), localFunName.end(), line);
                if(!line.empty() && index == localFunName.end()){
                    localFunName.push_back(line);
                }
            }
            #ifdef DEBUG
            errs() << "  Function:" << tmpF->getName() <<'\n' <<'\n';
            #endif
            for (Function::iterator bb = tmpF->begin(); bb != tmpF->end(); ++bb) {
                for (BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                    #ifdef DEBUG
                    errs() << "  Inst Before" <<'\n';
                    inst->dump();
                    #endif
                    
                    if (LoadInst *LI = dyn_cast<LoadInst>(inst)) {
                        #ifdef DEBUG
                        LI->dump();
                        LI->getOperand(0)->dump();
                        LI->getOperand(0)->getType()->getContainedType(0)->dump();
//                        isStdorPthreadType(LI->getPointerOperand()->getType());
                        errs() << "LoadInst Deubg1 :" << '\n';
                        #endif
                        
                        if (pointerLevel(LI->getOperand(0)->getType()) >= 2 && !(LI->getOperand(0)->getType()->getContainedType(0)->isFunctionTy())) {
                            #ifdef DEBUG
//                            bb->dump();
                            errs() << "LoadInst Deubg:" << '\n';
                            LI->dump();
                            LI->getPointerOperand()->getType()->dump();
                            #endif
                            if (LI->getPointerOperand()->getType()->isPointerTy()) {
                                Type *T = getSouType(LI->getPointerOperand()->getType(), pointerLevel(LI->getPointerOperand()->getType()));
                                #ifdef DEBUG
                                if (T->isStructTy()) {
                                    errs() << "isStructTy!!! Type name: " << T->getStructName() << '\n';
                                }
                                #endif
                            }
                            int useNum = 0;
                            int LIUseNum = 0;
                            int FunArgUseNum = 0;
                                //BUG:Bitcast转换以后要继续考虑是否为不需要转换的！！！
                                Function::iterator tmpBB = bb;
                            for (Function::iterator tmpBB = bb; tmpBB != tmpF->end(); ++tmpBB) {
                                for (BasicBlock::iterator inst2 = tmpBB->begin(); inst2 != tmpBB->end(); ++inst2) {
                                    if (Instruction *I = dyn_cast<Instruction>(inst2)) {
                                        if (!dyn_cast<BitCastInst>(I)) {
                                            for (Instruction::op_iterator op = I->op_begin(); op != I->op_end(); ++op) {
                                                if (Instruction *Iop = dyn_cast<Instruction>(op)) {
                                                    if (isComeFormLI(Iop, LI)) {
                                                        useNum++;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                
                            }
                            
                                for (Function::iterator tmpBB = bb; tmpBB != tmpF->end(); ++tmpBB) {
                                    for (BasicBlock::iterator inst2 = tmpBB->begin(); inst2 != tmpBB->end(); ++inst2) {
                                        if (StoreInst *SI = dyn_cast<StoreInst>(inst2)) {
                                            if (isComeFormLI(SI->getValueOperand(), LI) && SI->getValueOperand()->getType()->isPointerTy()) {
                                                LIUseNum++;
                                                continue;
                                            } else if (isComeFormLI(SI->getPointerOperand(), LI)) {
                                                useNum++;
                                            }
                                        } else if(CallInst *CI = dyn_cast<CallInst>(inst2)){
                                            if (Function *fTemp = CI->getCalledFunction()) {
                                                if (!(fTemp->getFunctionType()->isVarArg())) {
                                                    auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
                                                    if (index != localFunName.end()) {
#ifdef DEBUG
                                                        errs() << "find LocalFun!" << '\n';
                                                        CI->dump();
#endif
                                                        for (Instruction::op_iterator oi = CI->op_begin(); oi != CI->op_end(); ++oi) {
                                                            if (Value *V = dyn_cast<Value>(oi)) {
#ifdef DEBUG
#endif
                                                                if (isComeFormLI(V, LI)) {
#ifdef DEBUG
                                                                    errs() << "find LocalFun use!" << '\n';
                                                                    errs() << fTemp->getName();
#endif
                                                                    LIUseNum++;
                                                                    FunArgUseNum++;
                                                                    continue;
                                                                }
                                                            }
                                                            
                                                        }
                                                    }
                                                }

                                            }
                                            else {
                                                if (!(CI->getFunctionType()->isVarArg())) {
                                                    for (Instruction::op_iterator oi = CI->op_begin(); oi != CI->op_end(); ++oi) {
                                                        if (Value *V = dyn_cast<Value>(oi)) {
                                                            if (isComeFormLI(V, LI)) {
#ifdef DEBUG
                                                                errs() << "find Function Pointer LI use!" << '\n';
#endif
                                                                LIUseNum++;
                                                                FunArgUseNum++;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }

                                        } else if (ReturnInst *RI = dyn_cast<ReturnInst>(inst2)) {
                                            #ifdef DEBUG
                                            errs() << "RET debug:" << '\n';
                                            RI->dump();
                                            #endif
                                            if (RI->getReturnValue() && !(RI->getReturnValue()->getType()->isVoidTy()) && isComeFormLI(RI->getReturnValue(), LI)) {
                                                #ifdef DEBUG
                                                errs() << "find RET use:" << '\n';
                                                #endif
                                                LIUseNum++;
                                                continue;
                                            }
                                        } else if (InvokeInst *II = dyn_cast<InvokeInst>(inst2)) {
                                            if (Function *fTemp = II->getCalledFunction()) {
                                                if (!(fTemp->getFunctionType()->isVarArg())) {
                                                    auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
                                                    if (index != localFunName.end()) {
#ifdef DEBUG
                                                        errs() << "find invoke LocalFun!" << '\n';
                                                        II->dump();
#endif
                                                        for (Instruction::op_iterator oi = II->arg_begin(); oi != II->arg_end(); ++oi) {
                                                            if (Value *V = dyn_cast<Value>(oi)) {
#ifdef DEBUG
                                                                errs() << "invoke oi!" << '\n';
#endif
                                                                if (isComeFormLI(V, LI)) {
#ifdef DEBUG
                                                                    errs() << "find invoke LocalFun use!" << '\n';
                                                                    //                                                                errs() << fTemp->getName();
#endif
                                                                    
                                                                    LIUseNum++;
                                                                    FunArgUseNum++;
                                                                    continue;
                                                                }
                                                            }
                                                            
                                                        }
                                                    }
                                                }
                                                
                                                
                                            }
                                            else{
                                                if (!(II->getFunctionType()->isVarArg())) {
                                                    for (Instruction::op_iterator oi = II->op_begin(); oi != II->op_end(); ++oi) {
                                                        if (Value *V = dyn_cast<Value>(oi)) {
                                                            if (isComeFormLI(V, LI)) {
#ifdef DEBUG
                                                                errs() << "find Function Pointer LI use!" << '\n';
#endif
                                                                LIUseNum++;
                                                                FunArgUseNum++;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                                
                                            }
                                        }

                                    }
                                }
#ifdef DEBUG
                            errs() << "FunArgUseNum1:" << FunArgUseNum << '\n';
                            errs() << "useNum:" << useNum - LIUseNum << '\n';
#endif
                            useNum = useNum - LIUseNum;
                            if (useNum > 0) {
                                LoadInst *sameLI = new LoadInst(LI->getPointerOperand(), "sameLI", &(*inst));
                                inst++;
                                Value *phi = insertLoadCheckInBasicBlock(tmpF, bb, inst, sameLI);
                                inst--;
                                LI->replaceAllUsesWith(phi);
                                if (LIUseNum > 0) {
                                    #ifdef DEBUG
                                    errs() << "FunArgUseNum2:" << FunArgUseNum << '\n';
                                    #endif
                                    Function::iterator tmpBB = bb;
                                    for (Function::iterator tmpBB = bb; tmpBB != tmpF->end(); ++tmpBB) {
                                        for (BasicBlock::iterator inst2 = tmpBB->begin(); inst2 != tmpBB->end(); ++inst2) {
                                            if (LIUseNum <= 0) {
                                                break;
                                            }
                                            if (StoreInst *SI = dyn_cast<StoreInst>(inst2)) {
                                                if (isComeFormSouce(SI->getValueOperand(), phi)&& SI->getValueOperand()->getType()->isPointerTy()) {
                                                    LIUseNum--;
                                                    if (BitCastInst *BCI = dyn_cast<BitCastInst>(SI->getValueOperand())) {
                                                        BitCastInst *nBCI = new BitCastInst(sameLI, BCI->getType(), "", SI);
                                                        SI->setOperand(0, nBCI);
                                                        #ifdef DEBUG
                                                        SI->dump();
                                                        nBCI->dump();
                                                        #endif
                                                        if (BCI->getNumUses() == 0) {
                                                            BCI->eraseFromParent();
                                                        }
                                                    } else {
                                                        SI->setOperand(0, sameLI);
                                                        #ifdef DEBUG
                                                        SI->dump();
                                                        #endif
                                                    }

                                                }
                                            } else if (FunArgUseNum > 0 && dyn_cast<CallInst>(inst2)) {
#ifdef DEBUG
                                                errs() << "find CallInst!" << '\n';
#endif
                                                if (CallInst *CI = dyn_cast<CallInst>(inst2)) {
                                                    if (Function *fTemp = CI->getCalledFunction()) {
                                                        #ifdef DEBUG
                                                        errs() << "Function VarArg debug:\n";
                                                        errs() << fTemp->getName() << '\n';
                                                        errs() << fTemp->getFunctionType()->isVarArg() << '\n';
                                                        #endif
                                                        if (!(fTemp->getFunctionType()->isVarArg())) {
                                                            auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
#ifdef DEBUG
                                                            errs() << "chang FunArg:" << '\n';
#endif
                                                            if (index != localFunName.end()) {
                                                                for (unsigned i = 0; i < CI->getNumOperands(); ++i) {
                                                                    if (Value *V = dyn_cast<Value>(CI->getOperand(i))) {
                                                                        if (isComeFormSouce(V, phi)) {
#ifdef DEBUG
                                                                            bb->dump();
                                                                            errs() << "chang FunArg:" << '\n';
                                                                            CI->dump();
                                                                            sameLI->dump();
#endif
                                                                            LIUseNum--;
                                                                            FunArgUseNum--;
                                                                            if (BitCastInst *BCI = dyn_cast<BitCastInst>(CI->getOperand(i))) {
                                                                                BitCastInst *nBCI = new BitCastInst(sameLI, BCI->getType(), "", CI);
                                                                                CI->setOperand(i, nBCI);
#ifdef DEBUG
                                                                                CI->dump();
                                                                                nBCI->dump();
#endif
                                                                                if (BCI->getNumUses() == 0) {
                                                                                    BCI->eraseFromParent();
                                                                                }
                                                                            } else if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(CI->getOperand(i))) {
                                                                                PtrToIntInst *nPTI = new PtrToIntInst(sameLI, CI->getOperand(i)->getType(), "", &(*CI));
                                                                                CI->setOperand(i, nPTI);
                                                                                if (PTI->getNumUses() == 0) {
                                                                                    PTI->eraseFromParent();
                                                                                }
                                                                            } else {
                                                                                CI->setOperand(i, sameLI);
#ifdef DEBUG
                                                                                CI->dump();
#endif
                                                                            }
                                                                            
                                                                        }
                                                                    }
                                                                }
                                                                
                                                            }
                                                        }
                                                        
                                                    }
                                                    else {
                                                        if (!(CI->getFunctionType()->isVarArg())) {
                                                            for (unsigned i = 0; i < CI->getNumOperands(); ++i) {
                                                                if (Value *V = dyn_cast<Value>(CI->llvm::User::getOperand(i))) {
                                                                    if (isComeFormSouce(V, phi)) {
#ifdef DEBUG
                                                                        errs() << "chang FunArg:" << '\n';
                                                                        CI->dump();
#endif
                                                                        LIUseNum--;
                                                                        FunArgUseNum--;
                                                                        if (BitCastInst *BCI = dyn_cast<BitCastInst>(CI->getOperand(i))) {
                                                                            
                                                                            BitCastInst *nBCI = new BitCastInst(sameLI, BCI->getType(), "", CI);
                                                                            CI->setOperand(i, nBCI);
                                                                            if (BCI->getNumUses() == 0) {
                                                                                BCI->eraseFromParent();
                                                                            }
                                                                        } else if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(CI->getOperand(i))) {
                                                                            PtrToIntInst *nPTI = new PtrToIntInst(sameLI, CI->getOperand(i)->getType(), "", &(*CI));
                                                                            CI->setOperand(i, nPTI);
                                                                            if (PTI->getNumUses() == 0) {
                                                                                PTI->eraseFromParent();
                                                                            }
                                                                        } else {
                                                                            CI->setOperand(i, sameLI);
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                        
                                                    }
                                                }

                                            } else if (ReturnInst *RI = dyn_cast<ReturnInst>(inst2)) {
                                                if (RI->getReturnValue() && !(RI->getReturnValue()->getType()->isVoidTy()) && RI->getReturnValue() == phi) {
#ifdef DEBUG
                                                    errs() << "chang RetArg:" << '\n';
#endif
                                                    LIUseNum--;
                                                    RI->setOperand(0, sameLI);
                                                }
                                            } else if (InvokeInst *II = dyn_cast<InvokeInst>(inst2)) {
                                                if (Function *fTemp = II->getCalledFunction()) {
                                                    if (!(fTemp->getFunctionType()->isVarArg())) {
                                                        auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
#ifdef DEBUG
                                                        errs() << "chang FunArg:" << '\n';
#endif
                                                        if (index != localFunName.end()) {
                                                            for (unsigned i = 0; i < II->getNumOperands(); ++i) {
                                                                if (Value *V = dyn_cast<Value>(II->getOperand(i))) {
                                                                    if (isComeFormSouce(V, phi)) {
#ifdef DEBUG
                                                                        bb->dump();
                                                                        errs() << "chang FunArg:" << '\n';
                                                                        II->dump();
                                                                        sameLI->dump();
#endif
                                                                        LIUseNum--;
                                                                        FunArgUseNum--;
                                                                        if (BitCastInst *BCI = dyn_cast<BitCastInst>(II->getOperand(i))) {
                                                                            BitCastInst *nBCI = new BitCastInst(sameLI, BCI->getType(), "", II);
                                                                            II->setOperand(i, nBCI);
#ifdef DEBUG
                                                                            II->dump();
                                                                            nBCI->dump();
#endif
                                                                            if (BCI->getNumUses() == 0) {
                                                                                BCI->eraseFromParent();
                                                                            }
                                                                        } else if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(II->getOperand(i))) {
                                                                            PtrToIntInst *nPTI = new PtrToIntInst(sameLI, II->getOperand(i)->getType(), "", &(*II));
                                                                            II->setOperand(i, nPTI);
                                                                            if (PTI->getNumUses() == 0) {
                                                                                PTI->eraseFromParent();
                                                                            }
                                                                        } else {
                                                                            II->setOperand(i, sameLI);
#ifdef DEBUG
                                                                            II->dump();
#endif
                                                                        }
                                                                        
                                                                    }
                                                                }
                                                            }
                                                            
                                                        }
                                                    }
                                                    
                                                }
                                                else{
                                                    if (!(II->getFunctionType()->isVarArg())) {
                                                        for (unsigned i = 0; i < II->getNumOperands(); ++i) {
                                                            if (Value *V = dyn_cast<Value>(II->llvm::User::getOperand(i))) {
                                                                if (isComeFormSouce(V, phi)) {
#ifdef DEBUG
                                                                    errs() << "chang FunArg:" << '\n';
                                                                    II->dump();
#endif
                                                                    LIUseNum--;
                                                                    FunArgUseNum--;
                                                                    if (BitCastInst *BCI = dyn_cast<BitCastInst>(II->getOperand(i))) {
                                                                        BitCastInst *nBCI = new BitCastInst(sameLI, BCI->getType(), "", II);
                                                                        II->setOperand(i, nBCI);
                                                                        if (BCI->getNumUses() == 0) {
                                                                            BCI->eraseFromParent();
                                                                        }
                                                                    } else if (PtrToIntInst *PTI = dyn_cast<PtrToIntInst>(II->getOperand(i))) {
                                                                        PtrToIntInst *nPTI = new PtrToIntInst(sameLI, II->getOperand(i)->getType(), "", &(*II));
                                                                        II->setOperand(i, nPTI);
                                                                        if (PTI->getNumUses() == 0) {
                                                                            PTI->eraseFromParent();
                                                                        }
                                                                    } else {
                                                                        II->setOperand(i, sameLI);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                if (LI->getNumUses() == 0) {
                                    LI->eraseFromParent();
                                }
                                

                            }
                        }
                        
                    }
                    
                    
                    
                    if (CallInst *CI = dyn_cast<CallInst>(inst)) {
                        if (Function *fTemp = CI->getCalledFunction()) {
                            if (CI && CI->getCalledFunction()->getName().equals("free")) {
                                #ifdef DEBUG
                                errs() << "free debug!" << '\n';
                                #endif
                                CI->setCalledFunction(tmpF->getParent()->getFunction("safeFree"));
                            } else if (CI && (CI->getCalledFunction()->getName().contains("llvm.memset.") || CI->getCalledFunction()->getName().contains("llvm.memcpy."))) {
                                Value *phi = insertLoadCheckInBasicBlock(tmpF, bb, inst, CI->getArgOperand(0));
                                CI->setArgOperand(0, phi);
                            } else {
                                auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
                                if (index == localFunName.end()) {
                                    for (unsigned int i = 0; i < CI->getNumArgOperands(); ++i) {
                                        if (CI->getArgOperand(i)->getType()->isPointerTy() && isComeFormLoaclCall(CI->getArgOperand(i))) {
                                            #ifdef DEBUG
                                            errs() << "find local call use!:\n";
                                            CI->dump();
                                            CI->getArgOperand(i)->dump();
                                            #endif
                                            Value *phi = insertLoadCheckInBasicBlock(tmpF, bb, inst, CI->getArgOperand(i));
                                            CI->setArgOperand(i, phi);
                                            #ifdef DEBUG
                                            bb->dump();
                                            #endif
                                        }
                                    }
                                } else {
                                    #ifdef DEBUG
                                    errs() << "Call debug1!\n";
                                    CI->dump();
                                    #endif
                                    if (CI->getType()->isPointerTy()) {
                                        if (CI->getNumUses() > 0) {
                                            BasicBlock::iterator tmpI = inst;
                                            tmpI++;
                                            AllocaInst *AI = new AllocaInst(CI->getType(), 0, "na", CI);
                                            StoreInst *SI = new StoreInst(CI, AI, &(*tmpI));
                                            LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                            CI->replaceAllUsesWith(LI);
                                            SI->setOperand(0, CI);
//                                            inst++;
                                            continue;
                                        }
                                    }
                                    
                                }
                            }
                            #ifdef DEBUG
                            errs() << CI->getCalledFunction()->getName() << '\n';
                            #endif
                        } else if (BitCastOperator *BCO = dyn_cast<BitCastOperator>(CI->getCalledValue())) {
                            if (BCO->getOperand(0)->getName().equals("free")) {
                                #ifdef DEBUG
                                errs() << "free Function!\n";
                                #endif
                                LoadInst *LI = dyn_cast<LoadInst>(CI->getOperand(0));
                                BitCastInst *BCI = NULL;
                                Value *FreeArg = LI->getPointerOperand();
                                if (LI) {
                                    #ifdef DEBUG
                                    LI->dump();
                                    #endif
                                    if (LI->getPointerOperand()->getType() != PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(bb->getContext())))) {
                                        BCI = new BitCastInst(LI->getPointerOperand(), PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(bb->getContext()))), "", &(*inst));
                                    }
                                }
                                
                                if (BCI) {
                                    FreeArg = BCI;
                                }
                                
                                std::vector<Value *> freeArg;
                                freeArg.push_back(FreeArg);
                                ArrayRef<Value *> funcArg(freeArg);
                                Value *func = tmpF->getParent()->getFunction("safeFree");
                                CallInst *nCI = CallInst::Create(func, funcArg, "", &(*inst));
                                inst--;
                                CI->eraseFromParent();
                                inst++;
                                
                            }
                        } else {
                            if (CI->getType()->isPointerTy()) {
                                if (CI->getNumUses() > 0) {
                                    BasicBlock::iterator tmpI = inst;
                                    tmpI++;
                                    AllocaInst *AI = new AllocaInst(CI->getType(), 0, "na", CI);
                                    StoreInst *SI = new StoreInst(CI, AI, &(*tmpI));
                                    LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                    CI->replaceAllUsesWith(LI);
                                    SI->setOperand(0, CI);
                                    inst++;
                                    continue;
                                }
                            }
                        }
                        
                    }
                    
                    if (InvokeInst *II = dyn_cast<InvokeInst>(inst)) {
                        if (Function *fTemp = II->getCalledFunction()) {
                            if (fTemp->getName().equals("free")) {
#ifdef DEBUG
                                errs() << "free debug!" << '\n';
#endif
                                II->setCalledFunction(tmpF->getParent()->getFunction("safeFree"));
                            } else if (fTemp->getName().equals("malloc")) {
                                II->setCalledFunction(tmpF->getParent()->getFunction("safeMalloc"));
                                AllocaInst *AI = new AllocaInst(II->getType(), 0, "na", II);
                                BasicBlock *norBB = II->getNormalDest();
                                BasicBlock::iterator tmpI = norBB->begin();
                                StoreInst *SI = new StoreInst(II, AI, &(*tmpI));
                                LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                II->replaceAllUsesWith(LI);
                                SI->setOperand(0, II);
                                continue;
                            } else {
                                auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
                                if (index == localFunName.end()) {
                                    for (unsigned int i = 0; i < II->getNumArgOperands(); ++i) {
                                        if (II->getArgOperand(i)->getType()->isPointerTy() && isComeFormLoaclCall(II->getArgOperand(i))) {
#ifdef DEBUG
                                            errs() << "Invoke local call use!:\n";
                                            II->dump();
                                            II->getArgOperand(i)->dump();
#endif
                                            Value *phi = insertLoadCheckInBasicBlock(tmpF, bb, inst, II->getArgOperand(i));
                                            II->setArgOperand(i, phi);
#ifdef DEBUG
                                            bb->dump();
#endif
                                        }
                                    }
                                    
                                    //                                if (fTemp->getName().equals("malloc")) {
                                    //                                    II->setCalledFunction(tmpF->getParent()->getFunction("safeMalloc"));
                                    //                                    AllocaInst *AI = new AllocaInst(II->getType(), 0, "na", II);
                                    //                                    BasicBlock *norBB = II->getNormalDest();
                                    //                                    BasicBlock::iterator tmpI = norBB->begin();
                                    //                                    StoreInst *SI = new StoreInst(II, AI, &(*tmpI));
                                    //                                    LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                    //                                    II->replaceAllUsesWith(LI);
                                    //                                    SI->setOperand(0, II);
                                    //                                    //                                    inst++;
                                    //                                    continue;
                                    //                                }
                                    
                                } else {
                                    
#ifdef DEBUG
                                    errs() << "Invoke debug1!\n";
                                    II->dump();
                                    II->getType()->dump();
                                    errs() <<"II->getNumUses(): " << II->getNumUses() << '\n';
#endif
                                    if (II->getType()->isPointerTy()) {
                                        if (II->getNumUses() > 0) {
                                            AllocaInst *AI = new AllocaInst(II->getType(), 0, "na", II);
                                            BasicBlock *norBB = II->getNormalDest();
                                            BasicBlock::iterator tmpI = norBB->begin();
                                            StoreInst *SI = new StoreInst(II, AI, &(*tmpI));
                                            LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                            II->replaceAllUsesWith(LI);
                                            SI->setOperand(0, II);
                                            //                                    inst++;
                                            continue;
                                        }
                                    }
                                    
                                }
                            }
                            
                        } else {
                            if (II->getType()->isPointerTy()) {
                                if (II->getNumUses() > 0) {
                                    AllocaInst *AI = new AllocaInst(II->getType(), 0, "na", II);
                                    BasicBlock *norBB = II->getNormalDest();
                                    BasicBlock::iterator tmpI = norBB->begin();
                                    StoreInst *SI = new StoreInst(II, AI, &(*tmpI));
                                    LoadInst *LI = new LoadInst(AI, "li", &(*tmpI));
                                    II->replaceAllUsesWith(LI);
                                    SI->setOperand(0, II);
                                    //                                    inst++;
                                    continue;
                                }
                            }
                        }
                    }
                    
                    if (StoreInst *SI = dyn_cast<StoreInst>(inst)) {
                        #ifdef DEBUG
                        errs() << "SI debug:\n";
                        SI->getValueOperand()->dump();
                        #endif
                        if (isComeFromGEPAndChange(SI->getValueOperand())) {
                            #ifdef DEBUG
                            errs() << "SI Value Come from GEP and Ptr Change!\n";
                            #endif
                            if (getComeFromGEPAndChangeOrigin(SI->getValueOperand())) {
                                #ifdef DEBUG
                                errs() << "SI Debug 1!\n";
                                SI->getValueOperand()->dump();
                                #endif
                                Value *V = getComeFromGEPAndChangeOrigin(SI->getValueOperand());
                                #ifdef DEBUG
                                errs() << "SI Debug 11!\n";
                                #endif
                                if (PHINode *phi = dyn_cast<PHINode>(V)) {
                                    #ifdef DEBUG
                                    errs() << "SI Debug 2!\n";
                                    #endif
                                    if (LoadInst *LI = dyn_cast<LoadInst>(phi->getOperand(0))) {
                                        #ifdef DEBUG
                                        errs() << "SI Debug 3!\n";
                                        #endif
                                        if (pointerLevel(LI->getPointerOperand()->getType()) >= 2) {
                                            #ifdef DEBUG
                                            errs() << "SI Debug 4!\n";
                                            #endif
                                            std::vector<Value *> getPtrArg;
                                            
                                            BitCastInst *originBCI = new BitCastInst(LI->getPointerOperand(), PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext()))), "oriBCI", &(*inst));
                                            getPtrArg.push_back(originBCI);
                                            BitCastInst *oldBCI = new BitCastInst(SI->getPointerOperand(), PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext()))), "oldBCI", &(*inst));
                                            getPtrArg.push_back(oldBCI);
                                            BitCastInst *ptrBCI = new BitCastInst(SI->getValueOperand(), PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext())), "ptrBCI", &(*inst));
                                            getPtrArg.push_back(ptrBCI);
                                            
                                            ArrayRef<Value *> funcArg(getPtrArg);
                                            Value *func = tmpF->getParent()->getFunction("getPtr");
                                            CallInst *nCI = CallInst::Create(func, funcArg, "", &(*inst));
                                            inst++;
                                            SI->eraseFromParent();
                                            inst--;
                                        }
                                    }
                                }else if (GlobalValue *GV = dyn_cast<GlobalValue>(V)) {
                                    #ifdef DEBUG
                                    errs() << "GlobalValue1!\n";
                                    #endif
//                                    if (!isStdorPthreadType(GV->getType())) {
                                        #ifdef DEBUG
                                        errs() << "GlobalValue!\n";
                                        #endif
                                        std::vector<Value *> getPtrArg;
                                        
                                        BitCastInst *originBCI = new BitCastInst(V, PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext()))), "oriBCI", &(*inst));
                                        getPtrArg.push_back(originBCI);
                                        BitCastInst *oldBCI = new BitCastInst(SI->getPointerOperand(), PointerType::getUnqual(PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext()))), "oldBCI", &(*inst));
                                        getPtrArg.push_back(oldBCI);
                                        BitCastInst *ptrBCI = new BitCastInst(SI->getValueOperand(), PointerType::getUnqual(Type::getInt8Ty(tmpF->getContext())), "ptrBCI", &(*inst));
                                        getPtrArg.push_back(ptrBCI);
                                        
                                        ArrayRef<Value *> funcArg(getPtrArg);
                                        Value *func = tmpF->getParent()->getFunction("getPtr");
                                        CallInst *nCI = CallInst::Create(func, funcArg, "", &(*inst));
                                        inst++;
                                        SI->eraseFromParent();
                                        inst--;
//                                    }
                                }
                            }
                        }else if (isSIValueComeFromMalloc(SI)) {
                            CallInst *CI = isSIValueComeFromMalloc(SI);
                            BasicBlock::iterator tmp = inst;
                            bool isBBhead = true;
                            #ifdef DEBUG
                            errs() << "malloc debug!" << '\n';
                            #endif
                            tmp++;
                            #ifdef DEBUG
                            tmp->dump();
                            #endif
                            changTOSafeMalloc(tmpF, CI, SI, tmp);
                            inst = tmp;
                            inst--;
                        }
                    }
                    
                    #ifdef DEBUG
                    inst->dump();
                    errs() << "  Inst After" <<'\n' <<'\n';
                    #endif
                }
            }
            return true;
            
            
        };
        
        Value * insertLoadCheckInBasicBlock(Function* F, Function::iterator &originBB, BasicBlock::iterator &insetPoint, Value *address){
            PtrToIntInst *PTI = new PtrToIntInst(address, Type::getInt64Ty(originBB->getContext()), "", &(*insetPoint));
            BinaryOperator *BO = BinaryOperator::Create(Instruction::BinaryOps::And, PTI, ConstantInt::get(Type::getInt64Ty(originBB->getContext()), MULTIPTRHEAD, false), "", &(*insetPoint));
            ICmpInst *ICM = new ICmpInst(&(*insetPoint), llvm::CmpInst::ICMP_EQ, BO, ConstantInt::get(Type::getInt64Ty(originBB->getContext()), MULTIPTR, false));
            
            BasicBlock *newBB = llvm::SplitBlock(&(*originBB), &(*insetPoint), nullptr, nullptr);
            BasicBlock *oldBB = &(*originBB);
            BasicBlock::iterator inst = originBB->begin();
            newBB->setName("newBasicBlock");
            originBB->setName("oldBasicBlock");
            
            BasicBlock *nBAND = BasicBlock::Create(originBB->getContext(), "ANDBB", F, newBB);
            BranchInst *nBIAND = BranchInst::Create(newBB, nBAND);

            BranchInst *oldBR = BranchInst::Create(nBAND, newBB, ICM, &(*originBB));
            inst = originBB->end();
            inst--;
            inst--;
            inst->eraseFromParent();
            
            originBB++;
            inst = originBB->begin();
            BinaryOperator *BOAnd = BinaryOperator::Create(Instruction::BinaryOps::And, PTI, ConstantInt::get(Type::getInt64Ty(originBB->getContext()), AND_PTR_VALUE, false), "", &(*inst));
            IntToPtrInst *ITPAnd = new IntToPtrInst(BOAnd, PointerType::getUnqual(address->getType()), "", &(*inst));

            LoadInst *multiLI = new LoadInst(ITPAnd, "", &(*inst));
            PtrToIntInst *PTImulti = new PtrToIntInst(multiLI, Type::getInt64Ty(originBB->getContext()), "", &(*inst));
            BinaryOperator *BOmulte = BinaryOperator::Create(Instruction::BinaryOps::And, PTImulti, ConstantInt::get(Type::getInt64Ty(originBB->getContext()), AND_PTR_VALUE, false), "", &(*inst));
            IntToPtrInst *ITPmulti = new IntToPtrInst(BOmulte, multiLI->getType(), "", &(*inst));
            
            originBB++;
            inst = originBB->begin();
            PHINode *PhiNode = PHINode::Create(address->getType(), 2, "", &(*inst));
            PhiNode->addIncoming(address, oldBB);
            PhiNode->addIncoming(ITPmulti, nBAND);
            return PhiNode;
        }
        
        //判断ICMP的操作数是否来源于Value V
        bool instComeFromVal(Instruction *I, Value *V){
            bool result = false;
            for (unsigned i = 0; i < I->getNumOperands(); i++) {
                if (Value *OPV = dyn_cast<Value>(I->getOperand(i))) {
                    if (OPV == V) {
                        //若Value等于操作数，即ICMP操作数来自于该Value，则返回真
                        return true;
                    }else if (Instruction *OPI = dyn_cast<Instruction>(OPV)){
                        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(OPI)) {
                            //若GEP指令操作数超过2个，则读取Value内部数据结构，这种情况不符合情况，返回假
                            if (GEP->getNumOperands() > 2) {
                                return false;
                            }
                        }
                        //若来自函数调用，这种情况不符合情况，返回假
                        if (CallInst *C = dyn_cast<CallInst>(OPV)) {
                            return false;
                        }
                        //函数中排出了一些不符合情况的特例，后面出现BUG，可能需要进一步添加特例
                        //除此之外，递归操作数是指令的的来源
                        result = instComeFromVal(OPI, V);
                    }
                }
            }
            return result;
        };
        
        
        
        //判断源类型是否为结构体（若干级指针或者直接为结构体）
        bool isSouceStructType(Type *T){
            if (T->isPointerTy() || T->isArrayTy()) {
                while (T->getContainedType(0)->isPointerTy()) {
                    T = T->getContainedType(0);
                }
                T = T->getContainedType(0);
            }
            return T->isStructTy();
        }
        
        //返回T的指针级数
        int pointerLevel(Type *T){
            int i = 0;
            if (T->isPointerTy()) {
                while (T->getContainedType(0)->isPointerTy()) {
                    T = T->getContainedType(0);
                    i++;
                }
                i++;
            }
            return i;
        }
        
        
        //获取level级指针的源类型
        Type* getSouType(Type *T, int level){
            if (level < 1) {
                return T;
            }else{
                for (int i = 0; i < level; i++) {
                    T = T->getContainedType(0);
                }
                return T;
            }
        }
        
        //获取指向T类型的level级指针
        Type* getPtrType(Type *T, int level){
            if (level < 1) {
                return T;
            }else{
                for (int i = 0; i < level; i++) {
                    T = llvm::PointerType::getUnqual(T);
                }
                return T;
            }
        }
        
        bool isStackPointer(Value *V) {
            if (isa<AllocaInst>(V)) {
                return true;
            }
            if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
                return isStackPointer(BC->getOperand(0));
            } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
                return isStackPointer(PI->getOperand(0));
            } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
                return isStackPointer(GEP->getPointerOperand());
            }
            
            return false;
        }
        
        bool isComeFormSouce(Value *V, Value*S) {
            if (V == S) {
                return true;
            }
            if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
                return isComeFormSouce(BC->getOperand(0), S);
            } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
                return isComeFormSouce(PI->getOperand(0), S);
            } else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
                return isComeFormSouce(LI->getPointerOperand(), S);
            }
            
            return false;
        }
        
        bool isComeFormLI(Value *V, Value *LI) {
            if (V == LI) {
                return true;
            }
            if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
                return isComeFormLI(BC->getOperand(0), LI);
            } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
                return isComeFormLI(PI->getOperand(0), LI);
            } else if (PHINode *phi = dyn_cast<PHINode>(V)) {
                bool ret = false;
                for (unsigned int i = 0; i < phi->getNumIncomingValues(); ++i) {
                    ret |= isComeFormLI(phi->getIncomingValue(i), LI);
                }
                return ret;
            }
            return false;
        }
        
        Value* isComeFormLoaclCall(Value *V) {
            if (CallInst *CI = dyn_cast<CallInst>(V)) {
                if (Function *fTemp = CI->getCalledFunction()) {
                    auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
                    if (index != localFunName.end()) {
                        return CI;
                    }
                }
            } else if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
                return isComeFormLoaclCall(BC->getOperand(0));
            } else if (PHINode *phi = dyn_cast<PHINode>(V)) {
                for (unsigned int i = 0; i < phi->getNumIncomingValues(); ++i) {
                    if (isComeFormLoaclCall(phi->getIncomingValue(i))) {
                        return isComeFormLoaclCall(phi->getIncomingValue(i));
                    }
                }
            }
            return NULL;
        }
        
        Value* getFirstLoadPtrOP(Value *V) {
            if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
                return getFirstLoadPtrOP(BC->getOperand(0));
            } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
                return getFirstLoadPtrOP(PI->getOperand(0));
            } else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
                return LI;
            }
            return NULL;
        }
        
        bool  isSIComeFromMalloc(StoreInst *SI, Value *M){
            if (SI->getValueOperand() == M) {
                return true;
            }else if (BitCastInst *BCI = dyn_cast<BitCastInst>(SI->getValueOperand())) {
                return isSIComeFromMalloc(SI, BCI);
            }
            return false;
        }
        
        bool  isComeFromGEPAndChange(Value *V){
            if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
                if ((dyn_cast<ConstantInt>(GEP->getOperand(1)))) {
                    (dyn_cast<ConstantInt>(GEP->getOperand(1)))->equalsInt(0);
                }
                #ifdef DEBUG
                errs() << "isComeFromGEPAndChange debug1\n";
                #endif
                if ((dyn_cast<ConstantInt>(GEP->getOperand(1)) && !((dyn_cast<ConstantInt>(GEP->getOperand(1)))->equalsInt(0))) || (GEP->getNumIndices() > 1)) {
                    #ifdef DEBUG
                    errs() << "isComeFromGEPAndChange debug2\n";
                    #endif
                    return true;
                } else {
                    #ifdef DEBUG
                    errs() << "isComeFromGEPAndChange debug3\n";
                    #endif
                    if (GetElementPtrInst *nGEP = dyn_cast<GetElementPtrInst>(GEP->getPointerOperand())) {
                        #ifdef DEBUG
                        errs() << "isComeFromGEPAndChange debug4\n";
                        #endif
                        return isComeFromGEPAndChange(GEP->getPointerOperand());
                    } else if (BitCastInst *BCI = dyn_cast<BitCastInst>(V)) {
                        #ifdef DEBUG
                        errs() << "isComeFromGEPAndChange debug5\n";
                        #endif
                        return isComeFromGEPAndChange(BCI->getOperand(0));
                    }
                }
            }else if (BitCastInst *BCI = dyn_cast<BitCastInst>(V)) {
                
                return isComeFromGEPAndChange(BCI->getOperand(0));
            }else if (BitCastOperator *BCO = dyn_cast<BitCastOperator>(V)) {
                return isComeFromGEPAndChange(BCO->getOperand(0));
            }else if (ConstantExpr *CE = dyn_cast<llvm::ConstantExpr>(V)) {
                if (CE->getOpcode() == Instruction::GetElementPtr) {
                    if (CE->getNumOperands() > 1) {
                        return true;
                    }
                }
            }
            return false;
        }
        
        Value *  getComeFromGEPAndChangeOrigin(Value *V){
            if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
//                errs() << "getComeFromGEPAndChangeOrigin1\n";
                
                if (((dyn_cast<ConstantInt>(GEP->getOperand(1))) && !dyn_cast<ConstantInt>(GEP->getOperand(1))->equalsInt(0)) || (GEP->getNumIndices() > 1)) {
//                    errs() << "getComeFromGEPAndChangeOrigin2\n";
                    return GEP->getPointerOperand();
                } else {
//                    errs() << "getComeFromGEPAndChangeOrigin3\n";
                    if (GetElementPtrInst *nGEP = dyn_cast<GetElementPtrInst>(GEP->getPointerOperand())) {
//                        errs() << "getComeFromGEPAndChangeOrigin4\n";
                        return getComeFromGEPAndChangeOrigin(GEP->getPointerOperand());
                    } else if (BitCastInst *BCI = dyn_cast<BitCastInst>(V)) {
//                        errs() << "getComeFromGEPAndChangeOrigin5\n";
                        return getComeFromGEPAndChangeOrigin(BCI->getOperand(0));
                    }
                }
//                errs() << "getComeFromGEPAndChangeOrigin6\n";
            }else if (BitCastInst *BCI = dyn_cast<BitCastInst>(V)) {
//                errs() << "getComeFromGEPAndChangeOrigin7\n";
                return getComeFromGEPAndChangeOrigin(BCI->getOperand(0));
            }else if (BitCastOperator *BCO = dyn_cast<BitCastOperator>(V)) {
//                errs() << "getComeFromGEPAndChangeOrigin8\n";
                return getComeFromGEPAndChangeOrigin(BCO->getOperand(0));
            }else if (ConstantExpr *CE = dyn_cast<llvm::ConstantExpr>(V)) {
//                errs() << "getComeFromGEPAndChangeOrigin9\n";
                if (CE->getOpcode() == Instruction::GetElementPtr) {
//                    errs() << "getComeFromGEPAndChangeOrigin10\n";
                    if (CE->getNumOperands() > 1) {
//                        errs() << "getComeFromGEPAndChangeOrigin11\n";
                        return CE->getOperand(0);
                    }
                }
            }
            return NULL;
        }
        
        CallInst* isSIValueComeFromMalloc(Value *V){
            if (CallInst *CI = dyn_cast<CallInst>(V)) {
                if (Function *fTemp = CI->getCalledFunction()) {
                    if (CI->getCalledFunction()->getName().equals("malloc")) {
                        return CI;
                    }
                }
            }else if (StoreInst *SI = dyn_cast<StoreInst>(V)) {
                return isSIValueComeFromMalloc(SI->getValueOperand());
            }else if (BitCastInst *BCI = dyn_cast<BitCastInst>(V)) {
                return isSIValueComeFromMalloc(BCI->getOperand(0));
            }
            return NULL;
        }
        
        void changTOSafeMalloc(Function *tmpF, CallInst *CI, StoreInst *SI, BasicBlock::iterator &nextInst) {
            CI->setCalledFunction(tmpF->getParent()->getFunction("safeMalloc"));
        }
        
//        bool isStdorPthreadType(Type *T){
//            StructType *ST = NULL;
//            if (pointerLevel(T) > 0) {
////                errs() << "isStdorPthreadType debug1\n";
//                ST = dyn_cast<StructType>(getSouType(T, pointerLevel(T)));
//            } else {
////                errs() << "isStdorPthreadType debug2\n";
//                ST = dyn_cast<StructType>(T);
//            }
//            if (ST) {
////                errs() << "isStdorPthreadType debug3\n";
//                if (ST->hasName() && (ST->getStructName().contains("std::") || ST->getStructName().contains("_pthread"))) {
////                    errs() << "isStdorPthreadType debug4\n";
//                    return true;
//                } else {
////                    errs() << "isStdorPthreadType debug5\n";
//                    for (unsigned i = 0; i < ST->getNumElements(); ++i) {
////                        errs() << "isStdorPthreadType debug6\n";
//                        if (isStdorPthreadTypeNoIter(ST->getElementType(i))) {
////                            errs() << "isStdorPthreadType debug7\n";
//                            return true;
//                        }
//                    }
//                }
//            }
////            errs() << "isStdorPthreadType debug8\n";
//            return false;
//        }
        
        bool isStdorPthreadType(Type *T){
            return false;
        }
        
        bool isStdorPthreadTypeNoIter(Type *T){
            StructType *ST = NULL;
            if (pointerLevel(T) > 0) {
                ST = dyn_cast<StructType>(getSouType(T, pointerLevel(T)));
            } else {
                ST = dyn_cast<StructType>(T);
            }
            if (ST) {
                if (ST->hasName() && (ST->getStructName().contains("std::") || ST->getStructName().contains("_pthread"))) {
                    return true;
                }
            }
            return false;
        }
        
        bool insertDPcheck(Function *tmpF, Function::iterator &bb, BasicBlock::iterator &inst, Value *value){
            {
                    int useNum = value->getNumUses();
                    int LIUseNum = 0;
                    int FunArgUseNum = 0;
//                #ifdef DEBUG
                errs() << "insertDPcheck value useNum: "<< useNum << '\n';
//                #endif
                    if(useNum >= 1){
                        //BUG:Bitcast转换以后要继续考虑是否为不需要转换的！！！
                        Function::iterator tmpBB = bb;
                        for (Function::iterator tmpBB = bb; tmpBB != tmpF->end(); ++tmpBB) {
                            for (BasicBlock::iterator inst2 = tmpBB->begin(); inst2 != tmpBB->end(); ++inst2) {
                                if (value == dyn_cast<Value>(inst2)) {
                                    continue;
                                }
                                if (useNum <= 0) {
                                    break;
                                }
                                if (StoreInst *SI = dyn_cast<StoreInst>(inst2)) {
                                    if (isComeFormLI(SI->getValueOperand(), value) && SI->getValueOperand()->getType()->isPointerTy()) {
                                        LIUseNum++;
//                                        useNum--;
                                        SI->dump();
                                        errs() << "StoreInst--!" << '\n';
                                        continue;
                                    }
                                } else if(CallInst *CI = dyn_cast<CallInst>(inst2)){
                                    if (Function *fTemp = CI->getCalledFunction()) {
                                        auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());

                                        if (index != localFunName.end()) {
//#ifdef DEBUG
                                            errs() << "find LocalFun!" << '\n';
                                            CI->dump();
//#endif
                                            for (Instruction::op_iterator oi = CI->op_begin(); oi != CI->op_end(); ++oi) {
                                                if (Value *V = dyn_cast<Value>(oi)) {
//#ifdef DEBUG
                                                    V->dump();
                                                    value->dump();
                                                    errs() << isComeFormLI(V, value) << '\n';
//#endif
                                                    if (isComeFormLI(V, value)) {
//#ifdef DEBUG
                                                        errs() << "find LocalFun use!" << '\n';
//#endif
                                                        LIUseNum++;
                                                        FunArgUseNum++;
//                                                        useNum--;
                                                        errs() << "LocalFun use--!" << '\n';
                                                        continue;
                                                    }
                                                }

                                            }
                                        }

                                    }else{
                                        for (Instruction::op_iterator oi = CI->op_begin(); oi != CI->op_end(); ++oi) {
                                            if (Value *V = dyn_cast<Value>(oi)) {
                                                if (isComeFormLI(V, value)) {
//#ifdef DEBUG
                                                    errs() << "find Function Pointer LI use!" << '\n';
//#endif
                                                    LIUseNum++;
                                                    FunArgUseNum++;
//                                                    useNum--;
                                                    errs() << "LocalFun Pointer use--!" << '\n';
                                                    continue;
                                                }
                                            }
                                        }
                                    }

                                } else if (ReturnInst *RI = dyn_cast<ReturnInst>(inst2)) {
//#ifdef DEBUG
                                    errs() << "RET debug:" << '\n';
                                    RI->dump();
//#endif
                                    if (RI->getReturnValue() && !(RI->getReturnValue()->getType()->isVoidTy()) && isComeFormLI(RI->getReturnValue(), value)) {
//#ifdef DEBUG
                                        errs() << "find RET use:" << '\n';
//#endif
                                        LIUseNum++;
//                                        useNum--;
                                        errs() << "RET use--!" << '\n';
                                        continue;
                                    }
                                }
                            }
                        }

                    }
//#ifdef DEBUG
                    errs() << "FunArgUseNum2:" << FunArgUseNum << '\n';
                    errs() << "useNum2:" << useNum << '\n';
//#endif
                    if (useNum > 0) {
//                        LoadInst *sameLI = new LoadInst(value->getPointerOperand(), "sameLI", &(*inst));
                        inst++;
                        Value *phi = insertLoadCheckInBasicBlock(tmpF, bb, inst, value);
                        errs() << "insertLoadCheckInBasicBlock:" << '\n';
                        phi->dump();
                        
                        inst--;
                        value->replaceAllUsesWith(phi);
                        if (LIUseNum > 0) {
//#ifdef DEBUG
                            errs() << "FunArgUseNum2:" << FunArgUseNum << '\n';
//#endif
                            Function::iterator tmpBB = bb;
                            for (Function::iterator tmpBB = bb; tmpBB != tmpF->end(); ++tmpBB) {
                                for (BasicBlock::iterator inst2 = tmpBB->begin(); inst2 != tmpBB->end(); ++inst2) {
                                    if (LIUseNum <= 0) {
                                        break;
                                    }
                                    if (StoreInst *SI = dyn_cast<StoreInst>(inst2)) {
                                        if (SI->getValueOperand() == phi && SI->getValueOperand()->getType()->isPointerTy()) {
                                            LIUseNum--;
                                            SI->setOperand(0, value);
                                        }
                                    } else if (FunArgUseNum > 0 && dyn_cast<CallInst>(inst2)) {
//#ifdef DEBUG
                                        errs() << "find CallInst!" << '\n';
//#endif
                                        if (CallInst *CI = dyn_cast<CallInst>(inst2)) {
                                            if (Function *fTemp = CI->getCalledFunction()) {
                                                auto index = std::find(localFunName.begin(), localFunName.end(), fTemp->getName().str());
//#ifdef DEBUG
                                                errs() << "chang FunArg:" << '\n';
//#endif
                                                if (index != localFunName.end()) {
                                                    for (unsigned i = 0; i < CI->getNumOperands(); ++i) {
                                                        if (Value *V = dyn_cast<Value>(CI->llvm::User::getOperand(i))) {
                                                            if (isComeFormSouce(V, phi)) {
//#ifdef DEBUG
                                                                bb->dump();
                                                                errs() << "chang FunArg:" << '\n';
                                                                CI->dump();
                                                                errs() << i << '\n';
                                                                value->dump();
//#endif
                                                                LIUseNum--;
                                                                FunArgUseNum--;
                                                                if (BitCastInst *BCI = dyn_cast<BitCastInst>(CI->getOperand(i))) {
                                                                    BitCastInst *nBCI = new BitCastInst(value, BCI->getType(), "", CI);
                                                                    CI->setOperand(i, nBCI);
                                                                    if (BCI->getNumUses() == 0) {
                                                                        BCI->eraseFromParent();
                                                                    }
                                                                } else {
                                                                    CI->setOperand(i, value);
                                                                }
                                                            }
                                                        }
                                                    }

                                                }
                                            }else{
                                                for (unsigned i = 0; i < CI->getNumOperands(); ++i) {
                                                    if (Value *V = dyn_cast<Value>(CI->llvm::User::getOperand(i))) {
                                                        if (isComeFormSouce(V, phi)) {
//#ifdef DEBUG
                                                            errs() << "chang FunArg:" << '\n';
                                                            CI->dump();
//#endif
                                                            LIUseNum--;
                                                            FunArgUseNum--;
                                                            if (BitCastInst *BCI = dyn_cast<BitCastInst>(CI->getOperand(i))) {
                                                                BitCastInst *nBCI = new BitCastInst(value, BCI->getType(), "", CI);
                                                                CI->setOperand(i, nBCI);
                                                                if (BCI->getNumUses() == 0) {
                                                                    BCI->eraseFromParent();
                                                                }
                                                            } else {
                                                                CI->setOperand(i, value);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }

                                    } else if (ReturnInst *RI = dyn_cast<ReturnInst>(inst2)) {
                                        if (RI->getReturnValue() && !(RI->getReturnValue()->getType()->isVoidTy()) && RI->getReturnValue() == phi) {
//#ifdef DEBUG
                                            errs() << "chang RetArg:" << '\n';
//#endif
                                            LIUseNum--;
                                            RI->setOperand(0, value);
                                        }
                                    }
                                }
                            }
                        }

                    }

            }
        }
        
    };
    
}

char MyPass::ID = 0;
static RegisterPass<MyPass> X("MyPass", "MyPass Pass");
Pass *createMyPass() { return new MyPass(); }
