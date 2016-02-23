/*
 *  Copyright (c) 2014-15 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <pablo/pablo_compiler.h>
#include <pablo/codegenstate.h>
#include <pablo/carry_data.h>
#include <pablo/carry_manager.h>
#include <pablo/printer_pablos.h>
#include <pablo/function.h>
#include <re/re_name.h>
#include <stdexcept>
#include <include/simd-lib/bitblock.hpp>
#include <sstream>
#include <IDISA/idisa_builder.h>
#include <IDISA/idisa_avx_builder.h>
#include <llvm/Pass.h>
#include <llvm/PassManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/Compiler.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/Host.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/ADT/Twine.h>
#include <iostream>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/FileSystem.h>
#ifndef NDEBUG
#include <llvm/IR/Verifier.h>
#endif

//#include <llvm/PassManager.h>
//#include <llvm/Transforms/IPO/PassManagerBuilder.h>

#include <hrtime.h>

static cl::OptionCategory eIRDumpOptions("LLVM IR Dump Options", "These options control dumping of LLVM IR.");
static cl::opt<bool> DumpGeneratedIR("dump-generated-IR", cl::init(false), cl::desc("Print LLVM IR generated by Pablo Compiler."), cl::cat(eIRDumpOptions));
static cl::opt<std::string> IROutputFilename("dump-generated-IR-output", cl::init(""), cl::desc("output IR filename"), cl::cat(eIRDumpOptions));


static cl::OptionCategory fTracingOptions("Run-time Tracing Options", "These options control execution traces.");
static cl::opt<bool> DumpTrace("dump-trace", cl::init(false), cl::desc("Generate dynamic traces of executed assignments."), cl::cat(fTracingOptions));

namespace pablo {

PabloCompiler::PabloCompiler(Module * m, IDISA::IDISA_Builder * b)
: mMod(m)
, iBuilder(b)
, mBitBlockType(b->getBitBlockType())
, mCarryManager(nullptr)
, mInputType(nullptr)
, mKBuilder(nullptr)
, mWhileDepth(0)
, mIfDepth(0)
, mFunction(nullptr)
, mInputAddressPtr(nullptr)
, mOutputAddressPtr(nullptr)
, mMaxWhileDepth(0)
, mFilePosIdx(2) {
    
}

PabloCompiler::~PabloCompiler() {
}
 
void PabloCompiler::setKernel(KernelBuilder * kBuilder){
    mKBuilder = kBuilder;   
} 

llvm::Function * PabloCompiler::compile(PabloFunction * function) {

    #ifdef PRINT_TIMING_INFORMATION
    const timestamp_t pablo_compilation_start = read_cycle_counter();
    #endif
  
    PabloBlock * const mainScope = function->getEntryBlock();

    mainScope->enumerateScopes(0);
    
    Examine(*function);

    mCarryManager = new CarryManager(iBuilder);

    GenerateKernel(mainScope, function);
       
    delete mCarryManager;
    mCarryManager = nullptr;
    
    #ifdef PRINT_TIMING_INFORMATION
    const timestamp_t pablo_compilation_end = read_cycle_counter();
    std::cerr << "PABLO COMPILATION TIME: " << (pablo_compilation_end - pablo_compilation_start) << std::endl;
    #endif


    if (LLVM_UNLIKELY(DumpGeneratedIR)) {

        if (IROutputFilename.empty()) {
            mMod->dump();
        } else {
            std::error_code error;
            llvm::raw_fd_ostream out(IROutputFilename, error, sys::fs::OpenFlags::F_None);
            mMod->print(out, nullptr);
        }
    }

    #ifndef NDEBUG
    raw_os_ostream err(std::cerr);
    verifyModule(*mMod, &err);
    #endif

    return mFunction;
}

inline void PabloCompiler::GenerateKernel(PabloBlock * mainScope, PabloFunction * function) {
  
    for(int i=0; i<8; i++){
        mKBuilder->addKernelInputStream(1, "basis_bits");
    }
    mKBuilder->addKernelOutputStream(1);
    mKBuilder->addKernelOutputStream(1);

    mCarryManager->initialize(mainScope, mKBuilder);
 
    int segBlocks = mKBuilder->getSegmentBlocks();
    mKBuilder->PrepareDoBlockFunction();
    struct Inputs inputs = mKBuilder->openDoBlock();
    struct Outputs outputs;
    mFunction = mKBuilder->getDoBlockFunction();

    mCarryManager->initialize_setPtrs(mKBuilder);

    valptr results[segBlocks][2];
    for(int j=0; j<segBlocks; j++){     
        for(int i=0; i<inputs.streams[j].size(); i++){
            mMarkerMap[function->getParameter(i)] = inputs.streams[j][i];
        }

        compileBlock(mainScope);

        Value * filePos = iBuilder->CreateAdd(mKBuilder->getKernelInternalState(mFilePosIdx), iBuilder->getInt64(iBuilder->getBitBlockWidth()));
        mKBuilder->changeKernelInternalState(mFilePosIdx, filePos);

        mCarryManager->set_BlockNo(mKBuilder);

        results[j][0] = mMarkerMap[function->getResult(0)];
        results[j][1] = mMarkerMap[function->getResult(1)];
        outputs.streams.push_back(results[j]);
    }    

    mKBuilder->closeDoBlock(outputs);
    mKBuilder->finalizeMethods();
}

inline void PabloCompiler::GenerateFunction(PabloFunction & function) {
    mInputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>(function.getNumOfParameters(), mBitBlockType)), 0);
    Type * outputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>(function.getNumOfResults(), mBitBlockType)), 0);
    FunctionType * functionType = FunctionType::get(Type::getVoidTy(mMod->getContext()), std::vector<Type *>({mInputType, outputType}), false);


    //Starts on process_block
    SmallVector<AttributeSet, 3> Attrs;
    Attrs.push_back(AttributeSet::get(mMod->getContext(), ~0U, std::vector<Attribute::AttrKind>({ Attribute::NoUnwind, Attribute::UWTable })));
    Attrs.push_back(AttributeSet::get(mMod->getContext(), 1U, std::vector<Attribute::AttrKind>({ Attribute::ReadOnly, Attribute::NoCapture })));
    Attrs.push_back(AttributeSet::get(mMod->getContext(), 2U, std::vector<Attribute::AttrKind>({ Attribute::ReadNone, Attribute::NoCapture })));
    AttributeSet AttrSet = AttributeSet::get(mMod->getContext(), Attrs);

    // Create the function that will be generated.
    mFunction = Function::Create(functionType, GlobalValue::ExternalLinkage, function.getName()->value(), mMod);
    mFunction->setCallingConv(CallingConv::C);
    mFunction->setAttributes(AttrSet);

    Function::arg_iterator args = mFunction->arg_begin();
    mInputAddressPtr = args++;
    mInputAddressPtr->setName("input");
    mOutputAddressPtr = args++;
    mOutputAddressPtr->setName("output");
}

inline void PabloCompiler::Examine(PabloFunction & function) {
    mWhileDepth = 0;
    mIfDepth = 0;
    mMaxWhileDepth = 0;
    Examine(function.getEntryBlock());
    if (LLVM_UNLIKELY(mWhileDepth != 0 || mIfDepth != 0)) {
        throw std::runtime_error("Malformed Pablo AST: Unbalanced If or While nesting depth!");
    }
}


void PabloCompiler::Examine(PabloBlock * block) {
    for (Statement * stmt : *block) {
        if (If * ifStatement = dyn_cast<If>(stmt)) {
            Examine(ifStatement->getBody());
        }
        else if (While * whileStatement = dyn_cast<While>(stmt)) {
            mMaxWhileDepth = std::max(mMaxWhileDepth, ++mWhileDepth);
            Examine(whileStatement->getBody());
            --mWhileDepth;
        }
    }
}

void PabloCompiler::compileBlock(PabloBlock * block) {
    mPabloBlock = block;
    for (const Statement * statement : *block) {
        compileStatement(statement);
    }
    mPabloBlock = block->getParent();
}

void PabloCompiler::compileIf(const If * ifStatement) {        
    //
    //  The If-ElseZero stmt:
    //  if <predicate:expr> then <body:stmt>* elsezero <defined:var>* endif
    //  If the value of the predicate is nonzero, then determine the values of variables
    //  <var>* by executing the given statements.  Otherwise, the value of the
    //  variables are all zero.  Requirements: (a) no variable that is defined within
    //  the body of the if may be accessed outside unless it is explicitly
    //  listed in the variable list, (b) every variable in the defined list receives
    //  a value within the body, and (c) the logical consequence of executing
    //  the statements in the event that the predicate is zero is that the
    //  values of all defined variables indeed work out to be 0.
    //
    //  Simple Implementation with Phi nodes:  a phi node in the if exit block
    //  is inserted for each variable in the defined variable list.  It receives
    //  a zero value from the ifentry block and the defined value from the if
    //  body.
    //

    BasicBlock * const ifEntryBlock = iBuilder->GetInsertBlock();
    BasicBlock * const ifBodyBlock = BasicBlock::Create(mMod->getContext(), "if.body", mFunction, 0);
    BasicBlock * const ifEndBlock = BasicBlock::Create(mMod->getContext(), "if.end", mFunction, 0);
    
    PabloBlock * ifBody = ifStatement->getBody();
    
    Value * const condition = compileExpression(ifStatement->getCondition());
    
    mCarryManager->enterScope(ifBody);
    iBuilder->CreateCondBr(mCarryManager->generateSummaryTest(condition), ifBodyBlock, ifEndBlock);
    
    // Entry processing is complete, now handle the body of the if.
    iBuilder->SetInsertPoint(ifBodyBlock);
    
    compileBlock(ifBody);
    BasicBlock * ifExitBlock = iBuilder->GetInsertBlock();

    if (mCarryManager->hasCarries()) {
        mCarryManager->storeCarryOutSummary();
    }
    mCarryManager->addOuterSummaryToNestedSummary();

    iBuilder->CreateBr(ifEndBlock);
    //End Block
    iBuilder->SetInsertPoint(ifEndBlock);
    for (const PabloAST * node : ifStatement->getDefined()) {
        const Assign * assign = cast<Assign>(node);
        PHINode * phi = iBuilder->CreatePHI(mBitBlockType, 2, assign->getName()->value());
        auto f = mMarkerMap.find(assign);
        assert (f != mMarkerMap.end());
        phi->addIncoming(iBuilder->allZeroes(), ifEntryBlock);
        phi->addIncoming(f->second, ifExitBlock);
        mMarkerMap[assign] = phi;
    }
    // Create the phi Node for the summary variable, if needed.
    mCarryManager->buildCarryDataPhisAfterIfBody(ifEntryBlock, ifExitBlock);
    mCarryManager->leaveScope();
}

void PabloCompiler::compileWhile(const While * whileStatement) {

    PabloBlock * const whileBody = whileStatement->getBody();
    
    BasicBlock * whileEntryBlock = iBuilder->GetInsertBlock();
    BasicBlock * whileBodyBlock = BasicBlock::Create(mMod->getContext(), "while.body", mFunction, 0);
    BasicBlock * whileEndBlock = BasicBlock::Create(mMod->getContext(), "while.end", mFunction, 0);

    mCarryManager->enterScope(whileBody);
    mCarryManager->ensureCarriesLoadedRecursive();

    const auto & nextNodes = whileStatement->getVariants();
    std::vector<PHINode *> nextPhis;
    nextPhis.reserve(nextNodes.size());

    // On entry to the while structure, proceed to execute the first iteration
    // of the loop body unconditionally.   The while condition is tested at the end of
    // the loop.

    iBuilder->CreateBr(whileBodyBlock);
    iBuilder->SetInsertPoint(whileBodyBlock);

    //
    // There are 3 sets of Phi nodes for the while loop.
    // (1) Carry-ins: (a) incoming carry data first iterations, (b) zero thereafter
    // (2) Carry-out accumulators: (a) zero first iteration, (b) |= carry-out of each iteration
    // (3) Next nodes: (a) values set up before loop, (b) modified values calculated in loop.

    mCarryManager->initializeWhileEntryCarryDataPhis(whileEntryBlock);

    // for any Next nodes in the loop body, initialize to (a) pre-loop value.
    for (const Next * n : nextNodes) {
        PHINode * phi = iBuilder->CreatePHI(mBitBlockType, 2, n->getName()->value());
        auto f = mMarkerMap.find(n->getInitial());
        assert (f != mMarkerMap.end());
        phi->addIncoming(f->second, whileEntryBlock);
        mMarkerMap[n->getInitial()] = phi;
        nextPhis.push_back(phi);
    }

    //
    // Now compile the loop body proper.  Carry-out accumulated values
    // and iterated values of Next nodes will be computed.
    ++mWhileDepth;
    compileBlock(whileBody);

    BasicBlock * whileExitBlock = iBuilder->GetInsertBlock();

    if (mCarryManager->hasCarries()) {
        mCarryManager->storeCarryOutSummary();
    }
    mCarryManager->finalizeWhileBlockCarryDataPhis(whileExitBlock);

    // Terminate the while loop body with a conditional branch back.
    iBuilder->CreateCondBr(iBuilder->bitblock_any(compileExpression(whileStatement->getCondition())), whileBodyBlock, whileEndBlock);

    // and for any Next nodes in the loop body
    for (unsigned i = 0; i < nextNodes.size(); i++) {
        const Next * n = nextNodes[i];
        auto f = mMarkerMap.find(n->getExpr());
        if (LLVM_UNLIKELY(f == mMarkerMap.end())) {
            throw std::runtime_error("Next node expression was not compiled!");
        }
        nextPhis[i]->addIncoming(f->second, whileExitBlock);
    }

    iBuilder->SetInsertPoint(whileEndBlock);
    --mWhileDepth;

    mCarryManager->ensureCarriesStoredRecursive();
    mCarryManager->leaveScope();
}


void PabloCompiler::compileStatement(const Statement * stmt) {
    Value * expr = nullptr;
    if (const Assign * assign = dyn_cast<const Assign>(stmt)) {
        expr = compileExpression(assign->getExpression());
    }
    else if (const Next * next = dyn_cast<const Next>(stmt)) {
        expr = compileExpression(next->getExpr());
    }
    else if (const If * ifStatement = dyn_cast<const If>(stmt)) {
        compileIf(ifStatement);
        return;
    }
    else if (const While * whileStatement = dyn_cast<const While>(stmt)) {
        compileWhile(whileStatement);
        return;
    }
    else if (const Call* call = dyn_cast<Call>(stmt)) {
        // Call the callee once and store the result in the marker map.
        if (mMarkerMap.count(call)) {
            return;
        }

        const Prototype * proto = call->getPrototype();
        const String * callee = proto->getName();

        Type * inputType = StructType::get(mMod->getContext(), std::vector<Type *>{proto->getNumOfParameters(), mBitBlockType});
        Type * outputType = StructType::get(mMod->getContext(), std::vector<Type *>{proto->getNumOfResults(), mBitBlockType});
        FunctionType * functionType = FunctionType::get(Type::getVoidTy(mMod->getContext()), std::vector<Type *>{PointerType::get(inputType, 0), PointerType::get(outputType, 0)}, false);

        //Starts on process_block
        SmallVector<AttributeSet, 3> Attrs;
        Attrs.push_back(AttributeSet::get(mMod->getContext(), 1U, std::vector<Attribute::AttrKind>({ Attribute::ReadOnly, Attribute::NoCapture })));
        Attrs.push_back(AttributeSet::get(mMod->getContext(), 2U, std::vector<Attribute::AttrKind>({ Attribute::ReadNone, Attribute::NoCapture })));
        AttributeSet AttrSet = AttributeSet::get(mMod->getContext(), Attrs);

        Function * externalFunction = cast<Function>(mMod->getOrInsertFunction(callee->value(), functionType, AttrSet));
        if (LLVM_UNLIKELY(externalFunction == nullptr)) {
            throw std::runtime_error("Could not create static method call for external function \"" + callee->to_string() + "\"");
        }
        externalFunction->setCallingConv(llvm::CallingConv::C);


        AllocaInst * outputStruct = iBuilder->CreateAlloca(outputType);
        iBuilder->CreateCall2(externalFunction, mInputAddressPtr, outputStruct);
        Value * outputPtr = iBuilder->CreateGEP(outputStruct, std::vector<Value *>({ iBuilder->getInt32(0), iBuilder->getInt32(0) }));
        expr = iBuilder->CreateAlignedLoad(outputPtr, iBuilder->getBitBlockWidth() / 8, false);
    }
    else if (const And * pablo_and = dyn_cast<And>(stmt)) {
        expr = iBuilder->simd_and(compileExpression(pablo_and->getOperand(0)), compileExpression(pablo_and->getOperand(1)));
    }
    else if (const Or * pablo_or = dyn_cast<Or>(stmt)) {
        expr = iBuilder->simd_or(compileExpression(pablo_or->getOperand(0)), compileExpression(pablo_or->getOperand(1)));
    }
    else if (const Xor * pablo_xor = dyn_cast<Xor>(stmt)) {
        expr = iBuilder->simd_xor(compileExpression(pablo_xor->getOperand(0)), compileExpression(pablo_xor->getOperand(1)));
    }
    else if (const Sel * sel = dyn_cast<Sel>(stmt)) {
        Value* ifMask = compileExpression(sel->getCondition());
        Value* ifTrue = iBuilder->simd_and(ifMask, compileExpression(sel->getTrueExpr()));
        Value* ifFalse = iBuilder->simd_and(iBuilder->simd_not(ifMask), compileExpression(sel->getFalseExpr()));
        expr = iBuilder->simd_or(ifTrue, ifFalse);
    }
    else if (const Not * pablo_not = dyn_cast<Not>(stmt)) {
        expr = iBuilder->simd_not(compileExpression(pablo_not->getExpr()));
    }
    else if (const Advance * adv = dyn_cast<Advance>(stmt)) {
        Value * const strm_value = compileExpression(adv->getExpr());
        expr = mCarryManager->advanceCarryInCarryOut(adv->getLocalAdvanceIndex(), adv->getAdvanceAmount(), strm_value);
    }
    else if (const Mod64Advance * adv = dyn_cast<Mod64Advance>(stmt)) {
        Value * const strm_value = compileExpression(adv->getExpr());
        expr = iBuilder->simd_slli(64, strm_value, adv->getAdvanceAmount());
    }
    else if (const MatchStar * mstar = dyn_cast<MatchStar>(stmt)) {
        Value * const marker = compileExpression(mstar->getMarker());
        Value * const cc = compileExpression(mstar->getCharClass());
        Value * const marker_and_cc = iBuilder->simd_and(marker, cc);
        Value * const sum = mCarryManager->addCarryInCarryOut(mstar->getLocalCarryIndex(), marker_and_cc, cc);
        expr = iBuilder->simd_or(iBuilder->simd_xor(sum, cc), marker);
    }
    else if (const Mod64MatchStar * mstar = dyn_cast<Mod64MatchStar>(stmt)) {
        Value * const marker = compileExpression(mstar->getMarker());
        Value * const cc = compileExpression(mstar->getCharClass());
        Value * const marker_and_cc = iBuilder->simd_and(marker, cc);
        Value * const sum = iBuilder->simd_add(64, marker_and_cc, cc);
        expr = iBuilder->simd_or(iBuilder->simd_xor(sum, cc), marker);
    }
    else if (const ScanThru * sthru = dyn_cast<ScanThru>(stmt)) {
        Value * const  marker_expr = compileExpression(sthru->getScanFrom());
        Value * const  cc_expr = compileExpression(sthru->getScanThru());
        Value * const  sum = mCarryManager->addCarryInCarryOut(sthru->getLocalCarryIndex(), marker_expr, cc_expr);
        expr = iBuilder->simd_and(sum, iBuilder->simd_not(cc_expr));
    }
    else if (const Mod64ScanThru * sthru = dyn_cast<Mod64ScanThru>(stmt)) {
        Value * const marker_expr = compileExpression(sthru->getScanFrom());
        Value * const cc_expr = compileExpression(sthru->getScanThru());
        Value * const sum = iBuilder->simd_add(64, marker_expr, cc_expr);
        expr = iBuilder->simd_and(sum, iBuilder->simd_not(cc_expr));
    }
    else if (const Count * c = dyn_cast<Count>(stmt)) {
        Value * const to_count = compileExpression(c->getExpr());
        expr = mCarryManager->popCount(to_count, c->getGlobalCountIndex());
    } else {
        std::string tmp;
        llvm::raw_string_ostream msg(tmp);
        msg << "Internal error: ";
        PabloPrinter::print(stmt, msg);
        msg << " is not a recognized statement in the Pablo compiler.";
        throw std::runtime_error(msg.str());
    }
    mMarkerMap[stmt] = expr;
    if (DumpTrace) {
        iBuilder->genPrintRegister(stmt->getName()->to_string(), expr);
    }
    
}

Value * PabloCompiler::compileExpression(const PabloAST * expr) {
    if (isa<Ones>(expr)) {
        return iBuilder->allOnes();
    }
    else if (isa<Zeroes>(expr)) {
        return iBuilder->allZeroes();
    }
    auto f = mMarkerMap.find(expr);
    if (LLVM_UNLIKELY(f == mMarkerMap.end())) {
        std::string o;
        llvm::raw_string_ostream str(o);
        str << "\"";
        PabloPrinter::print(expr, str);
        str << "\" was used before definition!";
        throw std::runtime_error(str.str());
    }
    return f->second;
}

void PabloCompiler::SetOutputValue(Value * marker, const unsigned index) {
    if (LLVM_UNLIKELY(marker == nullptr)) {
        throw std::runtime_error("Cannot set result " + std::to_string(index) + " to Null");
    }
    if (LLVM_UNLIKELY(marker->getType()->isPointerTy())) {
        marker = iBuilder->CreateAlignedLoad(marker, iBuilder->getBitBlockWidth()/8, false);
    }
    Value* indices[] = {iBuilder->getInt64(0), iBuilder->getInt32(index)};
    Value* gep = iBuilder->CreateGEP(mOutputAddressPtr, indices);
    if (marker->getType() != mBitBlockType) {
        marker = iBuilder->CreateBitCast(marker, mBitBlockType);
    }
    iBuilder->CreateAlignedStore(marker, gep, iBuilder->getBitBlockWidth()/8, false);
}

}
