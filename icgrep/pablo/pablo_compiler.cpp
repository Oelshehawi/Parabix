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
#include <cc/cc_namemap.hpp>
#include <re/re_name.h>
#include <stdexcept>
#include <include/simd-lib/bitblock.hpp>
#include <sstream>
#include <IDISA/idisa_builder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Pass.h>
#include <llvm/PassManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
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
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/MCJIT.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/ADT/Twine.h>
#include <iostream>

static cl::OptionCategory eIRDumpOptions("LLVM IR Dump Options", "These options control dumping of LLVM IR.");
static cl::opt<bool> DumpGeneratedIR("dump-generated-IR", cl::init(false), cl::desc("print LLVM IR generated by RE compilation"), cl::cat(eIRDumpOptions));

static cl::OptionCategory fTracingOptions("Run-time Tracing Options", "These options control execution traces.");
static cl::opt<bool> TraceNext("trace-next-nodes", cl::init(false), cl::desc("Generate dynamic traces of executed Next nodes (while control variables)."), cl::cat(fTracingOptions));
static cl::opt<bool> DumpTrace("dump-trace", cl::init(false), cl::desc("Generate dynamic traces of executed assignments."), cl::cat(fTracingOptions));

extern "C" {
  void wrapped_print_register(char * regName, BitBlock bit_block) {
      print_register<BitBlock>(regName, bit_block);
  }
}

namespace pablo {

PabloCompiler::PabloCompiler()
: mMod(nullptr)
, mBuilder(nullptr)
, mCarryManager(nullptr)
, mBitBlockType(VectorType::get(IntegerType::get(getGlobalContext(), 64), BLOCK_SIZE / 64))
, iBuilder(mBitBlockType)
, mInputType(nullptr)
, mCarryDataPtr(nullptr)
, mWhileDepth(0)
, mIfDepth(0)
, mZeroInitializer(ConstantAggregateZero::get(mBitBlockType))
, mOneInitializer(ConstantVector::getAllOnesValue(mBitBlockType))
, mFunction(nullptr)
, mInputAddressPtr(nullptr)
, mOutputAddressPtr(nullptr)
, mMaxWhileDepth(0)
, mPrintRegisterFunction(nullptr) {

}

PabloCompiler::~PabloCompiler() {
}
    
void PabloCompiler::InstallExternalFunction(std::string C_fn_name, void * fn_ptr, const size_t carrySize) {
    mExternalMap.insert(std::make_pair(C_fn_name, fn_ptr));
}

void PabloCompiler::genPrintRegister(std::string regName, Value * bitblockValue) {
    Constant * regNameData = ConstantDataArray::getString(mMod->getContext(), regName);
    GlobalVariable *regStrVar = new GlobalVariable(*mMod,
                                                   ArrayType::get(IntegerType::get(mMod->getContext(), 8), regName.length()+1),
                                                   /*isConstant=*/ true,
                                                   /*Linkage=*/ GlobalValue::PrivateLinkage,
                                                   /*Initializer=*/ regNameData);
    Value * regStrPtr = mBuilder->CreateGEP(regStrVar, {mBuilder->getInt64(0), mBuilder->getInt32(0)});
    mBuilder->CreateCall(mPrintRegisterFunction, {regStrPtr, bitblockValue});
}

CompiledPabloFunction PabloCompiler::compile(PabloFunction & function) {

    Examine(function);

    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    Module * module = new Module("", getGlobalContext());

    mMod = module;

    std::string errMessage;
    #ifdef USE_LLVM_3_5
    EngineBuilder builder(mMod);
    #else
    EngineBuilder builder(std::move(std::unique_ptr<Module>(mMod)));
    #endif
    builder.setErrorStr(&errMessage);
    builder.setMCPU(sys::getHostCPUName());
    #ifdef USE_LLVM_3_5
    builder.setUseMCJIT(true);
    #endif
    builder.setOptLevel(mMaxWhileDepth ? CodeGenOpt::Level::Less : CodeGenOpt::Level::None);
    ExecutionEngine * engine = builder.create();
    if (engine == nullptr) {
        throw std::runtime_error("Could not create ExecutionEngine: " + errMessage);
    }
    DeclareFunctions(engine);
    DeclareCallFunctions(engine);

    auto func = compile(function, mMod);

    //Display the IR that has been generated by this module.
    if (LLVM_UNLIKELY(DumpGeneratedIR)) {
        module->dump();
    }
    //Create a verifier.  The verifier will print an error message if our module is malformed in any way.
    verifyModule(*module, &dbgs());

    engine->finalizeObject();

    return CompiledPabloFunction(func.second, func.first, engine);
}

std::pair<llvm::Function *, size_t> PabloCompiler::compile(PabloFunction & function, Module * module) {

    Examine(function);

    mMod = module;

    mBuilder = new IRBuilder<>(mMod->getContext());

    iBuilder.initialize(mMod, mBuilder);

    mCarryManager = new CarryManager(mBuilder, mBitBlockType, mZeroInitializer, mOneInitializer, &iBuilder);

    GenerateFunction(function);

    mBuilder->SetInsertPoint(BasicBlock::Create(mMod->getContext(), "entry", mFunction,0));

    //The basis bits structure
    for (unsigned i = 0; i != function.getParameters().size(); ++i) {
        Value* indices[] = {mBuilder->getInt64(0), mBuilder->getInt32(i)};
        Value * gep = mBuilder->CreateGEP(mInputAddressPtr, indices);
        LoadInst * basisBit = mBuilder->CreateAlignedLoad(gep, BLOCK_SIZE/8, false, function.getParameter(i)->getName()->to_string());
        mMarkerMap.insert(std::make_pair(function.getParameter(i), basisBit));
        if (DumpTrace) {
            genPrintRegister(function.getParameter(i)->getName()->to_string(), basisBit);
        }
    }
        
    unsigned totalCarryDataSize = mCarryManager->initialize(&(function.getEntryBlock()), mCarryDataPtr);
    
    //Generate the IR instructions for the function.
    compileBlock(function.getEntryBlock());
    
    mCarryManager->generateBlockNoIncrement();

    if (DumpTrace || TraceNext) {
        genPrintRegister("mBlockNo", mBuilder->CreateAlignedLoad(mBuilder->CreateBitCast(mCarryManager->getBlockNoPtr(), PointerType::get(mBitBlockType, 0)), BLOCK_SIZE/8, false));
    }
    
    // Write the output values out
    for (unsigned i = 0; i != function.getResults().size(); ++i) {
        SetOutputValue(mMarkerMap[function.getResult(i)], i);
    }

    //Terminate the block
    ReturnInst::Create(mMod->getContext(), mBuilder->GetInsertBlock());

    // Clean up
    delete mCarryManager; mCarryManager = nullptr;
    delete mBuilder; mBuilder = nullptr;
    mMod = nullptr; // don't delete this. It's either owned by the ExecutionEngine or the calling function.

    //Return the required size of the carry data area to the process_block function.
    return std::make_pair(mFunction, totalCarryDataSize * sizeof(BitBlock));
}

inline void PabloCompiler::GenerateFunction(PabloFunction & function) {
    mInputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>(function.getParameters().size(), mBitBlockType)), 0);
    Type * carryType = PointerType::get(mBitBlockType, 0);
    Type * outputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>(function.getResults().size(), mBitBlockType)), 0);
    FunctionType * functionType = FunctionType::get(Type::getVoidTy(mMod->getContext()), {{mInputType, carryType, outputType}}, false);

#ifdef USE_UADD_OVERFLOW
#ifdef USE_TWO_UADD_OVERFLOW
    // Type Definitions for llvm.uadd.with.overflow.carryin.i128 or .i256
    std::vector<Type*>StructTy_0_fields;
    StructTy_0_fields.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    StructTy_0_fields.push_back(IntegerType::get(mMod->getContext(), 1));
    StructType *StructTy_0 = StructType::get(mMod->getContext(), StructTy_0_fields, /*isPacked=*/false);

    std::vector<Type*>FuncTy_1_args;
    FuncTy_1_args.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    FuncTy_1_args.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    FunctionType* FuncTy_1 = FunctionType::get(
                                              /*Result=*/StructTy_0,
                                              /*Params=*/FuncTy_1_args,
                                              /*isVarArg=*/false);

    mFunctionUaddOverflow = mMod->getFunction("llvm.uadd.with.overflow.i" +
                                              std::to_string(BLOCK_SIZE));
    if (!mFunctionUaddOverflow) {
        mFunctionUaddOverflow= Function::Create(
          /*Type=*/ FuncTy_1,
          /*Linkage=*/ GlobalValue::ExternalLinkage,
          /*Name=*/ "llvm.uadd.with.overflow.i" + std::to_string(BLOCK_SIZE), mMod); // (external, no body)
        mFunctionUaddOverflow->setCallingConv(CallingConv::C);
    }
    AttributeSet mFunctionUaddOverflowPAL;
    {
        SmallVector<AttributeSet, 4> Attrs;
        AttributeSet PAS;
        {
          AttrBuilder B;
          B.addAttribute(Attribute::NoUnwind);
          B.addAttribute(Attribute::ReadNone);
          PAS = AttributeSet::get(mMod->getContext(), ~0U, B);
        }

        Attrs.push_back(PAS);
        mFunctionUaddOverflowPAL = AttributeSet::get(mMod->getContext(), Attrs);
    }
    mFunctionUaddOverflow->setAttributes(mFunctionUaddOverflowPAL);
#else
    // Type Definitions for llvm.uadd.with.overflow.carryin.i128 or .i256
    std::vector<Type*>StructTy_0_fields;
    StructTy_0_fields.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    StructTy_0_fields.push_back(IntegerType::get(mMod->getContext(), 1));
    StructType *StructTy_0 = StructType::get(mMod->getContext(), StructTy_0_fields, /*isPacked=*/false);

    std::vector<Type*>FuncTy_1_args;
    FuncTy_1_args.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    FuncTy_1_args.push_back(IntegerType::get(mMod->getContext(), BLOCK_SIZE));
    FuncTy_1_args.push_back(IntegerType::get(mMod->getContext(), 1));
    FunctionType* FuncTy_1 = FunctionType::get(
                                              /*Result=*/StructTy_0,
                                              /*Params=*/FuncTy_1_args,
                                              /*isVarArg=*/false);

    mFunctionUaddOverflowCarryin = mMod->getFunction("llvm.uadd.with.overflow.carryin.i" +
                                              std::to_string(BLOCK_SIZE));
    if (!mFunctionUaddOverflowCarryin) {
        mFunctionUaddOverflowCarryin = Function::Create(
          /*Type=*/ FuncTy_1,
          /*Linkage=*/ GlobalValue::ExternalLinkage,
          /*Name=*/ "llvm.uadd.with.overflow.carryin.i" + std::to_string(BLOCK_SIZE), mMod); // (external, no body)
        mFunctionUaddOverflowCarryin->setCallingConv(CallingConv::C);
    }
    AttributeSet mFunctionUaddOverflowCarryinPAL;
    {
        SmallVector<AttributeSet, 4> Attrs;
        AttributeSet PAS;
        {
          AttrBuilder B;
          B.addAttribute(Attribute::NoUnwind);
          B.addAttribute(Attribute::ReadNone);
          PAS = AttributeSet::get(mMod->getContext(), ~0U, B);
        }

        Attrs.push_back(PAS);
        mFunctionUaddOverflowCarryinPAL = AttributeSet::get(mMod->getContext(), Attrs);
    }
    mFunctionUaddOverflowCarryin->setAttributes(mFunctionUaddOverflowCarryinPAL);
#endif
#endif

    //Starts on process_block
    SmallVector<AttributeSet, 4> Attrs;
    Attrs.push_back(AttributeSet::get(mMod->getContext(), ~0U, { Attribute::NoUnwind, Attribute::UWTable }));
    Attrs.push_back(AttributeSet::get(mMod->getContext(), 1U, { Attribute::ReadOnly, Attribute::NoCapture }));
    Attrs.push_back(AttributeSet::get(mMod->getContext(), 2U, { Attribute::NoCapture }));
    Attrs.push_back(AttributeSet::get(mMod->getContext(), 3U, { Attribute::ReadNone, Attribute::NoCapture }));
    AttributeSet AttrSet = AttributeSet::get(mMod->getContext(), Attrs);

    // Create the function that will be generated.
    mFunction = Function::Create(functionType, GlobalValue::ExternalLinkage, function.getName()->value(), mMod);
    mFunction->setCallingConv(CallingConv::C);
    mFunction->setAttributes(AttrSet);

    Function::arg_iterator args = mFunction->arg_begin();
    mInputAddressPtr = args++;
    mInputAddressPtr->setName("input");
    mCarryDataPtr = args++;
    mCarryDataPtr->setName("carry");
    mOutputAddressPtr = args++;
    mOutputAddressPtr->setName("output");
}

inline void PabloCompiler::Examine(PabloFunction & function) {
    if (mMod == nullptr) {

        mWhileDepth = 0;
        mIfDepth = 0;
        mMaxWhileDepth = 0;

        Examine(function.getEntryBlock());

        if (LLVM_UNLIKELY(mWhileDepth != 0 || mIfDepth != 0)) {
            throw std::runtime_error("Malformed Pablo AST: Unbalanced If or While nesting depth!");
        }
    }
}


void PabloCompiler::Examine(PabloBlock & block) {
    for (Statement * stmt : block) {
        if (Call * call = dyn_cast<Call>(stmt)) {
            mCalleeMap.insert(std::make_pair(call->getCallee(), nullptr));
        }
        else if (If * ifStatement = dyn_cast<If>(stmt)) {
            Examine(ifStatement->getBody());
        }
        else if (While * whileStatement = dyn_cast<While>(stmt)) {
            mMaxWhileDepth = std::max(mMaxWhileDepth, ++mWhileDepth);
            Examine(whileStatement->getBody());
            --mWhileDepth;
        }
    }
}

inline void PabloCompiler::DeclareFunctions(ExecutionEngine * const engine) {
    if (DumpTrace || TraceNext) {
        //This function can be used for testing to print the contents of a register from JIT'd code to the terminal window.
        mPrintRegisterFunction = mMod->getOrInsertFunction("wrapped_print_register", Type::getVoidTy(mMod->getContext()), Type::getInt8PtrTy(mMod->getContext()), mBitBlockType, NULL);
        if (engine) engine->addGlobalMapping(cast<GlobalValue>(mPrintRegisterFunction), (void *)&wrapped_print_register);
    }
}
    
void PabloCompiler::DeclareCallFunctions(ExecutionEngine * const engine) {
    for (auto mapping : mCalleeMap) {
        const String * callee = mapping.first;
        auto ei = mExternalMap.find(callee->value());
        if (ei != mExternalMap.end()) {

            Type * inputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>{8, mBitBlockType}), 0);
            Type * carryType = PointerType::get(mBitBlockType, 0);
            Type * outputType = PointerType::get(StructType::get(mMod->getContext(), std::vector<Type *>{1, mBitBlockType}), 0);
            FunctionType * functionType = FunctionType::get(Type::getVoidTy(mMod->getContext()), std::vector<Type *>{inputType, carryType, outputType}, false);

            //Starts on process_block
            SmallVector<AttributeSet, 3> Attrs;
            Attrs.push_back(AttributeSet::get(mMod->getContext(), 1U, { Attribute::ReadOnly, Attribute::NoCapture }));
            Attrs.push_back(AttributeSet::get(mMod->getContext(), 2U, { Attribute::NoCapture }));
            Attrs.push_back(AttributeSet::get(mMod->getContext(), 3U, { Attribute::ReadNone, Attribute::NoCapture }));
            AttributeSet AttrSet = AttributeSet::get(mMod->getContext(), Attrs);

            Function * externalFunction = cast<Function>(mMod->getOrInsertFunction(callee->value(), functionType, AttrSet));
            if (LLVM_UNLIKELY(externalFunction == nullptr)) {
                throw std::runtime_error("Could not create static method call for external function \"" + callee->to_string() + "\"");
            }
            externalFunction->setCallingConv(llvm::CallingConv::C);

            if (engine) engine->addGlobalMapping(externalFunction, ei->second);
            mCalleeMap[callee] = externalFunction;
        }
        else {
            throw std::runtime_error("External function \"" + callee->to_string() + "\" not installed");
        }
    }
}

void PabloCompiler::compileBlock(PabloBlock & block) {
    mPabloBlock = & block;
    for (const Statement * statement : block) {
        compileStatement(statement);
    }
    mPabloBlock = block.getParent();
}

Value * PabloCompiler::genBitTest2(Value * e1, Value * e2) {
    Type * t1 = e1->getType();
    Type * t2 = e2->getType();
    if (t1 == mBitBlockType) {
        if (t2 == mBitBlockType) {
            return iBuilder.bitblock_any(mBuilder->CreateOr(e1, e2));
        }
        else {
            Value * m1 = mBuilder->CreateZExt(iBuilder.hsimd_signmask(16, e1), t2);
            return mBuilder->CreateICmpNE(mBuilder->CreateOr(m1, e2), ConstantInt::get(t2, 0));
        }
    }
    else if (t2 == mBitBlockType) {
        Value * m2 = mBuilder->CreateZExt(iBuilder.hsimd_signmask(16, e2), t1);
        return mBuilder->CreateICmpNE(mBuilder->CreateOr(e1, m2), ConstantInt::get(t1, 0));
    }
    else {
        return mBuilder->CreateICmpNE(mBuilder->CreateOr(e1, e2), ConstantInt::get(t1, 0));
    }
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

    BasicBlock * ifEntryBlock = mBuilder->GetInsertBlock();
    BasicBlock * ifBodyBlock = BasicBlock::Create(mMod->getContext(), "if.body", mFunction, 0);
    BasicBlock * ifEndBlock = BasicBlock::Create(mMod->getContext(), "if.end", mFunction, 0);
    
    PabloBlock & ifBody = ifStatement -> getBody();
    
    Value * if_test_value = compileExpression(ifStatement->getCondition());
    
    mCarryManager->enterScope(&ifBody);
    if (mCarryManager->blockHasCarries()) {
        // load the summary variable
        Value* last_if_pending_data = mCarryManager->getCarrySummaryExpr();
        mBuilder->CreateCondBr(genBitTest2(if_test_value, last_if_pending_data), ifBodyBlock, ifEndBlock);

    }
    else {
        mBuilder->CreateCondBr(iBuilder.bitblock_any(if_test_value), ifBodyBlock, ifEndBlock);
    }
    // Entry processing is complete, now handle the body of the if.
    mBuilder->SetInsertPoint(ifBodyBlock);
    
    
    ++mIfDepth;
    compileBlock(ifBody);
    --mIfDepth;
    if (mCarryManager->blockHasCarries()) {
        mCarryManager->generateCarryOutSummaryCodeIfNeeded();
    }
    BasicBlock * ifBodyFinalBlock = mBuilder->GetInsertBlock();
    mBuilder->CreateBr(ifEndBlock);
    //End Block
    mBuilder->SetInsertPoint(ifEndBlock);
    for (const PabloAST * node : ifStatement->getDefined()) {
        const Assign * assign = cast<Assign>(node);
        PHINode * phi = mBuilder->CreatePHI(mBitBlockType, 2, assign->getName()->value());
        auto f = mMarkerMap.find(assign);
        assert (f != mMarkerMap.end());
        phi->addIncoming(mZeroInitializer, ifEntryBlock);
        phi->addIncoming(f->second, ifBodyFinalBlock);
        mMarkerMap[assign] = phi;
    }
    // Create the phi Node for the summary variable, if needed.
    mCarryManager->addSummaryPhiIfNeeded(ifEntryBlock, ifBodyFinalBlock);
    mCarryManager->leaveScope();
}

void PabloCompiler::compileWhile(const While * whileStatement) {

    PabloBlock & whileBody = whileStatement -> getBody();
    
    BasicBlock * whileEntryBlock = mBuilder->GetInsertBlock();
    BasicBlock * whileBodyBlock = BasicBlock::Create(mMod->getContext(), "while.body", mFunction, 0);
    BasicBlock * whileEndBlock = BasicBlock::Create(mMod->getContext(), "while.end", mFunction, 0);

    mCarryManager->enterScope(&whileBody);
    mCarryManager->ensureCarriesLoadedRecursive();

    const auto & nextNodes = whileStatement->getVariants();
    std::vector<PHINode *> nextPhis;
    nextPhis.reserve(nextNodes.size());

    // On entry to the while structure, proceed to execute the first iteration
    // of the loop body unconditionally.   The while condition is tested at the end of
    // the loop.

    mBuilder->CreateBr(whileBodyBlock);
    mBuilder->SetInsertPoint(whileBodyBlock);

    //
    // There are 3 sets of Phi nodes for the while loop.
    // (1) Carry-ins: (a) incoming carry data first iterations, (b) zero thereafter
    // (2) Carry-out accumulators: (a) zero first iteration, (b) |= carry-out of each iteration
    // (3) Next nodes: (a) values set up before loop, (b) modified values calculated in loop.

    mCarryManager->initializeCarryDataPhisAtWhileEntry(whileEntryBlock);

    // for any Next nodes in the loop body, initialize to (a) pre-loop value.
    for (const Next * n : nextNodes) {
        PHINode * phi = mBuilder->CreatePHI(mBitBlockType, 2, n->getName()->value());
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

    BasicBlock * whileBodyFinalBlock = mBuilder->GetInsertBlock();

    mCarryManager->extendCarryDataPhisAtWhileBodyFinalBlock(whileBodyFinalBlock);

    // Terminate the while loop body with a conditional branch back.
    mBuilder->CreateCondBr(iBuilder.bitblock_any(compileExpression(whileStatement->getCondition())), whileBodyBlock, whileEndBlock);

    // and for any Next nodes in the loop body
    for (unsigned i = 0; i < nextNodes.size(); i++) {
        const Next * n = nextNodes[i];
        auto f = mMarkerMap.find(n->getExpr());
        if (LLVM_UNLIKELY(f == mMarkerMap.end())) {
            throw std::runtime_error("Next node expression was not compiled!");
        }
        nextPhis[i]->addIncoming(f->second, whileBodyFinalBlock);
    }

    mBuilder->SetInsertPoint(whileEndBlock);
    if (mCarryManager->blockHasCarries()) {
        mCarryManager->generateCarryOutSummaryCodeIfNeeded();
    }
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
        if (TraceNext) {
            genPrintRegister(next->getName()->to_string(), expr);
        }
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
        //Call the callee once and store the result in the marker map.
        if (mMarkerMap.count(call) != 0) {
            return;
        }
        auto ci = mCalleeMap.find(call->getCallee());
        if (LLVM_UNLIKELY(ci == mCalleeMap.end())) {
            throw std::runtime_error("Unexpected error locating static function for \"" + call->getCallee()->to_string() + "\"");
        }       

        Function * function = ci->second;
        auto arg = function->getArgumentList().begin();
        Value * carryFramePtr = ConstantPointerNull::get(cast<PointerType>((++arg)->getType()));
        AllocaInst * outputStruct = mBuilder->CreateAlloca(cast<PointerType>((++arg)->getType())->getElementType());
        mBuilder->CreateCall3(function, mInputAddressPtr, carryFramePtr, outputStruct);
        Value * outputPtr = mBuilder->CreateGEP(outputStruct, { mBuilder->getInt32(0), mBuilder->getInt32(0) });
        expr = mBuilder->CreateAlignedLoad(outputPtr, BLOCK_SIZE / 8, false);
    }
    else if (const And * pablo_and = dyn_cast<And>(stmt)) {
        expr = mBuilder->CreateAnd(compileExpression(pablo_and->getExpr1()), compileExpression(pablo_and->getExpr2()), "and");
    }
    else if (const Or * pablo_or = dyn_cast<Or>(stmt)) {
        expr = mBuilder->CreateOr(compileExpression(pablo_or->getExpr1()), compileExpression(pablo_or->getExpr2()), "or");
    }
    else if (const Xor * pablo_xor = dyn_cast<Xor>(stmt)) {
        expr = mBuilder->CreateXor(compileExpression(pablo_xor->getExpr1()), compileExpression(pablo_xor->getExpr2()), "xor");
    }
    else if (const Sel * sel = dyn_cast<Sel>(stmt)) {
        Value* ifMask = compileExpression(sel->getCondition());
        Value* ifTrue = mBuilder->CreateAnd(ifMask, compileExpression(sel->getTrueExpr()));
        Value* ifFalse = mBuilder->CreateAnd(genNot(ifMask), compileExpression(sel->getFalseExpr()));
        expr = mBuilder->CreateOr(ifTrue, ifFalse);
    }
    else if (const Not * pablo_not = dyn_cast<Not>(stmt)) {
        expr = genNot(compileExpression(pablo_not->getExpr()));
    }
    else if (const Advance * adv = dyn_cast<Advance>(stmt)) {
        Value* strm_value = compileExpression(adv->getExpr());
        int shift = adv->getAdvanceAmount();
        unsigned advance_index = adv->getLocalAdvanceIndex();
        expr = mCarryManager->advanceCarryInCarryOut(advance_index, shift, strm_value);
    }
    else if (const MatchStar * mstar = dyn_cast<MatchStar>(stmt)) {
        Value * marker = compileExpression(mstar->getMarker());
        Value * cc = compileExpression(mstar->getCharClass());
        Value * marker_and_cc = mBuilder->CreateAnd(marker, cc);
        unsigned carry_index = mstar->getLocalCarryIndex();
        expr = mBuilder->CreateOr(mBuilder->CreateXor(genAddWithCarry(marker_and_cc, cc, carry_index), cc), marker, "matchstar");
    }
    else if (const ScanThru * sthru = dyn_cast<ScanThru>(stmt)) {
        Value * marker_expr = compileExpression(sthru->getScanFrom());
        Value * cc_expr = compileExpression(sthru->getScanThru());
        unsigned carry_index = sthru->getLocalCarryIndex();
        expr = mBuilder->CreateAnd(genAddWithCarry(marker_expr, cc_expr, carry_index), genNot(cc_expr), "scanthru");
    }
    else {
        llvm::raw_os_ostream cerr(std::cerr);
        PabloPrinter::print(stmt, cerr);
        throw std::runtime_error("Unrecognized Pablo Statement! can't compile.");
    }
    mMarkerMap[stmt] = expr;
    if (DumpTrace) {
        genPrintRegister(stmt->getName()->to_string(), expr);
    }
    
}

Value * PabloCompiler::compileExpression(const PabloAST * expr) {
    if (isa<Ones>(expr)) {
        return mOneInitializer;
    }
    else if (isa<Zeroes>(expr)) {
        return mZeroInitializer;
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


#ifdef USE_UADD_OVERFLOW
#ifdef USE_TWO_UADD_OVERFLOW
PabloCompiler::SumWithOverflowPack PabloCompiler::callUaddOverflow(Value* int128_e1, Value* int128_e2) {
    std::vector<Value*> struct_res_params;
    struct_res_params.push_back(int128_e1);
    struct_res_params.push_back(int128_e2);
    CallInst* struct_res = CallInst::Create(mFunctionUaddOverflow, struct_res_params, "uadd_overflow_res", mBasicBlock);
    struct_res->setCallingConv(CallingConv::C);
    struct_res->setTailCall(false);
    AttributeSet struct_res_PAL;
    struct_res->setAttributes(struct_res_PAL);

    SumWithOverflowPack ret;

    std::vector<unsigned> int128_sum_indices;
    int128_sum_indices.push_back(0);
    ret.sum = ExtractValueInst::Create(struct_res, int128_sum_indices, "sum", mBasicBlock);

    std::vector<unsigned> int1_obit_indices;
    int1_obit_indices.push_back(1);
    ret.obit = ExtractValueInst::Create(struct_res, int1_obit_indices, "obit", mBasicBlock);

    return ret;
}
#else
PabloCompiler::SumWithOverflowPack PabloCompiler::callUaddOverflow(Value* int128_e1, Value* int128_e2, Value* int1_cin) {
    std::vector<Value*> struct_res_params;
    struct_res_params.push_back(int128_e1);
    struct_res_params.push_back(int128_e2);
    struct_res_params.push_back(int1_cin);
    CallInst* struct_res = CallInst::Create(mFunctionUaddOverflowCarryin, struct_res_params, "uadd_overflow_res", mBasicBlock);
    struct_res->setCallingConv(CallingConv::C);
    struct_res->setTailCall(false);
    AttributeSet struct_res_PAL;
    struct_res->setAttributes(struct_res_PAL);

    SumWithOverflowPack ret;

    std::vector<unsigned> int128_sum_indices;
    int128_sum_indices.push_back(0);
    ret.sum = ExtractValueInst::Create(struct_res, int128_sum_indices, "sum", mBasicBlock);

    std::vector<unsigned> int1_obit_indices;
    int1_obit_indices.push_back(1);
    ret.obit = ExtractValueInst::Create(struct_res, int1_obit_indices, "obit", mBasicBlock);

    return ret;
}
#endif
#endif


Value* PabloCompiler::genAddWithCarry(Value* e1, Value* e2, unsigned localIndex) {
    Value * carryq_value = mCarryManager->getCarryOpCarryIn(localIndex);
#ifdef USE_TWO_UADD_OVERFLOW
    //This is the ideal implementation, which uses two uadd.with.overflow
    //The back end should be able to recognize this pattern and combine it into uadd.with.overflow.carryin
    CastInst* int128_e1 = new BitCastInst(e1, mBuilder->getIntNTy(BLOCK_SIZE), "e1_128", mBasicBlock);
    CastInst* int128_e2 = new BitCastInst(e2, mBuilder->getIntNTy(BLOCK_SIZE), "e2_128", mBasicBlock);
    CastInst* int128_carryq_value = new BitCastInst(carryq_value, mBuilder->getIntNTy(BLOCK_SIZE), "carryq_128", mBasicBlock);

    SumWithOverflowPack sumpack0, sumpack1;

    sumpack0 = callUaddOverflow(int128_e1, int128_e2);
    sumpack1 = callUaddOverflow(sumpack0.sum, int128_carryq_value);

    Value* obit = mBuilder->CreateOr(sumpack0.obit, sumpack1.obit, "carry_bit");
    Value* sum = mBuilder->CreateBitCast(sumpack1.sum, mBitBlockType, "ret_sum");

    /*obit is the i1 carryout, zero extend and insert it into a v2i64 or v4i64 vector.*/
    ConstantAggregateZero* const_packed_5 = ConstantAggregateZero::get(mBitBlockType);
    ConstantInt* const_int32_6 = ConstantInt::get(mMod->getContext(), APInt(32, StringRef("0"), 10));
    CastInst* int64_o0 = new ZExtInst(obit, IntegerType::get(mMod->getContext(), 64), "o0", mBasicBlock);
    InsertElementInst* carry_out = InsertElementInst::Create(const_packed_5, int64_o0, const_int32_6, "carry_out", mBasicBlock);

#elif defined USE_UADD_OVERFLOW
    //use llvm.uadd.with.overflow.i128 or i256
    CastInst* int128_e1 = new BitCastInst(e1, mBuilder->getIntNTy(BLOCK_SIZE), "e1_128", mBasicBlock);
    CastInst* int128_e2 = new BitCastInst(e2, mBuilder->getIntNTy(BLOCK_SIZE), "e2_128", mBasicBlock);

    //get i1 carryin from iBLOCK_SIZE
    ConstantInt* const_int32_6 = ConstantInt::get(mMod->getContext(), APInt(32, StringRef("0"), 10));
    ExtractElementInst * int64_carryq_value = ExtractElementInst::Create(carryq_value, const_int32_6, "carryq_64", mBasicBlock);
    CastInst* int1_carryq_value = new TruncInst(int64_carryq_value, IntegerType::get(mMod->getContext(), 1), "carryq_1", mBasicBlock);

    SumWithOverflowPack sumpack0;
    sumpack0 = callUaddOverflow(int128_e1, int128_e2, int1_carryq_value);
    Value* obit = sumpack0.obit;
    Value* sum = mBuilder->CreateBitCast(sumpack0.sum, mBitBlockType, "sum");

    /*obit is the i1 carryout, zero extend and insert it into a v2i64 or v4i64 vector.*/
    ConstantAggregateZero* const_packed_5 = ConstantAggregateZero::get(mBitBlockType);
    CastInst* int64_o0 = new ZExtInst(obit, IntegerType::get(mMod->getContext(), 64), "o0", mBasicBlock);
    InsertElementInst* carry_out = InsertElementInst::Create(const_packed_5, int64_o0, const_int32_6, "carry_out", mBasicBlock);
#elif (BLOCK_SIZE == 128)
    //calculate carry through logical ops
    Value* carrygen = mBuilder->CreateAnd(e1, e2, "carrygen");
    Value* carryprop = mBuilder->CreateOr(e1, e2, "carryprop");
    Value* digitsum = mBuilder->CreateAdd(e1, e2, "digitsum");
    Value* partial = mBuilder->CreateAdd(digitsum, carryq_value, "partial");
    Value* digitcarry = mBuilder->CreateOr(carrygen, mBuilder->CreateAnd(carryprop, genNot(partial)));
    Value* mid_carry_in = genShiftLeft64(mBuilder->CreateLShr(digitcarry, 63), "mid_carry_in");

    Value* sum = mBuilder->CreateAdd(partial, mid_carry_in, "sum");
    Value* carry_out = genShiftHighbitToLow(BLOCK_SIZE, mBuilder->CreateOr(carrygen, mBuilder->CreateAnd(carryprop, genNot(sum))));
#else
    //BLOCK_SIZE == 256, there is no other implementation
    static_assert(false, "Add with carry for 256-bit bitblock requires USE_UADD_OVERFLOW");
#endif //USE_TWO_UADD_OVERFLOW

    mCarryManager->setCarryOpCarryOut(localIndex, carry_out);
    return sum;
}

Value * PabloCompiler::genShiftHighbitToLow(unsigned FieldWidth, Value * op) {
    unsigned FieldCount = BLOCK_SIZE/FieldWidth;
    VectorType * vType = VectorType::get(IntegerType::get(mMod->getContext(), FieldWidth), FieldCount);
    Value * v = mBuilder->CreateBitCast(op, vType);
    return mBuilder->CreateBitCast(mBuilder->CreateLShr(v, FieldWidth - 1), mBitBlockType);
}

Value* PabloCompiler::genShiftLeft64(Value* e, const Twine &namehint) {
    Value* i128_val = mBuilder->CreateBitCast(e, mBuilder->getIntNTy(BLOCK_SIZE));
    return mBuilder->CreateBitCast(mBuilder->CreateShl(i128_val, 64, namehint), mBitBlockType);
}

inline Value* PabloCompiler::genNot(Value* expr) {
    return mBuilder->CreateXor(expr, mOneInitializer, "not");
}
    
void PabloCompiler::SetOutputValue(Value * marker, const unsigned index) {
    if (marker->getType()->isPointerTy()) {
        marker = mBuilder->CreateAlignedLoad(marker, BLOCK_SIZE/8, false);
    }
    Value* indices[] = {mBuilder->getInt64(0), mBuilder->getInt32(index)};
    Value* gep = mBuilder->CreateGEP(mOutputAddressPtr, indices);
    mBuilder->CreateAlignedStore(marker, gep, BLOCK_SIZE/8, false);
}

CompiledPabloFunction::CompiledPabloFunction(size_t carryDataSize, Function * function, ExecutionEngine * executionEngine)
: CarryDataSize(carryDataSize)
, FunctionPointer(executionEngine->getPointerToFunction(function))
, mFunction(function)
, mExecutionEngine(executionEngine)
{

}

// Clean up the memory for the compiled function once we're finished using it.
CompiledPabloFunction::~CompiledPabloFunction() {
    if (mExecutionEngine) {
        assert (mFunction);
        // mExecutionEngine->freeMachineCodeForFunction(mFunction); // This function only prints a "not supported" message. Reevaluate with LLVM 3.6.
        delete mExecutionEngine;
    }
}

}
