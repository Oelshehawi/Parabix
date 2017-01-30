/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#include "kernel.h"
#include <llvm/IR/Value.h>               // for Value
#include <llvm/Support/ErrorHandling.h>  // for report_fatal_error
#include <toolchain.h>                   // for BufferSegments, SegmentSize
#include <kernels/streamset.h>           // for StreamSetBuffer
#include <llvm/ADT/StringRef.h>          // for StringRef, operator==
#include <llvm/IR/CallingConv.h>         // for ::C
#include <llvm/IR/Constant.h>            // for Constant
#include <llvm/IR/Constants.h>           // for ConstantInt
#include <llvm/IR/Function.h>            // for Function, Function::arg_iter...
#include <llvm/IR/Instructions.h>        // for LoadInst (ptr only), PHINode
#include <llvm/IR/Module.h>
#include <llvm/Support/Compiler.h>       // for LLVM_UNLIKELY
#include <llvm/Support/raw_ostream.h>
namespace llvm { class BasicBlock; }
namespace llvm { class Type; }

static const auto BLOCK_NO_SCALAR = "blockNo";

static const auto DO_BLOCK_SUFFIX = "_DoBlock";

static const auto FINAL_BLOCK_SUFFIX = "_FinalBlock";

using namespace llvm;
using namespace kernel;
using namespace parabix;

unsigned KernelBuilder::addScalar(Type * const type, const std::string & name) {
    if (LLVM_UNLIKELY(mKernelStateType != nullptr)) {
        llvm::report_fatal_error("Cannot add kernel field " + name + " after kernel state finalized");
    }
    if (LLVM_UNLIKELY(mKernelMap.count(name))) {
        llvm::report_fatal_error("Kernel already contains field " + name);
    }
    const auto index = mKernelFields.size();
    mKernelMap.emplace(name, index);
    mKernelFields.push_back(type);
    return index;
}

unsigned KernelBuilder::addUnnamedScalar(Type * const type) {
    if (LLVM_UNLIKELY(mKernelStateType != nullptr)) {
        llvm::report_fatal_error("Cannot add unnamed kernel field after kernel state finalized");
    }
    const auto index = mKernelFields.size();
    mKernelFields.push_back(type);
    return index;
}

void KernelBuilder::prepareKernel() {
    if (LLVM_UNLIKELY(mKernelStateType != nullptr)) {
        llvm::report_fatal_error("Cannot prepare kernel after kernel state finalized");
    }
    unsigned blockSize = iBuilder->getBitBlockWidth();
    if (mStreamSetInputs.size() != mStreamSetInputBuffers.size()) {
        std::string tmp;
        raw_string_ostream out(tmp);
        out << "kernel contains " << mStreamSetInputBuffers.size() << " input buffers for "
            << mStreamSetInputs.size() << " input stream sets.";
        throw std::runtime_error(out.str());
    }
    if (mStreamSetOutputs.size() != mStreamSetOutputBuffers.size()) {
        std::string tmp;
        raw_string_ostream out(tmp);
        out << "kernel contains " << mStreamSetOutputBuffers.size() << " output buffers for "
            << mStreamSetOutputs.size() << " output stream sets.";
        throw std::runtime_error(out.str());
    }
    int streamSetNo = 0;
    for (unsigned i = 0; i < mStreamSetInputs.size(); i++) {
        if ((mStreamSetInputBuffers[i]->getBufferSize() > 0) && (mStreamSetInputBuffers[i]->getBufferSize() < codegen::SegmentSize + (blockSize + mLookAheadPositions - 1)/blockSize)) {
             llvm::report_fatal_error("Kernel preparation: Buffer size too small " + mStreamSetInputs[i].name);
        }
        mScalarInputs.push_back(Binding{mStreamSetInputBuffers[i]->getStreamBufferPointerType(), mStreamSetInputs[i].name + bufferPtrSuffix});
        mStreamSetNameMap.emplace(mStreamSetInputs[i].name, streamSetNo);
        addScalar(iBuilder->getSizeTy(), mStreamSetInputs[i].name + processedItemCountSuffix);
        streamSetNo++;
    }
    for (unsigned i = 0; i < mStreamSetOutputs.size(); i++) {
        mScalarInputs.push_back(Binding{mStreamSetOutputBuffers[i]->getStreamBufferPointerType(), mStreamSetOutputs[i].name + bufferPtrSuffix});
        mStreamSetNameMap.emplace(mStreamSetOutputs[i].name, streamSetNo);
        addScalar(iBuilder->getSizeTy(), mStreamSetOutputs[i].name + producedItemCountSuffix);
        streamSetNo++;
    }
    for (auto binding : mScalarInputs) {
        addScalar(binding.type, binding.name);
    }
    for (auto binding : mScalarOutputs) {
        addScalar(binding.type, binding.name);
    }
    for (auto binding : mInternalScalars) {
        addScalar(binding.type, binding.name);
    }
    addScalar(iBuilder->getSizeTy(), BLOCK_NO_SCALAR);
    addScalar(iBuilder->getSizeTy(), logicalSegmentNoScalar);
    addScalar(iBuilder->getInt1Ty(), terminationSignal);
    mKernelStateType = StructType::create(iBuilder->getContext(), mKernelFields, mKernelName);
}

std::unique_ptr<Module> KernelBuilder::createKernelModule(const std::vector<StreamSetBuffer *> & inputs, const std::vector<StreamSetBuffer *> & outputs) {
    auto saveModule = iBuilder->getModule();
    auto savePoint = iBuilder->saveIP();
    auto module = make_unique<Module>(mKernelName + "_" + iBuilder->getBitBlockTypeName(), iBuilder->getContext());
    iBuilder->setModule(module.get());
    generateKernel(inputs, outputs);
    iBuilder->setModule(saveModule);
    iBuilder->restoreIP(savePoint);
    return module;
}

void KernelBuilder::generateKernel(const std::vector<StreamSetBuffer *> & inputs, const std::vector<StreamSetBuffer *> & outputs) {
    auto savePoint = iBuilder->saveIP();
    Module * const m = iBuilder->getModule();
    mStreamSetInputBuffers.assign(inputs.begin(), inputs.end());
    mStreamSetOutputBuffers.assign(outputs.begin(), outputs.end());
    prepareKernel(); // possibly overridden by the KernelBuilder subtype
    addKernelDeclarations(m);
    callGenerateInitMethod();
    callGenerateDoSegmentMethod();
    // Implement the accumulator get functions
    for (auto binding : mScalarOutputs) {
        Function * f = getAccumulatorFunction(binding.name);
        iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "get_" + binding.name, f));
        Value * self = &*(f->arg_begin());
        Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(binding.name)});
        Value * retVal = iBuilder->CreateLoad(ptr);
        iBuilder->CreateRet(retVal);
    }
    iBuilder->restoreIP(savePoint);
}

void KernelBuilder::callGenerateDoSegmentMethod() const {
    Function * doSegmentFunction = getDoSegmentFunction();
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), mKernelName + "_entry", doSegmentFunction, 0));
    auto args = doSegmentFunction->arg_begin();
    Value * self = &*(args++);
    Value * doFinal = &*(args++);
    std::vector<Value *> producerPos;
    for (unsigned i = 0; i < mStreamSetInputs.size(); i++) {
        producerPos.push_back(&*(args++));
    }
    assert (args == doSegmentFunction->arg_end());
    generateDoSegmentMethod(doSegmentFunction, self, doFinal, producerPos); // must be overridden by the KernelBuilder subtype
    iBuilder->CreateRetVoid();
}

void KernelBuilder::callGenerateInitMethod() const {
    Function * initFunction = getInitFunction();
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "Init_entry", initFunction, 0));
    Function::arg_iterator args = initFunction->arg_begin();
    Value * self = &*(args++);
    iBuilder->CreateStore(ConstantAggregateZero::get(mKernelStateType), self);
    for (auto binding : mScalarInputs) {
        Value * param = &*(args++);
        Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(binding.name)});
        iBuilder->CreateStore(param, ptr);
    }
    generateInitMethod(initFunction, self);
    iBuilder->CreateRetVoid();
}

// Default init method, possibly overridden if special init actions required.
void KernelBuilder::generateInitMethod(Function * /* initFunction */, Value * /* self */) const { }


ConstantInt * KernelBuilder::getScalarIndex(const std::string & name) const {
    const auto f = mKernelMap.find(name);
    if (LLVM_UNLIKELY(f == mKernelMap.end())) {
        llvm::report_fatal_error("Kernel does not contain scalar: " + name);
    }
    return iBuilder->getInt32(f->second);
}

unsigned KernelBuilder::getScalarCount() const {
    return mKernelFields.size();
}

Value * KernelBuilder::getScalarFieldPtr(Value * self, const std::string & fieldName) const {
    return getScalarFieldPtr(self, getScalarIndex(fieldName));
}

Value * KernelBuilder::getScalarFieldPtr(Value * self, Value * index) const {
    return iBuilder->CreateGEP(self, {iBuilder->getInt32(0), index});
}

Value * KernelBuilder::getScalarField(Value * self, const std::string & fieldName) const {
    return iBuilder->CreateLoad(getScalarFieldPtr(self, fieldName));
}

Value * KernelBuilder::getScalarField(Value * self, Value * index) const {
    return iBuilder->CreateLoad(getScalarFieldPtr(self, index));
}

void KernelBuilder::setScalarField(Value * self, const std::string & fieldName, Value * value) const {
    iBuilder->CreateStore(value, getScalarFieldPtr(self, fieldName));
}

void KernelBuilder::setScalarField(Value * self, Value * index, Value * value) const {
    iBuilder->CreateStore(value, getScalarFieldPtr(self, index));
}

LoadInst * KernelBuilder::acquireLogicalSegmentNo(Value * self) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(logicalSegmentNoScalar)});
    return iBuilder->CreateAtomicLoadAcquire(ptr);
}

Value * KernelBuilder::getProcessedItemCount(Value * self, const std::string & ssName) const {
    return getScalarField(self, ssName + processedItemCountSuffix);
}

Value * KernelBuilder::getProducedItemCount(Value * self, const std::string & ssName) const {
    return getScalarField(self, ssName + producedItemCountSuffix);
}

Value * KernelBuilder::getTerminationSignal(Value * self) const {
    return getScalarField(self, terminationSignal);
}

void KernelBuilder::releaseLogicalSegmentNo(Value * self, Value * newCount) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(logicalSegmentNoScalar)});
    iBuilder->CreateAtomicStoreRelease(newCount, ptr);
}

void KernelBuilder::setProcessedItemCount(Value * self, const std::string & name, Value * value) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(name + processedItemCountSuffix)});
    iBuilder->CreateStore(value, ptr);
}

void KernelBuilder::setProducedItemCount(Value * self, const std::string & name, Value * value) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(name + producedItemCountSuffix)});
    iBuilder->CreateStore(value, ptr);
}

void KernelBuilder::setTerminationSignal(Value * self) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(terminationSignal)});
    iBuilder->CreateStore(ConstantInt::get(iBuilder->getInt1Ty(), 1), ptr);
}

Value * KernelBuilder::getBlockNo(Value * self) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(BLOCK_NO_SCALAR)});
    return iBuilder->CreateLoad(ptr);
}

void KernelBuilder::setBlockNo(Value * self, Value * value) const {
    Value * ptr = iBuilder->CreateGEP(self, {iBuilder->getInt32(0), getScalarIndex(BLOCK_NO_SCALAR)});
    iBuilder->CreateStore(value, ptr);
}

Argument * KernelBuilder::getParameter(Function * const f, const std::string & name) const {
    for (auto & arg : f->getArgumentList()) {
        if (arg.getName().equals(name)) {
            return &arg;
        }
    }
    llvm::report_fatal_error(f->getName() + " does not have parameter " + name);
}

Value * KernelBuilder::createDoSegmentCall(const std::vector<llvm::Value *> & args) const {
    return iBuilder->CreateCall(getDoSegmentFunction(), args);
}

Value * KernelBuilder::createGetAccumulatorCall(Value * self, const std::string & accumName) const {
    return iBuilder->CreateCall(getAccumulatorFunction(accumName), {self});
}


unsigned KernelBuilder::getStreamSetIndex(const std::string & name) const {
    const auto f = mStreamSetNameMap.find(name);
    if (LLVM_UNLIKELY(f == mStreamSetNameMap.end())) {
        llvm::report_fatal_error("Kernel " + getName() + " does not contain stream set: " + name);
    }
    return f->second;
}

Value * KernelBuilder::getStreamSetBufferPtr(Value * self, const std::string & name) const {
    return getScalarField(self, name + bufferPtrSuffix);
}

inline const StreamSetBuffer * KernelBuilder::getStreamSetBuffer(const std::string & name) const {
    const unsigned structIdx = getStreamSetIndex(name);
    if (structIdx < mStreamSetInputs.size()) {
        return mStreamSetInputBuffers[structIdx];
    } else {
        return mStreamSetOutputBuffers[structIdx - mStreamSetInputs.size()];
    }
}

Value * KernelBuilder::getStreamSetPtr(Value * self, const std::string & name, Value * blockNo) const {
    return getStreamSetBuffer(name)->getStreamSetPtr(getStreamSetBufferPtr(self, name), blockNo);
}

Value * KernelBuilder::getStream(Value * self, const std::string & name, Value * blockNo, Value * index) const {
    return getStreamSetBuffer(name)->getStream(getStreamSetBufferPtr(self, name), blockNo, index);
}

Value * KernelBuilder::getStream(Value * self, const std::string & name, Value * blockNo, Value * index1, Value * index2) const {
    assert (index1->getType() == index2->getType());
    return getStreamSetBuffer(name)->getStream(getStreamSetBufferPtr(self, name), blockNo, index1, index2);
}

Value * KernelBuilder::getStreamView(Value * self, const std::string & name, Value * blockNo, Value * index) const {
    return getStreamSetBuffer(name)->getStreamView(getStreamSetBufferPtr(self, name), blockNo, index);
}

Value * KernelBuilder::getStreamView(llvm::Type * type, Value * self, const std::string & name, Value * blockNo, Value * index) const {
    return getStreamSetBuffer(name)->getStreamView(type, getStreamSetBufferPtr(self, name), blockNo, index);
}

void KernelBuilder::createInstance() {
    if (LLVM_UNLIKELY(mKernelStateType == nullptr)) {
        llvm::report_fatal_error("Cannot create kernel instance before calling prepareKernel()");
    }
    mKernelInstance = iBuilder->CreateCacheAlignedAlloca(mKernelStateType);
    std::vector<Value *> init_args = {mKernelInstance};
    for (auto a : mInitialArguments) {
        init_args.push_back(a);
    }
    for (auto b : mStreamSetInputBuffers) {
        init_args.push_back(b->getStreamSetBasePtr());
    }
    for (auto b : mStreamSetOutputBuffers) {
        init_args.push_back(b->getStreamSetBasePtr());
    }
    Function * initMethod = getInitFunction();
    iBuilder->CreateCall(initMethod, init_args);
}

//  The default finalBlock method simply dispatches to the doBlock routine.
void BlockOrientedKernel::generateFinalBlockMethod(Function * function, Value * self, Value * /* remainingBytes */, Value * /* blockNo */) const {
//    std::vector<Value *> args = {self};
//    for (Argument & arg : function->getArgumentList()){
//        args.push_back(&arg);
//    }
    iBuilder->CreateCall(getDoBlockFunction(), { self });
}

//  The default doSegment method dispatches to the doBlock routine for
//  each block of the given number of blocksToDo, and then updates counts.
void BlockOrientedKernel::generateDoSegmentMethod(Function * doSegmentFunction, Value * self, Value * doFinal, const std::vector<Value *> &producerPos) const {

    auto savePoint = iBuilder->saveIP();
    callGenerateDoBlockMethod();
    callGenerateDoFinalBlockMethod();
    iBuilder->restoreIP(savePoint);

    BasicBlock * entryBlock = iBuilder->GetInsertBlock();
    BasicBlock * strideLoopCond = BasicBlock::Create(iBuilder->getContext(), mKernelName + "_strideLoopCond", doSegmentFunction, 0);
    BasicBlock * strideLoopBody = BasicBlock::Create(iBuilder->getContext(), mKernelName + "_strideLoopBody", doSegmentFunction, 0);
    BasicBlock * stridesDone = BasicBlock::Create(iBuilder->getContext(), mKernelName + "_stridesDone", doSegmentFunction, 0);
    BasicBlock * doFinalBlock = BasicBlock::Create(iBuilder->getContext(), mKernelName + "_doFinalBlock", doSegmentFunction, 0);
    BasicBlock * segmentDone = BasicBlock::Create(iBuilder->getContext(), mKernelName + "_segmentDone", doSegmentFunction, 0);
    Type * const size_ty = iBuilder->getSizeTy();

    ConstantInt * stride = iBuilder->getSize(iBuilder->getStride());
    ConstantInt * strideBlocks = iBuilder->getSize(iBuilder->getStride() / iBuilder->getBitBlockWidth());

    Value * availablePos = producerPos[0];
    for (unsigned i = 1; i < mStreamSetInputs.size(); i++) {
        Value * p = producerPos[i];
        availablePos = iBuilder->CreateSelect(iBuilder->CreateICmpULT(availablePos, p), availablePos, p);
    }
    Value * processed = getProcessedItemCount(self, mStreamSetInputs[0].name);
    Value * itemsAvail = iBuilder->CreateSub(availablePos, processed);
    Value * stridesToDo = iBuilder->CreateUDiv(itemsAvail, stride);
    iBuilder->CreateBr(strideLoopCond);

    iBuilder->SetInsertPoint(strideLoopCond);
    PHINode * stridesRemaining = iBuilder->CreatePHI(size_ty, 2, "stridesRemaining");
    stridesRemaining->addIncoming(stridesToDo, entryBlock);
    Value * notDone = iBuilder->CreateICmpUGT(stridesRemaining, iBuilder->getSize(0));
    iBuilder->CreateCondBr(notDone, strideLoopBody, stridesDone);

    iBuilder->SetInsertPoint(strideLoopBody);
    Value * blockNo = getBlockNo(self);

    iBuilder->CreateCall(getDoBlockFunction(), self);

    setBlockNo(self, iBuilder->CreateAdd(blockNo, strideBlocks));
    stridesRemaining->addIncoming(iBuilder->CreateSub(stridesRemaining, iBuilder->getSize(1)), strideLoopBody);
    iBuilder->CreateBr(strideLoopCond);

    iBuilder->SetInsertPoint(stridesDone);
    // Update counts for the full strides processed.
    Value * segmentItemsProcessed = iBuilder->CreateMul(stridesToDo, stride);
    for (unsigned i = 0; i < mStreamSetInputs.size(); i++) {
        Value * preProcessed = getProcessedItemCount(self, mStreamSetInputs[i].name);
        setProcessedItemCount(self, mStreamSetInputs[i].name, iBuilder->CreateAdd(preProcessed, segmentItemsProcessed));
    }
    if (!mDoBlockUpdatesProducedItemCountsAttribute) {
        for (unsigned i = 0; i < mStreamSetOutputs.size(); i++) {
            Value * preProduced = getProducedItemCount(self, mStreamSetOutputs[i].name);
            setProducedItemCount(self, mStreamSetOutputs[i].name, iBuilder->CreateAdd(preProduced, segmentItemsProcessed));
        }
    }

    // Now conditionally perform the final block processing depending on the doFinal parameter.
    iBuilder->CreateCondBr(doFinal, doFinalBlock, segmentDone);
    iBuilder->SetInsertPoint(doFinalBlock);

    Value * remainingItems = iBuilder->CreateSub(producerPos[0], getProcessedItemCount(self, mStreamSetInputs[0].name));

    iBuilder->CreateCall(getDoFinalBlockFunction(), {self, remainingItems});

    // createFinalBlockCall(self, remainingItems);
    for (unsigned i = 0; i < mStreamSetInputs.size(); i++) {
        Value * preProcessed = getProcessedItemCount(self, mStreamSetInputs[i].name);
        setProcessedItemCount(self, mStreamSetInputs[i].name, iBuilder->CreateAdd(preProcessed, remainingItems));
    }
    if (!mDoBlockUpdatesProducedItemCountsAttribute) {
        for (unsigned i = 0; i < mStreamSetOutputs.size(); i++) {
            Value * preProduced = getProducedItemCount(self, mStreamSetOutputs[i].name);
            setProducedItemCount(self, mStreamSetOutputs[i].name, iBuilder->CreateAdd(preProduced, remainingItems));
        }
    }
    setTerminationSignal(self);
    iBuilder->CreateBr(segmentDone);

    iBuilder->SetInsertPoint(segmentDone);

}

void BlockOrientedKernel::callGenerateDoBlockMethod() const {
    Function * f = getDoBlockFunction();
    auto args = f->arg_begin();
    Value * const self = &(*args);
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "entry", f));
    generateDoBlockMethod(f, self, getBlockNo(self)); // must be implemented by the KernelBuilder subtype
    iBuilder->CreateRetVoid();
}

void BlockOrientedKernel::callGenerateDoFinalBlockMethod() const {
    Function * f = getDoFinalBlockFunction();
    auto args = f->arg_begin();
    Value * const self = &(*args++);
    Value * const remainingBytes = &(*args);
    iBuilder->SetInsertPoint(BasicBlock::Create(iBuilder->getContext(), "entry", f));
    generateFinalBlockMethod(f, self, remainingBytes, getBlockNo(self)); // possibly overridden by the KernelBuilder subtype
    iBuilder->CreateRetVoid();
}

Function * BlockOrientedKernel::getDoBlockFunction() const {
    return iBuilder->getModule()->getFunction(mKernelName + DO_BLOCK_SUFFIX);
}

Function * BlockOrientedKernel::getDoFinalBlockFunction() const {
    return iBuilder->getModule()->getFunction(mKernelName + FINAL_BLOCK_SUFFIX);
}

void BlockOrientedKernel::addAdditionalKernelDeclarations(Module * m, PointerType * selfType) const {
    // Create the doBlock and finalBlock function prototypes
    FunctionType * doBlockFunctionType = FunctionType::get(iBuilder->getVoidTy(), {selfType}, false);
    Function * doBlockFn = Function::Create(doBlockFunctionType, GlobalValue::ExternalLinkage, mKernelName + DO_BLOCK_SUFFIX, m);
    doBlockFn->setCallingConv(CallingConv::C);
    doBlockFn->setDoesNotThrow();
    doBlockFn->setDoesNotCapture(1);
    auto doBlockArgs = doBlockFn->arg_begin();
    Value * doBlockArg = &*(doBlockArgs++);
    doBlockArg->setName("self");

    FunctionType * finalBlockType = FunctionType::get(iBuilder->getVoidTy(), {selfType, iBuilder->getSizeTy()}, false);
    Function * finalBlockFn = Function::Create(finalBlockType, GlobalValue::ExternalLinkage, mKernelName + FINAL_BLOCK_SUFFIX, m);
    finalBlockFn->setCallingConv(CallingConv::C);
    finalBlockFn->setDoesNotThrow();
    finalBlockFn->setDoesNotCapture(1);
    auto finalBlockArgs = finalBlockFn->arg_begin();
    Value * finalBlockArg = &*(finalBlockArgs++);
    finalBlockArg->setName("self");
    finalBlockArg = &*(finalBlockArgs++);
    finalBlockArg->setName("remainingBytes");

}

// CONSTRUCTOR
KernelBuilder::KernelBuilder(IDISA::IDISA_Builder * builder,
                             std::string && kernelName,
                             std::vector<Binding> && stream_inputs,
                             std::vector<Binding> && stream_outputs,
                             std::vector<Binding> && scalar_parameters,
                             std::vector<Binding> && scalar_outputs,
                             std::vector<Binding> && internal_scalars)
: KernelInterface(builder, std::move(kernelName), std::move(stream_inputs), std::move(stream_outputs), std::move(scalar_parameters), std::move(scalar_outputs), std::move(internal_scalars))
, mNoTerminateAttribute(false)
, mDoBlockUpdatesProducedItemCountsAttribute(false) {

}

KernelBuilder::~KernelBuilder() { }

// CONSTRUCTOR
BlockOrientedKernel::BlockOrientedKernel(IDISA::IDISA_Builder * builder,
                                         std::string && kernelName,
                                         std::vector<Binding> && stream_inputs,
                                         std::vector<Binding> && stream_outputs,
                                         std::vector<Binding> && scalar_parameters,
                                         std::vector<Binding> && scalar_outputs,
                                         std::vector<Binding> && internal_scalars)
: KernelBuilder(builder, std::move(kernelName), std::move(stream_inputs), std::move(stream_outputs), std::move(scalar_parameters), std::move(scalar_outputs), std::move(internal_scalars)) {

}




// CONSTRUCTOR
SegmentOrientedKernel::SegmentOrientedKernel(IDISA::IDISA_Builder * builder,
                                             std::string && kernelName,
                                             std::vector<Binding> && stream_inputs,
                                             std::vector<Binding> && stream_outputs,
                                             std::vector<Binding> && scalar_parameters,
                                             std::vector<Binding> && scalar_outputs,
                                             std::vector<Binding> && internal_scalars)
: KernelBuilder(builder, std::move(kernelName), std::move(stream_inputs), std::move(stream_outputs), std::move(scalar_parameters), std::move(scalar_outputs), std::move(internal_scalars)) {

}
