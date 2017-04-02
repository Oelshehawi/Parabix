/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#ifndef KERNEL_BUILDER_H
#define KERNEL_BUILDER_H

#include <string>           // for string
#include <memory>           // for unique_ptr
#include "interface.h"      // for KernelInterface
#include <boost/container/flat_map.hpp>
#include <IR_Gen/idisa_builder.h>

//namespace llvm { class ConstantInt; }
#include <llvm/IR/Constants.h>
namespace llvm { class Function; }
namespace llvm { class IntegerType; }
namespace llvm { class LoadInst; }
namespace llvm { class Type; }
namespace llvm { class Value; }
namespace parabix { class StreamSetBuffer; }

namespace kernel {
    
class KernelBuilder : public KernelInterface {
    using NameMap = boost::container::flat_map<std::string, unsigned>;
public:
    
    // Create a module for the kernel, including the kernel state type declaration and
    // the full implementation of all required methods.     
    //
    std::unique_ptr<llvm::Module> createKernelModule(const std::vector<parabix::StreamSetBuffer *> & inputs, const std::vector<parabix::StreamSetBuffer *> & outputs);
    
    // Generate the Kernel to the current module (iBuilder->getModule()).
    void generateKernel(const std::vector<parabix::StreamSetBuffer *> & inputs, const std::vector<parabix::StreamSetBuffer *> & outputs);
    
    void createInstance() override;

    llvm::Value * getProducedItemCount(llvm::Value * instance, const std::string & name, llvm::Value * doFinal = nullptr) const final;

    void setProducedItemCount(llvm::Value * instance, const std::string & name, llvm::Value * value) const final;

    llvm::Value * getConsumedItemCount(llvm::Value * instance, const std::string & name) const final;

    void setConsumedItemCount(llvm::Value * instance, const std::string & name, llvm::Value * value) const final;

    llvm::Value * getProcessedItemCount(llvm::Value * instance, const std::string & name) const final;

    void setProcessedItemCount(llvm::Value * instance, const std::string & name, llvm::Value * value) const final;

    virtual void reserveBytes(llvm::Value * instance, const std::string & name, llvm::Value * requested) const;

    bool hasNoTerminateAttribute() { return mNoTerminateAttribute;}
    
    llvm::Value * getTerminationSignal(llvm::Value * instance) const final;

    void setTerminationSignal(llvm::Value * instance) const final;

    // Get the value of a scalar field for a given instance.
    llvm::Value * getScalarField(llvm::Value * instance, const std::string & fieldName) const;

    llvm::Value * getScalarField(llvm::Value * instance, llvm::Value * index) const;

    // Set the value of a scalar field for a given instance.
    void setScalarField(llvm::Value *instance, const std::string & fieldName, llvm::Value * value) const;

    void setScalarField(llvm::Value * instance, llvm::Value * index, llvm::Value * value) const;

    // Synchronization actions for executing a kernel for a particular logical segment.
    //
    // Before the segment is processed, acquireLogicalSegmentNo must be used to load
    // the segment number of the kernel state to ensure that the previous segment is
    // complete (by checking that the acquired segment number is equal to the desired segment
    // number).
    // After all segment processing actions for the kernel are complete, and any necessary
    // data has been extracted from the kernel for further pipeline processing, the
    // segment number must be incremented and stored using releaseLogicalSegmentNo.
    llvm::LoadInst * acquireLogicalSegmentNo(llvm::Value * instance) const;

    void releaseLogicalSegmentNo(llvm::Value * instance, llvm::Value * newFieldVal) const;

    // Get a parameter by name.
    llvm::Argument * getParameter(llvm::Function * f, const std::string & name) const;

    inline llvm::IntegerType * getSizeTy() const {
        return getBuilder()->getSizeTy();
    }

    inline llvm::Type * getStreamTy(const unsigned FieldWidth = 1) {
        return getBuilder()->getStreamTy(FieldWidth);
    }
    
    inline llvm::Type * getStreamSetTy(const unsigned NumElements = 1, const unsigned FieldWidth = 1) {
        return getBuilder()->getStreamSetTy(NumElements, FieldWidth);
    }
    
    virtual ~KernelBuilder() = 0;
    
    const std::vector<const parabix::StreamSetBuffer *> & getStreamSetInputBuffers() const { return mStreamSetInputBuffers; }

    const std::vector<const parabix::StreamSetBuffer *> & getStreamSetOutputBuffers() const { return mStreamSetOutputBuffers; }

    llvm::Value * createDoSegmentCall(const std::vector<llvm::Value *> & args) const;

    llvm::Value * createGetAccumulatorCall(llvm::Value * self, const std::string & accumName) const;

protected:

    // Constructor
    KernelBuilder(IDISA::IDISA_Builder * builder,
                    std::string && kernelName,
                    std::vector<Binding> && stream_inputs,
                    std::vector<Binding> && stream_outputs,
                    std::vector<Binding> && scalar_parameters,
                    std::vector<Binding> && scalar_outputs,
                    std::vector<Binding> && internal_scalars);

    //
    // Kernel builder subtypes define their logic of kernel construction
    // in terms of 3 virtual methods for
    // (a) preparing the Kernel state data structure
    // (b) defining the logic of the doBlock function, and
    // (c) defining the logic of the finalBlock function.
    //
    // Note: the kernel state data structure must only be finalized after
    // all scalar fields have been added.   If there are no fields to
    // be added, the default method for preparing kernel state may be used.
    
    void setNoTerminateAttribute(const bool noTerminate = true) {
        mNoTerminateAttribute = noTerminate;
    }

    void prepareKernelSignature();

    virtual void prepareKernel();

    virtual void generateInitMethod() { }
    
    virtual void generateDoSegmentMethod(llvm::Value * doFinal, const std::vector<llvm::Value *> & producerPos) = 0;

    // Add an additional scalar field to the KernelState struct.
    // Must occur before any call to addKernelDeclarations or createKernelModule.
    unsigned addScalar(llvm::Type * type, const std::string & name);

    unsigned addUnnamedScalar(llvm::Type * type);

    unsigned getScalarCount() const;

    // Run-time access of Kernel State and parameters of methods for
    // use in implementing kernels.
    
    // Get the index of a named scalar field within the kernel state struct.
    llvm::ConstantInt * getScalarIndex(const std::string & name) const;

    // Get the value of a scalar field for a given instance.
    llvm::Value * getScalarField(const std::string & fieldName) const {
        return getScalarField(getSelf(), fieldName);
    }

    llvm::Value * getScalarField(llvm::Value * index) const {
        return getScalarField(getSelf(), index);
    }

    // Set the value of a scalar field for a given instance.
    void setScalarField(const std::string & fieldName, llvm::Value * value) const {
        return setScalarField(getSelf(), fieldName, value);
    }

    void setScalarField(llvm::Value * index, llvm::Value * value) const {
        return setScalarField(getSelf(), index, value);
    }

    llvm::Value * getInputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex) const;

    llvm::Value * loadInputStreamBlock(const std::string & name, llvm::Value * streamIndex) const;
    
    llvm::Value * getInputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) const;
    
    llvm::Value * loadInputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) const;
    
    llvm::Value * getInputStreamSetCount(const std::string & name) const;

    llvm::Value * getOutputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex) const;
    
    void storeOutputStreamBlock(const std::string & name, llvm::Value * streamIndex, llvm::Value * toStore) const;
    
    llvm::Value * getOutputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) const;
    
    void storeOutputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * toStore) const;

    llvm::Value * getOutputStreamSetCount(const std::string & name) const;

    llvm::Value * getAdjustedInputStreamBlockPtr(llvm::Value * blockAdjustment, const std::string & name, llvm::Value * streamIndex) const;

    llvm::Value * getRawInputPointer(const std::string & name, llvm::Value * streamIndex, llvm::Value * absolutePosition) const;

    llvm::Value * getRawOutputPointer(const std::string & name, llvm::Value * streamIndex, llvm::Value * absolutePosition) const;

    void reserveBytes(const std::string & name, llvm::Value * requested) const {
        reserveBytes(getSelf(), name, requested);
    }

    llvm::Value * getScalarFieldPtr(const std::string & name) const {
        return getScalarFieldPtr(getSelf(), name);
    }

    llvm::Value * getScalarFieldPtr(llvm::Value * index) const {
        return getScalarFieldPtr(getSelf(), index);
    }

    inline llvm::Value * getProducedItemCount(const std::string & name) const {
        return getProducedItemCount(getSelf(), name);
    }

    inline void setProducedItemCount(const std::string & name, llvm::Value * value) const {
        setProducedItemCount(getSelf(), name, value);
    }

    inline llvm::Value * getConsumedItemCount(const std::string & name) const {
        return getConsumedItemCount(getSelf(), name);
    }

    inline void setConsumedItemCount(const std::string & name, llvm::Value * value) const {
        setConsumedItemCount(getSelf(), name, value);
    }

    inline llvm::Value * getProcessedItemCount(const std::string & name) const {
        return getProcessedItemCount(getSelf(), name);
    }

    inline void setProcessedItemCount(const std::string & name, llvm::Value * value) const {
        setProcessedItemCount(getSelf(), name, value);
    }

    llvm::Value * getTerminationSignal() const {
        return getTerminationSignal(getSelf());
    }

    void setTerminationSignal() const {
        return setTerminationSignal(getSelf());
    }

    llvm::Value * getSelf() const {
        return mSelf;
    }

    llvm::BasicBlock * CreateBasicBlock(std::string && name) const;

    // Stream set helpers.

    llvm::Value * getStreamSetBufferPtr(const std::string & name) const;

    llvm::Value * getScalarFieldPtr(llvm::Value * instance, const std::string & name) const;

    llvm::Value * getScalarFieldPtr(llvm::Value * instance, llvm::Value * index) const;

    unsigned getStreamSetIndex(const std::string & name) const;

    const parabix::StreamSetBuffer * getInputStreamSetBuffer(const std::string & name) const {
        const auto index = getStreamSetIndex(name);
        assert (index < mStreamSetInputBuffers.size());
        return mStreamSetInputBuffers[index];
    }

    const parabix::StreamSetBuffer * getOutputStreamSetBuffer(const std::string & name) const {
        const auto index = getStreamSetIndex(name);
        assert (index < mStreamSetOutputBuffers.size());
        return mStreamSetOutputBuffers[index];
    }

    void callGenerateInitMethod();

    void callGenerateDoSegmentMethod();

private:

    llvm::Value * computeBlockIndex(const std::vector<Binding> & binding, const std::string & name, llvm::Value * itemCount) const;

protected:

    llvm::Value *                                   mSelf;
    llvm::Function *                                mCurrentMethod;

    std::vector<llvm::Type *>                       mKernelFields;
    NameMap                                         mKernelMap;
    NameMap                                         mStreamSetNameMap;
    std::vector<const parabix::StreamSetBuffer *>   mStreamSetInputBuffers;
    std::vector<const parabix::StreamSetBuffer *>   mStreamSetOutputBuffers;
    bool                                            mNoTerminateAttribute;

};

class SegmentOrientedKernel : public KernelBuilder {
protected:

    SegmentOrientedKernel(IDISA::IDISA_Builder * builder,
                          std::string && kernelName,
                          std::vector<Binding> && stream_inputs,
                          std::vector<Binding> && stream_outputs,
                          std::vector<Binding> && scalar_parameters,
                          std::vector<Binding> && scalar_outputs,
                          std::vector<Binding> && internal_scalars);

    virtual ~SegmentOrientedKernel() { }

};

class BlockOrientedKernel : public KernelBuilder {
protected:

    void CreateDoBlockMethodCall();

    // Each kernel builder subtype must provide its own logic for generating
    // doBlock calls.
    virtual void generateDoBlockMethod() = 0;

    // Each kernel builder subtypre must also specify the logic for processing the
    // final block of stream data, if there is any special processing required
    // beyond simply calling the doBlock function.   In the case that the final block
    // processing may be trivially implemented by dispatching to the doBlock method
    // without additional preparation, the default generateFinalBlockMethod need
    // not be overridden.

    virtual void generateFinalBlockMethod(llvm::Value * remainingItems);

    void generateDoSegmentMethod(llvm::Value * doFinal, const std::vector<llvm::Value *> & producerPos) override final;

    BlockOrientedKernel(IDISA::IDISA_Builder * builder,
                        std::string && kernelName,
                        std::vector<Binding> && stream_inputs,
                        std::vector<Binding> && stream_outputs,
                        std::vector<Binding> && scalar_parameters,
                        std::vector<Binding> && scalar_outputs,
                        std::vector<Binding> && internal_scalars);

    virtual ~BlockOrientedKernel() { }

private:

    bool useIndirectBr() const {
        return iBuilder->supportsIndirectBr();
    }

    void writeDoBlockMethod();

    void writeFinalBlockMethod(llvm::Value * remainingItems);

private:

    llvm::Function *        mDoBlockMethod;
    llvm::BasicBlock *      mStrideLoopBody;
    llvm::IndirectBrInst *  mStrideLoopBranch;
    llvm::PHINode *         mStrideLoopTarget;
};


}
#endif 
