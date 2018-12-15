#ifndef KERNEL_BUILDER_H
#define KERNEL_BUILDER_H

#include <IR_Gen/idisa_builder.h>
#include <kernels/kernel.h>

namespace kernel {

class Kernel;

class KernelBuilder : public virtual IDISA::IDISA_Builder {
    friend class Kernel;
    friend class MultiBlockKernel;
    friend class PipelineGenerator;
public:

    // Get the value of a scalar field for the current instance.
    llvm::Value * getScalarFieldPtr(llvm::Value * index);

    llvm::Value * getScalarFieldPtr(const std::string & fieldName);

    llvm::Value * getScalarField(const std::string & fieldName);

    // Set the value of a scalar field for the current instance.
    void setScalarField(const std::string & fieldName, llvm::Value * value);

    // Synchronization actions for executing a kernel for a particular logical segment.
    //
    // Before the segment is processed, acquireLogicalSegmentNo must be used to load
    // the segment number of the kernel state to ensure that the previous segment is
    // complete (by checking that the acquired segment number is equal to the desired segment
    // number).
    // After all segment processing actions for the kernel are complete, and any necessary
    // data has been extracted from the kernel for further pipeline processing, the
    // segment number must be incremented and stored using releaseLogicalSegmentNo.
    llvm::LoadInst * acquireLogicalSegmentNo();

    void releaseLogicalSegmentNo(llvm::Value * const nextSegNo);

    llvm::Value * getAvailableItemCount(const std::string & name);

    llvm::Value * getAccessibleItemCount(const std::string & name);

    llvm::Value * getProcessedItemCount(const std::string & name) {
        return getNamedItemCount(name, PROCESSED_ITEM_COUNT_SUFFIX);
    }

    void setProcessedItemCount(const std::string & name, llvm::Value * value) {
        setNamedItemCount(name, PROCESSED_ITEM_COUNT_SUFFIX, value);
    }

    llvm::Value * getProducedItemCount(const std::string & name) {
        return getNamedItemCount(name, PRODUCED_ITEM_COUNT_SUFFIX);
    }

    void setProducedItemCount(const std::string & name, llvm::Value * value) {
        setNamedItemCount(name, PRODUCED_ITEM_COUNT_SUFFIX, value);
    }

    llvm::Value * getConsumedItemCount(const std::string & name) {
        return getNamedItemCount(name, CONSUMED_ITEM_COUNT_SUFFIX);
    }

    void setConsumedItemCount(const std::string & name, llvm::Value * value) {
        setNamedItemCount(name, CONSUMED_ITEM_COUNT_SUFFIX, value);
    }

    llvm::Value * getNonDeferredProcessedItemCount(const Binding & input) {
        return getNamedItemCount(input.getName(), input.isDeferred() ? NON_DEFERRED_ITEM_COUNT_SUFFIX : PROCESSED_ITEM_COUNT_SUFFIX);
    }

    void setNonDeferredProcessedItemCount(const Binding & input, llvm::Value * value) {
        setNamedItemCount(input.getName(), input.isDeferred() ? NON_DEFERRED_ITEM_COUNT_SUFFIX : PROCESSED_ITEM_COUNT_SUFFIX, value);
    }

    llvm::Value * getNonDeferredProducedItemCount(const Binding & output) {
        return getNamedItemCount(output.getName(), output.isDeferred() ? NON_DEFERRED_ITEM_COUNT_SUFFIX : PRODUCED_ITEM_COUNT_SUFFIX);
    }

    void setNonDeferredProducedItemCount(const Binding & output, llvm::Value * value) {
        setNamedItemCount(output.getName(), output.isDeferred() ? NON_DEFERRED_ITEM_COUNT_SUFFIX : PRODUCED_ITEM_COUNT_SUFFIX, value);
    }

    llvm::Value * getTerminationSignal();

    void setTerminationSignal() { setTerminationSignal(getTrue()); }

    void setTerminationSignal(llvm::Value * const value);

    llvm::Value * getCycleCountPtr();

    // Run-time access of Kernel State and parameters of methods for
    // use in implementing kernels.

    llvm::Value * getInputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex) {
        return getInputStreamBlockPtr(name, streamIndex, nullptr);
    }

    llvm::Value * getInputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * blockOffset);

    llvm::Value * getInputStreamLogicalBasePtr(const Binding & input);

    llvm::Value * loadInputStreamBlock(const std::string & name, llvm::Value * streamIndex) {
        return loadInputStreamBlock(name, streamIndex, nullptr);
    }

    llvm::Value * loadInputStreamBlock(const std::string & name, llvm::Value * streamIndex, llvm::Value * blockOffset);

    llvm::Value * getInputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) {
        return getInputStreamPackPtr(name, streamIndex, packIndex, nullptr);
    }

    llvm::Value * getInputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * blockOffset);

    llvm::Value * loadInputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) {
        return loadInputStreamPack(name, streamIndex, packIndex, nullptr);
    }

    llvm::Value * loadInputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * blockOffset);

    llvm::Value * getInputStreamSetCount(const std::string & name);

    llvm::Value * getOutputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex) {
        return getOutputStreamBlockPtr(name, streamIndex, nullptr);
    }

    llvm::Value * getOutputStreamBlockPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * blockOffset);

    llvm::Value * getOutputStreamLogicalBasePtr(const Binding & output);

    llvm::StoreInst * storeOutputStreamBlock(const std::string & name, llvm::Value * streamIndex, llvm::Value * toStore) {
        return storeOutputStreamBlock(name, streamIndex, nullptr, toStore);
    }

    llvm::StoreInst * storeOutputStreamBlock(const std::string & name, llvm::Value * streamIndex, llvm::Value * blockOffset, llvm::Value * toStore);

    llvm::Value * getOutputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex) {
        return getOutputStreamPackPtr(name, streamIndex, packIndex, nullptr);
    }

    llvm::Value * getOutputStreamPackPtr(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * blockOffset);

    llvm::StoreInst * storeOutputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * toStore) {
        return storeOutputStreamPack(name, streamIndex, packIndex, nullptr, toStore);
    }

    llvm::StoreInst * storeOutputStreamPack(const std::string & name, llvm::Value * streamIndex, llvm::Value * packIndex, llvm::Value * blockOffset, llvm::Value * toStore);

    llvm::Value * getOutputStreamSetCount(const std::string & name);

    llvm::Value * getRawInputPointer(const std::string & name, llvm::Value * absolutePosition);

    llvm::Value * getRawOutputPointer(const std::string & name, llvm::Value * absolutePosition);

    llvm::Value * getBaseAddress(const std::string & name);

    void setBaseAddress(const std::string & name, llvm::Value * addr);

    llvm::Value * getCapacity(const std::string & name);

    void setCapacity(const std::string & name, llvm::Value * capacity);

    llvm::CallInst * createDoSegmentCall(const std::vector<llvm::Value *> & args);

    const Kernel * getKernel() const {
        return mKernel;
    }

    void setKernel(const Kernel * const kernel) {
        mKernel = kernel;
    }

    // overloading wrongly subsitutes this for CBuilder function. renamed for now until I can investigate why.
    llvm::Value * CreateUDiv2(llvm::Value * const number, const ProcessingRate::RateValue & divisor, const llvm::Twine & Name = "");

    llvm::Value * CreateCeilUDiv2(llvm::Value * const number, const ProcessingRate::RateValue & divisor, const llvm::Twine & Name = "");

    llvm::Value * CreateMul2(llvm::Value * const number, const ProcessingRate::RateValue & factor, const llvm::Twine & Name = "");

    llvm::Value * CreateCeilUMul2(llvm::Value * const number, const ProcessingRate::RateValue & factor, const llvm::Twine & Name = "");

    llvm::Type * resolveStreamSetType(llvm::Type * streamSetType);

    unsigned getStride() const {
        return mStride;
    }

protected:

    KernelBuilder(llvm::LLVMContext & C, unsigned nativeVectorWidth, unsigned vectorWidth, unsigned laneWidth)
    : IDISA::IDISA_Builder(C, nativeVectorWidth, vectorWidth, laneWidth)
    , mStride(vectorWidth)
    , mKernel(nullptr) {

    }

    const unsigned mStride;

    llvm::Value * getScalarFieldPtr(llvm::Value * handle, llvm::Value * index);

    llvm::Value * getScalarFieldPtr(llvm::Value * instance, const std::string & fieldName);

    llvm::Value * getNamedItemCount(const std::string & name, const std::string & suffix);

    void setNamedItemCount(const std::string & name, const std::string & suffix, llvm::Value * const value);

    std::string getKernelName() const final;

protected:
    const Kernel * mKernel;

};

template <class SpecifiedArchitectureBuilder>
class KernelBuilderImpl final : public KernelBuilder, public SpecifiedArchitectureBuilder {
public:
    KernelBuilderImpl(llvm::LLVMContext & C, unsigned vectorWidth, unsigned laneWidth)
    : IDISA::IDISA_Builder(C, SpecifiedArchitectureBuilder::NativeBitBlockWidth, vectorWidth, laneWidth)
    , KernelBuilder(C, SpecifiedArchitectureBuilder::NativeBitBlockWidth, vectorWidth, laneWidth)
    , SpecifiedArchitectureBuilder(C, vectorWidth, laneWidth) {

    }
};

}

#endif // KERNEL_BUILDER_H
