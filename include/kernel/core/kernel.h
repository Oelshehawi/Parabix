/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#ifndef KERNEL_H
#define KERNEL_H

#include "binding_map.hpp"
#include "relationship.h"
#include "streamset.h"
#include <util/not_null.h>
#include <util/slab_allocator.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/Compiler.h>
#include <memory>
#include <string>
#include <vector>

namespace llvm { class IndirectBrInst; }
namespace llvm { class PHINode; }

class BaseDriver;

const static std::string BUFFER_HANDLE_SUFFIX = "_buffer";

namespace kernel {

class KernelBuilder;
class StreamSetBuffer;
class StreamSet;

class Kernel : public AttributeSet {
    friend class KernelBuilder;
    friend class PipelineBuilder;
    friend class PipelineCompiler;
    friend class PipelineKernel;
    friend class OptimizationBranch;
    friend class OptimizationBranchCompiler;
    friend class BaseDriver;
public:

    using BuilderRef = const std::unique_ptr<KernelBuilder> &;

    using ArgIterator = llvm::Function::arg_iterator;

    enum class TypeId {
        SegmentOriented
        , MultiBlock
        , BlockOriented
        , Pipeline
        , OptimizationBranch
    };

    static bool classof(const Kernel *) { return true; }

    static bool classof(const void *) { return false; }

    LLVM_READNONE TypeId getTypeId() const {
        return mTypeId;
    }

    enum class ScalarType { Input, Output, Internal, NonPersistent, ThreadLocal };

    struct InternalScalar {

        ScalarType getScalarType() const {
            return mScalarType;
        }

        llvm::Type * getValueType() const {
            return mValueType;
        }

        const std::string & getName() const {
            return mName;
        }

        const unsigned getGroup() const {
            return mGroup;
        }

        explicit InternalScalar(llvm::Type * const valueType,
                                const llvm::StringRef name, const unsigned group = 1)
        : InternalScalar(ScalarType::Internal, valueType, name, group) {

        }

        explicit InternalScalar(const ScalarType scalarType, llvm::Type * const valueType,
                                const llvm::StringRef name, const unsigned group = 1)
        : mScalarType(scalarType), mValueType(valueType), mName(name.str()), mGroup(group) {

        }

    private:
        const ScalarType        mScalarType;
        llvm::Type * const      mValueType;
        const std::string       mName;
        const unsigned          mGroup;
    };

    using InternalScalars = std::vector<InternalScalar>;

    using ScalarValueMap = llvm::StringMap<llvm::Value *>;

    enum class PortType { Input, Output };

    struct StreamSetPort {
        PortType Type;
        unsigned Number;

        StreamSetPort() : Type(PortType::Input), Number(0) { }
        explicit StreamSetPort(PortType Type, unsigned Number) : Type(Type), Number(Number) { }

        bool operator < (const StreamSetPort other) const {
            if (Type == other.Type) {
                return Number < other.Number;
            } else {
                return Type == PortType::Input;
            }
        }

        bool operator == (const StreamSetPort other) const {
            return (Type == other.Type) && (Number == other.Number);
        }
    };

    // Kernel Signatures and Module IDs
    //
    // A kernel signature uniquely identifies a kernel and its full functionality.
    // In the event that a particular kernel instance is to be generated and compiled
    // to produce object code, and we have a cached kernel object code instance with
    // the same signature and targetting the same IDISA architecture, then the cached
    // object code may safely be used to avoid recompilation.
    //
    // A kernel signature is a byte string of arbitrary length.
    //
    // Kernel developers should take responsibility for designing appropriate signature
    // mechanisms that are short, inexpensive to compute and guarantee uniqueness
    // based on the semantics of the kernel.
    //
    // If no other mechanism is available, the default makeSignature() method uses the
    // full LLVM IR (before optimization) of the kernel instance.
    //
    // A kernel Module ID is short string that is used as a name for a particular kernel
    // instance.  Kernel Module IDs are used to look up and retrieve cached kernel
    // instances and so should be highly likely to uniquely identify a kernel instance.
    //
    // The ideal case is that a kernel Module ID serves as a full kernel signature thus
    // guaranteeing uniqueness.  In this case, hasSignature() should return false.
    //

    //
    // Kernel builder subtypes define their logic of kernel construction
    // in terms of 3 virtual methods for
    // (a) preparing the Kernel state data structure
    // (c) defining the logic of the finalBlock function.
    //
    // Note: the kernel state data structure must only be finalized after
    // all scalar fields have been added.   If there are no fields to
    // be added, the default method for preparing kernel state may be used.

    LLVM_READNONE virtual const std::string getName() const {
        return mKernelName;
    }

    LLVM_READNONE virtual bool hasFamilyName() const {
        return false;
    }

    LLVM_READNONE virtual bool containsKernelFamilies() const {
        return false;
    }

    LLVM_READNONE virtual const std::string getFamilyName() const {
        if (hasFamilyName()) {
            return getDefaultFamilyName();
        } else {
            return getName();
        }
    }

    virtual std::string makeSignature(BuilderRef b) const;

    virtual bool hasSignature() const { return true; }

    virtual bool isCachable() const { return false; }

    LLVM_READNONE bool isStateful() const {
        return mSharedStateType != nullptr;
    }

    LLVM_READNONE bool hasThreadLocal() const {
        return mThreadLocalStateType  != nullptr;
    }

    unsigned getStride() const { return mStride; }

    void setStride(const unsigned stride) { mStride = stride; }

    const Bindings & getInputStreamSetBindings() const {
        return mInputStreamSets;
    }

    Bindings & getInputStreamSetBindings() {
        return mInputStreamSets;
    }

    const Binding & getInputStreamSetBinding(const unsigned i) const {
        assert (i < getNumOfStreamInputs());
        return mInputStreamSets[i];
    }

    LLVM_READNONE const Binding & getInputStreamSetBinding(const llvm::StringRef name) const {
        return getInputStreamSetBinding(getBinding(BindingType::StreamInput, name).Index);
    }

    LLVM_READNONE StreamSet * getInputStreamSet(const unsigned i) const {
        return llvm::cast<StreamSet>(getInputStreamSetBinding(i).getRelationship());
    }

    LLVM_READNONE StreamSet * getInputStreamSet(const llvm::StringRef name) const {
        return llvm::cast<StreamSet>(getInputStreamSetBinding(name).getRelationship());
    }

    void setInputStreamSet(const llvm::StringRef name, StreamSet * value) {
        setInputStreamSetAt(getBinding(BindingType::StreamInput, name).Index, value);
    }

    LLVM_READNONE unsigned getNumOfStreamInputs() const {
        return mInputStreamSets.size();
    }

    LLVM_READNONE const OwnedStreamSetBuffers & getInputStreamSetBuffers() const {
        return mStreamSetInputBuffers;
    }

    LLVM_READNONE StreamSetBuffer * getInputStreamSetBuffer(const unsigned i) const {
        assert (i < mStreamSetInputBuffers.size());
        assert (mStreamSetInputBuffers[i]);
        return mStreamSetInputBuffers[i].get();
    }

    LLVM_READNONE StreamSetBuffer * getInputStreamSetBuffer(const llvm::StringRef name) const {
        return getInputStreamSetBuffer(getBinding(BindingType::StreamInput, name).Index);
    }

    LLVM_READNONE const Binding & getOutputStreamSetBinding(const unsigned i) const {
        assert (i < getNumOfStreamOutputs());
        return mOutputStreamSets[i];
    }

    LLVM_READNONE const Binding & getOutputStreamSetBinding(const llvm::StringRef name) const {
        return getOutputStreamSetBinding(getBinding(BindingType::StreamOutput, name).Index);
    }

    LLVM_READNONE StreamSet * getOutputStreamSet(const unsigned i) const {
        return llvm::cast<StreamSet>(getOutputStreamSetBinding(i).getRelationship());
    }

    LLVM_READNONE StreamSet * getOutputStreamSet(const llvm::StringRef name) const {
        return llvm::cast<StreamSet>(getOutputStreamSetBinding(name).getRelationship());
    }

    void setOutputStreamSet(const llvm::StringRef name, StreamSet * value) {
        setOutputStreamSetAt(getBinding(BindingType::StreamOutput, name).Index, value);
    }

    const Bindings & getOutputStreamSetBindings() const {
        return mOutputStreamSets;
    }

    Bindings & getOutputStreamSetBindings() {
        return mOutputStreamSets;
    }

    unsigned getNumOfStreamOutputs() const {
        return mOutputStreamSets.size();
    }

    LLVM_READNONE const OwnedStreamSetBuffers & getOutputStreamSetBuffers() const {
        return mStreamSetOutputBuffers;
    }

    LLVM_READNONE StreamSetBuffer * getOutputStreamSetBuffer(const unsigned i) const {
        assert (i < mStreamSetOutputBuffers.size());
        assert (mStreamSetOutputBuffers[i]);
        return mStreamSetOutputBuffers[i].get();
    }

    LLVM_READNONE StreamSetBuffer * getOutputStreamSetBuffer(const llvm::StringRef name) const {
        return getOutputStreamSetBuffer(getBinding(BindingType::StreamOutput, name).Index);
    }

    const Bindings & getInputScalarBindings() const {
        return mInputScalars;
    }

    Bindings & getInputScalarBindings() {
        return mInputScalars;
    }

    const Binding & getInputScalarBinding(const unsigned i) const {
        assert (i < mInputScalars.size());
        return mInputScalars[i];
    }

    LLVM_READNONE const Binding & getInputScalarBinding(const llvm::StringRef name) const {
        return getInputScalarBinding(getBinding(BindingType::ScalarInput, name).Index);
    }

    LLVM_READNONE Scalar * getInputScalar(const unsigned i) {
        return llvm::cast<Scalar>(getInputScalarBinding(i).getRelationship());
    }

    LLVM_READNONE Scalar * getInputScalar(const llvm::StringRef name) {
        return llvm::cast<Scalar>(getInputScalarBinding(name).getRelationship());
    }

    LLVM_READNONE unsigned getNumOfScalarInputs() const {
        return mInputScalars.size();
    }

    const Bindings & getOutputScalarBindings() const {
        return mOutputScalars;
    }

    Bindings & getOutputScalarBindings() {
        return mOutputScalars;
    }

    const Binding & getOutputScalarBinding(const unsigned i) const {
        assert (i < mOutputScalars.size());
        return mOutputScalars[i];
    }

    LLVM_READNONE const Binding & getOutputScalarBinding(const llvm::StringRef name) const {
        return getOutputScalarBinding(getBinding(BindingType::ScalarOutput, name).Index);
    }

    LLVM_READNONE Scalar * getOutputScalar(const llvm::StringRef name) {
        return llvm::cast<Scalar>(getOutputScalarBinding(name).getRelationship());
    }

    LLVM_READNONE Scalar * getOutputScalar(const unsigned i) {
        return llvm::cast<Scalar>(getOutputScalarBinding(i).getRelationship());
    }


    LLVM_READNONE unsigned getNumOfScalarOutputs() const {
        return mOutputScalars.size();
    }

    void addInternalScalar(llvm::Type * type, const llvm::StringRef name, const unsigned group = 1) {
        mInternalScalars.emplace_back(ScalarType::Internal, type, name, group);
    }

    void addNonPersistentScalar(llvm::Type * type, const llvm::StringRef name) {
        mInternalScalars.emplace_back(ScalarType::NonPersistent, type, name, 0);
    }

    void addThreadLocalScalar(llvm::Type * type, const llvm::StringRef name, const unsigned group = 1) {
        mInternalScalars.emplace_back(ScalarType::ThreadLocal, type, name, group);
    }

    llvm::Value * getHandle() const {
        return mSharedHandle;
    }

    void setHandle(BuilderRef b, llvm::Value * const handle) const;

    llvm::Value * getThreadLocalHandle() const {
        return mThreadLocalHandle;
    }

    void setThreadLocalHandle(llvm::Value * const handle) const {
        mThreadLocalHandle = handle;
    }

    llvm::Module * setModule(llvm::Module * const module);

    llvm::Module * getModule() const {
        return mModule;
    }

    llvm::StructType * getSharedStateType() const {
        return mSharedStateType;
    }

    llvm::StructType * getThreadLocalStateType() const {
        return mThreadLocalStateType;
    }

    LLVM_READNONE const StreamSetBuffer * getStreamSetBuffer(const llvm::StringRef name) const {
        const auto port = getStreamPort(name);
        if (port.Type == PortType::Input) {
            return getInputStreamSetBuffer(port.Number);
        } else {
            return getOutputStreamSetBuffer(port.Number);
        }
    }

    llvm::Module * makeModule(BuilderRef b);

    // Add ExternalLinkage method declarations for the kernel to a given client module.
    virtual void addKernelDeclarations(BuilderRef b);

    llvm::Value * createInstance(BuilderRef b) const;

    void initializeInstance(BuilderRef b, llvm::ArrayRef<llvm::Value *> args);

    llvm::Value * finalizeInstance(BuilderRef b, llvm::Value * const handle) const;

    llvm::Value * initializeThreadLocalInstance(BuilderRef b, llvm::Value * handle);

    void finalizeThreadLocalInstance(BuilderRef b, llvm::ArrayRef<llvm::Value *> args) const;

    void generateKernel(BuilderRef b);

    void prepareKernel(BuilderRef b);

    void prepareCachedKernel(BuilderRef b);

    LLVM_READNONE std::string getCacheName(BuilderRef b) const;

    LLVM_READNONE StreamSetPort getStreamPort(const llvm::StringRef name) const;

    LLVM_READNONE const Binding & getStreamBinding(const llvm::StringRef name) const {
        return getStreamBinding(getStreamPort(name));
    }

    LLVM_READNONE const Binding & getStreamBinding(const StreamSetPort port) const {
        return (port.Type == PortType::Input) ? getInputStreamSetBinding(port.Number) : getOutputStreamSetBinding(port.Number);
    }

    LLVM_READNONE ProcessingRate::RateValue getLowerBound(const Binding & binding) const;

    LLVM_READNONE ProcessingRate::RateValue getUpperBound(const Binding & binding) const;

    LLVM_READNONE bool requiresOverflow(const Binding & binding) const;

    /* Fill in any generated names / attributes for the kernel if their initialization is dependent on
     * settings / bindings added after construction. */
    virtual void finalizeKernel() { }

    enum MainMethodGenerationType {
        AddInternal
        , DeclareExternal
        , AddExternal
    };

    virtual llvm::Function * addOrDeclareMainFunction(BuilderRef b, const MainMethodGenerationType method);

    using InitArgs = llvm::SmallVector<llvm::Value *, 32>;

    using InitArgTypes = llvm::SmallVector<llvm::Type *, 32>;

    using ParamMap = llvm::DenseMap<Scalar *, llvm::Value *>;

    llvm::Value * constructFamilyKernels(BuilderRef b, InitArgs & hostArgs, const ParamMap & params) const;

    virtual bool hasStaticMain() const { return true; }

    virtual ~Kernel() = 0;

protected:

    static std::string getStringHash(const llvm::StringRef str);

    LLVM_READNONE std::string getDefaultFamilyName() const;

    virtual void addInternalProperties(BuilderRef) { }

    virtual void linkExternalMethods(BuilderRef) { }

    virtual void generateInitializeMethod(BuilderRef) { }

    virtual void generateInitializeThreadLocalMethod(BuilderRef) { }

    virtual void generateKernelMethod(BuilderRef) = 0;

    virtual void generateFinalizeThreadLocalMethod(BuilderRef) { }

    virtual void generateFinalizeMethod(BuilderRef) { }

    virtual void addAdditionalFunctions(BuilderRef) { }

    virtual void setInputStreamSetAt(const unsigned i, StreamSet * value);

    virtual void setOutputStreamSetAt(const unsigned i, StreamSet * value);

    virtual void setInputScalarAt(const unsigned i, Scalar * value);

    virtual void setOutputScalarAt(const unsigned i, Scalar * value);

    virtual std::vector<llvm::Value *> getFinalOutputScalars(BuilderRef b);

    LLVM_READNONE const BindingMapEntry & getBinding(const BindingType type, const llvm::StringRef name) const;

    LLVM_READNONE llvm::Value * getAccessibleInputItems(const llvm::StringRef name) const {
        return getAccessibleInputItems(getBinding(BindingType::StreamInput, name).Index);
    }

    LLVM_READNONE llvm::Value * getAccessibleInputItems(const unsigned index) const {
        assert (index < mAccessibleInputItems.size());
        return mAccessibleInputItems[index];
    }

    LLVM_READNONE llvm::Value * getAvailableInputItems(const llvm::StringRef name) const {
        return getAvailableInputItems(getBinding(BindingType::StreamInput, name).Index);
    }

    LLVM_READNONE llvm::Value * getAvailableInputItems(const unsigned index) const {
        assert (index < mAvailableInputItems.size());
        return mAvailableInputItems[index];
    }

    LLVM_READNONE bool canSetTerminateSignal() const;

    LLVM_READNONE llvm::Value * getTerminationSignalPtr() const {
        return mTerminationSignalPtr;
    }

    LLVM_READNONE llvm::Value * getProcessedInputItemsPtr(const llvm::StringRef name) const {
        return getProcessedInputItemsPtr(getBinding(BindingType::StreamInput, name).Index);
    }

    LLVM_READNONE llvm::Value * getProcessedInputItemsPtr(const unsigned index) const {
        return mProcessedInputItemPtr[index];
    }

    LLVM_READNONE llvm::Value * getProducedOutputItemsPtr(const llvm::StringRef name) const {
        return getProducedOutputItemsPtr(getBinding(BindingType::StreamOutput, name).Index);
    }

    LLVM_READNONE llvm::Value * getProducedOutputItemsPtr(const unsigned index) const {
        return mProducedOutputItemPtr[index];
    }

    LLVM_READNONE llvm::Value * getWritableOutputItems(const llvm::StringRef name) const {
        return getWritableOutputItems(getBinding(BindingType::StreamOutput, name).Index);
    }

    LLVM_READNONE llvm::Value * getWritableOutputItems(const unsigned index) const {
        return mWritableOutputItems[index];
    }

    LLVM_READNONE llvm::Value * getConsumedOutputItems(const llvm::StringRef name) const {
        return getConsumedOutputItems(getBinding(BindingType::StreamOutput, name).Index);
    }

    LLVM_READNONE llvm::Value * getConsumedOutputItems(const unsigned index) const {
        return mConsumedOutputItems[index];
    }

    llvm::Value * getNumOfStrides() const {
        return mNumOfStrides;
    }

    llvm::Value * getExternalSegNo() const {
        return mExternalSegNo;
    }

    LLVM_READNONE llvm::Value * isFinal() const {
        return mIsFinal;
    }

    virtual void addFamilyInitializationArgTypes(BuilderRef b, InitArgTypes & argTypes) const;

    virtual void bindFamilyInitializationArguments(BuilderRef b, ArgIterator & arg, const ArgIterator & arg_end) const;

    virtual void recursivelyConstructFamilyKernels(BuilderRef b, InitArgs & args, const ParamMap & params) const;

    // Constructor
    Kernel(BuilderRef b,
           const TypeId typeId, std::string && kernelName,
           Bindings &&stream_inputs, Bindings &&stream_outputs,
           Bindings &&scalar_inputs, Bindings &&scalar_outputs,
           InternalScalars && internal_scalars);

private:

    llvm::Function * addInitializeDeclaration(BuilderRef b) const;

    void callGenerateInitializeMethod(BuilderRef b);

    llvm::Function * addInitializeThreadLocalDeclaration(BuilderRef b) const;

    void callGenerateInitializeThreadLocalMethod(BuilderRef b);

    llvm::Function * addDoSegmentDeclaration(BuilderRef b) const;

    std::vector<llvm::Type *> getDoSegmentFields(BuilderRef b) const;

    void callGenerateDoSegmentMethod(BuilderRef b);

    void setDoSegmentProperties(BuilderRef b, const llvm::ArrayRef<llvm::Value *> args);

    std::vector<llvm::Value *> getDoSegmentProperties(BuilderRef b) const;

    llvm::Function * addFinalizeThreadLocalDeclaration(BuilderRef b) const;

    void callGenerateFinalizeThreadLocalMethod(BuilderRef b);

    llvm::Function * addFinalizeDeclaration(BuilderRef b) const;

    void callGenerateFinalizeMethod(BuilderRef b);

    void addBaseKernelProperties(BuilderRef b);

    llvm::Function * getInitializeFunction(BuilderRef b, const bool alwayReturnDeclaration = true) const;

    llvm::Function * getInitializeThreadLocalFunction(BuilderRef b, const bool alwayReturnDeclaration = true) const;

    llvm::Function * getDoSegmentFunction(BuilderRef b, const bool alwayReturnDeclaration = true) const;

    llvm::Function * getFinalizeThreadLocalFunction(BuilderRef b, const bool alwayReturnDeclaration = true) const;

    llvm::Function * getFinalizeFunction(BuilderRef b, const bool alwayReturnDeclaration = true) const;

    void constructStateTypes(BuilderRef b);

    enum class InitializeScalarMapOptions {
        SkipThreadLocal
        , IncludeThreadLocal
    };

    void initializeScalarMap(BuilderRef b, const InitializeScalarMapOptions options) const;

    unsigned getSharedScalarIndex(KernelBuilder * b, const llvm::StringRef name) const;

    llvm::Value * getScalarValuePtr(KernelBuilder * b, const llvm::StringRef name) const;

    void setTerminationSignalPtr(llvm::Value * ptr) {
        mTerminationSignalPtr = ptr;
    }

    void setExternalSegNo(llvm::Value * segNo) {
        mExternalSegNo = segNo;
    }

protected:

    mutable bool                    mIsGenerated = false;

    mutable llvm::Value *           mSharedHandle = nullptr;
    mutable llvm::Value *           mThreadLocalHandle = nullptr;

    llvm::Module *                  mModule = nullptr;
    llvm::StructType *              mSharedStateType = nullptr;
    llvm::StructType *              mThreadLocalStateType = nullptr;

    Bindings                        mInputStreamSets;
    Bindings                        mOutputStreamSets;

    Bindings                        mInputScalars;
    Bindings                        mOutputScalars;
    InternalScalars                 mInternalScalars;

    llvm::Function *                mCurrentMethod = nullptr;
    unsigned                        mStride;

    llvm::Value *                   mTerminationSignalPtr = nullptr;
    llvm::Value *                   mIsFinal = nullptr;
    llvm::Value *                   mNumOfStrides = nullptr;
    llvm::Value *                   mFixedRateFactor = nullptr;
    llvm::Value *                   mThreadLocalPtr = nullptr;
    llvm::Value *                   mExternalSegNo = nullptr;

    std::vector<llvm::Value *>      mUpdatableProcessedInputItemPtr;
    std::vector<llvm::Value *>      mProcessedInputItemPtr;

    std::vector<llvm::Value *>      mAccessibleInputItems;
    std::vector<llvm::Value *>      mAvailableInputItems;
    std::vector<llvm::Value *>      mPopCountRateArray;
    std::vector<llvm::Value *>      mNegatedPopCountRateArray;

    std::vector<llvm::Value *>      mUpdatableProducedOutputItemPtr;
    std::vector<llvm::Value *>      mProducedOutputItemPtr;

    std::vector<llvm::Value *>      mWritableOutputItems;
    std::vector<llvm::Value *>      mConsumedOutputItems;

    mutable ScalarValueMap          mScalarValueMap;
    mutable BindingMap              mBindingMap;

    const std::string               mKernelName;
    const TypeId                    mTypeId;

    mutable OwnedStreamSetBuffers   mStreamSetInputBuffers;
    mutable OwnedStreamSetBuffers   mStreamSetOutputBuffers;

};

class SegmentOrientedKernel : public Kernel {
public:

    static bool classof(const Kernel * const k) {
        return k->getTypeId() == TypeId::SegmentOriented;
    }

    static bool classof(const void *) { return false; }

protected:

    SegmentOrientedKernel(BuilderRef b,
                          std::string && kernelName,
                          Bindings &&stream_inputs,
                          Bindings &&stream_outputs,
                          Bindings &&scalar_parameters,
                          Bindings &&scalar_outputs,
                          InternalScalars && internal_scalars);
public:

    virtual void generateDoSegmentMethod(BuilderRef b) = 0;

protected:

    void generateKernelMethod(BuilderRef b) final;

};

class MultiBlockKernel : public Kernel {
    friend class BlockOrientedKernel;
    friend class OptimizationBranch;
public:

    static bool classof(const Kernel * const k) {
        return k->getTypeId() == TypeId::MultiBlock;
    }

    static bool classof(const void *) { return false; }

protected:

    MultiBlockKernel(BuilderRef b,
                     std::string && kernelName,
                     Bindings && stream_inputs,
                     Bindings && stream_outputs,
                     Bindings && scalar_parameters,
                     Bindings && scalar_outputs,
                     InternalScalars && internal_scalars);

    virtual void generateMultiBlockLogic(BuilderRef b, llvm::Value * const numOfStrides) = 0;

private:

    MultiBlockKernel(BuilderRef b,
                     const TypeId kernelTypId,
                     std::string && kernelName,
                     Bindings && stream_inputs,
                     Bindings && stream_outputs,
                     Bindings && scalar_parameters,
                     Bindings && scalar_outputs,
                     InternalScalars && internal_scalars);

private:

    void generateKernelMethod(BuilderRef b) final;

};


class BlockOrientedKernel : public MultiBlockKernel {
public:

    static bool classof(const Kernel * const k) {
        return k->getTypeId() == TypeId::BlockOriented;
    }

    static bool classof(const void *) { return false; }

protected:

    void CreateDoBlockMethodCall(BuilderRef b);

    // Each kernel builder subtype must provide its own logic for generating
    // doBlock calls.
    virtual void generateDoBlockMethod(BuilderRef b) = 0;

    // Each kernel builder subtypre must also specify the logic for processing the
    // final block of stream data, if there is any special processing required
    // beyond simply calling the doBlock function.   In the case that the final block
    // processing may be trivially implemented by dispatching to the doBlock method
    // without additional preparation, the default generateFinalBlockMethod need
    // not be overridden.

    virtual void generateFinalBlockMethod(BuilderRef b, llvm::Value * remainingItems);

    BlockOrientedKernel(BuilderRef b,
                        std::string && kernelName,
                        Bindings && stream_inputs,
                        Bindings && stream_outputs,
                        Bindings && scalar_parameters,
                        Bindings && scalar_outputs,
                        InternalScalars && internal_scalars);

    llvm::Value * getRemainingItems(BuilderRef b);

private:

    void annotateInputBindingsWithPopCountArrayAttributes();

    void incrementCountableItemCounts(BuilderRef b);

    llvm::Value * getPopCountRateItemCount(BuilderRef b, const ProcessingRate & rate);

    void generateMultiBlockLogic(BuilderRef b, llvm::Value * const numOfStrides) final;

    void writeDoBlockMethod(BuilderRef b);

    void writeFinalBlockMethod(BuilderRef b, llvm::Value * remainingItems);

private:

    llvm::Function *            mDoBlockMethod;
    llvm::BasicBlock *          mStrideLoopBody;
    llvm::IndirectBrInst *      mStrideLoopBranch;
    llvm::PHINode *             mStrideLoopTarget;
    llvm::PHINode *             mStrideBlockIndex;
};

}

#endif
