#ifndef PIPELINE_KERNEL_H
#define PIPELINE_KERNEL_H

#include <kernel/core/kernel.h>
#include <type_traits>
#include <functional>
#include <kernel/pipeline/driver/driver.h>
#include <boost/container/flat_map.hpp>

namespace llvm { class Value; }

namespace kernel {

const static std::string INITIALIZE_FUNCTION_POINTER_SUFFIX = "_IFP";
const static std::string ALLOCATE_SHARED_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX = "_AFP";
const static std::string INITIALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX = "_ITFP";
const static std::string ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX = "_ATFP";
const static std::string DO_SEGMENT_FUNCTION_POINTER_SUFFIX = "_SFP";
const static std::string FINALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX = "_FTIP";
const static std::string FINALIZE_FUNCTION_POINTER_SUFFIX = "_FIP";

class PipelineAnalysis;
class PipelineBuilder;
class PipelineCompiler;

class PipelineKernel : public Kernel {
    friend class Kernel;
    friend class PipelineCompiler;
    friend class PipelineAnalysis;
    friend class PipelineBuilder;
public:

    static bool classof(const Kernel * const k) {
        return k->getTypeId() == TypeId::Pipeline;
    }

    static bool classof(const void *) { return false; }

public:

    using Scalars = std::vector<Scalar *>;
    using Kernels = std::vector<Kernel *>;

    struct CallBinding {
        std::string Name;
        llvm::FunctionType * Type;
        void * FunctionPointer;
        Scalars Args;

        mutable llvm::Constant * Callee;

        CallBinding(std::string Name, llvm::FunctionType * Type, void * FunctionPointer, std::initializer_list<Scalar *> && Args)
        : Name(std::move(Name)), Type(Type), FunctionPointer(FunctionPointer), Args(Args.begin(), Args.end()), Callee(nullptr) { }    
    };

    using CallBindings = std::vector<CallBinding>;

    using LengthAssertion = std::array<const StreamSet *, 2>;

    using LengthAssertions = std::vector<LengthAssertion>;

    bool hasSignature() const final { return true; }

    bool isCachable() const override;

    bool externallyInitialized() const override;

    void setInputStreamSetAt(const unsigned i, StreamSet * const value) final;

    void setOutputStreamSetAt(const unsigned i, StreamSet * const value) final;

    void setInputScalarAt(const unsigned i, Scalar * const value) final;

    void setOutputScalarAt(const unsigned i, Scalar * const value) final;

    llvm::StringRef getSignature() const final {
        return mSignature;
    }

    const unsigned getNumOfThreads() const {
        return mNumOfThreads;
    }

    const Kernels & getKernels() const {
        return mKernels;
    }

    const CallBindings & getCallBindings() const {
        return mCallBindings;
    }

    const LengthAssertions & getLengthAssertions() const {
        return mLengthAssertions;
    }

    void addKernelDeclarations(BuilderRef b) final;

    std::unique_ptr<KernelCompiler> instantiateKernelCompiler(BuilderRef b) const final;

    virtual ~PipelineKernel();

    virtual void instantiateNestedPipeline(const std::unique_ptr<PipelineBuilder> &) {}

protected:

    PipelineKernel(BuilderRef b,
                   std::string && signature,
                   const unsigned numOfThreads,
                   Kernels && kernels, CallBindings && callBindings,
                   Bindings && stream_inputs, Bindings && stream_outputs,
                   Bindings && scalar_inputs, Bindings && scalar_outputs,
                   LengthAssertions && lengthAssertions);


private:

    void addFamilyInitializationArgTypes(BuilderRef b, InitArgTypes & argTypes) const final;

    void recursivelyConstructFamilyKernels(BuilderRef b, InitArgs & args, const ParamMap & params, NestedStateObjs & toFree) const final;

    void linkExternalMethods(BuilderRef b) final;

    LLVM_READNONE bool allocatesInternalStreamSets() const final;

    void generateAllocateSharedInternalStreamSetsMethod(BuilderRef b, llvm::Value * expectedNumOfStrides) final;

    void generateAllocateThreadLocalInternalStreamSetsMethod(BuilderRef b, llvm::Value * expectedNumOfStrides) final;

    void addAdditionalFunctions(BuilderRef b) final;

    void addInternalProperties(BuilderRef b) final;

    void generateInitializeMethod(BuilderRef b) final;

    void generateInitializeThreadLocalMethod(BuilderRef b) final;

    void generateKernelMethod(BuilderRef b) final;

    void generateFinalizeThreadLocalMethod(BuilderRef b) final;

    void generateFinalizeMethod(BuilderRef b) final;

    void runOptimizationPasses(BuilderRef b) const final;

protected:

    const unsigned                            mNumOfThreads;
    const std::string                         mSignature;
    Kernels                                   mKernels;
    CallBindings                              mCallBindings;
    LengthAssertions                          mLengthAssertions;

};

}

#endif // PIPELINE_KERNEL_H
