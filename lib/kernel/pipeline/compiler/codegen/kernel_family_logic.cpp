#include "../pipeline_compiler.hpp"

namespace kernel {

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addFamilyKernelProperties
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::addFamilyKernelProperties(BuilderRef b,
                                                 const unsigned kernelId,
                                                 const unsigned groupId) const {
    if (LLVM_UNLIKELY(isKernelFamilyCall(kernelId))) {

        PointerType * const voidPtrTy = b->getVoidPtrTy();
        const auto prefix = makeKernelName(kernelId);
        const auto tl = mKernel->hasThreadLocal();
        const auto ai = mKernel->allocatesInternalStreamSets();
        if (ai) {
            mTarget->addInternalScalar(voidPtrTy, prefix + ALLOCATE_SHARED_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX, groupId);
        }
        if (tl) {
            mTarget->addInternalScalar(voidPtrTy, prefix + INITIALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX, groupId);
            if (ai) {
                mTarget->addInternalScalar(voidPtrTy, prefix + ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX, groupId);
            }
        }
        mTarget->addInternalScalar(voidPtrTy, prefix + DO_SEGMENT_FUNCTION_POINTER_SUFFIX, groupId);
        if (tl) {
            mTarget->addInternalScalar(voidPtrTy, prefix + FINALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX, groupId);
        }
        mTarget->addInternalScalar(voidPtrTy, prefix + FINALIZE_FUNCTION_POINTER_SUFFIX, groupId);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief bindFamilyInitializationArguments
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::bindFamilyInitializationArguments(BuilderRef b, ArgIterator & arg, const ArgIterator & arg_end) const {

  //  PointerType * const voidPtrTy = b->getVoidPtrTy();

    #ifndef NDEBUG
    unsigned inputNum = 0;
    #endif
    Constant * voidPtr = ConstantPointerNull::get(b->getVoidPtrTy());

    for (auto binding : make_iterator_range(out_edges(PipelineInput, mFamilyScalarGraph))) {

        auto & D = mFamilyScalarGraph[binding];
        assert (D.InputNum == inputNum++);
        const auto kernelId = target(binding, mFamilyScalarGraph);
        assert (kernelId != PipelineInput);

        auto nextArg = [&](const unsigned flags) {
            assert (arg != arg_end);
            Value * v = &*arg;
            assert (v->getType() == b->getVoidPtrTy());


//            b->CallPrintInt(" < " + getName() + "." +
//                            getKernel(kernelId)->getName() + ".arg" +
//                            std::to_string(arg->getArgNo()), v);

            if ((D.CaptureFlags & flags) == flags) {
//                v = &*arg;
//                assert (v->getType() == b->getVoidPtrTy());
                b->CreateAssert(v, "invalid family param %" PRIu64, b->getSize(arg->getArgNo()));
            } else {
//                v = &*arg;
//                assert (v->getType() == b->getVoidPtrTy());
                b->CreateAssertZero(v, "invalid non-zero family param %" PRIu64, b->getSize(arg->getArgNo()));
                v = voidPtr;
            }
            std::advance(arg, 1);
            return v;
        };

        assert (D.SharedStateObject == nullptr);

        D.SharedStateObject =
            nextArg(FamilyScalarData::CaptureSharedStateObject);
        D.allocateSharedInternalStreamSetsFuncPointer =
            nextArg(FamilyScalarData::CaptureAllocateInternal);
        D.initializeThreadLocalFuncPointer =
            nextArg(FamilyScalarData::CaptureThreadLocal);
        D.allocateThreadLocalFuncPointer =
            nextArg(FamilyScalarData::CaptureThreadLocal | FamilyScalarData::CaptureAllocateInternal);
        D.doSegmentFuncPointer =
            nextArg(0);
        D.finalizeThreadLocalFuncPointer =
            nextArg(FamilyScalarData::CaptureThreadLocal);
        D.finalizeFuncPointer =
            nextArg(0);

        if ((D.CaptureFlags & FamilyScalarData::CaptureStoreInKernelState) != 0) {

            // get the internal prefix for this kernel.
            const auto prefix = makeKernelName(kernelId);

            auto storeNextScalar = [&](const StringRef name, Value * value) {
                auto ptr = getScalarFieldPtr(b.get(), name); assert (ptr);
                if (LLVM_UNLIKELY(CheckAssertions)) {
                    b->CreateAssert(value, "family parameter (%s) was given a null value", b->GetString(name));
                }
                b->CreateStore(value, ptr);
            };

            if (LLVM_LIKELY((D.CaptureFlags & FamilyScalarData::CaptureSharedStateObject) != 0)) {
                storeNextScalar(prefix, D.SharedStateObject);
            }

            if ((D.CaptureFlags & FamilyScalarData::CaptureAllocateInternal) != 0) {
                storeNextScalar(prefix + ALLOCATE_SHARED_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX, D.allocateSharedInternalStreamSetsFuncPointer);
            }
            if ((D.CaptureFlags & FamilyScalarData::CaptureThreadLocal) != 0) {
                storeNextScalar(prefix + INITIALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX, D.initializeThreadLocalFuncPointer);
                if ((D.CaptureFlags & FamilyScalarData::CaptureAllocateInternal) != 0) {
                    storeNextScalar(prefix + ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX, D.allocateThreadLocalFuncPointer);
                }
            }
            storeNextScalar(prefix + DO_SEGMENT_FUNCTION_POINTER_SUFFIX, D.doSegmentFuncPointer);
            if ((D.CaptureFlags & FamilyScalarData::CaptureThreadLocal) != 0) {
                storeNextScalar(prefix + FINALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX, D.finalizeThreadLocalFuncPointer);
            }
            storeNextScalar(prefix + FINALIZE_FUNCTION_POINTER_SUFFIX, D.finalizeFuncPointer);
        }
    }

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addFamilyCallInitializationArguments
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::addFamilyCallInitializationArguments(BuilderRef b, const unsigned kernelId, ArgVec & args) const {

    #ifndef NDEBUG
    unsigned paramNum = 0;
    #endif

    for (auto binding : make_iterator_range(in_edges(PipelineOutput + kernelId, mFamilyScalarGraph))) {
        const FamilyScalarData & D = mFamilyScalarGraph[binding];
        assert (D.PassedParamNum == paramNum++);
        args.push_back(D.SharedStateObject);
        args.push_back(D.allocateSharedInternalStreamSetsFuncPointer);
        args.push_back(D.initializeThreadLocalFuncPointer);
        args.push_back(D.allocateThreadLocalFuncPointer);
        args.push_back(D.doSegmentFuncPointer);
        assert(isFromCurrentFunction(b.get(), D.doSegmentFuncPointer, false));
        args.push_back(D.finalizeThreadLocalFuncPointer);
        args.push_back(D.finalizeFuncPointer);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getInitializationFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::callKernelInitializeFunction(BuilderRef b, const ArgVec & args) const {
    Function * const init = mKernel->getInitializeFunction(b);
    assert (init->getFunctionType()->getNumParams() == args.size());
    return b->CreateCall(init->getFunctionType(), init, args);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getInitializationThreadLocalFunction
 ** ------------------------------------------------------------------------------------------------------------- */
 void PipelineCompiler::callKernelInitializeThreadLocalFunction(BuilderRef b) const {
    Function * const init = mKernel->getInitializeThreadLocalFunction(b);
    Value * func = init;
    if (isKernelFamilyCall(mKernelId)) {
        func = getFamilyFunctionFromKernelState(b, init->getType(), INITIALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX);
    }
    SmallVector<Value *, 2> args;
    if (mKernelSharedHandle) {
        args.push_back(mKernelSharedHandle);
    }
    const auto prefix = makeKernelName(mKernelId);
    Value * const threadLocal = getScalarFieldPtr(b.get(), prefix + KERNEL_THREAD_LOCAL_SUFFIX);

    if (isKernelFamilyCall(mKernelId)) {
        PointerType * const ptrTy = cast<PointerType>(init->getFunctionType()->getParamType(args.size()));
        args.push_back(ConstantPointerNull::getNullValue(ptrTy));
    } else {
        args.push_back(threadLocal);
    }
    Value * const retVal = b->CreateCall(init->getFunctionType(), func, args);
    if (isKernelFamilyCall(mKernelId)) {
        b->CreateStore(b->CreatePointerCast(retVal, b->getVoidPtrTy()), threadLocal);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getKernelAllocateSharedInternalStreamSetsFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::getKernelAllocateSharedInternalStreamSetsFunction(BuilderRef b) const {
    Function * const term = mKernel->getAllocateSharedInternalStreamSetsFunction(b, false);
    if (isKernelFamilyCall(mKernelId)) {
        return getFamilyFunctionFromKernelState(b, term->getType(), ALLOCATE_SHARED_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX);
    }
    return term;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getKernelAllocateThreadLocalInternalStreamSetsFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::getKernelAllocateThreadLocalInternalStreamSetsFunction(BuilderRef b) const {
    Function * const term = mKernel->getAllocateThreadLocalInternalStreamSetsFunction(b, false);
    if (isKernelFamilyCall(mKernelId)) {
        return getFamilyFunctionFromKernelState(b, term->getType(), ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_FUNCTION_POINTER_SUFFIX);
    }
    return term;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getDoSegmentFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::getKernelDoSegmentFunction(BuilderRef b) const {
    Function * const doSegment = mKernel->getDoSegmentFunction(b);
    if (isKernelFamilyCall(mKernelId)) {
        return getFamilyFunctionFromKernelState(b, doSegment->getType(), DO_SEGMENT_FUNCTION_POINTER_SUFFIX);
    }
    return doSegment;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getInitializationThreadLocalFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::callKernelFinalizeThreadLocalFunction(BuilderRef b, const SmallVector<Value *, 2> & args) const {
    Function * const finalize = mKernel->getFinalizeThreadLocalFunction(b);
    Value * func = finalize;
    if (isKernelFamilyCall(mKernelId)) {
        func = getFamilyFunctionFromKernelState(b, finalize->getType(), FINALIZE_THREAD_LOCAL_FUNCTION_POINTER_SUFFIX);
    }
    return b->CreateCall(finalize->getFunctionType(), func, args);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getFinalizeFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::callKernelFinalizeFunction(BuilderRef b, const SmallVector<Value *, 1> & args) const {
    Function * const term = mKernel->getFinalizeFunction(b);
    Value * func = term;
    if (isKernelFamilyCall(mKernelId)) {
        func = getFamilyFunctionFromKernelState(b, term->getType(), FINALIZE_FUNCTION_POINTER_SUFFIX);
    }
    return b->CreateCall(term->getFunctionType(), func, args);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getFamilyFunctionFromKernelState
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::getFamilyFunctionFromKernelState(BuilderRef b, Type * const type, const std::string & suffix) const {
    const auto prefix = makeKernelName(mKernelId);
    Value * const funcPtr = b->getScalarField(prefix + suffix);
    assert (funcPtr->getType() == b->getVoidPtrTy());
    if (LLVM_UNLIKELY(CheckAssertions)) {
        b->CreateAssert(funcPtr, prefix + suffix + " is null");
    }
    return b->CreatePointerCast(funcPtr, type);
}

}
