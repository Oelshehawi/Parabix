/*
 *  Copyright (c) 2018 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#include <kernel/core/kernel.h>
#include <kernel/core/kernel_compiler.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <boost/container/flat_set.hpp>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Format.h>
#include <llvm/Analysis/ConstantFolding.h>
#if BOOST_VERSION < 106600
#include <boost/uuid/sha1.hpp>
#else
#include <boost/uuid/detail/sha1.hpp>
#endif
#include <boost/intrusive/detail/math.hpp>

using namespace llvm;
using namespace boost;
using boost::container::flat_set;
using IDISA::FixedVectorType;

using boost::intrusive::detail::floor_log2;
using boost::intrusive::detail::is_pow2;

namespace kernel {

using AttrId = Attribute::KindId;
using Rational = ProcessingRate::Rational;
using RateId = ProcessingRate::KindId;
using StreamSetPort = Kernel::StreamSetPort;
using PortType = Kernel::PortType;

const static auto INITIALIZE_SUFFIX = "_Initialize";
const static auto INITIALIZE_THREAD_LOCAL_SUFFIX = "_InitializeThreadLocal";
const static auto ALLOCATE_SHARED_INTERNAL_STREAMSETS_SUFFIX = "_AllocateSharedInternalStreamSets";
const static auto ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_SUFFIX = "_AllocateThreadLocalInternalStreamSets";
const static auto DO_SEGMENT_SUFFIX = "_DoSegment";
const static auto FINALIZE_THREAD_LOCAL_SUFFIX = "_FinalizeThreadLocal";
const static auto FINALIZE_SUFFIX = "_Finalize";
#ifdef ENABLE_PAPI
const static auto PAPI_INITIALIZE_EVENTSET = "_PAPIInitializeEventSet";
#endif

const static auto SHARED_SUFFIX = "_shared_state";
const static auto THREAD_LOCAL_SUFFIX = "_thread_local";

#define BEGIN_SCOPED_REGION {
#define END_SCOPED_REGION }

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief isLocalBuffer
 ** ------------------------------------------------------------------------------------------------------------- */
/* static */ bool Kernel::isLocalBuffer(const Binding & output, const bool includeShared) {
    // NOTE: if this function is modified, fix the PipelineCompiler to match it.
    for (const auto & attr : output.getAttributes()) {
        switch (attr.getKind()) {
            case Binding::AttributeId::SharedManagedBuffer:
                if (!includeShared) break;
            case Binding::AttributeId::ManagedBuffer:
            case Binding::AttributeId::ReturnedBuffer:
                return true;
            default: break;
        }
    }
    return output.getRate().isUnknown();
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief requiresExplicitPartialFinalStride
 ** ------------------------------------------------------------------------------------------------------------- */
bool Kernel::requiresExplicitPartialFinalStride() const {
    if (LLVM_UNLIKELY(hasAttribute(AttrId::InternallySynchronized))) {
        return false;
    }
    const auto m = getNumOfStreamOutputs();
    for (unsigned i = 0; i < m; ++i) {
        const Binding & output = getOutputStreamSetBinding(i);
        for (const Attribute & attr : output.getAttributes()) {
            switch (attr.getKind()) {
                case AttrId::Add:
                case AttrId::Delayed:
                    if (LLVM_LIKELY(attr.amount() > 0)) {
                        return true;
                    }
                case AttrId::Deferred:
                    return true;
                default: break;
            }
        }
    }
    return false;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief hasFixedRateIO
 ** ------------------------------------------------------------------------------------------------------------- */
bool Kernel::hasFixedRateIO() const {
    for (const auto & input : mInputStreamSets) {
        const ProcessingRate & rate = input.getRate();
        if (rate.isFixed()) {
            return true;
        }
    }
    for (const auto & output : mOutputStreamSets) {
        const ProcessingRate & rate = output.getRate();
        if (rate.isFixed()) {
            return true;
        }
    }
    return false;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief canSetTerminateSignal
 ** ------------------------------------------------------------------------------------------------------------ */
bool Kernel::canSetTerminateSignal() const {
    for (const Attribute & attr : getAttributes()) {
        switch (attr.getKind()) {
            case AttrId::MayFatallyTerminate:
            case AttrId::CanTerminateEarly:
            case AttrId::MustExplicitlyTerminate:
                return true;
            default: continue;
        }
    }
    return false;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief instantiateKernelCompiler
 ** ------------------------------------------------------------------------------------------------------------- */
std::unique_ptr<KernelCompiler> Kernel::instantiateKernelCompiler(BuilderRef /* b */) const {
    return std::make_unique<KernelCompiler>(const_cast<Kernel *>(this));
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeCacheName
 ** ------------------------------------------------------------------------------------------------------------- */
std::string Kernel::makeCacheName(BuilderRef b) {
    std::string cacheName;
    raw_string_ostream out(cacheName);
    out << getName() << '_' << b->getBuilderUniqueName();
#if 0
    auto appendStreamSetType = [&](const char code, const Bindings & bindings) {
        for (const auto & binding : bindings) {
            const auto r = static_cast<const StreamSet *>(binding.getRelationship();
            out << '_' << code << r->getNumElements() << 'x' << r->getFieldWidth();
        }
    };
    appendStreamSetType('I', mInputStreamSets);
    appendStreamSetType('O', mOutputStreamSets);
    auto appendScalarType = [&](const char code, const Bindings & bindings) {
        for (const auto & binding : bindings) {
            const auto r = static_cast<const Scalar *>(binding.getRelationship();
            out << '_' << code << r->getFieldWidth();
        }
    };
    appendScalarType('I', mInputScalars);
    appendScalarType('O', mOutputScalars);

    for (const auto & internal : mInternalScalars) {
        out << 'X' << (unsigned)internal.getScalarType()
            << '.' << internal.getGroup();
        internal.getType().print(out);
    }
#endif
    out.flush();
    return cacheName;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief makeModule
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::makeModule(BuilderRef b) {
    // NOTE: this assumes that the BuilderRef used to make the module has the same config as the
    // one that generates it later. Would be better if this didn't but that will require redesigning
    // the compilation and object cache interface.
    assert (mModule == nullptr);
    Module * const m = new Module(makeCacheName(b), b->getContext());
    Module * const prior = b->getModule();
    m->setTargetTriple(prior->getTargetTriple());
    m->setDataLayout(prior->getDataLayout());
    mModule = m;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief generateKernel
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::generateKernel(BuilderRef b) {
    assert (!mGenerated);
    mGenerated = true;
    if (LLVM_UNLIKELY(mModule == nullptr)) {
        report_fatal_error(getName() + " does not have a module");
    }
    if (LLVM_UNLIKELY(mStride == 0)) {
        report_fatal_error(getName() + ": stride cannot be 0");
    }
    b->setModule(mModule);
    assert (mSharedStateType == nullptr && mThreadLocalStateType == nullptr);
    instantiateKernelCompiler(b)->generateKernel(b);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief nullIfEmpty
 ** ------------------------------------------------------------------------------------------------------------- */
inline StructType * nullIfEmpty(StructType * type) {
    return (type && type->isEmptyTy()) ? nullptr : type;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief concat
 ** ------------------------------------------------------------------------------------------------------------- */
inline StringRef concat(StringRef A, StringRef B, SmallVector<char, 256> & tmp) {
    Twine C = A + B;
    tmp.clear();
    C.toVector(tmp);
    return StringRef(tmp.data(), tmp.size());
}

inline StructType * getTypeByName(Module * const m, StringRef name) {
#if LLVM_VERSION_INTEGER >= LLVM_VERSION_CODE(12, 0, 0)
    return StructType::getTypeByName(m->getContext(), name);
#else
    return m->getTypeByName(name);
#endif
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief ensureLoaded
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::ensureLoaded() {
    if (LLVM_LIKELY(mGenerated)) {
        return;
    }
    assert (mModule);
    SmallVector<char, 256> tmp;
    mSharedStateType = nullIfEmpty(getTypeByName(mModule, concat(getName(), SHARED_SUFFIX, tmp)));
    mThreadLocalStateType = nullIfEmpty(getTypeByName(mModule, concat(getName(), THREAD_LOCAL_SUFFIX, tmp)));
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief loadCachedKernel
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::loadCachedKernel(BuilderRef b) {
    assert (!mGenerated);
    assert ("loadCachedKernel was called after associating kernel with module" && !mModule);
    mModule = b->getModule(); assert (mModule);
    SmallVector<char, 256> tmp;
    mSharedStateType = nullIfEmpty(getTypeByName(mModule, concat(getName(), SHARED_SUFFIX, tmp)));
    mThreadLocalStateType = nullIfEmpty(getTypeByName(mModule, concat(getName(), THREAD_LOCAL_SUFFIX, tmp)));
    linkExternalMethods(b);
    mGenerated = true;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief linkExternalMethods
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::linkExternalMethods(BuilderRef b) {
    auto & driver = b->getDriver();
    Module * const m = b->getModule(); assert (m);
    for (const LinkedFunction & linked : mLinkedFunctions) {
        driver.addLinkFunction(m, linked.Name, linked.Type, linked.FunctionPtr);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief constructStateTypes
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::constructStateTypes(BuilderRef b) {
    Module * const m = getModule(); assert (b->getModule() == m);
    SmallVector<char, 256> tmpShared;
    auto strShared = concat(getName(), SHARED_SUFFIX, tmpShared);
    mSharedStateType = getTypeByName(m, strShared);
    SmallVector<char, 256> tmpThreadLocal;
    auto strThreadLocal = concat(getName(), THREAD_LOCAL_SUFFIX, tmpThreadLocal);
    mThreadLocalStateType = getTypeByName(m, strThreadLocal);
    if (LLVM_LIKELY(mSharedStateType == nullptr && mThreadLocalStateType == nullptr)) {

        flat_set<unsigned> sharedGroups;
        flat_set<unsigned> threadLocalGroups;

        for (const auto & scalar : mInternalScalars) {
            assert (scalar.getValueType());
            switch (scalar.getScalarType()) {
                case ScalarType::Internal:
                    sharedGroups.insert(scalar.getGroup());
                    break;
                case ScalarType::ThreadLocal:
                    threadLocalGroups.insert(scalar.getGroup());
                    break;
                default: break;
            }
        }

        const auto sharedGroupCount = sharedGroups.size();
        const auto threadLocalGroupCount = threadLocalGroups.size();

        std::vector<std::vector<Type *>> shared(sharedGroupCount + 2);
        std::vector<std::vector<Type *>> threadLocal(threadLocalGroupCount);

        for (const auto & scalar : mInputScalars) {
            assert (scalar.getType());
            shared[0].push_back(scalar.getType());
        }

        // TODO: make "grouped" internal scalars that are automatically packed into cache-aligned structs
        // within the kernel state to hide the complexity from the user?
        for (const auto & scalar : mInternalScalars) {
            assert (scalar.getValueType());

            auto getGroupIndex = [&](const flat_set<unsigned> & groups) {
                const auto f = groups.find(scalar.getGroup());
                assert (f != groups.end());
                return std::distance(groups.begin(), f);
            };

            switch (scalar.getScalarType()) {
                case ScalarType::Internal:
                    shared[getGroupIndex(sharedGroups) + 1].push_back(scalar.getValueType());
                    break;
                case ScalarType::ThreadLocal:
                    threadLocal[getGroupIndex(threadLocalGroups)].push_back(scalar.getValueType());
                    break;
                default: break;
            }
        }

        assert (shared[sharedGroupCount + 1].empty());
        for (const auto & scalar : mOutputScalars) {
            assert (scalar.getType());
            shared[sharedGroupCount + 1].push_back(scalar.getType());
        }

        DataLayout dl(m);

        IntegerType * const int8Ty = b->getInt8Ty();

        auto getTypeSize = [&](Type * const type) -> uint64_t {
            if (type == nullptr) {
                return 0UL;
            }
            #if LLVM_VERSION_INTEGER < LLVM_VERSION_CODE(11, 0, 0)
            return dl.getTypeAllocSize(type);
            #else
            return dl.getTypeAllocSize(type).getFixedSize();
            #endif
        };

        const size_t cacheAlignment = b->getCacheAlignment();

        auto makeStructType = [&](const std::vector<std::vector<Type *>> & structTypeVec,
                                  StringRef name, const bool addGroupCacheLinePadding) -> StructType * {

            const auto n = structTypeVec.size();
            for (unsigned i = 0; i < n; ++i) {
                const auto & V = structTypeVec[i];
                for (unsigned j = 0; j < V.size(); ++j) {
                    if (LLVM_LIKELY(!V[j]->isEmptyTy())) {
                        goto found_non_empty_type;
                    }
                }
            }
            return nullptr;
found_non_empty_type:
            std::vector<Type *> structTypes(n * 2);

            const auto align = addGroupCacheLinePadding ? cacheAlignment : 1UL;

            size_t byteOffset = 0;
            for (unsigned i = 0; i < n; ++i) {
                StructType * const sty = StructType::create(b->getContext(), structTypeVec[i]);
                assert (sty->isSized());
                const auto typeSize = getTypeSize(sty);
                byteOffset += typeSize;
                const auto offset = (byteOffset % align);
                const auto padding = i < (n - 1) ? ((align - offset) % align) : 0UL;
                structTypes[i * 2] = sty;
                ArrayType * const paddingTy = ArrayType::get(int8Ty, padding);
                assert (paddingTy->isSized());
                structTypes[i * 2 + 1] = paddingTy;
                byteOffset += padding;
            }

            StructType * const st = StructType::create(b->getContext(), structTypes, name);
            assert (!st->isEmptyTy());
            assert (st->isSized());

            #ifndef NDEBUG
            const StructLayout * const sl = dl.getStructLayout(st);
            assert ("expected stuct size does not match type size?" && sl->getSizeInBytes() >= byteOffset);
            if (addGroupCacheLinePadding) {
                for (unsigned i = 0; i < n; ++i) {
                    const auto offset = sl->getElementOffset(i * 2);
                    assert ("cache line group alignment failed." && (offset % cacheAlignment) == 0);
                }
            }
            #endif

            assert (!st->isEmptyTy());
            assert (getTypeSize(st) > 0);

            return st;
        };

        // NOTE: StructType::create always creates a new type even if an identical one exists.
        const auto allowStructPadding = !codegen::DebugOptionIsSet(codegen::DisableCacheAlignedKernelStructs);
        mSharedStateType = makeStructType(shared, strShared, sharedGroupCount > 1 && allowStructPadding);
        assert (nullIfEmpty(mSharedStateType) == mSharedStateType);
        mThreadLocalStateType = makeStructType(threadLocal, strThreadLocal, false);
        assert (nullIfEmpty(mThreadLocalStateType) == mThreadLocalStateType);

        if (LLVM_UNLIKELY(DebugOptionIsSet(codegen::PrintKernelSizes))) {
            errs() << "KERNEL: " << mKernelName
                   << " SHARED STATE: " << getTypeSize(mSharedStateType) << " bytes"
                      ", THREAD LOCAL STATE: "  << getTypeSize(mThreadLocalStateType) << " bytes\n";
        }

    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief generateOrLoadKernel
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::generateOrLoadKernel(BuilderRef b) {
    if (LLVM_LIKELY(isGenerated())) {
        /* do nothing */
    } else if (getInitializeFunction(b, false)) {
        loadCachedKernel(b);
    } else {
        setModule(b->getModule());
        generateKernel(b);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addKernelDeclarations
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::addKernelDeclarations(BuilderRef b) {
    addInitializeDeclaration(b);
    addAllocateSharedInternalStreamSetsDeclaration(b);
    addInitializeThreadLocalDeclaration(b);
    addAllocateThreadLocalInternalStreamSetsDeclaration(b);
    addDoSegmentDeclaration(b);
    addFinalizeThreadLocalDeclaration(b);
    addFinalizeDeclaration(b);
    linkExternalMethods(b);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getInitializeFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getInitializeFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), INITIALIZE_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addInitializeDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addInitializeDeclaration
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addInitializeDeclaration(BuilderRef b) const {
    SmallVector<char, 256> tmp;
    const auto funcName = concat(getName(), INITIALIZE_SUFFIX, tmp);
    Module * const m = b->getModule();
    Function * initFunc = m->getFunction(funcName);
    if (LLVM_LIKELY(initFunc == nullptr)) {
        InitArgTypes params;
        if (LLVM_LIKELY(isStateful())) {
            params.push_back(getSharedStateType()->getPointerTo());
        }
        for (const Binding & binding : mInputScalars) {
            params.push_back(binding.getType());
        }
        addAdditionalInitializationArgTypes(b, params);
        FunctionType * const initType = FunctionType::get(b->getSizeTy(), params, false);
        initFunc = Function::Create(initType, GlobalValue::ExternalLinkage, funcName, m);
        initFunc->setCallingConv(CallingConv::C);
        initFunc->setDoesNotRecurse();

        auto arg = initFunc->arg_begin();
        auto setNextArgName = [&](const StringRef name) {
            assert (arg != initFunc->arg_end());
            arg->setName(name);
            std::advance(arg, 1);
        };
        if (LLVM_LIKELY(isStateful())) {
            arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
            setNextArgName("shared");
        }
        for (const Binding & binding : mInputScalars) {
            setNextArgName(binding.getName());
        }

    }
    return initFunc;
}


/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addFamilyInitializationArgTypes
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::addAdditionalInitializationArgTypes(BuilderRef /* b */, InitArgTypes & /* argTypes */) const {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getInitializeThreadLocalFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getInitializeThreadLocalFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    assert (hasThreadLocal());
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), INITIALIZE_THREAD_LOCAL_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addInitializeThreadLocalDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addInitializeThreadLocalDeclaration
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addInitializeThreadLocalDeclaration(BuilderRef b) const {
    Function * func = nullptr;
    if (hasThreadLocal()) {
        SmallVector<char, 256> tmp;
        const auto funcName = concat(getName(), INITIALIZE_THREAD_LOCAL_SUFFIX, tmp);
        Module * const m = b->getModule();
        func = m->getFunction(funcName);
        if (LLVM_LIKELY(func == nullptr)) {

//            FixedArray<Type *, 2> params;
//            PointerType * const voidPtrTy = b->getVoidPtrTy();
//            params[0] = voidPtrTy;
//            params[1] = voidPtrTy;

            SmallVector<Type *, 2> params;
            if (LLVM_LIKELY(isStateful())) {
                params.push_back(getSharedStateType()->getPointerTo());
            }
            params.push_back(getThreadLocalStateType()->getPointerTo());
            PointerType * const retTy = getThreadLocalStateType()->getPointerTo();
            FunctionType * const funcType = FunctionType::get(retTy, params, false);
            func = Function::Create(funcType, GlobalValue::ExternalLinkage, funcName, m);
            func->setCallingConv(CallingConv::C);
            func->setDoesNotRecurse();

            auto arg = func->arg_begin();
            auto setNextArgName = [&](const StringRef name) {
                assert (arg != func->arg_end());
                arg->setName(name);
                std::advance(arg, 1);
            };
            if (LLVM_LIKELY(isStateful())) {
                arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
                setNextArgName("shared");
            }
            arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
            setNextArgName("threadlocal");
            assert (arg == func->arg_end());
        }
        assert (func);
    }
    return func;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief hasInternalStreamSets
 ** ------------------------------------------------------------------------------------------------------------- */
bool Kernel::allocatesInternalStreamSets() const {
    return false;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getAllocateInternalStreamSets
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getAllocateSharedInternalStreamSetsFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), ALLOCATE_SHARED_INTERNAL_STREAMSETS_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addAllocateSharedInternalStreamSetsDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addAllocateInternalStreamSets
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addAllocateSharedInternalStreamSetsDeclaration(BuilderRef b) const {
    Function * func = nullptr;
    if (allocatesInternalStreamSets()) {
        SmallVector<char, 256> tmp;
        const auto funcName = concat(getName(), ALLOCATE_SHARED_INTERNAL_STREAMSETS_SUFFIX, tmp);
        Module * const m = b->getModule();
        func = m->getFunction(funcName);

        if (LLVM_LIKELY(func == nullptr)) {

            SmallVector<Type *, 2> params;
            if (LLVM_LIKELY(isStateful())) {
                params.push_back(getSharedStateType()->getPointerTo());
            }
            params.push_back(b->getSizeTy());

            FunctionType * const funcType = FunctionType::get(b->getVoidTy(), params, false);
            func = Function::Create(funcType, GlobalValue::ExternalLinkage, funcName, m);
            func->setCallingConv(CallingConv::C);
            func->setDoesNotRecurse();

            auto arg = func->arg_begin();
            auto setNextArgName = [&](const StringRef name) {
                assert (arg != func->arg_end());
                arg->setName(name);
                std::advance(arg, 1);
            };
            if (LLVM_LIKELY(isStateful())) {
                arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
                setNextArgName("shared");
            }
            setNextArgName("expectedNumOfStrides");
            assert (arg == func->arg_end());
        }
        assert (func);
    }
    return func;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief generateAllocateSharedInternalStreamSetsMethod
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::generateAllocateSharedInternalStreamSetsMethod(BuilderRef /* b */, Value * /* expectedNumOfStrides */) {
    report_fatal_error("Kernel::generateAllocateSharedInternalStreamSetsMethod is not handled yet");
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getAllocateThreadLocalInternalStreamSetsFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getAllocateThreadLocalInternalStreamSetsFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addAllocateThreadLocalInternalStreamSetsDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addAllocateThreadLocalInternalStreamSetsDeclaration
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addAllocateThreadLocalInternalStreamSetsDeclaration(BuilderRef b) const {
    Function * func = nullptr;
    if (allocatesInternalStreamSets() && hasThreadLocal()) {
        SmallVector<char, 256> tmp;
        const auto funcName = concat(getName(), ALLOCATE_THREAD_LOCAL_INTERNAL_STREAMSETS_SUFFIX, tmp);
        Module * const m = b->getModule();
        func = m->getFunction(funcName);
        if (LLVM_LIKELY(func == nullptr)) {

            SmallVector<Type *, 3> params;
            if (LLVM_LIKELY(isStateful())) {
                params.push_back(getSharedStateType()->getPointerTo());
            }
            params.push_back(getThreadLocalStateType()->getPointerTo());
            params.push_back(b->getSizeTy());

            FunctionType * const funcType = FunctionType::get(b->getVoidTy(), params, false);
            func = Function::Create(funcType, GlobalValue::ExternalLinkage, funcName, m);
            func->setCallingConv(CallingConv::C);
            func->setDoesNotRecurse();

            auto arg = func->arg_begin();
            auto setNextArgName = [&](const StringRef name) {
                assert (arg != func->arg_end());
                arg->setName(name);
                std::advance(arg, 1);
            };
            if (LLVM_LIKELY(isStateful())) {
                arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
                setNextArgName("shared");
            }
            setNextArgName("threadLocal");
            setNextArgName("expectedNumOfStrides");
            assert (arg == func->arg_end());
        }
        assert (func);
    }
    return func;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief generateAllocateThreadLocalInternalStreamSetsMethod
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::generateAllocateThreadLocalInternalStreamSetsMethod(BuilderRef /* b */, Value * /* expectedNumOfStrides */) {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getDoSegmentFields
 ** ------------------------------------------------------------------------------------------------------------- */
std::vector<Type *> Kernel::getDoSegmentFields(BuilderRef b) const {

    // WARNING: any change to this must be reflected in addDoSegmentDeclaration,
    // KernelCompiler::getDoSegmentProperties, KernelCompiler::setDoSegmentProperties,
    // PipelineCompiler::buildKernelCallArgumentList and PipelineKernel::addOrDeclareMainFunction

    IntegerType * const sizeTy = b->getSizeTy();
    PointerType * const sizePtrTy = sizeTy->getPointerTo();
    const auto n = mInputStreamSets.size();
    const auto m = mOutputStreamSets.size();

    std::vector<Type *> fields;
    fields.reserve(4 + 3 * (n + m));
    if (LLVM_LIKELY(isStateful())) {
        fields.push_back(getSharedStateType()->getPointerTo());  // handle
    }
    if (LLVM_UNLIKELY(hasThreadLocal())) {
        fields.push_back(getThreadLocalStateType()->getPointerTo());  // handle
    }
    const auto internallySynchronized = hasAttribute(AttrId::InternallySynchronized);
    const auto isMainPipeline = (getTypeId() == TypeId::Pipeline) && !internallySynchronized;

    if (LLVM_UNLIKELY(!isMainPipeline)) {
        if (LLVM_UNLIKELY(internallySynchronized)) {
            fields.push_back(sizeTy); // external SegNo
        }
        fields.push_back(sizeTy); // numOfStrides
        if (LLVM_LIKELY(hasFixedRateIO())) {
            fields.push_back(sizeTy); // fixed rate factor
        }
    }

    PointerType * const voidPtrTy = b->getVoidPtrTy();

    for (unsigned i = 0; i < n; ++i) {
        const Binding & input = mInputStreamSets[i];
        // virtual base input address
        fields.push_back(voidPtrTy);
        // is closed
        if (LLVM_UNLIKELY(internallySynchronized)) {
            fields.push_back(b->getInt1Ty());
        }
        // processed input items
        if (isMainPipeline || isAddressable(input)) {
            fields.push_back(sizePtrTy); // updatable
        } else if (isCountable(input)) {
            fields.push_back(sizeTy); // constant
        }
        // accessible input items
        if (isMainPipeline || requiresItemCount(input)) {
            fields.push_back(sizeTy);
        }
    }

    const auto hasTerminationSignal = canSetTerminateSignal();

    for (unsigned i = 0; i < m; ++i) {
        const Binding & output = mOutputStreamSets[i];
        const auto isShared = output.hasAttribute(AttrId::SharedManagedBuffer);
        const auto isLocal = Kernel::isLocalBuffer(output, false);

        // shared dynamic buffer handle or virtual base output address
        if (LLVM_UNLIKELY(isShared)) {
            fields.push_back(voidPtrTy);
        } else if (LLVM_UNLIKELY(isMainPipeline || isLocal)) {
            fields.push_back(voidPtrTy->getPointerTo());
        } else {
            fields.push_back(voidPtrTy);
        }

        //TODO: if an I/O rate is deferred and this is internally synchronized, we need both item counts

        // produced output items
        if (hasTerminationSignal || isMainPipeline || isAddressable(output)) {
            fields.push_back(sizePtrTy); // updatable
        } else if (isCountable(output)) {
            fields.push_back(sizeTy); // constant
        }
        // Although local buffers are considered to be owned by (and thus the memory managed by) this
        // kernel, the OptimizationBranch kernel delegates owned buffer management to its branch
        // pipelines. This means there are at least two seperate owners for a buffer; however, we know
        // by construction only one branch can be executing and any kernels within the pipelines must
        // be synchronized; thus at most one branch could resize a buffer at any particular moment.
        // However, we need to share the current state of the buffer between the branches to ensure
        // that we are not using an old buffer allocation.
        if (isShared || isLocal) {
            fields.push_back(sizeTy); // consumed
        } else if (isMainPipeline || requiresItemCount(output)) {
            fields.push_back(sizeTy); // writable item count
        }
    }
    return fields;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addDoSegmentDeclaration
 ** ------------------------------------------------------------------------------------------------------------ */
Function * Kernel::addDoSegmentDeclaration(BuilderRef b) const {

    // WARNING: any change to this must be reflected in getDoSegmentProperties, setDoSegmentProperties,
    // getDoSegmentFields, and PipelineCompiler::writeKernelCall

    SmallVector<char, 256> tmp;
    const auto funcName = concat(getName(), DO_SEGMENT_SUFFIX, tmp);
    Module * const m = b->getModule();
    Function * doSegment = m->getFunction(funcName);
    if (LLVM_LIKELY(doSegment == nullptr)) {

        Type * const retTy = canSetTerminateSignal() ? b->getSizeTy() : b->getVoidTy();
        FunctionType * const doSegmentType = FunctionType::get(retTy, getDoSegmentFields(b), false);
        doSegment = Function::Create(doSegmentType, GlobalValue::ExternalLinkage, funcName, m);
        doSegment->setCallingConv(CallingConv::C);
        doSegment->setDoesNotRecurse();

        auto arg = doSegment->arg_begin();
        auto setNextArgName = [&](const StringRef name) {
            assert (arg);
            assert (arg != doSegment->arg_end());
            arg->setName(name);
            // TODO: add WriteOnly attributes for the appropriate I/O parameters?
            std::advance(arg, 1);
        };
        if (LLVM_LIKELY(isStateful())) {
            arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
            setNextArgName("shared");
        }
        if (LLVM_UNLIKELY(hasThreadLocal())) {
            arg->addAttr(llvm::Attribute::AttrKind::NoCapture);
            setNextArgName("threadLocal");
        }
        const auto internallySynchronized = hasAttribute(AttrId::InternallySynchronized);
        const auto isMainPipeline = (getTypeId() == TypeId::Pipeline) && !internallySynchronized;

        if (LLVM_LIKELY(!isMainPipeline)) {
            if (LLVM_UNLIKELY(internallySynchronized)) {
                setNextArgName("segNo");
            }
            setNextArgName("numOfStrides");
            if (hasFixedRateIO()) {
                setNextArgName("fixedRateFactor");
            }
        }

        for (unsigned i = 0; i < mInputStreamSets.size(); ++i) {
            const Binding & input = mInputStreamSets[i];
            setNextArgName(input.getName());
            if (LLVM_UNLIKELY(internallySynchronized)) {
                setNextArgName(input.getName() + "_closed");
            }
            if (LLVM_LIKELY(isMainPipeline || isAddressable(input) || isCountable(input))) {
                setNextArgName(input.getName() + "_processed");
            }
            if (isMainPipeline || requiresItemCount(input)) {
                setNextArgName(input.getName() + "_accessible");
            }
        }

        const auto hasTerminationSignal = canSetTerminateSignal();

        for (unsigned i = 0; i < mOutputStreamSets.size(); ++i) {
            const Binding & output = mOutputStreamSets[i];
            setNextArgName(output.getName());
            if (LLVM_LIKELY(hasTerminationSignal || isAddressable(output) || isCountable(output))) {
                setNextArgName(output.getName() + "_produced");
            }
            if (LLVM_UNLIKELY(isLocalBuffer(output))) {
                setNextArgName(output.getName() + "_consumed");
            } else if (isMainPipeline || requiresItemCount(output)) {
                setNextArgName(output.getName() + "_writable");
            }

        }


        //assert (arg == doSegment->arg_end());
    }
    return doSegment;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getDoSegmentFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getDoSegmentFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), DO_SEGMENT_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addDoSegmentDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getFinalizeThreadLocalFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getFinalizeThreadLocalFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    assert (hasThreadLocal());
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), FINALIZE_THREAD_LOCAL_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addFinalizeThreadLocalDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addFinalizeThreadLocalDeclaration
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addFinalizeThreadLocalDeclaration(BuilderRef b) const {
    Function * func = nullptr;
    if (hasThreadLocal()) {
        SmallVector<char, 256> tmp;
        const auto funcName = concat(getName(), FINALIZE_THREAD_LOCAL_SUFFIX, tmp);
        Module * const m = b->getModule();
        func = m->getFunction(funcName);
        if (LLVM_LIKELY(func == nullptr)) {
            SmallVector<Type *, 2> params;
            if (LLVM_LIKELY(isStateful())) {
                params.push_back(getSharedStateType()->getPointerTo());
            }
            PointerType * const threadLocalPtrTy = getThreadLocalStateType()->getPointerTo();
            params.push_back(threadLocalPtrTy);
            params.push_back(threadLocalPtrTy);

            FunctionType * const funcType = FunctionType::get(b->getVoidTy(), params, false);
            func = Function::Create(funcType, GlobalValue::ExternalLinkage, funcName, m);
            func->setCallingConv(CallingConv::C);
            func->setDoesNotRecurse();

            auto arg = func->arg_begin();
            auto setNextArgName = [&](const StringRef name) {
                assert (arg != func->arg_end());
                arg->setName(name);
                std::advance(arg, 1);
            };
            if (LLVM_LIKELY(isStateful())) {
                setNextArgName("shared");
            }
            setNextArgName("main_thread_local");
            setNextArgName("thread_local");
            assert (arg == func->arg_end());

        }
    }
    return func;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getFinalizeFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::getFinalizeFunction(BuilderRef b, const bool alwayReturnDeclaration) const {
    const Module * const module = b->getModule();
    SmallVector<char, 256> tmp;
    Function * f = module->getFunction(concat(getName(), FINALIZE_SUFFIX, tmp));
    if (LLVM_UNLIKELY(f == nullptr && alwayReturnDeclaration)) {
        f = addFinalizeDeclaration(b);
    }
    return f;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addFinalizeDeclaration
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addFinalizeDeclaration(BuilderRef b) const {
    SmallVector<char, 256> tmp;
    const auto funcName = concat(getName(), FINALIZE_SUFFIX, tmp);
    Module * const m = b->getModule();
    Function * terminateFunc = m->getFunction(funcName);
    if (LLVM_LIKELY(terminateFunc == nullptr)) {
        Type * resultType = nullptr;
        if (mOutputScalars.empty()) {
            resultType = b->getVoidTy();
        } else {
            const auto n = mOutputScalars.size();
            SmallVector<Type *, 16> outputType(n);
            for (unsigned i = 0; i < n; ++i) {
                outputType[i] = mOutputScalars[i].getType();
            }
            if (n == 1) {
                resultType = outputType[0];
            } else {
                resultType = StructType::get(b->getContext(), outputType);
            }
        }
        std::vector<Type *> params;
        if (LLVM_LIKELY(isStateful())) {
            params.push_back(getSharedStateType()->getPointerTo());
        }
        if (LLVM_LIKELY(hasThreadLocal())) {
            params.push_back(getThreadLocalStateType()->getPointerTo());
        }
        FunctionType * const terminateType = FunctionType::get(resultType, params, false);
        terminateFunc = Function::Create(terminateType, GlobalValue::ExternalLinkage, funcName, m);
        terminateFunc->setCallingConv(CallingConv::C);
        terminateFunc->setDoesNotRecurse();

        auto args = terminateFunc->arg_begin();
        if (LLVM_LIKELY(isStateful())) {
            (args++)->setName("shared");
        }
        if (LLVM_LIKELY(hasThreadLocal())) {
            (args++)->setName("threadLocal");
        }
        assert (args == terminateFunc->arg_end());
    }
    return terminateFunc;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief addOrDeclareMainFunction
 ** ------------------------------------------------------------------------------------------------------------- */
Function * Kernel::addOrDeclareMainFunction(BuilderRef /* b */, const MainMethodGenerationType /* method */) const {
    llvm::report_fatal_error("Only PipelineKernels can declare a main method.");
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief createInstance
 ** ------------------------------------------------------------------------------------------------------------- */
Value * Kernel::createInstance(BuilderRef b) const {
    if (LLVM_LIKELY(isStateful())) {
        Value * const handle = b->CreatePageAlignedMalloc(getSharedStateType());
        return handle;
    }
    llvm_unreachable("createInstance should not be called on stateless kernels");
    return nullptr;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief initializeInstance
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::initializeInstance(BuilderRef b, ArrayRef<Value *> args) const {
    assert (args.size() == getNumOfScalarInputs() + 1);
    assert (args[0] && "cannot initialize before creation");
    assert (args[0]->getType()->getPointerElementType() == getSharedStateType());
    Function * const init = getInitializeFunction(b);
    b->CreateCall(init->getFunctionType(), init, args);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief initializeThreadLocalInstance
 ** ------------------------------------------------------------------------------------------------------------- */
Value * Kernel::initializeThreadLocalInstance(BuilderRef b, ArrayRef<Value *> args) const {
    Value * instance = nullptr;
    if (hasThreadLocal()) {
        assert (args.size() == ((isStateful() ? 1u : 0u) + (hasThreadLocal() ? 1u : 0u)));
        Function * const init = getInitializeThreadLocalFunction(b);
        instance = b->CreateCall(init->getFunctionType(), init, args);
    }
    return instance;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief finalizeThreadLocalInstance
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::finalizeThreadLocalInstance(BuilderRef b, ArrayRef<Value *> args) const {
    assert (args.size() == ((isStateful() ? 1u : 0u) + (hasThreadLocal() ? 2u : 0u)));
    Function * const init = getFinalizeThreadLocalFunction(b); assert (init);
    b->CreateCall(init->getFunctionType(), init, args);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief finalizeInstance
 ** ------------------------------------------------------------------------------------------------------------- */
Value * Kernel::finalizeInstance(BuilderRef b, ArrayRef<Value *> args) const {
    Function * const termFunc = getFinalizeFunction(b);
    assert (args.size() == ((isStateful() ? 1u : 0u) + (hasThreadLocal() ? 1u : 0u)));
    Value * result = b->CreateCall(termFunc->getFunctionType(), termFunc, args);
    if (mOutputScalars.empty()) {
        assert (!result || result->getType()->isVoidTy());
        result = nullptr;
    }
    return result;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief constructFamilyKernels
 ** ------------------------------------------------------------------------------------------------------------- */
Value * Kernel::constructFamilyKernels(BuilderRef b, InitArgs & hostArgs, ParamMap & params, NestedStateObjs & toFree) const {

    // TODO: need to test for termination on init call

    Value * handle = nullptr;
    BEGIN_SCOPED_REGION
    InitArgs initArgs;
    if (LLVM_LIKELY(isStateful())) {
        handle = createInstance(b);
        initArgs.push_back(handle);
        toFree.push_back(handle);
    }
    for (const Binding & input : mInputScalars) {
        const auto val = params.get(input.getRelationship());
        if (LLVM_UNLIKELY(val == nullptr)) {
            SmallVector<char, 512> tmp;
            raw_svector_ostream out(tmp);
            out << "Could not find paramater for " << getName() << ':' << input.getName()
                << " from the provided program parameters";
            report_fatal_error(out.str());
        }
        initArgs.push_back(val);
    }

    Function * const init = getInitializeFunction(b);

    // If we're calling this with a family call, then the family kernels associated with it
    // must be passed into the function itself.

    recursivelyConstructFamilyKernels(b, initArgs, params, toFree);

    if (hasInternallyGeneratedStreamSets()) {
        for (const auto & rs : getInternallyGeneratedStreamSets()) {
            ParamMap::PairEntry entry;
            if (LLVM_UNLIKELY(!params.get(rs, entry))) {
                SmallVector<char, 512> tmp;
                raw_svector_ostream out(tmp);
                out << "Could not find paramater for "
                    << "internally generated streamset"
                    << " from the provided program parameters";
                report_fatal_error(out.str());
            }
            initArgs.push_back(entry.first);
            initArgs.push_back(entry.second);
        }
    }
    assert (init->getFunctionType()->getNumParams() == initArgs.size());
    b->CreateCall(init->getFunctionType(), init, initArgs);
    END_SCOPED_REGION

    PointerType * const voidPtrTy = b->getVoidPtrTy();
    Value * const voidPtr = ConstantPointerNull::get(voidPtrTy);

    hostArgs.reserve(7);

    auto addHostArg = [&](Value * ptr) {
        if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
            b->CreateAssert(ptr, "constructFamilyKernels cannot pass a null value to pipeline");
        }
        hostArgs.push_back(b->CreatePointerCast(ptr, voidPtrTy));
    };

    auto addHostVoidArg = [&]() {
        hostArgs.push_back(voidPtr);
    };

    const auto k = hostArgs.size();

    if (LLVM_LIKELY(isStateful())) {
        addHostArg(handle);
    } else {
        addHostVoidArg();
    }
    const auto tl = hasThreadLocal();
    const auto ai = allocatesInternalStreamSets();
    if (ai) {
        addHostArg(getAllocateSharedInternalStreamSetsFunction(b));
    } else {
        addHostVoidArg();
    }
    if (tl) {
        addHostArg(getInitializeThreadLocalFunction(b));
        if (ai) {
            addHostArg(getAllocateThreadLocalInternalStreamSetsFunction(b));
        } else {
            addHostVoidArg();
        }
    } else {
        addHostVoidArg();
        addHostVoidArg();
    }
    addHostArg(getDoSegmentFunction(b));
    if (tl) {
        addHostArg(getFinalizeThreadLocalFunction(b));
    } else {
        addHostVoidArg();
    }

    // TODO: queue these in a list of termination functions to add to main?
    addHostArg(getFinalizeFunction(b));

    assert (hostArgs.size() == (k + 7));

    return handle;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief recursivelyConstructFamilyKernels
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::recursivelyConstructFamilyKernels(BuilderRef b, InitArgs & args, ParamMap & params, NestedStateObjs & toFree) const {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief runOptimizationPasses
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::runOptimizationPasses(BuilderRef /* b */) const {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getStringHash
 *
 * Create a fixed length string hash of the given str
 ** ------------------------------------------------------------------------------------------------------------- */
std::string Kernel::getStringHash(const StringRef str) {

    uint32_t digest[5]; // 160 bits in total
    boost::uuids::detail::sha1 sha1;
    sha1.process_bytes(str.data(), str.size());
    sha1.get_digest(digest);

    std::string buffer;
    buffer.reserve((5 * 8) + 1);
    raw_string_ostream out(buffer);
    for (unsigned i = 0; i < 5; ++i) {
        out << format_hex_no_prefix(digest[i], 8);
    }
    out.flush();

    return buffer;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief setInputStreamSetAt
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::setInputStreamSetAt(const unsigned i, StreamSet * const value) {
    mInputStreamSets[i].setRelationship(value);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief setOutputStreamSetAt
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::setOutputStreamSetAt(const unsigned i, StreamSet * const value) {
    mOutputStreamSets[i].setRelationship(value);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief setInputScalarAt
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::setInputScalarAt(const unsigned i, Scalar * const value) {
    mInputScalars[i].setRelationship(value);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief setOutputScalarAt
 ** ------------------------------------------------------------------------------------------------------------- */
void Kernel::setOutputScalarAt(const unsigned i, Scalar * const value) {
    mOutputScalars[i].setRelationship(value);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief generateKernelMethod
 ** ------------------------------------------------------------------------------------------------------------- */
void SegmentOrientedKernel::generateKernelMethod(BuilderRef b) {
    generateDoSegmentMethod(b);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getFamilyName
 ** ------------------------------------------------------------------------------------------------------------- */
std::string Kernel::getFamilyName() const {
    std::string tmp;
    raw_string_ostream out(tmp);
    char flags = 0;
    if (LLVM_LIKELY(isStateful())) {
        flags |= 1;
    }
    if (LLVM_UNLIKELY(hasThreadLocal())) {
        flags |= 2;
    }
    if (LLVM_UNLIKELY(allocatesInternalStreamSets())) {
        flags |= 4;
    }
    out << 'F' << ('0' + flags) << getStride();
    AttributeSet::print(out);
    for (const Binding & input : mInputScalars) {
        out << ",IV("; input.print(this, out); out << ')';
    }
    for (const Binding & input : mInputStreamSets) {
        out << ",IS("; input.print(this, out); out << ')';
    }
    for (const Binding & output : mOutputStreamSets) {
        out << ",OS("; output.print(this, out); out << ')';
    }
    for (const Binding & output : mOutputScalars) {
        out << ",OV("; output.print(this, out); out << ')';
    }
    out.flush();
    return tmp;
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief annotateKernelNameWithDebugFlags
 ** ------------------------------------------------------------------------------------------------------------- */
/* static */ std::string Kernel::annotateKernelNameWithDebugFlags(TypeId id, std::string && name) {
    raw_string_ostream buffer(name);
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableAsserts))) {
        buffer << "_EA";
    } else if (LLVM_UNLIKELY(id == Kernel::TypeId::Pipeline)) {
        // TODO: look into cleaner method for this
        if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnablePipelineAsserts))) {
            buffer << "_EA";
        }
    }
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::EnableMProtect))) {
        buffer << "_MP";
    }
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::DisableIndirectBranch))) {
        buffer << "_Ibranch";
    }
    if (LLVM_UNLIKELY(codegen::DebugOptionIsSet(codegen::DisableCacheAlignedKernelStructs))) {
        buffer << "_DCacheAlign";
    }
    if (LLVM_UNLIKELY(codegen::FreeCallBisectLimit >= 0)) {
        buffer << "_FreeLimit";
    }
    buffer.flush();
    return std::move(name);
}

// CONSTRUCTOR
Kernel::Kernel(BuilderRef b,
               const TypeId typeId,
               std::string && kernelName,
               Bindings && stream_inputs,
               Bindings && stream_outputs,
               Bindings && scalar_inputs,
               Bindings && scalar_outputs,
               InternalScalars && internal_scalars)
: mTypeId(typeId)
, mStride(b->getBitBlockWidth())
, mInputStreamSets(std::move(stream_inputs))
, mOutputStreamSets(std::move(stream_outputs))
, mInputScalars(std::move(scalar_inputs))
, mOutputScalars(std::move(scalar_outputs))
, mInternalScalars( std::move(internal_scalars))
, mKernelName(annotateKernelNameWithDebugFlags(typeId, std::move(kernelName))) {

}

Kernel::Kernel(BuilderRef b,
               const TypeId typeId,
               Bindings && stream_inputs,
               Bindings && stream_outputs,
               Bindings && scalar_inputs,
               Bindings && scalar_outputs)
: mTypeId(typeId)
, mStride(b->getBitBlockWidth())
, mInputStreamSets(std::move(stream_inputs))
, mOutputStreamSets(std::move(stream_outputs))
, mInputScalars(std::move(scalar_inputs))
, mOutputScalars(std::move(scalar_outputs))
, mInternalScalars()
, mKernelName() {

}

Kernel::~Kernel() { }

// CONSTRUCTOR
SegmentOrientedKernel::SegmentOrientedKernel(BuilderRef b,
                                             std::string && kernelName,
                                             Bindings &&stream_inputs,
                                             Bindings &&stream_outputs,
                                             Bindings &&scalar_parameters,
                                             Bindings &&scalar_outputs,
                                             InternalScalars && internal_scalars)
: Kernel(b,
TypeId::SegmentOriented, std::move(kernelName),
std::move(stream_inputs), std::move(stream_outputs),
std::move(scalar_parameters), std::move(scalar_outputs),
std::move(internal_scalars)) {

}

}
