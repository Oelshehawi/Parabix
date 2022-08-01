#ifndef SYNCHRONIZATION_LOGIC_HPP
#define SYNCHRONIZATION_LOGIC_HPP

#include "pipeline_compiler.hpp"

// Suppose T1 and T2 are two pipeline threads where all segment processing
// of kernel Ki in T1 logically happens before Ki in T2.

// Any stateless kernel (or kernel marked as internally synchronized) with
// countable input rates that is not a source, sink or side-effecting can
// be executed in parallel once we've calculated the "future" item count
// position(s). However, T2 may finish before T1 and a Kj>i in T2 could
// attempt to consume unfinished data from T1. So we must ensure that T1
// is always completely finished before T2 may execute Kj.

// For any such kernel, we require two counters. The first marks that T1
// has computed T2's initial processed item counts. The second informs T2
// when T1 has finished writing to its output streams. T2 may begin p
// rocessing once it acquires the first lock but cannot write its output
// until acquiring the second.

// If each stride of output of Ki cannot be guaranteed to be written on
// a cache-aligned boundary, regardless of input state, a temporary output
// buffer is required. After acquiring the second lock, the data
// must be copied to the shared stream set. To minimize redundant copies,
// if at the point of executing Ki,
// we require an additional lock that indicates whether some kernel "owns"
// the actual stream set.

// Even though T1 and T2 process a segment per call, a segment may require
// several iterations (due to buffer contraints, final stride processing,
// etc.) Thus to execute a stateful internally synchronized kernel, we must
// hold both buffer locks until reaching the last partial segment.

// TODO: Fix cycle counter and serialize option for nested pipelines

namespace kernel {

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief obtainCurrentSegmentNumber
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::obtainCurrentSegmentNumber(BuilderRef b, BasicBlock * const entryBlock) {
    if (mIsNestedPipeline) {
        assert (mSegNo == mExternalSegNo);
    } else {
        #ifndef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
        ConstantInt * const sz_ONE = b->getSize(1);
        if (LLVM_LIKELY(mNumOfThreads > 1)) {
            Value * const segNoPtr = b->getScalarFieldPtr(NEXT_LOGICAL_SEGMENT_NUMBER);
            // NOTE: this must be atomic or the pipeline will deadlock when some thread
            // fetches a number before the prior one to fetch the same number updates it.
            mSegNo = b->CreateAtomicFetchAndAdd(sz_ONE, segNoPtr);
        } else {
            Value * const initialSegNo = sz_ONE;
        #else
            Value * const initialSegNo = mSegNo; assert (mSegNo);
        #endif
            PHINode * const segNo = b->CreatePHI(initialSegNo->getType(), 2, "segNo");
            segNo->addIncoming(initialSegNo, entryBlock);
            mSegNo = segNo;
        #ifndef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
        }
        #endif
    }
    assert (mSegNo);
    #ifdef USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS
    mBaseSegNo = mSegNo;
    mCurrentNestedSynchronizationVariable = 0;
    #endif
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief incrementCurrentSegNo
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::incrementCurrentSegNo(BuilderRef b, BasicBlock * const exitBlock) {
    #ifndef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
    if (LLVM_UNLIKELY(mNumOfThreads != 1)) {
        return;
    }
    #endif
    if (LLVM_LIKELY(mIsNestedPipeline)) {
        return;
    }
    assert (mNumOfThreads > 0);
    #ifdef USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS
    Value * const segNo = mBaseSegNo;
    #else
    Value * const segNo = mSegNo;
    #endif
    Value * const nextSegNo = b->CreateAdd(segNo, b->getSize(mNumOfThreads));
    cast<PHINode>(segNo)->addIncoming(nextSegNo, exitBlock);
}

namespace  {

LLVM_READNONE Constant * __getSyncLockName(BuilderRef b, const unsigned type) {
    switch (type) {
        case SYNC_LOCK_PRE_INVOCATION: return b->GetString("pre-invocation ");
        case SYNC_LOCK_POST_INVOCATION: return b->GetString("post-invocation ");
        case SYNC_LOCK_FULL: return b->GetString("");
        default: llvm_unreachable("unknown sync lock?");
    }
    return nullptr;
}

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief acquireCurrentSegment
 *
 * Before the segment is processed, this loads the segment number of the kernel state and ensures the previous
 * segment is complete (by checking that the acquired segment number is equal to the desired segment number).
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::acquireSynchronizationLock(BuilderRef b, const unsigned kernelId, const unsigned type, Value * const segNo) {
    if (mNumOfThreads != 1 || mIsNestedPipeline) {
        // TODO: make this an inline function?

        const auto prefix = makeKernelName(kernelId);
        const auto serialize = codegen::DebugOptionIsSet(codegen::SerializeThreads);
        const unsigned waitingOnIdx = serialize ? LastKernel : kernelId;
        Value * const waitingOnPtr = getSynchronizationLockPtrForKernel(b, waitingOnIdx, type);
        #ifdef PRINT_DEBUG_MESSAGES
        debugPrint(b, prefix + ": waiting for %ssegment number %" PRIu64 ", initially %" PRIu64,
                   __getSyncLockName(b, type), segNo, b->CreateAtomicLoadAcquire(waitingOnPtr));
        #endif
        BasicBlock * const nextNode = b->GetInsertBlock()->getNextNode(); assert (nextNode);
        BasicBlock * const acquire = b->CreateBasicBlock(prefix + "_LSN_acquire", nextNode);
        BasicBlock * const acquired = b->CreateBasicBlock(prefix + "_LSN_acquired", nextNode);
        b->CreateBr(acquire);

        b->SetInsertPoint(acquire);
        Value * const currentSegNo = b->CreateAtomicLoadAcquire(waitingOnPtr);
        if (LLVM_UNLIKELY(CheckAssertions)) {
            Value * const pendingOrReady = b->CreateICmpULE(currentSegNo, segNo);
            SmallVector<char, 256> tmp;
            raw_svector_ostream out(tmp);
            out << "%s: acquired %ssegment number is %" PRIu64 " "
                   "but was expected to be within [0,%" PRIu64 "]";
            b->CreateAssert(pendingOrReady, out.str(), mKernelName[kernelId], __getSyncLockName(b, type), currentSegNo, segNo);
        }
        Value * const ready = b->CreateICmpEQ(segNo, currentSegNo);
        b->CreateLikelyCondBr(ready, acquired, acquire);

        b->SetInsertPoint(acquired);

        #ifdef PRINT_DEBUG_MESSAGES
        debugPrint(b, "# " + prefix + " acquired %ssegment number %" PRIu64, __getSyncLockName(b, type), segNo);
        #endif
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief releaseCurrentSegment
 *
 * After executing the kernel, the segment number must be incremented to release the kernel for the next thread.
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::releaseSynchronizationLock(BuilderRef b, const unsigned kernelId, const unsigned type, Value * const segNo) {
    if (mNumOfThreads != 1 || mIsNestedPipeline || TraceProducedItemCounts || TraceUnconsumedItemCounts || TraceIO) {
        const auto prefix = makeKernelName(kernelId);
        Value * const waitingOnPtr = getSynchronizationLockPtrForKernel(b, kernelId, type);

        Value * const nextSegNo = b->CreateAdd(segNo, b->getSize(1));

        if (LLVM_UNLIKELY(CheckAssertions)) {
            Value * const updated = b->CreateAtomicCmpXchg(waitingOnPtr, segNo, nextSegNo,
                                                           AtomicOrdering::Release, AtomicOrdering::Acquire);
            Value * const observed = b->CreateExtractValue(updated, { 0 });
            Value * const success = b->CreateExtractValue(updated, { 1 });
            SmallVector<char, 256> tmp;
            raw_svector_ostream out(tmp);
            out << "%s: released %ssegment number is %" PRIu64
                   " but was expected to be %" PRIu64;
            b->CreateAssert(success, out.str(), mKernelName[kernelId], __getSyncLockName(b, type), observed, segNo);

        } else {
            b->CreateAtomicStoreRelease(nextSegNo, waitingOnPtr);
        }
        #ifdef PRINT_DEBUG_MESSAGES
        debugPrint(b, prefix + ": released %ssegment number %" PRIu64, __getSyncLockName(b, type), segNo);
        #endif
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getSynchronizationLockPtrForKernel
 ** ------------------------------------------------------------------------------------------------------------- */
inline Value * PipelineCompiler::getSynchronizationLockPtrForKernel(BuilderRef b, const unsigned kernelId, const unsigned type) const {
    return getScalarFieldPtr(b.get(), makeKernelName(kernelId) + LOGICAL_SEGMENT_SUFFIX[type]);
}

#ifdef USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS
/** ------------------------------------------------------------------------------------------------------------- *
 * @brief obtainNextSegmentNumber
 ** ------------------------------------------------------------------------------------------------------------- */
Value * PipelineCompiler::obtainNextSegmentNumber(BuilderRef b) {
    Value * const ptr = getScalarFieldPtr(b.get(),
        NESTED_LOGICAL_SEGMENT_NUMBER_PREFIX + std::to_string(mCurrentNestedSynchronizationVariable));
    // Value * const nextSegNo = b->CreateAtomicFetchAndAdd(b->getSize(1), ptr);
    Value * const nextSegNo = b->CreateLoad(ptr);
    b->CreateStore(b->CreateAdd(nextSegNo, b->getSize(1)), ptr);
    #ifdef PRINT_DEBUG_MESSAGES
    const auto prefix = makeKernelName(mKernelId);
    debugPrint(b, prefix + ": obtained %" PRIu64 "-th next segment number %" PRIu64,
               b->getSize(mCurrentNestedSynchronizationVariable), nextSegNo);
    #endif
    return nextSegNo;
}
#endif

}

#endif // SYNCHRONIZATION_LOGIC_HPP
