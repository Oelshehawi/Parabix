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
 * @brief identifyAllInternallySynchronizedKernels
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::identifyAllInternallySynchronizedKernels() {
    if (mNumOfThreads > 1 || ExternallySynchronized) {
        if (LLVM_UNLIKELY(KernelOnHybridThread.any())) {

            const auto firstOnHybridThread = KernelOnHybridThread.find_first_in(FirstKernel, PipelineOutput);
            assert (firstOnHybridThread != -1);
            HybridSyncLock = static_cast<unsigned>(firstOnHybridThread);

            auto maxProducer = PipelineInput;
            for (const auto kernel : KernelOnHybridThread.set_bits()) {
                for (const auto e : make_iterator_range(in_edges(kernel, mBufferGraph))) {
                    const auto producer = parent(source(e, mBufferGraph), mBufferGraph);
                    assert (producer < kernel);
                    maxProducer = std::max<unsigned>(maxProducer, producer);
                }
            }
            assert (maxProducer < firstOnHybridThread);
            FixedDataSyncLock = maxProducer;

            RequiresSynchronization.set(HybridSyncLock);
            RequiresSynchronization.set(FixedDataSyncLock);
        }

        if (LLVM_UNLIKELY(mNumOfThreads > (KernelOnHybridThread.any() ? 2U : 1U))) {
            for (auto kernel = FirstKernel; kernel <= LastKernel; ++kernel) {
                const Kernel * const kernelObj = getKernel(kernel);
                if (kernelObj->hasAttribute(AttrId::InternallySynchronized)) {
                    continue;
                }
                if (KernelOnHybridThread.test(kernel)) {
                    continue;
                }
                RequiresSynchronization.set(kernel);
            }
        }
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief readFirstSegmentNumber
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::readFirstSegmentNumber(BuilderRef b) {
    if (ExternallySynchronized) {
        mSegNo = b->getExternalSegNo(); assert (mSegNo);
    }
    else if (mNumOfThreads == 1) {
        mSegNo = b->getSize(0);
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief obtainCurrentSegmentNumber
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::obtainCurrentSegmentNumber(BuilderRef b, BasicBlock * const entryBlock) {
    ConstantInt * const ONE = b->getSize(1);
    if (!ExternallySynchronized) {
        #ifndef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
        if (LLVM_LIKELY(mNumOfThreads > 1)) {
            Value * const segNoPtr = b->getScalarFieldPtr(NEXT_LOGICAL_SEGMENT_NUMBER);
            mSegNo = b->CreateAtomicFetchAndAdd(ONE, segNoPtr);
        } else {
        #endif
            assert (mSegNo);
            PHINode * const segNo = b->CreatePHI(mSegNo->getType(), 2);
            segNo->addIncoming(mSegNo, entryBlock);
            mSegNo = segNo;
        #ifndef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
        }
        #endif
    }
    mNextSegNo = b->CreateAdd(mSegNo, ONE);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief incrementCurrentSegNo
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::incrementCurrentSegNo(BuilderRef b, BasicBlock * const exitBlock) {
    #ifdef USE_FIXED_SEGMENT_NUMBER_INCREMENTS
    if (LLVM_LIKELY(ExternallySynchronized)) {
        return;
    }
    assert (mNumOfThreads > 0);
    unsigned step = 0;
    if (mCompilingHybridThread) {
        step = 1;
    } else {
        step = mNumOfThreads;
        if (PartitionOnHybridThread.any()) {
            step -= 1;
        }
    }
    assert (step > 0);
    Value * const nextSegNo = b->CreateAdd(mSegNo, b->getSize(step));
    cast<PHINode>(mSegNo)->addIncoming(nextSegNo, exitBlock);
    #else
    if (LLVM_LIKELY(ExternallySynchronized || mNumOfThreads > 1)) {
        return;
    }
    cast<PHINode>(mSegNo)->addIncoming(mNextSegNo, exitBlock);
    #endif
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief acquireCurrentSegment
 *
 * Before the segment is processed, this loads the segment number of the kernel state and ensures the previous
 * segment is complete (by checking that the acquired segment number is equal to the desired segment number).
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::acquireSynchronizationLock(BuilderRef b, const unsigned kernelId) {
    if (LLVM_LIKELY(RequiresSynchronization.test(kernelId))) {

        assert (KernelOnHybridThread.test(kernelId) == mCompilingHybridThread);
        const auto prefix = makeKernelName(kernelId);
        const auto serialize = codegen::DebugOptionIsSet(codegen::SerializeThreads);
        const unsigned waitingOnIdx = serialize ? LastKernel : kernelId;
        Value * const waitingOnPtr = getSynchronizationLockPtrForKernel(b, waitingOnIdx);
        #ifdef PRINT_DEBUG_MESSAGES
        debugPrint(b, prefix + ": waiting for %" PRIu64 ", initially %" PRIu64, mSegNo, b->CreateLoad(waitingOnPtr));
        #endif
        const auto waitingOn = makeKernelName(waitingOnIdx);
        Value * const waitingOnPtr = getScalarFieldPtr(b.get(), waitingOn + LOGICAL_SEGMENT_SUFFIX);
//        #ifdef PRINT_DEBUG_MESSAGES
//        debugPrint(b, prefix + ": waiting for %" PRIu64 ", initially %" PRIu64, mSegNo, b->CreateLoad(waitingOnPtr));
//        #endif
        BasicBlock * const nextNode = b->GetInsertBlock()->getNextNode();
        BasicBlock * const acquire = b->CreateBasicBlock(prefix + "_LSN_acquire", nextNode);
        BasicBlock * const acquired = b->CreateBasicBlock(prefix + "_LSN_acquired", nextNode);

        b->CreateBr(acquire);

        b->SetInsertPoint(acquire);
        Value * const currentSegNo = b->CreateAtomicLoadAcquire(waitingOnPtr);
        if (LLVM_UNLIKELY(CheckAssertions)) {
            Value * const pendingOrReady = b->CreateICmpULE(currentSegNo, mSegNo);
            SmallVector<char, 256> tmp;
            raw_svector_ostream out(tmp);
            out << "%s: logical segment number is %" PRIu64 " "
                   "but was expected to be [0,%" PRIu64 "]";
            b->CreateAssert(pendingOrReady, out.str(), mCurrentKernelName, currentSegNo, mSegNo);
        }
        Value * const ready = b->CreateICmpEQ(mSegNo, currentSegNo);
        b->CreateLikelyCondBr(ready, acquired, acquire);

        b->SetInsertPoint(acquired);

//        #ifdef PRINT_DEBUG_MESSAGES
//        debugPrint(b, "# " + prefix + " acquired SegNo %" PRIu64, mSegNo);
//        #endif
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief releaseCurrentSegment
 *
 * After executing the kernel, the segment number must be incremented to release the kernel for the next thread.
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::releaseSynchronizationLock(BuilderRef b, const unsigned kernelId) {
    const auto required = RequiresSynchronization.test(kernelId);
    if (LLVM_LIKELY(required || mCompilingHybridThread || TraceProducedItemCounts || TraceUnconsumedItemCounts)) {
        const auto prefix = makeKernelName(kernelId);
        Value * const waitingOnPtr = getSynchronizationLockPtrForKernel(b, kernelId);
        assert (KernelOnHybridThread.test(kernelId) == mCompilingHybridThread);
        if (LLVM_UNLIKELY(CheckAssertions)) {
            Value * const currentSegNo = b->CreateLoad(waitingOnPtr);
            currentSegNo = b->CreateLoad(waitingOnPtr);
        }
        b->CreateAtomicStoreRelease(mNextSegNo, waitingOnPtr);
//        #ifdef PRINT_DEBUG_MESSAGES
//        debugPrint(b, prefix + ": released %" PRIu64, mSegNo);
//        #endif
        if (LLVM_UNLIKELY(CheckAssertions && required)) {
            Value * const unchanged = b->CreateICmpEQ(mSegNo, currentSegNo);
            SmallVector<char, 256> tmp;
            raw_svector_ostream out(tmp);
            out << "%s: logical segment number is %" PRIu64
                   " but was expected to be %" PRIu64;
            b->CreateAssert(unchanged, out.str(), mKernelName[kernelId], currentSegNo, mSegNo);
        }
        b->CreateAtomicStoreRelease(mNextSegNo, waitingOnPtr);
        #ifdef PRINT_DEBUG_MESSAGES
        debugPrint(b, prefix + ": released %" PRIu64, mSegNo);
        #endif
    }
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief acquireCurrentSegment
 *
 * Before the segment is processed, this loads the segment number of the kernel state and ensures the previous
 * segment is complete (by checking that the acquired segment number is equal to the desired segment number).
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::acquireHybridThreadSynchronizationLock(BuilderRef b) {
    if (KernelOnHybridThread.any()) {
        assert (mNumOfThreads > 1);

        BasicBlock * const nextNode = b->GetInsertBlock()->getNextNode();
        BasicBlock * const waiting = b->CreateBasicBlock("hybrid_sync_waiting" , nextNode);
        BasicBlock * const waited = b->CreateBasicBlock("hybrid_sync_waited", nextNode);

        const auto syncLock = mCompilingHybridThread ? FixedDataSyncLock : HybridSyncLock;
        assert (KernelOnHybridThread.test(syncLock) != mCompilingHybridThread);

        assert (FirstKernel <= syncLock && syncLock <= LastKernel);
        Value * const otherThread = getSynchronizationLockPtrForKernel(b, syncLock);
        b->CreateBr(waiting);

        b->SetInsertPoint(waiting);
        Value * const thisSegNo = b->CreateAtomicLoadAcquire(otherThread);
        Value * const ready = b->CreateICmpULE(mSegNo, thisSegNo);
        Value * const done = b->CreateIsNotNull(readTerminationSignal(b, KernelPartitionId[syncLock]));
        b->CreateLikelyCondBr(b->CreateOr(ready, done), waited, waiting);

        b->SetInsertPoint(waited);
    }
}



/** ------------------------------------------------------------------------------------------------------------- *
 * @brief releaseHybridThreadSynchronizationLock
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::releaseHybridThreadSynchronizationLock(BuilderRef b) {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief releaseHybridThreadSynchronizationLock
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::writeFinalHybridThreadSynchronizationNumber(BuilderRef b) {

}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief getSynchronizationLockPtrForKernel
 ** ------------------------------------------------------------------------------------------------------------- */
inline Value * PipelineCompiler::getSynchronizationLockPtrForKernel(BuilderRef b, const unsigned kernelId) const {
    return getScalarFieldPtr(b.get(), makeKernelName(kernelId) + LOGICAL_SEGMENT_SUFFIX);
}

/** ------------------------------------------------------------------------------------------------------------- *
 * @brief verifyCurrentSynchronizationLock
 ** ------------------------------------------------------------------------------------------------------------- */
void PipelineCompiler::verifyCurrentSynchronizationLock(BuilderRef b) const {
    if (CheckAssertions) {
        const auto required = RequiresSynchronization.test(mKernelId);
        if (required) {
            const auto serialize = codegen::DebugOptionIsSet(codegen::SerializeThreads);
            const unsigned waitingOnIdx = serialize ? LastKernel : mKernelId;
            const auto waitingOn = makeKernelName(waitingOnIdx);
            Value * const waitingOnPtr = getScalarFieldPtr(b.get(), waitingOn + LOGICAL_SEGMENT_SUFFIX);
            Value * const currentSegNo = b->CreateLoad(waitingOnPtr);
            Value * const valid = b->CreateICmpEQ(mSegNo, currentSegNo);
            b->CreateAssert(valid, "%s does not have the correct segment number (%" PRIu64 " instead of %" PRIu64 ")",
                            mCurrentKernelName,currentSegNo, mSegNo);
        }
    }
}


}

#endif // SYNCHRONIZATION_LOGIC_HPP
