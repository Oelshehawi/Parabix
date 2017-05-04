/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#ifndef STREAMSET_H
#define STREAMSET_H

#include <llvm/IR/Type.h>  // for Type
namespace IDISA { class IDISA_Builder; }
namespace llvm { class Value; }
namespace kernel { class KernelBuilder; }

namespace parabix {
    
class StreamSetBuffer {
    friend class kernel::KernelBuilder;

public:

    enum class BufferKind : unsigned {
        BlockBuffer
        , SourceBuffer
        , ExternalBuffer
        , CircularBuffer
        , CircularCopybackBuffer
        , SwizzledCopybackBuffer
        , ExpandableBuffer
    };

    BufferKind getBufferKind() const {
        return mBufferKind;
    }
    
    std::string getUniqueID() const {
        return mUniqueID;
    }

    llvm::Type * getType() const {
        return mType;
    }

    llvm::Type * getBaseType() const {
        return mBaseType;
    }

    llvm::PointerType * getPointerType() const {
        return getType()->getPointerTo(mAddressSpace);
    }

    size_t getBufferBlocks() const {
        return mBufferBlocks;
    }

    llvm::Value * getStreamSetBasePtr() const {
        return mStreamSetBufferPtr;
    }

    virtual void allocateBuffer(IDISA::IDISA_Builder * const iBuilder);

    virtual void releaseBuffer(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const;

    virtual llvm::Value * getStreamBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * blockIndex, const bool readOnly) const;

    virtual llvm::Value * getStreamPackPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * blockIndex, llvm::Value * packIndex, const bool readOnly) const;
    
    virtual llvm::Value * getStreamSetCount(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const;

    llvm::Value * getRawItemPointer(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * absolutePosition) const;

    virtual void setBaseAddress(IDISA::IDISA_Builder * const iBuilder, llvm::Value * addr, llvm::Value *) const;

    virtual void setBufferedSize(IDISA::IDISA_Builder * const iBuilder, llvm::Value * size, llvm::Value *) const;

    virtual llvm::Value * getBufferedSize(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const;

    // The number of items that cam be linearly accessed from a given logical stream position.
    virtual llvm::Value * getLinearlyAccessibleItems(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * fromPosition) const;

    virtual llvm::Value * getLinearlyAccessibleBlocks(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * fromBlock) const;
    
    virtual void createBlockAlignedCopy(IDISA::IDISA_Builder * const iBuilder, llvm::Value * targetBlockPtr, llvm::Value * sourceBlockPtr, llvm::Value * itemsToCopy) const;

    virtual void reserveBytes(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * requested) const;

    virtual ~StreamSetBuffer() = 0;

    kernel::KernelBuilder * getProducer() const {
        return mProducer;
    }

    const std::vector<kernel::KernelBuilder *> & getConsumers() const {
        return mConsumers;
    }

protected:

    StreamSetBuffer(BufferKind k, llvm::Type * baseType, llvm::Type * resolvedType, unsigned blocks, unsigned AddressSpace);

    // Get the buffer pointer for a given block of the stream.
    virtual llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockNo) const = 0;

    bool isCapacityGuaranteed(const llvm::Value * const index, const size_t capacity) const;

    llvm::Value * modByBufferBlocks(IDISA::IDISA_Builder * const iBuilder, llvm::Value * const offset) const;

    virtual llvm::Value * getBaseAddress(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const;

    void setProducer(kernel::KernelBuilder * const producer) {
        assert (producer);
        mProducer = producer;
    }

    void addConsumer(kernel::KernelBuilder * const consumer) {
        assert (consumer);
        mConsumers.push_back(consumer);
    }

protected:
    const BufferKind                        mBufferKind;
    llvm::Type * const                      mType;
    const size_t                            mBufferBlocks;
    const unsigned                          mAddressSpace;
    llvm::Value *                           mStreamSetBufferPtr;
    llvm::Type * const                      mBaseType;
    std::string                             mUniqueID;
    kernel::KernelBuilder *                 mProducer;
    std::vector<kernel::KernelBuilder *>    mConsumers;
};   

class SingleBlockBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {
        return b->getBufferKind() == BufferKind::BlockBuffer;
    }   

    SingleBlockBuffer(IDISA::IDISA_Builder * b, llvm::Type * type);

protected:

    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockNo) const override;
};

class SourceBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {
        return b->getBufferKind() == BufferKind::SourceBuffer;
    }

    SourceBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, unsigned AddressSpace = 0);

    void setBaseAddress(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * addr) const override;

    void setBufferedSize(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * size) const override;

    llvm::Value * getBufferedSize(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const override;

    llvm::Value * getLinearlyAccessibleItems(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * fromPosition) const override;

protected:

    llvm::Value * getBaseAddress(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const override;

    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockNo) const override;

};

class ExternalBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {
        return b->getBufferKind() == BufferKind::ExternalBuffer;
    }

    ExternalBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, llvm::Value * addr, unsigned AddressSpace = 0);

    // Can't allocate - raise an error. */
    void allocateBuffer(IDISA::IDISA_Builder * const iBuilder) override;

    llvm::Value * getLinearlyAccessibleItems(IDISA::IDISA_Builder * const iBuilder, llvm::Value * fromPosition, llvm::Value *) const override;

protected:
    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockNo) const override;
};

class CircularBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {
        return b->getBufferKind() == BufferKind::CircularBuffer;
    }
    
    CircularBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, size_t bufferBlocks, unsigned AddressSpace = 0);

protected:
    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockIndex) const override;
};
    

//
//  A CircularCopybackBuffer operates as a circular buffer buffer with an overflow area
//  for temporary use by the kernel that writes to it.   If the kernel uses the overflow
//  area, it must perform the doCopyBack action before releasing the buffer for use by
//  subsequent kernels.
//  Kernels that read from a CircularCopybackBuffer must not access the overflow area.
//
class CircularCopybackBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::CircularCopybackBuffer;}
    
    CircularCopybackBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, size_t bufferBlocks, size_t overflowBlocks, unsigned AddressSpace = 0);

    void allocateBuffer(IDISA::IDISA_Builder * const iBuilder) override;
    
    // Generate copyback code for the given number of overflowItems.
    void createCopyBack(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * overflowItems) const;
        
protected:
    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockIndex) const override;
private:
    size_t mOverflowBlocks;

};
    
class SwizzledCopybackBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::SwizzledCopybackBuffer;}
    
    SwizzledCopybackBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, size_t bufferBlocks, size_t overflowBlocks, unsigned fieldwidth = 64, unsigned AddressSpace = 0);
    
    void allocateBuffer(IDISA::IDISA_Builder * const iBuilder) override;
    
    void createBlockAlignedCopy(IDISA::IDISA_Builder * const iBuilder, llvm::Value * targetBlockPtr, llvm::Value * sourceBlockPtr, llvm::Value * itemsToCopy) const override;

    // Generate copyback code for the given number of overflowItems.
    void createCopyBack(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * overflowItems) const;
    
protected:
    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * blockIndex) const override;
private:
    size_t mOverflowBlocks;
    unsigned mFieldWidth;
    
};

// ExpandableBuffers do not allow access to the base stream set but will automatically increase the number of streams
// within their set whenever the index exceeds its capacity
//
class ExpandableBuffer final : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::ExpandableBuffer;}

    ExpandableBuffer(IDISA::IDISA_Builder * b, llvm::Type * type, size_t bufferBlocks, unsigned AddressSpace = 0);

    llvm::Value * getStreamBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * blockIndex, const bool readOnly) const override;

    llvm::Value * getStreamPackPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * blockIndex, llvm::Value * packIndex, const bool readOnly) const override;

    llvm::Value * getLinearlyAccessibleItems(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * fromPosition) const override;

    void allocateBuffer(IDISA::IDISA_Builder * const iBuilder) override;

    llvm::Value * getStreamSetCount(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const override;

    void releaseBuffer(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const override;

protected:

    llvm::Value * getBaseAddress(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self) const override;

    llvm::Value * getStreamSetBlockPtr(IDISA::IDISA_Builder * const iBuilder, llvm::Value * blockIndex, llvm::Value *) const override;

private:

    std::pair<llvm::Value *, llvm::Value *> getInternalStreamBuffer(IDISA::IDISA_Builder * const iBuilder, llvm::Value * self, llvm::Value * streamIndex, llvm::Value * blockIndex, const bool readOnly) const;

private:

    const uint64_t  mInitialCapacity;

};

}
#endif // STREAMSET_H
