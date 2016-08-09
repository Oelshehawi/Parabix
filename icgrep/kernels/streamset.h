/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#ifndef STREAMSET_H
#define STREAMSET_H

#include <string>
#include <vector>
#include <IDISA/idisa_builder.h>
#include <llvm/IR/Type.h>
    
namespace parabix {
    
enum FieldType {i1 = 1, i2 = 2, i4 = 4, i8 = 8, i16 = 16, i32 = 32, i64 = 64, i128 = 128, i256 = 256};

class StreamSetType {
public:
    StreamSetType(int count, int width) : mStreamCount(count), mFieldWidth(width) {}
    int StreamCount() { return mStreamCount;}
    int StreamFieldWidth() { return mFieldWidth;}
    
    llvm::Type * getStreamSetBlockType(IDISA::IDISA_Builder * iBuilder);
    
private:
    int mStreamCount;
    int mFieldWidth;
};

class StreamSetBuffer {
public:
    enum class BufferKind : unsigned {BlockBuffer, ExternalUnboundedBuffer, CircularBuffer, ExpandingBuffer};
    inline BufferKind getBufferKind() const {return mBufferKind;}
    
    llvm::Type * getStreamSetBlockType();

    virtual size_t getBufferSize() = 0;
    
    virtual llvm::Value * allocateBuffer() = 0;
    
    llvm::Value * getStreamSetBasePtr() {return mStreamSetBufferPtr;}
    
    // Get the buffer pointer for a given block of the stream.
    virtual llvm::Value * getStreamSetBlockPointer(llvm::Value * bufferBasePtr, llvm::Value * blockNo) = 0;
    
    
    
protected:
    StreamSetBuffer(BufferKind k, IDISA::IDISA_Builder * b, StreamSetType ss_type) :
        mBufferKind(k), iBuilder(b), mStreamSetType(ss_type), mBufferBlocks(1), mAddrSpace(0), mStreamSetBufferPtr(nullptr) {
    }
    const BufferKind       mBufferKind;
    IDISA::IDISA_Builder * iBuilder;
    StreamSetType mStreamSetType;
    size_t mBufferBlocks;
    int mAddrSpace;
    llvm::Value * mStreamSetBufferPtr;

};   
    

class SingleBlockBuffer : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::BlockBuffer;}
    
    SingleBlockBuffer(IDISA::IDISA_Builder * b, StreamSetType ss_type) :
    StreamSetBuffer(BufferKind::BlockBuffer, b, ss_type) {}
    
    size_t getBufferSize() override;
    llvm::Value * allocateBuffer() override;
    llvm::Value * getStreamSetBlockPointer(llvm::Value * bufferBasePtr, llvm::Value * blockNo) override;
};
    
class ExternalUnboundedBuffer : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::ExternalUnboundedBuffer;}
    
    ExternalUnboundedBuffer(IDISA::IDISA_Builder * b, StreamSetType ss_type, unsigned AddressSpace = 0) :
        StreamSetBuffer(BufferKind::ExternalUnboundedBuffer, b, ss_type) {
            mBufferBlocks = 0;
            mAddrSpace = AddressSpace;
        }
    
    void setStreamSetBuffer(llvm::Value * ptr);
    
    size_t getBufferSize() override;
    // Can't allocate - raise an error. */
    llvm::Value * allocateBuffer() override;
    llvm::Value * getStreamSetBlockPointer(llvm::Value * bufferBasePtr, llvm::Value * blockNo) override;

private:
    unsigned mAddrSpace;
};

class CircularBuffer : public StreamSetBuffer {
public:
    static inline bool classof(const StreamSetBuffer * b) {return b->getBufferKind() == BufferKind::CircularBuffer;}
  
    CircularBuffer(IDISA::IDISA_Builder * b, StreamSetType ss_type, size_t bufferBlocks) :
        StreamSetBuffer(BufferKind::CircularBuffer, b, ss_type) {
            mBufferBlocks = bufferBlocks;
            if (((bufferBlocks - 1) & bufferBlocks) != 0) {
                throw std::runtime_error("CircularStreamSetBuffer: number of blocks must be a power of 2!");
            }
        }

    size_t getBufferSize() override;
    llvm::Value * allocateBuffer() override;
    llvm::Value * getStreamSetBlockPointer(llvm::Value * bufferBasePtr, llvm::Value * blockNo) override;
};

}
#endif // STREAMSET_H
