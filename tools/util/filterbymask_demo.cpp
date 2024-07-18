#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <kernel/core/kernel_builder.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <llvm/ADT/StringRef.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <fcntl.h>
#include <pablo/pablo_toolchain.h>
#include <pablo/builder.hpp>
#include <kernel/streamutils/deletion.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/Support/raw_ostream.h>
#include <kernel/basis/s2p_kernel.h>
#include <kernel/basis/p2s_kernel.h>
#include <kernel/core/idisa_target.h>
#include <cstdio>
#include <vector>
#include <llvm/Support/ErrorHandling.h>
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <re/cc/cc_kernel.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <pablo/pe_ones.h>
#include <pablo/pe_zeroes.h>
#include <pablo/bixnum/bixnum.h>
#include <iostream>
#include <kernel/pipeline/driver/cpudriver.h>

using namespace kernel;
using namespace llvm;
using namespace codegen;
using namespace pablo;

#define SHOW_STREAM(name) if (codegen::EnableIllustrator) P->captureBitstream(#name, name);
#define SHOW_BIXNUM(name) if (codegen::EnableIllustrator) P->captureBixNum(#name, name);
#define SHOW_BYTES(name) if (codegen::EnableIllustrator) P->captureByteData(#name, name);

static cl::OptionCategory MaskDemoOptions("Mask Demo Options", "Mask demo options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(MaskDemoOptions));

class MaskKernel final : public MultiBlockKernel {
public:
    MaskKernel(KernelBuilder & b, StreamSet * const byteStream, StreamSet * const maskStream, StreamSet * const outputStream);
    static constexpr unsigned fw = 32;
    static constexpr unsigned rate = 1;
protected:
    void generateMultiBlockLogic(KernelBuilder & b, llvm::Value * const numOfStrides) override;
};

MaskKernel::MaskKernel(KernelBuilder & b, StreamSet * const byteStream, StreamSet * const maskStream, StreamSet * const outputStream)
: MultiBlockKernel(b, "mask_kernel",
{Binding{"byteStream", byteStream, FixedRate(rate)}, Binding{"maskStream", maskStream, FixedRate(rate)}},
    {Binding{"outputStream", outputStream, PopcountOf("maskStream")}}, {}, {}, {}) {}

void MaskKernel::generateMultiBlockLogic(KernelBuilder & b, Value * const numOfStrides) {
    const unsigned inputPacksPerStride = fw * rate;
    PointerType * bitBlockPtrTy = PointerType::get(b.getBitBlockType(), 0);

    BasicBlock * entry = b.GetInsertBlock();
    BasicBlock * maskLoop = b.CreateBasicBlock("maskLoop");
    BasicBlock * maskFinalize = b.CreateBasicBlock("maskFinalize");
    Constant * const ZERO = b.getSize(0);
    Value * numOfBlocks = numOfStrides;
    if (getStride() != b.getBitBlockWidth()) {
        numOfBlocks = b.CreateShl(numOfStrides, b.getSize(std::log2(getStride() / b.getBitBlockWidth())));
    }
    b.CreateBr(maskLoop);
    b.SetInsertPoint(maskLoop);
    PHINode * blockOffsetPhi = b.CreatePHI(b.getSizeTy(), 2);
    blockOffsetPhi->addIncoming(ZERO, entry);

    Value * bytepack[inputPacksPerStride];
    Value * mask;
    for (unsigned i = 0; i < inputPacksPerStride; i++) {
        bytepack[i] = b.loadInputStreamPack("byteStream", ZERO, b.getInt32(i), blockOffsetPhi);
    }

    mask = b.loadInputStreamBlock("maskStream", ZERO, blockOffsetPhi); 
    
    mask = b.CreateBitCast(mask, llvm::FixedVectorType::get(b.getIntNTy(b.getBitBlockWidth()/8),8));

    b.CallPrintRegister("Mask:", mask);

    Value * compressed[inputPacksPerStride];
    Value * output_ptr = b.getOutputStreamBlockPtr("byteStream", b.getInt32(0));
    output_ptr = b.CreatePointerCast(output_ptr, b.getInt8PtrTy());
    for (unsigned i = 0; i < inputPacksPerStride; i++) {
    // Extract the mask field for the current pack
    Value * maskField = b.CreateExtractElement(mask, b.getInt32(i));

    // Calculate the offset using the popcount of the mask field
    Value * offset = b.CreatePopcount(maskField);
    
    // Compress the bytepack using the mask field
    compressed[i] = b.mvmd_compress(fw, bytepack[i], maskField);
    b.CallPrintRegister("Compressed:", compressed[i]);

    b.storeOutputStreamBlock("outputStream", ZERO, b.getInt32(i), offset, compressed[i]);

    // Calculate the address to store the compressed data
    // Value * storeAddr = b.CreateGEP(b.getInt8Ty(), output_ptr, offset);
    // storeAddr = b.CreateBitCast(storeAddr, bitBlockPtrTy);
    
    // // Store the compressed data at the calculated address
    // b.CreateStore(compressed[i], storeAddr);

    // Update the produced item count
    Value * unitsGenerated = b.getProducedItemCount("byteStream");
    b.CallPrintRegister("Units Generated:", unitsGenerated);

    // Add the offset to the produced item count
    unitsGenerated = b.CreateAdd(unitsGenerated, b.CreateZExt(offset, b.getSizeTy()));
    b.CallPrintRegister("Units Generated after add:", unitsGenerated);

    // Set the produced item count
    b.setProducedItemCount("byteStream", unitsGenerated);
    }


    Value * nextBlk = b.CreateAdd(blockOffsetPhi, b.getSize(1));
    blockOffsetPhi->addIncoming(nextBlk, maskLoop);
    Value * moreToDo = b.CreateICmpNE(nextBlk, numOfBlocks);

    b.CreateCondBr(moreToDo, maskLoop, maskFinalize);
    b.SetInsertPoint(maskFinalize);
}

class CreateMaskKernel : public PabloKernel {
public:
    CreateMaskKernel(KernelBuilder & b, StreamSet * inputStream, StreamSet * maskStream)
        : PabloKernel(b, "CreateMaskKernel",
                      {Binding{"inputStream", inputStream}}, {Binding{"maskStream", maskStream}}) {}
protected:
    void generatePabloMethod() override;
};

void CreateMaskKernel::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    Var * inputStream = pb.createExtract(getInputStreamVar("inputStream"), pb.getInteger(0));

    PabloAST * lastByte = pb.createAdvance(pb.createNot(pb.createScanThru(pb.createNot(inputStream), pb.createOnes())), 1);

    pb.createAssign(pb.createExtract(getOutputStreamVar("maskStream"), pb.getInteger(0)), lastByte);
}

typedef void (*MaskDemoFunctionType)(uint32_t fd);

MaskDemoFunctionType maskdemo_gen(CPUDriver & driver) {
    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b.getInt32Ty(), "inputFileDescriptor"}}, {});

    Scalar * fileDescriptor = P->getInputScalar("inputFileDescriptor");

    StreamSet * const inputStream = P->CreateStreamSet(1, 8);
    StreamSet * const maskStream = P->CreateStreamSet(1, 8);

    P->CreateKernelCall<ReadSourceKernel>(fileDescriptor, inputStream);
    P->CreateKernelCall<CreateMaskKernel>(inputStream, maskStream);

    StreamSet * const outputStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<MaskKernel>(inputStream, maskStream, outputStream);
    SHOW_BYTES(outputStream);
    SHOW_STREAM(outputStream);

    P->CreateKernelCall<StdOutKernel>(outputStream);

    return reinterpret_cast<MaskDemoFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&MaskDemoOptions, codegen::codegen_flags()});
    CPUDriver pxDriver("maskdemo");

    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        llvm::errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
    } else {
        MaskDemoFunctionType func = nullptr;
        func = maskdemo_gen(pxDriver);
        func(fd);
        close(fd);
    }
    return 0;
}

