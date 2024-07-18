#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>               // for StdOutKernel_
#include <llvm/IR/Function.h>                      // for Function, Function...
#include <llvm/IR/Module.h>                        // for Module
#include <llvm/Support/CommandLine.h>              // for ParseCommandLineOp...
#include <llvm/Support/Debug.h>                    // for dbgs
#include <kernel/core/kernel_builder.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <kernel/io/stdout_kernel.h>
#include <llvm/ADT/StringRef.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <fcntl.h>

#define SHOW_STREAM(name) if (codegen::EnableIllustrator) P->captureBitstream(#name, name)
#define SHOW_BIXNUM(name) if (codegen::EnableIllustrator) P->captureBixNum(#name, name)
#define SHOW_BYTES(name) if (codegen::EnableIllustrator) P->captureByteData(#name, name)

using namespace kernel;
using namespace llvm;
using namespace codegen;

static cl::OptionCategory PackDemoOptions("Pack Demo Options", "Pack demo options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(PackDemoOptions));

class PackKernel final : public MultiBlockKernel {
public:
    PackKernel(KernelBuilder & b,
              StreamSet * const byteStream,
              StreamSet * const Merged);
    static constexpr unsigned fw = 8;
    static constexpr unsigned inputRate = 1;
    static constexpr unsigned outputRate = 2;
protected:
    void generateMultiBlockLogic(KernelBuilder & b, llvm::Value * const numOfStrides) override;

};

PackKernel::PackKernel(KernelBuilder & b, StreamSet * const byteStream, StreamSet * const Merged)
: MultiBlockKernel(b, "pack_kernel",
{Binding{"byteStream", byteStream, FixedRate(inputRate)}},
    {Binding{"Merged", Merged, FixedRate(outputRate)}}, {}, {}, {})  {}

void PackKernel::generateMultiBlockLogic(KernelBuilder & b, Value * const numOfStrides) {
    llvm::errs() << "Generating multi-block logic\n";
    const unsigned inputPacksPerStride = fw * inputRate;
    const unsigned outputPacksPerStride = fw * outputRate;

    BasicBlock * entry = b.GetInsertBlock();
    BasicBlock * packLoop = b.CreateBasicBlock("packLoop");
    BasicBlock * packFinalize = b.CreateBasicBlock("packFinalize");
    Constant * const ZERO = b.getSize(0);
    // how many blocks of data; termination condition of while loop
    Value * numOfBlocks = numOfStrides;  
    if (getStride() != b.getBitBlockWidth()) {
        numOfBlocks = b.CreateShl(numOfStrides, b.getSize(std::log2(getStride()/b.getBitBlockWidth())));
        llvm::errs() << "stride = " << getStride() << "\n";
    }
    b.CreateBr(packLoop);
    b.SetInsertPoint(packLoop);
    PHINode * blockOffsetPhi = b.CreatePHI(b.getSizeTy(), 2);
    blockOffsetPhi->addIncoming(ZERO, entry);

    Value * bytepack[inputPacksPerStride];
    for (unsigned i = 0; i < inputPacksPerStride; i++) {
        llvm::errs() << "Loading input stream pack " << i << "\n";
        bytepack[i] = b.loadInputStreamPack("byteStream", ZERO, b.getInt32(i), blockOffsetPhi);
    }

    Value * duplicated[outputPacksPerStride];

    for (unsigned i = 0; i < inputPacksPerStride; i++) {
        llvm::errs() << "Duplicating input pack " << i << "\n";
        duplicated[2*i] = b.esimd_mergel(fw, bytepack[i], bytepack[i]);
        duplicated[2*i+1] = b.esimd_mergeh(fw, bytepack[i], bytepack[i]);

        b.storeOutputStreamPack("Merged", ZERO, b.getInt32(2*i), blockOffsetPhi, duplicated[2*i]);
        b.storeOutputStreamPack("Merged", ZERO, b.getInt32(2*i+1), blockOffsetPhi, duplicated[2*i+1]);
    }

    Value * nextBlk = b.CreateAdd(blockOffsetPhi, b.getSize(1));
    blockOffsetPhi->addIncoming(nextBlk, packLoop);
    Value * moreToDo = b.CreateICmpNE(nextBlk, numOfBlocks);

    b.CreateCondBr(moreToDo, packLoop, packFinalize);
    b.SetInsertPoint(packFinalize);
    llvm::errs() << "Finished generating multi-block logic\n";
}

typedef void (*PackDemoFunctionType)(uint32_t fd);

PackDemoFunctionType packdemo_gen (CPUDriver & driver) {

    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b.getInt32Ty(), "inputFileDecriptor"}}, {});

    Scalar * fileDescriptor = P->getInputScalar("inputFileDecriptor");

    // Source data
    StreamSet * const codeUnitStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<ReadSourceKernel>(fileDescriptor, codeUnitStream);
    SHOW_BYTES(codeUnitStream);

    StreamSet * const mergedStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<PackKernel>(codeUnitStream, mergedStream);
    SHOW_BYTES(mergedStream);

    P->CreateKernelCall<StdOutKernel>(mergedStream);

    return reinterpret_cast<PackDemoFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&PackDemoOptions, codegen::codegen_flags()});
    CPUDriver pxDriver("packdemo");
    const int fd = open(inputFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
    } else {
        PackDemoFunctionType func = nullptr;
        func = packdemo_gen(pxDriver);
        func(fd);
        close(fd);
    }
    return 0;
}