#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <kernel/core/kernel_builder.h>
#include <toolchain/toolchain.h>
#include <kernel/pipeline/driver/cpudriver.h>
#include <kernel/core/streamset.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <fcntl.h>

#define SHOW_STREAM(name) if (codegen::EnableIllustrator) P->captureBitstream(#name, name)
#define SHOW_BIXNUM(name) if (codegen::EnableIllustrator) P->captureBixNum(#name, name)
#define SHOW_BYTES(name) if (codegen::EnableIllustrator) P->captureByteData(#name, name)

using namespace kernel;
using namespace llvm;
using namespace codegen;

static cl::OptionCategory FilterByMaskDemoOptions("FilterByMask Demo Options", "FilterByMask demo options.");
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(FilterByMaskDemoOptions));
static cl::opt<std::string> maskFile(cl::Positional, cl::desc("<mask file>"), cl::Required, cl::cat(FilterByMaskDemoOptions));

class FilterByMaskKernel final : public MultiBlockKernel {
public:
    FilterByMaskKernel(KernelBuilder & b, StreamSet * const maskStream, StreamSet * const byteStream, StreamSet * const filteredStream)
    : MultiBlockKernel(b, "filterbymask_kernel",
    {Binding{"maskStream", maskStream, FixedRate(1)}, Binding{"byteStream", byteStream, FixedRate(1)}},
    {Binding{"filteredStream", filteredStream, PopcountOf("maskStream")}}, {}, {}, {}) {}

protected:
    void generateMultiBlockLogic(KernelBuilder & b, llvm::Value * const numOfStrides) override {
        const unsigned fieldWidth = 32;
        Value * mask = b.loadInputStreamBlock("maskStream", b.getInt32(0));
        Value * input = b.loadInputStreamBlock("byteStream", b.getInt32(0));
        Value * filtered = b.mvmd_compress(fieldWidth, input, mask);

        b.storeOutputStreamBlock("filteredStream", b.getInt32(0), filtered);
    }
};

typedef void (*FilterByMaskDemoFunctionType)(uint32_t fd, uint32_t mask_fd);

FilterByMaskDemoFunctionType filterbymaskdemo_gen(CPUDriver & driver) {
    auto & b = driver.getBuilder();
    auto P = driver.makePipeline({Binding{b.getInt32Ty(), "inputFileDescriptor"}, Binding{b.getInt32Ty(), "maskFileDescriptor"}}, {});

    Scalar * inputFileDescriptor = P->getInputScalar("inputFileDescriptor");
    Scalar * maskFileDescriptor = P->getInputScalar("maskFileDescriptor");

    StreamSet * const maskStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<ReadSourceKernel>(maskFileDescriptor, maskStream);
    SHOW_BYTES(maskStream);

    StreamSet * const byteStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<ReadSourceKernel>(inputFileDescriptor, byteStream);
    SHOW_BYTES(byteStream);

    StreamSet * const filteredStream = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<FilterByMaskKernel>(maskStream, byteStream, filteredStream);
    SHOW_BYTES(filteredStream);

    P->CreateKernelCall<StdOutKernel>(filteredStream);

    return reinterpret_cast<FilterByMaskDemoFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    codegen::ParseCommandLineOptions(argc, argv, {&FilterByMaskDemoOptions, codegen::codegen_flags()});
    CPUDriver pxDriver("filterbymaskdemo");
    const int fd = open(inputFile.c_str(), O_RDONLY);
    const int mask_fd = open(maskFile.c_str(), O_RDONLY);
    if (LLVM_UNLIKELY(fd == -1)) {
        errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
        return 1;
    }
    if (LLVM_UNLIKELY(mask_fd == -1)) {
        errs() << "Error: cannot open " << maskFile << " for processing. Skipped.\n";
        close(fd);
        return 1;
    }

    FilterByMaskDemoFunctionType func = nullptr;
    func = filterbymaskdemo_gen(pxDriver);
    func(fd, mask_fd);

    close(fd);
    close(mask_fd);
    return 0;
}
