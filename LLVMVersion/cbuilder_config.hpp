
/* Optimal LLVM IRBuilder<> configuration for CBuilder to inherit from.
   Robust against the LLVM IRBuilder<> class hierarchy changes across
   older and newer LLVM versions. */

#ifndef CBUILDER_CONFIH_H
#define CBUILDER_CONFIH_H

#include <llvm/IR/IRBuilder.h>

namespace llvm { class ConstantFolder; }
namespace llvm { class IRBuilderDefaultInserter; }
namespace llvm { class LLVMContext; }

typedef llvm::IRBuilder<llvm::ConstantFolder, llvm::IRBuilderDefaultInserter> CBuilderBase;

#endif
