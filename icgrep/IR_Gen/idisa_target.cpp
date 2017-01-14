/*
 *  Copyright (c) 2016 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */

#include "idisa_target.h"
#include <toolchain.h>
#include <IR_Gen/idisa_avx_builder.h>
#include <IR_Gen/idisa_sse_builder.h>
#include <IR_Gen/idisa_i64_builder.h>
#include <IR_Gen/idisa_nvptx_builder.h>

namespace IDISA {
    
IDISA_Builder * GetIDISA_Builder(Module * mod) {
    const bool hasAVX2 = AVX2_available();
    const bool isArch32Bit = Triple(llvm::sys::getProcessTriple()).isArch32Bit();
    if (LLVM_LIKELY(codegen::BlockSize == 0)) {  // No BlockSize override: use processor SIMD width
        codegen::BlockSize = hasAVX2 ? 256 : 128;
    }
    if (codegen::BlockSize >= 256) {
        if (hasAVX2) {
            return new IDISA_AVX2_Builder(mod, isArch32Bit ? 32 : 64, codegen::BlockSize);
        }
    } else if (codegen::BlockSize == 64) {
        return new IDISA_I64_Builder(mod, isArch32Bit ? 32 : 64);
    }
    return new IDISA_SSE2_Builder(mod, isArch32Bit ? 32 : 64, codegen::BlockSize);
}

IDISA_Builder * GetIDISA_GPU_Builder(Module * mod) {
    return new IDISA_NVPTX20_Builder(mod, 64);
}

}
