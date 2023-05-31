#ifndef PIPELINE_KERNEL_COMPILER_CONFIG_H
#define PIPELINE_KERNEL_COMPILER_CONFIG_H

#define PRINT_DEBUG_MESSAGES

#define PRINT_DEBUG_MESSAGES_FOR_KERNEL_NUM 2

// #define PRINT_DEBUG_MESSAGES_FOR_NESTED_PIPELINE_ONLY

// #define PRINT_DEBUG_MESSAGES_FOR_MARKED_KERNELS_ONLY

#define PRINT_DEBUG_MESSAGES_INCLUDE_THREAD_NUM

// #define FORCE_PIPELINE_ASSERTIONS

// #define DISABLE_ZERO_EXTEND

// #define DISABLE_INPUT_ZEROING

// #define DISABLE_OUTPUT_ZEROING

// #define DISABLE_PARTITION_JUMPING

// #define FORCE_LAST_KERNEL_CONSUMER_WRITE_FOR_STREAMSETS

// #define FORCE_EACH_KERNEL_INTO_UNIQUE_PARTITION

// #define TEST_ALL_KERNEL_INPUTS

// #define TEST_ALL_CONSUMERS

// #define FORCE_POP_COUNTS_TO_BE_BITBLOCK_STEPS

// #define USE_PARTITION_GUIDED_SYNCHRONIZATION_VARIABLE_REGIONS

#define GROUP_SHARED_KERNEL_STATE_INTO_CACHE_LINE_ALIGNED_REGIONS

#define FORCE_ALL_INTRA_PARTITION_STREAMSETS_TO_BE_LINEAR

#define FORCE_ALL_INTER_PARTITION_STREAMSETS_TO_BE_LINEAR

// #define THREADLOCAL_BUFFER_CAPACITY_MULTIPLIER 100

// #define NON_THREADLOCAL_BUFFER_CAPACITY_MULTIPLIER 100

// #define PREVENT_THREAD_LOCAL_BUFFERS_FROM_SHARING_MEMORY

// #define DISABLE_ALL_DATA_PARALLEL_SYNCHRONIZATION

#define DISABLE_LINKED_PARTITIONS

// #define FORCE_PIPELINE_TO_PRESERVE_CONSUMED_DATA

// #define OPTIMIZATION_BRANCH_ALWAYS_TAKES_REGULAR_BRANCH

// #define ALLOW_INTERNALLY_SYNCHRONIZED_KERNELS_TO_BE_DATA_PARALLEL

// #define PIN_THREADS_TO_INDIVIDUAL_CORES

// #define USE_LOOKBEHIND_FOR_LAST_VALUE // must match pipeline/internal/popcount_kernel.h

#endif // PIPELINE_KERNEL_COMPILER_CONFIG_H
