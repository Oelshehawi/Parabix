#ifndef PIPELINE_KERNEL_COMPILER_CONFIG_H
#define PIPELINE_KERNEL_COMPILER_CONFIG_H

// #define PRINT_DEBUG_MESSAGES

// #define PRINT_DEBUG_MESSAGES_FOR_KERNEL_NUM 2

// #define PRINT_DEBUG_MESSAGES_INCLUDE_THREAD_NUM

// #define DISABLE_ZERO_EXTEND

// #define DISABLE_INPUT_ZEROING

// #define DISABLE_OUTPUT_ZEROING

// #define DISABLE_PARTITION_JUMPING

// #define FORCE_PIPELINE_ASSERTIONS

#define THREAD_LOCAL_BUFFER_OVERSIZE_FACTOR 16

// #define FORCE_LAST_KERNEL_CONSUMER_WRITE_FOR_STREAMSETS

// #define FORCE_EACH_KERNEL_INTO_UNIQUE_PARTITION

// #define TEST_ALL_KERNEL_INPUTS

// #define TEST_ALL_CONSUMERS

// #define PRINT_BUFFER_GRAPH

#define ENABLE_GRAPH_TESTING_FUNCTIONS

// #define FORCE_POP_COUNTS_TO_BE_BITBLOCK_STEPS

#define USE_FIXED_SEGMENT_NUMBER_INCREMENTS

#define GROUP_SHARED_KERNEL_STATE_INTO_CACHE_LINE_ALIGNED_REGIONS

// #define FUSE_ADJACENT_LINKED_PARTITIONS

#define FORCE_ALL_INTRA_PARTITION_STREAMSETS_TO_BE_LINEAR

#define FORCE_ALL_INTER_PARTITION_STREAMSETS_TO_BE_LINEAR

// #define PIN_THREADS_TO_INDIVIDUAL_CORES

// #define SPLIT_DISCONNECTED_PARTITION_COMPONENTS

// #define USE_LOOKBEHIND_FOR_LAST_VALUE // must match pipeline/internal/popcount_kernel.h

#endif // PIPELINE_KERNEL_COMPILER_CONFIG_H
