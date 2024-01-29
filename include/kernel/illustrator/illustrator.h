#ifndef ILLUSTRATOR_H
#define ILLUSTRATOR_H

#include <stdlib.h>

namespace kernel {

class StreamDataIllustrator;

extern "C"
StreamDataIllustrator * createStreamDataIllustrator();

// Each kernel can verify that the display Name of every illustrated value is locally unique but since multiple instances
// of a kernel can be instantiated, we also need the address of the state object to identify each value. Additionally, the
// presence of family kernels means we cannot guarantee that all kernels will be compiled at the same time so we cannot
// number the illustrated values at compile time.
extern "C"
void illustratorRegisterCapturedData(StreamDataIllustrator * illustrator, const char * kernelName, const char * streamName, const void * stateObject, const size_t dim0, const size_t dim1, const size_t itemWidth,
                                     const uint8_t memoryOrdering, const uint8_t illustratorTypeId, const char replacement0, const char replacement1);


extern "C"
void illustratorCaptureStreamData(StreamDataIllustrator * illustrator, const char * kernelName, const char * streamName, const void * stateObject,
                                 const size_t strideNum, const void * streamData, const size_t from, const size_t to);

extern "C"
void illustratorDisplayCapturedData(const StreamDataIllustrator * illustrator);

extern "C"
void destroyStreamDataIllustrator(StreamDataIllustrator *);

}

#endif // ILLUSTRATOR_H
