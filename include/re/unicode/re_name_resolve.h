#ifndef RE_NAME_RESOLVE_H
#define RE_NAME_RESOLVE_H

#include <re/transforms/re_transformer.h>

namespace re {

    class RE;
    class Name;
    enum class NameStandard {Posix, Unicode};
    RE * resolveEscapeNames(RE * re, NameStandard c = NameStandard::Unicode);
    RE * resolveAnchors(RE * r, RE * breakRE,
                        NameTransformationMode m = NameTransformationMode::None);

}
#endif
