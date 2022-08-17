#include <re/transforms/reference_transform.h>

#include <re/adt/adt.h>
#include <re/analysis/capture-ref.h>
#include <re/analysis/re_analysis.h>
#include <re/transforms/re_transformer.h>
#include <re/transforms/name_intro.h>
#include <unicode/data/PropertyAliases.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm;

namespace re {


struct FixedReferenceTransformer : public NameIntroduction {
public:
    FixedReferenceTransformer(const ReferenceInfo & info) :
    NameIntroduction("FixedReferenceTransformer"),
        mRefInfo(info) {}
    RE * transformReference(Reference * r) override {
        auto rg1 = getLengthRange(r->getCapture(), &cc::Unicode);
        if (rg1.first != rg1.second) return r;
        std::string instanceName = r->getInstanceName();
        auto mapping = mRefInfo.twixtREs.find(instanceName);
        if (mapping == mRefInfo.twixtREs.end()) return r;
        auto rg2 = getLengthRange(mapping->second, &cc::Unicode);
        if (rg2.first != rg2.second) return r;
        UCD::property_t p = r->getReferencedProperty();
        std::string pname = p == UCD::identity ? "Unicode" : UCD::getPropertyFullName(p);
        int fixed_dist = rg1.first + rg2.first;
        std::string externalName = pname + "@-" + std::to_string(fixed_dist);
        return createName(externalName, r);
    };
private:
    const ReferenceInfo & mRefInfo;
};

RE * fixedReferenceTransform(const ReferenceInfo & info, RE * r) {
    return FixedReferenceTransformer(info).transformRE(r);
}

}
