/*
 *  Copyright (c) 2018 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <string>
#include <vector>
#include <locale>
#include <codecvt>
#include <re/Unicode/decomposition.h>
#include <re/re_cc.h>
#include <re/re_seq.h>
#include <re/re_alt.h>
#include <re/re_group.h>
#include <re/re_range.h>
#include <re/re_diff.h>
#include <re/re_intersect.h>
#include <re/re_assertion.h>
#include <UCD/unicode_set.h>
#include <UCD/PropertyAliases.h>
#include <UCD/PropertyObjects.h>
#include <UCD/PropertyObjectTable.h>
#include <UCD/PropertyValueAliases.h>
#include <llvm/Support/Casting.h>

using namespace llvm;
using namespace re;

namespace UCD {
    
// Constants for computation of Hangul decompositions, see Unicode Standard, section 3.12.
const codepoint_t Hangul_SBase = 0xAC00;
const codepoint_t Hangul_LBase = 0x1100;
//const codepoint_t Hangul_LMax = 0x1112;
const codepoint_t Hangul_VBase = 0x1161;
//const codepoint_t Hangul_VMax = 0x1175;
const codepoint_t Hangul_TBase = 0x11A7;
//const codepoint_t Hangul_TMax = 0x11C2;
const unsigned Hangul_TCount = 28;
const unsigned Hangul_NCount = 588;
const unsigned Hangul_SCount = 11172;

static inline std::u32string getStringPiece(Seq * s, unsigned position) {
    unsigned pos = position;
    unsigned size = s->size();
    std::u32string rslt;
    while ((pos < size) && isa<CC>((*s)[pos])) {
        CC * cc = cast<CC>((*s)[pos]);
        if (cc->empty()) return rslt;
        codepoint_t lo = lo_codepoint(cc->front());
        codepoint_t hi = hi_codepoint(cc->back());
        if (lo != hi) // not a singleton CC; end of the string piece.
            return rslt;
        rslt.push_back(lo);
        pos++;
    }
    return rslt;
}
    
NFD_Transformer::NFD_Transformer(DecompositionOptions opt) :
    RE_Transformer("toNFD"),
    mOptions(opt),
    decompTypeObj(cast<EnumeratedPropertyObject>(property_object_table[dt])),
    decompMappingObj(cast<StringPropertyObject>(property_object_table[dm])),
    cccObj(cast<EnumeratedPropertyObject>(property_object_table[ccc])),
    caseFoldObj(cast<StringOverridePropertyObject>(property_object_table[cf])),
    canonicalMapped(decompTypeObj->GetCodepointSet(DT_ns::Can)),
    cc0Set(cccObj->GetCodepointSet(CCC_ns::NR)),
    selfNFKD(decompMappingObj->GetReflexiveSet()),
    selfCaseFold(caseFoldObj->GetReflexiveSet())
{}

static UnicodeSet HangulPrecomposed = UnicodeSet(Hangul_SBase, Hangul_SBase + Hangul_SCount - 1);

bool hasOption(enum DecompositionOptions optionSet, enum DecompositionOptions testOption) {
    return (testOption & optionSet) != 0;
}
    
bool NFD_Transformer::reordering_needed(std::u32string & prefix, codepoint_t suffix_cp) {
    if (prefix.empty()) return false;
    if (cc0Set.contains(suffix_cp)) return false;
    auto cc1 = cccObj->GetEnumerationValue(prefix.back());
    auto cc2 = cccObj->GetEnumerationValue(suffix_cp);
    return cc1 > cc2;
}

void NFD_Transformer::NFD_append1(std::u32string & NFD_string, codepoint_t cp) {
    if (HangulPrecomposed.contains(cp)) {
        // Apply NFD normalization; no NFKD or casefolding required
        auto SIndex = cp - Hangul_SBase;
        auto LIndex = SIndex / Hangul_NCount;
        auto VIndex = (SIndex % Hangul_NCount) / Hangul_TCount;
        auto TIndex = SIndex % Hangul_TCount;
        NFD_string.push_back(Hangul_LBase + LIndex);
        NFD_string.push_back(Hangul_VBase + VIndex);
        if (TIndex > 0) {
            NFD_string.push_back(Hangul_TBase + TIndex);
        }
    } else if (canonicalMapped.contains(cp)) {
        std::string u8decomposed = decompMappingObj->GetStringValue(cp);
        std::u32string dms = conv.from_bytes(u8decomposed);
        // Recursive normalization may be necessary.
        NFD_append(NFD_string, dms);
        // After canonical mappings are handled, canonical ordering may be required.
        // This should be done before casefolding.
    } else if (reordering_needed(NFD_string, cp)) {
        // Reorder the last two characters - recursion will handle
        // rare multiposition reordering.
        std::u32string reordered({cp, NFD_string.back()});
        NFD_string.pop_back();
        NFD_append(NFD_string, reordered);
    } else if (hasOption(mOptions, UCD::CaseFold) && !selfCaseFold.contains(cp)) {
        std::u32string dms = conv.from_bytes(caseFoldObj->GetStringValue(cp));
        NFD_append(NFD_string, dms);
    } else if (hasOption(mOptions, UCD::NFKD) && (!selfNFKD.contains(cp))) {
        std::u32string dms = conv.from_bytes(decompMappingObj->GetStringValue(cp));
        NFD_append(NFD_string, dms);
    } else {
        NFD_string.push_back(cp);
    }
}

void NFD_Transformer::NFD_append(std::u32string & NFD_string, std::u32string & to_convert) {
    for (unsigned i = 0; i < to_convert.size(); i++) {
        NFD_append1(NFD_string, to_convert[i]);
    }
}

RE * NFD_Transformer::transformGroup(Group * g) {
    re::Group::Mode mode = g->getMode();
    re::Group::Sense sense = g->getSense();
    auto r = g->getRE();
    UCD::DecompositionOptions saveOptions = mOptions;
    if (mode == re::Group::Mode::CaseInsensitiveMode) {
        if (sense == re::Group::Sense::On) {
            mOptions = static_cast<UCD::DecompositionOptions>(mOptions | UCD::CaseFold);
        } else {
            mOptions = static_cast<UCD::DecompositionOptions>(mOptions & ~UCD::CaseFold);
        }
    } else if (mode == re::Group::Mode::CompatibilityMode) {
        if (sense == re::Group::Sense::On) {
            mOptions = static_cast<UCD::DecompositionOptions>(mOptions | UCD::NFKD);
        } else {
            mOptions = static_cast<UCD::DecompositionOptions>(mOptions & ~UCD::NFKD);
        }
    }
    RE * t = transform(r);
    mOptions = saveOptions;
    if (t == r) return g;
    return makeGroup(mode, t, sense);
    
}

RE * NFD_Transformer::transformCC(CC * cc) {
    UnicodeSet mappingRequired = *cc & (canonicalMapped + HangulPrecomposed);
    if (hasOption(mOptions, UCD::CaseFold)) {
        mappingRequired = mappingRequired + (*cc - selfCaseFold);
    }
    if (hasOption(mOptions, UCD::NFKD)) {
        mappingRequired = mappingRequired + (*cc - selfNFKD);
    }
    if (mappingRequired.empty()) return cc;
    std::vector<RE *> alts;
    CC * finalCC = makeCC(*cc - mappingRequired);
    for (const interval_t & i : mappingRequired) {
        for (codepoint_t cp = lo_codepoint(i); cp <= hi_codepoint(i); cp++) {
            std::u32string decomp;
            NFD_append1(decomp, cp);
            if (decomp.size() == 1) {
                finalCC = makeCC(finalCC, makeCC(decomp[0]));
            } else {
                alts.push_back(u32string2re(decomp));
            }
        }
    }
    if (!finalCC->empty()) alts.push_back(finalCC);
    return makeAlt(alts.begin(), alts.end());
}

RE * NFD_Transformer::transformSeq(Seq * seq) {
    // find and process all string pieces
    unsigned size = seq->size();
    if (size == 0) return seq;
    std::vector<RE *> list;
    unsigned i = 0;
    while (i < size) {
        std::u32string stringPiece = getStringPiece(seq, i);
        if (stringPiece.size() > 0) {
            std::u32string s;
            NFD_append(s, stringPiece);
            list.push_back(u32string2re(s));
            i += stringPiece.size();
        } else {
            list.push_back(transform((*seq)[i]));
            i++;
        }
    }
    return makeSeq(list.begin(), list.end());
}
} // end namespace UCD
