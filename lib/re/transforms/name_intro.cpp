/*
 *  Copyright (c) 2022 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include <re/transforms/name_intro.h>

#include <llvm/Support/Casting.h>
#include <llvm/Support/raw_ostream.h>
#include <re/adt/adt.h>
#include <re/adt/re_alt.h>
#include <re/alphabet/alphabet.h>
#include <re/analysis/re_analysis.h>
#include <re/transforms/re_transformer.h>
#include <map>
#include <memory>

using namespace llvm;

namespace re {

Name * NameIntroduction::createName(std::string name, RE * defn) {
    auto f = mNameMap.find(name);
    if (f == mNameMap.end()) {
        mNameMap.emplace(name, defn);
        return makeName(name, defn);
    } else {
        return makeName(name, f->second);
    }
}

void NameIntroduction::showProcessing() {
    for (auto m: mNameMap) {
        llvm::errs() << "Name " << m.first << " ==> " << Printer_RE::PrintRE(m.second) << "\n";
    }
}

VariableLengthCCNamer::VariableLengthCCNamer(unsigned UTF_bits) : NameIntroduction("VariableLengthCCNamer") {
        mEncoder.setCodeUnitBits(UTF_bits);
    }

RE * VariableLengthCCNamer::transformCC (CC * cc) {
    bool variable_length = false;
    variable_length = mEncoder.encoded_length(lo_codepoint(cc->front())) < mEncoder.encoded_length(hi_codepoint(cc->back()));
    if (variable_length) {
        return createName(cc->canonicalName(), cc);
    }
    return cc;
}

FixedSpanNamer::FixedSpanNamer(const cc::Alphabet * a) : NameIntroduction("FixedSpanNamer"), mAlphabet(a), mLgthPrefix("len") {}

RE * FixedSpanNamer::transform(RE * r) {
    auto rg = getLengthRange(r, mAlphabet);
    if ((rg.first == rg.second) && (rg.first > 0)) {
        Name * n = createName(mLgthPrefix + std::to_string(rg.first), r);
        return n;
    }
    if (Alt * alt = dyn_cast<Alt>(r)) {
        std::vector<RE *> newAlts;
        std::map<int, std::vector<RE *>> fixedLengthAlts;
        for (auto e : *alt) {
            auto rg = getLengthRange(e, mAlphabet);
            if (rg.first == 0) return alt;  //  zero-length REs cause problems
            if (rg.first == rg.second) {
                auto f = fixedLengthAlts.find(rg.first);
                if (f == fixedLengthAlts.end()) {
                    fixedLengthAlts.emplace(rg.first, std::vector<RE *>{e});
                } else {
                    f->second.push_back(e);
                }
            } else {
                newAlts.push_back(e);
            }
        }
        if (fixedLengthAlts.empty()) return alt;
        for (auto grp : fixedLengthAlts) {
            RE * defn;
            if (grp.second.size() == 1) {
                defn = grp.second[0];
            } else {
                defn = makeAlt(grp.second.begin(), grp.second.end());
            }
            Name * n = createName(mLgthPrefix + std::to_string(grp.first), defn);
            newAlts.push_back(n);
        }
        if (newAlts.size() == 1) return newAlts[0];
        return makeAlt(newAlts.begin(), newAlts.end());
    }
    return r;
}

UniquePrefixNamer::UniquePrefixNamer() : NameIntroduction("UniquePrefixNamer") {}

RE * UniquePrefixNamer::transform(RE * r) {
    if (Alt * alt = dyn_cast<Alt>(r)) {
        std::vector<RE *> alts;
        bool fixedPrefixFound = false;
        for (auto e : *alt) {
            RE * prefix, * suffix;
            std::tie(prefix, suffix) = ParseUniquePrefix(e);
            if (isEmptySeq(prefix) || isEmptySeq(suffix)) {
                alts.push_back(e);
            } else {
                fixedPrefixFound = true;
                std::string prefixName = Printer_RE::PrintRE(prefix);
                Name * pfx = makeName(prefixName, prefix);
                std::string altName = Printer_RE::PrintRE(e);
                Name * n = createName(altName, makeSeq({pfx, suffix}));
                alts.push_back(n);
            }
        }
        if (fixedPrefixFound) {
            return makeAlt(alts.begin(), alts.end());
        }
        return r;
    }
    RE * prefix, * suffix;
    std::tie(prefix, suffix) = ParseUniquePrefix(r);
    if (isEmptySeq(prefix) || isEmptySeq(suffix)) {
        return r;
    }
    std::string prefixName = Printer_RE::PrintRE(prefix);
    Name * pfx = makeName(prefixName, prefix);
    std::string rName = Printer_RE::PrintRE(r);
    return createName(rName, makeSeq({pfx, suffix}));
}

const CC * variableCodepoints(const RE * re) {
    if (const Seq * seq = dyn_cast<Seq>(re)) {
        CC * variable = makeCC();
        for (const RE * e : *seq) {
            variable = makeCC(variable, variableCodepoints(e));
        }
        return variable;
    } else if (const Rep * rep = dyn_cast<Rep>(re)) {
        if (rep->getLB() == rep->getUB()) {
            return variableCodepoints(rep->getRE());
        } else {
            return matchableCodepoints(rep->getRE());
        }
    } else if (const Alt * alt = dyn_cast<Alt>(re)) {
        // rule that all matchable codepoints are variable
        return matchableCodepoints(alt);
    } else if (const Name * n = dyn_cast<Name>(re)) {
        return variableCodepoints(n->getDefinition());
    } else if (const Diff * diff = dyn_cast<Diff>(re)) {
        return variableCodepoints(diff->getLH());
    } else if (const Intersect * e = dyn_cast<Intersect>(re)) {
        return intersectCC(variableCodepoints(e->getLH()), variableCodepoints(e->getRH()));
    } else if (const Group * g = dyn_cast<Group>(re)) {
        return variableCodepoints(g->getRE());
    } else if (const Capture * c = dyn_cast<Capture>(re)) {
        return variableCodepoints(c->getCapturedRE());
    } else if (const Reference * r = dyn_cast<Reference>(re)) {
        return variableCodepoints(r->getCapture());
    }
    // Other expressions are all singleCCs, not variable.
    return makeCC();
}

unsigned fixedCodepointCount(const RE * re, const CC * variableCC) {
    unsigned countSoFar = 0;
    if (const CC * cc = dyn_cast<CC>(re)) {
        if (cc->intersects(*variableCC)) return 0;
        return 1;
    } else if (const PropertyExpression * pe = dyn_cast<PropertyExpression>(re)) {
        if (pe->getKind() == PropertyExpression::Kind::Codepoint) {
            if (CC * cc = dyn_cast<CC>(pe->getResolvedRE())) {
                return fixedCodepointCount(cc, variableCC);
            }
        }
        return 0;
    } else if (const Seq * seq = dyn_cast<Seq>(re)) {
        for (const RE * e : *seq) {
            countSoFar += fixedCodepointCount(e, variableCC);
        }
        return countSoFar;
    } else if (const Rep * rep = dyn_cast<Rep>(re)) {
        return (rep->getLB()) * fixedCodepointCount(rep->getRE(), variableCC);
    } else if (const Alt * alt = dyn_cast<Alt>(re)) {
        // rule that all matchable codepoints are variable
        return 0;
    } else if (const Name * n = dyn_cast<Name>(re)) {
        return fixedCodepointCount(n->getDefinition(), variableCC);
    } else if (const Diff * diff = dyn_cast<Diff>(re)) {
        if (const CC * cc = dyn_cast<CC>(diff->getRH())) {
            if (variableCC->subset(*cc)) {
                if (isa<Any>(diff->getLH())) return 1;
                if (const CC * cc1 = dyn_cast<CC>(diff->getLH())) {
                    if (cc1->subset(*cc)) return 0;
                    return 1;
                }
                return 0;
            }
            return 0;
        }
        return 0;
    } else if (const Intersect * e = dyn_cast<Intersect>(re)) {
        auto isec = intersectCC(matchableCodepoints(e->getLH()), matchableCodepoints(e->getRH()));
        if (isec->intersects(*variableCC)) return 0;
        return 1;
    } else if (const Group * g = dyn_cast<Group>(re)) {
        return fixedCodepointCount(g->getRE(), variableCC);
    } else if (const Capture * c = dyn_cast<Capture>(re)) {
        return fixedCodepointCount(c->getCapturedRE(), variableCC);
    } else if (const Reference * r = dyn_cast<Reference>(re)) {
        return fixedCodepointCount(r->getCapture(), variableCC);
    }
    return 0;
}

std::string Repeated_CC_Seq_Namer::genSym() {
    mGenSym++;
    return mPrefix + std::to_string(mGenSym);
}

Repeated_CC_Seq_Namer::Repeated_CC_Seq_Namer() :
    NameIntroduction("Repeated_CC_Seq_Namer"), mPrefix("rep"), mGenSym(0) {}

RE * Repeated_CC_Seq_Namer::transform(RE * r) {
    const CC * varCC = variableCodepoints(r);
    if (varCC->empty()) return r;
    unsigned fixed = fixedCodepointCount(r, varCC);
    llvm::errs() << "fixedCodepointCount" << fixed << "\n";
    if (fixed > 0) {
        auto nameStr = genSym();
        Name * n = createName(nameStr, r);
        mInfoMap.emplace(nameStr, std::make_pair(varCC, fixed));
        return n;
    }
    if (Alt * alt = dyn_cast<Alt>(r)) {
        std::vector<RE *> newAlts;
        bool repCCseqFound = false;
        for (auto e : *alt) {
            const CC * varCC = variableCodepoints(r);
            unsigned fixed = fixedCodepointCount(r, varCC);
            if (fixed == 0) {
                newAlts.push_back(e);
                continue;
            }
            repCCseqFound = true;
            auto nameStr = genSym();
            Name * n = createName(nameStr, r);
            mInfoMap.emplace(nameStr, std::make_pair(varCC, fixed));
            newAlts.push_back(n);
        }
        if (!repCCseqFound) return alt;
        if (newAlts.size() == 1) return newAlts[0];
        return makeAlt(newAlts.begin(), newAlts.end());
    }
    return r;
}

class Canonical_External_Names : public RE_Transformer {
public:
    Canonical_External_Names(std::vector<std::string> & external_names);
protected:
    RE * transformName (Name * n) override;
private:
    std::map<std::string, Name *>  mExternalMap;
};

Canonical_External_Names::Canonical_External_Names(std::vector<std::string> & external_names)
: RE_Transformer("Canonical_External_Names") {
    for (unsigned i = 0; i < external_names.size(); i++) {
        mExternalMap.emplace(external_names[i], makeName("@" + std::to_string(i)));
    }
}

RE * Canonical_External_Names::transformName(Name * name) {
    auto f = mExternalMap.find(name->getFullName());
    if (f == mExternalMap.end()) return name;
    Name * canon_name = f->second;
    if (canon_name->getDefinition() == nullptr) {
        canon_name->setDefinition(name->getDefinition());
    }
    return canon_name;
}

RE * canonicalizeExternals(RE * r, std::vector<std::string> & external_names) {
    return Canonical_External_Names(external_names).transformRE(r);
}

}

