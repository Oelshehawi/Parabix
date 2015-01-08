/*
 *  Copyright (c) 2014 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "re_compiler.h"
//Regular Expressions
#include <re/re_name.h>
#include <re/re_any.h>
#include <re/re_start.h>
#include <re/re_end.h>
#include <re/re_alt.h>
#include <re/re_cc.h>
#include <re/re_seq.h>
#include <re/re_rep.h>
#include <re/re_diff.h>
#include <re/re_intersect.h>
#include <re/re_assertion.h>
#include <re/re_analysis.h>
#include <cc/cc_namemap.hpp>
#include <pablo/codegenstate.h>

#include <assert.h>
#include <stdexcept>

using namespace pablo;

namespace re {


RE_Compiler::RE_Compiler(PabloBlock & baseCG, const cc::CC_NameMap & nameMap)
: mCG(baseCG)
, mLineFeed(nullptr)
, mInitial(nullptr)
, mNonFinal(nullptr)
{

}
    
    
MarkerType RE_Compiler::AdvanceMarker(MarkerType m, MarkerPosition newpos, PabloBlock & pb) {
    if (m.pos == newpos) return m;
    if (m.pos > newpos) throw std::runtime_error("icgrep internal error: attempt to AdvanceMarker backwards");
    Assign * a = m.stream;
    if (m.pos == FinalMatchByte) {
        // Must advance at least to InitialPostPositionByte
        a = pb.createAssign("adv", pb.createAdvance(a, 1));
    }
    // Now at InitialPostPositionByte; is a further advance needed?
    if (newpos == FinalPostPositionByte) {
        // Must advance through nonfinal bytes
        a = pb.createAssign("scanToFinal", pb.createScanThru(pb.createAnd(mInitial, a), mNonFinal));
    }
    return {newpos, a};
}

void RE_Compiler::AlignMarkers(MarkerType & m1, MarkerType & m2, PabloBlock & pb) {
    if (m1.pos < m2.pos) {
        m1 = AdvanceMarker(m1, m2.pos, pb); 
    }
    else if (m2.pos < m1.pos) {
        m2 = AdvanceMarker(m2, m1.pos, pb); 
    }
}
    
    

#define USE_IF_FOR_NONFINAL 1
#define USE_IF_FOR_CRLF
#define UNICODE_LINE_BREAK true


void RE_Compiler::initializeRequiredStreams(cc::CC_Compiler & ccc) {

    const std::string initial = "initial";
    const std::string nonfinal = "nonfinal";

    Assign * LF = mCG.createAssign("LF", ccc.compileCC(makeCC(0x0A)));
    mLineFeed = LF;
    PabloAST * CR = ccc.compileCC(makeCC(0x0D));
    PabloAST * LF_VT_FF_CR = ccc.compileCC(makeCC(0x0A, 0x0D));
#ifndef USE_IF_FOR_CRLF
    mCRLF = mCG.createAnd(mCG.createAdvance(CR, 1), mLineFeed);
#else
    PabloBlock & crb = PabloBlock::Create(mCG);
    Assign * cr1 = crb.createAssign("cr1", crb.createAdvance(CR, 1));
    Assign * acrlf = crb.createAssign("crlf", crb.createAnd(cr1, LF));
    mCG.createIf(CR, std::move(std::vector<Assign *>{acrlf}), crb);
    mCRLF = acrlf;
#endif

#ifndef USE_IF_FOR_NONFINAL
    PabloAST * u8single = ccc.compileCC(makeCC(0x00, 0x7F));
    PabloAST * u8pfx2 = ccc.compileCC(makeCC(0xC2, 0xDF));
    PabloAST * u8pfx3 = ccc.compileCC(makeCC(0xE0, 0xEF));
    PabloAST * u8pfx4 = ccc.compileCC(makeCC(0xF0, 0xF4));
    PabloAST * u8pfx = mCG.createOr(mCG.createOr(u8pfx2, u8pfx3), u8pfx4);
    mInitial = mCG.createAssign(initial, mCG.createOr(u8pfx, u8single));

    PabloAST * u8scope32 = mCG.createAdvance(u8pfx3, 1);
    PabloAST * u8scope42 = mCG.createAdvance(u8pfx4, 1);
    PabloAST * u8scope43 = mCG.createAdvance(u8scope42, 1);
    PabloAST * NEL = mCG.createAnd(mCG.createAdvance(ccc.compileCC(makeCC(0xC2)), 1), ccc.compileCC(makeCC(0x85)));
    PabloAST * E2_80 = mCG.createAnd(mCG.createAdvance(ccc.compileCC(makeCC(0xE2)), 1), ccc.compileCC(makeCC(0x80)));
    PabloAST * LS_PS = mCG.createAnd(mCG.createAdvance(E2_80, 1), ccc.compileCC(makeCC(0xA8,0xA9)));
    PabloAST * LB_chars = mCG.createOr(LF_VT_FF_CR, mCG.createOr(NEL, LS_PS));
    mNonFinal = mCG.createAssign(nonfinal, mCG.createOr(mCG.createOr(u8pfx, u8scope32), mCG.createOr(u8scope42, u8scope43)));
    mUnicodeLineBreak = mCG.createAnd(LB_chars, mCG.createNot(mCRLF));  // count the CR, but not CRLF
#endif

#ifdef USE_IF_FOR_NONFINAL
    PabloAST * u8single = ccc.compileCC(makeCC(0x00, 0x7F));
    PabloAST * u8pfx = ccc.compileCC(makeCC(0xC0, 0xFF));
    PabloBlock & it = PabloBlock::Create(mCG);
    PabloAST * u8pfx2 = ccc.compileCC(makeCC(0xC2, 0xDF), it);
    PabloAST * u8pfx3 = ccc.compileCC(makeCC(0xE0, 0xEF), it);
    PabloAST * u8pfx4 = ccc.compileCC(makeCC(0xF0, 0xF4), it);
    Assign * valid_pfx = it.createAssign("valid_pfx", it.createOr(it.createOr(u8pfx2, u8pfx3), u8pfx4));
    PabloAST * u8scope32 = it.createAdvance(u8pfx3, 1);
    PabloAST * u8scope42 = it.createAssign("u8scope42", it.createAdvance(u8pfx4, 1));
    PabloAST * u8scope43 = it.createAdvance(u8scope42, 1);
    Assign * a_nonfinal = it.createAssign(nonfinal, it.createOr(it.createOr(u8pfx, u8scope32), it.createOr(u8scope42, u8scope43)));
    PabloAST * NEL = it.createAnd(it.createAdvance(ccc.compileCC(makeCC(0xC2), it), 1), ccc.compileCC(makeCC(0x85), it));
    PabloAST * E2_80 = it.createAnd(it.createAdvance(ccc.compileCC(makeCC(0xE2), it), 1), ccc.compileCC(makeCC(0x80), it));
    PabloAST * LS_PS = it.createAnd(it.createAdvance(E2_80, 1), ccc.compileCC(makeCC(0xA8,0xA9), it));
    Assign * NEL_LS_PS = it.createAssign("NEL_LS_PS", it.createOr(NEL, LS_PS));
    mCG.createIf(u8pfx, std::move(std::vector<Assign *>{valid_pfx, a_nonfinal, NEL_LS_PS}), it);
    PabloAST * LB_chars = mCG.createOr(LF_VT_FF_CR, NEL_LS_PS);
    mInitial = mCG.createAssign(initial, mCG.createOr(u8single, valid_pfx));
    mNonFinal = a_nonfinal;
    mUnicodeLineBreak = mCG.createAnd(LB_chars, mCG.createNot(mCRLF));  // count the CR, but not CRLF
    #endif
}

void RE_Compiler::finalizeMatchResult(MarkerType match_result) {
    //These three lines are specifically for grep.
    PabloAST * lb = UNICODE_LINE_BREAK ? mUnicodeLineBreak : mLineFeed;
    Assign * v = markerVar(match_result);
    mCG.createAssign("matches", mCG.createAnd(mCG.createMatchStar(v, mCG.createNot(lb)), lb), 0);
    mCG.createAssign("lf", mCG.createAnd(lb, mCG.createNot(mCRLF)), 1);
}

MarkerType RE_Compiler::compile(RE * re, PabloBlock & pb) {
    return process(re, makeMarker(InitialPostPositionByte, pb.createAssign("start", pb.createOnes())), pb);
}

PabloAST * RE_Compiler::character_class_strm(Name * name, PabloBlock & pb) {
    Assign * var = name->getCompiled();
    if (var) {
        return var;
    }
    else {
        RE * def = name->getDefinition();
        if (def != nullptr) {
            MarkerType m = compile(def, mCG);
            assert(markerPos(m) == FinalMatchByte);
            Assign * v = markerVar(m);
            name->setCompiled(markerVar(m));
            return v;
        }
        else if (name->getType() == Name::Type::UnicodeProperty) {
            return pb.createCall(name->getName());
        }
        else {
            throw std::runtime_error("Unresolved name " + name->getName());
        }
    }
}

PabloAST * RE_Compiler::nextUnicodePosition(MarkerType m, PabloBlock & pb) {
    if (markerPos(m) == FinalPostPositionByte) {
        return markerVar(m);
    }
    else if (markerPos(m) == InitialPostPositionByte) {
        return pb.createScanThru(pb.createAnd(mInitial, markerVar(m)), mNonFinal);
    }
    else {
        //return pb.createAdvanceThenScanThru(pb.createVar(markerVar(m), pb), mNonFinal);
        return pb.createScanThru(pb.createAnd(mInitial, pb.createAdvance(markerVar(m), 1)), mNonFinal);
    }
}

MarkerType RE_Compiler::process(RE * re, MarkerType marker, PabloBlock & pb) {
    if (Name * name = dyn_cast<Name>(re)) {
        return process(name, marker, pb);
    }
    else if (Seq* seq = dyn_cast<Seq>(re)) {
        return process(seq, marker, pb);
    }
    else if (Alt * alt = dyn_cast<Alt>(re)) {
        return process(alt, marker, pb);
    }
    else if (Rep * rep = dyn_cast<Rep>(re)) {
        return process(rep, marker, pb);
    }
    else if (Assertion * a = dyn_cast<Assertion>(re)) {
        return process(a, marker, pb);
    }
    else if (isa<Any>(re)) {
        PabloAST * nextPos = nextUnicodePosition(marker, pb);
        PabloAST * dot = pb.createNot(UNICODE_LINE_BREAK ? pb.createOr(mUnicodeLineBreak, mCRLF) : mLineFeed);
        return makeMarker(FinalMatchByte, pb.createAssign("dot", pb.createAnd(nextPos, dot)));
    }
    else if (Diff * diff = dyn_cast<Diff>(re)) {
        return process(diff, marker, pb);
    }
    else if (Intersect * ix = dyn_cast<Intersect>(re)) {
        return process(ix, marker, pb);
    }
    else if (isa<Start>(re)) {
        MarkerType m = AdvanceMarker(marker, InitialPostPositionByte, pb);
        if (UNICODE_LINE_BREAK) {
            PabloAST * line_end = mCG.createOr(mUnicodeLineBreak, mCRLF);
            PabloAST * sol = pb.createNot(pb.createOr(pb.createAdvance(pb.createNot(line_end), 1), mCRLF));
            return makeMarker(InitialPostPositionByte, pb.createAssign("sol", pb.createAnd(markerVar(m), sol)));
        }
        else {
            PabloAST * sol = pb.createNot(pb.createAdvance(pb.createNot(mLineFeed), 1));
            return makeMarker(InitialPostPositionByte, pb.createAssign("sol", pb.createAnd(markerVar(m), sol)));
        }
    }
    else if (isa<End>(re)) {
        if (UNICODE_LINE_BREAK) {
            PabloAST * nextPos = nextUnicodePosition(marker, pb);
            return makeMarker(FinalPostPositionByte, pb.createAssign("end", pb.createAnd(nextPos, mUnicodeLineBreak)));
        }
        PabloAST * nextPos = markerVar(AdvanceMarker(marker, InitialPostPositionByte, pb));  // For LF match
        return makeMarker(InitialPostPositionByte, pb.createAssign("eol", pb.createAnd(nextPos, mLineFeed)));
    }
    return marker;
}

MarkerType RE_Compiler::process(Name * name, MarkerType marker, PabloBlock & pb) {
    MarkerType nextPos;
    if (markerPos(marker) == FinalPostPositionByte) nextPos = marker;
    else if (name->getType() == Name::Type::Byte) {
        nextPos = AdvanceMarker(marker, InitialPostPositionByte, pb);
    }
    else {
        nextPos = AdvanceMarker(marker, FinalPostPositionByte, pb);
    }
    return makeMarker(FinalMatchByte, pb.createAssign("m", pb.createAnd(markerVar(nextPos), character_class_strm(name, pb))));
}

MarkerType RE_Compiler::process(Seq * seq, MarkerType marker, PabloBlock & pb) {
    for (RE * re : *seq) {
        marker = process(re, marker, pb);
    }
    return marker;
}

MarkerType RE_Compiler::process(Alt * alt, MarkerType marker, PabloBlock & pb) {
    std::vector<PabloAST *>  accum = {pb.createZeroes(), pb.createZeroes(), pb.createZeroes()};
    MarkerType const base = marker;
    // The following may be useful to force a common Advance rather than separate
    // Advances in each alternative.
    // MarkerType const base = makeMarker(InitialPostPositionByte, postPositionVar(marker, pb), pb);
    for (RE * re : *alt) {
        MarkerType rslt = process(re, base, pb);
        MarkerPosition p = markerPos(rslt);
        accum[p] = pb.createOr(accum[p], markerVar(rslt));
    }
    if (isa<Zeroes>(accum[InitialPostPositionByte]) && isa<Zeroes>(accum[FinalPostPositionByte])) {
        return makeMarker(FinalMatchByte, pb.createAssign("alt", accum[FinalMatchByte]));
    }
    PabloAST * combine = pb.createOr(accum[InitialPostPositionByte], pb.createAdvance(accum[FinalMatchByte], 1));
    if (isa<Zeroes>(accum[FinalPostPositionByte])) {
        return makeMarker(InitialPostPositionByte, pb.createAssign("alt", combine));
    }
    combine = pb.createOr(pb.createScanThru(pb.createAnd(mInitial, combine), mNonFinal), accum[FinalPostPositionByte]);
    return makeMarker(FinalPostPositionByte, pb.createAssign("alt", combine));
}

MarkerType RE_Compiler::process(Assertion * a, MarkerType marker, PabloBlock & pb) {
    RE * asserted = a->getAsserted();
    if (a->getKind() == Assertion::Kind::Lookbehind) {
        MarkerType m = marker;
        MarkerType lookback = compile(asserted, pb);
        AlignMarkers(m, lookback, pb);
        Assign * lb = markerVar(lookback);
        if (a->getSense() == Assertion::Sense::Negative) {
            lb = pb.createAssign("not", pb.createNot(lb));
        }
        return makeMarker(markerPos(m), pb.createAssign("lookback", pb.createAnd(markerVar(marker), lb)));
    }
    else if (isUnicodeUnitLength(asserted)) {
        MarkerType lookahead = compile(asserted, pb);
        assert(markerPos(lookahead) == FinalMatchByte);
        Assign * la = markerVar(lookahead);
        if (a->getSense() == Assertion::Sense::Negative) {
            la = pb.createAssign("not", pb.createNot(la));
        }
        MarkerType fbyte = AdvanceMarker(marker, FinalPostPositionByte, pb);
        return makeMarker(FinalPostPositionByte, pb.createAssign("lookahead", pb.createAnd(markerVar(fbyte), la)));
    }
    else {
        throw std::runtime_error("Unsupported lookahead assertion.");
    }
}

MarkerType RE_Compiler::process(Diff * diff, MarkerType marker, PabloBlock & pb) {
    RE * lh = diff->getLH();
    RE * rh = diff->getRH();
    if (isUnicodeUnitLength(lh) && isUnicodeUnitLength(rh)) {
        MarkerType t1 = process(lh, marker, pb);
        MarkerType t2 = process(rh, marker, pb);
        AlignMarkers(t1, t2, pb);
        return makeMarker(markerPos(t1), pb.createAssign("diff", pb.createAnd(markerVar(t1), pb.createNot(markerVar(t2)))));
    }
    throw std::runtime_error("Unsupported Diff operands: " + Printer_RE::PrintRE(diff));
}

MarkerType RE_Compiler::process(Intersect * x, MarkerType marker, PabloBlock & pb) {
    RE * lh = x->getLH();
    RE * rh = x->getRH();
    if (isUnicodeUnitLength(lh) && isUnicodeUnitLength(rh)) {
        MarkerType t1 = process(lh, marker, pb);
        MarkerType t2 = process(rh, marker, pb);
        AlignMarkers(t1, t2, pb);
        return makeMarker(markerPos(t1), pb.createAssign("intersect", pb.createAnd(markerVar(t1), markerVar(t2))));
    }
    throw std::runtime_error("Unsupported Intersect operands: " + Printer_RE::PrintRE(x));
}

MarkerType RE_Compiler::process(Rep * rep, MarkerType marker, PabloBlock & pb) {
    int lb = rep->getLB();
    int ub = rep->getUB();
    if (lb > 0) {
        marker = processLowerBound(rep->getRE(), lb, marker, pb);
    }
    if (ub == Rep::UNBOUNDED_REP) {
        return processUnboundedRep(rep->getRE(), marker, pb);
    }
    else { // if (rep->getUB() != Rep::UNBOUNDED_REP)
        return processBoundedRep(rep->getRE(), ub - lb, marker, pb);
    }
}

/*
   Given a stream |repeated| marking positions immediately after matches to an item
   of length |repeated_lgth|, compute a stream marking positions immediately after
   |repeat_count| consecutive occurrences of such items.
*/

inline Assign * RE_Compiler::consecutive(Assign * repeated, int repeated_lgth, int repeat_count, pablo::PabloBlock & pb) {
        int i = repeated_lgth;
        int total_lgth = repeat_count * repeated_lgth;
        Assign * consecutive_i = repeated;
        while (i * 2 < total_lgth) {
            PabloAST * v = consecutive_i;
            consecutive_i = pb.createAssign("consecutive", pb.createAnd(v, pb.createAdvance(v, i)));
            i *= 2;
        }        
        if (i < total_lgth) {
            PabloAST * v = consecutive_i;
            consecutive_i = pb.createAssign("consecutive", pb.createAnd(v, pb.createAdvance(v, total_lgth - i)));
        }
        return consecutive_i;
}

MarkerType RE_Compiler::processLowerBound(RE * repeated, int lb, MarkerType marker, PabloBlock & pb) {
    if (isByteLength(repeated)) {
        PabloAST * cc = markerVar(compile(repeated, pb));
        Assign * cc_lb = consecutive(pb.createAssign("repeated", pb.createAdvance(cc,1)), 1, lb, pb);
        PabloAST * marker_fwd = pb.createAdvance(markerVar(marker), markerPos(marker) == FinalMatchByte ? lb + 1 : lb);
        return makeMarker(InitialPostPositionByte, pb.createAssign("lowerbound", pb.createAnd(marker_fwd, cc_lb)));
    }
    // Fall through to general case.
    while (lb-- != 0) {
        marker = process(repeated, marker, pb);
    }
    return marker;
}

MarkerType RE_Compiler::processBoundedRep(RE * repeated, int ub, MarkerType marker, PabloBlock & pb) {
    if (isByteLength(repeated)) {
        // log2 upper bound for fixed length (=1) class
        // Mask out any positions that are more than ub positions from a current match.
        // Use matchstar, then apply filter.
        Assign * nonMatch = pb.createAssign("nonmatch", pb.createNot(markerVar(AdvanceMarker(marker, InitialPostPositionByte, pb))));
        PabloAST * upperLimitMask = pb.createNot(consecutive(nonMatch, 1, ub + 1, pb));
        PabloAST * cursor = markerVar(AdvanceMarker(marker, InitialPostPositionByte, pb));
        PabloAST * rep_class_var = markerVar(compile(repeated, pb));
        return makeMarker(InitialPostPositionByte, pb.createAssign("bounded", pb.createAnd(pb.createMatchStar(cursor, rep_class_var), upperLimitMask)));
    }
    // Fall through to general case.
    while (ub-- != 0) {
        MarkerType a = process(repeated, marker, pb);
        MarkerType m = marker;
        AlignMarkers(a, m, pb);
        marker = makeMarker(markerPos(a), pb.createAssign("m", pb.createOr(markerVar(a), markerVar(m))));
    }
    return marker;
}

MarkerType RE_Compiler::processUnboundedRep(RE * repeated, MarkerType marker, PabloBlock & pb) {
    // always use PostPosition markers for unbounded repetition.
    PabloAST * base = markerVar(AdvanceMarker(marker, InitialPostPositionByte, pb));
    
    if (isByteLength(repeated)) {
        PabloAST * cc = markerVar(compile(repeated, pb));  
        return makeMarker(InitialPostPositionByte, pb.createAssign("unbounded", pb.createMatchStar(base, cc)));
    }
    else if (isUnicodeUnitLength(repeated)) {
        PabloAST * cc = markerVar(compile(repeated, pb));
        return makeMarker(InitialPostPositionByte, pb.createAssign("unbounded", pb.createAnd(pb.createMatchStar(base, pb.createOr(mNonFinal, cc)), mInitial)));
    }
    else {
        Assign * whileTest = pb.createAssign("test", base);
        Assign * whileAccum = pb.createAssign("accum", base);

        PabloBlock & wb = PabloBlock::Create(pb);

        PabloAST * loopComputation = markerVar(AdvanceMarker(process(repeated, makeMarker(InitialPostPositionByte, whileTest), wb), InitialPostPositionByte, wb));
        Next * nextWhileTest = wb.createNext(whileTest, wb.createAnd(loopComputation, wb.createNot(whileAccum)));
        wb.createNext(whileAccum, wb.createOr(loopComputation, whileAccum));

        pb.createWhile(nextWhileTest, wb);

        return makeMarker(InitialPostPositionByte, pb.createAssign("unbounded", whileAccum));
    }    
} // end of namespace re
}
