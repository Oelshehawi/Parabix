/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "ztf-logic.h"
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <pablo/bixnum/bixnum.h>
#include <pablo/pe_zeroes.h>
#include <pablo/builder.hpp>
#include <pablo/pe_ones.h>
#include <re/ucd/ucd_compiler.hpp>
#include <re/unicode/re_name_resolve.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>

using namespace pablo;
using namespace kernel;
using namespace llvm;

std::string LengthGroupAnnotation(std::vector<LengthGroup> lengthGroups) {
    std::string s;
    for (unsigned i = 0; i < lengthGroups.size(); i++) {
        s += ":" + std::to_string(lengthGroups[i].lo) + "_" + std::to_string(lengthGroups[i].hi);
    }
    return s;
}

WordMarkKernel::WordMarkKernel(const std::unique_ptr<KernelBuilder> & kb, StreamSet * BasisBits, StreamSet * WordMarks)
: PabloKernel(kb, "WordMarks", {Binding{"source", BasisBits}}, {Binding{"WordMarks", WordMarks}}) { }

void WordMarkKernel::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    cc::Parabix_CC_Compiler_Builder ccc(getEntryScope(), getInputStreamSet("source"));
    UCD::UCDCompiler ucdCompiler(ccc);
    re::Name * word = re::makeName("word", re::Name::Type::UnicodeProperty);
    word = llvm::cast<re::Name>(re::resolveUnicodeNames(word));
    UCD::UCDCompiler::NameMap nameMap;
    nameMap.emplace(word, nullptr);
    ucdCompiler.generateWithDefaultIfHierarchy(nameMap, pb);
    auto f = nameMap.find(word);
    if (f == nameMap.end()) llvm::report_fatal_error("Cannot find word property");
    PabloAST * wordChar = f->second;
    pb.createAssign(pb.createExtract(getOutputStreamVar("WordMarks"), pb.getInteger(0)), wordChar);
}

void ByteRun::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    PabloAST * excluded = getInputStreamSet("excluded")[0];

    PabloAST * mismatches = pb.createZeroes();
    for (unsigned i = 0; i < 8; i++) {
        mismatches = pb.createOr(mismatches,
                                 pb.createXor(basis[i], pb.createAdvance(basis[i], 1)),
                                 "mismatches_to_bit" + std::to_string(i));
    }
    PabloAST * matchesprior = pb.createInFile(pb.createNot(mismatches), "matchesprior");
    matchesprior = pb.createAnd(matchesprior, pb.createNot(excluded));
    pb.createAssign(pb.createExtract(getOutputStreamVar("runMask"), pb.getInteger(0)), matchesprior);
}

ZTF_DecodeLengths::ZTF_DecodeLengths(const std::unique_ptr<KernelBuilder> & b,
                                     StreamSet * basisBits,
                                     std::vector<LengthGroup> lengthGroups,
                                     std::vector<StreamSet *> & groupStreams)
: PabloKernel(b, "ZTF_DecodeLengths" + LengthGroupAnnotation(lengthGroups),
              {Binding{"basisBits", basisBits}}, {}), mLengthGroups(lengthGroups) {
    for (unsigned i = 0; i < lengthGroups.size(); i++) {
        unsigned lo = lengthGroups[i].lo;
        unsigned hi = lengthGroups[i].hi;
        std::string groupName = "lengthGroup" + std::to_string(lo) +  "_" + std::to_string(hi);
        mOutputStreamSets.emplace_back(groupName, groupStreams[i]);
    }
}

void ZTF_DecodeLengths::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basisBits");
    std::vector<PabloAST *> groupStreams(mLengthGroups.size());
    cc::Parabix_CC_Compiler_Builder ccc(getEntryScope(), basis);
    PabloAST * ASCII = ccc.compileCC(re::makeCC(0x0, 0x7F));
    unsigned const offset = 2;
    for (unsigned i = 0; i < mLengthGroups.size(); i++) {
        unsigned lo = mLengthGroups[i].lo;
        unsigned hi = mLengthGroups[i].hi;
        PabloAST * prefixCC = ccc.compileCC(re::makeCC(0xC0 + 2*(lo-offset), 0xC0 + 2*(hi-offset) + 1));
        std::string groupName = "lengthGroup" + std::to_string(lo) +  "_" + std::to_string(hi);
        groupStreams[i] = pb.createAnd(pb.createAdvance(prefixCC, 1), ASCII, groupName);
        pb.createAssign(pb.createExtract(getOutputStreamVar(groupName), pb.getInteger(0)), groupStreams[i]);
    }
}

void ZTF_Symbols::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basisBits");
    cc::Parabix_CC_Compiler_Builder ccc(getEntryScope(), basis);
    pablo::PabloAST * wordChar = getInputStreamSet("wordChar")[0];
    // Find start bytes of word characters.
    PabloAST * ASCII = ccc.compileCC(re::makeCC(0x0, 0x7F));
    PabloAST * prefix2 = ccc.compileCC(re::makeCC(0xC2, 0xDF));
    PabloAST * prefix3 = ccc.compileCC(re::makeCC(0xE0, 0xEF));
    PabloAST * prefix4 = ccc.compileCC(re::makeCC(0xF0, 0xF4));
    PabloAST * wc1 = pb.createAnd(ASCII, wordChar);
    wc1 = pb.createOr(wc1, pb.createAnd(prefix2, pb.createLookahead(wordChar, 1)));
    wc1 = pb.createOr(wc1, pb.createAnd(prefix3, pb.createLookahead(wordChar, 2)));
    wc1 = pb.createOr(wc1, pb.createAnd(prefix4, pb.createLookahead(wordChar, 3)));
    //
    // ZTF Code symbols
    PabloAST * ZTF_sym = pb.createAnd(pb.createAdvance(prefix2, 1), ASCII);
    PabloAST * ZTF_prefix = pb.createAnd(prefix2, pb.createNot(pb.createLookahead(basis[7], 1)));
    // Filter out ZTF code symbols from word characters.
    wc1 = pb.createAnd(wc1, pb.createNot(ZTF_sym));
    //
    PabloAST * wordStart = pb.createAnd(pb.createNot(pb.createAdvance(wordChar, 1)), wc1, "wordStart");
    // Nulls, Linefeeds and ZTF_symbols are also treated as symbol starts.
    PabloAST * LF = ccc.compileCC(re::makeByte(0x0A));
    PabloAST * Null = ccc.compileCC(re::makeByte(0x0));
    PabloAST * symStart = pb.createOr3(wordStart, ZTF_prefix, pb.createOr(LF, Null));
    // The next character after a ZTF symbol or a line feed also starts a new symbol.
    symStart = pb.createOr(symStart, pb.createAdvance(pb.createOr(ZTF_sym, LF), 1), "symStart");
    //
    // runs are the bytes after a start symbol until the next symStart byte.
    pablo::PabloAST * runs = pb.createInFile(pb.createNot(symStart));
    pb.createAssign(pb.createExtract(getOutputStreamVar("symbolRuns"), pb.getInteger(0)), runs);
}

ZTF_SymbolEncoder::ZTF_SymbolEncoder(const std::unique_ptr<kernel::KernelBuilder> & b,
                      std::vector<LengthGroup> & lenGroups,
                      StreamSet * const basis,
                      StreamSet * bixHash,
                      StreamSet * extractionMask,
                      StreamSet * runIdx,
                      StreamSet * encoded)
    : pablo::PabloKernel(b, "ZTF_SymbolEncoder" + LengthGroupAnnotation(lenGroups),
                         {Binding{"basis", basis},
                             Binding{"bixHash", bixHash, FixedRate(), LookAhead(1)},
                             Binding{"extractionMask", extractionMask},
                             Binding{"runIdx", runIdx}},
                         {Binding{"encoded", encoded}}),
    mLenGroups(lenGroups) {}


void ZTF_SymbolEncoder::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    std::vector<PabloAST *> bixHash = getInputStreamSet("bixHash");
    PabloAST * extractionMask = getInputStreamSet("extractionMask")[0];
    BixNum runIdx = getInputStreamSet("runIdx");
    std::vector<PabloAST *> encoded(8);
    Var * encodedVar = getOutputStreamVar("encoded");
    //  ZTF symbol prefixes are inserted at the position of the first 1 bit
    //  following a series of 0 bits in the extraction mask.
    PabloAST * ZTF_prefix = pb.createAnd(extractionMask, pb.createAdvance(pb.createNot(extractionMask), 1));
    PabloAST * ZTF_suffix = pb.createAdvance(ZTF_prefix, 1);
    //
    // ZTF_suffixes consist of a high 0 bit and the low 7 bits of the hash value.
    for (unsigned i = 0; i < 7; i++)  {
        encoded[i] = pb.createSel(ZTF_suffix, bixHash[i], basis[i]);
    }
    encoded[7] = pb.createAnd(basis[7], pb.createNot(ZTF_suffix));
    //
    // While the low 7 hash bits are at the ZTF_suffix position, the others
    // are needed at the ZTF_prefix position, requiring lookahead.
    BixNum highHash(bixHash.size() - 7);
    for (unsigned i = 0; i < bixHash.size() - 7; i++) {
        highHash[i] = pb.createLookahead(bixHash[i + 7], 1, "highHash");
    }
    //
    // ZTF prefixes depend on the length group, but always have the high 2 bits set in each case.
    encoded[7] = pb.createOr(ZTF_prefix, encoded[7]);
    encoded[6] = pb.createOr(ZTF_prefix, encoded[6]);
    //
    // Determine the symbol length at the ZTF_prefix position.
    // The run index numbers from the second position starting with 0,
    // so the length is 2 + the runIndex value at the end of the symbol.
    // At the ZTF_prefix position, the length is the runIndex plus 3.
    BixNum symLength = bnc.AddFull(runIdx, 3);

    // The encoding scheme starts at 0xC2, with the low 6 bit value of 2.
    BixNum base = bnc.ZeroExtend(bnc.Create(2), 6);
    for (unsigned i = 0; i < mLenGroups.size(); i++) {
        unsigned extra_hash_bits = mLenGroups[i].hashBits - 7;  //low 7 bits in suffix
        unsigned multiplier = 1<<extra_hash_bits;
        PabloAST * inGroup = pb.createAnd(bnc.UGE(symLength, mLenGroups[i].lo), bnc.ULE(symLength, mLenGroups[i].hi), "inGroup_" + std::to_string(i));
        inGroup = pb.createAnd(inGroup, ZTF_prefix);
        BixNum lenOffset = bnc.SubModular(symLength, mLenGroups[i].lo);
        BixNum lenBase = bnc.AddModular(base, bnc.MulModular(lenOffset, multiplier));
        BixNum value = bnc.AddModular(lenBase, bnc.Truncate(highHash, extra_hash_bits));
        for (unsigned j = 0; j < 6; j++) {
            encoded[j] = pb.createSel(inGroup, value[j], encoded[j], "encoded[" + std::to_string(j) + "]");
        }
        base = bnc.AddModular(base, multiplier * (mLenGroups[i].hi - mLenGroups[i].lo + 1));
    }
    for (unsigned i = 0; i < 8; i++) {
        pb.createAssign(pb.createExtract(encodedVar, pb.getInteger(i)), encoded[i]);
    }
}


void ZTF_ExpansionDecoder::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    std::unique_ptr<cc::CC_Compiler> ccc;
    ccc = make_unique<cc::Parabix_CC_Compiler_Builder>(getEntryScope(), basis);
    PabloAST * ASCII_lookahead = pb.createNot(pb.createLookahead(basis[7], 1));
    PabloAST * const ZTF_Sym = pb.createAnd(ccc->compileCC(re::makeByte(0xC2, 0xDF)), ASCII_lookahead, "ZTF_sym");
    Var * lengthVar = getOutputStreamVar("insertBixNum");
    for (unsigned i = 0; i < 4; i++) {
        pb.createAssign(pb.createExtract(lengthVar, pb.getInteger(i)), pb.createAnd(ZTF_Sym, basis[i+1]));
    }
}

LengthSorter::LengthSorter(const std::unique_ptr<kernel::KernelBuilder> & b,
                           StreamSet * symbolRun, StreamSet * const lengthBixNum,
                           StreamSet * overflow,
                           std::vector<LengthGroup> lengthGroups,
                           std::vector<StreamSet *> & groupStreams)
: PabloKernel(b, "LengthSorter" + std::to_string(lengthBixNum->getNumElements()) + LengthGroupAnnotation(lengthGroups),
              {Binding{"symbolRun", symbolRun, FixedRate(), LookAhead(1)},
                  Binding{"lengthBixNum", lengthBixNum},
                  Binding{"overflow", overflow}},
              {}), mLengthGroups(lengthGroups) {
    for (unsigned i = 0; i < lengthGroups.size(); i++) {
        unsigned lo = lengthGroups[i].lo;
        unsigned hi = lengthGroups[i].hi;
        std::string groupName = "lengthGroup" + std::to_string(lo) +  "_" + std::to_string(hi);
        mOutputStreamSets.emplace_back(groupName, groupStreams[i]);
    }
}

void LengthSorter::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    PabloAST * run = getInputStreamSet("symbolRun")[0];
    std::vector<PabloAST *> lengthBixNum = getInputStreamSet("lengthBixNum");
    PabloAST * overflow = getInputStreamSet("overflow")[0];
    PabloAST * runFinal = pb.createAnd(run, pb.createNot(pb.createLookahead(run, 1)));
    runFinal = pb.createAnd(runFinal, pb.createNot(overflow));
    // Run index codes count from 0 on the 2nd byte of a symbol.
    // So the length is 2 more than the bixnum.
    const unsigned offset = 2;
    std::vector<PabloAST *> groupStreams(mLengthGroups.size());
    for (unsigned i = 0; i < mLengthGroups.size(); i++) {
        unsigned lo = mLengthGroups[i].lo;
        unsigned hi = mLengthGroups[i].hi;
        std::string groupName = "lengthGroup" + std::to_string(lo) +  "_" + std::to_string(hi);
        groupStreams[i] = pb.createAnd3(bnc.UGE(lengthBixNum, lo - offset), bnc.ULE(lengthBixNum, hi - offset), runFinal, groupName);
        pb.createAssign(pb.createExtract(getOutputStreamVar(groupName), pb.getInteger(0)), groupStreams[i]);
    }
}
