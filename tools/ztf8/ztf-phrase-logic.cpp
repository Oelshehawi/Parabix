/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "ztf-phrase-logic.h"
#include "ztf-phrase-scan.h"

#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <pablo/bixnum/bixnum.h>
#include <pablo/pablo_intrinsic.h>
#include <pablo/pe_zeroes.h>
#include <pablo/builder.hpp>
#include <pablo/pe_ones.h>
#include <pablo/pe_debugprint.h>
#include <re/ucd/ucd_compiler.hpp>
#include <re/unicode/resolve_properties.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <llvm/Support/raw_ostream.h>
#include <sstream>
#include <kernel/io/stdout_kernel.h>                 // for StdOutKernel_
#include <kernel/util/debug_display.h>
#include <grep/grep_kernel.h>
#include <kernel/streamutils/deletion.h>
#include <kernel/streamutils/streams_merge.h>
#include <kernel/util/linebreak_kernel.h>

using namespace pablo;
using namespace kernel;
using namespace llvm;

UpdateNextHashMarks::UpdateNextHashMarks(BuilderRef kb,
                    EncodingInfo & encodingScheme,
                    StreamSet * extractionMask,
                    StreamSet * hashMarksToUpdate,
                    unsigned groupNo,
                    StreamSet * hashMarksUpdated)
: PabloKernel(kb, "UpdateNextHashMarks"+std::to_string(groupNo),
            {Binding{"extractionMask", extractionMask},
             Binding{"hashMarksToUpdate", hashMarksToUpdate}},
            {Binding{"hashMarksUpdated", hashMarksUpdated}}), mEncodingScheme(encodingScheme), mGroupNo(groupNo) { }

void UpdateNextHashMarks::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    PabloAST * extractionMask = getInputStreamSet("extractionMask")[0]; // marks all the compressible byte positions with 0
    PabloAST * hashMarksToUpdate = getInputStreamSet("hashMarksToUpdate")[0];
    PabloAST * result = hashMarksToUpdate;

    // eliminate any (k-1)-sym phrases in the region of compressed bytes
    result = pb.createAnd(extractionMask, result);
    // eliminate any direct overlapping hashMarks between k-sym and (k-1)-sym phrases
    // every compressedMark in compressedMarks has 2/3/4 byte codewords written at the last 2/3/4 bytes of the phrase
    // Advance compressedMarks by 2,3,4 pos and check if any hashMarksToUpdate marked in the codeword position
    unsigned advPos = 0;
    if (mEncodingScheme.byLength.size() == 5) {
        if (mGroupNo < 3) {
        advPos = 2;
        }
        else if (mGroupNo == 3) {
            advPos = 3;
        }
        else { //mGroupNo = 4
            advPos = 4;
        }
    }
    if (mEncodingScheme.byLength.size() == 4) {
        if (mGroupNo < 2) {
            advPos = 2;
        }
        else if (mGroupNo == 2) {
            advPos = 3;
        }
        else { //mGroupNo = 4
            advPos = 4;
        }
    }
    extractionMask = pb.createAdvance(extractionMask, advPos); // min codeword sequence length
    result = pb.createAnd(result, extractionMask, "result");
    //pb.createDebugPrint(result, "result");
    /*
        1111............11 => extractionMask
        111111............ => adv(extractionMask,2)
        ....111111111111.. => compressedMarks
        ...1.....1.......1 => hashMarksToUpdate
        ...1.............1 => result
        ...1.............. => codewordPositions
    */
    // figure out what hashmarks need to be eliminated and XOR with received hashmarks
    pb.createAssign(pb.createExtract(getOutputStreamVar("hashMarksUpdated"), pb.getInteger(0)), result);
}

InverseStream::InverseStream(BuilderRef kb,
                StreamSet * inStream,
                StreamSet * selected)
: PabloKernel(kb, "InverseStream_",
            {Binding{"inStream", inStream, FixedRate(), LookAhead(1)}},
            {Binding{"selected", selected}}) { }

void InverseStream::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    PabloAST * toInverse = getInputStreamSet("inStream")[0];
    PabloAST * result = pb.createAnd(toInverse, pb.createNot(pb.createLookahead(toInverse, 1)));
    pb.createAssign(pb.createExtract(getOutputStreamVar("selected"), pb.getInteger(0)), result);

}

LengthSelector::LengthSelector(BuilderRef b,
                           EncodingInfo & encodingScheme,
                           StreamSet * groupLenBixnum,
                           StreamSet * hashMarks,
                           StreamSet * selectedHashMarksPos,
                           unsigned offset)
: PabloKernel(b, "LengthSelector" + encodingScheme.uniqueSuffix() + std::to_string(offset),
              {Binding{"hashMarks", hashMarks},
               Binding{"groupLenBixnum", groupLenBixnum}},
              {Binding{"selectedHashMarksPos", selectedHashMarksPos}}), mEncodingScheme(encodingScheme), mOffset(offset) { }

void LengthSelector::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    PabloAST * hashMarks = getInputStreamSet("hashMarks")[0];
    Var * selectedHashMarksPosStreamVar = getOutputStreamVar("selectedHashMarksPos");
    std::vector<PabloAST *> groupLenBixnum = getInputStreamSet("groupLenBixnum");
    unsigned offset = mOffset;
    unsigned minSymLenOffset = 6;
    if (mEncodingScheme.byLength.size() == 4) {
        minSymLenOffset = 1;
    }
    unsigned lo = mEncodingScheme.minSymbolLength()+minSymLenOffset; // min k-sym phrase length = 9 bytes
    unsigned hi = mEncodingScheme.maxSymbolLength();
    unsigned groupSize = hi - lo + 1;
    std::vector<PabloAST *> selectedLengthMarks(groupSize);
    for (unsigned i = lo; i <= hi; i++) {
        PabloAST * lenBixnum = bnc.EQ(groupLenBixnum, i - offset);
        pb.createAssign(pb.createExtract(selectedHashMarksPosStreamVar, pb.getInteger(i-lo)), pb.createAnd(hashMarks, lenBixnum));
    }
}

LengthBasedHashMarkSelection::LengthBasedHashMarkSelection(BuilderRef b,
                           EncodingInfo & encodingScheme,
                           unsigned offset,
                           unsigned currLen,
                           StreamSet * lengthwiseHashMarks, // 24 bitstreams
                           StreamSet * selectedHashMarks) // output
: PabloKernel(b, "LengthBasedHashMarkSelection" + encodingScheme.uniqueSuffix() + std::to_string(offset),
              {Binding{"lengthwiseHashMarks", lengthwiseHashMarks, FixedRate(), LookAhead(32)}},
              {Binding{"selectedHashMarks", selectedHashMarks}}), mEncodingScheme(encodingScheme), mOffset(offset), mCurrLen(currLen) { }

void LengthBasedHashMarkSelection::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    Var * selectedEndStreamVar = getOutputStreamVar("selectedHashMarks");
    std::vector<PabloAST *> lengthwiseHashMarks = getInputStreamSet("lengthwiseHashMarks");
    for (unsigned currLen = mEncodingScheme.maxSymbolLength(); currLen >= mOffset; currLen--) {
        unsigned idx = currLen-mOffset;
/* Step 1: Check for overlap between phrases of same length:
    Adv every lengthwiseHashMarks pos by curLen-1 positions (one bit at a time).
    If any of the phrases are being overlapped by preceeding phrase of same length, eliminate them.
    Do this atleast twice - if there are consecutive phrases overlapped by one another,
    select the max number of non-overlapping phrases.
*/
        PabloAST * idxHashEndMarks = lengthwiseHashMarks[idx]; // hashmarks of length idx+9
        PabloAST * toAdvanceEnd = idxHashEndMarks;
        PabloAST * overlapsWithPrevEndMark = pb.createZeroes();
        // step 1.1
        for (unsigned i = 1; i < currLen; i++) {
            toAdvanceEnd = pb.createAdvance(toAdvanceEnd, 1);
            overlapsWithPrevEndMark = pb.createOr(overlapsWithPrevEndMark, pb.createAnd(toAdvanceEnd, idxHashEndMarks));
        }
        lengthwiseHashMarks[idx] = pb.createXor(lengthwiseHashMarks[idx], overlapsWithPrevEndMark);

        // pb.createDebugPrint(selectedInit, "selectedInit-1");
        // step 1.2 -> ///////////////////////////////////////////////////////////////////////////////////////////// uncomment after full testing
        // toAdvanceStart = selectedInit;
        // overlapsWithPrevEndMark = pb.createZeroes();
        // for (unsigned i = 1; i < currLen; i++) {
        //     toAdvanceStart = pb.createAdvance(toAdvanceStart, 1);
        //     overlapsWithPrevEndMark = pb.createOr(overlapsWithPrevEndMark, pb.createAnd(toAdvanceStart, idxHashStartMarks));
        // }
        // selectedInit = pb.createOr(selectedInit, pb.createXor(idxHashStartMarks, overlapsWithPrevEndMark));
        // pb.createDebugPrint(selectedInit, "selectedInit-2");
        // step 2
        for (unsigned i = idx+1; i < lengthwiseHashMarks.size(); i++) {
            PabloAST * lenIEndmarks = lengthwiseHashMarks[i];
            PabloAST * preceededByLongerPhraseEndMarks = pb.createZeroes();
            // check if any of the current selected phrases (of length Eg: 16) are preceeded by any longer length phrases (> 16)
            // already marked for compression; Eliminate such phrases from current selected group
            for (unsigned j = 1; j < currLen; j++) {
                lenIEndmarks = pb.createAdvance(lenIEndmarks, 1);
                preceededByLongerPhraseEndMarks = pb.createOr(preceededByLongerPhraseEndMarks, pb.createAnd(lenIEndmarks, lengthwiseHashMarks[idx]));
            } 
            lengthwiseHashMarks[idx] = pb.createXor(lengthwiseHashMarks[idx], preceededByLongerPhraseEndMarks);
        }
    }
    for (unsigned i = 0; i < lengthwiseHashMarks.size(); i++) {
        pb.createAssign(pb.createExtract(selectedEndStreamVar, pb.getInteger(i)), lengthwiseHashMarks[i]);
    }
}


OverlappingLookaheadMarkSelect::OverlappingLookaheadMarkSelect(BuilderRef b,
                           unsigned currLen,
                           unsigned offset,
                           StreamSet * lengthwiseHashMarks,
                           StreamSet * lengthwiseHashMarksUpdates,
                           StreamSet * selectedHashMarks)
: PabloKernel(b, "OverlappingLookaheadMarkSelect" + std::to_string(currLen) +"_"+ std::to_string(offset),
              {Binding{"lengthwiseHashMarks", lengthwiseHashMarks, FixedRate(), LookAhead(32)}},
              {Binding{"lengthwiseHashMarksUpdates", lengthwiseHashMarksUpdates},
               Binding{"selectedHashMarks", selectedHashMarks}}), mCurrLen(currLen), mOffset(offset) { }

void OverlappingLookaheadMarkSelect::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    Var * lengthwiseHashMarksUpdatesVar = getOutputStreamVar("lengthwiseHashMarksUpdates");
    Var * selectedHashMarksVar = getOutputStreamVar("selectedHashMarks");
    std::vector<PabloAST *> lengthwiseHashMarks = getInputStreamSet("lengthwiseHashMarks");
    // step 3 - eliminates the longer phrase hashMark instead of shorter phrase hashMark
    unsigned idx = mCurrLen-mOffset;
    PabloAST * selectedFinalEndMarks = lengthwiseHashMarks[idx];
    // pb.createDebugPrint(selectedFinalEndMarks, "selectedFinalEndMarks");
    // PabloAST * selectedPhraseSpan = pb.createIntrinsicCall(pablo::Intrinsic::SpanUpTo, {lenSortedHashMarkStarts[i], lengthwiseHashMarks[i]});
    // selectedPhraseSpan = pb.createOr(selectedPhraseSpan, lengthwiseHashMarks[i]);
    PabloAST * toUpdateEndMarks = pb.createZeroes();
    for (unsigned i = idx+1; i < lengthwiseHashMarks.size(); i++){
        for (unsigned j = 1; j < i+mOffset; j++) {
            toUpdateEndMarks = pb.createOr(toUpdateEndMarks, pb.createAnd(selectedFinalEndMarks, 
                                                                          pb.createLookahead(lengthwiseHashMarks[i], j)));
        }
    }
    lengthwiseHashMarks[idx] = pb.createXor(lengthwiseHashMarks[idx], toUpdateEndMarks);
    // pb.createDebugPrint(lengthwiseHashMarks[idx], "lengthwiseHashMarks["+std::to_string(idx)+"]");
    for (unsigned i = 0; i < lengthwiseHashMarks.size(); i++) {
        pb.createAssign(pb.createExtract(lengthwiseHashMarksUpdatesVar, pb.getInteger(i)), lengthwiseHashMarks[i]);
    }
    PabloAST * selected = pb.createZeroes();
    if (mCurrLen == mOffset) {
        for (unsigned i = 0; i < lengthwiseHashMarks.size(); i++) {
            selected = pb.createOr(selected, lengthwiseHashMarks[i]);
        }
    }
    pb.createAssign(pb.createExtract(selectedHashMarksVar, pb.getInteger(0)), selected);
}

BixnumHashMarks::BixnumHashMarks(BuilderRef kb,
                EncodingInfo & encodingScheme,
                StreamSet * phraseLenBixnum,
                StreamSet * hashMarks,
                unsigned toUpdateHashMarks,
                StreamSet * accumHashMarks)
: PabloKernel(kb, "BixnumHashMarks"+std::to_string(toUpdateHashMarks),
            {Binding{"phraseLenBixnum", phraseLenBixnum},
             Binding{"hashMarks", hashMarks}},
            {Binding{"accumHashMarks", accumHashMarks}}), mEncodingScheme(encodingScheme), mUpdateCount(toUpdateHashMarks) { }

void BixnumHashMarks::generatePabloMethod() {
    pablo::PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> phraseLenBixnum = getInputStreamSet("phraseLenBixnum");
    PabloAST * hashMarks = getInputStreamSet("hashMarks")[0];
    std::vector<PabloAST *> hashMarksUpdated;
    unsigned maxLength = mEncodingScheme.maxSymbolLength();
    unsigned toUpdateHashMarks = maxLength - mUpdateCount + 1;
    unsigned offset = 4;
    for (unsigned i = mUpdateCount; i <= maxLength; i++) {
        PabloAST * curHashMarksBixnum = pb.createZeroes();
        curHashMarksBixnum = pb.createOr(curHashMarksBixnum, pb.createAnd(hashMarks, phraseLenBixnum[i-offset]));
        hashMarksUpdated.push_back(curHashMarksBixnum);
    }
    for (unsigned i = 0; i < toUpdateHashMarks; i++) {
        pb.createAssign(pb.createExtract(getOutputStreamVar("accumHashMarks"), pb.getInteger(i)), hashMarksUpdated[i]);
    }
}

ZTF_PhraseDecodeLengths::ZTF_PhraseDecodeLengths(BuilderRef b,
                                                EncodingInfo & encodingScheme,
                                                unsigned numSym,
                                                StreamSet * basisBits,
                                                StreamSet * groupStreams,
                                                StreamSet * hashtableStreams,
                                                StreamSet * hashtableSpan,
                                                bool fullyDecompress) // TODO: don't need this flag too
: PabloKernel(b, "ZTF_PhraseDecodeLengths" + encodingScheme.uniqueSuffix(),
              {Binding{"basisBits", basisBits, FixedRate(), LookAhead(1)}},
              {Binding{"groupStreams", groupStreams},
               Binding{"hashtableStreams", hashtableStreams},
               Binding{"hashtableSpan", hashtableSpan, FixedRate()/*, Add1()*/}}), // span was fa001
    mEncodingScheme(encodingScheme), mNumSym(numSym), mFullyDecompress(fullyDecompress) { }

void ZTF_PhraseDecodeLengths::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    unsigned enc_len = mEncodingScheme.byLength.size();
    std::vector<PabloAST *> basis = getInputStreamSet("basisBits");
    std::vector<PabloAST *> groupStreams(mNumSym * enc_len);
    PabloAST * hashTableBoundaryCommon = pb.createAnd(pb.createAnd(basis[7], basis[6]), pb.createAnd(basis[5], basis[4])); //Fx
    PabloAST * hashTableBoundaryStartHi = pb.createAnd3(basis[3], basis[2], basis[1]); //xE, xF
    PabloAST * hashTableBoundaryEndHi = pb.createAnd(hashTableBoundaryStartHi, basis[0]); //xF
    hashTableBoundaryStartHi = pb.createXor(hashTableBoundaryStartHi, hashTableBoundaryEndHi); // xE

    PabloAST * hashTableBoundaryStart = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryStartHi);
    PabloAST * hashTableBoundaryEnd = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryEndHi);
    PabloAST * hashTableBoundaryStartFinal = pb.createAnd(hashTableBoundaryStart, pb.createAdvance(hashTableBoundaryStart, 1));
    PabloAST * hashTableBoundaryEndFinal = pb.createAnd(hashTableBoundaryEnd, pb.createAdvance(hashTableBoundaryEnd, 1));

    PabloAST * hashTableSpan = pb.createIntrinsicCall(pablo::Intrinsic::SpanUpTo, {hashTableBoundaryStartFinal, hashTableBoundaryEndFinal});
    // Valid 4-byte UTF-8 codeunits
    PabloAST * toEliminate = pb.createAnd(pb.createLookahead(basis[7], 1), pb.createOr(hashTableBoundaryStart, hashTableBoundaryEnd)); // hashTableBoundaryEnd is not a valid UTF-8 prefix
    hashTableSpan = pb.createOr3(hashTableSpan, hashTableBoundaryEndFinal, toEliminate);

    PabloAST * fileStart = pb.createNot(pb.createAdvance(pb.createOnes(), 1));
    PabloAST * EOFbit = pb.createAtEOF(pb.createAdvance(pb.createOnes(), 1));

    PabloAST * filterSpan = pb.createIntrinsicCall(pablo::Intrinsic::SpanUpTo, {fileStart, EOFbit});
    filterSpan = pb.createXor(filterSpan, hashTableSpan);

    PabloAST * hashtableBoundaries = pb.createOr(hashTableBoundaryStartFinal, hashTableBoundaryEndFinal);//, toEliminate);
    PabloAST * boundaryEndInvalidCodeword = pb.createAdvance(hashTableBoundaryEndFinal, 3);
    PabloAST * boundaryStartInvalidCodeword = pb.createAdvance(hashTableBoundaryStartFinal, 3);
    PabloAST * allInvalidBoundaryCodeword = pb.createNot(pb.createOr(boundaryEndInvalidCodeword, boundaryStartInvalidCodeword));
    PabloAST * ASCII = bnc.ULT(basis, 0x80);
    PabloAST * suffix_80_BF = pb.createAnd(bnc.UGE(basis, 0x80), bnc.ULE(basis, 0xBF));
    Var * groupStreamVar = getOutputStreamVar("groupStreams");
    Var * hashTableStreamVar = getOutputStreamVar("hashtableStreams");
    for (unsigned i = 0; i < enc_len; i++) {
        for (unsigned j = 0; j < mNumSym; j++) {
            unsigned idx = i + (j*enc_len);
            groupStreams[idx] = pb.createZeroes();
        }
        LengthGroupInfo groupInfo = mEncodingScheme.byLength[i];
        unsigned base = groupInfo.prefix_base;
        unsigned base_divided = base;
        if (i == 1) {
            base += 8;
        }
        unsigned next_base = 0;
        unsigned next_base_divided = 0;
        if(mEncodingScheme.byLength.size() == 5) {
            if (i < 2) {
                next_base = base + 8;
            }
            else {
                next_base = base + 16;
            }
        }
        if(mEncodingScheme.byLength.size() == 4) {
            if (i == 0) {
                next_base = base + 8;
            }
            else {
                next_base = base + 16;
            }
            if (i == 1) next_base_divided = base_divided + 8;
        }
        PabloAST * inGroup = pb.createAnd(bnc.UGE(basis, base), bnc.ULT(basis, next_base));
/*      curGroupStream =>
            0 -> C0-C7 00-7F
            1 -> C8-CF 00-7F
            2 -> D0-DF 00-7F
            3 -> E0-EF 00-7F 00-7F / EO-EF 00-7F 80-BF
            4 -> F0-FF 00-7F 00-7F 00-7F / F0-FF 00-7F 00-7F 80-BF
        updated curGroupStream =>
            0 -> C0-C7 00-7F
            1 -> C8-DF 00-7F
            2 -> E0-EF 00-7F 00-7F / EO-EF 00-7F 80-BF
            3 -> F0-FF 00-7F 00-7F 00-7F / F0-FF 00-7F 00-7F 80-BF
        encodingScheme1
            i = 0, 1, 2, 3, 4
            j = 0, 1
            idx = 0, 5, 1, 6, 2, 7, 3, 8, 4, 9
        encodingScheme2
            i = 0, 1, 2, 3
            j = 0, 1
            idx = 0, 4, 1, 5, 2, 6, 3, 7
*/
        PabloAST * curGroupStream = pb.createAnd(pb.createAdvance(inGroup, 1), ASCII); // PFX 00-7F
        if(i == 1) {
            PabloAST * inGroup_5_8 = pb.createAnd(bnc.UGE(basis, base_divided), bnc.ULT(basis, next_base_divided));
            PabloAST * curGroupStream_5_8 = pb.createAnd(pb.createAdvance(inGroup_5_8, 1), ASCII);
            groupStreams[i+enc_len] = curGroupStream_5_8;
        }
        groupStreams[i] = curGroupStream;
        for (unsigned j = 2; j < groupInfo.encoding_bytes; j++) {
            groupStreams[i] = pb.createAnd(pb.createAdvance(groupStreams[i], 1), ASCII);
            if (j+1 == groupInfo.encoding_bytes) {
                // PFX 00-7F{1,2} 80-BF
                unsigned idx = i+enc_len;
                curGroupStream = pb.createAnd(pb.createAdvance(curGroupStream, groupInfo.encoding_bytes-2), suffix_80_BF);
                if ((mEncodingScheme.byLength.size() == 5 && idx == 9) || 
                    (mEncodingScheme.byLength.size() == 4 && idx == 7)) {
                    curGroupStream = pb.createAnd(curGroupStream, allInvalidBoundaryCodeword);
                }
                groupStreams[i+enc_len] = curGroupStream;
                //pb.createOr(groupStreams[i], curGroupStream);
            }
        }
        if((mEncodingScheme.byLength.size() == 5) && (i == 4 || i == 9)) {
            groupStreams[i] = pb.createAnd(groupStreams[i], allInvalidBoundaryCodeword);
        }
        if((mEncodingScheme.byLength.size() == 4) && (i == 3 || i == 7)) {
            groupStreams[i] = pb.createAnd(groupStreams[i], allInvalidBoundaryCodeword);
        }
    }
    for (unsigned i = 0; i < (mNumSym * enc_len); i++) {
        pb.createAssign(pb.createExtract(groupStreamVar, pb.getInteger(i)), pb.createAnd(groupStreams[i], pb.createNot(hashTableSpan)));
        pb.createAssign(pb.createExtract(hashTableStreamVar, pb.getInteger(i)), pb.createAnd(groupStreams[i], pb.createXor(hashtableBoundaries, hashTableSpan)));
    }
    // pb.createDebugPrint(pb.createCount(filterSpan), "filterSpan");
    // pb.createDebugPrint(pb.createCount(hashTableSpan), "hashTableSpan");
    // pb.createDebugPrint(pb.createCount(hashTableBoundaryStartFinal), "hashTableBoundaryStartFinal");
    // pb.createDebugPrint(pb.createCount(hashTableBoundaryEndFinal), "hashTableBoundaryEndFinal");
    pb.createAssign(pb.createExtract(getOutputStreamVar("hashtableSpan"), pb.getInteger(0)), filterSpan);
}

std::pair<unsigned, unsigned> getNumOfPrefix(unsigned groupNo) {
    switch(groupNo) {
        case 0: return std::make_pair(8, 1);
        case 1: return std::make_pair(8, 1);
        case 2: return std::make_pair(4, 4);
        case 3: return std::make_pair(2, 8);
        case 4: return std::make_pair(1, 1);
        default: return std::make_pair(0, 0);
    }
}
unsigned getLenStartPfx(EncodingInfo & encodingScheme, unsigned groupNo, unsigned length) {
    unsigned groupStartPfx = 0;
    auto g = encodingScheme.byLength[groupNo];
    switch(groupNo) {
        case 0: groupStartPfx = 192;
        case 1: groupStartPfx = 200;
        case 2: groupStartPfx = 208;
        case 3: groupStartPfx = 224;
        case 4: groupStartPfx = 240;
        default: groupStartPfx = 0;
    }
    return groupStartPfx + (length - g.lo);
}

std::vector<unsigned> getPrefixForGroupLength(EncodingInfo & encodingScheme, unsigned length) {
    std::vector<unsigned> prefixes;
    // llvm::errs() << "p-> " << length << "\n";
    unsigned groupNo = encodingScheme.getLengthGroupNo(length);
    auto numPfx = getNumOfPrefix(groupNo); // # of prefix, jump
    unsigned lenPfx = getLenStartPfx(encodingScheme, groupNo, length); //length start pfx offset
    for (unsigned i = 0; i < numPfx.first; i++) {
        prefixes.push_back(lenPfx + (i * numPfx.second));
    }
    // for (auto p : prefixes) {
    //     llvm::errs() << "p-> " << p << "\n";
    // }
    return prefixes;
}

ProcessCandidateMatches::ProcessCandidateMatches(BuilderRef kb,
                EncodingInfo & encodingScheme,
                StreamSet * basis,
                StreamSet * results,
                StreamSet * dictStart,
                StreamSet * candidateMatchesInDict,
                StreamSet * nonCandidateMatchesInDict,
                StreamSet * codeWordInCipherText,
                StreamSet * candidateMatchesInCipherText,
                bool matchOnly)
: PabloKernel(kb, "ProcessCandidateMatches_" + std::to_string(matchOnly),
            {Binding{"basis", basis, FixedRate(), LookAhead(encodingScheme.maxEncodingBytes() - 1)},
             Binding{"results", results, FixedRate(), LookAhead(1)}},
            {Binding{"dictStart", dictStart, FixedRate(), Add1()},
             Binding{"candidateMatchesInDict", candidateMatchesInDict, FixedRate(), Add1()},
             Binding{"nonCandidateMatchesInDict", nonCandidateMatchesInDict, FixedRate(), Add1()},
             Binding{"codeWordInCipherText", codeWordInCipherText, FixedRate(), Add1()},
             Binding{"candidateMatchesInCipherText", candidateMatchesInCipherText, FixedRate(), Add1()}}),
mEncodingScheme(encodingScheme), mMatchOnly(matchOnly) { }

void ProcessCandidateMatches::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    PabloAST * results = getInputStreamSet("results")[0];
    Var * candidateMatchesInDictVar = getOutputStreamVar("candidateMatchesInDict");
    Var * nonCandidateMatchesInDictVar = getOutputStreamVar("nonCandidateMatchesInDict");
    Var * codeWordInCipherTextVar = getOutputStreamVar("codeWordInCipherText");

    ///CHECK: Almost done except the prefix byte: eliminate matches that have codeword suffix as match start pos
    PabloAST * candidateMatchStart = results;
    if (!mMatchOnly) {
        candidateMatchStart = pb.createOr(results, pb.createLookahead(results, 1));
        candidateMatchStart = pb.createXor(candidateMatchStart, results);
        candidateMatchStart = pb.createAdvance(candidateMatchStart, 1);
    }
    // auto pfx = getPrefixForGroupLength(mEncodingScheme, mCandidateMatchLen);
    PabloAST * hashTableBoundaryCommon = pb.createAnd(pb.createAnd(basis[7], basis[6]), pb.createAnd(basis[5], basis[4])); //Fx
    PabloAST * hashTableBoundaryStartHi = pb.createAnd3(basis[3], basis[2], basis[1]); //xE, xF
    PabloAST * hashTableBoundaryEndHi = pb.createAnd(hashTableBoundaryStartHi, basis[0]); //xF
    hashTableBoundaryStartHi = pb.createXor(hashTableBoundaryStartHi, hashTableBoundaryEndHi); // xE

    PabloAST * hashTableBoundaryStart = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryStartHi);
    PabloAST * hashTableBoundaryEnd = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryEndHi);
    PabloAST * hashTableBoundaryStartFinal = pb.createAnd(hashTableBoundaryStart, pb.createAdvance(hashTableBoundaryStart, 1));
    PabloAST * hashTableBoundaryEndFinal = pb.createAnd(hashTableBoundaryEnd, pb.createAdvance(hashTableBoundaryEnd, 1));
    PabloAST * EOFbit = pb.createAtEOF(pb.createAdvance(pb.createOnes(), 1));

    PabloAST * hashTableSpan = pb.createIntrinsicCall(pablo::Intrinsic::SpanUpTo, {hashTableBoundaryStartFinal, hashTableBoundaryEndFinal});
    PabloAST * toEliminate = pb.createAnd(pb.createLookahead(basis[7], 1), pb.createOr(hashTableBoundaryStart, hashTableBoundaryEnd));
    hashTableSpan = pb.createOr3(hashTableSpan, hashTableBoundaryEndFinal, toEliminate);

    PabloAST * boundaryEndInvalidCodeword = pb.createAdvance(hashTableBoundaryEndFinal, 3);
    PabloAST * boundaryStartInvalidCodeword = pb.createAdvance(hashTableBoundaryStartFinal, 3);
    PabloAST * allInvalidBoundaryCodeword = pb.createNot(pb.createOr(boundaryEndInvalidCodeword, boundaryStartInvalidCodeword));

    PabloAST * allGroupStream = pb.createZeroes();
    PabloAST * ASCII = bnc.ULT(basis, 0x80);
    PabloAST * suffix_80_BF = pb.createAnd(bnc.UGE(basis, 0x80), bnc.ULE(basis, 0xBF));
    /// CHECK: if any codeword byte position collides with candidateMatchStart pos, eliminate that candidateMatchStart bit
    for (unsigned i = 0; i < mEncodingScheme.byLength.size(); i++) {
        PabloAST * groupStreams = pb.createZeroes();
        LengthGroupInfo groupInfo = mEncodingScheme.byLength[i];
        unsigned base = groupInfo.prefix_base;
        unsigned next_base = 0;
        if (i == 0) {
            next_base = base + 8;
        }
        else if (i == 1) {
            next_base = base + 24;
        }
        else {
            next_base = base + 16;
        }
        PabloAST * inGroup = pb.createAnd(bnc.UGE(basis, base), bnc.ULT(basis, next_base));
        /// CHECK: eliminate any codeword prefix in dictionary matched incorrectly 
        PabloAST * curGroupStream = pb.createAnd(pb.createAdvance(inGroup, 1), ASCII); // PFX 00-7F
        candidateMatchStart = pb.createAnd(pb.createNot(curGroupStream), candidateMatchStart);
        // groupStream marks 1-bit at the suffix byte of codewords of i-th length-group
        groupStreams = curGroupStream;

        for (unsigned j = 2; j < groupInfo.encoding_bytes; j++) {
            groupStreams = pb.createAnd(pb.createAdvance(groupStreams, 1), ASCII);
            // eliminate any candidate match start position that is a codeword suffix byte
            candidateMatchStart = pb.createAnd(pb.createNot(groupStreams), candidateMatchStart);
            if (j+1 == groupInfo.encoding_bytes) {
                // PFX 00-7F{1,2} 80-BF
                unsigned idx = i+mEncodingScheme.byLength.size();
                curGroupStream = pb.createAnd(pb.createAdvance(curGroupStream, groupInfo.encoding_bytes-2), suffix_80_BF);
                if (idx == 7) {
                    curGroupStream = pb.createAnd(curGroupStream, allInvalidBoundaryCodeword);
                }
                 // not needed: no valid character starts with suffix_80_BF 
                // candidateMatchStart = pb.createAnd(pb.createNot(curGroupStream), candidateMatchStart);
            }
            groupStreams = curGroupStream;
        }
        if(i == 3 || i == 7) {
            groupStreams = pb.createAnd(groupStreams, allInvalidBoundaryCodeword);
        }
        allGroupStream = pb.createOr(allGroupStream, groupStreams);
    }
    // candidateMatchStart marks the match start pos of current length-group (ideally marks the phrases)
    // advance candidateMatchStart until it coincides with groupStream marker for that phrase
    // allGroupStream has a codeword marker for every phrase. No candidate mark will move past its codeword last byte
    PabloAST * movedCandidateMatches = pb.createZeroes();
    PabloAST * candidateMatchStartCopy = candidateMatchStart;
    for (unsigned i = 1; i < mEncodingScheme.maxSymbolLength()+mEncodingScheme.maxEncodingBytes(); i++) {
        candidateMatchStartCopy = pb.createAdvance(candidateMatchStartCopy, 1);
        movedCandidateMatches = pb.createOr(movedCandidateMatches, pb.createAnd(candidateMatchStartCopy, allGroupStream));
        candidateMatchStartCopy = pb.createAnd(pb.createNot(allGroupStream), candidateMatchStartCopy);
    }

    pb.createAssign(pb.createExtract(candidateMatchesInDictVar, pb.getInteger(0)), pb.createAnd(hashTableSpan, movedCandidateMatches));
    // movedCandidateMatches is a subset of allGroupStream; so XOR should delete the movedCandidateMatches from allGroupStream
    // AND with hashTableSpan gived nonCandidateMatchesInDict
    pb.createAssign(pb.createExtract(nonCandidateMatchesInDictVar, pb.getInteger(0)), pb.createAnd(hashTableSpan, pb.createXor(movedCandidateMatches, allGroupStream)));
    pb.createAssign(pb.createExtract(codeWordInCipherTextVar, pb.getInteger(0)), pb.createAnd(allGroupStream, pb.createNot(hashTableSpan)));
    pb.createAssign(pb.createExtract(getOutputStreamVar("dictStart"), pb.getInteger(0)), pb.createOr(hashTableBoundaryStartFinal, EOFbit));
    // Results after eliminating invalid candidate matches
    pb.createAssign(pb.createExtract(getOutputStreamVar("candidateMatchesInCipherText"), pb.getInteger(0)), candidateMatchStart); // candidate marks in dict awa compressed data part
}

Bindings ZTF_PhraseExpansionDecoderInputBindings(EncodingInfo & encodingScheme, StreamSet * basis) {
    return {Binding{"basis", basis, FixedRate(), LookAhead(encodingScheme.maxEncodingBytes() - 1)}};
}

ZTF_PhraseExpansionDecoder::ZTF_PhraseExpansionDecoder(BuilderRef b,
                                           EncodingInfo & encodingScheme,
                                           StreamSet * const basis,
                                           StreamSet * insertBixNum,
                                           bool fullyDecompress)
: pablo::PabloKernel(b, "ZTF_PhraseExpansionDecoder" + encodingScheme.uniqueSuffix() + std::to_string(fullyDecompress),
                     ZTF_PhraseExpansionDecoderInputBindings(encodingScheme, basis),
                     {Binding{"insertBixNum", insertBixNum}}),
    mEncodingScheme(encodingScheme), mFullyDecompress(fullyDecompress)  {}

void ZTF_PhraseExpansionDecoder::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    BixNumCompiler bnc(pb);
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    std::vector<PabloAST *> ASCII_lookaheads;
    std::vector<PabloAST *> sfx_80_BF_lookaheads;
    PabloAST * ASCII_lookahead = pb.createNot(pb.createLookahead(basis[7], 1)); // for lg 0,1,2
    ASCII_lookaheads.push_back(ASCII_lookahead);
    //pb.createDebugPrint(ASCII_lookahead, "ASCII_lookahead");
    // for lg 3,4
    PabloAST * hashTableBoundaryCommon = pb.createAnd(pb.createAnd(basis[7], basis[6]), pb.createAnd(basis[5], basis[4])); //Fx
    PabloAST * hashTableBoundaryStartHi = pb.createAnd3(basis[3], basis[2], basis[1]); //xE, xF
    PabloAST * hashTableBoundaryEndHi = pb.createAnd(hashTableBoundaryStartHi, basis[0]); //xF
    hashTableBoundaryStartHi = pb.createXor(hashTableBoundaryStartHi, hashTableBoundaryEndHi); // xE

    PabloAST * hashTableBoundaryStart = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryStartHi);
    PabloAST * hashTableBoundaryEnd = pb.createAnd(hashTableBoundaryCommon, hashTableBoundaryEndHi);
    PabloAST * hashTableBoundaryStartFinal = pb.createAnd(hashTableBoundaryStart, pb.createAdvance(hashTableBoundaryStart, 1));
    PabloAST * hashTableBoundaryEndFinal = pb.createAnd(hashTableBoundaryEnd, pb.createAdvance(hashTableBoundaryEnd, 1));
    // pb.createDebugPrint(pb.createCount(hashTableBoundaryStartFinal), "hashTableBoundaryStartFinal");
    // pb.createDebugPrint(pb.createCount(hashTableBoundaryEndFinal), "hashTableBoundaryEndFinal");

    PabloAST * hashTableSpan = pb.createIntrinsicCall(pablo::Intrinsic::SpanUpTo, {hashTableBoundaryStartFinal, hashTableBoundaryEndFinal});
    PabloAST * toEliminate = pb.createAnd(pb.createLookahead(basis[7], 1), pb.createOr(hashTableBoundaryStart, hashTableBoundaryEnd));
    hashTableSpan = pb.createOr3(hashTableSpan, hashTableBoundaryEndFinal, toEliminate);

    for (unsigned i = 2; i < mEncodingScheme.maxEncodingBytes(); i++) {
        PabloAST * ASCII_lookahead_multibyte = pb.createAnd(ASCII_lookahead, pb.createNot(pb.createLookahead(basis[7], pb.getInteger(i))));
        ASCII_lookaheads.push_back(ASCII_lookahead_multibyte);
        //pb.createDebugPrint(pb.createLookahead(basis[7], pb.getInteger(i)), "ASCII_lookahead_multibyte");
    }
    for(unsigned i = 2; i < mEncodingScheme.maxEncodingBytes(); i++) {
        PabloAST * suffix_lookahead = pb.createAnd(pb.createLookahead(basis[7], pb.getInteger(i)), pb.createNot(pb.createLookahead(basis[6], pb.getInteger(i)))); // 80-BF
        suffix_lookahead = pb.createAnd(suffix_lookahead, ASCII_lookahead); // E0-EF 00-7F 80-BF; F0-FF 00-7F 00-7F 80-BF
        sfx_80_BF_lookaheads.push_back(suffix_lookahead);
    }
    /*
        CODEWORDS                                                    | VALID UTF-8
        2-byte -> non-ASCII ASCII               > bit 7 -> 1 0       | 2-byte -> non-ASCII 80-BF               > bit 7 -> 1 1
        3-byte -> non-ASCII ASCII ASCII         > bit 7 -> 1 0 0     | 3-byte -> non-ASCII 80-BF 80-BF         > bit 7 -> 1 1 1
        3-byte -> non-ASCII ASCII ASCII ASCII   > bit 7 -> 1 0 0 0   | 3-byte -> non-ASCII 80-BF 80-BF 80-BF   > bit 7 -> 1 1 1 1
        10000000 - 10111111
    */
    /*
        3    |  0xC0-0xC7               (192-199) 0000 0001 0010 0011 0100 0101 0110 0111
        4    |  0xC8-0xCF               (200-208) 1000 1001 1010 1011 1100 1101 1110 1111
        5    |  0xD0, 0xD4, 0xD8, 0xDC  } - base = 0,4,8,12  0000 0100 1000 1100 // low 2 bits + (lo - encoding_bytes)
        6    |  0xD1, 0xD5, 0xD9, 0xDD  } - base = 1,5,9,13  0001 0101 1001 1101
        7    |  0xD2, 0xD6, 0xDA, 0xDE  } - base = 2,6,10,14 0010 0110 1010 1110
        8    |  0xD3, 0xD7, 0xDB, 0xDF  } - base = 3,7,11,15 0011 0111 1011 1111
        9-16 |  0xE0 - 0xEF (3-bytes)   } - lo - encoding_bytes = 9 - 3 = 6
                                            length = low 3 bits + (lo - encoding_bytes)
        17-32|  0xF0 - 0xFF (4-bytes)   } - lo - encoding_bytes = 17 - 4 = 13
                                            length = pfx-base + (lo - encoding_bytes)
    */
    BixNum insertLgth(5, pb.createZeroes());
    for (unsigned i = 0; i < mEncodingScheme.byLength.size(); i++) {
        BixNum relative(5, pb.createZeroes());
        BixNum toInsert(5, pb.createZeroes());
        LengthGroupInfo groupInfo = mEncodingScheme.byLength[i];
        unsigned lo = groupInfo.lo;
        unsigned base = groupInfo.prefix_base;
        unsigned next_base;
        PabloAST * inGroup = pb.createZeroes();
        PabloAST * groupRange = pb.createZeroes();
        unsigned two_byte_cw_end = 3;
        unsigned pfx_jump_8 = 2;
        unsigned lookAhead1= 2;
        unsigned lookAhead2 = 3;
        if (mEncodingScheme.byLength.size() == 4) {
            two_byte_cw_end = 2;
            pfx_jump_8 = 1;
            lookAhead1 = 1;
            lookAhead2 = 2;
        }
        if (i < two_byte_cw_end) {
            if (i < pfx_jump_8) {
                next_base = base + 8;
                groupRange = pb.createAnd(bnc.UGE(basis, base), bnc.ULT(basis, next_base));
                inGroup = pb.createOr(inGroup, pb.createAnd(ASCII_lookaheads[0], groupRange));
                //count.push_back(inGroup);
            }
            else {
                next_base = base + 16;
                groupRange = pb.createAnd(bnc.UGE(basis, base), bnc.ULT(basis, next_base));
                inGroup = pb.createOr(inGroup, pb.createAnd(ASCII_lookaheads[0], groupRange));
                BixNum diff = bnc.SubModular(basis, base); // SubModular range (0-7)
                for (unsigned extractIdx = 0; extractIdx < 2; extractIdx++) { // extract low 2 bits
                    relative[extractIdx] = pb.createOr(relative[extractIdx], diff[extractIdx]);
                }
            }
            //pb.createDebugPrint(inGroup, "inGroup["+std::to_string(i)+"]");
            toInsert = bnc.AddModular(relative, lo - groupInfo.encoding_bytes);
        }
        else {
            next_base = base + 16;
            groupRange = pb.createAnd(bnc.UGE(basis, base), bnc.ULT(basis, next_base));
            PabloAST * lookahead_accum = pb.createOr(ASCII_lookaheads[i-lookAhead1], sfx_80_BF_lookaheads[i-lookAhead2]);
            inGroup = pb.createOr(inGroup, pb.createAnd(lookahead_accum, groupRange));
            //pb.createDebugPrint(inGroup, "inGroup["+std::to_string(i)+"]");
            if (i == two_byte_cw_end) {
                BixNum diff = bnc.SubModular(basis, base); // 0,8; 1,9; 2,10; etc...
                for (unsigned extractIdx = 0; extractIdx < 3; extractIdx++) {
                    relative[extractIdx] = pb.createOr(relative[extractIdx], diff[extractIdx]);
                }
            }
            else {
                BixNum diff = bnc.SubModular(basis, base); // SubModular range (0-7)
                for (unsigned extractIdx = 0; extractIdx < 4; extractIdx++) { // extract low 4 bits
                    relative[extractIdx] = pb.createOr(relative[extractIdx], diff[extractIdx]);
                }
            }
            toInsert = bnc.AddModular(relative, lo - groupInfo.encoding_bytes);
        }
        for (unsigned j = 0; j < 5; j++) {
            insertLgth[j] = pb.createSel(inGroup, toInsert[j], insertLgth[j], "insertLgth[" + std::to_string(j) + "]");
        }
    }
    Var * lengthVar = getOutputStreamVar("insertBixNum");
    for (unsigned i = 0; i < 5; i++) {
        pb.createAssign(pb.createExtract(lengthVar, pb.getInteger(i)), pb.createAnd(pb.createNot(hashTableSpan), insertLgth[i]));
    }
}

void MatchedSegmentsKernel::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    auto cipherTextCandidateMatches = getInputStreamSet("MatchesInCipherText")[0];
    auto codewordMatches = getInputStreamSet("CodewordMatches")[0];
    auto matches = pb.createOr(cipherTextCandidateMatches, codewordMatches);
    PabloAST * dictStarts = pb.createExtract(getInputStreamVar("dictStart"), pb.getInteger(0));
    PabloAST * notDictStart = pb.createNot(dictStarts);
    PabloAST * match_follow = pb.createMatchStar(matches, notDictStart);
    PabloAST * segmentStarts = pb.createInFile(pb.createNot(pb.createAdvance(pb.createNot(dictStarts), 1)));
    pb.createAssign(pb.createExtract(getOutputStreamVar("SegmentStarts"), 0), segmentStarts);
    Var * const matchedSegments = getOutputStreamVar("MatchedSegments");
    pb.createAssign(pb.createExtract(matchedSegments, pb.getInteger(0)), pb.createAnd(match_follow, dictStarts, "MatchedSegments"));
}

MatchedSegmentsKernel::MatchedSegmentsKernel (BuilderRef iBuilder, StreamSet * MatchesInCipherText, StreamSet * CodewordMatches, StreamSet * dictStart, StreamSet * MatchedSegments, StreamSet * SegmentStarts)
: PabloKernel(iBuilder, "MatchedSegmentsKernel" + std::to_string(MatchesInCipherText->getNumElements()),
// inputs
{Binding{"MatchesInCipherText", MatchesInCipherText},
 Binding{"CodewordMatches", CodewordMatches},
 Binding{"dictStart", dictStart, FixedRate()}},
// output
{Binding{"MatchedSegments", MatchedSegments, FixedRate(), Add1()},
 Binding{"SegmentStarts", SegmentStarts, FixedRate(), Add1()}}) {

}

kernel::StreamSet * kernel::ZTFLinesLogic(const std::unique_ptr<ProgramBuilder> & P,
                                EncodingInfo & encodingScheme,
                                StreamSet * const Basis,
                                StreamSet * const Results,
                                StreamSet * const hashtableMarks,
                                StreamSet * const decodedMarks,
                                StreamSet * const filterSpan,
                                bool matchOnlyMode) {
// NOTE: The grep output requires complete lines to be printed as output and lines may be divided across multiple segments.
    StreamSet * const dictStart = P->CreateStreamSet(1);
    StreamSet * const candidateMatchesInDict = P->CreateStreamSet(1);
    StreamSet * const codeWordInCipherText = P->CreateStreamSet(1);
    StreamSet * const nonCandidateMatchesInDict = P->CreateStreamSet(1);
    StreamSet * const candidateMatchesInCipherText = P->CreateStreamSet(1);
/*
    1. eliminate all the invalid matches in dictionary. (matches that start from codeword pfx/sfx bytes)
    2. finalize the candidate matches: mark the codewords adjacent to the phrases with candidate matches (in dictionary part).
        i. for every match in dictionary, move the match pos to the last byte of phrase. Assign to streams of different length groups.
       ii. parse the compressed data, create a hashtable of the codewords with candidate matches.
      iii. mark the codewords which have a hashtable entry.
*/
    /// WIP: Update results to remove any invalid matches in the dictionary (all done except pfx byte)
    // Input: basis, candidateMatches
    // Output: candidateMatchCodeWordInDict, nonCandidateMatchCodeWordInDict, codeWordInCipherText
    P->CreateKernelCall<ProcessCandidateMatches>(encodingScheme, Basis, Results, dictStart, candidateMatchesInDict, nonCandidateMatchesInDict, codeWordInCipherText/*all codewords in ciphertext*/, candidateMatchesInCipherText/*plaintext match of sub-expression*/, matchOnlyMode); // add 1-bit at the end of dictEnd stream
    //Perform single scan of compressed data to finalize candidate matches
    StreamSet * const basis_bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(Basis, basis_bytes);
    StreamSet * const allCandidateMatches = P->CreateStreamSet(1);
    P->CreateKernelCall<FinalizeCandidateMatches>(encodingScheme, basis_bytes, candidateMatchesInDict, nonCandidateMatchesInDict, codeWordInCipherText, allCandidateMatches);
    StreamSet * const MatchedSegmentEnds = P->CreateStreamSet();
    StreamSet * SegmentStarts = P->CreateStreamSet(1, 1); // Advance dictStart by 1 position
    P->CreateKernelCall<MatchedSegmentsKernel>(candidateMatchesInCipherText, allCandidateMatches, dictStart, MatchedSegmentEnds, SegmentStarts);
    StreamSet * MatchesBySegment = P->CreateStreamSet(1, 1);
    // 1-bit per segment indicating presense of candidate matches in the segment
    FilterByMask(P, dictStart, MatchedSegmentEnds, MatchesBySegment);
    P->CreateKernelCall<DebugDisplayKernel>("MatchesBySegment", MatchesBySegment); // filter the bits that collide with dictionary start and also is a match at the segment end
    StreamSet * MatchedSegmentStarts = P->CreateStreamSet(1, 1);
    SpreadByMask(P, SegmentStarts, MatchesBySegment, MatchedSegmentStarts);
    StreamSet * MatchedSegmentSpans = P->CreateStreamSet(1, 1);
    P->CreateKernelCall<LineSpansKernel>(MatchedSegmentStarts, MatchedSegmentEnds, MatchedSegmentSpans);
    // P->CreateKernelCall<DebugDisplayKernel>("MatchedSegmentSpans", MatchedSegmentSpans);

    StreamSet * const toDecompress_basis = P->CreateStreamSet(8);
    FilterByMask(P, MatchedSegmentSpans, Basis, toDecompress_basis);
    // StreamSet * const bytes = P->CreateStreamSet(1, 8);
    // P->CreateKernelCall<P2SKernel>(toDecompress_basis, bytes);
    // P->CreateKernelCall<StdOutKernel>(bytes);

    StreamSet * const ztfInsertionLengths = P->CreateStreamSet(5);
    P->CreateKernelCall<ZTF_PhraseExpansionDecoder>(encodingScheme, Basis, ztfInsertionLengths, false);
    StreamSet * const ztfRunSpreadMask = InsertionSpreadMask(P, ztfInsertionLengths);
    StreamSet * const ztfHash_u8_Basis = P->CreateStreamSet(8);
    SpreadByMask(P, ztfRunSpreadMask, Basis, ztfHash_u8_Basis);
    P->CreateKernelCall<ZTF_PhraseDecodeLengths>(encodingScheme, 2/*SymCount*/, ztfHash_u8_Basis, decodedMarks, hashtableMarks, filterSpan, false);
    StreamSet * const ztfHash_u8bytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(ztfHash_u8_Basis, ztfHash_u8bytes);
    return ztfHash_u8bytes;
}
