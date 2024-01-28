/*
 *  Copyright (c) 2022 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 */


#include <cstdio>
#include <vector>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Module.h>
#include <re/adt/re_name.h>
#include <re/adt/re_re.h>
#include <pablo/codegenstate.h>
#include <pablo/pe_zeroes.h>        // for Zeroes
#include <grep/grep_kernel.h>
#include <kernel/core/kernel_builder.h>
#include <kernel/pipeline/pipeline_builder.h>
#include <kernel/streamutils/deletion.h>
#include <kernel/streamutils/pdep_kernel.h>
#include <kernel/streamutils/run_index.h>
#include <kernel/streamutils/string_insert.h>
#include <kernel/basis/s2p_kernel.h>
#include <kernel/basis/p2s_kernel.h>
#include <kernel/io/source_kernel.h>
#include <kernel/io/stdout_kernel.h>
#include <kernel/util/debug_display.h>
#include <kernel/unicode/charclasses.h>
#include <kernel/unicode/utf8gen.h>
#include <kernel/unicode/utf8_decoder.h>
#include <re/adt/re_name.h>
#include <re/cc/cc_kernel.h>
#include <re/cc/cc_compiler.h>
#include <re/cc/cc_compiler_target.h>
#include <string>
#include <toolchain/toolchain.h>
#include <pablo/pablo_toolchain.h>
#include <fcntl.h>
#include <iostream>
#include <kernel/pipeline/driver/cpudriver.h>
#include <unicode/data/PropertyAliases.h>
#include <unicode/data/PropertyObjects.h>
#include <unicode/data/PropertyObjectTable.h>
#include <unicode/utf/utf_compiler.h>
#include <re/toolchain/toolchain.h>

using namespace kernel;
using namespace llvm;
using namespace pablo;

//  These declarations are for command line processing.
//  See the LLVM CommandLine Library Manual https://llvm.org/docs/CommandLine.html
static cl::OptionCategory Xch_Options("Character transformation Options", "Character transformation Options.");
static cl::opt<std::string> XfrmProperty(cl::Positional, cl::desc("transformation kind (Unicode property)"), cl::Required, cl::cat(Xch_Options));
static cl::opt<std::string> inputFile(cl::Positional, cl::desc("<input file>"), cl::Required, cl::cat(Xch_Options));

#define SHOW_STREAM(name) if (illustratorAddr) illustrator.captureBitstream(P, #name, name)
#define SHOW_BIXNUM(name) if (illustratorAddr) illustrator.captureBixNum(P, #name, name)
#define SHOW_BYTES(name) if (illustratorAddr) illustrator.captureByteData(P, #name, name)

class AdjustU8bixnum : public pablo::PabloKernel {
public:
    AdjustU8bixnum(BuilderRef b,
                   StreamSet * Basis, StreamSet * InsertBixNum,
                   StreamSet * AdjustedBixNum);
protected:
    void generatePabloMethod() override;
private:
    unsigned mBixBits;
};

AdjustU8bixnum::AdjustU8bixnum (BuilderRef b,
                                StreamSet * Basis, StreamSet * InsertBixNum,
                                StreamSet * AdjustedBixNum)
: PabloKernel(b, "adjust_bixnum" + std::to_string(InsertBixNum->getNumElements()) + "x1",
// inputs
{Binding{"basis", Basis}, Binding{"insert_bixnum", InsertBixNum, FixedRate(1), LookAhead(2)}},
// output
{Binding{"adjusted_bixnum", AdjustedBixNum}}),
    mBixBits(InsertBixNum->getNumElements()) {
}

void AdjustU8bixnum::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    Var * insert_bixnum = getInputStreamVar("insert_bixnum");
    Var * insert_bit0 = pb.createExtract(insert_bixnum, pb.getInteger(0));
    std::vector<PabloAST *> adjusted_bixnum;
    // Insertion positions for a three byte UTF-8 sequence are
    // marked at the third byte.   The max insertion is 1, for
    // conversion to a four-byte sequence.  The insertion position
    // must be adjusted two positions forward.
    PabloAST * prefix = pb.createAnd(basis[7], basis[6]);
    PabloAST * prefix34 = pb.createAnd(prefix, basis[5]);
    PabloAST * prefix3 = pb.createAnd(prefix34, pb.createNot(basis[4]));
    PabloAST * p3_adjust = pb.createAnd(prefix3, pb.createLookahead(insert_bit0, 2));
    p3_adjust = pb.createOr(p3_adjust, pb.createAdvance(p3_adjust, 2));
    adjusted_bixnum.push_back(pb.createXor(p3_adjust, insert_bit0));
    // Insertion positions for a two byte UTF-8 sequence are
    // marked at the second byte.   The insertion is 1 or 2, for
    // conversion to a three- or four-byte sequence.  Adjust one
    // position forward.
    PabloAST * prefix2 = pb.createAnd(prefix, pb.createNot(basis[5]));
    PabloAST * p2_adjust_0 = pb.createAnd(prefix2, pb.createLookahead(insert_bit0, 1));
    p2_adjust_0 = pb.createOr(p2_adjust_0, pb.createAdvance(p2_adjust_0, 1));
    adjusted_bixnum[0] = pb.createXor(p2_adjust_0, adjusted_bixnum[0]);
    if (mBixBits == 2) {
        Var * insert_bit1 = pb.createExtract(insert_bixnum, pb.getInteger(1));
        PabloAST * p2_adjust_1 = pb.createAnd(prefix2, pb.createLookahead(insert_bit1, 1));
        p2_adjust_1 = pb.createOr(p2_adjust_1, pb.createAdvance(p2_adjust_1, 1));
        adjusted_bixnum.push_back(pb.createXor(p2_adjust_1, insert_bit1));
    }
    Var * const adjusted = getOutputStreamVar("adjusted_bixnum");
    for (unsigned i = 0; i < mBixBits; i++) {
        pb.createAssign(pb.createExtract(adjusted, pb.getInteger(i)), adjusted_bixnum[i]);
    }
}

class CreateU8delMask : public pablo::PabloKernel {
public:
    CreateU8delMask(BuilderRef b,
                    StreamSet * Basis, StreamSet * DeletionBixNum,
                    StreamSet * DelMask);
protected:
    void generatePabloMethod() override;
private:
    unsigned mBixBits;
};

CreateU8delMask::CreateU8delMask (BuilderRef b,
                                StreamSet * Basis, StreamSet * DeletionBixNum,
                                StreamSet * DelMask)
: PabloKernel(b, "u8_delmask" + std::to_string(DeletionBixNum->getNumElements()) + "x1",
// inputs
{Binding{"basis", Basis}, Binding{"deletion_bixnum", DeletionBixNum, FixedRate(1), LookAhead(3)}},
// output
{Binding{"selection_mask", DelMask}}),
    mBixBits(DeletionBixNum->getNumElements()) {
}

void CreateU8delMask::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    Var * deletion_bixnum = getInputStreamVar("deletion_bixnum");
    Var * del_bixnum0 = pb.createExtract(deletion_bixnum, pb.getInteger(0));
    // Deletion bixnums are calculated at the final position of a UTF-8
    // sequence.   If the deletion amount is nonzero, then the
    // prefix position is marked for deletion.
    PabloAST * prefix = pb.createAnd(basis[7], basis[6]);
    PabloAST * prefix2 = pb.createAnd(prefix, pb.createNot(basis[5]));
    PabloAST * prefix34 = pb.createAnd(prefix, basis[5]);
    PabloAST * prefix3 = pb.createAnd(prefix34, pb.createNot(basis[4]));
    PabloAST * prefix4 = pb.createAnd(prefix34, basis[4]);
    PabloAST * del_mask = pb.createAnd(prefix2, pb.createLookahead(del_bixnum0, 1));
    del_mask = pb.createOr(del_mask, pb.createAnd(prefix3, pb.createLookahead(del_bixnum0, 2)));
    del_mask = pb.createOr(del_mask, pb.createAnd(prefix4, pb.createLookahead(del_bixnum0, 3)));
    if (mBixBits == 2) {
        Var * del_bixnum1 = pb.createExtract(deletion_bixnum, pb.getInteger(1));
        del_mask = pb.createOr(del_mask, pb.createAnd(prefix3, pb.createLookahead(del_bixnum1, 2)));
        del_mask = pb.createOr(del_mask, pb.createAnd(prefix4, pb.createLookahead(del_bixnum1, 3)));
        // The second byte of a three-byte sequence is deleted if the deletion amount is 2.
        PabloAST * scope32 = pb.createAdvance(prefix3, 1);
        del_mask = pb.createOr(del_mask, pb.createAnd(scope32, pb.createLookahead(del_bixnum1, 1)));
        // The second byte of a four-byte sequence is deleted if the deletion amount is 2 or 3.
        PabloAST * scope42 = pb.createAdvance(prefix4, 1);
        del_mask = pb.createOr(del_mask, pb.createAnd(scope42, pb.createLookahead(del_bixnum1, 2)));
        // The third byte of a four-byte sequence is deleted if the deletion amount is 3.
        PabloAST * scope43 = pb.createAdvance(prefix4, 2);
        PabloAST * del3 = pb.createAnd(pb.createLookahead(del_bixnum0, 1), pb.createLookahead(del_bixnum1, 1));
        del_mask = pb.createOr(del_mask, pb.createAnd(scope43, del3));
    }
    PabloAST * selected = pb.createInFile(pb.createNot(del_mask));
    Var * const selection_mask = getOutputStreamVar("selection_mask");
    pb.createAssign(pb.createExtract(selection_mask, pb.getInteger(0)), selected);
}

class UTF8_BytePosition : public pablo::PabloKernel {
public:
    UTF8_BytePosition(BuilderRef b, StreamSet * Basis, StreamSet * Positions);
protected:
    void generatePabloMethod() override;
};

UTF8_BytePosition::UTF8_BytePosition(BuilderRef b, StreamSet * Basis, StreamSet * Positions)
: PabloKernel(b, "UTF8_BytePosition",
{Binding{"basis", Basis, FixedRate(1), LookAhead(2)}},
// output
{Binding{"positions", Positions}}) {
}

void UTF8_BytePosition::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    // Classify the input data based on source information.
    PabloAST * prefix = pb.createAnd(basis[7], basis[6]);
    PabloAST * prefix2 = pb.createAnd(prefix, pb.createNot(basis[5]));
    PabloAST * prefix34 = pb.createAnd(prefix, basis[5]);
    PabloAST * prefix3 = pb.createAnd(prefix34, pb.createNot(basis[4]));
    PabloAST * prefix4 = pb.createAnd(prefix34, basis[4]);
    PabloAST * scope22 = pb.createAdvance(prefix2, 1);
    PabloAST * scope32 = pb.createAdvance(prefix3, 1);
    PabloAST * scope33 = pb.createAdvance(scope32, 1);
    PabloAST * scope42 = pb.createAdvance(prefix4, 1);
    PabloAST * scope43 = pb.createAdvance(scope42, 1);
    PabloAST * scope44 = pb.createAdvance(scope43, 1);
    PabloAST * ASCII = pb.createNot(basis[7]);
    PabloAST * u8_last = pb.createOr(ASCII, pb.createOr3(scope44, scope33, scope22));
    PabloAST * u8_secondlast = pb.createOr3(scope43, scope32, prefix2);
    PabloAST * u8_thirdlast = pb.createOr(scope42, prefix3);
    Var * positionsVar = getOutputStreamVar("positions");
    pb.createAssign(pb.createExtract(positionsVar, pb.getInteger(0)), u8_last);
    pb.createAssign(pb.createExtract(positionsVar, pb.getInteger(1)), u8_secondlast);
    pb.createAssign(pb.createExtract(positionsVar, pb.getInteger(2)), u8_thirdlast);
}

class UTF8_Target_Class : public pablo::PabloKernel {
public:
    UTF8_Target_Class
        (BuilderRef b,
         StreamSet * Positions, StreamSet * SpreadMask, StreamSet * FilterMask,
         StreamSet * TargetClass);
protected:
    void generatePabloMethod() override;
};

UTF8_Target_Class::UTF8_Target_Class
    (BuilderRef b,
     StreamSet * Positions, StreamSet * SpreadMask, StreamSet * FilterMask,
     StreamSet * TargetClass)
: PabloKernel(b, "UTF8_Target_Class",
{Binding{"positions", Positions, FixedRate(1), LookAhead(2)},
 Binding{"spreadmask", SpreadMask, FixedRate(1), LookAhead(2)},
 Binding{"filtermask", FilterMask}},
// output
{Binding{"target_class", TargetClass}}) {
}

void UTF8_Target_Class::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    Var * src_u8last = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(0));
    Var * src_secondlast = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(1));
    Var * src_thirdlast = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(2));
    PabloAST * src_prefix4 = pb.createNot(pb.createOr3(src_u8last, src_secondlast, src_thirdlast));
    Var * spreadmask = pb.createExtract(getInputStreamVar("spreadmask"), pb.getInteger(0));
    Var * filtermask = pb.createExtract(getInputStreamVar("filtermask"), pb.getInteger(0));
    // Insertions add up to 3 new UTF-8 bytes:
    // 1-3 bytes prior to a source ASCII byte to create a multibyte sequence,
    // 1-2 bytes prior to a 2-byte sequence to create a 3-4 byte sequence, or
    // 1 byte prior to a 3-byte sequence to create a 4-byte sequence.
    // Classify the new bytes.
    PabloAST * inserted = pb.createNot(spreadmask);
    PabloAST * new_secondlast = pb.createAnd(inserted, pb.createLookahead(src_u8last, 1));
    // Insertions can generate a new third last UTF-8 byte in two ways:
    // (a) Insertion of immediately before a second last UTF-8 position in the source.
    // (b) Insertion of two bytes before a last UTF-8 position in the source.
    PabloAST * i3a = pb.createAnd(inserted, pb.createLookahead(src_secondlast, 1));
    PabloAST * i3b = pb.createAnd3(inserted,
                                   pb.createNot(pb.createLookahead(spreadmask, 1)),
                                   pb.createLookahead(src_u8last, 2));
    PabloAST * new_thirdlast = pb.createOr(i3a, i3b);
    //
    // All other insertions are for a new prefix4.
    PabloAST * new_prefix4 = pb.createAnd(inserted,
                                          pb.createNot(pb.createOr(new_secondlast, new_thirdlast)));
    //
    PabloAST * secondlast = pb.createOr(pb.createAnd(filtermask, src_secondlast), new_secondlast);
    PabloAST * thirdlast = pb.createOr(pb.createAnd(filtermask, src_thirdlast), new_thirdlast);
    PabloAST * prefix4 = pb.createOr(pb.createAnd(filtermask, src_prefix4), new_prefix4);
    Var * targetClassVar = getOutputStreamVar("target_class");
    pb.createAssign(pb.createExtract(targetClassVar, pb.getInteger(0)), secondlast);
    pb.createAssign(pb.createExtract(targetClassVar, pb.getInteger(1)), thirdlast);
    pb.createAssign(pb.createExtract(targetClassVar, pb.getInteger(2)), prefix4);
}

class UTF8_CharacterTranslator : public pablo::PabloKernel {
public:
    UTF8_CharacterTranslator
        (BuilderRef b,
         StreamSet * Basis, StreamSet * XfrmBasis, StreamSet * TargetPositions, StreamSet * SpreadMask, StreamSet * FilterMask,
         StreamSet * Output);
protected:
    void generatePabloMethod() override;
private:
    unsigned mXfrmBits;
};

UTF8_CharacterTranslator::UTF8_CharacterTranslator
    (BuilderRef b,
     StreamSet * Basis, StreamSet * XfrmBasis, StreamSet * TargetPositions, StreamSet * SpreadMask, StreamSet * FilterMask,
     StreamSet * Output)
: PabloKernel(b, "u8_transform_bits_" + std::to_string(XfrmBasis->getNumElements()) + "x1",
{Binding{"basis", Basis, FixedRate(1), LookAhead(2)},
 Binding{"xfrm_basis", XfrmBasis, FixedRate(1), LookAhead(3)},
 Binding{"positions", TargetPositions},
 Binding{"spreadmask", SpreadMask},
 Binding{"filtermask", FilterMask}},
// output
{Binding{"output_basis", Output}}),
    mXfrmBits(XfrmBasis->getNumElements()) {
}

void UTF8_CharacterTranslator::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    Var * basisVar = getInputStreamVar("basis");
    std::vector<PabloAST *> basis(8);
    for (unsigned i = 0; i < 8; i++) {
        basis[i] = pb.createExtract(basisVar, pb.getInteger(i));
    }
    Var * xfrmVar = getInputStreamVar("xfrm_basis");
    std::vector<PabloAST *> xfrm_basis(mXfrmBits);
    for (unsigned i = 0; i < mXfrmBits; i++) {
        xfrm_basis[i] = pb.createExtract(xfrmVar, pb.getInteger(i));
    }
    Var * spreadmask = pb.createExtract(getInputStreamVar("spreadmask"), pb.getInteger(0));
    Var * filtermask = pb.createExtract(getInputStreamVar("filtermask"), pb.getInteger(0));
    Var * tgt_secondlast = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(0));
    Var * tgt_thirdlast = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(1));
    Var * tgt_prefix4 = pb.createExtract(getInputStreamVar("positions"), pb.getInteger(2));
    PabloAST * tgt_u8last = pb.createNot(pb.createOr3(tgt_secondlast, tgt_thirdlast, tgt_prefix4));
    //
    //  Initial ASCII bit movement:
    PabloAST * inserted = pb.createNot(spreadmask);
    PabloAST * deleted = pb.createNot(filtermask);
    PabloAST * bit6_ahead1 = pb.createLookahead(basis[6], 1);
    basis[0] = pb.createSel(pb.createAnd(tgt_secondlast, inserted), bit6_ahead1, basis[0]);
    PabloAST * suffix_to_ASCII = pb.createAnd(pb.createAdvance(deleted, 1), tgt_u8last);
    basis[6] = pb.createSel(suffix_to_ASCII, pb.createAdvance(basis[0], 1), basis[6]);
    //
    //  Now proceed to set up the correct UTF-8 bits encoding ASCII, prefixes
    //  and suffixes appropriately.
    //
    PabloAST * last_suffix = pb.createAdvance(tgt_secondlast, 1);
    PabloAST * tgt_ASCII = pb.createAnd(tgt_u8last, pb.createNot(last_suffix));
    PabloAST * tgt_prefix2 = pb.createAnd(tgt_secondlast,
                                          pb.createNot(pb.createAdvance(tgt_thirdlast, 1)));
    PabloAST * tgt_prefix3 = pb.createAnd(tgt_thirdlast,
                                          pb.createNot(pb.createAdvance(tgt_prefix4, 1)));
    PabloAST * tgt_prefix = pb.createOr3(tgt_prefix2, tgt_prefix3, tgt_prefix4);
    //
    //  Set bit 7 to 1 for prefix/suffix, 0 for ASCII
    basis[7] = pb.createNot(tgt_ASCII);
    //  Set bit 6 to 1 for prefix bytes, 0 for suffix bytes, unchanged for ASCII.
    basis[6] = pb.createSel(tgt_ASCII, basis[6], tgt_prefix);
    //  Clear bit 5 of prefix3 bytes converted to suffix bytes.
    PabloAST * prefix3_to_suffix =
        pb.createAnd3(tgt_thirdlast, spreadmask, pb.createAdvance(inserted, 1));
    basis[5] = pb.createAnd(basis[5], pb.createNot(prefix3_to_suffix));
    //  Set bit 5 of new prefix3/4 bytes bytes.
    basis[5] = pb.createOr3(basis[5], tgt_prefix3, tgt_prefix4);
    //  Set bit 4 of new prefix4 bytes bytes.
    basis[4] = pb.createOr(basis[4], tgt_prefix4);
    //
    //  Translate Unicode bits 0 through 5 at the u8last position.
    for (unsigned U_bit = 0; U_bit < 6; U_bit++) {
        if (U_bit < mXfrmBits) {
            unsigned u8_bit = U_bit;
            PabloAST * translated = pb.createXor(xfrm_basis[U_bit], basis[u8_bit]);
            basis[u8_bit] = pb.createSel(tgt_u8last, translated, basis[u8_bit]);
        }
    }
    // Translate bit 6 at ASCII positions.
    if (mXfrmBits > 6) {
        basis[6] = pb.createSel(tgt_ASCII, pb.createXor(xfrm_basis[6], basis[6]), basis[6]);
    }
    //  Translate Unicode bits 6 through 11 at the second last UTF-8 byte position.
    for (unsigned U_bit = 6; U_bit < 12; U_bit++) {
        if (U_bit < mXfrmBits) {
            unsigned u8_bit = U_bit - 6;
            PabloAST * xfrm_bit = pb.createLookahead(xfrm_basis[U_bit], 1);
            PabloAST * translated = pb.createXor(xfrm_bit, basis[u8_bit]);
            basis[u8_bit] = pb.createSel(tgt_secondlast, translated, basis[u8_bit]);
        }
    }
    //  Translate Unicode bits 12 through 17 at the third last UTF-8 byte position.
    for (unsigned U_bit = 12; U_bit < 18; U_bit++) {
        if (U_bit < mXfrmBits) {
            unsigned u8_bit = U_bit - 12;
            PabloAST * xfrm_bit = pb.createLookahead(xfrm_basis[U_bit], 2);
            PabloAST * translated = pb.createXor(xfrm_bit, basis[u8_bit]);
            basis[u8_bit] = pb.createSel(tgt_thirdlast, translated, basis[u8_bit]);
        }
    }
    //  Translate Unicode bits 18 through 20 at the UTF-8 prefix4 byte position.
    for (unsigned U_bit = 18; U_bit < 21; U_bit++) {
        if (U_bit < mXfrmBits) {
            unsigned u8_bit = U_bit - 18;
            PabloAST * xfrm_bit = pb.createLookahead(xfrm_basis[U_bit], 3);
            PabloAST * translated = pb.createXor(xfrm_bit, basis[u8_bit]);
            basis[u8_bit] = pb.createSel(tgt_prefix4, translated, basis[u8_bit]);
        }
    }
    Var * translatedVar = getOutputStreamVar("output_basis");
    for (unsigned i = 0; i < 8; i++) {
        pb.createAssign(pb.createExtract(translatedVar, pb.getInteger(i)), basis[i]);
    }
}

class ApplyTransform : public pablo::PabloKernel {
public:
    ApplyTransform(BuilderRef b,
                   UCD::CodePointPropertyObject * p,
                   StreamSet * Basis, StreamSet * Output);
protected:
    void generatePabloMethod() override;
private:
    UCD::CodePointPropertyObject * mPropertyObject;
};

ApplyTransform::ApplyTransform (BuilderRef b,
                                UCD::CodePointPropertyObject * p,
                                StreamSet * Basis, StreamSet * Output)
: PabloKernel(b, getPropertyEnumName(p->getPropertyCode()) + "_transformer_" + std::to_string(Basis->getNumElements()) + "x1",
// inputs
{Binding{"basis", Basis}},
// output
{Binding{"output_basis", Output}}),
    mPropertyObject(p) {
}

void ApplyTransform::generatePabloMethod() {
    PabloBuilder pb(getEntryScope());
    //const UCD::UnicodeSet & nullSet = mPropertyObject->GetNullSet();
    std::vector<UCD::UnicodeSet> & xfrms = mPropertyObject->GetBitTransformSets();
    std::vector<re::CC *> xfrm_ccs;
    for (auto & b : xfrms) {
        xfrm_ccs.push_back(re::makeCC(b, &cc::Unicode));
    }
    UTF::UTF_Compiler unicodeCompiler(getInput(0), pb);
    std::vector<Var *> xfrm_vars;
    for (unsigned i = 0; i < xfrm_ccs.size(); i++) {
        xfrm_vars.push_back(pb.createVar("xfrm_cc_" + std::to_string(i), pb.createZeroes()));
        unicodeCompiler.addTarget(xfrm_vars[i], xfrm_ccs[i]);
    }
    if (LLVM_UNLIKELY(re::AlgorithmOptionIsSet(re::DisableIfHierarchy))) {
        unicodeCompiler.compile(UTF::UTF_Compiler::IfHierarchy::None);
    } else {
        unicodeCompiler.compile();
    }
    std::vector<PabloAST *> basis = getInputStreamSet("basis");
    std::vector<PabloAST *> transformed(basis.size());
    Var * const out = getOutputStreamVar("output_basis");
    for (unsigned i = 0; i < basis.size(); i++) {
        if (i < xfrm_vars.size()) {
            transformed[i] = pb.createXor(xfrm_vars[i], basis[i]);
        } else {
            transformed[i] = basis[i];
        }
        pb.createAssign(pb.createExtract(out, pb.getInteger(i)), transformed[i]);
    }
}

typedef void (*XfrmFunctionType)(uint32_t fd, ParabixIllustrator * illustrator);

XfrmFunctionType generatePipeline(CPUDriver & pxDriver,
                                  UCD::CodePointPropertyObject * p,
                                  ParabixIllustrator & illustrator) {
    // A Parabix program is build as a set of kernel calls called a pipeline.
    // A pipeline is construction using a Parabix driver object.
    auto & b = pxDriver.getBuilder();
    auto P = pxDriver.makePipeline({Binding{b->getInt32Ty(), "inputFileDecriptor"},
                                    Binding{b->getIntAddrTy(), "illustratorAddr"}}, {});
    //  The program will use a file descriptor as an input.
    Scalar * fileDescriptor = P->getInputScalar("inputFileDecriptor");
    //   If the --illustrator-width= parameter is specified, bitstream
    //   data is to be displayed.
    Scalar * illustratorAddr = nullptr;
    if (codegen::IllustratorDisplay > 0) {
        illustratorAddr = P->getInputScalar("illustratorAddr");
        illustrator.registerIllustrator(illustratorAddr);
    }
    // File data from mmap
    StreamSet * ByteStream = P->CreateStreamSet(1, 8);
    //  MMapSourceKernel is a Parabix Kernel that produces a stream of bytes
    //  from a file descriptor.
    P->CreateKernelCall<MMapSourceKernel>(fileDescriptor, ByteStream);
    SHOW_BYTES(ByteStream);

    //  The Parabix basis bits representation is created by the Parabix S2P kernel.
    StreamSet * BasisBits = P->CreateStreamSet(8, 1);
    P->CreateKernelCall<S2PKernel>(ByteStream, BasisBits);
    SHOW_BIXNUM(BasisBits);

    std::vector<UCD::UnicodeSet> & insertion_bixnum = p->GetUTF8insertionBixNum();
    unsigned bix_bits = insertion_bixnum.size();

    StreamSet * ExpandedBasis = BasisBits;
    StreamSet * SpreadMask = nullptr;
    if (bix_bits > 0) {
        std::vector<re::CC *> insertion_ccs;
        for (auto & b : insertion_bixnum) {
            insertion_ccs.push_back(re::makeCC(b, &cc::Unicode));
        }
        StreamSet * InsertBixNum = P->CreateStreamSet(bix_bits);
        P->CreateKernelCall<CharClassesKernel>(insertion_ccs, BasisBits, InsertBixNum);
        SHOW_BIXNUM(InsertBixNum);

        StreamSet * AdjustedBixNum = P->CreateStreamSet(bix_bits);
        P->CreateKernelCall<AdjustU8bixnum>(BasisBits, InsertBixNum, AdjustedBixNum);
        SHOW_BIXNUM(AdjustedBixNum);

        SpreadMask = InsertionSpreadMask(P, AdjustedBixNum, InsertPosition::Before);
        SHOW_STREAM(SpreadMask);

        ExpandedBasis = P->CreateStreamSet(8, 1);
        SpreadByMask(P, SpreadMask, BasisBits, ExpandedBasis);
        SHOW_BIXNUM(ExpandedBasis);
    } else {
        llvm::errs() << "bit_bits = 0\n";
    }

    StreamSet * U8_Positions = P->CreateStreamSet(3, 1);
    P->CreateKernelCall<UTF8_BytePosition>(ExpandedBasis, U8_Positions);
    SHOW_BIXNUM(U8_Positions);

    StreamSet * SelectionMask = nullptr;
    std::vector<UCD::UnicodeSet> & deletion_bixnum = p->GetUTF8deletionBixNum();
    unsigned del_bix_bits = deletion_bixnum.size();
    if (del_bix_bits > 0) {
        std::vector<re::CC *> deletion_ccs;
        for (auto & b : deletion_bixnum) {
            deletion_ccs.push_back(re::makeCC(b, &cc::Unicode));
        }

        StreamSet * DeletionBixNum = P->CreateStreamSet(del_bix_bits);
        P->CreateKernelCall<CharClassesKernel>(deletion_ccs, ExpandedBasis, DeletionBixNum);
        SHOW_BIXNUM(DeletionBixNum);

        SelectionMask = P->CreateStreamSet(1);
        P->CreateKernelCall<CreateU8delMask>(ExpandedBasis, DeletionBixNum, SelectionMask);
        SHOW_STREAM(SelectionMask);
    } else {
        llvm::errs() << "del_bit_bits = 0\n";
    }
    StreamSet * TargetClass = P->CreateStreamSet(3, 1);
    P->CreateKernelCall<UTF8_Target_Class>(U8_Positions, SpreadMask, SelectionMask, TargetClass);
    SHOW_BIXNUM(TargetClass);

    std::vector<UCD::UnicodeSet> & xfrms = p->GetBitTransformSets();
    std::vector<re::CC *> xfrm_ccs;
    for (auto & b : xfrms) {
        xfrm_ccs.push_back(re::makeCC(b, &cc::Unicode));
    }
    StreamSet * XfrmBasis = P->CreateStreamSet(xfrm_ccs.size());
    P->CreateKernelCall<CharClassesKernel>(xfrm_ccs, ExpandedBasis, XfrmBasis);
    SHOW_BIXNUM(XfrmBasis);

    StreamSet * Translated = P->CreateStreamSet(8);
    P->CreateKernelCall<UTF8_CharacterTranslator>(ExpandedBasis, XfrmBasis, TargetClass, SpreadMask, SelectionMask, Translated);
    SHOW_BIXNUM(Translated);

    StreamSet * OutputBasis = P->CreateStreamSet(8);
    FilterByMask(P, SelectionMask, Translated, OutputBasis);
    SHOW_BIXNUM(OutputBasis);

    StreamSet * OutputBytes = P->CreateStreamSet(1, 8);
    P->CreateKernelCall<P2SKernel>(OutputBasis, OutputBytes);
    //SHOW_BYTES(OutputBytes);

    P->CreateKernelCall<StdOutKernel>(OutputBytes);
    return reinterpret_cast<XfrmFunctionType>(P->compile());
}

int main(int argc, char *argv[]) {
    //  ParseCommandLineOptions uses the LLVM CommandLine processor, but we also add
    //  standard Parabix command line options such as -help, -ShowPablo and many others.
    codegen::ParseCommandLineOptions(argc, argv, {&Xch_Options, pablo::pablo_toolchain_flags(), codegen::codegen_flags()});
    ParabixIllustrator illustrator(codegen::IllustratorDisplay);

    UCD::property_t prop = UCD::getPropertyCode(XfrmProperty);
    UCD::PropertyObject * propObj = UCD::getPropertyObject(prop);
    if (UCD::CodePointPropertyObject * p = dyn_cast<UCD::CodePointPropertyObject>(propObj)) {
        CPUDriver driver("xfrm_function");
        //  Build and compile the Parabix pipeline by calling the Pipeline function above.
        XfrmFunctionType fn = generatePipeline(driver, p, illustrator);
        //  The compile function "fn"  can now be used.   It takes a file
        //  descriptor as an input, which is specified by the filename given by
        //  the inputFile command line option.]

        const int fd = open(inputFile.c_str(), O_RDONLY);
        if (LLVM_UNLIKELY(fd == -1)) {
            llvm::errs() << "Error: cannot open " << inputFile << " for processing. Skipped.\n";
        } else {
            fn(fd, &illustrator);
            close(fd);
            if (codegen::IllustratorDisplay > 0) {
                illustrator.displayAllCapturedData();
            }
        }
    } else {
        llvm::report_fatal_error("Expecting codepoint property");
    }
    return 0;
}
