/*
 *  Copyright (c) 2018 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#ifndef TO_UTF8_H
#define TO_UTF8_H

#include <unicode/utf/utf_encoder.h>
#include <re/adt/adt.h>
#include <re/transforms/re_transformer.h>

namespace re {class CC;}
namespace re {

class EncodingTransformer : public RE_Transformer {
public:
    const cc::Alphabet * getIndexingAlphabet() const {return mIndexingAlphabet;}
    const cc::Alphabet * getEncodingAlphabet() const {return mEncodingAlphabet;}
protected:
    EncodingTransformer(std::string transformationName,
                        const cc::Alphabet * indexingAlphabet,
                        const cc::Alphabet * encodingAlphabet) :
    RE_Transformer(transformationName),
    mIndexingAlphabet(indexingAlphabet),
    mEncodingAlphabet(encodingAlphabet) {}
protected:
    const cc::Alphabet * mIndexingAlphabet;
    const cc::Alphabet * mEncodingAlphabet;
};

class UTF8_Transformer : public EncodingTransformer {
public:
    UTF8_Transformer(bool useInternalNaming = false);
protected:
    RE * transformCC(CC * cc) override;
    RE * rangeCodeUnits(codepoint_t lo, codepoint_t hi, unsigned index, const unsigned lgth);
    RE * rangeToUTF8(codepoint_t lo, codepoint_t hi);

private:
    UTF_Encoder mEncoder;
    bool mInternalNaming;
};

//
//  Transform all Unicode CCs to an equivalent expansion
//  using UTF8 CCs.   Embed each transformed Unicode CC in
//  a name object.
//
RE * toUTF8(RE * r, bool useInternalNaming = false);
}

#endif // TO_UTF8_H
