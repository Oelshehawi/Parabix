/*
 *  Copyright (c) 2019 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */
#ifndef JSON_KERNEL_H
#define JSON_KERNEL_H

#include <pablo/pablo_kernel.h>
#include <kernel/core/kernel_builder.h>

namespace kernel {

// This enum MUST reflect the type Lex on json.pablo file
enum Lex {
    lCurly = 0,
    rCurly,
    lBracket,
    rBracket,
    colon,
    comma,
    dQuote,
    hyphen,
    digit,
    backslash,
    n, // # first letter of null
    f, // # first letter of false
    t, // # first letter of true
    ws
};

enum KwMarker {
    kwNullEnd = 0,
    kwTrueEnd,
    kwFalseEnd,
};

/*
    Given the JSON lex for characters backslash and double quotes,
    this kernel returns the marker of a JSON string, based on paper
    Parsing Gigabytes of JSON per Second (Daniel Lemire and Geoff Langdale)

             json: { "key1\"": value1, "key2"  : null }
    input example: ..1.....11..........1....1..........
    output marker: ..1......1..........1....1..........
      output span: ...111111............1111...........
*/
class JSONStringMarker : public pablo::PabloKernel {
public:
    JSONStringMarker(const std::unique_ptr<KernelBuilder> & b,
                     StreamSet * const backslash, StreamSet * const dQuotes,
                     StreamSet * strMarker, StreamSet * strSpan)
    : pablo::PabloKernel(b,
                         "jsonStrMarker",
                         {Binding{"backslash", backslash}, Binding{"dQuotes", dQuotes}},
                         {Binding{"marker", strMarker}, Binding{"span", strSpan}}) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

/*
   Marks keywords letters such as l', 'a', 's', 'r', 'u', 'e',
   joining it at the end with 'n', 't' and 'f'

            json: { "keynull": false, "keyt": true }
   input example: ......1......1..........1...1.....
          output:..................1.............1..

    Note: we do not return the beginning of the marker here because lookahead
    only works on input streams, so this will be done in a further step.
*/
class JSONKeywordEndMarker : public pablo::PabloKernel {
public:
    JSONKeywordEndMarker(const std::unique_ptr<KernelBuilder> & b,
                      StreamSet * const basis,
                      std::vector<StreamSet *> literals, StreamSet * const strSpan,
                      StreamSet * kwMarker)
    : pablo::PabloKernel(b,
                         "jsonKeywordMarker",
                         {
                            Binding{"basis", basis},
                            Binding{"n", literals[0]},
                            Binding{"t", literals[1]},
                            Binding{"f", literals[2]},
                            Binding{"strSpan", strSpan}
                         },
                         {
                            Binding{"kwEndMarker", kwMarker},
                         }) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

/*
   Finds symbols used in numbers such as 'e', 'E', '.'
   and join them at the end if they match the expression:
   \-?(0|[1-9][0-9]*)(.[0-9]+)?([Ee][+-]?[0-9]+)?
*/
class JSONNumberSpan : public pablo::PabloKernel {
public:
    JSONNumberSpan(const std::unique_ptr<KernelBuilder> & b,
                   StreamSet * const basis, StreamSet * const lex, StreamSet * const strSpan,
                   StreamSet * nbrLex, StreamSet * nbrSpan, StreamSet * nbrErr)
    : pablo::PabloKernel(b,
                         "jsonNumberMarker",
                         {Binding{"basis", basis, FixedRate(1), LookAhead(1)}, Binding{"lex", lex}, Binding{"strSpan", strSpan}},
                         {Binding{"nbrLex", nbrLex}, Binding{"nbrSpan", nbrSpan}, Binding{"nbrErr", nbrErr}}) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

class JSONFindKwAndExtraneousChars : public pablo::PabloKernel {
    public:
    JSONFindKwAndExtraneousChars(const std::unique_ptr<KernelBuilder> & b,
                        StreamSet * const combinedSpans, StreamSet * const kwEndMarkers,
                        StreamSet * const kwMarker, StreamSet * extraErr)
    : pablo::PabloKernel(b,
                         "jsonFindKwAndExtraneousChars",
                         {Binding{"combinedSpans", combinedSpans}, Binding{"kwEndMarkers", kwEndMarkers, FixedRate(1), LookAhead(4)}},
                         {Binding{"kwMarker", kwMarker}, Binding{"extraErr", extraErr}}) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

/*
 * Clean lexer in case there are still 'dirty' chars in the string span
 *        json: { "ke{1": value1, "ke}2"  : null }
 *         span: ...1111............1111...........
 *  lexIn.lCurly 1....1............................
 *  lexIn.rCurly .....................1...........1
 *  lexIn.lCurly 1.................................
 *  lexIn.rCurly .................................1
*/
class JSONLexSanitizer : public pablo::PabloKernel {
public:
    JSONLexSanitizer(const std::unique_ptr<KernelBuilder> & b,
                     StreamSet * const stringSpan, StreamSet * const validDQuotes, StreamSet * const lexIn,
                     StreamSet * lexOut)
    : pablo::PabloKernel(b,
                         "jsonLexSanitizer",
                         {Binding{"strSpan", stringSpan}, Binding{"validDQuotes", validDQuotes}, Binding{"lexIn", lexIn}},
                         {Binding{"lexOut", lexOut}}) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

class JSONErrsSanitizer : public pablo::PabloKernel {
public:
    JSONErrsSanitizer(const std::unique_ptr<KernelBuilder> & b, StreamSet * const ws, StreamSet * const errsIn, StreamSet * errsOut)
    : pablo::PabloKernel(b,
                         "jsonErrsSanitizer",
                         {Binding{"ws", ws}, Binding{"errsIn", errsIn}},
                         {Binding{"errsOut", errsOut}}) {}
    bool isCachable() const override { return true; }
    bool hasSignature() const override { return false; }
protected:
    void generatePabloMethod() override;
};

}

#endif
