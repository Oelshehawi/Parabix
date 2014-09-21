/*
 *  Copyright (c) 2014 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#include "re_parser.h"
#include "re_alt.h"
#include "re_end.h"
#include "re_rep.h"
#include "re_seq.h"
#include "re_start.h"
#include "parsefailure.h"
#include <algorithm>

RE * RE_Parser::parse_re(const std::string & regular_expression, const bool allow_escapes_within_charset) {
    RE_Parser parser(regular_expression, allow_escapes_within_charset);
    RE * re = parser.parse_alt(false);
    if (re == nullptr) {
        throw ParseFailure("An unexpected parsing error occurred!");
    }
    return re;
}

inline RE_Parser::RE_Parser(const std::string & regular_expression, const bool allow_escapes_within_charset)
: _cursor(regular_expression.begin())
, _end(regular_expression.end())
, _allow_escapes_within_charset(allow_escapes_within_charset)
{

}

RE * RE_Parser::parse_alt(const bool subexpression) {
    std::unique_ptr<Alt> alt(new Alt());
    for (;;) {
        alt->push_back(parse_seq());
        if (_cursor == _end || *_cursor != '|') {
            break;
        }
        ++_cursor; // advance past the alternation character '|'
    }
    if (alt->empty())
    {
        throw NoRegularExpressionFound();
    }
    else if (subexpression) {
        if (_cursor == _end || *_cursor != ')') {
            throw ParseFailure("Parenthesization error!");
        }
        ++_cursor;
    }
    else if (_cursor != _end) { // !subexpression
        throw ParseFailure("Cannot fully parse statement!");
    }

    RE * re;
    if (alt->size() == 1) {
        re = alt->back();
        alt->pop_back();
    }
    else {
        re = alt.release();
    }
    return re;
}

inline RE * RE_Parser::parse_seq() {
    std::unique_ptr<Seq> seq(new Seq());
    for (;;) {
        RE * re = parse_next_token();
        if (re == nullptr) {
            break;
        }
        seq->push_back(extend_item(re));
    }
    if (seq->empty())
    {
        throw NoRegularExpressionFound();
    }

    RE * re;
    if (seq->size() == 1) {
        re = seq->back();
        seq->pop_back();
    }
    else {
        re = seq.release();
    }
    return re;
}

RE * RE_Parser::parse_next_token() {
    RE * re = nullptr;
    if (_cursor != _end) {
        switch (*_cursor) {
            case '(':
                ++_cursor;
                re = parse_alt(true);
                break;
            case '^':
                ++_cursor;
                re = new Start;
                break;
            case '$':
                ++_cursor;
                re = new End;
                break;
            case '|': case ')':
                break;
            case '*': case '+': case '?': case ']': case '{': case '}':
                throw ParseFailure("Illegal metacharacter usage!");
            case '[':
                re = parse_charset();
                break;
            case '.': // the 'any' metacharacter
                re = parse_any_character();
                break;
            default:
                re = parse_literal();
                break;
        }
    }
    return re;
}

CC * RE_Parser::parse_any_character() {
    CC * cc = new CC();
    cc->insert_range(0, 9);
    cc->insert_range(11, 0x10FFFF);
    ++_cursor;
    return cc;
}

RE * RE_Parser::extend_item(RE * re) {
    if (_cursor == _end) {
        return re;
    }
    switch (*_cursor) {
        case '*':
            ++_cursor; // skip past the '*'
            re = new Rep(re, 0, UNBOUNDED_REP);
            break;
        case '?':
            ++_cursor; // skip past the '?'
            re = new Rep(re, 0, 1);
            break;
        case '+':
            ++_cursor; // skip past the '+'
            re = new Rep(re, 1, UNBOUNDED_REP);
            break;
        case '{':
            re = parse_range_bound(re);
            break;
        default:
            return re;
    }
    // this only occurs if we encountered one of the non-default cases above.
    return extend_item(re);
}

inline RE * RE_Parser::parse_range_bound(RE * re) {
    ++_cursor;
    throw_incomplete_expression_error_if_end_of_stream();
    Rep * rep = nullptr;
    unsigned lower_bound;
    if (*_cursor == ',') {
        ++_cursor;
        lower_bound = 0;
    }
    else {
        lower_bound = parse_int();
    }
    throw_incomplete_expression_error_if_end_of_stream();
    if (*_cursor == '}') {
        rep = new Rep(re, lower_bound, lower_bound);
    }
    else if (*_cursor != ',') {
        throw BadLowerBound();
    }
    else { // [^,}]
        ++_cursor;
        throw_incomplete_expression_error_if_end_of_stream();
        if (*_cursor == '}') {
            rep = new Rep(re, lower_bound, UNBOUNDED_REP);
        }
        else {
            const unsigned upper_bound = parse_int();
            if (*_cursor != '}') {
                throw BadUpperBound();
            }
            rep = new Rep(re, lower_bound, upper_bound);
        }
    }
    ++_cursor;
    return rep;
}

inline RE * RE_Parser::parse_literal() {
    // handle the escaped metacharacter (assuming it is one)
    if (*_cursor == '\\') {
        return parse_escaped_metacharacter();
    }
    else {
        return new CC(parse_utf8_codepoint());
    }
}

inline RE * RE_Parser::parse_escaped_metacharacter() {
    ++_cursor;
    throw_incomplete_expression_error_if_end_of_stream();
    bool negated = false;
    switch (*_cursor) {
        case '(': case ')': case '*': case '+':
        case '.': case '?': case '[': case '\\':
        case ']': case '{': case '|': case '}':
            return new CC(*_cursor++);
        case 'u':
            return new CC(parse_hex());
        case 'P':
            negated = true;
        case 'p':
            return parse_unicode_category(negated);
    }
    throw ParseFailure("Illegal backslash escape!");
}

unsigned RE_Parser::parse_utf8_codepoint() {
    unsigned c = static_cast<unsigned>(*_cursor++);
    if (c > 0x80) { // if non-ascii
        if (c < 0xC2) {
            throw InvalidUTF8Encoding();
        }
        else { // [0xC2, 0xFF]
            unsigned bytes = 0;
            if (c < 0xE0) { // [0xC2, 0xDF]
                c &= 0x1F;
                bytes = 1;
            }
            else if (c < 0xF0) { // [0xE0, 0xEF]
                c &= 0x0F;
                bytes = 2;
            }
            else { // [0xF0, 0xFF]
                c &= 0x0F;
                bytes = 3;
            }
            while (--bytes) {
                if (++_cursor == _end || (*_cursor & 0xC0) != 0x80) {
                    throw InvalidUTF8Encoding();
                }
                c = (c << 6) | static_cast<unsigned>(*_cursor & 0x3F);
            }
        }
    }
    return c;
}

inline Name * RE_Parser::parse_unicode_category(const bool negated) {
    if (++_cursor != _end && *_cursor == '{') {
        std::unique_ptr<Name> name = std::unique_ptr<Name>(new Name);
        name->setType(Name::UnicodeCategory);
        name->setNegated(negated);
        const cursor_t start = _cursor + 1;
        for (;;) {
            ++_cursor;
            if (_cursor == _end) {
                throw UnclosedUnicodeCharacterClass();
            }
            if (*_cursor == '}') {
                break;
            }
            ++_cursor;
        }
        name->setName(std::string(start, _cursor));
        if (isValidUnicodeCategoryName(name)) {
            ++_cursor;
            return name.release();
        }
    }
    throw ParseFailure("Incorrect Unicode character class format!");
}

RE * RE_Parser::parse_charset() {
    std::unique_ptr<CC> cc(new CC());
    bool negated = false;
    bool included_closing_square_bracket = false;
    cursor_t start = ++_cursor;
    while (_cursor != _end) {
        bool literal = true;
        switch (*_cursor) {
            case '^':
                // If the first character after the [ is a ^ (caret) then the matching character class is complemented.
                if (start == _cursor) {
                    negated = true;
                    start = ++_cursor; // move the start ahead incase the next character is a [ or -
                    literal = false;                    
                }
                break;
            case ']':
                // To include a ], put it immediately after the opening [ or [^; if it occurs later it will
                // close the bracket expression.
                if (start == _cursor) {
                    cc->insert1(']');
                    ++_cursor;
                    included_closing_square_bracket = true;
                    literal = false;
                    break;
                }
                if (negated) {
                    negate_cc(cc);
                }
                ++_cursor;
                return cc.release();
            // The hyphen (-) is not treated as a range separator if it appears first or last, or as the
            // endpoint of a range.
            case '-':
                if (true) {
                    literal = false;
                    const cursor_t next = _cursor + 1;
                    if (next == _end) {
                        goto parse_failed;
                    }
                    if ((start == _cursor) ? (*next != '-') : (*next == ']')) {
                        _cursor = next;
                        cc->insert1('-');
                        break;
                    }
                }
                throw ParseFailure("Invalid Lower Range Bound!");
            // case ':':
        }
        if (literal) {
            unsigned low;
            if (parse_charset_literal(low)) {
                // the previous literal allows for a - to create a range; test for it
                if (_cursor == _end) {
                    break; // out of loop to failure handling
                }
                if (*_cursor == '-') { // in range unless the next character is a ']'
                    if (++_cursor == _end) {
                        break; // out of loop to failure handling
                    }
                    if (*_cursor != ']') {
                        unsigned high;
                        if (!parse_charset_literal(high)) {
                            throw ParseFailure("Invalid Upper Range Bound!");
                        }
                        cc->insert_range(low, high);
                    }
                    continue;
                }
            }
            cc->insert1(low);
        }
    }
parse_failed:
    if (included_closing_square_bracket) {
        throw ParseFailure("One ']' cannot close \"[]\" or \"[^]\"; use \"[]]\" or \"[^]]\" instead.");
    }
    else {
        throw UnclosedCharacterClass();
    }
}

inline bool RE_Parser::parse_charset_literal(unsigned & literal) {
    if (_cursor == _end) {
        return false;
    }
    if (*_cursor == '\\') {
        if (++_cursor == _end) {
            return false;
        }
        switch (*_cursor) {
            case '(': case ')': case '*': case '+':
            case '.': case '?': case '[': case '\\':
            case ']': case '{': case '|': case '}':
                if (_allow_escapes_within_charset) {
                    literal = *_cursor++;
                    return true;
                }
                break;
            case 'u':
                literal = parse_hex();
                return true;
            // probably need to pass in the CC to handle \w, \s, etc...
        }
        throw ParseFailure("Unknown charset escape!");
    }
    else {
        literal = parse_utf8_codepoint();
        return true;
    }
    return false;
}

unsigned RE_Parser::parse_int() {
    unsigned value = 0;
    for (; _cursor != _end; ++_cursor) {
        if (!isdigit(*_cursor)) {
            break;
        }
        value *= 10;
        value += static_cast<int>(*_cursor) - 48;
    }
    return value;
}

unsigned RE_Parser::parse_hex() {
    if (++_cursor != _end && *_cursor == '{') {
        unsigned value = 0;
        for (++_cursor; _cursor != _end; ++_cursor) {
            const char t = *_cursor;
            if (t == '}') {
                ++_cursor;
                return value;
            }
            value *= 16;
            if (t >= '0' && t <= '9') {
                value |= (t - '0');
            }
            else if ((t | 32) >= 'a' && (t | 32) <= 'f') {
                value |= ((t | 32) - 'a') + 10;
            }
            else {
                break;
            }
        }
    }
    throw ParseFailure("Bad Unicode hex notation!");
}

inline void RE_Parser::negate_cc(std::unique_ptr<CC> & cc) {
    cc->negate_class();
    cc->remove1(10);
}

bool RE_Parser::isValidUnicodeCategoryName(const std::unique_ptr<Name> & name) {
    static const char * SET_OF_VALID_CATEGORIES[] = {
        "C", "Cc", "Cf", "Cn", "Co", "Cs",
        "L", "L&", "Lc", "Ll", "Lm", "Lo", "Lt", "Lu",
        "M", "Mc", "Me", "Mn",
        "N", "Nd", "Nl", "No",
        "P", "Pc", "Pd", "Pe", "Pf", "Pi", "Po", "Ps",
        "S", "Sc", "Sk", "Sm", "So",
        "Z", "Zl", "Zp", "Zs"
    };
    // NOTE: this method isn't as friendly as using an unordered_set for VALID_CATEGORIES since it requires
    // that the set is in ALPHABETICAL ORDER; however it ought to have less memory overhead than an
    // unordered_set and roughly equivalent speed.
    return std::binary_search(std::begin(SET_OF_VALID_CATEGORIES), std::end(SET_OF_VALID_CATEGORIES), name->getName());
}

inline void RE_Parser::throw_incomplete_expression_error_if_end_of_stream() const {
    if (_cursor == _end) throw IncompleteRegularExpression();
}
