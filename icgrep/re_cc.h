/*
 *  Copyright (c) 2014 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#ifndef RE_CC_H
#define RE_CC_H

#include "re_re.h"

#include <iostream>
#include <string>
#include <sstream>
#include <utility>
#include <vector>


struct CharSetItem{
    int lo_codepoint;
    int hi_codepoint;
};

class CC : public RE
{
public:
    CC();
    CC(int codepoint);
    CC(int lo_codepoint, int hi_codepoint);
    CC(CC* cc1, CC* cc2);
    ~CC();
    std::vector<CharSetItem> getItems();
    std::string getName();
    std::string getId();
    bool is_member(int codepoint);
    void insert1(int codepoint);
    void insert_range(int lo_codepoint,int hi_codepoint);
    void negate_class();
    void remove1(int codepoint);
    void remove_range(int lo_codepoint,int hi_codepoint);

protected:
    static int msCSIidx;
private:
    static const int mUnicodeMax = 0x10FFFF;

    void gensym_name();
    bool is_member_helper(int codepoint, int idx);
    void joinCharSets(std::vector<CharSetItem> items1);
    void joinCharSets_helper(std::vector<CharSetItem> items1, int idx);
    void insert_range_helper(int lo_codepoint, int hi_codepoint, int idx);
    void negate_class_helper(int idx, int b);
    void remove_range_helper(int lo_codepoint, int hi_codepoint, int idx);

    std::vector<CharSetItem> mSparseCharSet;
    std::string mId;
};

#endif // RE_CC_H
