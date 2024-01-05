
/*
 *  Copyright (c) 2024 International Characters, Inc.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters, Inc.
 *
 *  This file is generated by UCD_properties.py - manual edits may be lost.
 *  CompositionExclusions
 */

#include <unicode/core/unicode_set.h>
#include <unicode/data/PropertyAliases.h>
#include <unicode/data/PropertyObjects.h>
#include <unicode/data/PropertyValueAliases.h>

namespace UCD {
    namespace CE_ns {
        /** Code Point Ranges for CE
        [0958, 095f], [09dc, 09dd], [09df, 09df], [0a33, 0a33],
        [0a36, 0a36], [0a59, 0a5b], [0a5e, 0a5e], [0b5c, 0b5d],
        [0f43, 0f43], [0f4d, 0f4d], [0f52, 0f52], [0f57, 0f57],
        [0f5c, 0f5c], [0f69, 0f69], [0f76, 0f76], [0f78, 0f78],
        [0f93, 0f93], [0f9d, 0f9d], [0fa2, 0fa2], [0fa7, 0fa7],
        [0fac, 0fac], [0fb9, 0fb9], [2adc, 2adc], [fb1d, fb1d],
        [fb1f, fb1f], [fb2a, fb36], [fb38, fb3c], [fb3e, fb3e],
        [fb40, fb41], [fb43, fb44], [fb46, fb4e], [1d15e, 1d164],
        [1d1bb, 1d1c0]**/


        namespace {
        const static UnicodeSet::run_t __codepoint_set_runs[] = {
        {Empty, 74}, {Mixed, 1}, {Empty, 3}, {Mixed, 1}, {Empty, 2},
        {Mixed, 2}, {Empty, 7}, {Mixed, 1}, {Empty, 31}, {Mixed, 4},
        {Empty, 216}, {Mixed, 1}, {Empty, 1665}, {Mixed, 3}, {Empty, 1711},
        {Mixed, 2}, {Empty, 1}, {Mixed, 2}, {Empty, 31089}};
        const static UnicodeSet::bitquad_t  __codepoint_set_quads[] = {
        0xff000000, 0xb0000000, 0x00480000, 0x4e000000, 0x30000000,
        0x10842008, 0x01400200, 0x20080000, 0x02001084, 0x10000000,
        0xa0000000, 0x5f7ffc00, 0x00007fdb, 0xc0000000, 0x0000001f,
        0xf8000000, 0x00000001};
        }

        const static UnicodeSet codepoint_set{const_cast<UnicodeSet::run_t *>(__codepoint_set_runs), 19, 0, const_cast<UnicodeSet::bitquad_t *>(__codepoint_set_quads), 17, 0};

        static BinaryPropertyObject property_object{CE, std::move(codepoint_set)};
    }
PropertyObject * get_CE_PropertyObject() {  return & CE_ns::property_object; }
}
