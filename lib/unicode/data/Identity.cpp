
/*
 *  Part of the Parabix Project, under the Open Software License 3.0.
 *  SPDX-License-Identifier: OSL-3.0
 *
 *  This file is generated by UCD_properties.py - manual edits may be lost.
 *  Identity
 */

#include <unicode/core/unicode_set.h>
#include <unicode/data/PropertyAliases.h>
#include <unicode/data/PropertyObjects.h>
#include <unicode/data/PropertyValueAliases.h>

namespace UCD {
    namespace IDENTITY_ns {
        /** Code Point Ranges for identity mapping to <none>
        **/

        
        namespace {
        const static UnicodeSet::run_t __null_codepoint_set_runs[] = {
        {Empty, 34816}};
        const static UnicodeSet::bitquad_t * const __null_codepoint_set_quads = nullptr;
        }

        const static UnicodeSet null_codepoint_set{const_cast<UnicodeSet::run_t *>(__null_codepoint_set_runs), 1, 0, const_cast<UnicodeSet::bitquad_t *>(__null_codepoint_set_quads), 0, 0};



        /** Code Point Ranges for identity mapping to <codepoint>
        [0000, 10ffff]**/

        
        namespace {
        const static UnicodeSet::run_t __reflexive_set_runs[] = {
        {Full, 34816}};
        const static UnicodeSet::bitquad_t * const __reflexive_set_quads = nullptr;
        }

        const static UnicodeSet reflexive_set{const_cast<UnicodeSet::run_t *>(__reflexive_set_runs), 1, 0, const_cast<UnicodeSet::bitquad_t *>(__reflexive_set_quads), 0, 0};



        const static std::unordered_map<codepoint_t, codepoint_t> explicit_cp_data = {
        };
        static CodePointPropertyObject property_object(identity,
                                                    std::move(null_codepoint_set),
                                                    std::move(reflexive_set),
                                                    std::move(explicit_cp_data));
    }
PropertyObject * get_IDENTITY_PropertyObject() {  return & IDENTITY_ns::property_object; }
}
