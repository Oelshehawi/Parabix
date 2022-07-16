/*
 *  Copyright (c) 2022 International Characters.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters.
 */

#pragma once

#include <string>

namespace re {
class RE;

RE * name_variable_length_CCs(RE * r, unsigned UTF_bits = 8);

RE * name_min_length_alts(RE * r, std::string minLengthPfx = "minLgth");

}

