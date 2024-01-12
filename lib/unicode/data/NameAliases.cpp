
/*
 *  Copyright (c) 2024 International Characters, Inc.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters, Inc.
 *
 *  This file is generated by UCD_properties.py - manual edits may be lost.
 *  NameAliases
 */

#include <unicode/core/unicode_set.h>
#include <unicode/data/PropertyAliases.h>
#include <unicode/data/PropertyObjects.h>
#include <unicode/data/PropertyValueAliases.h>

namespace UCD {
    namespace NAME_ALIAS_ns {
        /** Code Point Ranges for Name_Alias mapping to <none>
        **/

        
        namespace {
        const static UnicodeSet::run_t __null_codepoint_set_runs[] = {
        {Empty, 34816}};
        const static UnicodeSet::bitquad_t * const __null_codepoint_set_quads = nullptr;
        }

        const static UnicodeSet null_codepoint_set{const_cast<UnicodeSet::run_t *>(__null_codepoint_set_runs), 1, 0, const_cast<UnicodeSet::bitquad_t *>(__null_codepoint_set_quads), 0, 0};



        /** Code Point Ranges for Name_Alias mapping to <codepoint>
        **/

        
        namespace {
        const static UnicodeSet::run_t __reflexive_set_runs[] = {
        {Empty, 34816}};
        const static UnicodeSet::bitquad_t * const __reflexive_set_quads = nullptr;
        }

        const static UnicodeSet reflexive_set{const_cast<UnicodeSet::run_t *>(__reflexive_set_runs), 1, 0, const_cast<UnicodeSet::bitquad_t *>(__reflexive_set_quads), 0, 0};



        const static std::vector<unsigned> buffer_offsets = {
        0, 4, 8, 12, 16, 20, 24, 28, 32, 35, 39, 43, 46, 49, 52, 55, 58, 62,
        66, 70, 74, 78, 82, 86, 90, 94, 98, 102, 106, 109, 112, 115, 118,
        121, 125, 129, 133, 137, 141, 145, 149, 153, 157, 161, 165, 169,
        173, 177, 180, 184, 188, 192, 196, 200, 204, 208, 211, 215, 219,
        223, 227, 231, 235, 238, 242, 245, 249, 254, 258, 283, 306, 310,
        314, 349, 369, 387, 405, 419, 433, 469, 502, 540, 571, 605, 610,
        615, 620, 624, 629, 634, 639, 643, 647, 651, 655, 659, 663, 667,
        671, 677, 682, 685, 689, 693, 697, 701, 731, 749, 766, 826, 887,
        914, 940, 944, 948, 952, 956, 960, 964, 968, 972, 976, 981, 986,
        991, 996, 1001, 1006, 1011, 1073, 1080, 1105, 1148, 1177, 1207,
        1234, 1262, 1284, 1337, 1342, 1347, 1352, 1357, 1362, 1367, 1372,
        1377, 1382, 1387, 1392, 1397, 1402, 1407, 1412, 1417, 1422, 1427,
        1432, 1437, 1442, 1447, 1452, 1457, 1462, 1467, 1472, 1477, 1482,
        1487, 1492, 1497, 1502, 1507, 1512, 1517, 1522, 1527, 1532, 1537,
        1542, 1547, 1552, 1557, 1562, 1567, 1572, 1577, 1582, 1587, 1592,
        1597, 1602, 1607, 1612, 1617, 1622, 1627, 1632, 1637, 1642, 1647,
        1652, 1657, 1662, 1667, 1672, 1677, 1682, 1687, 1692, 1697, 1702,
        1707, 1712, 1717, 1722, 1727, 1732, 1737, 1742, 1747, 1752, 1758,
        1764, 1770, 1776, 1782, 1788, 1794, 1800, 1806, 1812, 1818, 1824,
        1830, 1836, 1842, 1848, 1854, 1860, 1866, 1872, 1878, 1884, 1890,
        1896, 1902, 1908, 1914, 1920, 1926, 1932, 1938, 1944, 1950, 1956,
        1962, 1968, 1974, 1980, 1986, 1992, 1998, 2004, 2010, 2016, 2022,
        2028, 2034, 2040, 2046, 2052, 2058, 2064, 2070, 2076, 2082, 2088,
        2094, 2100, 2106, 2112, 2118, 2124, 2130, 2136, 2142, 2148, 2154,
        2160, 2166, 2172, 2178, 2184, 2190, 2196, 2202, 2208, 2214, 2220,
        2226, 2232, 2238, 2244, 2250, 2256, 2262, 2268, 2274, 2280, 2286,
        2292, 2298, 2304, 2310, 2316, 2322, 2328, 2334, 2340, 2346, 2352,
        2358, 2364, 2370, 2376, 2382, 2388, 2394, 2400, 2406, 2412, 2418,
        2424, 2430, 2436, 2442, 2448, 2454, 2460, 2466, 2472, 2478, 2484,
        2490, 2496, 2502, 2508, 2514, 2520, 2526, 2532, 2538, 2544, 2550,
        2556, 2562, 2568, 2574, 2580, 2586, 2592, 2598, 2604, 2610, 2616,
        2622, 2628, 2634, 2640, 2646, 2652, 2658, 2664, 2670, 2676, 2682,
        2688, 2694};
        const static char string_buffer alignas(64) [2816] = u8R"__(NUL
SOH
STX
ETX
EOT
ENQ
ACK
BEL
BS
TAB
EOL
VT
FF
CR
SO
SI
DLE
DC1
DC2
DC3
DC4
NAK
SYN
ETB
CAN
EOM
SUB
ESC
FS
GS
RS
US
SP
DEL
PAD
HOP
BPH
NBH
IND
NEL
SSA
ESA
HTS
HTJ
VTS
PLD
PLU
RI
SS2
SS3
DCS
PU1
PU2
STS
CCH
MW
SPA
EPA
SOS
SGC
SCI
CSI
ST
OSC
PM
APC
NBSP
SHY
LATIN CAPITAL LETTER GHA
LATIN SMALL LETTER GHA
CGJ
ALM
SYRIAC SUBLINEAR COLON SKEWED LEFT
KANNADA LETTER LLLA
LAO LETTER FO FON
LAO LETTER FO FAY
LAO LETTER RO
LAO LETTER LO
TIBETAN MARK BKA- SHOG GI MGO RGYAN
HANGUL JONGSEONG YESIEUNG-KIYEOK
HANGUL JONGSEONG YESIEUNG-SSANGKIYEOK
HANGUL JONGSEONG SSANGYESIEUNG
HANGUL JONGSEONG YESIEUNG-KHIEUKH
FVS1
FVS2
FVS3
MVS
FVS4
ZWSP
ZWNJ
ZWJ
LRM
RLM
LRE
RLE
PDF
LRO
RLO
NNBSP
MMSP
WJ
LRI
RLI
FSI
PDI
WEIERSTRASS ELLIPTIC FUNCTION
MICR ON US SYMBOL
MICR DASH SYMBOL
LEFTWARDS TRIANGLE-HEADED ARROW WITH DOUBLE VERTICAL STROKE
RIGHTWARDS TRIANGLE-HEADED ARROW WITH DOUBLE VERTICAL STROKE
YI SYLLABLE ITERATION MARK
MYANMAR LETTER KHAMTI LLA
VS1
VS2
VS3
VS4
VS5
VS6
VS7
VS8
VS9
VS10
VS11
VS12
VS13
VS14
VS15
VS16
PRESENTATION FORM FOR VERTICAL RIGHT WHITE LENTICULAR BRACKET
ZWNBSP
CUNEIFORM SIGN NU11 TENU
CUNEIFORM SIGN NU11 OVER NU11 BUR OVER BUR
MEDEFAIDRIN CAPITAL LETTER H
MEDEFAIDRIN CAPITAL LETTER NG
MEDEFAIDRIN SMALL LETTER H
MEDEFAIDRIN SMALL LETTER NG
HENTAIGANA LETTER E-1
BYZANTINE MUSICAL SYMBOL FTHORA SKLIRON CHROMA VASIS
VS17
VS18
VS19
VS20
VS21
VS22
VS23
VS24
VS25
VS26
VS27
VS28
VS29
VS30
VS31
VS32
VS33
VS34
VS35
VS36
VS37
VS38
VS39
VS40
VS41
VS42
VS43
VS44
VS45
VS46
VS47
VS48
VS49
VS50
VS51
VS52
VS53
VS54
VS55
VS56
VS57
VS58
VS59
VS60
VS61
VS62
VS63
VS64
VS65
VS66
VS67
VS68
VS69
VS70
VS71
VS72
VS73
VS74
VS75
VS76
VS77
VS78
VS79
VS80
VS81
VS82
VS83
VS84
VS85
VS86
VS87
VS88
VS89
VS90
VS91
VS92
VS93
VS94
VS95
VS96
VS97
VS98
VS99
VS100
VS101
VS102
VS103
VS104
VS105
VS106
VS107
VS108
VS109
VS110
VS111
VS112
VS113
VS114
VS115
VS116
VS117
VS118
VS119
VS120
VS121
VS122
VS123
VS124
VS125
VS126
VS127
VS128
VS129
VS130
VS131
VS132
VS133
VS134
VS135
VS136
VS137
VS138
VS139
VS140
VS141
VS142
VS143
VS144
VS145
VS146
VS147
VS148
VS149
VS150
VS151
VS152
VS153
VS154
VS155
VS156
VS157
VS158
VS159
VS160
VS161
VS162
VS163
VS164
VS165
VS166
VS167
VS168
VS169
VS170
VS171
VS172
VS173
VS174
VS175
VS176
VS177
VS178
VS179
VS180
VS181
VS182
VS183
VS184
VS185
VS186
VS187
VS188
VS189
VS190
VS191
VS192
VS193
VS194
VS195
VS196
VS197
VS198
VS199
VS200
VS201
VS202
VS203
VS204
VS205
VS206
VS207
VS208
VS209
VS210
VS211
VS212
VS213
VS214
VS215
VS216
VS217
VS218
VS219
VS220
VS221
VS222
VS223
VS224
VS225
VS226
VS227
VS228
VS229
VS230
VS231
VS232
VS233
VS234
VS235
VS236
VS237
VS238
VS239
VS240
VS241
VS242
VS243
VS244
VS245
VS246
VS247
VS248
VS249
VS250
VS251
VS252
VS253
VS254
VS255
VS256
)__";

        const static std::vector<codepoint_t> defined_cps{
        0x0000, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007,
        0x0008, 0x0009, 0x000a, 0x000b, 0x000c, 0x000d, 0x000e, 0x000f,
        0x0010, 0x0011, 0x0012, 0x0013, 0x0014, 0x0015, 0x0016, 0x0017,
        0x0018, 0x0019, 0x001a, 0x001b, 0x001c, 0x001d, 0x001e, 0x001f,
        0x0020, 0x007f, 0x0080, 0x0081, 0x0082, 0x0083, 0x0084, 0x0085,
        0x0086, 0x0087, 0x0088, 0x0089, 0x008a, 0x008b, 0x008c, 0x008d,
        0x008e, 0x008f, 0x0090, 0x0091, 0x0092, 0x0093, 0x0094, 0x0095,
        0x0096, 0x0097, 0x0098, 0x0099, 0x009a, 0x009b, 0x009c, 0x009d,
        0x009e, 0x009f, 0x00a0, 0x00ad, 0x01a2, 0x01a3, 0x034f, 0x061c,
        0x0709, 0x0cde, 0x0e9d, 0x0e9f, 0x0ea3, 0x0ea5, 0x0fd0, 0x11ec,
        0x11ed, 0x11ee, 0x11ef, 0x180b, 0x180c, 0x180d, 0x180e, 0x180f,
        0x200b, 0x200c, 0x200d, 0x200e, 0x200f, 0x202a, 0x202b, 0x202c,
        0x202d, 0x202e, 0x202f, 0x205f, 0x2060, 0x2066, 0x2067, 0x2068,
        0x2069, 0x2118, 0x2448, 0x2449, 0x2b7a, 0x2b7c, 0xa015, 0xaa6e,
        0xfe00, 0xfe01, 0xfe02, 0xfe03, 0xfe04, 0xfe05, 0xfe06, 0xfe07,
        0xfe08, 0xfe09, 0xfe0a, 0xfe0b, 0xfe0c, 0xfe0d, 0xfe0e, 0xfe0f,
        0xfe18, 0xfeff, 0x122d4, 0x122d5, 0x16e56, 0x16e57, 0x16e76,
        0x16e77, 0x1b001, 0x1d0c5, 0xe0100, 0xe0101, 0xe0102, 0xe0103,
        0xe0104, 0xe0105, 0xe0106, 0xe0107, 0xe0108, 0xe0109, 0xe010a,
        0xe010b, 0xe010c, 0xe010d, 0xe010e, 0xe010f, 0xe0110, 0xe0111,
        0xe0112, 0xe0113, 0xe0114, 0xe0115, 0xe0116, 0xe0117, 0xe0118,
        0xe0119, 0xe011a, 0xe011b, 0xe011c, 0xe011d, 0xe011e, 0xe011f,
        0xe0120, 0xe0121, 0xe0122, 0xe0123, 0xe0124, 0xe0125, 0xe0126,
        0xe0127, 0xe0128, 0xe0129, 0xe012a, 0xe012b, 0xe012c, 0xe012d,
        0xe012e, 0xe012f, 0xe0130, 0xe0131, 0xe0132, 0xe0133, 0xe0134,
        0xe0135, 0xe0136, 0xe0137, 0xe0138, 0xe0139, 0xe013a, 0xe013b,
        0xe013c, 0xe013d, 0xe013e, 0xe013f, 0xe0140, 0xe0141, 0xe0142,
        0xe0143, 0xe0144, 0xe0145, 0xe0146, 0xe0147, 0xe0148, 0xe0149,
        0xe014a, 0xe014b, 0xe014c, 0xe014d, 0xe014e, 0xe014f, 0xe0150,
        0xe0151, 0xe0152, 0xe0153, 0xe0154, 0xe0155, 0xe0156, 0xe0157,
        0xe0158, 0xe0159, 0xe015a, 0xe015b, 0xe015c, 0xe015d, 0xe015e,
        0xe015f, 0xe0160, 0xe0161, 0xe0162, 0xe0163, 0xe0164, 0xe0165,
        0xe0166, 0xe0167, 0xe0168, 0xe0169, 0xe016a, 0xe016b, 0xe016c,
        0xe016d, 0xe016e, 0xe016f, 0xe0170, 0xe0171, 0xe0172, 0xe0173,
        0xe0174, 0xe0175, 0xe0176, 0xe0177, 0xe0178, 0xe0179, 0xe017a,
        0xe017b, 0xe017c, 0xe017d, 0xe017e, 0xe017f, 0xe0180, 0xe0181,
        0xe0182, 0xe0183, 0xe0184, 0xe0185, 0xe0186, 0xe0187, 0xe0188,
        0xe0189, 0xe018a, 0xe018b, 0xe018c, 0xe018d, 0xe018e, 0xe018f,
        0xe0190, 0xe0191, 0xe0192, 0xe0193, 0xe0194, 0xe0195, 0xe0196,
        0xe0197, 0xe0198, 0xe0199, 0xe019a, 0xe019b, 0xe019c, 0xe019d,
        0xe019e, 0xe019f, 0xe01a0, 0xe01a1, 0xe01a2, 0xe01a3, 0xe01a4,
        0xe01a5, 0xe01a6, 0xe01a7, 0xe01a8, 0xe01a9, 0xe01aa, 0xe01ab,
        0xe01ac, 0xe01ad, 0xe01ae, 0xe01af, 0xe01b0, 0xe01b1, 0xe01b2,
        0xe01b3, 0xe01b4, 0xe01b5, 0xe01b6, 0xe01b7, 0xe01b8, 0xe01b9,
        0xe01ba, 0xe01bb, 0xe01bc, 0xe01bd, 0xe01be, 0xe01bf, 0xe01c0,
        0xe01c1, 0xe01c2, 0xe01c3, 0xe01c4, 0xe01c5, 0xe01c6, 0xe01c7,
        0xe01c8, 0xe01c9, 0xe01ca, 0xe01cb, 0xe01cc, 0xe01cd, 0xe01ce,
        0xe01cf, 0xe01d0, 0xe01d1, 0xe01d2, 0xe01d3, 0xe01d4, 0xe01d5,
        0xe01d6, 0xe01d7, 0xe01d8, 0xe01d9, 0xe01da, 0xe01db, 0xe01dc,
        0xe01dd, 0xe01de, 0xe01df, 0xe01e0, 0xe01e1, 0xe01e2, 0xe01e3,
        0xe01e4, 0xe01e5, 0xe01e6, 0xe01e7, 0xe01e8, 0xe01e9, 0xe01ea,
        0xe01eb, 0xe01ec, 0xe01ed, 0xe01ee, 0xe01ef};
        static StringPropertyObject property_object(Name_Alias,
                                                    std::move(null_codepoint_set),
                                                    std::move(reflexive_set),
                                                    static_cast<const char *>(string_buffer),
                                                    std::move(buffer_offsets),
                                                    std::move(defined_cps));
    }
PropertyObject * get_NAME_ALIAS_PropertyObject() {  return & NAME_ALIAS_ns::property_object; }
}

