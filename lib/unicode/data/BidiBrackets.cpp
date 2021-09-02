
/*
 *  Copyright (c) 2021 International Characters, Inc.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters, Inc.
 *
 *  This file is generated by UCD_properties.py - manual edits may be lost.
 *  BidiBrackets
 */

#include <unicode/core/unicode_set.h>
#include <unicode/data/PropertyAliases.h>
#include <unicode/data/PropertyObjects.h>
#include <unicode/data/PropertyValueAliases.h>

namespace UCD {
    namespace BPB_ns {
        /** Code Point Ranges for bpb mapping to <none>
        [0000, 0027], [002a, 005a], [005c, 005c], [005e, 007a],
        [007c, 007c], [007e, 0f39], [0f3e, 169a], [169d, 2044],
        [2047, 207c], [207f, 208c], [208f, 2307], [230c, 2328],
        [232b, 2767], [2776, 27c4], [27c7, 27e5], [27f0, 2982],
        [2999, 29d7], [29dc, 29fb], [29fe, 2e21], [2e2a, 3007],
        [3012, 3013], [301c, fe58], [fe5f, ff07], [ff0a, ff3a],
        [ff3c, ff3c], [ff3e, ff5a], [ff5c, ff5c], [ff5e, ff5e],
        [ff61, ff61], [ff64, 10ffff]**/

        
        namespace {
        const static UnicodeSet::run_t __null_codepoint_set_runs[] = {
        {Full, 1}, {Mixed, 3}, {Full, 117}, {Mixed, 1}, {Full, 58},
        {Mixed, 1}, {Full, 77}, {Mixed, 3}, {Full, 19}, {Mixed, 2},
        {Full, 33}, {Mixed, 1}, {Full, 2}, {Mixed, 2}, {Full, 12},
        {Mixed, 1}, {Full, 1}, {Mixed, 2}, {Full, 33}, {Mixed, 1},
        {Full, 14}, {Mixed, 1}, {Full, 1649}, {Mixed, 1}, {Full, 5},
        {Mixed, 4}, {Full, 32772}};
        const static UnicodeSet::bitquad_t  __null_codepoint_set_quads[] = {
        0xfffffcff, 0xd7ffffff, 0xd7ffffff, 0xc3ffffff, 0xe7ffffff,
        0xffffff9f, 0x9fffffff, 0xffff9fff, 0xfffff0ff, 0xfffff9ff,
        0xffc000ff, 0xffffff9f, 0xffff003f, 0xfe000007, 0xf0ffffff,
        0xcfffffff, 0xfffffc03, 0xf00c00ff, 0x81ffffff, 0xfffffcff,
        0xd7ffffff, 0x57ffffff, 0xfffffff2};
        }

        const static UnicodeSet null_codepoint_set{const_cast<UnicodeSet::run_t *>(__null_codepoint_set_runs), 27, 0, const_cast<UnicodeSet::bitquad_t *>(__null_codepoint_set_quads), 23, 0};



        /** Code Point Ranges for bpb mapping to <codepoint>
        **/

        
        namespace {
        const static UnicodeSet::run_t __reflexive_set_runs[] = {
        {Empty, 34816}};
        const static UnicodeSet::bitquad_t * const __reflexive_set_quads = nullptr;
        }

        const static UnicodeSet reflexive_set{const_cast<UnicodeSet::run_t *>(__reflexive_set_runs), 1, 0, const_cast<UnicodeSet::bitquad_t *>(__reflexive_set_quads), 0, 0};



        const static std::vector<unsigned> buffer_offsets = {
        0, 2, 4, 6, 8, 10, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56,
        60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116,
        120, 124, 128, 132, 136, 140, 144, 148, 152, 156, 160, 164, 168,
        172, 176, 180, 184, 188, 192, 196, 200, 204, 208, 212, 216, 220,
        224, 228, 232, 236, 240, 244, 248, 252, 256, 260, 264, 268, 272,
        276, 280, 284, 288, 292, 296, 300, 304, 308, 312, 316, 320, 324,
        328, 332, 336, 340, 344, 348, 352, 356, 360, 364, 368, 372, 376,
        380, 384, 388, 392, 396, 400, 404, 408, 412, 416, 420, 424, 428,
        432, 436, 440, 444, 448, 452, 456, 460, 464, 468};
        const static char string_buffer alignas(64) [512] = u8R"__()
(
]
[
}
{
༻
༺
༽
༼
᚜
᚛
⁆
⁅
⁾
⁽
₎
₍
⌉
⌈
⌋
⌊
〉
〈
❩
❨
❫
❪
❭
❬
❯
❮
❱
❰
❳
❲
❵
❴
⟆
⟅
⟧
⟦
⟩
⟨
⟫
⟪
⟭
⟬
⟯
⟮
⦄
⦃
⦆
⦅
⦈
⦇
⦊
⦉
⦌
⦋
⦐
⦏
⦎
⦍
⦒
⦑
⦔
⦓
⦖
⦕
⦘
⦗
⧙
⧘
⧛
⧚
⧽
⧼
⸣
⸢
⸥
⸤
⸧
⸦
⸩
⸨
〉
〈
》
《
」
「
』
『
】
【
〕
〔
〗
〖
〙
〘
〛
〚
﹚
﹙
﹜
﹛
﹞
﹝
）
（
］
［
｝
｛
｠
｟
｣
｢
)__";

        const static std::vector<codepoint_t> defined_cps{
        0x0028, 0x0029, 0x005b, 0x005d, 0x007b, 0x007d, 0x0f3a, 0x0f3b,
        0x0f3c, 0x0f3d, 0x169b, 0x169c, 0x2045, 0x2046, 0x207d, 0x207e,
        0x208d, 0x208e, 0x2308, 0x2309, 0x230a, 0x230b, 0x2329, 0x232a,
        0x2768, 0x2769, 0x276a, 0x276b, 0x276c, 0x276d, 0x276e, 0x276f,
        0x2770, 0x2771, 0x2772, 0x2773, 0x2774, 0x2775, 0x27c5, 0x27c6,
        0x27e6, 0x27e7, 0x27e8, 0x27e9, 0x27ea, 0x27eb, 0x27ec, 0x27ed,
        0x27ee, 0x27ef, 0x2983, 0x2984, 0x2985, 0x2986, 0x2987, 0x2988,
        0x2989, 0x298a, 0x298b, 0x298c, 0x298d, 0x298e, 0x298f, 0x2990,
        0x2991, 0x2992, 0x2993, 0x2994, 0x2995, 0x2996, 0x2997, 0x2998,
        0x29d8, 0x29d9, 0x29da, 0x29db, 0x29fc, 0x29fd, 0x2e22, 0x2e23,
        0x2e24, 0x2e25, 0x2e26, 0x2e27, 0x2e28, 0x2e29, 0x3008, 0x3009,
        0x300a, 0x300b, 0x300c, 0x300d, 0x300e, 0x300f, 0x3010, 0x3011,
        0x3014, 0x3015, 0x3016, 0x3017, 0x3018, 0x3019, 0x301a, 0x301b,
        0xfe59, 0xfe5a, 0xfe5b, 0xfe5c, 0xfe5d, 0xfe5e, 0xff08, 0xff09,
        0xff3b, 0xff3d, 0xff5b, 0xff5d, 0xff5f, 0xff60, 0xff62, 0xff63};
        static StringPropertyObject property_object(bpb,
                                                    std::move(null_codepoint_set),
                                                    std::move(reflexive_set),
                                                    static_cast<const char *>(string_buffer),
                                                    std::move(buffer_offsets),
                                                    std::move(defined_cps));
    }
PropertyObject * get_BPB_PropertyObject() {  return & BPB_ns::property_object; }
  namespace BPT_ns {
    const unsigned independent_prop_values = 3;
    /** Code Point Ranges for n
    [0000, 0027], [002a, 005a], [005c, 005c], [005e, 007a], [007c, 007c],
    [007e, 0f39], [0f3e, 169a], [169d, 2044], [2047, 207c], [207f, 208c],
    [208f, 2307], [230c, 2328], [232b, 2767], [2776, 27c4], [27c7, 27e5],
    [27f0, 2982], [2999, 29d7], [29dc, 29fb], [29fe, 2e21], [2e2a, 3007],
    [3012, 3013], [301c, fe58], [fe5f, ff07], [ff0a, ff3a], [ff3c, ff3c],
    [ff3e, ff5a], [ff5c, ff5c], [ff5e, ff5e], [ff61, ff61], [ff64, 10ffff]**/


    namespace {
    const static UnicodeSet::run_t __n_Set_runs[] = {
    {Full, 1}, {Mixed, 3}, {Full, 117}, {Mixed, 1}, {Full, 58}, {Mixed, 1},
    {Full, 77}, {Mixed, 3}, {Full, 19}, {Mixed, 2}, {Full, 33}, {Mixed, 1},
    {Full, 2}, {Mixed, 2}, {Full, 12}, {Mixed, 1}, {Full, 1}, {Mixed, 2},
    {Full, 33}, {Mixed, 1}, {Full, 14}, {Mixed, 1}, {Full, 1649},
    {Mixed, 1}, {Full, 5}, {Mixed, 4}, {Full, 32772}};
    const static UnicodeSet::bitquad_t  __n_Set_quads[] = {
    0xfffffcff, 0xd7ffffff, 0xd7ffffff, 0xc3ffffff, 0xe7ffffff, 0xffffff9f,
    0x9fffffff, 0xffff9fff, 0xfffff0ff, 0xfffff9ff, 0xffc000ff, 0xffffff9f,
    0xffff003f, 0xfe000007, 0xf0ffffff, 0xcfffffff, 0xfffffc03, 0xf00c00ff,
    0x81ffffff, 0xfffffcff, 0xd7ffffff, 0x57ffffff, 0xfffffff2};
    }

    const static UnicodeSet n_Set{const_cast<UnicodeSet::run_t *>(__n_Set_runs), 27, 0, const_cast<UnicodeSet::bitquad_t *>(__n_Set_quads), 23, 0};

    /** Code Point Ranges for o
    [0028, 0028], [005b, 005b], [007b, 007b], [0f3a, 0f3a], [0f3c, 0f3c],
    [169b, 169b], [2045, 2045], [207d, 207d], [208d, 208d], [2308, 2308],
    [230a, 230a], [2329, 2329], [2768, 2768], [276a, 276a], [276c, 276c],
    [276e, 276e], [2770, 2770], [2772, 2772], [2774, 2774], [27c5, 27c5],
    [27e6, 27e6], [27e8, 27e8], [27ea, 27ea], [27ec, 27ec], [27ee, 27ee],
    [2983, 2983], [2985, 2985], [2987, 2987], [2989, 2989], [298b, 298b],
    [298d, 298d], [298f, 298f], [2991, 2991], [2993, 2993], [2995, 2995],
    [2997, 2997], [29d8, 29d8], [29da, 29da], [29fc, 29fc], [2e22, 2e22],
    [2e24, 2e24], [2e26, 2e26], [2e28, 2e28], [3008, 3008], [300a, 300a],
    [300c, 300c], [300e, 300e], [3010, 3010], [3014, 3014], [3016, 3016],
    [3018, 3018], [301a, 301a], [fe59, fe59], [fe5b, fe5b], [fe5d, fe5d],
    [ff08, ff08], [ff3b, ff3b], [ff5b, ff5b], [ff5f, ff5f], [ff62, ff62]**/


    namespace {
    const static UnicodeSet::run_t __o_Set_runs[] = {
    {Empty, 1}, {Mixed, 3}, {Empty, 117}, {Mixed, 1}, {Empty, 58},
    {Mixed, 1}, {Empty, 77}, {Mixed, 3}, {Empty, 19}, {Mixed, 2},
    {Empty, 33}, {Mixed, 1}, {Empty, 2}, {Mixed, 2}, {Empty, 12},
    {Mixed, 1}, {Empty, 1}, {Mixed, 2}, {Empty, 33}, {Mixed, 1},
    {Empty, 14}, {Mixed, 1}, {Empty, 1649}, {Mixed, 1}, {Empty, 5},
    {Mixed, 4}, {Empty, 32772}};
    const static UnicodeSet::bitquad_t  __o_Set_quads[] = {
    0x00000100, 0x08000000, 0x08000000, 0x14000000, 0x08000000, 0x00000020,
    0x20000000, 0x00002000, 0x00000500, 0x00000200, 0x00155500, 0x00000020,
    0x00005540, 0x00aaaaa8, 0x05000000, 0x10000000, 0x00000154, 0x05515500,
    0x2a000000, 0x00000100, 0x08000000, 0x88000000, 0x00000004};
    }

    const static UnicodeSet o_Set{const_cast<UnicodeSet::run_t *>(__o_Set_runs), 27, 0, const_cast<UnicodeSet::bitquad_t *>(__o_Set_quads), 23, 0};

    /** Code Point Ranges for c
    [0029, 0029], [005d, 005d], [007d, 007d], [0f3b, 0f3b], [0f3d, 0f3d],
    [169c, 169c], [2046, 2046], [207e, 207e], [208e, 208e], [2309, 2309],
    [230b, 230b], [232a, 232a], [2769, 2769], [276b, 276b], [276d, 276d],
    [276f, 276f], [2771, 2771], [2773, 2773], [2775, 2775], [27c6, 27c6],
    [27e7, 27e7], [27e9, 27e9], [27eb, 27eb], [27ed, 27ed], [27ef, 27ef],
    [2984, 2984], [2986, 2986], [2988, 2988], [298a, 298a], [298c, 298c],
    [298e, 298e], [2990, 2990], [2992, 2992], [2994, 2994], [2996, 2996],
    [2998, 2998], [29d9, 29d9], [29db, 29db], [29fd, 29fd], [2e23, 2e23],
    [2e25, 2e25], [2e27, 2e27], [2e29, 2e29], [3009, 3009], [300b, 300b],
    [300d, 300d], [300f, 300f], [3011, 3011], [3015, 3015], [3017, 3017],
    [3019, 3019], [301b, 301b], [fe5a, fe5a], [fe5c, fe5c], [fe5e, fe5e],
    [ff09, ff09], [ff3d, ff3d], [ff5d, ff5d], [ff60, ff60], [ff63, ff63]**/


    namespace {
    const static UnicodeSet::run_t __c_Set_runs[] = {
    {Empty, 1}, {Mixed, 3}, {Empty, 117}, {Mixed, 1}, {Empty, 58},
    {Mixed, 1}, {Empty, 77}, {Mixed, 3}, {Empty, 19}, {Mixed, 2},
    {Empty, 33}, {Mixed, 1}, {Empty, 2}, {Mixed, 2}, {Empty, 12},
    {Mixed, 1}, {Empty, 1}, {Mixed, 2}, {Empty, 33}, {Mixed, 1},
    {Empty, 14}, {Mixed, 1}, {Empty, 1649}, {Mixed, 1}, {Empty, 5},
    {Mixed, 4}, {Empty, 32772}};
    const static UnicodeSet::bitquad_t  __c_Set_quads[] = {
    0x00000200, 0x20000000, 0x20000000, 0x28000000, 0x10000000, 0x00000040,
    0x40000000, 0x00004000, 0x00000a00, 0x00000400, 0x002aaa00, 0x00000040,
    0x0000aa80, 0x01555550, 0x0a000000, 0x20000000, 0x000002a8, 0x0aa2aa00,
    0x54000000, 0x00000200, 0x20000000, 0x20000000, 0x00000009};
    }

    const static UnicodeSet c_Set{const_cast<UnicodeSet::run_t *>(__c_Set_runs), 27, 0, const_cast<UnicodeSet::bitquad_t *>(__c_Set_quads), 23, 0};

    static EnumeratedPropertyObject property_object
        {bpt,
        BPT_ns::independent_prop_values,
        std::move(BPT_ns::enum_names),
        std::move(BPT_ns::value_names),
        std::move(BPT_ns::aliases_only_map),{
        &n_Set, &o_Set, &c_Set
        }};
    }
PropertyObject * get_BPT_PropertyObject() {  return & BPT_ns::property_object; }
}

