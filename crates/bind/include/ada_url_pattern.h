/*
 * ada_url_pattern.h: ada 4.0.0's URLPattern, over vbind's ada.h.
 *
 * Written by scripts/vendor-ada-url-pattern.py; do not edit. Everything
 * between the "begin file" and "end file" marks is copied from
 * https://github.com/ada-url/ada (Copyright 2023 Yagiz Nizipli and Daniel
 * Lemire, Apache-2.0 or MIT; expected.h is Sy Brand's tl::expected, CC0),
 * with the functions of ada's .cpp files marked inline. The code parses
 * and matches patterns; the URLs it meets are parsed by ada.h's
 * ada::parse, which is vurl. Included by ada.h, not on its own.
 */
#ifndef VBIND_ADA_URL_PATTERN_H
#define VBIND_ADA_URL_PATTERN_H

#include <algorithm>
#include <array>
#include <charconv>
#include <concepts>
#include <optional>
#include <ostream>
#include <ranges>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>

/* ada's identifier code points (IdentifierStart and IdentifierPart of
 * ECMAScript), read out of ada 4.0.0 one code point at a time. */
namespace ada::idna {
inline constexpr uint32_t vbind_id_start[][2] = {
    {0x24, 0x24}, {0x41, 0x5a}, {0x5f, 0x5f}, {0x61, 0x7a},
    {0xaa, 0xaa}, {0xb5, 0xb5}, {0xba, 0xba}, {0xc0, 0xd6},
    {0xd8, 0xf6}, {0xf8, 0x2c1}, {0x2c6, 0x2d1}, {0x2e0, 0x2e4},
    {0x2ec, 0x2ec}, {0x2ee, 0x2ee}, {0x370, 0x374}, {0x376, 0x377},
    {0x37a, 0x37d}, {0x37f, 0x37f}, {0x386, 0x386}, {0x388, 0x38a},
    {0x38c, 0x38c}, {0x38e, 0x3a1}, {0x3a3, 0x3f5}, {0x3f7, 0x481},
    {0x48a, 0x52f}, {0x531, 0x556}, {0x559, 0x559}, {0x560, 0x588},
    {0x5d0, 0x5ea}, {0x5ef, 0x5f2}, {0x620, 0x64a}, {0x66e, 0x66f},
    {0x671, 0x6d3}, {0x6d5, 0x6d5}, {0x6e5, 0x6e6}, {0x6ee, 0x6ef},
    {0x6fa, 0x6fc}, {0x6ff, 0x6ff}, {0x710, 0x710}, {0x712, 0x72f},
    {0x74d, 0x7a5}, {0x7b1, 0x7b1}, {0x7ca, 0x7ea}, {0x7f4, 0x7f5},
    {0x7fa, 0x7fa}, {0x800, 0x815}, {0x81a, 0x81a}, {0x824, 0x824},
    {0x828, 0x828}, {0x840, 0x858}, {0x860, 0x86a}, {0x870, 0x887},
    {0x889, 0x88f}, {0x8a0, 0x8c9}, {0x904, 0x939}, {0x93d, 0x93d},
    {0x950, 0x950}, {0x958, 0x961}, {0x971, 0x980}, {0x985, 0x98c},
    {0x98f, 0x990}, {0x993, 0x9a8}, {0x9aa, 0x9b0}, {0x9b2, 0x9b2},
    {0x9b6, 0x9b9}, {0x9bd, 0x9bd}, {0x9ce, 0x9ce}, {0x9dc, 0x9dd},
    {0x9df, 0x9e1}, {0x9f0, 0x9f1}, {0x9fc, 0x9fc}, {0xa05, 0xa0a},
    {0xa0f, 0xa10}, {0xa13, 0xa28}, {0xa2a, 0xa30}, {0xa32, 0xa33},
    {0xa35, 0xa36}, {0xa38, 0xa39}, {0xa59, 0xa5c}, {0xa5e, 0xa5e},
    {0xa72, 0xa74}, {0xa85, 0xa8d}, {0xa8f, 0xa91}, {0xa93, 0xaa8},
    {0xaaa, 0xab0}, {0xab2, 0xab3}, {0xab5, 0xab9}, {0xabd, 0xabd},
    {0xad0, 0xad0}, {0xae0, 0xae1}, {0xaf9, 0xaf9}, {0xb05, 0xb0c},
    {0xb0f, 0xb10}, {0xb13, 0xb28}, {0xb2a, 0xb30}, {0xb32, 0xb33},
    {0xb35, 0xb39}, {0xb3d, 0xb3d}, {0xb5c, 0xb5d}, {0xb5f, 0xb61},
    {0xb71, 0xb71}, {0xb83, 0xb83}, {0xb85, 0xb8a}, {0xb8e, 0xb90},
    {0xb92, 0xb95}, {0xb99, 0xb9a}, {0xb9c, 0xb9c}, {0xb9e, 0xb9f},
    {0xba3, 0xba4}, {0xba8, 0xbaa}, {0xbae, 0xbb9}, {0xbd0, 0xbd0},
    {0xc05, 0xc0c}, {0xc0e, 0xc10}, {0xc12, 0xc28}, {0xc2a, 0xc39},
    {0xc3d, 0xc3d}, {0xc58, 0xc5a}, {0xc5c, 0xc5d}, {0xc60, 0xc61},
    {0xc80, 0xc80}, {0xc85, 0xc8c}, {0xc8e, 0xc90}, {0xc92, 0xca8},
    {0xcaa, 0xcb3}, {0xcb5, 0xcb9}, {0xcbd, 0xcbd}, {0xcdc, 0xcde},
    {0xce0, 0xce1}, {0xcf1, 0xcf2}, {0xd04, 0xd0c}, {0xd0e, 0xd10},
    {0xd12, 0xd3a}, {0xd3d, 0xd3d}, {0xd4e, 0xd4e}, {0xd54, 0xd56},
    {0xd5f, 0xd61}, {0xd7a, 0xd7f}, {0xd85, 0xd96}, {0xd9a, 0xdb1},
    {0xdb3, 0xdbb}, {0xdbd, 0xdbd}, {0xdc0, 0xdc6}, {0xe01, 0xe30},
    {0xe32, 0xe33}, {0xe40, 0xe46}, {0xe81, 0xe82}, {0xe84, 0xe84},
    {0xe86, 0xe8a}, {0xe8c, 0xea3}, {0xea5, 0xea5}, {0xea7, 0xeb0},
    {0xeb2, 0xeb3}, {0xebd, 0xebd}, {0xec0, 0xec4}, {0xec6, 0xec6},
    {0xedc, 0xedf}, {0xf00, 0xf00}, {0xf40, 0xf47}, {0xf49, 0xf6c},
    {0xf88, 0xf8c}, {0x1000, 0x102a}, {0x103f, 0x103f}, {0x1050, 0x1055},
    {0x105a, 0x105d}, {0x1061, 0x1061}, {0x1065, 0x1066}, {0x106e, 0x1070},
    {0x1075, 0x1081}, {0x108e, 0x108e}, {0x10a0, 0x10c5}, {0x10c7, 0x10c7},
    {0x10cd, 0x10cd}, {0x10d0, 0x10fa}, {0x10fc, 0x1248}, {0x124a, 0x124d},
    {0x1250, 0x1256}, {0x1258, 0x1258}, {0x125a, 0x125d}, {0x1260, 0x1288},
    {0x128a, 0x128d}, {0x1290, 0x12b0}, {0x12b2, 0x12b5}, {0x12b8, 0x12be},
    {0x12c0, 0x12c0}, {0x12c2, 0x12c5}, {0x12c8, 0x12d6}, {0x12d8, 0x1310},
    {0x1312, 0x1315}, {0x1318, 0x135a}, {0x1380, 0x138f}, {0x13a0, 0x13f5},
    {0x13f8, 0x13fd}, {0x1401, 0x166c}, {0x166f, 0x167f}, {0x1681, 0x169a},
    {0x16a0, 0x16ea}, {0x16ee, 0x16f8}, {0x1700, 0x1711}, {0x171f, 0x1731},
    {0x1740, 0x1751}, {0x1760, 0x176c}, {0x176e, 0x1770}, {0x1780, 0x17b3},
    {0x17d7, 0x17d7}, {0x17dc, 0x17dc}, {0x1820, 0x1878}, {0x1880, 0x18a8},
    {0x18aa, 0x18aa}, {0x18b0, 0x18f5}, {0x1900, 0x191e}, {0x1950, 0x196d},
    {0x1970, 0x1974}, {0x1980, 0x19ab}, {0x19b0, 0x19c9}, {0x1a00, 0x1a16},
    {0x1a20, 0x1a54}, {0x1aa7, 0x1aa7}, {0x1b05, 0x1b33}, {0x1b45, 0x1b4c},
    {0x1b83, 0x1ba0}, {0x1bae, 0x1baf}, {0x1bba, 0x1be5}, {0x1c00, 0x1c23},
    {0x1c4d, 0x1c4f}, {0x1c5a, 0x1c7d}, {0x1c80, 0x1c8a}, {0x1c90, 0x1cba},
    {0x1cbd, 0x1cbf}, {0x1ce9, 0x1cec}, {0x1cee, 0x1cf3}, {0x1cf5, 0x1cf6},
    {0x1cfa, 0x1cfa}, {0x1d00, 0x1dbf}, {0x1e00, 0x1f15}, {0x1f18, 0x1f1d},
    {0x1f20, 0x1f45}, {0x1f48, 0x1f4d}, {0x1f50, 0x1f57}, {0x1f59, 0x1f59},
    {0x1f5b, 0x1f5b}, {0x1f5d, 0x1f5d}, {0x1f5f, 0x1f7d}, {0x1f80, 0x1fb4},
    {0x1fb6, 0x1fbc}, {0x1fbe, 0x1fbe}, {0x1fc2, 0x1fc4}, {0x1fc6, 0x1fcc},
    {0x1fd0, 0x1fd3}, {0x1fd6, 0x1fdb}, {0x1fe0, 0x1fec}, {0x1ff2, 0x1ff4},
    {0x1ff6, 0x1ffc}, {0x2071, 0x2071}, {0x207f, 0x207f}, {0x2090, 0x209c},
    {0x2102, 0x2102}, {0x2107, 0x2107}, {0x210a, 0x2113}, {0x2115, 0x2115},
    {0x2118, 0x211d}, {0x2124, 0x2124}, {0x2126, 0x2126}, {0x2128, 0x2128},
    {0x212a, 0x2139}, {0x213c, 0x213f}, {0x2145, 0x2149}, {0x214e, 0x214e},
    {0x2160, 0x2188}, {0x2c00, 0x2ce4}, {0x2ceb, 0x2cee}, {0x2cf2, 0x2cf3},
    {0x2d00, 0x2d25}, {0x2d27, 0x2d27}, {0x2d2d, 0x2d2d}, {0x2d30, 0x2d67},
    {0x2d6f, 0x2d6f}, {0x2d80, 0x2d96}, {0x2da0, 0x2da6}, {0x2da8, 0x2dae},
    {0x2db0, 0x2db6}, {0x2db8, 0x2dbe}, {0x2dc0, 0x2dc6}, {0x2dc8, 0x2dce},
    {0x2dd0, 0x2dd6}, {0x2dd8, 0x2dde}, {0x3005, 0x3007}, {0x3021, 0x3029},
    {0x3031, 0x3035}, {0x3038, 0x303c}, {0x3041, 0x3096}, {0x309b, 0x309f},
    {0x30a1, 0x30fa}, {0x30fc, 0x30ff}, {0x3105, 0x312f}, {0x3131, 0x318e},
    {0x31a0, 0x31bf}, {0x31f0, 0x31ff}, {0x3400, 0x4dbf}, {0x4e00, 0xa48c},
    {0xa4d0, 0xa4fd}, {0xa500, 0xa60c}, {0xa610, 0xa61f}, {0xa62a, 0xa62b},
    {0xa640, 0xa66e}, {0xa67f, 0xa69d}, {0xa6a0, 0xa6ef}, {0xa717, 0xa71f},
    {0xa722, 0xa788}, {0xa78b, 0xa7dc}, {0xa7f1, 0xa801}, {0xa803, 0xa805},
    {0xa807, 0xa80a}, {0xa80c, 0xa822}, {0xa840, 0xa873}, {0xa882, 0xa8b3},
    {0xa8f2, 0xa8f7}, {0xa8fb, 0xa8fb}, {0xa8fd, 0xa8fe}, {0xa90a, 0xa925},
    {0xa930, 0xa946}, {0xa960, 0xa97c}, {0xa984, 0xa9b2}, {0xa9cf, 0xa9cf},
    {0xa9e0, 0xa9e4}, {0xa9e6, 0xa9ef}, {0xa9fa, 0xa9fe}, {0xaa00, 0xaa28},
    {0xaa40, 0xaa42}, {0xaa44, 0xaa4b}, {0xaa60, 0xaa76}, {0xaa7a, 0xaa7a},
    {0xaa7e, 0xaaaf}, {0xaab1, 0xaab1}, {0xaab5, 0xaab6}, {0xaab9, 0xaabd},
    {0xaac0, 0xaac0}, {0xaac2, 0xaac2}, {0xaadb, 0xaadd}, {0xaae0, 0xaaea},
    {0xaaf2, 0xaaf4}, {0xab01, 0xab06}, {0xab09, 0xab0e}, {0xab11, 0xab16},
    {0xab20, 0xab26}, {0xab28, 0xab2e}, {0xab30, 0xab5a}, {0xab5c, 0xab69},
    {0xab70, 0xabe2}, {0xac00, 0xd7a3}, {0xd7b0, 0xd7c6}, {0xd7cb, 0xd7fb},
    {0xf900, 0xfa6d}, {0xfa70, 0xfad9}, {0xfb00, 0xfb06}, {0xfb13, 0xfb17},
    {0xfb1d, 0xfb1d}, {0xfb1f, 0xfb28}, {0xfb2a, 0xfb36}, {0xfb38, 0xfb3c},
    {0xfb3e, 0xfb3e}, {0xfb40, 0xfb41}, {0xfb43, 0xfb44}, {0xfb46, 0xfbb1},
    {0xfbd3, 0xfd3d}, {0xfd50, 0xfd8f}, {0xfd92, 0xfdc7}, {0xfdf0, 0xfdfb},
    {0xfe70, 0xfe74}, {0xfe76, 0xfefc}, {0xff21, 0xff3a}, {0xff41, 0xff5a},
    {0xff66, 0xffbe}, {0xffc2, 0xffc7}, {0xffca, 0xffcf}, {0xffd2, 0xffd7},
    {0xffda, 0xffdc}, {0x10000, 0x1000b}, {0x1000d, 0x10026}, {0x10028, 0x1003a},
    {0x1003c, 0x1003d}, {0x1003f, 0x1004d}, {0x10050, 0x1005d}, {0x10080, 0x100fa},
    {0x10140, 0x10174}, {0x10280, 0x1029c}, {0x102a0, 0x102d0}, {0x10300, 0x1031f},
    {0x1032d, 0x1034a}, {0x10350, 0x10375}, {0x10380, 0x1039d}, {0x103a0, 0x103c3},
    {0x103c8, 0x103cf}, {0x103d1, 0x103d5}, {0x10400, 0x1049d}, {0x104b0, 0x104d3},
    {0x104d8, 0x104fb}, {0x10500, 0x10527}, {0x10530, 0x10563}, {0x10570, 0x1057a},
    {0x1057c, 0x1058a}, {0x1058c, 0x10592}, {0x10594, 0x10595}, {0x10597, 0x105a1},
    {0x105a3, 0x105b1}, {0x105b3, 0x105b9}, {0x105bb, 0x105bc}, {0x105c0, 0x105f3},
    {0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767}, {0x10780, 0x10785},
    {0x10787, 0x107b0}, {0x107b2, 0x107ba}, {0x10800, 0x10805}, {0x10808, 0x10808},
    {0x1080a, 0x10835}, {0x10837, 0x10838}, {0x1083c, 0x1083c}, {0x1083f, 0x10855},
    {0x10860, 0x10876}, {0x10880, 0x1089e}, {0x108e0, 0x108f2}, {0x108f4, 0x108f5},
    {0x10900, 0x10915}, {0x10920, 0x10939}, {0x10940, 0x10959}, {0x10980, 0x109b7},
    {0x109be, 0x109bf}, {0x10a00, 0x10a00}, {0x10a10, 0x10a13}, {0x10a15, 0x10a17},
    {0x10a19, 0x10a35}, {0x10a60, 0x10a7c}, {0x10a80, 0x10a9c}, {0x10ac0, 0x10ac7},
    {0x10ac9, 0x10ae4}, {0x10b00, 0x10b35}, {0x10b40, 0x10b55}, {0x10b60, 0x10b72},
    {0x10b80, 0x10b91}, {0x10c00, 0x10c48}, {0x10c80, 0x10cb2}, {0x10cc0, 0x10cf2},
    {0x10d00, 0x10d23}, {0x10d4a, 0x10d65}, {0x10d6f, 0x10d85}, {0x10e80, 0x10ea9},
    {0x10eb0, 0x10eb1}, {0x10ec2, 0x10ec7}, {0x10f00, 0x10f1c}, {0x10f27, 0x10f27},
    {0x10f30, 0x10f45}, {0x10f70, 0x10f81}, {0x10fb0, 0x10fc4}, {0x10fe0, 0x10ff6},
    {0x11003, 0x11037}, {0x11071, 0x11072}, {0x11075, 0x11075}, {0x11083, 0x110af},
    {0x110d0, 0x110e8}, {0x11103, 0x11126}, {0x11144, 0x11144}, {0x11147, 0x11147},
    {0x11150, 0x11172}, {0x11176, 0x11176}, {0x11183, 0x111b2}, {0x111c1, 0x111c4},
    {0x111da, 0x111da}, {0x111dc, 0x111dc}, {0x11200, 0x11211}, {0x11213, 0x1122b},
    {0x1123f, 0x11240}, {0x11280, 0x11286}, {0x11288, 0x11288}, {0x1128a, 0x1128d},
    {0x1128f, 0x1129d}, {0x1129f, 0x112a8}, {0x112b0, 0x112de}, {0x11305, 0x1130c},
    {0x1130f, 0x11310}, {0x11313, 0x11328}, {0x1132a, 0x11330}, {0x11332, 0x11333},
    {0x11335, 0x11339}, {0x1133d, 0x1133d}, {0x11350, 0x11350}, {0x1135d, 0x11361},
    {0x11380, 0x11389}, {0x1138b, 0x1138b}, {0x1138e, 0x1138e}, {0x11390, 0x113b5},
    {0x113b7, 0x113b7}, {0x113d1, 0x113d1}, {0x113d3, 0x113d3}, {0x11400, 0x11434},
    {0x11447, 0x1144a}, {0x1145f, 0x11461}, {0x11480, 0x114af}, {0x114c4, 0x114c5},
    {0x114c7, 0x114c7}, {0x11580, 0x115ae}, {0x115d8, 0x115db}, {0x11600, 0x1162f},
    {0x11644, 0x11644}, {0x11680, 0x116aa}, {0x116b8, 0x116b8}, {0x11700, 0x1171a},
    {0x11740, 0x11746}, {0x11800, 0x1182b}, {0x118a0, 0x118df}, {0x118ff, 0x11906},
    {0x11909, 0x11909}, {0x1190c, 0x11913}, {0x11915, 0x11916}, {0x11918, 0x1192f},
    {0x1193f, 0x1193f}, {0x11941, 0x11941}, {0x119a0, 0x119a7}, {0x119aa, 0x119d0},
    {0x119e1, 0x119e1}, {0x119e3, 0x119e3}, {0x11a00, 0x11a00}, {0x11a0b, 0x11a32},
    {0x11a3a, 0x11a3a}, {0x11a50, 0x11a50}, {0x11a5c, 0x11a89}, {0x11a9d, 0x11a9d},
    {0x11ab0, 0x11af8}, {0x11bc0, 0x11be0}, {0x11c00, 0x11c08}, {0x11c0a, 0x11c2e},
    {0x11c40, 0x11c40}, {0x11c72, 0x11c8f}, {0x11d00, 0x11d06}, {0x11d08, 0x11d09},
    {0x11d0b, 0x11d30}, {0x11d46, 0x11d46}, {0x11d60, 0x11d65}, {0x11d67, 0x11d68},
    {0x11d6a, 0x11d89}, {0x11d98, 0x11d98}, {0x11db0, 0x11ddb}, {0x11ee0, 0x11ef2},
    {0x11f02, 0x11f02}, {0x11f04, 0x11f10}, {0x11f12, 0x11f33}, {0x11fb0, 0x11fb0},
    {0x12000, 0x12399}, {0x12400, 0x1246e}, {0x12480, 0x12543}, {0x12f90, 0x12ff0},
    {0x13000, 0x1342f}, {0x13441, 0x13446}, {0x13460, 0x143fa}, {0x14400, 0x14646},
    {0x16100, 0x1611d}, {0x16800, 0x16a38}, {0x16a40, 0x16a5e}, {0x16a70, 0x16abe},
    {0x16ad0, 0x16aed}, {0x16b00, 0x16b2f}, {0x16b40, 0x16b43}, {0x16b63, 0x16b77},
    {0x16b7d, 0x16b8f}, {0x16d40, 0x16d6c}, {0x16e40, 0x16e7f}, {0x16ea0, 0x16eb8},
    {0x16ebb, 0x16ed3}, {0x16f00, 0x16f4a}, {0x16f50, 0x16f50}, {0x16f93, 0x16f9f},
    {0x16fe0, 0x16fe1}, {0x16fe3, 0x16fe3}, {0x16ff2, 0x16ff6}, {0x17000, 0x18cd5},
    {0x18cff, 0x18d1e}, {0x18d80, 0x18df2}, {0x1aff0, 0x1aff3}, {0x1aff5, 0x1affb},
    {0x1affd, 0x1affe}, {0x1b000, 0x1b122}, {0x1b132, 0x1b132}, {0x1b150, 0x1b152},
    {0x1b155, 0x1b155}, {0x1b164, 0x1b167}, {0x1b170, 0x1b2fb}, {0x1bc00, 0x1bc6a},
    {0x1bc70, 0x1bc7c}, {0x1bc80, 0x1bc88}, {0x1bc90, 0x1bc99}, {0x1d400, 0x1d454},
    {0x1d456, 0x1d49c}, {0x1d49e, 0x1d49f}, {0x1d4a2, 0x1d4a2}, {0x1d4a5, 0x1d4a6},
    {0x1d4a9, 0x1d4ac}, {0x1d4ae, 0x1d4b9}, {0x1d4bb, 0x1d4bb}, {0x1d4bd, 0x1d4c3},
    {0x1d4c5, 0x1d505}, {0x1d507, 0x1d50a}, {0x1d50d, 0x1d514}, {0x1d516, 0x1d51c},
    {0x1d51e, 0x1d539}, {0x1d53b, 0x1d53e}, {0x1d540, 0x1d544}, {0x1d546, 0x1d546},
    {0x1d54a, 0x1d550}, {0x1d552, 0x1d6a5}, {0x1d6a8, 0x1d6c0}, {0x1d6c2, 0x1d6da},
    {0x1d6dc, 0x1d6fa}, {0x1d6fc, 0x1d714}, {0x1d716, 0x1d734}, {0x1d736, 0x1d74e},
    {0x1d750, 0x1d76e}, {0x1d770, 0x1d788}, {0x1d78a, 0x1d7a8}, {0x1d7aa, 0x1d7c2},
    {0x1d7c4, 0x1d7cb}, {0x1df00, 0x1df1e}, {0x1df25, 0x1df2a}, {0x1e030, 0x1e06d},
    {0x1e100, 0x1e12c}, {0x1e137, 0x1e13d}, {0x1e14e, 0x1e14e}, {0x1e290, 0x1e2ad},
    {0x1e2c0, 0x1e2eb}, {0x1e4d0, 0x1e4eb}, {0x1e5d0, 0x1e5ed}, {0x1e5f0, 0x1e5f0},
    {0x1e6c0, 0x1e6de}, {0x1e6e0, 0x1e6e2}, {0x1e6e4, 0x1e6e5}, {0x1e6e7, 0x1e6ed},
    {0x1e6f0, 0x1e6f4}, {0x1e6fe, 0x1e6ff}, {0x1e7e0, 0x1e7e6}, {0x1e7e8, 0x1e7eb},
    {0x1e7ed, 0x1e7ee}, {0x1e7f0, 0x1e7fe}, {0x1e800, 0x1e8c4}, {0x1e900, 0x1e943},
    {0x1e94b, 0x1e94b}, {0x1ee00, 0x1ee03}, {0x1ee05, 0x1ee1f}, {0x1ee21, 0x1ee22},
    {0x1ee24, 0x1ee24}, {0x1ee27, 0x1ee27}, {0x1ee29, 0x1ee32}, {0x1ee34, 0x1ee37},
    {0x1ee39, 0x1ee39}, {0x1ee3b, 0x1ee3b}, {0x1ee42, 0x1ee42}, {0x1ee47, 0x1ee47},
    {0x1ee49, 0x1ee49}, {0x1ee4b, 0x1ee4b}, {0x1ee4d, 0x1ee4f}, {0x1ee51, 0x1ee52},
    {0x1ee54, 0x1ee54}, {0x1ee57, 0x1ee57}, {0x1ee59, 0x1ee59}, {0x1ee5b, 0x1ee5b},
    {0x1ee5d, 0x1ee5d}, {0x1ee5f, 0x1ee5f}, {0x1ee61, 0x1ee62}, {0x1ee64, 0x1ee64},
    {0x1ee67, 0x1ee6a}, {0x1ee6c, 0x1ee72}, {0x1ee74, 0x1ee77}, {0x1ee79, 0x1ee7c},
    {0x1ee7e, 0x1ee7e}, {0x1ee80, 0x1ee89}, {0x1ee8b, 0x1ee9b}, {0x1eea1, 0x1eea3},
    {0x1eea5, 0x1eea9}, {0x1eeab, 0x1eebb}, {0x20000, 0x2a6df}, {0x2a700, 0x2b81d},
    {0x2b820, 0x2cead}, {0x2ceb0, 0x2ebe0}, {0x2ebf0, 0x2ee5d}, {0x2f800, 0x2fa1d},
    {0x30000, 0x3134a}, {0x31350, 0x33479},
};
inline constexpr uint32_t vbind_id_part[][2] = {
    {0x24, 0x24}, {0x30, 0x39}, {0x41, 0x5a}, {0x5f, 0x5f},
    {0x61, 0x7a}, {0xaa, 0xaa}, {0xb5, 0xb5}, {0xb7, 0xb7},
    {0xba, 0xba}, {0xc0, 0xd6}, {0xd8, 0xf6}, {0xf8, 0x2c1},
    {0x2c6, 0x2d1}, {0x2e0, 0x2e4}, {0x2ec, 0x2ec}, {0x2ee, 0x2ee},
    {0x300, 0x374}, {0x376, 0x377}, {0x37a, 0x37d}, {0x37f, 0x37f},
    {0x386, 0x38a}, {0x38c, 0x38c}, {0x38e, 0x3a1}, {0x3a3, 0x3f5},
    {0x3f7, 0x481}, {0x483, 0x487}, {0x48a, 0x52f}, {0x531, 0x556},
    {0x559, 0x559}, {0x560, 0x588}, {0x591, 0x5bd}, {0x5bf, 0x5bf},
    {0x5c1, 0x5c2}, {0x5c4, 0x5c5}, {0x5c7, 0x5c7}, {0x5d0, 0x5ea},
    {0x5ef, 0x5f2}, {0x610, 0x61a}, {0x620, 0x669}, {0x66e, 0x6d3},
    {0x6d5, 0x6dc}, {0x6df, 0x6e8}, {0x6ea, 0x6fc}, {0x6ff, 0x6ff},
    {0x710, 0x74a}, {0x74d, 0x7b1}, {0x7c0, 0x7f5}, {0x7fa, 0x7fa},
    {0x7fd, 0x7fd}, {0x800, 0x82d}, {0x840, 0x85b}, {0x860, 0x86a},
    {0x870, 0x887}, {0x889, 0x88f}, {0x897, 0x8e1}, {0x8e3, 0x963},
    {0x966, 0x96f}, {0x971, 0x983}, {0x985, 0x98c}, {0x98f, 0x990},
    {0x993, 0x9a8}, {0x9aa, 0x9b0}, {0x9b2, 0x9b2}, {0x9b6, 0x9b9},
    {0x9bc, 0x9c4}, {0x9c7, 0x9c8}, {0x9cb, 0x9ce}, {0x9d7, 0x9d7},
    {0x9dc, 0x9dd}, {0x9df, 0x9e3}, {0x9e6, 0x9f1}, {0x9fc, 0x9fc},
    {0x9fe, 0x9fe}, {0xa01, 0xa03}, {0xa05, 0xa0a}, {0xa0f, 0xa10},
    {0xa13, 0xa28}, {0xa2a, 0xa30}, {0xa32, 0xa33}, {0xa35, 0xa36},
    {0xa38, 0xa39}, {0xa3c, 0xa3c}, {0xa3e, 0xa42}, {0xa47, 0xa48},
    {0xa4b, 0xa4d}, {0xa51, 0xa51}, {0xa59, 0xa5c}, {0xa5e, 0xa5e},
    {0xa66, 0xa75}, {0xa81, 0xa83}, {0xa85, 0xa8d}, {0xa8f, 0xa91},
    {0xa93, 0xaa8}, {0xaaa, 0xab0}, {0xab2, 0xab3}, {0xab5, 0xab9},
    {0xabc, 0xac5}, {0xac7, 0xac9}, {0xacb, 0xacd}, {0xad0, 0xad0},
    {0xae0, 0xae3}, {0xae6, 0xaef}, {0xaf9, 0xaff}, {0xb01, 0xb03},
    {0xb05, 0xb0c}, {0xb0f, 0xb10}, {0xb13, 0xb28}, {0xb2a, 0xb30},
    {0xb32, 0xb33}, {0xb35, 0xb39}, {0xb3c, 0xb44}, {0xb47, 0xb48},
    {0xb4b, 0xb4d}, {0xb55, 0xb57}, {0xb5c, 0xb5d}, {0xb5f, 0xb63},
    {0xb66, 0xb6f}, {0xb71, 0xb71}, {0xb82, 0xb83}, {0xb85, 0xb8a},
    {0xb8e, 0xb90}, {0xb92, 0xb95}, {0xb99, 0xb9a}, {0xb9c, 0xb9c},
    {0xb9e, 0xb9f}, {0xba3, 0xba4}, {0xba8, 0xbaa}, {0xbae, 0xbb9},
    {0xbbe, 0xbc2}, {0xbc6, 0xbc8}, {0xbca, 0xbcd}, {0xbd0, 0xbd0},
    {0xbd7, 0xbd7}, {0xbe6, 0xbef}, {0xc00, 0xc0c}, {0xc0e, 0xc10},
    {0xc12, 0xc28}, {0xc2a, 0xc39}, {0xc3c, 0xc44}, {0xc46, 0xc48},
    {0xc4a, 0xc4d}, {0xc55, 0xc56}, {0xc58, 0xc5a}, {0xc5c, 0xc5d},
    {0xc60, 0xc63}, {0xc66, 0xc6f}, {0xc80, 0xc83}, {0xc85, 0xc8c},
    {0xc8e, 0xc90}, {0xc92, 0xca8}, {0xcaa, 0xcb3}, {0xcb5, 0xcb9},
    {0xcbc, 0xcc4}, {0xcc6, 0xcc8}, {0xcca, 0xccd}, {0xcd5, 0xcd6},
    {0xcdc, 0xcde}, {0xce0, 0xce3}, {0xce6, 0xcef}, {0xcf1, 0xcf3},
    {0xd00, 0xd0c}, {0xd0e, 0xd10}, {0xd12, 0xd44}, {0xd46, 0xd48},
    {0xd4a, 0xd4e}, {0xd54, 0xd57}, {0xd5f, 0xd63}, {0xd66, 0xd6f},
    {0xd7a, 0xd7f}, {0xd81, 0xd83}, {0xd85, 0xd96}, {0xd9a, 0xdb1},
    {0xdb3, 0xdbb}, {0xdbd, 0xdbd}, {0xdc0, 0xdc6}, {0xdca, 0xdca},
    {0xdcf, 0xdd4}, {0xdd6, 0xdd6}, {0xdd8, 0xddf}, {0xde6, 0xdef},
    {0xdf2, 0xdf3}, {0xe01, 0xe3a}, {0xe40, 0xe4e}, {0xe50, 0xe59},
    {0xe81, 0xe82}, {0xe84, 0xe84}, {0xe86, 0xe8a}, {0xe8c, 0xea3},
    {0xea5, 0xea5}, {0xea7, 0xebd}, {0xec0, 0xec4}, {0xec6, 0xec6},
    {0xec8, 0xece}, {0xed0, 0xed9}, {0xedc, 0xedf}, {0xf00, 0xf00},
    {0xf18, 0xf19}, {0xf20, 0xf29}, {0xf35, 0xf35}, {0xf37, 0xf37},
    {0xf39, 0xf39}, {0xf3e, 0xf47}, {0xf49, 0xf6c}, {0xf71, 0xf84},
    {0xf86, 0xf97}, {0xf99, 0xfbc}, {0xfc6, 0xfc6}, {0x1000, 0x1049},
    {0x1050, 0x109d}, {0x10a0, 0x10c5}, {0x10c7, 0x10c7}, {0x10cd, 0x10cd},
    {0x10d0, 0x10fa}, {0x10fc, 0x1248}, {0x124a, 0x124d}, {0x1250, 0x1256},
    {0x1258, 0x1258}, {0x125a, 0x125d}, {0x1260, 0x1288}, {0x128a, 0x128d},
    {0x1290, 0x12b0}, {0x12b2, 0x12b5}, {0x12b8, 0x12be}, {0x12c0, 0x12c0},
    {0x12c2, 0x12c5}, {0x12c8, 0x12d6}, {0x12d8, 0x1310}, {0x1312, 0x1315},
    {0x1318, 0x135a}, {0x135d, 0x135f}, {0x1369, 0x1371}, {0x1380, 0x138f},
    {0x13a0, 0x13f5}, {0x13f8, 0x13fd}, {0x1401, 0x166c}, {0x166f, 0x167f},
    {0x1681, 0x169a}, {0x16a0, 0x16ea}, {0x16ee, 0x16f8}, {0x1700, 0x1715},
    {0x171f, 0x1734}, {0x1740, 0x1753}, {0x1760, 0x176c}, {0x176e, 0x1770},
    {0x1772, 0x1773}, {0x1780, 0x17d3}, {0x17d7, 0x17d7}, {0x17dc, 0x17dd},
    {0x17e0, 0x17e9}, {0x180b, 0x180d}, {0x180f, 0x1819}, {0x1820, 0x1878},
    {0x1880, 0x18aa}, {0x18b0, 0x18f5}, {0x1900, 0x191e}, {0x1920, 0x192b},
    {0x1930, 0x193b}, {0x1946, 0x196d}, {0x1970, 0x1974}, {0x1980, 0x19ab},
    {0x19b0, 0x19c9}, {0x19d0, 0x19da}, {0x1a00, 0x1a1b}, {0x1a20, 0x1a5e},
    {0x1a60, 0x1a7c}, {0x1a7f, 0x1a89}, {0x1a90, 0x1a99}, {0x1aa7, 0x1aa7},
    {0x1ab0, 0x1abd}, {0x1abf, 0x1add}, {0x1ae0, 0x1aeb}, {0x1b00, 0x1b4c},
    {0x1b50, 0x1b59}, {0x1b6b, 0x1b73}, {0x1b80, 0x1bf3}, {0x1c00, 0x1c37},
    {0x1c40, 0x1c49}, {0x1c4d, 0x1c7d}, {0x1c80, 0x1c8a}, {0x1c90, 0x1cba},
    {0x1cbd, 0x1cbf}, {0x1cd0, 0x1cd2}, {0x1cd4, 0x1cfa}, {0x1d00, 0x1f15},
    {0x1f18, 0x1f1d}, {0x1f20, 0x1f45}, {0x1f48, 0x1f4d}, {0x1f50, 0x1f57},
    {0x1f59, 0x1f59}, {0x1f5b, 0x1f5b}, {0x1f5d, 0x1f5d}, {0x1f5f, 0x1f7d},
    {0x1f80, 0x1fb4}, {0x1fb6, 0x1fbc}, {0x1fbe, 0x1fbe}, {0x1fc2, 0x1fc4},
    {0x1fc6, 0x1fcc}, {0x1fd0, 0x1fd3}, {0x1fd6, 0x1fdb}, {0x1fe0, 0x1fec},
    {0x1ff2, 0x1ff4}, {0x1ff6, 0x1ffc}, {0x200c, 0x200d}, {0x203f, 0x2040},
    {0x2054, 0x2054}, {0x2071, 0x2071}, {0x207f, 0x207f}, {0x2090, 0x209c},
    {0x20d0, 0x20dc}, {0x20e1, 0x20e1}, {0x20e5, 0x20f0}, {0x2102, 0x2102},
    {0x2107, 0x2107}, {0x210a, 0x2113}, {0x2115, 0x2115}, {0x2118, 0x211d},
    {0x2124, 0x2124}, {0x2126, 0x2126}, {0x2128, 0x2128}, {0x212a, 0x2139},
    {0x213c, 0x213f}, {0x2145, 0x2149}, {0x214e, 0x214e}, {0x2160, 0x2188},
    {0x2c00, 0x2ce4}, {0x2ceb, 0x2cf3}, {0x2d00, 0x2d25}, {0x2d27, 0x2d27},
    {0x2d2d, 0x2d2d}, {0x2d30, 0x2d67}, {0x2d6f, 0x2d6f}, {0x2d7f, 0x2d96},
    {0x2da0, 0x2da6}, {0x2da8, 0x2dae}, {0x2db0, 0x2db6}, {0x2db8, 0x2dbe},
    {0x2dc0, 0x2dc6}, {0x2dc8, 0x2dce}, {0x2dd0, 0x2dd6}, {0x2dd8, 0x2dde},
    {0x2de0, 0x2dff}, {0x3005, 0x3007}, {0x3021, 0x302f}, {0x3031, 0x3035},
    {0x3038, 0x303c}, {0x3041, 0x3096}, {0x3099, 0x309f}, {0x30a1, 0x30ff},
    {0x3105, 0x312f}, {0x3131, 0x318e}, {0x31a0, 0x31bf}, {0x31f0, 0x31ff},
    {0x3400, 0x4dbf}, {0x4e00, 0xa48c}, {0xa4d0, 0xa4fd}, {0xa500, 0xa60c},
    {0xa610, 0xa62b}, {0xa640, 0xa66f}, {0xa674, 0xa67d}, {0xa67f, 0xa6f1},
    {0xa717, 0xa71f}, {0xa722, 0xa788}, {0xa78b, 0xa7dc}, {0xa7f1, 0xa827},
    {0xa82c, 0xa82c}, {0xa840, 0xa873}, {0xa880, 0xa8c5}, {0xa8d0, 0xa8d9},
    {0xa8e0, 0xa8f7}, {0xa8fb, 0xa8fb}, {0xa8fd, 0xa92d}, {0xa930, 0xa953},
    {0xa960, 0xa97c}, {0xa980, 0xa9c0}, {0xa9cf, 0xa9d9}, {0xa9e0, 0xa9fe},
    {0xaa00, 0xaa36}, {0xaa40, 0xaa4d}, {0xaa50, 0xaa59}, {0xaa60, 0xaa76},
    {0xaa7a, 0xaac2}, {0xaadb, 0xaadd}, {0xaae0, 0xaaef}, {0xaaf2, 0xaaf6},
    {0xab01, 0xab06}, {0xab09, 0xab0e}, {0xab11, 0xab16}, {0xab20, 0xab26},
    {0xab28, 0xab2e}, {0xab30, 0xab5a}, {0xab5c, 0xab69}, {0xab70, 0xabea},
    {0xabec, 0xabed}, {0xabf0, 0xabf9}, {0xac00, 0xd7a3}, {0xd7b0, 0xd7c6},
    {0xd7cb, 0xd7fb}, {0xf900, 0xfa6d}, {0xfa70, 0xfad9}, {0xfb00, 0xfb06},
    {0xfb13, 0xfb17}, {0xfb1d, 0xfb28}, {0xfb2a, 0xfb36}, {0xfb38, 0xfb3c},
    {0xfb3e, 0xfb3e}, {0xfb40, 0xfb41}, {0xfb43, 0xfb44}, {0xfb46, 0xfbb1},
    {0xfbd3, 0xfd3d}, {0xfd50, 0xfd8f}, {0xfd92, 0xfdc7}, {0xfdf0, 0xfdfb},
    {0xfe00, 0xfe0f}, {0xfe20, 0xfe2f}, {0xfe33, 0xfe34}, {0xfe4d, 0xfe4f},
    {0xfe70, 0xfe74}, {0xfe76, 0xfefc}, {0xff10, 0xff19}, {0xff21, 0xff3a},
    {0xff3f, 0xff3f}, {0xff41, 0xff5a}, {0xff65, 0xffbe}, {0xffc2, 0xffc7},
    {0xffca, 0xffcf}, {0xffd2, 0xffd7}, {0xffda, 0xffdc}, {0x10000, 0x1000b},
    {0x1000d, 0x10026}, {0x10028, 0x1003a}, {0x1003c, 0x1003d}, {0x1003f, 0x1004d},
    {0x10050, 0x1005d}, {0x10080, 0x100fa}, {0x10140, 0x10174}, {0x101fd, 0x101fd},
    {0x10280, 0x1029c}, {0x102a0, 0x102d0}, {0x102e0, 0x102e0}, {0x10300, 0x1031f},
    {0x1032d, 0x1034a}, {0x10350, 0x1037a}, {0x10380, 0x1039d}, {0x103a0, 0x103c3},
    {0x103c8, 0x103cf}, {0x103d1, 0x103d5}, {0x10400, 0x1049d}, {0x104a0, 0x104a9},
    {0x104b0, 0x104d3}, {0x104d8, 0x104fb}, {0x10500, 0x10527}, {0x10530, 0x10563},
    {0x10570, 0x1057a}, {0x1057c, 0x1058a}, {0x1058c, 0x10592}, {0x10594, 0x10595},
    {0x10597, 0x105a1}, {0x105a3, 0x105b1}, {0x105b3, 0x105b9}, {0x105bb, 0x105bc},
    {0x105c0, 0x105f3}, {0x10600, 0x10736}, {0x10740, 0x10755}, {0x10760, 0x10767},
    {0x10780, 0x10785}, {0x10787, 0x107b0}, {0x107b2, 0x107ba}, {0x10800, 0x10805},
    {0x10808, 0x10808}, {0x1080a, 0x10835}, {0x10837, 0x10838}, {0x1083c, 0x1083c},
    {0x1083f, 0x10855}, {0x10860, 0x10876}, {0x10880, 0x1089e}, {0x108e0, 0x108f2},
    {0x108f4, 0x108f5}, {0x10900, 0x10915}, {0x10920, 0x10939}, {0x10940, 0x10959},
    {0x10980, 0x109b7}, {0x109be, 0x109bf}, {0x10a00, 0x10a03}, {0x10a05, 0x10a06},
    {0x10a0c, 0x10a13}, {0x10a15, 0x10a17}, {0x10a19, 0x10a35}, {0x10a38, 0x10a3a},
    {0x10a3f, 0x10a3f}, {0x10a60, 0x10a7c}, {0x10a80, 0x10a9c}, {0x10ac0, 0x10ac7},
    {0x10ac9, 0x10ae6}, {0x10b00, 0x10b35}, {0x10b40, 0x10b55}, {0x10b60, 0x10b72},
    {0x10b80, 0x10b91}, {0x10c00, 0x10c48}, {0x10c80, 0x10cb2}, {0x10cc0, 0x10cf2},
    {0x10d00, 0x10d27}, {0x10d30, 0x10d39}, {0x10d40, 0x10d65}, {0x10d69, 0x10d6d},
    {0x10d6f, 0x10d85}, {0x10e80, 0x10ea9}, {0x10eab, 0x10eac}, {0x10eb0, 0x10eb1},
    {0x10ec2, 0x10ec7}, {0x10efa, 0x10f1c}, {0x10f27, 0x10f27}, {0x10f30, 0x10f50},
    {0x10f70, 0x10f85}, {0x10fb0, 0x10fc4}, {0x10fe0, 0x10ff6}, {0x11000, 0x11046},
    {0x11066, 0x11075}, {0x1107f, 0x110ba}, {0x110c2, 0x110c2}, {0x110d0, 0x110e8},
    {0x110f0, 0x110f9}, {0x11100, 0x11134}, {0x11136, 0x1113f}, {0x11144, 0x11147},
    {0x11150, 0x11173}, {0x11176, 0x11176}, {0x11180, 0x111c4}, {0x111c9, 0x111cc},
    {0x111ce, 0x111da}, {0x111dc, 0x111dc}, {0x11200, 0x11211}, {0x11213, 0x11237},
    {0x1123e, 0x11241}, {0x11280, 0x11286}, {0x11288, 0x11288}, {0x1128a, 0x1128d},
    {0x1128f, 0x1129d}, {0x1129f, 0x112a8}, {0x112b0, 0x112ea}, {0x112f0, 0x112f9},
    {0x11300, 0x11303}, {0x11305, 0x1130c}, {0x1130f, 0x11310}, {0x11313, 0x11328},
    {0x1132a, 0x11330}, {0x11332, 0x11333}, {0x11335, 0x11339}, {0x1133b, 0x11344},
    {0x11347, 0x11348}, {0x1134b, 0x1134d}, {0x11350, 0x11350}, {0x11357, 0x11357},
    {0x1135d, 0x11363}, {0x11366, 0x1136c}, {0x11370, 0x11374}, {0x11380, 0x11389},
    {0x1138b, 0x1138b}, {0x1138e, 0x1138e}, {0x11390, 0x113b5}, {0x113b7, 0x113c0},
    {0x113c2, 0x113c2}, {0x113c5, 0x113c5}, {0x113c7, 0x113ca}, {0x113cc, 0x113d3},
    {0x113e1, 0x113e2}, {0x11400, 0x1144a}, {0x11450, 0x11459}, {0x1145e, 0x11461},
    {0x11480, 0x114c5}, {0x114c7, 0x114c7}, {0x114d0, 0x114d9}, {0x11580, 0x115b5},
    {0x115b8, 0x115c0}, {0x115d8, 0x115dd}, {0x11600, 0x11640}, {0x11644, 0x11644},
    {0x11650, 0x11659}, {0x11680, 0x116b8}, {0x116c0, 0x116c9}, {0x116d0, 0x116e3},
    {0x11700, 0x1171a}, {0x1171d, 0x1172b}, {0x11730, 0x11739}, {0x11740, 0x11746},
    {0x11800, 0x1183a}, {0x118a0, 0x118e9}, {0x118ff, 0x11906}, {0x11909, 0x11909},
    {0x1190c, 0x11913}, {0x11915, 0x11916}, {0x11918, 0x11935}, {0x11937, 0x11938},
    {0x1193b, 0x11943}, {0x11950, 0x11959}, {0x119a0, 0x119a7}, {0x119aa, 0x119d7},
    {0x119da, 0x119e1}, {0x119e3, 0x119e4}, {0x11a00, 0x11a3e}, {0x11a47, 0x11a47},
    {0x11a50, 0x11a99}, {0x11a9d, 0x11a9d}, {0x11ab0, 0x11af8}, {0x11b60, 0x11b67},
    {0x11bc0, 0x11be0}, {0x11bf0, 0x11bf9}, {0x11c00, 0x11c08}, {0x11c0a, 0x11c36},
    {0x11c38, 0x11c40}, {0x11c50, 0x11c59}, {0x11c72, 0x11c8f}, {0x11c92, 0x11ca7},
    {0x11ca9, 0x11cb6}, {0x11d00, 0x11d06}, {0x11d08, 0x11d09}, {0x11d0b, 0x11d36},
    {0x11d3a, 0x11d3a}, {0x11d3c, 0x11d3d}, {0x11d3f, 0x11d47}, {0x11d50, 0x11d59},
    {0x11d60, 0x11d65}, {0x11d67, 0x11d68}, {0x11d6a, 0x11d8e}, {0x11d90, 0x11d91},
    {0x11d93, 0x11d98}, {0x11da0, 0x11da9}, {0x11db0, 0x11ddb}, {0x11de0, 0x11de9},
    {0x11ee0, 0x11ef6}, {0x11f00, 0x11f10}, {0x11f12, 0x11f3a}, {0x11f3e, 0x11f42},
    {0x11f50, 0x11f5a}, {0x11fb0, 0x11fb0}, {0x12000, 0x12399}, {0x12400, 0x1246e},
    {0x12480, 0x12543}, {0x12f90, 0x12ff0}, {0x13000, 0x1342f}, {0x13440, 0x13455},
    {0x13460, 0x143fa}, {0x14400, 0x14646}, {0x16100, 0x16139}, {0x16800, 0x16a38},
    {0x16a40, 0x16a5e}, {0x16a60, 0x16a69}, {0x16a70, 0x16abe}, {0x16ac0, 0x16ac9},
    {0x16ad0, 0x16aed}, {0x16af0, 0x16af4}, {0x16b00, 0x16b36}, {0x16b40, 0x16b43},
    {0x16b50, 0x16b59}, {0x16b63, 0x16b77}, {0x16b7d, 0x16b8f}, {0x16d40, 0x16d6c},
    {0x16d70, 0x16d79}, {0x16e40, 0x16e7f}, {0x16ea0, 0x16eb8}, {0x16ebb, 0x16ed3},
    {0x16f00, 0x16f4a}, {0x16f4f, 0x16f87}, {0x16f8f, 0x16f9f}, {0x16fe0, 0x16fe1},
    {0x16fe3, 0x16fe4}, {0x16ff0, 0x16ff6}, {0x17000, 0x18cd5}, {0x18cff, 0x18d1e},
    {0x18d80, 0x18df2}, {0x1aff0, 0x1aff3}, {0x1aff5, 0x1affb}, {0x1affd, 0x1affe},
    {0x1b000, 0x1b122}, {0x1b132, 0x1b132}, {0x1b150, 0x1b152}, {0x1b155, 0x1b155},
    {0x1b164, 0x1b167}, {0x1b170, 0x1b2fb}, {0x1bc00, 0x1bc6a}, {0x1bc70, 0x1bc7c},
    {0x1bc80, 0x1bc88}, {0x1bc90, 0x1bc99}, {0x1bc9d, 0x1bc9e}, {0x1ccf0, 0x1ccf9},
    {0x1cf00, 0x1cf2d}, {0x1cf30, 0x1cf46}, {0x1d165, 0x1d169}, {0x1d16d, 0x1d172},
    {0x1d17b, 0x1d182}, {0x1d185, 0x1d18b}, {0x1d1aa, 0x1d1ad}, {0x1d242, 0x1d244},
    {0x1d400, 0x1d454}, {0x1d456, 0x1d49c}, {0x1d49e, 0x1d49f}, {0x1d4a2, 0x1d4a2},
    {0x1d4a5, 0x1d4a6}, {0x1d4a9, 0x1d4ac}, {0x1d4ae, 0x1d4b9}, {0x1d4bb, 0x1d4bb},
    {0x1d4bd, 0x1d4c3}, {0x1d4c5, 0x1d505}, {0x1d507, 0x1d50a}, {0x1d50d, 0x1d514},
    {0x1d516, 0x1d51c}, {0x1d51e, 0x1d539}, {0x1d53b, 0x1d53e}, {0x1d540, 0x1d544},
    {0x1d546, 0x1d546}, {0x1d54a, 0x1d550}, {0x1d552, 0x1d6a5}, {0x1d6a8, 0x1d6c0},
    {0x1d6c2, 0x1d6da}, {0x1d6dc, 0x1d6fa}, {0x1d6fc, 0x1d714}, {0x1d716, 0x1d734},
    {0x1d736, 0x1d74e}, {0x1d750, 0x1d76e}, {0x1d770, 0x1d788}, {0x1d78a, 0x1d7a8},
    {0x1d7aa, 0x1d7c2}, {0x1d7c4, 0x1d7cb}, {0x1d7ce, 0x1d7ff}, {0x1da00, 0x1da36},
    {0x1da3b, 0x1da6c}, {0x1da75, 0x1da75}, {0x1da84, 0x1da84}, {0x1da9b, 0x1da9f},
    {0x1daa1, 0x1daaf}, {0x1df00, 0x1df1e}, {0x1df25, 0x1df2a}, {0x1e000, 0x1e006},
    {0x1e008, 0x1e018}, {0x1e01b, 0x1e021}, {0x1e023, 0x1e024}, {0x1e026, 0x1e02a},
    {0x1e030, 0x1e06d}, {0x1e08f, 0x1e08f}, {0x1e100, 0x1e12c}, {0x1e130, 0x1e13d},
    {0x1e140, 0x1e149}, {0x1e14e, 0x1e14e}, {0x1e290, 0x1e2ae}, {0x1e2c0, 0x1e2f9},
    {0x1e4d0, 0x1e4f9}, {0x1e5d0, 0x1e5fa}, {0x1e6c0, 0x1e6de}, {0x1e6e0, 0x1e6f5},
    {0x1e6fe, 0x1e6ff}, {0x1e7e0, 0x1e7e6}, {0x1e7e8, 0x1e7eb}, {0x1e7ed, 0x1e7ee},
    {0x1e7f0, 0x1e7fe}, {0x1e800, 0x1e8c4}, {0x1e8d0, 0x1e8d6}, {0x1e900, 0x1e94b},
    {0x1e950, 0x1e959}, {0x1ee00, 0x1ee03}, {0x1ee05, 0x1ee1f}, {0x1ee21, 0x1ee22},
    {0x1ee24, 0x1ee24}, {0x1ee27, 0x1ee27}, {0x1ee29, 0x1ee32}, {0x1ee34, 0x1ee37},
    {0x1ee39, 0x1ee39}, {0x1ee3b, 0x1ee3b}, {0x1ee42, 0x1ee42}, {0x1ee47, 0x1ee47},
    {0x1ee49, 0x1ee49}, {0x1ee4b, 0x1ee4b}, {0x1ee4d, 0x1ee4f}, {0x1ee51, 0x1ee52},
    {0x1ee54, 0x1ee54}, {0x1ee57, 0x1ee57}, {0x1ee59, 0x1ee59}, {0x1ee5b, 0x1ee5b},
    {0x1ee5d, 0x1ee5d}, {0x1ee5f, 0x1ee5f}, {0x1ee61, 0x1ee62}, {0x1ee64, 0x1ee64},
    {0x1ee67, 0x1ee6a}, {0x1ee6c, 0x1ee72}, {0x1ee74, 0x1ee77}, {0x1ee79, 0x1ee7c},
    {0x1ee7e, 0x1ee7e}, {0x1ee80, 0x1ee89}, {0x1ee8b, 0x1ee9b}, {0x1eea1, 0x1eea3},
    {0x1eea5, 0x1eea9}, {0x1eeab, 0x1eebb}, {0x1fbf0, 0x1fbf9}, {0x20000, 0x2a6df},
    {0x2a700, 0x2b81d}, {0x2b820, 0x2cead}, {0x2ceb0, 0x2ebe0}, {0x2ebf0, 0x2ee5d},
    {0x2f800, 0x2fa1d}, {0x30000, 0x3134a}, {0x31350, 0x33479}, {0xe0100, 0xe01ef},
};
inline bool valid_name_code_point(char32_t code_point, bool first) {
  const auto* t = first ? vbind_id_start : vbind_id_part;
  size_t n = first ? std::size(vbind_id_start) : std::size(vbind_id_part);
  size_t lo = 0, hi = n;
  while (lo < hi) {
    size_t mid = (lo + hi) / 2;
    if (t[mid][1] < code_point) lo = mid + 1; else hi = mid;
  }
  return lo < n && t[lo][0] <= code_point;
}
}  // namespace ada::idna

/* begin file include/ada/expected.h */
/**
 * @file expected.h
 * @brief Definitions for std::expected
 * @private Excluded from docs through the doxygen file.
 */
///
// expected - An implementation of std::expected with extensions
// Written in 2017 by Sy Brand (tartanllama@gmail.com, @TartanLlama)
//
// Documentation available at http://tl.tartanllama.xyz/
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to the
// public domain worldwide. This software is distributed without any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software. If not, see
// <http://creativecommons.org/publicdomain/zero/1.0/>.
///

#ifndef TL_EXPECTED_HPP
#define TL_EXPECTED_HPP

#define TL_EXPECTED_VERSION_MAJOR 1
#define TL_EXPECTED_VERSION_MINOR 1
#define TL_EXPECTED_VERSION_PATCH 0

#include <exception>
#include <functional>
#include <type_traits>
#include <utility>

#if defined(__EXCEPTIONS) || defined(_CPPUNWIND)
#define TL_EXPECTED_EXCEPTIONS_ENABLED
#endif

#if (defined(_MSC_VER) && _MSC_VER == 1900)
#define TL_EXPECTED_MSVC2015
#define TL_EXPECTED_MSVC2015_CONSTEXPR
#else
#define TL_EXPECTED_MSVC2015_CONSTEXPR constexpr
#endif

#if (defined(__GNUC__) && __GNUC__ == 4 && __GNUC_MINOR__ <= 9 && \
     !defined(__clang__))
#define TL_EXPECTED_GCC49
#endif

#if (defined(__GNUC__) && __GNUC__ == 5 && __GNUC_MINOR__ <= 4 && \
     !defined(__clang__))
#define TL_EXPECTED_GCC54
#endif

#if (defined(__GNUC__) && __GNUC__ == 5 && __GNUC_MINOR__ <= 5 && \
     !defined(__clang__))
#define TL_EXPECTED_GCC55
#endif

#if !defined(TL_ASSERT)
// can't have assert in constexpr in C++11 and GCC 4.9 has a compiler bug
#if (__cplusplus > 201103L) && !defined(TL_EXPECTED_GCC49)
#include <cassert>
#define TL_ASSERT(x) assert(x)
#else
#define TL_ASSERT(x)
#endif
#endif

#if (defined(__GNUC__) && __GNUC__ == 4 && __GNUC_MINOR__ <= 9 && \
     !defined(__clang__))
// GCC < 5 doesn't support overloading on const&& for member functions

#define TL_EXPECTED_NO_CONSTRR
// GCC < 5 doesn't support some standard C++11 type traits
#define TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(T) \
  std::has_trivial_copy_constructor<T>
#define TL_EXPECTED_IS_TRIVIALLY_COPY_ASSIGNABLE(T) \
  std::has_trivial_copy_assign<T>

// This one will be different for GCC 5.7 if it's ever supported
#define TL_EXPECTED_IS_TRIVIALLY_DESTRUCTIBLE(T) \
  std::is_trivially_destructible<T>

// GCC 5 < v < 8 has a bug in is_trivially_copy_constructible which breaks
// std::vector for non-copyable types
#elif (defined(__GNUC__) && __GNUC__ < 8 && !defined(__clang__))
#ifndef TL_GCC_LESS_8_TRIVIALLY_COPY_CONSTRUCTIBLE_MUTEX
#define TL_GCC_LESS_8_TRIVIALLY_COPY_CONSTRUCTIBLE_MUTEX
namespace tl {
namespace detail {
template <class T>
struct is_trivially_copy_constructible
    : std::is_trivially_copy_constructible<T> {};
#ifdef _GLIBCXX_VECTOR
template <class T, class A>
struct is_trivially_copy_constructible<std::vector<T, A>> : std::false_type {};
#endif
}  // namespace detail
}  // namespace tl
#endif

#define TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(T) \
  tl::detail::is_trivially_copy_constructible<T>
#define TL_EXPECTED_IS_TRIVIALLY_COPY_ASSIGNABLE(T) \
  std::is_trivially_copy_assignable<T>
#define TL_EXPECTED_IS_TRIVIALLY_DESTRUCTIBLE(T) \
  std::is_trivially_destructible<T>
#else
#define TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(T) \
  std::is_trivially_copy_constructible<T>
#define TL_EXPECTED_IS_TRIVIALLY_COPY_ASSIGNABLE(T) \
  std::is_trivially_copy_assignable<T>
#define TL_EXPECTED_IS_TRIVIALLY_DESTRUCTIBLE(T) \
  std::is_trivially_destructible<T>
#endif

#if __cplusplus > 201103L
#define TL_EXPECTED_CXX14
#endif

#ifdef TL_EXPECTED_GCC49
#define TL_EXPECTED_GCC49_CONSTEXPR
#else
#define TL_EXPECTED_GCC49_CONSTEXPR constexpr
#endif

#if (__cplusplus == 201103L || defined(TL_EXPECTED_MSVC2015) || \
     defined(TL_EXPECTED_GCC49))
#define TL_EXPECTED_11_CONSTEXPR
#else
#define TL_EXPECTED_11_CONSTEXPR constexpr
#endif

namespace tl {
template <class T, class E>
class expected;

#ifndef TL_MONOSTATE_INPLACE_MUTEX
#define TL_MONOSTATE_INPLACE_MUTEX
class monostate {};

struct in_place_t {
  explicit in_place_t() = default;
};
static constexpr in_place_t in_place{};
#endif

template <class E>
class unexpected {
 public:
  static_assert(!std::is_same<E, void>::value, "E must not be void");

  unexpected() = delete;
  constexpr explicit unexpected(const E& e) : m_val(e) {}

  constexpr explicit unexpected(E&& e) : m_val(std::move(e)) {}

  template <class... Args, typename std::enable_if<std::is_constructible<
                               E, Args&&...>::value>::type* = nullptr>
  constexpr explicit unexpected(Args&&... args)
      : m_val(std::forward<Args>(args)...) {}
  template <
      class U, class... Args,
      typename std::enable_if<std::is_constructible<
          E, std::initializer_list<U>&, Args&&...>::value>::type* = nullptr>
  constexpr explicit unexpected(std::initializer_list<U> l, Args&&... args)
      : m_val(l, std::forward<Args>(args)...) {}

  constexpr const E& value() const& { return m_val; }
  TL_EXPECTED_11_CONSTEXPR E& value() & { return m_val; }
  TL_EXPECTED_11_CONSTEXPR E&& value() && { return std::move(m_val); }
  constexpr const E&& value() const&& { return std::move(m_val); }

 private:
  E m_val;
};

#ifdef __cpp_deduction_guides
template <class E>
unexpected(E) -> unexpected<E>;
#endif

template <class E>
constexpr bool operator==(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() == rhs.value();
}
template <class E>
constexpr bool operator!=(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() != rhs.value();
}
template <class E>
constexpr bool operator<(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() < rhs.value();
}
template <class E>
constexpr bool operator<=(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() <= rhs.value();
}
template <class E>
constexpr bool operator>(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() > rhs.value();
}
template <class E>
constexpr bool operator>=(const unexpected<E>& lhs, const unexpected<E>& rhs) {
  return lhs.value() >= rhs.value();
}

template <class E>
unexpected<typename std::decay<E>::type> make_unexpected(E&& e) {
  return unexpected<typename std::decay<E>::type>(std::forward<E>(e));
}

struct unexpect_t {
  unexpect_t() = default;
};
static constexpr unexpect_t unexpect{};

namespace detail {
template <typename E>
[[noreturn]] TL_EXPECTED_11_CONSTEXPR void throw_exception(E&& e) {
#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
  throw std::forward<E>(e);
#else
  (void)e;
#ifdef _MSC_VER
  __assume(0);
#else
  __builtin_unreachable();
#endif
#endif
}

#ifndef TL_TRAITS_MUTEX
#define TL_TRAITS_MUTEX
// C++14-style aliases for brevity
template <class T>
using remove_const_t = typename std::remove_const<T>::type;
template <class T>
using remove_reference_t = typename std::remove_reference<T>::type;
template <class T>
using decay_t = typename std::decay<T>::type;
template <bool E, class T = void>
using enable_if_t = typename std::enable_if<E, T>::type;
template <bool B, class T, class F>
using conditional_t = typename std::conditional<B, T, F>::type;

// std::conjunction from C++17
template <class...>
struct conjunction : std::true_type {};
template <class B>
struct conjunction<B> : B {};
template <class B, class... Bs>
struct conjunction<B, Bs...>
    : std::conditional<bool(B::value), conjunction<Bs...>, B>::type {};

#if defined(_LIBCPP_VERSION) && __cplusplus == 201103L
#define TL_TRAITS_LIBCXX_MEM_FN_WORKAROUND
#endif

// In C++11 mode, there's an issue in libc++'s std::mem_fn
// which results in a hard-error when using it in a noexcept expression
// in some cases. This is a check to workaround the common failing case.
#ifdef TL_TRAITS_LIBCXX_MEM_FN_WORKAROUND
template <class T>
struct is_pointer_to_non_const_member_func : std::false_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...)>
    : std::true_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...) &>
    : std::true_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...) &&>
    : std::true_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...) volatile>
    : std::true_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...) volatile&>
    : std::true_type {};
template <class T, class Ret, class... Args>
struct is_pointer_to_non_const_member_func<Ret (T::*)(Args...) volatile&&>
    : std::true_type {};

template <class T>
struct is_const_or_const_ref : std::false_type {};
template <class T>
struct is_const_or_const_ref<T const&> : std::true_type {};
template <class T>
struct is_const_or_const_ref<T const> : std::true_type {};
#endif

// std::invoke from C++17
// https://stackoverflow.com/questions/38288042/c11-14-invoke-workaround
template <
    typename Fn, typename... Args,
#ifdef TL_TRAITS_LIBCXX_MEM_FN_WORKAROUND
    typename = enable_if_t<!(is_pointer_to_non_const_member_func<Fn>::value &&
                             is_const_or_const_ref<Args...>::value)>,
#endif
    typename = enable_if_t<std::is_member_pointer<decay_t<Fn>>::value>, int = 0>
constexpr auto invoke(Fn&& f, Args&&... args) noexcept(
    noexcept(std::mem_fn(f)(std::forward<Args>(args)...)))
    -> decltype(std::mem_fn(f)(std::forward<Args>(args)...)) {
  return std::mem_fn(f)(std::forward<Args>(args)...);
}

template <typename Fn, typename... Args,
          typename = enable_if_t<!std::is_member_pointer<decay_t<Fn>>::value>>
constexpr auto invoke(Fn&& f, Args&&... args) noexcept(
    noexcept(std::forward<Fn>(f)(std::forward<Args>(args)...)))
    -> decltype(std::forward<Fn>(f)(std::forward<Args>(args)...)) {
  return std::forward<Fn>(f)(std::forward<Args>(args)...);
}

// std::invoke_result from C++17
template <class F, class, class... Us>
struct invoke_result_impl;

template <class F, class... Us>
struct invoke_result_impl<
    F,
    decltype(detail::invoke(std::declval<F>(), std::declval<Us>()...), void()),
    Us...> {
  using type =
      decltype(detail::invoke(std::declval<F>(), std::declval<Us>()...));
};

template <class F, class... Us>
using invoke_result = invoke_result_impl<F, void, Us...>;

template <class F, class... Us>
using invoke_result_t = typename invoke_result<F, Us...>::type;

#if defined(_MSC_VER) && _MSC_VER <= 1900
// TODO make a version which works with MSVC 2015
template <class T, class U = T>
struct is_swappable : std::true_type {};

template <class T, class U = T>
struct is_nothrow_swappable : std::true_type {};
#else
// https://stackoverflow.com/questions/26744589/what-is-a-proper-way-to-implement-is-swappable-to-test-for-the-swappable-concept
namespace swap_adl_tests {
// if swap ADL finds this then it would call std::swap otherwise (same
// signature)
struct tag {};

template <class T>
tag swap(T&, T&);
template <class T, std::size_t N>
tag swap(T (&a)[N], T (&b)[N]);

// helper functions to test if an unqualified swap is possible, and if it
// becomes std::swap
template <class, class>
std::false_type can_swap(...) noexcept(false);
template <class T, class U,
          class = decltype(swap(std::declval<T&>(), std::declval<U&>()))>
std::true_type can_swap(int) noexcept(noexcept(swap(std::declval<T&>(),
                                                    std::declval<U&>())));

template <class, class>
std::false_type uses_std(...);
template <class T, class U>
std::is_same<decltype(swap(std::declval<T&>(), std::declval<U&>())), tag>
uses_std(int);

template <class T>
struct is_std_swap_noexcept
    : std::integral_constant<bool,
                             std::is_nothrow_move_constructible<T>::value &&
                                 std::is_nothrow_move_assignable<T>::value> {};

template <class T, std::size_t N>
struct is_std_swap_noexcept<T[N]> : is_std_swap_noexcept<T> {};

template <class T, class U>
struct is_adl_swap_noexcept
    : std::integral_constant<bool, noexcept(can_swap<T, U>(0))> {};
}  // namespace swap_adl_tests

template <class T, class U = T>
struct is_swappable
    : std::integral_constant<
          bool,
          decltype(detail::swap_adl_tests::can_swap<T, U>(0))::value &&
              (!decltype(detail::swap_adl_tests::uses_std<T, U>(0))::value ||
               (std::is_move_assignable<T>::value &&
                std::is_move_constructible<T>::value))> {};

template <class T, std::size_t N>
struct is_swappable<T[N], T[N]>
    : std::integral_constant<
          bool,
          decltype(detail::swap_adl_tests::can_swap<T[N], T[N]>(0))::value &&
              (!decltype(detail::swap_adl_tests::uses_std<T[N], T[N]>(
                   0))::value ||
               is_swappable<T, T>::value)> {};

template <class T, class U = T>
struct is_nothrow_swappable
    : std::integral_constant<
          bool,
          is_swappable<T, U>::value &&
              ((decltype(detail::swap_adl_tests::uses_std<T, U>(0))::value &&
                detail::swap_adl_tests::is_std_swap_noexcept<T>::value) ||
               (!decltype(detail::swap_adl_tests::uses_std<T, U>(0))::value &&
                detail::swap_adl_tests::is_adl_swap_noexcept<T, U>::value))> {};
#endif
#endif

// Trait for checking if a type is a tl::expected
template <class T>
struct is_expected_impl : std::false_type {};
template <class T, class E>
struct is_expected_impl<expected<T, E>> : std::true_type {};
template <class T>
using is_expected = is_expected_impl<decay_t<T>>;

template <class T, class E, class U>
using expected_enable_forward_value = detail::enable_if_t<
    std::is_constructible<T, U&&>::value &&
    !std::is_same<detail::decay_t<U>, in_place_t>::value &&
    !std::is_same<expected<T, E>, detail::decay_t<U>>::value &&
    !std::is_same<unexpected<E>, detail::decay_t<U>>::value>;

template <class T, class E, class U, class G, class UR, class GR>
using expected_enable_from_other = detail::enable_if_t<
    std::is_constructible<T, UR>::value &&
    std::is_constructible<E, GR>::value &&
    !std::is_constructible<T, expected<U, G>&>::value &&
    !std::is_constructible<T, expected<U, G>&&>::value &&
    !std::is_constructible<T, const expected<U, G>&>::value &&
    !std::is_constructible<T, const expected<U, G>&&>::value &&
    !std::is_convertible<expected<U, G>&, T>::value &&
    !std::is_convertible<expected<U, G>&&, T>::value &&
    !std::is_convertible<const expected<U, G>&, T>::value &&
    !std::is_convertible<const expected<U, G>&&, T>::value>;

template <class T, class U>
using is_void_or = conditional_t<std::is_void<T>::value, std::true_type, U>;

template <class T>
using is_copy_constructible_or_void =
    is_void_or<T, std::is_copy_constructible<T>>;

template <class T>
using is_move_constructible_or_void =
    is_void_or<T, std::is_move_constructible<T>>;

template <class T>
using is_copy_assignable_or_void = is_void_or<T, std::is_copy_assignable<T>>;

template <class T>
using is_move_assignable_or_void = is_void_or<T, std::is_move_assignable<T>>;

}  // namespace detail

namespace detail {
struct no_init_t {};
static constexpr no_init_t no_init{};

// Implements the storage of the values, and ensures that the destructor is
// trivial if it can be.
//
// This specialization is for where neither `T` or `E` is trivially
// destructible, so the destructors must be called on destruction of the
// `expected`
template <class T, class E, bool = std::is_trivially_destructible<T>::value,
          bool = std::is_trivially_destructible<E>::value>
struct expected_storage_base {
  constexpr expected_storage_base() : m_val(T{}), m_has_val(true) {}
  constexpr expected_storage_base(no_init_t) : m_no_init(), m_has_val(false) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<T, Args&&...>::value>* =
                nullptr>
  constexpr expected_storage_base(in_place_t, Args&&... args)
      : m_val(std::forward<Args>(args)...), m_has_val(true) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr expected_storage_base(in_place_t, std::initializer_list<U> il,
                                  Args&&... args)
      : m_val(il, std::forward<Args>(args)...), m_has_val(true) {}
  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() {
    if (m_has_val) {
      m_val.~T();
    } else {
      m_unexpect.~unexpected<E>();
    }
  }
  union {
    T m_val;
    unexpected<E> m_unexpect;
    char m_no_init;
  };
  bool m_has_val;
};

// This specialization is for when both `T` and `E` are trivially-destructible,
// so the destructor of the `expected` can be trivial.
template <class T, class E>
struct expected_storage_base<T, E, true, true> {
  constexpr expected_storage_base() : m_val(T{}), m_has_val(true) {}
  constexpr expected_storage_base(no_init_t) : m_no_init(), m_has_val(false) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<T, Args&&...>::value>* =
                nullptr>
  constexpr expected_storage_base(in_place_t, Args&&... args)
      : m_val(std::forward<Args>(args)...), m_has_val(true) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr expected_storage_base(in_place_t, std::initializer_list<U> il,
                                  Args&&... args)
      : m_val(il, std::forward<Args>(args)...), m_has_val(true) {}
  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() = default;
  union {
    T m_val;
    unexpected<E> m_unexpect;
    char m_no_init;
  };
  bool m_has_val;
};

// T is trivial, E is not.
template <class T, class E>
struct expected_storage_base<T, E, true, false> {
  constexpr expected_storage_base() : m_val(T{}), m_has_val(true) {}
  TL_EXPECTED_MSVC2015_CONSTEXPR expected_storage_base(no_init_t)
      : m_no_init(), m_has_val(false) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<T, Args&&...>::value>* =
                nullptr>
  constexpr expected_storage_base(in_place_t, Args&&... args)
      : m_val(std::forward<Args>(args)...), m_has_val(true) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr expected_storage_base(in_place_t, std::initializer_list<U> il,
                                  Args&&... args)
      : m_val(il, std::forward<Args>(args)...), m_has_val(true) {}
  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() {
    if (!m_has_val) {
      m_unexpect.~unexpected<E>();
    }
  }

  union {
    T m_val;
    unexpected<E> m_unexpect;
    char m_no_init;
  };
  bool m_has_val;
};

// E is trivial, T is not.
template <class T, class E>
struct expected_storage_base<T, E, false, true> {
  constexpr expected_storage_base() : m_val(T{}), m_has_val(true) {}
  constexpr expected_storage_base(no_init_t) : m_no_init(), m_has_val(false) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<T, Args&&...>::value>* =
                nullptr>
  constexpr expected_storage_base(in_place_t, Args&&... args)
      : m_val(std::forward<Args>(args)...), m_has_val(true) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr expected_storage_base(in_place_t, std::initializer_list<U> il,
                                  Args&&... args)
      : m_val(il, std::forward<Args>(args)...), m_has_val(true) {}
  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() {
    if (m_has_val) {
      m_val.~T();
    }
  }
  union {
    T m_val;
    unexpected<E> m_unexpect;
    char m_no_init;
  };
  bool m_has_val;
};

// `T` is `void`, `E` is trivially-destructible
template <class E>
struct expected_storage_base<void, E, false, true> {
#if __GNUC__ <= 5
// no constexpr for GCC 4/5 bug
#else
  TL_EXPECTED_MSVC2015_CONSTEXPR
#endif
  expected_storage_base() : m_has_val(true) {}

  constexpr expected_storage_base(no_init_t) : m_val(), m_has_val(false) {}

  constexpr expected_storage_base(in_place_t) : m_has_val(true) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() = default;
  struct dummy {};
  union {
    unexpected<E> m_unexpect;
    dummy m_val;
  };
  bool m_has_val;
};

// `T` is `void`, `E` is not trivially-destructible
template <class E>
struct expected_storage_base<void, E, false, false> {
  constexpr expected_storage_base() : m_dummy(), m_has_val(true) {}
  constexpr expected_storage_base(no_init_t) : m_dummy(), m_has_val(false) {}

  constexpr expected_storage_base(in_place_t) : m_dummy(), m_has_val(true) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected_storage_base(unexpect_t, Args&&... args)
      : m_unexpect(std::forward<Args>(args)...), m_has_val(false) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected_storage_base(unexpect_t,
                                           std::initializer_list<U> il,
                                           Args&&... args)
      : m_unexpect(il, std::forward<Args>(args)...), m_has_val(false) {}

  ~expected_storage_base() {
    if (!m_has_val) {
      m_unexpect.~unexpected<E>();
    }
  }

  union {
    unexpected<E> m_unexpect;
    char m_dummy;
  };
  bool m_has_val;
};

// This base class provides some handy member functions which can be used in
// further derived classes
template <class T, class E>
struct expected_operations_base : expected_storage_base<T, E> {
  using expected_storage_base<T, E>::expected_storage_base;

  template <class... Args>
  void construct(Args&&... args) noexcept {
    new (std::addressof(this->m_val)) T(std::forward<Args>(args)...);
    this->m_has_val = true;
  }

  template <class Rhs>
  // NOLINTNEXTLINE(bugprone-exception-escape)
  void construct_with(Rhs&& rhs) noexcept {
    new (std::addressof(this->m_val)) T(std::forward<Rhs>(rhs).get());
    this->m_has_val = true;
  }

  template <class... Args>
  void construct_error(Args&&... args) noexcept {
    new (std::addressof(this->m_unexpect))
        unexpected<E>(std::forward<Args>(args)...);
    this->m_has_val = false;
  }

#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED

  // These assign overloads ensure that the most efficient assignment
  // implementation is used while maintaining the strong exception guarantee.
  // The problematic case is where rhs has a value, but *this does not.
  //
  // This overload handles the case where we can just copy-construct `T`
  // directly into place without throwing.
  template <class U = T,
            detail::enable_if_t<std::is_nothrow_copy_constructible<U>::value>* =
                nullptr>
  void assign(const expected_operations_base& rhs) noexcept {
    if (!this->m_has_val && rhs.m_has_val) {
      geterr().~unexpected<E>();
      construct(rhs.get());
    } else {
      assign_common(rhs);
    }
  }

  // This overload handles the case where we can attempt to create a copy of
  // `T`, then no-throw move it into place if the copy was successful.
  template <class U = T,
            detail::enable_if_t<!std::is_nothrow_copy_constructible<U>::value &&
                                std::is_nothrow_move_constructible<U>::value>* =
                nullptr>
  void assign(const expected_operations_base& rhs) noexcept {
    if (!this->m_has_val && rhs.m_has_val) {
      T tmp = rhs.get();
      geterr().~unexpected<E>();
      construct(std::move(tmp));
    } else {
      assign_common(rhs);
    }
  }

  // This overload is the worst-case, where we have to move-construct the
  // unexpected value into temporary storage, then try to copy the T into place.
  // If the construction succeeds, then everything is fine, but if it throws,
  // then we move the old unexpected value back into place before rethrowing the
  // exception.
  template <class U = T,
            detail::enable_if_t<
                !std::is_nothrow_copy_constructible<U>::value &&
                !std::is_nothrow_move_constructible<U>::value>* = nullptr>
  void assign(const expected_operations_base& rhs) {
    if (!this->m_has_val && rhs.m_has_val) {
      auto tmp = std::move(geterr());
      geterr().~unexpected<E>();

#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
      try {
        construct(rhs.get());
      } catch (...) {
        geterr() = std::move(tmp);
        throw;
      }
#else
      construct(rhs.get());
#endif
    } else {
      assign_common(rhs);
    }
  }

  // These overloads do the same as above, but for rvalues
  template <class U = T,
            detail::enable_if_t<std::is_nothrow_move_constructible<U>::value>* =
                nullptr>
  void assign(expected_operations_base&& rhs) noexcept {
    if (!this->m_has_val && rhs.m_has_val) {
      geterr().~unexpected<E>();
      construct(std::move(rhs).get());
    } else {
      assign_common(std::move(rhs));
    }
  }

  template <class U = T,
            detail::enable_if_t<
                !std::is_nothrow_move_constructible<U>::value>* = nullptr>
  void assign(expected_operations_base&& rhs) {
    if (!this->m_has_val && rhs.m_has_val) {
      auto tmp = std::move(geterr());
      geterr().~unexpected<E>();
#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
      try {
        construct(std::move(rhs).get());
      } catch (...) {
        geterr() = std::move(tmp);
        throw;
      }
#else
      construct(std::move(rhs).get());
#endif
    } else {
      assign_common(std::move(rhs));
    }
  }

#else

  // If exceptions are disabled then we can just copy-construct
  void assign(const expected_operations_base& rhs) noexcept {
    if (!this->m_has_val && rhs.m_has_val) {
      geterr().~unexpected<E>();
      construct(rhs.get());
    } else {
      assign_common(rhs);
    }
  }

  void assign(expected_operations_base&& rhs) noexcept {
    if (!this->m_has_val && rhs.m_has_val) {
      geterr().~unexpected<E>();
      construct(std::move(rhs).get());
    } else {
      assign_common(std::move(rhs));
    }
  }

#endif

  // The common part of move/copy assigning
  template <class Rhs>
  void assign_common(Rhs&& rhs) {
    if (this->m_has_val) {
      if (rhs.m_has_val) {
        get() = std::forward<Rhs>(rhs).get();
      } else {
        destroy_val();
        construct_error(std::forward<Rhs>(rhs).geterr());
      }
    } else {
      if (!rhs.m_has_val) {
        geterr() = std::forward<Rhs>(rhs).geterr();
      }
    }
  }

  bool has_value() const { return this->m_has_val; }

  TL_EXPECTED_11_CONSTEXPR T& get() & { return this->m_val; }
  constexpr const T& get() const& { return this->m_val; }
  TL_EXPECTED_11_CONSTEXPR T&& get() && { return std::move(this->m_val); }
#ifndef TL_EXPECTED_NO_CONSTRR
  constexpr const T&& get() const&& { return std::move(this->m_val); }
#endif

  TL_EXPECTED_11_CONSTEXPR unexpected<E>& geterr() & {
    return this->m_unexpect;
  }
  constexpr const unexpected<E>& geterr() const& { return this->m_unexpect; }
  TL_EXPECTED_11_CONSTEXPR unexpected<E>&& geterr() && {
    return std::move(this->m_unexpect);
  }
#ifndef TL_EXPECTED_NO_CONSTRR
  constexpr const unexpected<E>&& geterr() const&& {
    return std::move(this->m_unexpect);
  }
#endif

  TL_EXPECTED_11_CONSTEXPR void destroy_val() { get().~T(); }
};

// This base class provides some handy member functions which can be used in
// further derived classes
template <class E>
struct expected_operations_base<void, E> : expected_storage_base<void, E> {
  using expected_storage_base<void, E>::expected_storage_base;

  template <class... Args>
  void construct() noexcept {
    this->m_has_val = true;
  }

  // This function doesn't use its argument, but needs it so that code in
  // levels above this can work independently of whether T is void
  template <class Rhs>
  void construct_with(Rhs&&) noexcept {
    this->m_has_val = true;
  }

  template <class... Args>
  void construct_error(Args&&... args) noexcept {
    new (std::addressof(this->m_unexpect))
        unexpected<E>(std::forward<Args>(args)...);
    this->m_has_val = false;
  }

  template <class Rhs>
  void assign(Rhs&& rhs) noexcept {
    if (!this->m_has_val) {
      if (rhs.m_has_val) {
        geterr().~unexpected<E>();
        construct();
      } else {
        geterr() = std::forward<Rhs>(rhs).geterr();
      }
    } else {
      if (!rhs.m_has_val) {
        construct_error(std::forward<Rhs>(rhs).geterr());
      }
    }
  }

  bool has_value() const { return this->m_has_val; }

  TL_EXPECTED_11_CONSTEXPR unexpected<E>& geterr() & {
    return this->m_unexpect;
  }
  constexpr const unexpected<E>& geterr() const& { return this->m_unexpect; }
  TL_EXPECTED_11_CONSTEXPR unexpected<E>&& geterr() && {
    return std::move(this->m_unexpect);
  }
#ifndef TL_EXPECTED_NO_CONSTRR
  constexpr const unexpected<E>&& geterr() const&& {
    return std::move(this->m_unexpect);
  }
#endif

  TL_EXPECTED_11_CONSTEXPR void destroy_val() {
    // no-op
  }
};

// This class manages conditionally having a trivial copy constructor
// This specialization is for when T and E are trivially copy constructible
template <class T, class E,
          bool = is_void_or<T, TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(
                                   T)>::value &&
                 TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(E)::value>
struct expected_copy_base : expected_operations_base<T, E> {
  using expected_operations_base<T, E>::expected_operations_base;
};

// This specialization is for when T or E are not trivially copy constructible
template <class T, class E>
struct expected_copy_base<T, E, false> : expected_operations_base<T, E> {
  using expected_operations_base<T, E>::expected_operations_base;

  expected_copy_base() = default;
  expected_copy_base(const expected_copy_base& rhs)
      : expected_operations_base<T, E>(no_init) {
    if (rhs.has_value()) {
      this->construct_with(rhs);
    } else {
      this->construct_error(rhs.geterr());
    }
  }

  expected_copy_base(expected_copy_base&& rhs) = default;
  expected_copy_base& operator=(const expected_copy_base& rhs) = default;
  expected_copy_base& operator=(expected_copy_base&& rhs) = default;
};

// This class manages conditionally having a trivial move constructor
// Unfortunately there's no way to achieve this in GCC < 5 AFAIK, since it
// doesn't implement an analogue to std::is_trivially_move_constructible. We
// have to make do with a non-trivial move constructor even if T is trivially
// move constructible
#ifndef TL_EXPECTED_GCC49
template <class T, class E,
          bool =
              is_void_or<T, std::is_trivially_move_constructible<T>>::value &&
              std::is_trivially_move_constructible<E>::value>
struct expected_move_base : expected_copy_base<T, E> {
  using expected_copy_base<T, E>::expected_copy_base;
};
#else
template <class T, class E, bool = false>
struct expected_move_base;
#endif
template <class T, class E>
struct expected_move_base<T, E, false> : expected_copy_base<T, E> {
  using expected_copy_base<T, E>::expected_copy_base;

  expected_move_base() = default;
  expected_move_base(const expected_move_base& rhs) = default;

  expected_move_base(expected_move_base&& rhs) noexcept(
      std::is_nothrow_move_constructible<T>::value)
      : expected_copy_base<T, E>(no_init) {
    if (rhs.has_value()) {
      this->construct_with(std::move(rhs));
    } else {
      this->construct_error(std::move(rhs.geterr()));
    }
  }
  expected_move_base& operator=(const expected_move_base& rhs) = default;
  expected_move_base& operator=(expected_move_base&& rhs) = default;
};

// This class manages conditionally having a trivial copy assignment operator
template <
    class T, class E,
    bool =
        is_void_or<
            T, conjunction<TL_EXPECTED_IS_TRIVIALLY_COPY_ASSIGNABLE(T),
                           TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(T),
                           TL_EXPECTED_IS_TRIVIALLY_DESTRUCTIBLE(T)>>::value &&
        TL_EXPECTED_IS_TRIVIALLY_COPY_ASSIGNABLE(E)::value &&
        TL_EXPECTED_IS_TRIVIALLY_COPY_CONSTRUCTIBLE(E)::value &&
        TL_EXPECTED_IS_TRIVIALLY_DESTRUCTIBLE(E)::value>
struct expected_copy_assign_base : expected_move_base<T, E> {
  using expected_move_base<T, E>::expected_move_base;
};

template <class T, class E>
struct expected_copy_assign_base<T, E, false> : expected_move_base<T, E> {
  using expected_move_base<T, E>::expected_move_base;

  expected_copy_assign_base() = default;
  expected_copy_assign_base(const expected_copy_assign_base& rhs) = default;

  expected_copy_assign_base(expected_copy_assign_base&& rhs) = default;
  expected_copy_assign_base& operator=(const expected_copy_assign_base& rhs) {
    this->assign(rhs);
    return *this;
  }
  expected_copy_assign_base& operator=(expected_copy_assign_base&& rhs) =
      default;
};

// This class manages conditionally having a trivial move assignment operator
// Unfortunately there's no way to achieve this in GCC < 5 AFAIK, since it
// doesn't implement an analogue to std::is_trivially_move_assignable. We have
// to make do with a non-trivial move assignment operator even if T is trivially
// move assignable
#ifndef TL_EXPECTED_GCC49
template <
    class T, class E,
    bool = is_void_or<
               T, conjunction<std::is_trivially_destructible<T>,
                              std::is_trivially_move_constructible<T>,
                              std::is_trivially_move_assignable<T>>>::value &&
           std::is_trivially_destructible<E>::value &&
           std::is_trivially_move_constructible<E>::value &&
           std::is_trivially_move_assignable<E>::value>
struct expected_move_assign_base : expected_copy_assign_base<T, E> {
  using expected_copy_assign_base<T, E>::expected_copy_assign_base;
};
#else
template <class T, class E, bool = false>
struct expected_move_assign_base;
#endif

template <class T, class E>
struct expected_move_assign_base<T, E, false>
    : expected_copy_assign_base<T, E> {
  using expected_copy_assign_base<T, E>::expected_copy_assign_base;

  expected_move_assign_base() = default;
  expected_move_assign_base(const expected_move_assign_base& rhs) = default;

  expected_move_assign_base(expected_move_assign_base&& rhs) = default;

  expected_move_assign_base& operator=(const expected_move_assign_base& rhs) =
      default;

  expected_move_assign_base&
  operator=(expected_move_assign_base&& rhs) noexcept(
      std::is_nothrow_move_constructible<T>::value &&
      std::is_nothrow_move_assignable<T>::value) {
    this->assign(std::move(rhs));
    return *this;
  }
};

// expected_delete_ctor_base will conditionally delete copy and move
// constructors depending on whether T is copy/move constructible
template <class T, class E,
          bool EnableCopy = (is_copy_constructible_or_void<T>::value &&
                             std::is_copy_constructible<E>::value),
          bool EnableMove = (is_move_constructible_or_void<T>::value &&
                             std::is_move_constructible<E>::value)>
struct expected_delete_ctor_base {
  expected_delete_ctor_base() = default;
  expected_delete_ctor_base(const expected_delete_ctor_base&) = default;
  expected_delete_ctor_base(expected_delete_ctor_base&&) noexcept = default;
  expected_delete_ctor_base& operator=(const expected_delete_ctor_base&) =
      default;
  expected_delete_ctor_base& operator=(expected_delete_ctor_base&&) noexcept =
      default;
};

template <class T, class E>
struct expected_delete_ctor_base<T, E, true, false> {
  expected_delete_ctor_base() = default;
  expected_delete_ctor_base(const expected_delete_ctor_base&) = default;
  expected_delete_ctor_base(expected_delete_ctor_base&&) noexcept = delete;
  expected_delete_ctor_base& operator=(const expected_delete_ctor_base&) =
      default;
  expected_delete_ctor_base& operator=(expected_delete_ctor_base&&) noexcept =
      default;
};

template <class T, class E>
struct expected_delete_ctor_base<T, E, false, true> {
  expected_delete_ctor_base() = default;
  expected_delete_ctor_base(const expected_delete_ctor_base&) = delete;
  expected_delete_ctor_base(expected_delete_ctor_base&&) noexcept = default;
  expected_delete_ctor_base& operator=(const expected_delete_ctor_base&) =
      default;
  expected_delete_ctor_base& operator=(expected_delete_ctor_base&&) noexcept =
      default;
};

template <class T, class E>
struct expected_delete_ctor_base<T, E, false, false> {
  expected_delete_ctor_base() = default;
  expected_delete_ctor_base(const expected_delete_ctor_base&) = delete;
  expected_delete_ctor_base(expected_delete_ctor_base&&) noexcept = delete;
  expected_delete_ctor_base& operator=(const expected_delete_ctor_base&) =
      default;
  expected_delete_ctor_base& operator=(expected_delete_ctor_base&&) noexcept =
      default;
};

// expected_delete_assign_base will conditionally delete copy and move
// constructors depending on whether T and E are copy/move constructible +
// assignable
template <class T, class E,
          bool EnableCopy = (is_copy_constructible_or_void<T>::value &&
                             std::is_copy_constructible<E>::value &&
                             is_copy_assignable_or_void<T>::value &&
                             std::is_copy_assignable<E>::value),
          bool EnableMove = (is_move_constructible_or_void<T>::value &&
                             std::is_move_constructible<E>::value &&
                             is_move_assignable_or_void<T>::value &&
                             std::is_move_assignable<E>::value)>
struct expected_delete_assign_base {
  expected_delete_assign_base() = default;
  expected_delete_assign_base(const expected_delete_assign_base&) = default;
  expected_delete_assign_base(expected_delete_assign_base&&) noexcept = default;
  expected_delete_assign_base& operator=(const expected_delete_assign_base&) =
      default;
  expected_delete_assign_base& operator=(
      expected_delete_assign_base&&) noexcept = default;
};

template <class T, class E>
struct expected_delete_assign_base<T, E, true, false> {
  expected_delete_assign_base() = default;
  expected_delete_assign_base(const expected_delete_assign_base&) = default;
  expected_delete_assign_base(expected_delete_assign_base&&) noexcept = default;
  expected_delete_assign_base& operator=(const expected_delete_assign_base&) =
      default;
  expected_delete_assign_base& operator=(
      expected_delete_assign_base&&) noexcept = delete;
};

template <class T, class E>
struct expected_delete_assign_base<T, E, false, true> {
  expected_delete_assign_base() = default;
  expected_delete_assign_base(const expected_delete_assign_base&) = default;
  expected_delete_assign_base(expected_delete_assign_base&&) noexcept = default;
  expected_delete_assign_base& operator=(const expected_delete_assign_base&) =
      delete;
  expected_delete_assign_base& operator=(
      expected_delete_assign_base&&) noexcept = default;
};

template <class T, class E>
struct expected_delete_assign_base<T, E, false, false> {
  expected_delete_assign_base() = default;
  expected_delete_assign_base(const expected_delete_assign_base&) = default;
  expected_delete_assign_base(expected_delete_assign_base&&) noexcept = default;
  expected_delete_assign_base& operator=(const expected_delete_assign_base&) =
      delete;
  expected_delete_assign_base& operator=(
      expected_delete_assign_base&&) noexcept = delete;
};

// This is needed to be able to construct the expected_default_ctor_base which
// follows, while still conditionally deleting the default constructor.
struct default_constructor_tag {
  explicit constexpr default_constructor_tag() = default;
};

// expected_default_ctor_base will ensure that expected has a deleted default
// consturctor if T is not default constructible.
// This specialization is for when T is default constructible
template <class T, class E,
          bool Enable =
              std::is_default_constructible<T>::value || std::is_void<T>::value>
struct expected_default_ctor_base {
  constexpr expected_default_ctor_base() noexcept = default;
  constexpr expected_default_ctor_base(
      expected_default_ctor_base const&) noexcept = default;
  constexpr expected_default_ctor_base(expected_default_ctor_base&&) noexcept =
      default;
  expected_default_ctor_base& operator=(
      expected_default_ctor_base const&) noexcept = default;
  expected_default_ctor_base& operator=(expected_default_ctor_base&&) noexcept =
      default;

  constexpr explicit expected_default_ctor_base(default_constructor_tag) {}
};

// This specialization is for when T is not default constructible
template <class T, class E>
struct expected_default_ctor_base<T, E, false> {
  constexpr expected_default_ctor_base() noexcept = delete;
  constexpr expected_default_ctor_base(
      expected_default_ctor_base const&) noexcept = default;
  constexpr expected_default_ctor_base(expected_default_ctor_base&&) noexcept =
      default;
  expected_default_ctor_base& operator=(
      expected_default_ctor_base const&) noexcept = default;
  expected_default_ctor_base& operator=(expected_default_ctor_base&&) noexcept =
      default;

  constexpr explicit expected_default_ctor_base(default_constructor_tag) {}
};
}  // namespace detail

template <class E>
class bad_expected_access : public std::exception {
 public:
  explicit bad_expected_access(E e) : m_val(std::move(e)) {}

  virtual const char* what() const noexcept override {
    return "Bad expected access";
  }

  const E& error() const& { return m_val; }
  E& error() & { return m_val; }
  const E&& error() const&& { return std::move(m_val); }
  E&& error() && { return std::move(m_val); }

 private:
  E m_val;
};

/// An `expected<T, E>` object is an object that contains the storage for
/// another object and manages the lifetime of this contained object `T`.
/// Alternatively it could contain the storage for another unexpected object
/// `E`. The contained object may not be initialized after the expected object
/// has been initialized, and may not be destroyed before the expected object
/// has been destroyed. The initialization state of the contained object is
/// tracked by the expected object.
template <class T, class E>
class expected : private detail::expected_move_assign_base<T, E>,
                 private detail::expected_delete_ctor_base<T, E>,
                 private detail::expected_delete_assign_base<T, E>,
                 private detail::expected_default_ctor_base<T, E> {
  static_assert(!std::is_reference<T>::value, "T must not be a reference");
  static_assert(!std::is_same<T, std::remove_cv<in_place_t>::type>::value,
                "T must not be in_place_t");
  static_assert(!std::is_same<T, std::remove_cv<unexpect_t>::type>::value,
                "T must not be unexpect_t");
  static_assert(
      !std::is_same<T, typename std::remove_cv<unexpected<E>>::type>::value,
      "T must not be unexpected<E>");
  static_assert(!std::is_reference<E>::value, "E must not be a reference");

  T* valptr() { return std::addressof(this->m_val); }
  const T* valptr() const { return std::addressof(this->m_val); }
  unexpected<E>* errptr() { return std::addressof(this->m_unexpect); }
  const unexpected<E>* errptr() const {
    return std::addressof(this->m_unexpect);
  }

  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR U& val() {
    return this->m_val;
  }
  TL_EXPECTED_11_CONSTEXPR unexpected<E>& err() { return this->m_unexpect; }

  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  constexpr const U& val() const {
    return this->m_val;
  }
  constexpr const unexpected<E>& err() const { return this->m_unexpect; }

  using impl_base = detail::expected_move_assign_base<T, E>;
  using ctor_base = detail::expected_default_ctor_base<T, E>;

 public:
  typedef T value_type;
  typedef E error_type;
  typedef unexpected<E> unexpected_type;

#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto and_then(F&& f) & {
    return and_then_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto and_then(F&& f) && {
    return and_then_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto and_then(F&& f) const& {
    return and_then_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr auto and_then(F&& f) const&& {
    return and_then_impl(std::move(*this), std::forward<F>(f));
  }
#endif

#else
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto and_then(F&& f) & -> decltype(and_then_impl(
      std::declval<expected&>(), std::forward<F>(f))) {
    return and_then_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto and_then(F&& f) && -> decltype(and_then_impl(
      std::declval<expected&&>(), std::forward<F>(f))) {
    return and_then_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto and_then(F&& f) const& -> decltype(and_then_impl(
      std::declval<expected const&>(), std::forward<F>(f))) {
    return and_then_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr auto and_then(F&& f) const&& -> decltype(and_then_impl(
      std::declval<expected const&&>(), std::forward<F>(f))) {
    return and_then_impl(std::move(*this), std::forward<F>(f));
  }
#endif
#endif

#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto map(F&& f) & {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto map(F&& f) && {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto map(F&& f) const& {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  constexpr auto map(F&& f) const&& {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
#else
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(expected_map_impl(
      std::declval<expected&>(), std::declval<F&&>())) map(F&& f) & {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(expected_map_impl(std::declval<expected>(),
                                                      std::declval<F&&>()))
  map(F&& f) && {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr decltype(expected_map_impl(std::declval<const expected&>(),
                                       std::declval<F&&>()))
  map(F&& f) const& {
    return expected_map_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr decltype(expected_map_impl(std::declval<const expected&&>(),
                                       std::declval<F&&>())) map(F&& f)
      const&& {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
#endif
#endif

#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto transform(F&& f) & {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto transform(F&& f) && {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto transform(F&& f) const& {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  constexpr auto transform(F&& f) const&& {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
#else
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(expected_map_impl(
      std::declval<expected&>(), std::declval<F&&>())) transform(F&& f) & {
    return expected_map_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(expected_map_impl(std::declval<expected>(),
                                                      std::declval<F&&>()))
  transform(F&& f) && {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr decltype(expected_map_impl(std::declval<const expected&>(),
                                       std::declval<F&&>()))
  transform(F&& f) const& {
    return expected_map_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr decltype(expected_map_impl(std::declval<const expected&&>(),
                                       std::declval<F&&>())) transform(F&& f)
      const&& {
    return expected_map_impl(std::move(*this), std::forward<F>(f));
  }
#endif
#endif

#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto map_error(F&& f) & {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto map_error(F&& f) && {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto map_error(F&& f) const& {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  constexpr auto map_error(F&& f) const&& {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
#else
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(map_error_impl(
      std::declval<expected&>(), std::declval<F&&>())) map_error(F&& f) & {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(map_error_impl(std::declval<expected&&>(),
                                                   std::declval<F&&>()))
  map_error(F&& f) && {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr decltype(map_error_impl(std::declval<const expected&>(),
                                    std::declval<F&&>()))
  map_error(F&& f) const& {
    return map_error_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr decltype(map_error_impl(std::declval<const expected&&>(),
                                    std::declval<F&&>())) map_error(F&& f)
      const&& {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
#endif
#endif
#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto transform_error(F&& f) & {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR auto transform_error(F&& f) && {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr auto transform_error(F&& f) const& {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  constexpr auto transform_error(F&& f) const&& {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
#else
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(map_error_impl(
      std::declval<expected&>(),
      std::declval<F&&>())) transform_error(F&& f) & {
    return map_error_impl(*this, std::forward<F>(f));
  }
  template <class F>
  TL_EXPECTED_11_CONSTEXPR decltype(map_error_impl(std::declval<expected&&>(),
                                                   std::declval<F&&>()))
  transform_error(F&& f) && {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
  template <class F>
  constexpr decltype(map_error_impl(std::declval<const expected&>(),
                                    std::declval<F&&>()))
  transform_error(F&& f) const& {
    return map_error_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  constexpr decltype(map_error_impl(std::declval<const expected&&>(),
                                    std::declval<F&&>())) transform_error(F&& f)
      const&& {
    return map_error_impl(std::move(*this), std::forward<F>(f));
  }
#endif
#endif
  template <class F>
  expected TL_EXPECTED_11_CONSTEXPR or_else(F&& f) & {
    return or_else_impl(*this, std::forward<F>(f));
  }

  template <class F>
  expected TL_EXPECTED_11_CONSTEXPR or_else(F&& f) && {
    return or_else_impl(std::move(*this), std::forward<F>(f));
  }

  template <class F>
  expected constexpr or_else(F&& f) const& {
    return or_else_impl(*this, std::forward<F>(f));
  }

#ifndef TL_EXPECTED_NO_CONSTRR
  template <class F>
  expected constexpr or_else(F&& f) const&& {
    return or_else_impl(std::move(*this), std::forward<F>(f));
  }
#endif
  constexpr expected() = default;
  constexpr expected(const expected& rhs) = default;
  constexpr expected(expected&& rhs) = default;
  expected& operator=(const expected& rhs) = default;
  expected& operator=(expected&& rhs) = default;

  template <class... Args,
            detail::enable_if_t<std::is_constructible<T, Args&&...>::value>* =
                nullptr>
  constexpr expected(in_place_t, Args&&... args)
      : impl_base(in_place, std::forward<Args>(args)...),
        ctor_base(detail::default_constructor_tag{}) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr expected(in_place_t, std::initializer_list<U> il, Args&&... args)
      : impl_base(in_place, il, std::forward<Args>(args)...),
        ctor_base(detail::default_constructor_tag{}) {}

  template <
      class G = E,
      detail::enable_if_t<std::is_constructible<E, const G&>::value>* = nullptr,
      detail::enable_if_t<!std::is_convertible<const G&, E>::value>* = nullptr>
  explicit constexpr expected(const unexpected<G>& e)
      : impl_base(unexpect, e.value()),
        ctor_base(detail::default_constructor_tag{}) {}

  template <
      class G = E,
      detail::enable_if_t<std::is_constructible<E, const G&>::value>* = nullptr,
      detail::enable_if_t<std::is_convertible<const G&, E>::value>* = nullptr>
  constexpr expected(unexpected<G> const& e)
      : impl_base(unexpect, e.value()),
        ctor_base(detail::default_constructor_tag{}) {}

  template <
      class G = E,
      detail::enable_if_t<std::is_constructible<E, G&&>::value>* = nullptr,
      detail::enable_if_t<!std::is_convertible<G&&, E>::value>* = nullptr>
  explicit constexpr expected(unexpected<G>&& e) noexcept(
      std::is_nothrow_constructible<E, G&&>::value)
      : impl_base(unexpect, std::move(e.value())),
        ctor_base(detail::default_constructor_tag{}) {}

  template <
      class G = E,
      detail::enable_if_t<std::is_constructible<E, G&&>::value>* = nullptr,
      detail::enable_if_t<std::is_convertible<G&&, E>::value>* = nullptr>
  constexpr expected(unexpected<G>&& e) noexcept(
      std::is_nothrow_constructible<E, G&&>::value)
      : impl_base(unexpect, std::move(e.value())),
        ctor_base(detail::default_constructor_tag{}) {}

  template <class... Args,
            detail::enable_if_t<std::is_constructible<E, Args&&...>::value>* =
                nullptr>
  constexpr explicit expected(unexpect_t, Args&&... args)
      : impl_base(unexpect, std::forward<Args>(args)...),
        ctor_base(detail::default_constructor_tag{}) {}

  template <class U, class... Args,
            detail::enable_if_t<std::is_constructible<
                E, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  constexpr explicit expected(unexpect_t, std::initializer_list<U> il,
                              Args&&... args)
      : impl_base(unexpect, il, std::forward<Args>(args)...),
        ctor_base(detail::default_constructor_tag{}) {}

  template <class U, class G,
            detail::enable_if_t<!(std::is_convertible<U const&, T>::value &&
                                  std::is_convertible<G const&, E>::value)>* =
                nullptr,
            detail::expected_enable_from_other<T, E, U, G, const U&,
                                               const G&>* = nullptr>
  explicit TL_EXPECTED_11_CONSTEXPR expected(const expected<U, G>& rhs)
      : ctor_base(detail::default_constructor_tag{}) {
    if (rhs.has_value()) {
      this->construct(*rhs);
    } else {
      this->construct_error(rhs.error());
    }
  }

  template <
      class U, class G,
      detail::enable_if_t<(std::is_convertible<U const&, T>::value &&
                           std::is_convertible<G const&, E>::value)>* = nullptr,
      detail::expected_enable_from_other<T, E, U, G, const U&, const G&>* =
          nullptr>
  TL_EXPECTED_11_CONSTEXPR expected(const expected<U, G>& rhs)
      : ctor_base(detail::default_constructor_tag{}) {
    if (rhs.has_value()) {
      this->construct(*rhs);
    } else {
      this->construct_error(rhs.error());
    }
  }

  template <
      class U, class G,
      detail::enable_if_t<!(std::is_convertible<U&&, T>::value &&
                            std::is_convertible<G&&, E>::value)>* = nullptr,
      detail::expected_enable_from_other<T, E, U, G, U&&, G&&>* = nullptr>
  explicit TL_EXPECTED_11_CONSTEXPR expected(expected<U, G>&& rhs)
      : ctor_base(detail::default_constructor_tag{}) {
    if (rhs.has_value()) {
      this->construct(std::move(*rhs));
    } else {
      this->construct_error(std::move(rhs.error()));
    }
  }

  template <
      class U, class G,
      detail::enable_if_t<(std::is_convertible<U&&, T>::value &&
                           std::is_convertible<G&&, E>::value)>* = nullptr,
      detail::expected_enable_from_other<T, E, U, G, U&&, G&&>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR expected(expected<U, G>&& rhs)
      : ctor_base(detail::default_constructor_tag{}) {
    if (rhs.has_value()) {
      this->construct(std::move(*rhs));
    } else {
      this->construct_error(std::move(rhs.error()));
    }
  }

  template <class U = T,
            detail::enable_if_t<!std::is_convertible<U&&, T>::value>* = nullptr,
            detail::expected_enable_forward_value<T, E, U>* = nullptr>
  explicit TL_EXPECTED_MSVC2015_CONSTEXPR expected(U&& v)
      : expected(in_place, std::forward<U>(v)) {}

  template <class U = T,
            detail::enable_if_t<std::is_convertible<U&&, T>::value>* = nullptr,
            detail::expected_enable_forward_value<T, E, U>* = nullptr>
  TL_EXPECTED_MSVC2015_CONSTEXPR expected(U&& v)
      : expected(in_place, std::forward<U>(v)) {}

  template <
      class U = T, class G = T,
      detail::enable_if_t<std::is_nothrow_constructible<T, U&&>::value>* =
          nullptr,
      detail::enable_if_t<!std::is_void<G>::value>* = nullptr,
      detail::enable_if_t<
          (!std::is_same<expected<T, E>, detail::decay_t<U>>::value &&
           !detail::conjunction<std::is_scalar<T>,
                                std::is_same<T, detail::decay_t<U>>>::value &&
           std::is_constructible<T, U>::value &&
           std::is_assignable<G&, U>::value &&
           std::is_nothrow_move_constructible<E>::value)>* = nullptr>
  expected& operator=(U&& v) {
    if (has_value()) {
      val() = std::forward<U>(v);
    } else {
      err().~unexpected<E>();
      ::new (valptr()) T(std::forward<U>(v));
      this->m_has_val = true;
    }

    return *this;
  }

  template <
      class U = T, class G = T,
      detail::enable_if_t<!std::is_nothrow_constructible<T, U&&>::value>* =
          nullptr,
      detail::enable_if_t<!std::is_void<U>::value>* = nullptr,
      detail::enable_if_t<
          (!std::is_same<expected<T, E>, detail::decay_t<U>>::value &&
           !detail::conjunction<std::is_scalar<T>,
                                std::is_same<T, detail::decay_t<U>>>::value &&
           std::is_constructible<T, U>::value &&
           std::is_assignable<G&, U>::value &&
           std::is_nothrow_move_constructible<E>::value)>* = nullptr>
  expected& operator=(U&& v) {
    if (has_value()) {
      val() = std::forward<U>(v);
    } else {
      auto tmp = std::move(err());
      err().~unexpected<E>();

#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
      try {
        ::new (valptr()) T(std::forward<U>(v));
        this->m_has_val = true;
      } catch (...) {
        err() = std::move(tmp);
        throw;
      }
#else
      ::new (valptr()) T(std::forward<U>(v));
      this->m_has_val = true;
#endif
    }

    return *this;
  }

  template <class G = E,
            detail::enable_if_t<std::is_nothrow_copy_constructible<G>::value &&
                                std::is_assignable<G&, G>::value>* = nullptr>
  expected& operator=(const unexpected<G>& rhs) {
    if (!has_value()) {
      err() = rhs;
    } else {
      this->destroy_val();
      ::new (errptr()) unexpected<E>(rhs);
      this->m_has_val = false;
    }

    return *this;
  }

  template <class G = E,
            detail::enable_if_t<std::is_nothrow_move_constructible<G>::value &&
                                std::is_move_assignable<G>::value>* = nullptr>
  expected& operator=(unexpected<G>&& rhs) noexcept {
    if (!has_value()) {
      err() = std::move(rhs);
    } else {
      this->destroy_val();
      ::new (errptr()) unexpected<E>(std::move(rhs));
      this->m_has_val = false;
    }

    return *this;
  }

  template <class... Args, detail::enable_if_t<std::is_nothrow_constructible<
                               T, Args&&...>::value>* = nullptr>
  void emplace(Args&&... args) {
    if (has_value()) {
      val().~T();
    } else {
      err().~unexpected<E>();
      this->m_has_val = true;
    }
    ::new (valptr()) T(std::forward<Args>(args)...);
  }

  template <class... Args, detail::enable_if_t<!std::is_nothrow_constructible<
                               T, Args&&...>::value>* = nullptr>
  void emplace(Args&&... args) {
    if (has_value()) {
      val().~T();
      ::new (valptr()) T(std::forward<Args>(args)...);
    } else {
      auto tmp = std::move(err());
      err().~unexpected<E>();

#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
      try {
        ::new (valptr()) T(std::forward<Args>(args)...);
        this->m_has_val = true;
      } catch (...) {
        err() = std::move(tmp);
        throw;
      }
#else
      ::new (valptr()) T(std::forward<Args>(args)...);
      this->m_has_val = true;
#endif
    }
  }

  template <class U, class... Args,
            detail::enable_if_t<std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  void emplace(std::initializer_list<U> il, Args&&... args) {
    if (has_value()) {
      T t(il, std::forward<Args>(args)...);
      val() = std::move(t);
    } else {
      err().~unexpected<E>();
      ::new (valptr()) T(il, std::forward<Args>(args)...);
      this->m_has_val = true;
    }
  }

  template <class U, class... Args,
            detail::enable_if_t<!std::is_nothrow_constructible<
                T, std::initializer_list<U>&, Args&&...>::value>* = nullptr>
  void emplace(std::initializer_list<U> il, Args&&... args) {
    if (has_value()) {
      T t(il, std::forward<Args>(args)...);
      val() = std::move(t);
    } else {
      auto tmp = std::move(err());
      err().~unexpected<E>();

#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
      try {
        ::new (valptr()) T(il, std::forward<Args>(args)...);
        this->m_has_val = true;
      } catch (...) {
        err() = std::move(tmp);
        throw;
      }
#else
      ::new (valptr()) T(il, std::forward<Args>(args)...);
      this->m_has_val = true;
#endif
    }
  }

 private:
  using t_is_void = std::true_type;
  using t_is_not_void = std::false_type;
  using t_is_nothrow_move_constructible = std::true_type;
  using move_constructing_t_can_throw = std::false_type;
  using e_is_nothrow_move_constructible = std::true_type;
  using move_constructing_e_can_throw = std::false_type;

  void swap_where_both_have_value(expected& /*rhs*/, t_is_void) noexcept {
    // swapping void is a no-op
  }

  void swap_where_both_have_value(expected& rhs, t_is_not_void) {
    using std::swap;
    swap(val(), rhs.val());
  }

  void swap_where_only_one_has_value(expected& rhs, t_is_void) noexcept(
      std::is_nothrow_move_constructible<E>::value) {
    ::new (errptr()) unexpected_type(std::move(rhs.err()));
    rhs.err().~unexpected_type();
    std::swap(this->m_has_val, rhs.m_has_val);
  }

  void swap_where_only_one_has_value(expected& rhs, t_is_not_void) {
    swap_where_only_one_has_value_and_t_is_not_void(
        rhs, typename std::is_nothrow_move_constructible<T>::type{},
        typename std::is_nothrow_move_constructible<E>::type{});
  }

  void swap_where_only_one_has_value_and_t_is_not_void(
      expected& rhs, t_is_nothrow_move_constructible,
      e_is_nothrow_move_constructible) noexcept {
    auto temp = std::move(val());
    val().~T();
    ::new (errptr()) unexpected_type(std::move(rhs.err()));
    rhs.err().~unexpected_type();
    ::new (rhs.valptr()) T(std::move(temp));
    std::swap(this->m_has_val, rhs.m_has_val);
  }

  void swap_where_only_one_has_value_and_t_is_not_void(
      expected& rhs, t_is_nothrow_move_constructible,
      move_constructing_e_can_throw) {
    auto temp = std::move(val());
    val().~T();
#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
    try {
      ::new (errptr()) unexpected_type(std::move(rhs.err()));
      rhs.err().~unexpected_type();
      ::new (rhs.valptr()) T(std::move(temp));
      std::swap(this->m_has_val, rhs.m_has_val);
    } catch (...) {
      val() = std::move(temp);
      throw;
    }
#else
    ::new (errptr()) unexpected_type(std::move(rhs.err()));
    rhs.err().~unexpected_type();
    ::new (rhs.valptr()) T(std::move(temp));
    std::swap(this->m_has_val, rhs.m_has_val);
#endif
  }

  void swap_where_only_one_has_value_and_t_is_not_void(
      expected& rhs, move_constructing_t_can_throw,
      e_is_nothrow_move_constructible) {
    auto temp = std::move(rhs.err());
    rhs.err().~unexpected_type();
#ifdef TL_EXPECTED_EXCEPTIONS_ENABLED
    try {
      ::new (rhs.valptr()) T(std::move(val()));
      val().~T();
      ::new (errptr()) unexpected_type(std::move(temp));
      std::swap(this->m_has_val, rhs.m_has_val);
    } catch (...) {
      rhs.err() = std::move(temp);
      throw;
    }
#else
    ::new (rhs.valptr()) T(std::move(val()));
    val().~T();
    ::new (errptr()) unexpected_type(std::move(temp));
    std::swap(this->m_has_val, rhs.m_has_val);
#endif
  }

 public:
  template <class OT = T, class OE = E>
  detail::enable_if_t<detail::is_swappable<OT>::value &&
                      detail::is_swappable<OE>::value &&
                      (std::is_nothrow_move_constructible<OT>::value ||
                       std::is_nothrow_move_constructible<OE>::value)>
  swap(expected& rhs) noexcept(std::is_nothrow_move_constructible<T>::value &&
                               detail::is_nothrow_swappable<T>::value &&
                               std::is_nothrow_move_constructible<E>::value &&
                               detail::is_nothrow_swappable<E>::value) {
    if (has_value() && rhs.has_value()) {
      swap_where_both_have_value(rhs, typename std::is_void<T>::type{});
    } else if (!has_value() && rhs.has_value()) {
      rhs.swap(*this);
    } else if (has_value()) {
      swap_where_only_one_has_value(rhs, typename std::is_void<T>::type{});
    } else {
      using std::swap;
      swap(err(), rhs.err());
    }
  }

  constexpr const T* operator->() const {
    TL_ASSERT(has_value());
    return valptr();
  }
  TL_EXPECTED_11_CONSTEXPR T* operator->() {
    TL_ASSERT(has_value());
    return valptr();
  }

  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  constexpr const U& operator*() const& {
    TL_ASSERT(has_value());
    return val();
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR U& operator*() & {
    TL_ASSERT(has_value());
    return val();
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  constexpr const U&& operator*() const&& {
    TL_ASSERT(has_value());
    return std::move(val());
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR U&& operator*() && {
    TL_ASSERT(has_value());
    return std::move(val());
  }

  constexpr bool has_value() const noexcept { return this->m_has_val; }
  constexpr explicit operator bool() const noexcept { return this->m_has_val; }

  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR const U& value() const& {
    if (!has_value())
      detail::throw_exception(bad_expected_access<E>(err().value()));
    return val();
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR U& value() & {
    if (!has_value())
      detail::throw_exception(bad_expected_access<E>(err().value()));
    return val();
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR const U&& value() const&& {
    if (!has_value())
      detail::throw_exception(bad_expected_access<E>(std::move(err()).value()));
    return std::move(val());
  }
  template <class U = T,
            detail::enable_if_t<!std::is_void<U>::value>* = nullptr>
  TL_EXPECTED_11_CONSTEXPR U&& value() && {
    if (!has_value())
      detail::throw_exception(bad_expected_access<E>(std::move(err()).value()));
    return std::move(val());
  }

  constexpr const E& error() const& {
    TL_ASSERT(!has_value());
    return err().value();
  }
  TL_EXPECTED_11_CONSTEXPR E& error() & {
    TL_ASSERT(!has_value());
    return err().value();
  }
  constexpr const E&& error() const&& {
    TL_ASSERT(!has_value());
    return std::move(err().value());
  }
  TL_EXPECTED_11_CONSTEXPR E&& error() && {
    TL_ASSERT(!has_value());
    return std::move(err().value());
  }

  template <class U>
  constexpr T value_or(U&& v) const& {
    static_assert(std::is_copy_constructible<T>::value &&
                      std::is_convertible<U&&, T>::value,
                  "T must be copy-constructible and convertible to from U&&");
    return bool(*this) ? **this : static_cast<T>(std::forward<U>(v));
  }
  template <class U>
  TL_EXPECTED_11_CONSTEXPR T value_or(U&& v) && {
    static_assert(std::is_move_constructible<T>::value &&
                      std::is_convertible<U&&, T>::value,
                  "T must be move-constructible and convertible to from U&&");
    return bool(*this) ? std::move(**this) : static_cast<T>(std::forward<U>(v));
  }
};

namespace detail {
template <class Exp>
using exp_t = typename detail::decay_t<Exp>::value_type;
template <class Exp>
using err_t = typename detail::decay_t<Exp>::error_type;
template <class Exp, class Ret>
using ret_t = expected<Ret, err_t<Exp>>;

#ifdef TL_EXPECTED_CXX14
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>()))>
constexpr auto and_then_impl(Exp&& exp, F&& f) {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");

  return exp.has_value()
             ? detail::invoke(std::forward<F>(f), *std::forward<Exp>(exp))
             : Ret(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>()))>
constexpr auto and_then_impl(Exp&& exp, F&& f) {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");

  return exp.has_value() ? detail::invoke(std::forward<F>(f))
                         : Ret(unexpect, std::forward<Exp>(exp).error());
}
#else
template <class>
struct TC;
template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>())),
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr>
auto and_then_impl(Exp&& exp, F&& f) -> Ret {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");

  return exp.has_value()
             ? detail::invoke(std::forward<F>(f), *std::forward<Exp>(exp))
             : Ret(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>())),
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr>
constexpr auto and_then_impl(Exp&& exp, F&& f) -> Ret {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");

  return exp.has_value() ? detail::invoke(std::forward<F>(f))
                         : Ret(unexpect, std::forward<Exp>(exp).error());
}
#endif

#ifdef TL_EXPECTED_CXX14
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto expected_map_impl(Exp&& exp, F&& f) {
  using result = ret_t<Exp, detail::decay_t<Ret>>;
  return exp.has_value() ? result(detail::invoke(std::forward<F>(f),
                                                 *std::forward<Exp>(exp)))
                         : result(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto expected_map_impl(Exp&& exp, F&& f) {
  using result = expected<void, err_t<Exp>>;
  if (exp.has_value()) {
    detail::invoke(std::forward<F>(f), *std::forward<Exp>(exp));
    return result();
  }

  return result(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto expected_map_impl(Exp&& exp, F&& f) {
  using result = ret_t<Exp, detail::decay_t<Ret>>;
  return exp.has_value() ? result(detail::invoke(std::forward<F>(f)))
                         : result(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto expected_map_impl(Exp&& exp, F&& f) {
  using result = expected<void, err_t<Exp>>;
  if (exp.has_value()) {
    detail::invoke(std::forward<F>(f));
    return result();
  }

  return result(unexpect, std::forward<Exp>(exp).error());
}
#else
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>

constexpr auto expected_map_impl(Exp&& exp, F&& f)
    -> ret_t<Exp, detail::decay_t<Ret>> {
  using result = ret_t<Exp, detail::decay_t<Ret>>;

  return exp.has_value() ? result(detail::invoke(std::forward<F>(f),
                                                 *std::forward<Exp>(exp)))
                         : result(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              *std::declval<Exp>())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>

auto expected_map_impl(Exp&& exp, F&& f) -> expected<void, err_t<Exp>> {
  if (exp.has_value()) {
    detail::invoke(std::forward<F>(f), *std::forward<Exp>(exp));
    return {};
  }

  return unexpected<err_t<Exp>>(std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>

constexpr auto expected_map_impl(Exp&& exp, F&& f)
    -> ret_t<Exp, detail::decay_t<Ret>> {
  using result = ret_t<Exp, detail::decay_t<Ret>>;

  return exp.has_value() ? result(detail::invoke(std::forward<F>(f)))
                         : result(unexpect, std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>

auto expected_map_impl(Exp&& exp, F&& f) -> expected<void, err_t<Exp>> {
  if (exp.has_value()) {
    detail::invoke(std::forward<F>(f));
    return {};
  }

  return unexpected<err_t<Exp>>(std::forward<Exp>(exp).error());
}
#endif

#if defined(TL_EXPECTED_CXX14) && !defined(TL_EXPECTED_GCC49) && \
    !defined(TL_EXPECTED_GCC54) && !defined(TL_EXPECTED_GCC55)
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto map_error_impl(Exp&& exp, F&& f) {
  using result = expected<exp_t<Exp>, detail::decay_t<Ret>>;
  return exp.has_value()
             ? result(*std::forward<Exp>(exp))
             : result(unexpect, detail::invoke(std::forward<F>(f),
                                               std::forward<Exp>(exp).error()));
}
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto map_error_impl(Exp&& exp, F&& f) {
  using result = expected<exp_t<Exp>, monostate>;
  if (exp.has_value()) {
    return result(*std::forward<Exp>(exp));
  }

  detail::invoke(std::forward<F>(f), std::forward<Exp>(exp).error());
  return result(unexpect, monostate{});
}
template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto map_error_impl(Exp&& exp, F&& f) {
  using result = expected<exp_t<Exp>, detail::decay_t<Ret>>;
  return exp.has_value()
             ? result()
             : result(unexpect, detail::invoke(std::forward<F>(f),
                                               std::forward<Exp>(exp).error()));
}
template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto map_error_impl(Exp&& exp, F&& f) {
  using result = expected<exp_t<Exp>, monostate>;
  if (exp.has_value()) {
    return result();
  }

  detail::invoke(std::forward<F>(f), std::forward<Exp>(exp).error());
  return result(unexpect, monostate{});
}
#else
template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto map_error_impl(Exp&& exp, F&& f)
    -> expected<exp_t<Exp>, detail::decay_t<Ret>> {
  using result = expected<exp_t<Exp>, detail::decay_t<Ret>>;

  return exp.has_value()
             ? result(*std::forward<Exp>(exp))
             : result(unexpect, detail::invoke(std::forward<F>(f),
                                               std::forward<Exp>(exp).error()));
}

template <class Exp, class F,
          detail::enable_if_t<!std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto map_error_impl(Exp&& exp, F&& f) -> expected<exp_t<Exp>, monostate> {
  using result = expected<exp_t<Exp>, monostate>;
  if (exp.has_value()) {
    return result(*std::forward<Exp>(exp));
  }

  detail::invoke(std::forward<F>(f), std::forward<Exp>(exp).error());
  return result(unexpect, monostate{});
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto map_error_impl(Exp&& exp, F&& f)
    -> expected<exp_t<Exp>, detail::decay_t<Ret>> {
  using result = expected<exp_t<Exp>, detail::decay_t<Ret>>;

  return exp.has_value()
             ? result()
             : result(unexpect, detail::invoke(std::forward<F>(f),
                                               std::forward<Exp>(exp).error()));
}

template <class Exp, class F,
          detail::enable_if_t<std::is_void<exp_t<Exp>>::value>* = nullptr,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
auto map_error_impl(Exp&& exp, F&& f) -> expected<exp_t<Exp>, monostate> {
  using result = expected<exp_t<Exp>, monostate>;
  if (exp.has_value()) {
    return result();
  }

  detail::invoke(std::forward<F>(f), std::forward<Exp>(exp).error());
  return result(unexpect, monostate{});
}
#endif

#ifdef TL_EXPECTED_CXX14
template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
constexpr auto or_else_impl(Exp&& exp, F&& f) {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");
  return exp.has_value() ? std::forward<Exp>(exp)
                         : detail::invoke(std::forward<F>(f),
                                          std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
detail::decay_t<Exp> or_else_impl(Exp&& exp, F&& f) {
  return exp.has_value() ? std::forward<Exp>(exp)
                         : (detail::invoke(std::forward<F>(f),
                                           std::forward<Exp>(exp).error()),
                            std::forward<Exp>(exp));
}
#else
template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<!std::is_void<Ret>::value>* = nullptr>
auto or_else_impl(Exp&& exp, F&& f) -> Ret {
  static_assert(detail::is_expected<Ret>::value, "F must return an expected");
  return exp.has_value() ? std::forward<Exp>(exp)
                         : detail::invoke(std::forward<F>(f),
                                          std::forward<Exp>(exp).error());
}

template <class Exp, class F,
          class Ret = decltype(detail::invoke(std::declval<F>(),
                                              std::declval<Exp>().error())),
          detail::enable_if_t<std::is_void<Ret>::value>* = nullptr>
detail::decay_t<Exp> or_else_impl(Exp&& exp, F&& f) {
  return exp.has_value() ? std::forward<Exp>(exp)
                         : (detail::invoke(std::forward<F>(f),
                                           std::forward<Exp>(exp).error()),
                            std::forward<Exp>(exp));
}
#endif
}  // namespace detail

template <class T, class E, class U, class F>
constexpr bool operator==(const expected<T, E>& lhs,
                          const expected<U, F>& rhs) {
  return (lhs.has_value() != rhs.has_value())
             ? false
             : (!lhs.has_value() ? lhs.error() == rhs.error() : *lhs == *rhs);
}
template <class T, class E, class U, class F>
constexpr bool operator!=(const expected<T, E>& lhs,
                          const expected<U, F>& rhs) {
  return (lhs.has_value() != rhs.has_value())
             ? true
             : (!lhs.has_value() ? lhs.error() != rhs.error() : *lhs != *rhs);
}
template <class E, class F>
constexpr bool operator==(const expected<void, E>& lhs,
                          const expected<void, F>& rhs) {
  return (lhs.has_value() != rhs.has_value())
             ? false
             : (!lhs.has_value() ? lhs.error() == rhs.error() : true);
}
template <class E, class F>
constexpr bool operator!=(const expected<void, E>& lhs,
                          const expected<void, F>& rhs) {
  return (lhs.has_value() != rhs.has_value())
             ? true
             : (!lhs.has_value() ? lhs.error() == rhs.error() : false);
}

template <class T, class E, class U>
constexpr bool operator==(const expected<T, E>& x, const U& v) {
  return x.has_value() ? *x == v : false;
}
template <class T, class E, class U>
constexpr bool operator==(const U& v, const expected<T, E>& x) {
  return x.has_value() ? *x == v : false;
}
template <class T, class E, class U>
constexpr bool operator!=(const expected<T, E>& x, const U& v) {
  return x.has_value() ? *x != v : true;
}
template <class T, class E, class U>
constexpr bool operator!=(const U& v, const expected<T, E>& x) {
  return x.has_value() ? *x != v : true;
}

template <class T, class E>
constexpr bool operator==(const expected<T, E>& x, const unexpected<E>& e) {
  return x.has_value() ? false : x.error() == e.value();
}
template <class T, class E>
constexpr bool operator==(const unexpected<E>& e, const expected<T, E>& x) {
  return x.has_value() ? false : x.error() == e.value();
}
template <class T, class E>
constexpr bool operator!=(const expected<T, E>& x, const unexpected<E>& e) {
  return x.has_value() ? true : x.error() != e.value();
}
template <class T, class E>
constexpr bool operator!=(const unexpected<E>& e, const expected<T, E>& x) {
  return x.has_value() ? true : x.error() != e.value();
}

template <class T, class E,
          detail::enable_if_t<(std::is_void<T>::value ||
                               std::is_move_constructible<T>::value) &&
                              detail::is_swappable<T>::value &&
                              std::is_move_constructible<E>::value &&
                              detail::is_swappable<E>::value>* = nullptr>
void swap(expected<T, E>& lhs,
          expected<T, E>& rhs) noexcept(noexcept(lhs.swap(rhs))) {
  lhs.swap(rhs);
}
}  // namespace tl

#endif
/* end file include/ada/expected.h */
/* begin file include/ada/url_pattern_regex.h */
/**
 * @file url_search_params.h
 * @brief Declaration for the URL Search Params
 */
#ifndef ADA_URL_PATTERN_REGEX_H
#define ADA_URL_PATTERN_REGEX_H

#include <string>
#include <string_view>

#ifdef ADA_USE_UNSAFE_STD_REGEX_PROVIDER
#include <regex>
#endif  // ADA_USE_UNSAFE_STD_REGEX_PROVIDER

#if ADA_INCLUDE_URL_PATTERN
namespace ada::url_pattern_regex {

template <typename T>
concept regex_concept = requires(T t, std::string_view pattern,
                                 bool ignore_case, std::string_view input) {
  // Ensure the class has a type alias 'regex_type'
  typename T::regex_type;

  // Function to create a regex instance
  {
    T::create_instance(pattern, ignore_case)
  } -> std::same_as<std::optional<typename T::regex_type>>;

  // Function to perform regex search
  {
    T::regex_search(input, std::declval<typename T::regex_type&>())
  } -> std::same_as<std::optional<std::vector<std::optional<std::string>>>>;

  // Function to match regex pattern
  {
    T::regex_match(input, std::declval<typename T::regex_type&>())
  } -> std::same_as<bool>;

  // Copy constructor
  { T(std::declval<const T&>()) } -> std::same_as<T>;

  // Move constructor
  { T(std::declval<T&&>()) } -> std::same_as<T>;
};

#ifdef ADA_USE_UNSAFE_STD_REGEX_PROVIDER
class std_regex_provider final {
 public:
  std_regex_provider() = default;
  using regex_type = std::regex;
  static std::optional<regex_type> create_instance(std::string_view pattern,
                                                   bool ignore_case);
  static std::optional<std::vector<std::optional<std::string>>> regex_search(
      std::string_view input, const regex_type& pattern);
  static bool regex_match(std::string_view input, const regex_type& pattern);
};
#endif  // ADA_USE_UNSAFE_STD_REGEX_PROVIDER

}  // namespace ada::url_pattern_regex
#endif  // ADA_INCLUDE_URL_PATTERN
#endif  // ADA_URL_PATTERN_REGEX_H
/* end file include/ada/url_pattern_regex.h */
/* begin file include/ada/url_pattern_init.h */
/**
 * @file url_pattern_init.h
 * @brief Declaration for the url_pattern_init implementation.
 */
#ifndef ADA_URL_PATTERN_INIT_H
#define ADA_URL_PATTERN_INIT_H


#include <string_view>
#include <string>
#include <optional>
#include <iostream>

#if ADA_TESTING
#include <iostream>
#endif  // ADA_TESTING

#if ADA_INCLUDE_URL_PATTERN
namespace ada {

// Important: C++20 allows us to use concept rather than `using` or `typedef
// and allows functions with second argument, which is optional (using either
// std::nullopt or a parameter with default value)
template <typename F>
concept url_pattern_encoding_callback = requires(F f, std::string_view sv) {
  { f(sv) } -> std::same_as<tl::expected<std::string, errors>>;
};

// A structure providing matching patterns for individual components
// of a URL. When a URLPattern is created, or when a URLPattern is
// used to match or test against a URL, the input can be given as
// either a string or a URLPatternInit struct. If a string is given,
// it will be parsed to create a URLPatternInit. The URLPatternInit
// API is defined as part of the URLPattern specification.
// All provided strings must be valid UTF-8.
struct url_pattern_init {
  enum class process_type : uint8_t {
    url,
    pattern,
  };

  friend std::ostream& operator<<(std::ostream& os, process_type type) {
    switch (type) {
      case process_type::url:
        return os << "url";
      case process_type::pattern:
        return os << "pattern";
      default:
        return os << "unknown";
    }
  }

  // All strings must be valid UTF-8.
  // @see https://urlpattern.spec.whatwg.org/#process-a-urlpatterninit
  static tl::expected<url_pattern_init, errors> process(
      const url_pattern_init& init, process_type type,
      std::optional<std::string_view> protocol = std::nullopt,
      std::optional<std::string_view> username = std::nullopt,
      std::optional<std::string_view> password = std::nullopt,
      std::optional<std::string_view> hostname = std::nullopt,
      std::optional<std::string_view> port = std::nullopt,
      std::optional<std::string_view> pathname = std::nullopt,
      std::optional<std::string_view> search = std::nullopt,
      std::optional<std::string_view> hash = std::nullopt);

  // @see https://urlpattern.spec.whatwg.org/#process-protocol-for-init
  static tl::expected<std::string, errors> process_protocol(
      std::string_view value, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-username-for-init
  static tl::expected<std::string, errors> process_username(
      std::string_view value, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-password-for-init
  static tl::expected<std::string, errors> process_password(
      std::string_view value, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-hostname-for-init
  static tl::expected<std::string, errors> process_hostname(
      std::string_view value, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-port-for-init
  static tl::expected<std::string, errors> process_port(
      std::string_view port, std::string_view protocol, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-pathname-for-init
  static tl::expected<std::string, errors> process_pathname(
      std::string_view value, std::string_view protocol, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-search-for-init
  static tl::expected<std::string, errors> process_search(
      std::string_view value, process_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-hash-for-init
  static tl::expected<std::string, errors> process_hash(std::string_view value,
                                                        process_type type);

#if ADA_TESTING
  friend void PrintTo(const url_pattern_init& init, std::ostream* os) {
    *os << "protocol: '" << init.protocol.value_or("undefined") << "', ";
    *os << "username: '" << init.username.value_or("undefined") << "', ";
    *os << "password: '" << init.password.value_or("undefined") << "', ";
    *os << "hostname: '" << init.hostname.value_or("undefined") << "', ";
    *os << "port: '" << init.port.value_or("undefined") << "', ";
    *os << "pathname: '" << init.pathname.value_or("undefined") << "', ";
    *os << "search: '" << init.search.value_or("undefined") << "', ";
    *os << "hash: '" << init.hash.value_or("undefined") << "', ";
    *os << "base_url: '" << init.base_url.value_or("undefined") << "', ";
  }
#endif  // ADA_TESTING

  bool operator==(const url_pattern_init&) const;
  // If present, must be valid UTF-8.
  std::optional<std::string> protocol{};
  // If present, must be valid UTF-8.
  std::optional<std::string> username{};
  // If present, must be valid UTF-8.
  std::optional<std::string> password{};
  // If present, must be valid UTF-8.
  std::optional<std::string> hostname{};
  // If present, must be valid UTF-8.
  std::optional<std::string> port{};
  // If present, must be valid UTF-8.
  std::optional<std::string> pathname{};
  // If present, must be valid UTF-8.
  std::optional<std::string> search{};
  // If present, must be valid UTF-8.
  std::optional<std::string> hash{};
  // If present, must be valid UTF-8.
  std::optional<std::string> base_url{};
};
}  // namespace ada
#endif  // ADA_INCLUDE_URL_PATTERN
#endif  // ADA_URL_PATTERN_INIT_H
/* end file include/ada/url_pattern_init.h */
namespace ada {
template <url_pattern_regex::regex_concept regex_provider>
class url_pattern;
struct url_pattern_options;
namespace parser {
template <url_pattern_regex::regex_concept regex_provider>
tl::expected<url_pattern<regex_provider>, errors> parse_url_pattern_impl(
    std::variant<std::string_view, url_pattern_init>&& input,
    const std::string_view* base_url, const url_pattern_options* options);
}  // namespace parser
}  // namespace ada

/* begin file include/ada/url_pattern.h */
/**
 * @file url_pattern.h
 * @brief URLPattern API implementation.
 *
 * This header provides the URLPattern API as specified by the WHATWG URL
 * Pattern Standard. URLPattern allows matching URLs against patterns with
 * wildcards and named groups, similar to how regular expressions match strings.
 *
 * @see https://urlpattern.spec.whatwg.org/
 * @see https://developer.mozilla.org/en-US/docs/Web/API/URL_Pattern_API
 */
#ifndef ADA_URL_PATTERN_H
#define ADA_URL_PATTERN_H


#include <ostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <variant>
#include <vector>

#if ADA_TESTING
#include <iostream>
#endif  // ADA_TESTING

#if ADA_INCLUDE_URL_PATTERN
namespace ada {

enum class url_pattern_part_type : uint8_t {
  // The part represents a simple fixed text string.
  FIXED_TEXT,
  // The part represents a matching group with a custom regular expression.
  REGEXP,
  // The part represents a matching group that matches code points up to the
  // next separator code point. This is typically used for a named group like
  // ":foo" that does not have a custom regular expression.
  SEGMENT_WILDCARD,
  // The part represents a matching group that greedily matches all code points.
  // This is typically used for the "*" wildcard matching group.
  FULL_WILDCARD,
};

// Pattern type for fast-path matching optimization.
// This allows skipping expensive regex evaluation for common simple patterns.
enum class url_pattern_component_type : uint8_t {
  // Pattern is "^$" - only matches empty string
  EMPTY,
  // Pattern is "^<literal>$" - exact string match (no regex needed)
  EXACT_MATCH,
  // Pattern is "^(.*)$" - matches anything (full wildcard)
  FULL_WILDCARD,
  // Pattern requires actual regex evaluation
  REGEXP,
};

enum class url_pattern_part_modifier : uint8_t {
  // The part does not have a modifier.
  none,
  // The part has an optional modifier indicated by the U+003F (?) code point.
  optional,
  // The part has a "zero or more" modifier indicated by the U+002A (*) code
  // point.
  zero_or_more,
  // The part has a "one or more" modifier indicated by the U+002B (+) code
  // point.
  one_or_more,
};

// @see https://urlpattern.spec.whatwg.org/#part
class url_pattern_part {
 public:
  url_pattern_part(url_pattern_part_type _type, std::string&& _value,
                   url_pattern_part_modifier _modifier)
      : type(_type), value(std::move(_value)), modifier(_modifier) {}

  url_pattern_part(url_pattern_part_type _type, std::string&& _value,
                   url_pattern_part_modifier _modifier, std::string&& _name,
                   std::string&& _prefix, std::string&& _suffix)
      : type(_type),
        value(std::move(_value)),
        modifier(_modifier),
        name(std::move(_name)),
        prefix(std::move(_prefix)),
        suffix(std::move(_suffix)) {}
  // A part has an associated type, a string, which must be set upon creation.
  url_pattern_part_type type;
  // A part has an associated value, a string, which must be set upon creation.
  std::string value;
  // A part has an associated modifier a string, which must be set upon
  // creation.
  url_pattern_part_modifier modifier;
  // A part has an associated name, a string, initially the empty string.
  std::string name{};
  // A part has an associated prefix, a string, initially the empty string.
  std::string prefix{};
  // A part has an associated suffix, a string, initially the empty string.
  std::string suffix{};

  inline bool is_regexp() const noexcept;
};

// @see https://urlpattern.spec.whatwg.org/#options-header
struct url_pattern_compile_component_options {
  url_pattern_compile_component_options() = default;
  explicit url_pattern_compile_component_options(
      std::optional<char> new_delimiter = std::nullopt,
      std::optional<char> new_prefix = std::nullopt) noexcept
      : delimiter(new_delimiter), prefix(new_prefix) {}

  inline std::string_view get_delimiter() const ada_warn_unused;
  inline std::string_view get_prefix() const ada_warn_unused;

  // @see https://urlpattern.spec.whatwg.org/#options-ignore-case
  bool ignore_case = false;

  static url_pattern_compile_component_options DEFAULT;
  static url_pattern_compile_component_options HOSTNAME;
  static url_pattern_compile_component_options PATHNAME;

 private:
  // @see https://urlpattern.spec.whatwg.org/#options-delimiter-code-point
  std::optional<char> delimiter{};
  // @see https://urlpattern.spec.whatwg.org/#options-prefix-code-point
  std::optional<char> prefix{};
};

// The default options is an options struct with delimiter code point set to
// the empty string and prefix code point set to the empty string.
inline url_pattern_compile_component_options
    url_pattern_compile_component_options::DEFAULT(std::nullopt, std::nullopt);

// The hostname options is an options struct with delimiter code point set
// "." and prefix code point set to the empty string.
inline url_pattern_compile_component_options
    url_pattern_compile_component_options::HOSTNAME('.', std::nullopt);

// The pathname options is an options struct with delimiter code point set
// "/" and prefix code point set to "/".
inline url_pattern_compile_component_options
    url_pattern_compile_component_options::PATHNAME('/', '/');

// A struct providing the URLPattern matching results for a single
// URL component. The URLPatternComponentResult is only ever used
// as a member attribute of a URLPatternResult struct. The
// URLPatternComponentResult API is defined as part of the URLPattern
// specification.
struct url_pattern_component_result {
  std::string input;
  std::unordered_map<std::string, std::optional<std::string>> groups;

  bool operator==(const url_pattern_component_result&) const;

#if ADA_TESTING
  friend void PrintTo(const url_pattern_component_result& result,
                      std::ostream* os) {
    *os << "input: '" << result.input << "', group: ";
    for (const auto& group : result.groups) {
      *os << "(" << group.first << ", " << group.second.value_or("undefined")
          << ") ";
    }
  }
#endif  // ADA_TESTING
};

template <url_pattern_regex::regex_concept regex_provider>
class url_pattern_component {
 public:
  url_pattern_component() = default;

  // This function explicitly takes a std::string because it is moved.
  // To avoid unnecessary copy, move each value while calling the constructor.
  url_pattern_component(std::string&& new_pattern,
                        typename regex_provider::regex_type&& new_regexp,
                        std::vector<std::string>&& new_group_name_list,
                        bool new_has_regexp_groups,
                        url_pattern_component_type new_type,
                        std::string&& new_exact_match_value = {})
      : regexp(std::move(new_regexp)),
        pattern(std::move(new_pattern)),
        group_name_list(std::move(new_group_name_list)),
        exact_match_value(std::move(new_exact_match_value)),
        has_regexp_groups(new_has_regexp_groups),
        type(new_type) {}

  // @see https://urlpattern.spec.whatwg.org/#compile-a-component
  template <url_pattern_encoding_callback F>
  static tl::expected<url_pattern_component, errors> compile(
      std::string_view input, F& encoding_callback,
      url_pattern_compile_component_options& options);

  // @see https://urlpattern.spec.whatwg.org/#create-a-component-match-result
  url_pattern_component_result create_component_match_result(
      std::string&& input,
      std::vector<std::optional<std::string>>&& exec_result);

  // Fast path test that returns true/false without constructing result groups.
  // Uses cached pattern type to skip regex evaluation for simple patterns.
  bool fast_test(std::string_view input) const noexcept;

  // Fast path match that returns capture groups without regex for simple
  // patterns. Returns nullopt if pattern doesn't match, otherwise returns
  // capture groups.
  std::optional<std::vector<std::optional<std::string>>> fast_match(
      std::string_view input) const;

#if ADA_TESTING
  friend void PrintTo(const url_pattern_component& component,
                      std::ostream* os) {
    *os << "pattern: '" << component.pattern
        << "', has_regexp_groups: " << component.has_regexp_groups
        << "group_name_list: ";
    for (const auto& name : component.group_name_list) {
      *os << name << ", ";
    }
  }
#endif  // ADA_TESTING

  typename regex_provider::regex_type regexp{};
  std::string pattern{};
  std::vector<std::string> group_name_list{};
  // For EXACT_MATCH type: the literal string to compare against
  std::string exact_match_value{};
  bool has_regexp_groups = false;
  // Cached pattern type for fast-path optimization
  url_pattern_component_type type = url_pattern_component_type::REGEXP;
};

// A URLPattern input can be either a string or a URLPatternInit object.
// If it is a string, it must be a valid UTF-8 string.
using url_pattern_input = std::variant<std::string_view, url_pattern_init>;

// A struct providing the URLPattern matching results for all
// components of a URL. The URLPatternResult API is defined as
// part of the URLPattern specification.
struct url_pattern_result {
  std::vector<url_pattern_input> inputs;
  url_pattern_component_result protocol;
  url_pattern_component_result username;
  url_pattern_component_result password;
  url_pattern_component_result hostname;
  url_pattern_component_result port;
  url_pattern_component_result pathname;
  url_pattern_component_result search;
  url_pattern_component_result hash;
};

struct url_pattern_options {
  bool ignore_case = false;

#if ADA_TESTING
  friend void PrintTo(const url_pattern_options& options, std::ostream* os) {
    *os << "ignore_case: '" << options.ignore_case;
  }
#endif  // ADA_TESTING
};

/**
 * @brief URL pattern matching class implementing the URLPattern API.
 *
 * URLPattern provides a way to match URLs against patterns with wildcards
 * and named capture groups. It's useful for routing, URL-based dispatching,
 * and URL validation.
 *
 * Pattern syntax supports:
 * - Literal text matching
 * - Named groups: `:name` (matches up to the next separator)
 * - Wildcards: `*` (matches everything)
 * - Custom regex: `(pattern)`
 * - Optional segments: `:name?`
 * - Repeated segments: `:name+`, `:name*`
 *
 * @tparam regex_provider The regex implementation to use for pattern matching.
 *         Must satisfy the url_pattern_regex::regex_concept.
 *
 * @note All string inputs must be valid UTF-8.
 *
 * @see https://urlpattern.spec.whatwg.org/
 */
template <url_pattern_regex::regex_concept regex_provider>
class url_pattern {
 public:
  url_pattern() = default;

  /**
   * If non-null, base_url must pointer at a valid UTF-8 string.
   * @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-exec
   */
  result<std::optional<url_pattern_result>> exec(
      const url_pattern_input& input,
      const std::string_view* base_url = nullptr);

  /**
   * If non-null, base_url must pointer at a valid UTF-8 string.
   * @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-test
   */
  result<bool> test(const url_pattern_input& input,
                    const std::string_view* base_url = nullptr);

  /**
   * @see https://urlpattern.spec.whatwg.org/#url-pattern-match
   * This function expects a valid UTF-8 string if input is a string.
   */
  result<std::optional<url_pattern_result>> match(
      const url_pattern_input& input,
      const std::string_view* base_url_string = nullptr);

  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-protocol
  [[nodiscard]] std::string_view get_protocol() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-username
  [[nodiscard]] std::string_view get_username() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-password
  [[nodiscard]] std::string_view get_password() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-hostname
  [[nodiscard]] std::string_view get_hostname() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-port
  [[nodiscard]] std::string_view get_port() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-pathname
  [[nodiscard]] std::string_view get_pathname() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-search
  [[nodiscard]] std::string_view get_search() const ada_lifetime_bound;
  // @see https://urlpattern.spec.whatwg.org/#dom-urlpattern-hash
  [[nodiscard]] std::string_view get_hash() const ada_lifetime_bound;

  // If ignoreCase is true, the JavaScript regular expression created for each
  // pattern must use the `vi` flag. Otherwise, they must use the `v` flag.
  [[nodiscard]] bool ignore_case() const;

  // @see https://urlpattern.spec.whatwg.org/#url-pattern-has-regexp-groups
  [[nodiscard]] bool has_regexp_groups() const;

  // Helper to test all components at once. Returns true if all match.
  [[nodiscard]] bool test_components(
      std::string_view protocol, std::string_view username,
      std::string_view password, std::string_view hostname,
      std::string_view port, std::string_view pathname, std::string_view search,
      std::string_view hash) const;

#if ADA_TESTING
  friend void PrintTo(const url_pattern& c, std::ostream* os) {
    *os << "protocol_component: '" << c.get_protocol() << ", ";
    *os << "username_component: '" << c.get_username() << ", ";
    *os << "password_component: '" << c.get_password() << ", ";
    *os << "hostname_component: '" << c.get_hostname() << ", ";
    *os << "port_component: '" << c.get_port() << ", ";
    *os << "pathname_component: '" << c.get_pathname() << ", ";
    *os << "search_component: '" << c.get_search() << ", ";
    *os << "hash_component: '" << c.get_hash();
  }
#endif  // ADA_TESTING

  template <url_pattern_regex::regex_concept P>
  friend tl::expected<url_pattern<P>, errors> parser::parse_url_pattern_impl(
      std::variant<std::string_view, url_pattern_init>&& input,
      const std::string_view* base_url, const url_pattern_options* options);

  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> protocol_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> username_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> password_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> hostname_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> port_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> pathname_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> search_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  url_pattern_component<regex_provider> hash_component{};
  /**
   * @private
   * We can not make this private due to a LLVM bug.
   * Ref: https://github.com/ada-url/ada/pull/859
   */
  bool ignore_case_ = false;
};
}  // namespace ada
#endif  // ADA_INCLUDE_URL_PATTERN
#endif
/* end file include/ada/url_pattern.h */
/* begin file include/ada/url_pattern_helpers.h */
/**
 * @file url_pattern_helpers.h
 * @brief Declaration for the URLPattern helpers.
 */
#ifndef ADA_URL_PATTERN_HELPERS_H
#define ADA_URL_PATTERN_HELPERS_H


#include <string>
#include <tuple>
#include <vector>

#if ADA_INCLUDE_URL_PATTERN
namespace ada {
enum class errors : uint8_t;
}

namespace ada::url_pattern_helpers {

// @see https://urlpattern.spec.whatwg.org/#token
enum class token_type : uint8_t {
  INVALID_CHAR,    // 0
  OPEN,            // 1
  CLOSE,           // 2
  REGEXP,          // 3
  NAME,            // 4
  CHAR,            // 5
  ESCAPED_CHAR,    // 6
  OTHER_MODIFIER,  // 7
  ASTERISK,        // 8
  END,             // 9
};

#ifdef ADA_TESTING
std::string to_string(token_type type);
#endif  // ADA_TESTING

// @see https://urlpattern.spec.whatwg.org/#tokenize-policy
enum class token_policy {
  strict,
  lenient,
};

// @see https://urlpattern.spec.whatwg.org/#tokens
class token {
 public:
  token(token_type _type, size_t _index, std::string_view _value)
      : type(_type), index(_index), value(_value) {}

  // A token has an associated type, a string, initially "invalid-char".
  token_type type = token_type::INVALID_CHAR;

  // A token has an associated index, a number, initially 0. It is the position
  // of the first code point in the pattern string represented by the token.
  size_t index = 0;

  // A token has an associated value, a string, initially the empty string. It
  // contains the code points from the pattern string represented by the token.
  std::string_view value{};
};

// @see https://urlpattern.spec.whatwg.org/#pattern-parser
template <url_pattern_encoding_callback F>
class url_pattern_parser {
 public:
  url_pattern_parser(F& encoding_callback_,
                     std::string_view segment_wildcard_regexp_)
      : encoding_callback(encoding_callback_),
        segment_wildcard_regexp(segment_wildcard_regexp_) {}

  bool can_continue() const { return index < tokens.size(); }

  // @see https://urlpattern.spec.whatwg.org/#try-to-consume-a-token
  token* try_consume_token(token_type type);
  // @see https://urlpattern.spec.whatwg.org/#try-to-consume-a-modifier-token
  token* try_consume_modifier_token();
  // @see
  // https://urlpattern.spec.whatwg.org/#try-to-consume-a-regexp-or-wildcard-token
  token* try_consume_regexp_or_wildcard_token(const token* name_token);
  // @see https://urlpattern.spec.whatwg.org/#consume-text
  std::string consume_text();
  // @see https://urlpattern.spec.whatwg.org/#consume-a-required-token
  bool consume_required_token(token_type type);
  // @see
  // https://urlpattern.spec.whatwg.org/#maybe-add-a-part-from-the-pending-fixed-value
  std::optional<errors> maybe_add_part_from_the_pending_fixed_value()
      ada_warn_unused;
  // @see https://urlpattern.spec.whatwg.org/#add-a-part
  std::optional<errors> add_part(std::string_view prefix, token* name_token,
                                 token* regexp_or_wildcard_token,
                                 std::string_view suyffix,
                                 token* modifier_token) ada_warn_unused;

  std::vector<token> tokens{};
  F& encoding_callback;
  std::string segment_wildcard_regexp;
  std::vector<url_pattern_part> parts{};
  std::string pending_fixed_value{};
  size_t index = 0;
  size_t next_numeric_name = 0;
};

// @see https://urlpattern.spec.whatwg.org/#tokenizer
class Tokenizer {
 public:
  explicit Tokenizer(std::string_view new_input, token_policy new_policy)
      : input(new_input), policy(new_policy) {}

  // @see https://urlpattern.spec.whatwg.org/#get-the-next-code-point
  constexpr void get_next_code_point();

  // True when the most recent decoded unit was malformed UTF-8.
  bool had_invalid_code_point() const { return invalid_code_point; }

  // @see https://urlpattern.spec.whatwg.org/#seek-and-get-the-next-code-point
  constexpr void seek_and_get_next_code_point(size_t index);

  // @see https://urlpattern.spec.whatwg.org/#add-a-token

  void add_token(token_type type, size_t next_position, size_t value_position,
                 size_t value_length);

  // @see https://urlpattern.spec.whatwg.org/#add-a-token-with-default-length
  void add_token_with_default_length(token_type type, size_t next_position,
                                     size_t value_position);

  // @see
  // https://urlpattern.spec.whatwg.org/#add-a-token-with-default-position-and-length
  void add_token_with_defaults(token_type type);

  // @see https://urlpattern.spec.whatwg.org/#process-a-tokenizing-error
  std::optional<errors> process_tokenizing_error(
      size_t next_position, size_t value_position) ada_warn_unused;

  friend tl::expected<std::vector<token>, errors> tokenize(
      std::string_view input, token_policy policy);

 private:
  // has an associated input, a pattern string, initially the empty string.
  std::string_view input;
  // has an associated policy, a tokenize policy, initially "strict".
  token_policy policy;
  // has an associated token list, a token list, initially an empty list.
  std::vector<token> token_list{};
  // has an associated index, a number, initially 0.
  size_t index = 0;
  // has an associated next index, a number, initially 0.
  size_t next_index = 0;
  // has an associated code point, a Unicode code point, initially null.
  char32_t code_point{};
  // Tracks whether the last decoded code point was malformed UTF-8.
  bool invalid_code_point = false;
};

// @see https://urlpattern.spec.whatwg.org/#constructor-string-parser
template <url_pattern_regex::regex_concept regex_provider>
struct constructor_string_parser {
  explicit constructor_string_parser(std::string_view new_input,
                                     std::vector<token>&& new_token_list)
      : input(new_input), token_list(std::move(new_token_list)) {}
  // @see https://urlpattern.spec.whatwg.org/#parse-a-constructor-string
  static tl::expected<url_pattern_init, errors> parse(std::string_view input);

  // @see https://urlpattern.spec.whatwg.org/#constructor-string-parser-state
  enum class State {
    INIT,
    PROTOCOL,
    AUTHORITY,
    USERNAME,
    PASSWORD,
    HOSTNAME,
    PORT,
    PATHNAME,
    SEARCH,
    HASH,
    DONE,
  };

  // @see
  // https://urlpattern.spec.whatwg.org/#compute-protocol-matches-a-special-scheme-flag
  std::optional<errors> compute_protocol_matches_special_scheme_flag();

 private:
  // @see https://urlpattern.spec.whatwg.org/#rewind
  constexpr void rewind();

  // @see https://urlpattern.spec.whatwg.org/#is-a-hash-prefix
  constexpr bool is_hash_prefix();

  // @see https://urlpattern.spec.whatwg.org/#is-a-search-prefix
  constexpr bool is_search_prefix();

  // @see https://urlpattern.spec.whatwg.org/#change-state
  void change_state(State state, size_t skip);

  // @see https://urlpattern.spec.whatwg.org/#is-a-group-open
  constexpr bool is_group_open() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-group-close
  constexpr bool is_group_close() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-protocol-suffix
  constexpr bool is_protocol_suffix() const;

  // @see https://urlpattern.spec.whatwg.org/#next-is-authority-slashes
  constexpr bool next_is_authority_slashes() const;

  // @see https://urlpattern.spec.whatwg.org/#is-an-identity-terminator
  constexpr bool is_an_identity_terminator() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-pathname-start
  constexpr bool is_pathname_start() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-password-prefix
  constexpr bool is_password_prefix() const;

  // @see https://urlpattern.spec.whatwg.org/#is-an-ipv6-open
  constexpr bool is_an_ipv6_open() const;

  // @see https://urlpattern.spec.whatwg.org/#is-an-ipv6-close
  constexpr bool is_an_ipv6_close() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-port-prefix
  constexpr bool is_port_prefix() const;

  // @see https://urlpattern.spec.whatwg.org/#is-a-non-special-pattern-char
  constexpr bool is_non_special_pattern_char(size_t index,
                                             uint32_t value) const;

  // @see https://urlpattern.spec.whatwg.org/#get-a-safe-token
  constexpr const token* get_safe_token(size_t index) const;

  // @see https://urlpattern.spec.whatwg.org/#make-a-component-string
  std::string make_component_string();
  // has an associated input, a string, which must be set upon creation.
  std::string_view input;
  // has an associated token list, a token list, which must be set upon
  // creation.
  std::vector<token> token_list;
  // has an associated result, a URLPatternInit, initially set to a new
  // URLPatternInit.
  url_pattern_init result{};
  // has an associated component start, a number, initially set to 0.
  size_t component_start = 0;
  // has an associated token index, a number, initially set to 0.
  size_t token_index = 0;
  // has an associated token increment, a number, initially set to 1.
  size_t token_increment = 1;
  // has an associated group depth, a number, initially set to 0.
  size_t group_depth = 0;
  // has an associated hostname IPv6 bracket depth, a number, initially set to
  // 0.
  size_t hostname_ipv6_bracket_depth = 0;
  // has an associated protocol matches a special scheme flag, a boolean,
  // initially set to false.
  bool protocol_matches_a_special_scheme_flag = false;
  // has an associated state, a string, initially set to "init".
  State state = State::INIT;
};

// @see https://urlpattern.spec.whatwg.org/#canonicalize-a-protocol
tl::expected<std::string, errors> canonicalize_protocol(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-username
tl::expected<std::string, errors> canonicalize_username(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-password
tl::expected<std::string, errors> canonicalize_password(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-password
tl::expected<std::string, errors> canonicalize_hostname(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-an-ipv6-hostname
tl::expected<std::string, errors> canonicalize_ipv6_hostname(
    std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-port
tl::expected<std::string, errors> canonicalize_port(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-port
tl::expected<std::string, errors> canonicalize_port_with_protocol(
    std::string_view input, std::string_view protocol);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-pathname
tl::expected<std::string, errors> canonicalize_pathname(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-an-opaque-pathname
tl::expected<std::string, errors> canonicalize_opaque_pathname(
    std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-search
tl::expected<std::string, errors> canonicalize_search(std::string_view input);

// @see https://wicg.github.io/urlpattern/#canonicalize-a-hash
tl::expected<std::string, errors> canonicalize_hash(std::string_view input);

// @see https://urlpattern.spec.whatwg.org/#tokenize
tl::expected<std::vector<token>, errors> tokenize(std::string_view input,
                                                  token_policy policy);

// @see https://urlpattern.spec.whatwg.org/#process-a-base-url-string
std::string process_base_url_string(std::string_view input,
                                    url_pattern_init::process_type type);

// @see https://urlpattern.spec.whatwg.org/#escape-a-pattern-string
std::string escape_pattern_string(std::string_view input);

// @see https://urlpattern.spec.whatwg.org/#escape-a-regexp-string
std::string escape_regexp_string(std::string_view input);

// @see https://urlpattern.spec.whatwg.org/#is-an-absolute-pathname
constexpr bool is_absolute_pathname(
    std::string_view input, url_pattern_init::process_type type) noexcept;

// @see https://urlpattern.spec.whatwg.org/#parse-a-pattern-string
template <url_pattern_encoding_callback F>
tl::expected<std::vector<url_pattern_part>, errors> parse_pattern_string(
    std::string_view input, url_pattern_compile_component_options& options,
    F& encoding_callback);

// @see https://urlpattern.spec.whatwg.org/#generate-a-pattern-string
std::string generate_pattern_string(
    std::vector<url_pattern_part>& part_list,
    url_pattern_compile_component_options& options);

// @see
// https://urlpattern.spec.whatwg.org/#generate-a-regular-expression-and-name-list
std::tuple<std::string, std::vector<std::string>>
generate_regular_expression_and_name_list(
    const std::vector<url_pattern_part>& part_list,
    url_pattern_compile_component_options options);

// @see https://urlpattern.spec.whatwg.org/#hostname-pattern-is-an-ipv6-address
bool is_ipv6_address(std::string_view input) noexcept;

// @see
// https://urlpattern.spec.whatwg.org/#protocol-component-matches-a-special-scheme
template <url_pattern_regex::regex_concept regex_provider>
bool protocol_component_matches_special_scheme(
    ada::url_pattern_component<regex_provider>& input);

// @see https://urlpattern.spec.whatwg.org/#convert-a-modifier-to-a-string
std::string_view convert_modifier_to_string(url_pattern_part_modifier modifier);

// @see https://urlpattern.spec.whatwg.org/#generate-a-segment-wildcard-regexp
std::string generate_segment_wildcard_regexp(
    url_pattern_compile_component_options options);

}  // namespace ada::url_pattern_helpers
#endif  // ADA_INCLUDE_URL_PATTERN
#endif
/* end file include/ada/url_pattern_helpers.h */
/* begin file include/ada/parser-inl.h */
/**
 * @file parser-inl.h
 */
#ifndef ADA_PARSER_INL_H
#define ADA_PARSER_INL_H


#include <string>
#include <string_view>
#include <variant>

namespace ada::parser {
#if ADA_INCLUDE_URL_PATTERN
template <url_pattern_regex::regex_concept regex_provider>
tl::expected<url_pattern<regex_provider>, errors> parse_url_pattern_impl(
    std::variant<std::string_view, url_pattern_init>&& input,
    const std::string_view* base_url, const url_pattern_options* options) {
  // Let init be null.
  url_pattern_init init;

  // If input is a scalar value string then:
  if (std::holds_alternative<std::string_view>(input)) {
    // Set init to the result of running parse a constructor string given input.
    auto parse_result =
        url_pattern_helpers::constructor_string_parser<regex_provider>::parse(
            std::get<std::string_view>(input));
    if (!parse_result) {
      ada_log("constructor_string_parser::parse failed");
      return tl::unexpected(parse_result.error());
    }
    init = std::move(*parse_result);
    // If baseURL is null and init["protocol"] does not exist, then throw a
    // TypeError.
    if (!base_url && !init.protocol) {
      ada_log("base url is null and protocol is not set");
      return tl::unexpected(errors::type_error);
    }

    // If baseURL is not null, set init["baseURL"] to baseURL.
    if (base_url) {
      init.base_url = std::string(*base_url);
    }
  } else {
    // Assert: input is a URLPatternInit.
    ADA_ASSERT_TRUE(std::holds_alternative<url_pattern_init>(input));
    // If baseURL is not null, then throw a TypeError.
    if (base_url) {
      ada_log("base url is not null");
      return tl::unexpected(errors::type_error);
    }
    // Optimization: Avoid copy by moving the input value.
    // Set init to input.
    init = std::move(std::get<url_pattern_init>(input));
  }

  // Let processedInit be the result of process a URLPatternInit given init,
  // "pattern", null, null, null, null, null, null, null, and null.
  auto processed_init =
      url_pattern_init::process(init, url_pattern_init::process_type::pattern);
  if (!processed_init) {
    ada_log("url_pattern_init::process failed for init and 'pattern'");
    return tl::unexpected(processed_init.error());
  }

  // For each componentName of  "protocol", "username", "password", "hostname",
  // "port", "pathname", "search", "hash" If processedInit[componentName] does
  // not exist, then set processedInit[componentName] to "*".
  ADA_ASSERT_TRUE(processed_init.has_value());
  if (!processed_init->protocol) processed_init->protocol = "*";
  if (!processed_init->username) processed_init->username = "*";
  if (!processed_init->password) processed_init->password = "*";
  if (!processed_init->hostname) processed_init->hostname = "*";
  if (!processed_init->port) processed_init->port = "*";
  if (!processed_init->pathname) processed_init->pathname = "*";
  if (!processed_init->search) processed_init->search = "*";
  if (!processed_init->hash) processed_init->hash = "*";

  ada_log("-- processed_init->protocol: ", processed_init->protocol.value());
  ada_log("-- processed_init->username: ", processed_init->username.value());
  ada_log("-- processed_init->password: ", processed_init->password.value());
  ada_log("-- processed_init->hostname: ", processed_init->hostname.value());
  ada_log("-- processed_init->port: ", processed_init->port.value());
  ada_log("-- processed_init->pathname: ", processed_init->pathname.value());
  ada_log("-- processed_init->search: ", processed_init->search.value());
  ada_log("-- processed_init->hash: ", processed_init->hash.value());

  // If processedInit["protocol"] is a special scheme and processedInit["port"]
  // is a string which represents its corresponding default port in radix-10
  // using ASCII digits then set processedInit["port"] to the empty string.
  // TODO: Optimization opportunity.
  if (scheme::is_special(*processed_init->protocol)) {
    std::string_view port = processed_init->port.value();
    if (std::to_string(scheme::get_special_port(*processed_init->protocol)) ==
        port) {
      processed_init->port->clear();
    }
  }

  // Let urlPattern be a new URL pattern.
  url_pattern<regex_provider> url_pattern_{};

  // Set urlPattern's protocol component to the result of compiling a component
  // given processedInit["protocol"], canonicalize a protocol, and default
  // options.
  auto protocol_component = url_pattern_component<regex_provider>::compile(
      processed_init->protocol.value(),
      url_pattern_helpers::canonicalize_protocol,
      url_pattern_compile_component_options::DEFAULT);
  if (!protocol_component) {
    ada_log("url_pattern_component::compile failed for protocol ",
            processed_init->protocol.value());
    return tl::unexpected(protocol_component.error());
  }
  url_pattern_.protocol_component = std::move(*protocol_component);

  // Set urlPattern's username component to the result of compiling a component
  // given processedInit["username"], canonicalize a username, and default
  // options.
  auto username_component = url_pattern_component<regex_provider>::compile(
      processed_init->username.value(),
      url_pattern_helpers::canonicalize_username,
      url_pattern_compile_component_options::DEFAULT);
  if (!username_component) {
    ada_log("url_pattern_component::compile failed for username ",
            processed_init->username.value());
    return tl::unexpected(username_component.error());
  }
  url_pattern_.username_component = std::move(*username_component);

  // Set urlPattern's password component to the result of compiling a component
  // given processedInit["password"], canonicalize a password, and default
  // options.
  auto password_component = url_pattern_component<regex_provider>::compile(
      processed_init->password.value(),
      url_pattern_helpers::canonicalize_password,
      url_pattern_compile_component_options::DEFAULT);
  if (!password_component) {
    ada_log("url_pattern_component::compile failed for password ",
            processed_init->password.value());
    return tl::unexpected(password_component.error());
  }
  url_pattern_.password_component = std::move(*password_component);

  // TODO: Optimization opportunity. The following if statement can be
  // simplified.
  // If the result running hostname pattern is an IPv6 address given
  // processedInit["hostname"] is true, then set urlPattern's hostname component
  // to the result of compiling a component given processedInit["hostname"],
  // canonicalize an IPv6 hostname, and hostname options.
  if (url_pattern_helpers::is_ipv6_address(processed_init->hostname.value())) {
    ada_log("processed_init->hostname is ipv6 address");
    // then set urlPattern's hostname component to the result of compiling a
    // component given processedInit["hostname"], canonicalize an IPv6 hostname,
    // and hostname options.
    auto hostname_component = url_pattern_component<regex_provider>::compile(
        processed_init->hostname.value(),
        url_pattern_helpers::canonicalize_ipv6_hostname,
        url_pattern_compile_component_options::DEFAULT);
    if (!hostname_component) {
      ada_log("url_pattern_component::compile failed for ipv6 hostname ",
              processed_init->hostname.value());
      return tl::unexpected(hostname_component.error());
    }
    url_pattern_.hostname_component = std::move(*hostname_component);
  } else {
    // Otherwise, set urlPattern's hostname component to the result of compiling
    // a component given processedInit["hostname"], canonicalize a hostname, and
    // hostname options.
    auto hostname_component = url_pattern_component<regex_provider>::compile(
        processed_init->hostname.value(),
        url_pattern_helpers::canonicalize_hostname,
        url_pattern_compile_component_options::HOSTNAME);
    if (!hostname_component) {
      ada_log("url_pattern_component::compile failed for hostname ",
              processed_init->hostname.value());
      return tl::unexpected(hostname_component.error());
    }
    url_pattern_.hostname_component = std::move(*hostname_component);
  }

  // Set urlPattern's port component to the result of compiling a component
  // given processedInit["port"], canonicalize a port, and default options.
  auto port_component = url_pattern_component<regex_provider>::compile(
      processed_init->port.value(), url_pattern_helpers::canonicalize_port,
      url_pattern_compile_component_options::DEFAULT);
  if (!port_component) {
    ada_log("url_pattern_component::compile failed for port ",
            processed_init->port.value());
    return tl::unexpected(port_component.error());
  }
  url_pattern_.port_component = std::move(*port_component);

  // Let compileOptions be a copy of the default options with the ignore case
  // property set to options["ignoreCase"].
  auto compile_options = url_pattern_compile_component_options::DEFAULT;
  if (options) {
    compile_options.ignore_case = options->ignore_case;
  }

  // TODO: Optimization opportunity: Simplify this if statement.
  // If the result of running protocol component matches a special scheme given
  // urlPattern's protocol component is true, then:
  if (url_pattern_helpers::protocol_component_matches_special_scheme<
          regex_provider>(url_pattern_.protocol_component)) {
    // Let pathCompileOptions be copy of the pathname options with the ignore
    // case property set to options["ignoreCase"].
    auto path_compile_options = url_pattern_compile_component_options::PATHNAME;
    if (options) {
      path_compile_options.ignore_case = options->ignore_case;
    }

    // Set urlPattern's pathname component to the result of compiling a
    // component given processedInit["pathname"], canonicalize a pathname, and
    // pathCompileOptions.
    auto pathname_component = url_pattern_component<regex_provider>::compile(
        processed_init->pathname.value(),
        url_pattern_helpers::canonicalize_pathname, path_compile_options);
    if (!pathname_component) {
      ada_log("url_pattern_component::compile failed for pathname ",
              processed_init->pathname.value());
      return tl::unexpected(pathname_component.error());
    }
    url_pattern_.pathname_component = std::move(*pathname_component);
  } else {
    // Otherwise set urlPattern's pathname component to the result of compiling
    // a component given processedInit["pathname"], canonicalize an opaque
    // pathname, and compileOptions.
    auto pathname_component = url_pattern_component<regex_provider>::compile(
        processed_init->pathname.value(),
        url_pattern_helpers::canonicalize_opaque_pathname, compile_options);
    if (!pathname_component) {
      ada_log("url_pattern_component::compile failed for opaque pathname ",
              processed_init->pathname.value());
      return tl::unexpected(pathname_component.error());
    }
    url_pattern_.pathname_component = std::move(*pathname_component);
  }

  // Set urlPattern's search component to the result of compiling a component
  // given processedInit["search"], canonicalize a search, and compileOptions.
  auto search_component = url_pattern_component<regex_provider>::compile(
      processed_init->search.value(), url_pattern_helpers::canonicalize_search,
      compile_options);
  if (!search_component) {
    ada_log("url_pattern_component::compile failed for search ",
            processed_init->search.value());
    return tl::unexpected(search_component.error());
  }
  url_pattern_.search_component = std::move(*search_component);

  // Set urlPattern's hash component to the result of compiling a component
  // given processedInit["hash"], canonicalize a hash, and compileOptions.
  auto hash_component = url_pattern_component<regex_provider>::compile(
      processed_init->hash.value(), url_pattern_helpers::canonicalize_hash,
      compile_options);
  if (!hash_component) {
    ada_log("url_pattern_component::compile failed for hash ",
            processed_init->hash.value());
    return tl::unexpected(hash_component.error());
  }
  url_pattern_.hash_component = std::move(*hash_component);

  // Return urlPattern.
  return url_pattern_;
}
#endif  // ADA_INCLUDE_URL_PATTERN

}  // namespace ada::parser

#endif  // ADA_PARSER_INL_H
/* end file include/ada/parser-inl.h */
/* begin file include/ada/url_pattern-inl.h */
/**
 * @file url_pattern-inl.h
 * @brief Declaration for the URLPattern inline functions.
 */
#ifndef ADA_URL_PATTERN_INL_H
#define ADA_URL_PATTERN_INL_H


#include <algorithm>
#include <string_view>
#include <utility>

#if ADA_INCLUDE_URL_PATTERN
namespace ada {

inline bool url_pattern_init::operator==(const url_pattern_init& other) const {
  return protocol == other.protocol && username == other.username &&
         password == other.password && hostname == other.hostname &&
         port == other.port && search == other.search && hash == other.hash &&
         pathname == other.pathname;
}

inline bool url_pattern_component_result::operator==(
    const url_pattern_component_result& other) const {
  return input == other.input && groups == other.groups;
}

template <url_pattern_regex::regex_concept regex_provider>
url_pattern_component_result
url_pattern_component<regex_provider>::create_component_match_result(
    std::string&& input,
    std::vector<std::optional<std::string>>&& exec_result) {
  // Let result be a new URLPatternComponentResult.
  // Set result["input"] to input.
  // Let groups be a record<USVString, (USVString or undefined)>.
  auto result =
      url_pattern_component_result{.input = std::move(input), .groups = {}};

  // We explicitly start iterating from 0 even though the spec
  // says we should start from 1. This case is handled by the
  // std_regex_provider which removes the full match from index 0.
  // Use min() to guard against potential mismatches between
  // exec_result size and group_name_list size.
  const size_t size = std::min(exec_result.size(), group_name_list.size());
  result.groups.reserve(size);
  for (size_t index = 0; index < size; index++) {
    result.groups.emplace(group_name_list[index],
                          std::move(exec_result[index]));
  }
  return result;
}

template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_protocol() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's protocol component's pattern string.
  return protocol_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_username() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's username component's pattern string.
  return username_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_password() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's password component's pattern string.
  return password_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_hostname() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's hostname component's pattern string.
  return hostname_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_port() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's port component's pattern string.
  return port_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_pathname() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's pathname component's pattern string.
  return pathname_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_search() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's search component's pattern string.
  return search_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
std::string_view url_pattern<regex_provider>::get_hash() const
    ada_lifetime_bound {
  // Return this's associated URL pattern's hash component's pattern string.
  return hash_component.pattern;
}
template <url_pattern_regex::regex_concept regex_provider>
bool url_pattern<regex_provider>::ignore_case() const {
  return ignore_case_;
}
template <url_pattern_regex::regex_concept regex_provider>
bool url_pattern<regex_provider>::has_regexp_groups() const {
  // If this's associated URL pattern's has regexp groups, then return true.
  return protocol_component.has_regexp_groups ||
         username_component.has_regexp_groups ||
         password_component.has_regexp_groups ||
         hostname_component.has_regexp_groups ||
         port_component.has_regexp_groups ||
         pathname_component.has_regexp_groups ||
         search_component.has_regexp_groups || hash_component.has_regexp_groups;
}

inline bool url_pattern_part::is_regexp() const noexcept {
  return type == url_pattern_part_type::REGEXP;
}

inline std::string_view url_pattern_compile_component_options::get_delimiter()
    const {
  if (delimiter) {
    return {&delimiter.value(), 1};
  }
  return {};
}

inline std::string_view url_pattern_compile_component_options::get_prefix()
    const {
  if (prefix) {
    return {&prefix.value(), 1};
  }
  return {};
}

template <url_pattern_regex::regex_concept regex_provider>
template <url_pattern_encoding_callback F>
tl::expected<url_pattern_component<regex_provider>, errors>
url_pattern_component<regex_provider>::compile(
    std::string_view input, F& encoding_callback,
    url_pattern_compile_component_options& options) {
  ada_log("url_pattern_component::compile input: ", input);
  // Let part list be the result of running parse a pattern string given input,
  // options, and encoding callback.
  auto part_list = url_pattern_helpers::parse_pattern_string(input, options,
                                                             encoding_callback);

  if (!part_list) {
    ada_log("parse_pattern_string failed");
    return tl::unexpected(part_list.error());
  }

  // Detect pattern type early to potentially skip expensive regex compilation
  const auto has_regexp = [](const auto& part) { return part.is_regexp(); };
  const bool has_regexp_groups = std::ranges::any_of(*part_list, has_regexp);

  url_pattern_component_type component_type =
      url_pattern_component_type::REGEXP;
  std::string exact_match_value{};

  if (part_list->empty()) {
    component_type = url_pattern_component_type::EMPTY;
  } else if (part_list->size() == 1) {
    const auto& part = (*part_list)[0];
    if (part.type == url_pattern_part_type::FIXED_TEXT &&
        part.modifier == url_pattern_part_modifier::none &&
        !options.ignore_case) {
      component_type = url_pattern_component_type::EXACT_MATCH;
      exact_match_value = part.value;
    } else if (part.type == url_pattern_part_type::FULL_WILDCARD &&
               part.modifier == url_pattern_part_modifier::none &&
               part.prefix.empty() && part.suffix.empty()) {
      component_type = url_pattern_component_type::FULL_WILDCARD;
    }
  }

  // For simple patterns, skip regex generation and compilation entirely
  if (component_type != url_pattern_component_type::REGEXP) {
    auto pattern_string =
        url_pattern_helpers::generate_pattern_string(*part_list, options);
    // For FULL_WILDCARD, we need the group name from
    // generate_regular_expression
    std::vector<std::string> name_list;
    if (component_type == url_pattern_component_type::FULL_WILDCARD &&
        !part_list->empty()) {
      name_list.push_back((*part_list)[0].name);
    }
    return url_pattern_component<regex_provider>(
        std::move(pattern_string), typename regex_provider::regex_type{},
        std::move(name_list), has_regexp_groups, component_type,
        std::move(exact_match_value));
  }

  // Generate regex for complex patterns
  auto [regular_expression_string, name_list] =
      url_pattern_helpers::generate_regular_expression_and_name_list(*part_list,
                                                                     options);
  auto pattern_string =
      url_pattern_helpers::generate_pattern_string(*part_list, options);

  std::optional<typename regex_provider::regex_type> regular_expression =
      regex_provider::create_instance(regular_expression_string,
                                      options.ignore_case);
  if (!regular_expression) {
    return tl::unexpected(errors::type_error);
  }

  return url_pattern_component<regex_provider>(
      std::move(pattern_string), std::move(*regular_expression),
      std::move(name_list), has_regexp_groups, component_type,
      std::move(exact_match_value));
}

template <url_pattern_regex::regex_concept regex_provider>
bool url_pattern_component<regex_provider>::fast_test(
    std::string_view input) const noexcept {
  // Fast path for simple patterns - avoid regex evaluation
  // Using if-else for better branch prediction on common cases
  if (type == url_pattern_component_type::FULL_WILDCARD) {
    return true;
  }
  if (type == url_pattern_component_type::EXACT_MATCH) {
    return input == exact_match_value;
  }
  if (type == url_pattern_component_type::EMPTY) {
    return input.empty();
  }
  // type == REGEXP
  return regex_provider::regex_match(input, regexp);
}

template <url_pattern_regex::regex_concept regex_provider>
std::optional<std::vector<std::optional<std::string>>>
url_pattern_component<regex_provider>::fast_match(
    std::string_view input) const {
  // Handle each type directly without redundant checks
  if (type == url_pattern_component_type::FULL_WILDCARD) {
    // FULL_WILDCARD always matches - capture the input (even if empty)
    // If there's no group name, return empty groups
    if (group_name_list.empty()) {
      return std::vector<std::optional<std::string>>{};
    }
    // Capture the matched input (including empty strings)
    return std::vector<std::optional<std::string>>{std::string(input)};
  }
  if (type == url_pattern_component_type::EXACT_MATCH) {
    if (input == exact_match_value) {
      return std::vector<std::optional<std::string>>{};
    }
    return std::nullopt;
  }
  if (type == url_pattern_component_type::EMPTY) {
    if (input.empty()) {
      return std::vector<std::optional<std::string>>{};
    }
    return std::nullopt;
  }
  // type == REGEXP - use regex
  return regex_provider::regex_search(input, regexp);
}

template <url_pattern_regex::regex_concept regex_provider>
result<std::optional<url_pattern_result>> url_pattern<regex_provider>::exec(
    const url_pattern_input& input, const std::string_view* base_url) {
  // Return the result of match given this's associated URL pattern, input, and
  // baseURL if given.
  return match(input, base_url);
}

template <url_pattern_regex::regex_concept regex_provider>
bool url_pattern<regex_provider>::test_components(
    std::string_view protocol, std::string_view username,
    std::string_view password, std::string_view hostname, std::string_view port,
    std::string_view pathname, std::string_view search,
    std::string_view hash) const {
  return protocol_component.fast_test(protocol) &&
         username_component.fast_test(username) &&
         password_component.fast_test(password) &&
         hostname_component.fast_test(hostname) &&
         port_component.fast_test(port) &&
         pathname_component.fast_test(pathname) &&
         search_component.fast_test(search) && hash_component.fast_test(hash);
}

template <url_pattern_regex::regex_concept regex_provider>
result<bool> url_pattern<regex_provider>::test(
    const url_pattern_input& input, const std::string_view* base_url_string) {
  // If input is a URLPatternInit
  if (std::holds_alternative<url_pattern_init>(input)) {
    if (base_url_string) {
      return tl::unexpected(errors::type_error);
    }

    std::string protocol{}, username{}, password{}, hostname{};
    std::string port{}, pathname{}, search{}, hash{};

    auto apply_result = url_pattern_init::process(
        std::get<url_pattern_init>(input), url_pattern_init::process_type::url,
        protocol, username, password, hostname, port, pathname, search, hash);

    if (!apply_result) {
      return false;
    }

    std::string_view search_view = *apply_result->search;
    if (search_view.starts_with("?")) {
      search_view.remove_prefix(1);
    }

    return test_components(*apply_result->protocol, *apply_result->username,
                           *apply_result->password, *apply_result->hostname,
                           *apply_result->port, *apply_result->pathname,
                           search_view, *apply_result->hash);
  }

  // URL string input path
  result<url_aggregator> base_url;
  if (base_url_string) {
    base_url = ada::parse<url_aggregator>(*base_url_string, nullptr);
    if (!base_url) {
      return false;
    }
  }

  auto url =
      ada::parse<url_aggregator>(std::get<std::string_view>(input),
                                 base_url.has_value() ? &*base_url : nullptr);
  if (!url) {
    return false;
  }

  // Extract components as string_view
  auto protocol_view = url->get_protocol();
  if (protocol_view.ends_with(":")) {
    protocol_view.remove_suffix(1);
  }

  auto search_view = url->get_search();
  if (search_view.starts_with("?")) {
    search_view.remove_prefix(1);
  }

  auto hash_view = url->get_hash();
  if (hash_view.starts_with("#")) {
    hash_view.remove_prefix(1);
  }

  return test_components(protocol_view, url->get_username(),
                         url->get_password(), url->get_hostname(),
                         url->get_port(), url->get_pathname(), search_view,
                         hash_view);
}

template <url_pattern_regex::regex_concept regex_provider>
result<std::optional<url_pattern_result>> url_pattern<regex_provider>::match(
    const url_pattern_input& input, const std::string_view* base_url_string) {
  std::string protocol{};
  std::string username{};
  std::string password{};
  std::string hostname{};
  std::string port{};
  std::string pathname{};
  std::string search{};
  std::string hash{};

  // Let inputs be an empty list.
  // Append input to inputs.
  std::vector inputs{input};

  // If input is a URLPatternInit then:
  if (std::holds_alternative<url_pattern_init>(input)) {
    ada_log(
        "url_pattern::match called with url_pattern_init and base_url_string=",
        base_url_string);
    // If baseURLString was given, throw a TypeError.
    if (base_url_string) {
      ada_log("failed to match because base_url_string was given");
      return tl::unexpected(errors::type_error);
    }

    // Let applyResult be the result of process a URLPatternInit given input,
    // "url", protocol, username, password, hostname, port, pathname, search,
    // and hash.
    auto apply_result = url_pattern_init::process(
        std::get<url_pattern_init>(input), url_pattern_init::process_type::url,
        protocol, username, password, hostname, port, pathname, search, hash);

    // If this throws an exception, catch it, and return null.
    if (!apply_result.has_value()) {
      ada_log("match returned std::nullopt because process threw");
      return std::nullopt;
    }

    // Set protocol to applyResult["protocol"].
    ADA_ASSERT_TRUE(apply_result->protocol.has_value());
    protocol = std::move(apply_result->protocol.value());

    // Set username to applyResult["username"].
    ADA_ASSERT_TRUE(apply_result->username.has_value());
    username = std::move(apply_result->username.value());

    // Set password to applyResult["password"].
    ADA_ASSERT_TRUE(apply_result->password.has_value());
    password = std::move(apply_result->password.value());

    // Set hostname to applyResult["hostname"].
    ADA_ASSERT_TRUE(apply_result->hostname.has_value());
    hostname = std::move(apply_result->hostname.value());

    // Set port to applyResult["port"].
    ADA_ASSERT_TRUE(apply_result->port.has_value());
    port = std::move(apply_result->port.value());

    // Set pathname to applyResult["pathname"].
    ADA_ASSERT_TRUE(apply_result->pathname.has_value());
    pathname = std::move(apply_result->pathname.value());

    // Set search to applyResult["search"].
    ADA_ASSERT_TRUE(apply_result->search.has_value());
    if (apply_result->search->starts_with("?")) {
      search = apply_result->search->substr(1);
    } else {
      search = std::move(apply_result->search.value());
    }

    // Set hash to applyResult["hash"].
    ADA_ASSERT_TRUE(apply_result->hash.has_value());
    ADA_ASSERT_TRUE(!apply_result->hash->starts_with("#"));
    hash = std::move(apply_result->hash.value());
  } else {
    ADA_ASSERT_TRUE(std::holds_alternative<std::string_view>(input));

    // Let baseURL be null.
    result<url_aggregator> base_url;

    // If baseURLString was given, then:
    if (base_url_string) {
      // Let baseURL be the result of parsing baseURLString.
      base_url = ada::parse<url_aggregator>(*base_url_string, nullptr);

      // If baseURL is failure, return null.
      if (!base_url) {
        ada_log("match returned std::nullopt because failed to parse base_url=",
                *base_url_string);
        return std::nullopt;
      }

      // Append baseURLString to inputs.
      inputs.emplace_back(*base_url_string);
    }

    url_aggregator* base_url_value =
        base_url.has_value() ? &*base_url : nullptr;

    // Set url to the result of parsing input given baseURL.
    auto url = ada::parse<url_aggregator>(std::get<std::string_view>(input),
                                          base_url_value);

    // If url is failure, return null.
    if (!url) {
      ada_log("match returned std::nullopt because url failed");
      return std::nullopt;
    }

    // Set protocol to url's scheme.
    // IMPORTANT: Not documented on the URLPattern spec, but protocol suffix ':'
    // is removed. Similar work was done on workerd:
    // https://github.com/cloudflare/workerd/blob/8620d14012513a6ce04d079e401d3becac3c67bd/src/workerd/jsg/url.c%2B%2B#L2038
    protocol = url->get_protocol().substr(0, url->get_protocol().size() - 1);
    // Set username to url's username.
    username = url->get_username();
    // Set password to url's password.
    password = url->get_password();
    // Set hostname to url's host, serialized, or the empty string if the value
    // is null.
    hostname = url->get_hostname();
    // Set port to url's port, serialized, or the empty string if the value is
    // null.
    port = url->get_port();
    // Set pathname to the result of URL path serializing url.
    pathname = url->get_pathname();
    // Set search to url's query or the empty string if the value is null.
    // IMPORTANT: Not documented on the URLPattern spec, but search prefix '?'
    // is removed. Similar work was done on workerd:
    // https://github.com/cloudflare/workerd/blob/8620d14012513a6ce04d079e401d3becac3c67bd/src/workerd/jsg/url.c%2B%2B#L2232
    if (url->has_search()) {
      auto view = url->get_search();
      search = view.starts_with("?") ? url->get_search().substr(1) : view;
    }
    // Set hash to url's fragment or the empty string if the value is null.
    // IMPORTANT: Not documented on the URLPattern spec, but hash prefix '#' is
    // removed. Similar work was done on workerd:
    // https://github.com/cloudflare/workerd/blob/8620d14012513a6ce04d079e401d3becac3c67bd/src/workerd/jsg/url.c%2B%2B#L2242
    if (url->has_hash()) {
      auto view = url->get_hash();
      hash = view.starts_with("#") ? url->get_hash().substr(1) : view;
    }
  }

  // Use fast_match which skips regex for simple patterns (EMPTY, EXACT_MATCH,
  // FULL_WILDCARD) and only falls back to regex for complex REGEXP patterns.

  // Let protocolExecResult be RegExpBuiltinExec(urlPattern's protocol
  // component's regular expression, protocol).
  auto protocol_exec_result = protocol_component.fast_match(protocol);
  if (!protocol_exec_result) {
    return std::nullopt;
  }

  // Let usernameExecResult be RegExpBuiltinExec(urlPattern's username
  // component's regular expression, username).
  auto username_exec_result = username_component.fast_match(username);
  if (!username_exec_result) {
    return std::nullopt;
  }

  // Let passwordExecResult be RegExpBuiltinExec(urlPattern's password
  // component's regular expression, password).
  auto password_exec_result = password_component.fast_match(password);
  if (!password_exec_result) {
    return std::nullopt;
  }

  // Let hostnameExecResult be RegExpBuiltinExec(urlPattern's hostname
  // component's regular expression, hostname).
  auto hostname_exec_result = hostname_component.fast_match(hostname);
  if (!hostname_exec_result) {
    return std::nullopt;
  }

  // Let portExecResult be RegExpBuiltinExec(urlPattern's port component's
  // regular expression, port).
  auto port_exec_result = port_component.fast_match(port);
  if (!port_exec_result) {
    return std::nullopt;
  }

  // Let pathnameExecResult be RegExpBuiltinExec(urlPattern's pathname
  // component's regular expression, pathname).
  auto pathname_exec_result = pathname_component.fast_match(pathname);
  if (!pathname_exec_result) {
    return std::nullopt;
  }

  // Let searchExecResult be RegExpBuiltinExec(urlPattern's search component's
  // regular expression, search).
  auto search_exec_result = search_component.fast_match(search);
  if (!search_exec_result) {
    return std::nullopt;
  }

  // Let hashExecResult be RegExpBuiltinExec(urlPattern's hash component's
  // regular expression, hash).
  auto hash_exec_result = hash_component.fast_match(hash);
  if (!hash_exec_result) {
    return std::nullopt;
  }

  // Let result be a new URLPatternResult.
  auto result = url_pattern_result{};
  // Set result["inputs"] to inputs.
  result.inputs = std::move(inputs);
  // Set result["protocol"] to the result of creating a component match result
  // given urlPattern's protocol component, protocol, and protocolExecResult.
  result.protocol = protocol_component.create_component_match_result(
      std::move(protocol), std::move(*protocol_exec_result));

  // Set result["username"] to the result of creating a component match result
  // given urlPattern's username component, username, and usernameExecResult.
  result.username = username_component.create_component_match_result(
      std::move(username), std::move(*username_exec_result));

  // Set result["password"] to the result of creating a component match result
  // given urlPattern's password component, password, and passwordExecResult.
  result.password = password_component.create_component_match_result(
      std::move(password), std::move(*password_exec_result));

  // Set result["hostname"] to the result of creating a component match result
  // given urlPattern's hostname component, hostname, and hostnameExecResult.
  result.hostname = hostname_component.create_component_match_result(
      std::move(hostname), std::move(*hostname_exec_result));

  // Set result["port"] to the result of creating a component match result given
  // urlPattern's port component, port, and portExecResult.
  result.port = port_component.create_component_match_result(
      std::move(port), std::move(*port_exec_result));

  // Set result["pathname"] to the result of creating a component match result
  // given urlPattern's pathname component, pathname, and pathnameExecResult.
  result.pathname = pathname_component.create_component_match_result(
      std::move(pathname), std::move(*pathname_exec_result));

  // Set result["search"] to the result of creating a component match result
  // given urlPattern's search component, search, and searchExecResult.
  result.search = search_component.create_component_match_result(
      std::move(search), std::move(*search_exec_result));

  // Set result["hash"] to the result of creating a component match result given
  // urlPattern's hash component, hash, and hashExecResult.
  result.hash = hash_component.create_component_match_result(
      std::move(hash), std::move(*hash_exec_result));

  return result;
}

}  // namespace ada
#endif  // ADA_INCLUDE_URL_PATTERN
#endif
/* end file include/ada/url_pattern-inl.h */
/* begin file include/ada/url_pattern_helpers-inl.h */
/**
 * @file url_pattern_helpers-inl.h
 * @brief Declaration for the URLPattern helpers.
 */
#ifndef ADA_URL_PATTERN_HELPERS_INL_H
#define ADA_URL_PATTERN_HELPERS_INL_H

#include <optional>
#include <string_view>


#if ADA_INCLUDE_URL_PATTERN
namespace ada::url_pattern_helpers {
#if defined(ADA_TESTING) || defined(ADA_LOGGING)
inline std::string to_string(token_type type) {
  switch (type) {
    case token_type::INVALID_CHAR:
      return "INVALID_CHAR";
    case token_type::OPEN:
      return "OPEN";
    case token_type::CLOSE:
      return "CLOSE";
    case token_type::REGEXP:
      return "REGEXP";
    case token_type::NAME:
      return "NAME";
    case token_type::CHAR:
      return "CHAR";
    case token_type::ESCAPED_CHAR:
      return "ESCAPED_CHAR";
    case token_type::OTHER_MODIFIER:
      return "OTHER_MODIFIER";
    case token_type::ASTERISK:
      return "ASTERISK";
    case token_type::END:
      return "END";
    default:
      ada::unreachable();
  }
}
#endif  // defined(ADA_TESTING) || defined(ADA_LOGGING)

template <url_pattern_regex::regex_concept regex_provider>
constexpr void constructor_string_parser<regex_provider>::rewind() {
  // Set parser's token index to parser's component start.
  token_index = component_start;
  // Set parser's token increment to 0.
  token_increment = 0;
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_hash_prefix() {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index and "#".
  return is_non_special_pattern_char(token_index, '#');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_search_prefix() {
  // If result of running is a non-special pattern char given parser, parser's
  // token index and "?" is true, then return true.
  if (is_non_special_pattern_char(token_index, '?')) {
    return true;
  }

  // If parser's token list[parser's token index]'s value is not "?", then
  // return false.
  if (token_list[token_index].value != "?") {
    return false;
  }

  // If previous index is less than 0, then return true.
  if (token_index == 0) return true;
  // Let previous index be parser's token index - 1.
  auto previous_index = token_index - 1;
  // Let previous token be the result of running get a safe token given parser
  // and previous index.
  auto previous_token = get_safe_token(previous_index);
  ADA_ASSERT_TRUE(previous_token);
  // If any of the following are true, then return false:
  // - previous token's type is "name".
  // - previous token's type is "regexp".
  // - previous token's type is "close".
  // - previous token's type is "asterisk".
  return !(previous_token->type == token_type::NAME ||
           previous_token->type == token_type::REGEXP ||
           previous_token->type == token_type::CLOSE ||
           previous_token->type == token_type::ASTERISK);
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool
constructor_string_parser<regex_provider>::is_non_special_pattern_char(
    size_t index, uint32_t value) const {
  // Let token be the result of running get a safe token given parser and index.
  auto token = get_safe_token(index);
  ADA_ASSERT_TRUE(token);

  // If token's value is not value, then return false.
  // TODO: Remove this once we make sure get_safe_token returns a non-empty
  // string.
  if (!token->value.empty() &&
      static_cast<uint32_t>(token->value[0]) != value) {
    return false;
  }

  // If any of the following are true:
  // - token's type is "char";
  // - token's type is "escaped-char"; or
  // - token's type is "invalid-char",
  // - then return true.
  return token->type == token_type::CHAR ||
         token->type == token_type::ESCAPED_CHAR ||
         token->type == token_type::INVALID_CHAR;
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr const token*
constructor_string_parser<regex_provider>::get_safe_token(size_t index) const {
  // If index is less than parser's token list's size, then return parser's
  // token list[index].
  if (index < token_list.size()) [[likely]] {
    return &token_list[index];
  }

  // Assert: parser's token list's size is greater than or equal to 1.
  ADA_ASSERT_TRUE(!token_list.empty());

  // Let token be parser's token list[last index].
  // Assert: token's type is "end".
  ADA_ASSERT_TRUE(token_list.back().type == token_type::END);

  // Return token.
  return &token_list.back();
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_group_open()
    const {
  // If parser's token list[parser's token index]'s type is "open", then return
  // true.
  return token_list[token_index].type == token_type::OPEN;
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_group_close()
    const {
  // If parser's token list[parser's token index]'s type is "close", then return
  // true.
  return token_list[token_index].type == token_type::CLOSE;
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool
constructor_string_parser<regex_provider>::next_is_authority_slashes() const {
  // If the result of running is a non-special pattern char given parser,
  // parser's token index + 1, and "/" is false, then return false.
  if (!is_non_special_pattern_char(token_index + 1, '/')) {
    return false;
  }
  // If the result of running is a non-special pattern char given parser,
  // parser's token index + 2, and "/" is false, then return false.
  if (!is_non_special_pattern_char(token_index + 2, '/')) {
    return false;
  }
  return true;
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_protocol_suffix()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and ":".
  return is_non_special_pattern_char(token_index, ':');
}

template <url_pattern_regex::regex_concept regex_provider>
void constructor_string_parser<regex_provider>::change_state(State new_state,
                                                             size_t skip) {
  // If parser's state is not "init", not "authority", and not "done", then set
  // parser's result[parser's state] to the result of running make a component
  // string given parser.
  if (state != State::INIT && state != State::AUTHORITY &&
      state != State::DONE) {
    auto value = make_component_string();
    // TODO: Simplify this.
    switch (state) {
      case State::PROTOCOL: {
        result.protocol = value;
        break;
      }
      case State::USERNAME: {
        result.username = value;
        break;
      }
      case State::PASSWORD: {
        result.password = value;
        break;
      }
      case State::HOSTNAME: {
        result.hostname = value;
        break;
      }
      case State::PORT: {
        result.port = value;
        break;
      }
      case State::PATHNAME: {
        result.pathname = value;
        break;
      }
      case State::SEARCH: {
        result.search = value;
        break;
      }
      case State::HASH: {
        result.hash = value;
        break;
      }
      default:
        ada::unreachable();
    }
  }

  // If parser's state is not "init" and new state is not "done", then:
  if (state != State::INIT && new_state != State::DONE) {
    // If parser's state is "protocol", "authority", "username", or "password";
    // new state is "port", "pathname", "search", or "hash"; and parser's
    // result["hostname"] does not exist, then set parser's result["hostname"]
    // to the empty string.
    if ((state == State::PROTOCOL || state == State::AUTHORITY ||
         state == State::USERNAME || state == State::PASSWORD) &&
        (new_state == State::PORT || new_state == State::PATHNAME ||
         new_state == State::SEARCH || new_state == State::HASH) &&
        !result.hostname)
      result.hostname = "";
  }

  // If parser's state is "protocol", "authority", "username", "password",
  // "hostname", or "port"; new state is "search" or "hash"; and parser's
  // result["pathname"] does not exist, then:
  if ((state == State::PROTOCOL || state == State::AUTHORITY ||
       state == State::USERNAME || state == State::PASSWORD ||
       state == State::HOSTNAME || state == State::PORT) &&
      (new_state == State::SEARCH || new_state == State::HASH) &&
      !result.pathname) {
    if (protocol_matches_a_special_scheme_flag) {
      result.pathname = "/";
    } else {
      // Otherwise, set parser's result["pathname"] to the empty string.
      result.pathname = "";
    }
  }

  // If parser's state is "protocol", "authority", "username", "password",
  // "hostname", "port", or "pathname"; new state is "hash"; and parser's
  // result["search"] does not exist, then set parser's result["search"] to
  // the empty string.
  if ((state == State::PROTOCOL || state == State::AUTHORITY ||
       state == State::USERNAME || state == State::PASSWORD ||
       state == State::HOSTNAME || state == State::PORT ||
       state == State::PATHNAME) &&
      new_state == State::HASH && !result.search) {
    result.search = "";
  }

  // Set parser's state to new state.
  state = new_state;
  // Increment parser's token index by skip.
  token_index += skip;
  // Set parser's component start to parser's token index.
  component_start = token_index;
  // Set parser's token increment to 0.
  token_increment = 0;
}

template <url_pattern_regex::regex_concept regex_provider>
std::string constructor_string_parser<regex_provider>::make_component_string() {
  // Assert: parser's token index is less than parser's token list's size.
  ADA_ASSERT_TRUE(token_index < token_list.size());

  // Let token be parser's token list[parser's token index].
  // Let end index be token's index.
  const auto end_index = token_list[token_index].index;
  // Let component start token be the result of running get a safe token given
  // parser and parser's component start.
  const auto component_start_token = get_safe_token(component_start);
  ADA_ASSERT_TRUE(component_start_token);
  // Let component start input index be component start token's index.
  const auto component_start_input_index = component_start_token->index;
  // Return the code point substring from component start input index to end
  // index within parser's input.
  return std::string(input.substr(component_start_input_index,
                                  end_index - component_start_input_index));
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool
constructor_string_parser<regex_provider>::is_an_identity_terminator() const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and "@".
  return is_non_special_pattern_char(token_index, '@');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_pathname_start()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and "/".
  return is_non_special_pattern_char(token_index, '/');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_password_prefix()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and ":".
  return is_non_special_pattern_char(token_index, ':');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_an_ipv6_open()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and "[".
  return is_non_special_pattern_char(token_index, '[');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_an_ipv6_close()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and "]".
  return is_non_special_pattern_char(token_index, ']');
}

template <url_pattern_regex::regex_concept regex_provider>
constexpr bool constructor_string_parser<regex_provider>::is_port_prefix()
    const {
  // Return the result of running is a non-special pattern char given parser,
  // parser's token index, and ":".
  return is_non_special_pattern_char(token_index, ':');
}

constexpr void Tokenizer::get_next_code_point() {
  ada_log("Tokenizer::get_next_code_point called with index=", next_index);
  ADA_ASSERT_TRUE(next_index < input.size());
  // Decode the next UTF-8 code point. If malformed or truncated, mark it as
  // invalid, return the offending byte as the code point, and advance by one
  // to guarantee forward progress.
  invalid_code_point = false;
  code_point = 0;
  size_t number_bytes = 0;
  const size_t initial_index = next_index;
  unsigned char first_byte = input[next_index];

  if ((first_byte & 0x80) == 0) {
    // 1-byte character (ASCII)
    next_index++;
    code_point = first_byte;
    ada_log("Tokenizer::get_next_code_point returning ASCII code point=",
            uint32_t(code_point));
    ada_log("Tokenizer::get_next_code_point next_index =", next_index,
            " input.size()=", input.size());
    return;
  }
  ada_log("Tokenizer::get_next_code_point read first byte=",
          uint32_t(first_byte));
  if ((first_byte & 0xE0) == 0xC0) {
    code_point = first_byte & 0x1F;
    number_bytes = 2;
    ada_log("Tokenizer::get_next_code_point two bytes");
  } else if ((first_byte & 0xF0) == 0xE0) {
    code_point = first_byte & 0x0F;
    number_bytes = 3;
    ada_log("Tokenizer::get_next_code_point three bytes");
  } else if ((first_byte & 0xF8) == 0xF0) {
    code_point = first_byte & 0x07;
    number_bytes = 4;
    ada_log("Tokenizer::get_next_code_point four bytes");
  }

  // Invalid leading bytes that still match a multi-byte prefix.
  if ((number_bytes == 2 && first_byte < 0xC2) ||
      (number_bytes == 4 && first_byte > 0xF4)) {
    invalid_code_point = true;
    code_point = first_byte;
    next_index = initial_index + 1;
    return;
  }

  // Invalid leading byte (e.g., continuation byte outside a sequence).
  if (number_bytes == 0) {
    invalid_code_point = true;
    code_point = first_byte;
    next_index = initial_index + 1;
    return;
  }

  // Truncated UTF-8 sequence.
  if (number_bytes + next_index > input.size()) {
    invalid_code_point = true;
    code_point = first_byte;
    next_index = initial_index + 1;
    return;
  }

  for (size_t i = 1 + next_index; i < number_bytes + next_index; ++i) {
    unsigned char byte = input[i];
    if ((byte & 0xC0) != 0x80) {
      invalid_code_point = true;
      code_point = first_byte;
      next_index = initial_index + 1;
      return;
    }
    ada_log("Tokenizer::get_next_code_point read byte=", uint32_t(byte));
    code_point = (code_point << 6) | (byte & 0x3F);
  }
  ada_log("Tokenizer::get_next_code_point returning non-ASCII code point=",
          uint32_t(code_point));
  ada_log("Tokenizer::get_next_code_point next_index =", next_index,
          " input.size()=", input.size());
  next_index += number_bytes;
}

constexpr void Tokenizer::seek_and_get_next_code_point(size_t new_index) {
  ada_log("Tokenizer::seek_and_get_next_code_point called with new_index=",
          new_index);
  // Set tokenizer's next index to index.
  next_index = new_index;
  // Run get the next code point given tokenizer.
  get_next_code_point();
}

inline void Tokenizer::add_token(token_type type, size_t next_position,
                                 size_t value_position, size_t value_length) {
  ada_log("Tokenizer::add_token called with type=", to_string(type),
          " next_position=", next_position, " value_position=", value_position);
  ADA_ASSERT_TRUE(next_position >= value_position);

  // Let token be a new token.
  // Set token's type to type.
  // Set token's index to tokenizer's index.
  // Set token's value to the code point substring from value position with
  // length value length within tokenizer's input.
  // Append token to the back of tokenizer's token list.
  token_list.emplace_back(type, index,
                          input.substr(value_position, value_length));
  // Set tokenizer's index to next position.
  index = next_position;
}

inline void Tokenizer::add_token_with_default_length(token_type type,
                                                     size_t next_position,
                                                     size_t value_position) {
  // Let computed length be next position - value position.
  auto computed_length = next_position - value_position;
  // Run add a token given tokenizer, type, next position, value position, and
  // computed length.
  add_token(type, next_position, value_position, computed_length);
}

inline void Tokenizer::add_token_with_defaults(token_type type) {
  ada_log("Tokenizer::add_token_with_defaults called with type=",
          to_string(type));
  // Run add a token with default length given tokenizer, type, tokenizer's next
  // index, and tokenizer's index.
  add_token_with_default_length(type, next_index, index);
}

inline ada_warn_unused std::optional<errors>
Tokenizer::process_tokenizing_error(size_t next_position,
                                    size_t value_position) {
  // If tokenizer's policy is "strict", then throw a TypeError.
  if (policy == token_policy::strict) {
    ada_log("process_tokenizing_error failed with next_position=",
            next_position, " value_position=", value_position);
    return errors::type_error;
  }
  // Assert: tokenizer's policy is "lenient".
  ADA_ASSERT_TRUE(policy == token_policy::lenient);
  // Run add a token with default length given tokenizer, "invalid-char", next
  // position, and value position.
  add_token_with_default_length(token_type::INVALID_CHAR, next_position,
                                value_position);
  return std::nullopt;
}

template <url_pattern_encoding_callback F>
token* url_pattern_parser<F>::try_consume_modifier_token() {
  // Let token be the result of running try to consume a token given parser and
  // "other-modifier".
  auto token = try_consume_token(token_type::OTHER_MODIFIER);
  // If token is not null, then return token.
  if (token) return token;
  // Set token to the result of running try to consume a token given parser and
  // "asterisk".
  // Return token.
  return try_consume_token(token_type::ASTERISK);
}

template <url_pattern_encoding_callback F>
token* url_pattern_parser<F>::try_consume_regexp_or_wildcard_token(
    const token* name_token) {
  // Let token be the result of running try to consume a token given parser and
  // "regexp".
  auto token = try_consume_token(token_type::REGEXP);
  // If name token is null and token is null, then set token to the result of
  // running try to consume a token given parser and "asterisk".
  if (!name_token && !token) {
    token = try_consume_token(token_type::ASTERISK);
  }
  // Return token.
  return token;
}

template <url_pattern_encoding_callback F>
token* url_pattern_parser<F>::try_consume_token(token_type type) {
  ada_log("url_pattern_parser::try_consume_token called with type=",
          to_string(type));
  // Assert: parser's index is less than parser's token list size.
  ADA_ASSERT_TRUE(index < tokens.size());
  // Let next token be parser's token list[parser's index].
  auto& next_token = tokens[index];
  // If next token's type is not type return null.
  if (next_token.type != type) return nullptr;
  // Increase parser's index by 1.
  index++;
  // Return next token.
  return &next_token;
}

template <url_pattern_encoding_callback F>
std::string url_pattern_parser<F>::consume_text() {
  // Let result be the empty string.
  std::string result{};
  // While true:
  while (true) {
    // Let token be the result of running try to consume a token given parser
    // and "char".
    auto token = try_consume_token(token_type::CHAR);
    // If token is null, then set token to the result of running try to consume
    // a token given parser and "escaped-char".
    if (!token) token = try_consume_token(token_type::ESCAPED_CHAR);
    // If token is null, then break.
    if (!token) break;
    // Append token's value to the end of result.
    result.append(token->value);
  }
  // Return result.
  return result;
}

template <url_pattern_encoding_callback F>
bool url_pattern_parser<F>::consume_required_token(token_type type) {
  ada_log("url_pattern_parser::consume_required_token called with type=",
          to_string(type));
  // Let result be the result of running try to consume a token given parser and
  // type.
  return try_consume_token(type) != nullptr;
}

template <url_pattern_encoding_callback F>
std::optional<errors>
url_pattern_parser<F>::maybe_add_part_from_the_pending_fixed_value() {
  // If parser's pending fixed value is the empty string, then return.
  if (pending_fixed_value.empty()) {
    ada_log("pending_fixed_value is empty");
    return std::nullopt;
  }
  // Let encoded value be the result of running parser's encoding callback given
  // parser's pending fixed value.
  auto encoded_value = encoding_callback(pending_fixed_value);
  if (!encoded_value) {
    ada_log("failed to encode pending_fixed_value: ", pending_fixed_value);
    return encoded_value.error();
  }
  // Set parser's pending fixed value to the empty string.
  pending_fixed_value.clear();
  // Let part be a new part whose type is "fixed-text", value is encoded value,
  // and modifier is "none".
  // Append part to parser's part list.
  parts.emplace_back(url_pattern_part_type::FIXED_TEXT,
                     std::move(*encoded_value),
                     url_pattern_part_modifier::none);
  return std::nullopt;
}

template <url_pattern_encoding_callback F>
std::optional<errors> url_pattern_parser<F>::add_part(
    std::string_view prefix, token* name_token, token* regexp_or_wildcard_token,
    std::string_view suffix, token* modifier_token) {
  // Let modifier be "none".
  auto modifier = url_pattern_part_modifier::none;
  // If modifier token is not null:
  if (modifier_token) {
    // If modifier token's value is "?" then set modifier to "optional".
    if (modifier_token->value == "?") {
      modifier = url_pattern_part_modifier::optional;
    } else if (modifier_token->value == "*") {
      // Otherwise if modifier token's value is "*" then set modifier to
      // "zero-or-more".
      modifier = url_pattern_part_modifier::zero_or_more;
    } else if (modifier_token->value == "+") {
      // Otherwise if modifier token's value is "+" then set modifier to
      // "one-or-more".
      modifier = url_pattern_part_modifier::one_or_more;
    }
  }
  // If name token is null and regexp or wildcard token is null and modifier
  // is "none":
  if (!name_token && !regexp_or_wildcard_token &&
      modifier == url_pattern_part_modifier::none) {
    // Append prefix to the end of parser's pending fixed value.
    pending_fixed_value.append(prefix);
    return std::nullopt;
  }
  // Run maybe add a part from the pending fixed value given parser.
  if (auto error = maybe_add_part_from_the_pending_fixed_value()) {
    return *error;
  }
  // If name token is null and regexp or wildcard token is null:
  if (!name_token && !regexp_or_wildcard_token) {
    // Assert: suffix is the empty string.
    ADA_ASSERT_TRUE(suffix.empty());
    // If prefix is the empty string, then return.
    if (prefix.empty()) return std::nullopt;
    // Let encoded value be the result of running parser's encoding callback
    // given prefix.
    auto encoded_value = encoding_callback(prefix);
    if (!encoded_value) {
      return encoded_value.error();
    }
    // Let part be a new part whose type is "fixed-text", value is encoded
    // value, and modifier is modifier.
    // Append part to parser's part list.
    parts.emplace_back(url_pattern_part_type::FIXED_TEXT,
                       std::move(*encoded_value), modifier);
    return std::nullopt;
  }
  // Let regexp value be the empty string.
  std::string regexp_value{};
  // If regexp or wildcard token is null, then set regexp value to parser's
  // segment wildcard regexp.
  if (!regexp_or_wildcard_token) {
    regexp_value = segment_wildcard_regexp;
  } else if (regexp_or_wildcard_token->type == token_type::ASTERISK) {
    // Otherwise if regexp or wildcard token's type is "asterisk", then set
    // regexp value to the full wildcard regexp value.
    regexp_value = ".*";
  } else {
    // Otherwise set regexp value to regexp or wildcard token's value.
    regexp_value = regexp_or_wildcard_token->value;
  }
  // Let type be "regexp".
  auto type = url_pattern_part_type::REGEXP;
  // If regexp value is parser's segment wildcard regexp:
  if (regexp_value == segment_wildcard_regexp) {
    // Set type to "segment-wildcard".
    type = url_pattern_part_type::SEGMENT_WILDCARD;
    // Set regexp value to the empty string.
    regexp_value.clear();
  } else if (regexp_value == ".*") {
    // Otherwise if regexp value is the full wildcard regexp value:
    // Set type to "full-wildcard".
    type = url_pattern_part_type::FULL_WILDCARD;
    // Set regexp value to the empty string.
    regexp_value.clear();
  }
  // Let name be the empty string.
  std::string name{};
  // If name token is not null, then set name to name token's value.
  if (name_token) {
    name = name_token->value;
  } else if (regexp_or_wildcard_token != nullptr) {
    // Otherwise if regexp or wildcard token is not null:
    // Set name to parser's next numeric name, serialized.
    name = std::to_string(next_numeric_name);
    // Increment parser's next numeric name by 1.
    next_numeric_name++;
  }
  // If the result of running is a duplicate name given parser and name is
  // true, then throw a TypeError.
  if (std::ranges::any_of(
          parts, [&name](const auto& part) { return part.name == name; })) {
    return errors::type_error;
  }
  // Let encoded prefix be the result of running parser's encoding callback
  // given prefix.
  auto encoded_prefix = encoding_callback(prefix);
  if (!encoded_prefix) return encoded_prefix.error();
  // Let encoded suffix be the result of running parser's encoding callback
  // given suffix.
  auto encoded_suffix = encoding_callback(suffix);
  if (!encoded_suffix) return encoded_suffix.error();
  // Let part be a new part whose type is type, value is regexp value,
  // modifier is modifier, name is name, prefix is encoded prefix, and suffix
  // is encoded suffix.
  // Append part to parser's part list.
  parts.emplace_back(type, std::move(regexp_value), modifier, std::move(name),
                     std::move(*encoded_prefix), std::move(*encoded_suffix));
  return std::nullopt;
}

template <url_pattern_encoding_callback F>
tl::expected<std::vector<url_pattern_part>, errors> parse_pattern_string(
    std::string_view input, url_pattern_compile_component_options& options,
    F& encoding_callback) {
  ada_log("parse_pattern_string input=", input);
  // Let parser be a new pattern parser whose encoding callback is encoding
  // callback and segment wildcard regexp is the result of running generate a
  // segment wildcard regexp given options.
  auto parser = url_pattern_parser<F>(
      encoding_callback, generate_segment_wildcard_regexp(options));
  // Set parser's token list to the result of running tokenize given input and
  // "strict".
  auto tokenize_result = tokenize(input, token_policy::strict);
  if (!tokenize_result) {
    ada_log("parse_pattern_string tokenize failed");
    return tl::unexpected(tokenize_result.error());
  }
  parser.tokens = std::move(*tokenize_result);

  // While parser's index is less than parser's token list's size:
  while (parser.can_continue()) {
    // Let char token be the result of running try to consume a token given
    // parser and "char".
    auto char_token = parser.try_consume_token(token_type::CHAR);
    // Let name token be the result of running try to consume a token given
    // parser and "name".
    auto name_token = parser.try_consume_token(token_type::NAME);
    // Let regexp or wildcard token be the result of running try to consume a
    // regexp or wildcard token given parser and name token.
    auto regexp_or_wildcard_token =
        parser.try_consume_regexp_or_wildcard_token(name_token);
    // If name token is not null or regexp or wildcard token is not null:
    if (name_token || regexp_or_wildcard_token) {
      // Let prefix be the empty string.
      std::string prefix{};
      // If char token is not null then set prefix to char token's value.
      if (char_token) prefix = char_token->value;
      // If prefix is not the empty string and not options's prefix code point:
      if (!prefix.empty() && prefix != options.get_prefix()) {
        // Append prefix to the end of parser's pending fixed value.
        parser.pending_fixed_value.append(prefix);
        // Set prefix to the empty string.
        prefix.clear();
      }
      // Run maybe add a part from the pending fixed value given parser.
      if (auto error = parser.maybe_add_part_from_the_pending_fixed_value()) {
        ada_log("maybe_add_part_from_the_pending_fixed_value failed");
        return tl::unexpected(*error);
      }
      // Let modifier token be the result of running try to consume a modifier
      // token given parser.
      auto modifier_token = parser.try_consume_modifier_token();
      // Run add a part given parser, prefix, name token, regexp or wildcard
      // token, the empty string, and modifier token.
      if (auto error =
              parser.add_part(prefix, name_token, regexp_or_wildcard_token, "",
                              modifier_token)) {
        ada_log("parser.add_part failed");
        return tl::unexpected(*error);
      }
      // Continue.
      continue;
    }

    // Let fixed token be char token.
    auto fixed_token = char_token;
    // If fixed token is null, then set fixed token to the result of running try
    // to consume a token given parser and "escaped-char".
    if (!fixed_token)
      fixed_token = parser.try_consume_token(token_type::ESCAPED_CHAR);
    // If fixed token is not null:
    if (fixed_token) {
      // Append fixed token's value to parser's pending fixed value.
      parser.pending_fixed_value.append(fixed_token->value);
      // Continue.
      continue;
    }
    // Let open token be the result of running try to consume a token given
    // parser and "open".
    auto open_token = parser.try_consume_token(token_type::OPEN);
    // If open token is not null:
    if (open_token) {
      // Set prefix be the result of running consume text given parser.
      auto prefix_ = parser.consume_text();
      // Set name token to the result of running try to consume a token given
      // parser and "name".
      name_token = parser.try_consume_token(token_type::NAME);
      // Set regexp or wildcard token to the result of running try to consume a
      // regexp or wildcard token given parser and name token.
      regexp_or_wildcard_token =
          parser.try_consume_regexp_or_wildcard_token(name_token);
      // Let suffix be the result of running consume text given parser.
      auto suffix_ = parser.consume_text();
      // Run consume a required token given parser and "close".
      if (!parser.consume_required_token(token_type::CLOSE)) {
        ada_log("parser.consume_required_token failed");
        return tl::unexpected(errors::type_error);
      }
      // Set modifier token to the result of running try to consume a modifier
      // token given parser.
      auto modifier_token = parser.try_consume_modifier_token();
      // Run add a part given parser, prefix, name token, regexp or wildcard
      // token, suffix, and modifier token.
      if (auto error =
              parser.add_part(prefix_, name_token, regexp_or_wildcard_token,
                              suffix_, modifier_token)) {
        return tl::unexpected(*error);
      }
      // Continue.
      continue;
    }
    // Run maybe add a part from the pending fixed value given parser.
    if (auto error = parser.maybe_add_part_from_the_pending_fixed_value()) {
      ada_log("maybe_add_part_from_the_pending_fixed_value failed on line 992");
      return tl::unexpected(*error);
    }
    // Run consume a required token given parser and "end".
    if (!parser.consume_required_token(token_type::END)) {
      return tl::unexpected(errors::type_error);
    }
  }
  ada_log("parser.parts size is: ", parser.parts.size());
  // Return parser's part list.
  return parser.parts;
}

template <url_pattern_regex::regex_concept regex_provider>
bool protocol_component_matches_special_scheme(
    url_pattern_component<regex_provider>& component) {
  // Optimization: Use fast_test for simple patterns to avoid regex overhead
  switch (component.type) {
    case url_pattern_component_type::EMPTY:
      // Empty pattern can't match any special scheme
      return false;
    case url_pattern_component_type::EXACT_MATCH:
      // Direct string comparison for exact match patterns
      return component.exact_match_value == "http" ||
             component.exact_match_value == "https" ||
             component.exact_match_value == "ws" ||
             component.exact_match_value == "wss" ||
             component.exact_match_value == "ftp" ||
             component.exact_match_value == "file";
    case url_pattern_component_type::FULL_WILDCARD:
      // Full wildcard matches everything including special schemes
      return true;
    case url_pattern_component_type::REGEXP:
      // Fall back to regex matching for complex patterns
      auto& regex = component.regexp;
      return regex_provider::regex_match("http", regex) ||
             regex_provider::regex_match("https", regex) ||
             regex_provider::regex_match("ws", regex) ||
             regex_provider::regex_match("wss", regex) ||
             regex_provider::regex_match("ftp", regex) ||
             regex_provider::regex_match("file", regex);
  }
  ada::unreachable();
}

template <url_pattern_regex::regex_concept regex_provider>
inline std::optional<errors> constructor_string_parser<
    regex_provider>::compute_protocol_matches_special_scheme_flag() {
  ada_log(
      "constructor_string_parser::compute_protocol_matches_special_scheme_"
      "flag");
  // Let protocol string be the result of running make a component string given
  // parser.
  auto protocol_string = make_component_string();
  // Let protocol component be the result of compiling a component given
  // protocol string, canonicalize a protocol, and default options.
  auto protocol_component = url_pattern_component<regex_provider>::compile(
      protocol_string, canonicalize_protocol,
      url_pattern_compile_component_options::DEFAULT);
  if (!protocol_component) {
    ada_log("url_pattern_component::compile failed for protocol_string ",
            protocol_string);
    return protocol_component.error();
  }
  // If the result of running protocol component matches a special scheme given
  // protocol component is true, then set parser's protocol matches a special
  // scheme flag to true.
  if (protocol_component_matches_special_scheme(*protocol_component)) {
    protocol_matches_a_special_scheme_flag = true;
  }
  return std::nullopt;
}

template <url_pattern_regex::regex_concept regex_provider>
tl::expected<url_pattern_init, errors>
constructor_string_parser<regex_provider>::parse(std::string_view input) {
  ada_log("constructor_string_parser::parse input=", input);
  // Let parser be a new constructor string parser whose input is input and
  // token list is the result of running tokenize given input and "lenient".
  auto token_list = tokenize(input, token_policy::lenient);
  if (!token_list) {
    return tl::unexpected(token_list.error());
  }
  auto parser = constructor_string_parser(input, std::move(*token_list));

  // While parser's token index is less than parser's token list size:
  while (parser.token_index < parser.token_list.size()) {
    // Set parser's token increment to 1.
    parser.token_increment = 1;

    // If parser's token list[parser's token index]'s type is "end" then:
    if (parser.token_list[parser.token_index].type == token_type::END) {
      // If parser's state is "init":
      if (parser.state == State::INIT) {
        // Run rewind given parser.
        parser.rewind();
        // If the result of running is a hash prefix given parser is true, then
        // run change state given parser, "hash" and 1.
        if (parser.is_hash_prefix()) {
          parser.change_state(State::HASH, 1);
        } else if (parser.is_search_prefix()) {
          // Otherwise if the result of running is a search prefix given parser
          // is true: Run change state given parser, "search" and 1.
          parser.change_state(State::SEARCH, 1);
        } else {
          // Run change state given parser, "pathname" and 0.
          parser.change_state(State::PATHNAME, 0);
        }
        // Increment parser's token index by parser's token increment.
        parser.token_index += parser.token_increment;
        // Continue.
        continue;
      }

      if (parser.state == State::AUTHORITY) {
        // If parser's state is "authority":
        // Run rewind and set state given parser, and "hostname".
        parser.rewind();
        parser.change_state(State::HOSTNAME, 0);
        // Increment parser's token index by parser's token increment.
        parser.token_index += parser.token_increment;
        // Continue.
        continue;
      }

      // Run change state given parser, "done" and 0.
      parser.change_state(State::DONE, 0);
      // Break.
      break;
    }

    // If the result of running is a group open given parser is true:
    if (parser.is_group_open()) {
      // Increment parser's group depth by 1.
      parser.group_depth += 1;
      // Increment parser's token index by parser's token increment.
      parser.token_index += parser.token_increment;
      // Continue.
      continue;
    }

    // If parser's group depth is greater than 0:
    if (parser.group_depth > 0) {
      // If the result of running is a group close given parser is true, then
      // decrement parser's group depth by 1.
      if (parser.is_group_close()) {
        parser.group_depth -= 1;
      } else {
        // Increment parser's token index by parser's token increment.
        parser.token_index += parser.token_increment;
        continue;
      }
    }

    // Switch on parser's state and run the associated steps:
    switch (parser.state) {
      case State::INIT: {
        // If the result of running is a protocol suffix given parser is true:
        if (parser.is_protocol_suffix()) {
          // Run rewind and set state given parser and "protocol".
          parser.rewind();
          parser.change_state(State::PROTOCOL, 0);
        }
        break;
      }
      case State::PROTOCOL: {
        // If the result of running is a protocol suffix given parser is true:
        if (parser.is_protocol_suffix()) {
          // Run compute protocol matches a special scheme flag given parser.
          if (const auto error =
                  parser.compute_protocol_matches_special_scheme_flag()) {
            ada_log("compute_protocol_matches_special_scheme_flag failed");
            return tl::unexpected(*error);
          }
          // Let next state be "pathname".
          auto next_state = State::PATHNAME;
          // Let skip be 1.
          auto skip = 1;
          // If the result of running next is authority slashes given parser is
          // true:
          if (parser.next_is_authority_slashes()) {
            // Set next state to "authority".
            next_state = State::AUTHORITY;
            // Set skip to 3.
            skip = 3;
          } else if (parser.protocol_matches_a_special_scheme_flag) {
            // Otherwise if parser's protocol matches a special scheme flag is
            // true, then set next state to "authority".
            next_state = State::AUTHORITY;
          }

          // Run change state given parser, next state, and skip.
          parser.change_state(next_state, skip);
        }
        break;
      }
      case State::AUTHORITY: {
        // If the result of running is an identity terminator given parser is
        // true, then run rewind and set state given parser and "username".
        if (parser.is_an_identity_terminator()) {
          parser.rewind();
          parser.change_state(State::USERNAME, 0);
        } else if (parser.is_pathname_start() || parser.is_search_prefix() ||
                   parser.is_hash_prefix()) {
          // Otherwise if any of the following are true:
          // - the result of running is a pathname start given parser;
          // - the result of running is a search prefix given parser; or
          // - the result of running is a hash prefix given parser,
          // then run rewind and set state given parser and "hostname".
          parser.rewind();
          parser.change_state(State::HOSTNAME, 0);
        }
        break;
      }
      case State::USERNAME: {
        // If the result of running is a password prefix given parser is true,
        // then run change state given parser, "password", and 1.
        if (parser.is_password_prefix()) {
          parser.change_state(State::PASSWORD, 1);
        } else if (parser.is_an_identity_terminator()) {
          // Otherwise if the result of running is an identity terminator given
          // parser is true, then run change state given parser, "hostname",
          // and 1.
          parser.change_state(State::HOSTNAME, 1);
        }
        break;
      }
      case State::PASSWORD: {
        // If the result of running is an identity terminator given parser is
        // true, then run change state given parser, "hostname", and 1.
        if (parser.is_an_identity_terminator()) {
          parser.change_state(State::HOSTNAME, 1);
        }
        break;
      }
      case State::HOSTNAME: {
        // If the result of running is an IPv6 open given parser is true, then
        // increment parser's hostname IPv6 bracket depth by 1.
        if (parser.is_an_ipv6_open()) {
          parser.hostname_ipv6_bracket_depth += 1;
        } else if (parser.is_an_ipv6_close()) {
          // Otherwise if the result of running is an IPv6 close given parser is
          // true, then decrement parser's hostname IPv6 bracket depth by 1.
          parser.hostname_ipv6_bracket_depth -= 1;
        } else if (parser.is_port_prefix() &&
                   parser.hostname_ipv6_bracket_depth == 0) {
          // Otherwise if the result of running is a port prefix given parser is
          // true and parser's hostname IPv6 bracket depth is zero, then run
          // change state given parser, "port", and 1.
          parser.change_state(State::PORT, 1);
        } else if (parser.is_pathname_start()) {
          // Otherwise if the result of running is a pathname start given parser
          // is true, then run change state given parser, "pathname", and 0.
          parser.change_state(State::PATHNAME, 0);
        } else if (parser.is_search_prefix()) {
          // Otherwise if the result of running is a search prefix given parser
          // is true, then run change state given parser, "search", and 1.
          parser.change_state(State::SEARCH, 1);
        } else if (parser.is_hash_prefix()) {
          // Otherwise if the result of running is a hash prefix given parser is
          // true, then run change state given parser, "hash", and 1.
          parser.change_state(State::HASH, 1);
        }

        break;
      }
      case State::PORT: {
        // If the result of running is a pathname start given parser is true,
        // then run change state given parser, "pathname", and 0.
        if (parser.is_pathname_start()) {
          parser.change_state(State::PATHNAME, 0);
        } else if (parser.is_search_prefix()) {
          // Otherwise if the result of running is a search prefix given parser
          // is true, then run change state given parser, "search", and 1.
          parser.change_state(State::SEARCH, 1);
        } else if (parser.is_hash_prefix()) {
          // Otherwise if the result of running is a hash prefix given parser is
          // true, then run change state given parser, "hash", and 1.
          parser.change_state(State::HASH, 1);
        }
        break;
      }
      case State::PATHNAME: {
        // If the result of running is a search prefix given parser is true,
        // then run change state given parser, "search", and 1.
        if (parser.is_search_prefix()) {
          parser.change_state(State::SEARCH, 1);
        } else if (parser.is_hash_prefix()) {
          // Otherwise if the result of running is a hash prefix given parser is
          // true, then run change state given parser, "hash", and 1.
          parser.change_state(State::HASH, 1);
        }
        break;
      }
      case State::SEARCH: {
        // If the result of running is a hash prefix given parser is true, then
        // run change state given parser, "hash", and 1.
        if (parser.is_hash_prefix()) {
          parser.change_state(State::HASH, 1);
        }
        break;
      }
      case State::HASH: {
        // Do nothing
        break;
      }
      default: {
        // Assert: This step is never reached.
        unreachable();
      }
    }

    // Increment parser's token index by parser's token increment.
    parser.token_index += parser.token_increment;
  }

  // If parser's result contains "hostname" and not "port", then set parser's
  // result["port"] to the empty string.
  if (parser.result.hostname && !parser.result.port) {
    parser.result.port = "";
  }

  // Return parser's result.
  return parser.result;
}

}  // namespace ada::url_pattern_helpers
#endif  // ADA_INCLUDE_URL_PATTERN
#endif
/* end file include/ada/url_pattern_helpers-inl.h */
/* begin file src/url_pattern.cpp */
#if ADA_INCLUDE_URL_PATTERN


#include <algorithm>
#include <optional>
#include <string>

namespace ada {

inline tl::expected<url_pattern_init, errors> url_pattern_init::process(
    const url_pattern_init& init, url_pattern_init::process_type type,
    std::optional<std::string_view> protocol,
    std::optional<std::string_view> username,
    std::optional<std::string_view> password,
    std::optional<std::string_view> hostname,
    std::optional<std::string_view> port,
    std::optional<std::string_view> pathname,
    std::optional<std::string_view> search,
    std::optional<std::string_view> hash) {
  // Let result be the result of creating a new URLPatternInit.
  auto result = url_pattern_init{};

  // If protocol is not null, set result["protocol"] to protocol.
  if (protocol.has_value()) result.protocol = *protocol;

  // If username is not null, set result["username"] to username.
  if (username.has_value()) result.username = *username;

  // If password is not null, set result["password"] to password.
  if (password.has_value()) result.password = *password;

  // If hostname is not null, set result["hostname"] to hostname.
  if (hostname.has_value()) result.hostname = *hostname;

  // If port is not null, set result["port"] to port.
  if (port.has_value()) result.port = *port;

  // If pathname is not null, set result["pathname"] to pathname.
  if (pathname.has_value()) result.pathname = *pathname;

  // If search is not null, set result["search"] to search.
  if (search.has_value()) result.search = *search;

  // If hash is not null, set result["hash"] to hash.
  if (hash.has_value()) result.hash = *hash;

  // Let baseURL be null.
  std::optional<url_aggregator> base_url{};

  // If init["baseURL"] exists:
  if (init.base_url.has_value()) {
    // Set baseURL to the result of parsing init["baseURL"].
    auto parsing_result = ada::parse<url_aggregator>(*init.base_url);
    // If baseURL is failure, then throw a TypeError.
    if (!parsing_result) {
      return tl::unexpected(errors::type_error);
    }
    base_url = std::move(*parsing_result);

    // If init["protocol"] does not exist, then set result["protocol"] to the
    // result of processing a base URL string given baseURL's scheme and type.
    if (!init.protocol.has_value()) {
      ADA_ASSERT_TRUE(base_url.has_value());
      std::string_view base_url_protocol = base_url->get_protocol();
      if (base_url_protocol.ends_with(":")) base_url_protocol.remove_suffix(1);
      result.protocol =
          url_pattern_helpers::process_base_url_string(base_url_protocol, type);
    }

    // If type is not "pattern" and init contains none of "protocol",
    // "hostname", "port" and "username", then set result["username"] to the
    // result of processing a base URL string given baseURL's username and type.
    if (type != process_type::pattern && !init.protocol && !init.hostname &&
        !init.port && !init.username) {
      result.username = url_pattern_helpers::process_base_url_string(
          base_url->get_username(), type);
    }

    // TODO: Optimization opportunity: Merge this with the previous check.
    // If type is not "pattern" and init contains none of "protocol",
    // "hostname", "port", "username" and "password", then set
    // result["password"] to the result of processing a base URL string given
    // baseURL's password and type.
    if (type != process_type::pattern && !init.protocol && !init.hostname &&
        !init.port && !init.username && !init.password) {
      result.password = url_pattern_helpers::process_base_url_string(
          base_url->get_password(), type);
    }

    // If init contains neither "protocol" nor "hostname", then:
    if (!init.protocol && !init.hostname) {
      // Let baseHost be baseURL's host.
      // If baseHost is null, then set baseHost to the empty string.
      auto base_host = base_url->get_hostname();
      // Set result["hostname"] to the result of processing a base URL string
      // given baseHost and type.
      result.hostname =
          url_pattern_helpers::process_base_url_string(base_host, type);
    }

    // If init contains none of "protocol", "hostname", and "port", then:
    if (!init.protocol && !init.hostname && !init.port) {
      // If baseURL's port is null, then set result["port"] to the empty string.
      // Otherwise, set result["port"] to baseURL's port, serialized.
      result.port = base_url->get_port();
    }

    // If init contains none of "protocol", "hostname", "port", and "pathname",
    // then set result["pathname"] to the result of processing a base URL string
    // given the result of URL path serializing baseURL and type.
    if (!init.protocol && !init.hostname && !init.port && !init.pathname) {
      result.pathname = url_pattern_helpers::process_base_url_string(
          base_url->get_pathname(), type);
    }

    // If init contains none of "protocol", "hostname", "port", "pathname", and
    // "search", then:
    if (!init.protocol && !init.hostname && !init.port && !init.pathname &&
        !init.search) {
      // Let baseQuery be baseURL's query. get_search() carries the leading "?"
      // delimiter, but the spec inherits the query itself, so drop it.
      std::string_view base_query = base_url->get_search();
      if (base_query.starts_with("?")) base_query.remove_prefix(1);
      // Set result["search"] to the result of processing a base URL string
      // given baseQuery and type.
      result.search =
          url_pattern_helpers::process_base_url_string(base_query, type);
    }

    // If init contains none of "protocol", "hostname", "port", "pathname",
    // "search", and "hash", then:
    if (!init.protocol && !init.hostname && !init.port && !init.pathname &&
        !init.search && !init.hash) {
      // Let baseFragment be baseURL's fragment. get_hash() carries the leading
      // "#" delimiter, but the spec inherits the fragment itself, so drop it.
      std::string_view base_fragment = base_url->get_hash();
      if (base_fragment.starts_with("#")) base_fragment.remove_prefix(1);
      // Set result["hash"] to the result of processing a base URL string given
      // baseFragment and type.
      result.hash =
          url_pattern_helpers::process_base_url_string(base_fragment, type);
    }
  }

  // If init["protocol"] exists, then set result["protocol"] to the result of
  // process protocol for init given init["protocol"] and type.
  if (init.protocol) {
    auto process_result = process_protocol(*init.protocol, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.protocol = std::move(*process_result);
  }

  // If init["username"] exists, then set result["username"] to the result of
  // process username for init given init["username"] and type.
  if (init.username.has_value()) {
    auto process_result = process_username(*init.username, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.username = std::move(*process_result);
  }

  // If init["password"] exists, then set result["password"] to the result of
  // process password for init given init["password"] and type.
  if (init.password.has_value()) {
    auto process_result = process_password(*init.password, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.password = std::move(*process_result);
  }

  // If init["hostname"] exists, then set result["hostname"] to the result of
  // process hostname for init given init["hostname"] and type.
  if (init.hostname.has_value()) {
    auto process_result = process_hostname(*init.hostname, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.hostname = std::move(*process_result);
  }

  // If init["port"] exists, then set result["port"] to the result of process
  // port for init given init["port"], result["protocol"], and type.
  if (init.port) {
    auto process_result =
        process_port(*init.port, result.protocol.value_or("fake"), type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.port = std::move(*process_result);
  }

  // If init["pathname"] exists:
  if (init.pathname.has_value()) {
    // Set result["pathname"] to init["pathname"].
    result.pathname = init.pathname;

    // If the following are all true:
    // - baseURL is not null;
    // - baseURL has an opaque path; and
    // - the result of running is an absolute pathname given result["pathname"]
    // and type is false,
    if (base_url && !base_url->has_opaque_path &&
        !url_pattern_helpers::is_absolute_pathname(*result.pathname, type)) {
      // Let baseURLPath be the result of running process a base URL string
      // given the result of URL path serializing baseURL and type.
      // TODO: Optimization opportunity: Avoid returning a string if no slash
      // exist.
      std::string base_url_path = url_pattern_helpers::process_base_url_string(
          base_url->get_pathname(), type);

      // Let slash index be the index of the last U+002F (/) code point found in
      // baseURLPath, interpreted as a sequence of code points, or null if there
      // are no instances of the code point.
      auto slash_index = base_url_path.find_last_of('/');

      // If slash index is not null:
      if (slash_index != std::string::npos) {
        // Let new pathname be the code point substring from 0 to slash index +
        // 1 within baseURLPath.
        base_url_path.resize(slash_index + 1);
        // Append result["pathname"] to the end of new pathname.
        ADA_ASSERT_TRUE(result.pathname.has_value());
        base_url_path.append(std::move(*result.pathname));
        // Set result["pathname"] to new pathname.
        result.pathname = std::move(base_url_path);
      }
    }

    // Set result["pathname"] to the result of process pathname for init given
    // result["pathname"], result["protocol"], and type.
    auto pathname_processing_result =
        process_pathname(*result.pathname, result.protocol.value_or(""), type);
    if (!pathname_processing_result) {
      return tl::unexpected(pathname_processing_result.error());
    }
    result.pathname = std::move(*pathname_processing_result);
  }

  // If init["search"] exists then set result["search"] to the result of process
  // search for init given init["search"] and type.
  if (init.search) {
    auto process_result = process_search(*init.search, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.search = std::move(*process_result);
  }

  // If init["hash"] exists then set result["hash"] to the result of process
  // hash for init given init["hash"] and type.
  if (init.hash) {
    auto process_result = process_hash(*init.hash, type);
    if (!process_result) {
      return tl::unexpected(process_result.error());
    }
    result.hash = std::move(*process_result);
  }
  // Return result.
  return result;
}

inline tl::expected<std::string, errors> url_pattern_init::process_protocol(
    std::string_view value, process_type type) {
  ada_log("process_protocol=", value, " [", type, "]");
  // Let strippedValue be the given value with a single trailing U+003A (:)
  // removed, if any.
  if (value.ends_with(":")) {
    value.remove_suffix(1);
  }
  // If type is "pattern" then return strippedValue.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a protocol given strippedValue.
  return url_pattern_helpers::canonicalize_protocol(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_username(
    std::string_view value, process_type type) {
  // If type is "pattern" then return value.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a username given value.
  return url_pattern_helpers::canonicalize_username(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_password(
    std::string_view value, process_type type) {
  // If type is "pattern" then return value.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a password given value.
  return url_pattern_helpers::canonicalize_password(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_hostname(
    std::string_view value, process_type type) {
  ada_log("process_hostname value=", value, " type=", type);
  // If type is "pattern" then return value.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a hostname given value.
  return url_pattern_helpers::canonicalize_hostname(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_port(
    std::string_view port, std::string_view protocol, process_type type) {
  // If type is "pattern" then return portValue.
  if (type == process_type::pattern) {
    return std::string(port);
  }
  // Return the result of running canonicalize a port given portValue and
  // protocolValue.
  return url_pattern_helpers::canonicalize_port_with_protocol(port, protocol);
}

inline tl::expected<std::string, errors> url_pattern_init::process_pathname(
    std::string_view value, std::string_view protocol, process_type type) {
  // If type is "pattern" then return pathnameValue.
  if (type == process_type::pattern) {
    return std::string(value);
  }

  // If protocolValue is a special scheme or the empty string, then return the
  // result of running canonicalize a pathname given pathnameValue.
  if (protocol.empty() || scheme::is_special(protocol)) {
    return url_pattern_helpers::canonicalize_pathname(value);
  }

  // Return the result of running canonicalize an opaque pathname given
  // pathnameValue.
  return url_pattern_helpers::canonicalize_opaque_pathname(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_search(
    std::string_view value, process_type type) {
  // Let strippedValue be the given value with a single leading U+003F (?)
  // removed, if any.
  if (value.starts_with("?")) {
    value.remove_prefix(1);
  }
  // We cannot assert that the value is no longer starting with a single
  // question mark because technically it can start. The question is whether or
  // not we should remove the first question mark. Ref:
  // https://github.com/ada-url/ada/pull/992 The spec is not clear on this.

  // If type is "pattern" then return strippedValue.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a search given strippedValue.
  return url_pattern_helpers::canonicalize_search(value);
}

inline tl::expected<std::string, errors> url_pattern_init::process_hash(
    std::string_view value, process_type type) {
  // Let strippedValue be the given value with a single leading U+0023 (#)
  // removed, if any.
  if (value.starts_with("#")) {
    value.remove_prefix(1);
  }
  ADA_ASSERT_TRUE(!value.starts_with("#"));
  // If type is "pattern" then return strippedValue.
  if (type == process_type::pattern) {
    return std::string(value);
  }
  // Return the result of running canonicalize a hash given strippedValue.
  return url_pattern_helpers::canonicalize_hash(value);
}

}  // namespace ada

#endif  // ADA_INCLUDE_URL_PATTERN
/* end file src/url_pattern.cpp */
/* begin file src/url_pattern_helpers.cpp */
#if ADA_INCLUDE_URL_PATTERN

#include <algorithm>
#include <array>
#include <charconv>
#include <optional>
#include <ranges>
#include <string>


namespace ada::url_pattern_helpers {

inline std::tuple<std::string, std::vector<std::string>>
generate_regular_expression_and_name_list(
    const std::vector<url_pattern_part>& part_list,
    url_pattern_compile_component_options options) {
  // Let result be "^"
  std::string result = "^";
  // Reserve capacity to reduce reallocations
  result.reserve(part_list.size() * 16);

  // Let name list be a new list
  std::vector<std::string> name_list{};
  name_list.reserve(part_list.size());

  // Pre-generate segment wildcard regexp if needed (avoids repeated generation)
  std::string segment_wildcard_regexp;

  // For each part of part list:
  for (const url_pattern_part& part : part_list) {
    // If part's type is "fixed-text":
    if (part.type == url_pattern_part_type::FIXED_TEXT) {
      // If part's modifier is "none"
      if (part.modifier == url_pattern_part_modifier::none) {
        result.append(escape_regexp_string(part.value));
      } else {
        // (?:<fixed text>)<modifier>
        result.append("(?:");
        result.append(escape_regexp_string(part.value));
        result.push_back(')');
        result.append(convert_modifier_to_string(part.modifier));
      }
      continue;
    }

    // Assert: part's name is not the empty string
    ADA_ASSERT_TRUE(!part.name.empty());
    name_list.push_back(part.name);

    // Use string_view to avoid copies where possible
    std::string_view regexp_value = part.value;

    if (part.type == url_pattern_part_type::SEGMENT_WILDCARD) {
      // Lazy generate segment wildcard regexp
      if (segment_wildcard_regexp.empty()) {
        segment_wildcard_regexp = generate_segment_wildcard_regexp(options);
      }
      regexp_value = segment_wildcard_regexp;
    } else if (part.type == url_pattern_part_type::FULL_WILDCARD) {
      regexp_value = ".*";
    }

    // If part's prefix is the empty string and part's suffix is the empty
    // string
    if (part.prefix.empty() && part.suffix.empty()) {
      // If part's modifier is "none" or "optional"
      if (part.modifier == url_pattern_part_modifier::none ||
          part.modifier == url_pattern_part_modifier::optional) {
        // (<regexp value>)<modifier>
        result.push_back('(');
        result.append(regexp_value);
        result.push_back(')');
        result.append(convert_modifier_to_string(part.modifier));
      } else {
        // ((?:<regexp value>)<modifier>)
        result.append("((?:");
        result.append(regexp_value);
        result.push_back(')');
        result.append(convert_modifier_to_string(part.modifier));
        result.push_back(')');
      }
      continue;
    }

    // If part's modifier is "none" or "optional"
    if (part.modifier == url_pattern_part_modifier::none ||
        part.modifier == url_pattern_part_modifier::optional) {
      // (?:<prefix>(<regexp value>)<suffix>)<modifier>
      result.append("(?:");
      result.append(escape_regexp_string(part.prefix));
      result.push_back('(');
      result.append(regexp_value);
      result.push_back(')');
      result.append(escape_regexp_string(part.suffix));
      result.push_back(')');
      result.append(convert_modifier_to_string(part.modifier));
      continue;
    }

    // Assert: part's modifier is "zero-or-more" or "one-or-more"
    ADA_ASSERT_TRUE(part.modifier == url_pattern_part_modifier::zero_or_more ||
                    part.modifier == url_pattern_part_modifier::one_or_more);

    // Assert: part's prefix is not the empty string or part's suffix is not the
    // empty string
    ADA_ASSERT_TRUE(!part.prefix.empty() || !part.suffix.empty());

    // (?:<prefix>((?:<regexp value>)(?:<suffix><prefix>(?:<regexp
    // value>))*)<suffix>)?
    // Append "(?:" to the end of result.
    result.append("(?:");
    // Append the result of running escape a regexp string given part's prefix
    // to the end of result.
    result.append(escape_regexp_string(part.prefix));
    // Append "((?:" to the end of result.
    result.append("((?:");
    // Append regexp value to the end of result.
    result.append(regexp_value);
    // Append ")(?:" to the end of result.
    result.append(")(?:");
    // Append the result of running escape a regexp string given part's suffix
    // to the end of result.
    result.append(escape_regexp_string(part.suffix));
    // Append the result of running escape a regexp string given part's prefix
    // to the end of result.
    result.append(escape_regexp_string(part.prefix));
    // Append "(?:" to the end of result.
    result.append("(?:");
    // Append regexp value to the end of result.
    result.append(regexp_value);
    // Append "))*)" to the end of result.
    result.append("))*)");
    // Append the result of running escape a regexp string given part's suffix
    // to the end of result.
    result.append(escape_regexp_string(part.suffix));
    // Append ")" to the end of result.
    result.append(")");

    // If part's modifier is "zero-or-more" then append "?" to the end of result
    if (part.modifier == url_pattern_part_modifier::zero_or_more) {
      result += "?";
    }
  }

  // Append "$" to the end of result
  result += "$";

  // Return (result, name list)
  return {std::move(result), std::move(name_list)};
}

inline bool is_ipv6_address(std::string_view input) noexcept {
  // If input's code point length is less than 2, then return false.
  if (input.size() < 2) return false;

  // Let input code points be input interpreted as a list of code points.
  // If input code points[0] is U+005B ([), then return true.
  if (input.front() == '[') return true;
  // If input code points[0] is U+007B ({) and input code points[1] is U+005B
  // ([), then return true.
  if (input.starts_with("{[")) return true;
  // If input code points[0] is U+005C (\) and input code points[1] is U+005B
  // ([), then return true.
  return input.starts_with("\\[");
}

inline std::string_view convert_modifier_to_string(
    url_pattern_part_modifier modifier) {
  switch (modifier) {
      // If modifier is "zero-or-more", then return "*".
    case url_pattern_part_modifier::zero_or_more:
      return "*";
    // If modifier is "optional", then return "?".
    case url_pattern_part_modifier::optional:
      return "?";
    // If modifier is "one-or-more", then return "+".
    case url_pattern_part_modifier::one_or_more:
      return "+";
    // Return the empty string.
    default:
      return "";
  }
}

inline std::string generate_segment_wildcard_regexp(
    url_pattern_compile_component_options options) {
  // Let result be "[^".
  std::string result = "[^";
  // Append the result of running escape a regexp string given options's
  // delimiter code point to the end of result.
  result.append(escape_regexp_string(options.get_delimiter()));
  // Append "]+?" to the end of result.
  result.append("]+?");
  // Return result.
  ada_log("generate_segment_wildcard_regexp result: ", result);
  return result;
}

namespace {
// Unified lookup table for URL pattern character classification
// Bit flags for different character types
constexpr uint8_t CHAR_SCHEME = 1;  // valid in scheme (a-z, A-Z, 0-9, +, -, .)
constexpr uint8_t CHAR_UPPER = 2;   // uppercase letter (needs lowercasing)
constexpr uint8_t CHAR_SIMPLE_HOSTNAME = 4;  // simple hostname (a-z, 0-9, -, .)
constexpr uint8_t CHAR_SIMPLE_PATHNAME =
    8;  // simple pathname (a-z, A-Z, 0-9, /, -, _, ~)

constexpr std::array<uint8_t, 256> char_class_table = []() consteval {
  std::array<uint8_t, 256> table{};
  for (int c = 'a'; c <= 'z'; c++)
    table[c] = CHAR_SCHEME | CHAR_SIMPLE_HOSTNAME | CHAR_SIMPLE_PATHNAME;
  for (int c = 'A'; c <= 'Z'; c++)
    table[c] = CHAR_SCHEME | CHAR_UPPER | CHAR_SIMPLE_PATHNAME;
  for (int c = '0'; c <= '9'; c++)
    table[c] = CHAR_SCHEME | CHAR_SIMPLE_HOSTNAME | CHAR_SIMPLE_PATHNAME;
  table['+'] = CHAR_SCHEME;
  table['-'] = CHAR_SCHEME | CHAR_SIMPLE_HOSTNAME | CHAR_SIMPLE_PATHNAME;
  table['.'] =
      CHAR_SCHEME | CHAR_SIMPLE_HOSTNAME;  // not pathname (needs normalization)
  table['/'] = CHAR_SIMPLE_PATHNAME;
  table['_'] = CHAR_SIMPLE_PATHNAME;
  table['~'] = CHAR_SIMPLE_PATHNAME;
  return table;
}();
}  // namespace

inline tl::expected<std::string, errors> canonicalize_protocol(
    std::string_view input) {
  ada_log("canonicalize_protocol called with input=", input);
  if (input.empty()) [[unlikely]] {
    return "";
  }

  if (input.ends_with(":")) {
    input.remove_suffix(1);
  }

  // Fast path: special schemes are already canonical
  if (scheme::is_special(input)) {
    return std::string(input);
  }

  // Fast path: validate scheme chars and check for uppercase
  // First char must be alpha (not +, -, ., or digit)
  uint8_t first_flags = char_class_table[static_cast<uint8_t>(input[0])];
  if (!(first_flags & CHAR_SCHEME) || input[0] == '+' || input[0] == '-' ||
      input[0] == '.' || unicode::is_ascii_digit(input[0])) {
    return tl::unexpected(errors::type_error);
  }

  uint8_t needs_lowercase = first_flags & CHAR_UPPER;
  for (size_t i = 1; i < input.size(); i++) {
    uint8_t flags = char_class_table[static_cast<uint8_t>(input[i])];
    if (!(flags & CHAR_SCHEME)) {
      return tl::unexpected(errors::type_error);
    }
    needs_lowercase |= flags & CHAR_UPPER;
  }

  if (needs_lowercase == 0) {
    return std::string(input);
  }

  std::string result(input);
  unicode::to_lower_ascii(result.data(), result.size());
  return result;
}

inline tl::expected<std::string, errors> canonicalize_username(
    std::string_view input) {
  // If value is the empty string, return value.
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // Percent-encode the input using the userinfo percent-encode set.
  size_t idx = ada::unicode::percent_encode_index(
      input, character_sets::USERINFO_PERCENT_ENCODE);
  if (idx == input.size()) {
    // No encoding needed, return input as-is
    return std::string(input);
  }
  // Percent-encode from the first character that needs encoding
  return ada::unicode::percent_encode(
      input, character_sets::USERINFO_PERCENT_ENCODE, idx);
}

inline tl::expected<std::string, errors> canonicalize_password(
    std::string_view input) {
  // If value is the empty string, return value.
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // Percent-encode the input using the userinfo percent-encode set.
  size_t idx = ada::unicode::percent_encode_index(
      input, character_sets::USERINFO_PERCENT_ENCODE);
  if (idx == input.size()) {
    // No encoding needed, return input as-is
    return std::string(input);
  }
  // Percent-encode from the first character that needs encoding
  return ada::unicode::percent_encode(
      input, character_sets::USERINFO_PERCENT_ENCODE, idx);
}

inline tl::expected<std::string, errors> canonicalize_hostname(
    std::string_view input) {
  ada_log("canonicalize_hostname input=", input);
  if (input.empty()) [[unlikely]] {
    return "";
  }

  // Fast path: simple hostnames (lowercase ASCII, digits, -, .) need no IDNA.
  // The simple character set also covers IPv4-shaped hosts, which the slow
  // path rewrites ("0" -> "0.0.0.0", "0x7f.1" -> "127.0.0.1"). Exclude those
  // so the fast path can't return a non-canonical hostname.
  //
  // Pure-ASCII "xn--" labels are intentionally left on the fast path: with
  // beStrict=false, domain-to-ASCII returns the lowercased ASCII input even
  // when Unicode ToASCII would fail (e.g. invalid ACE "xn--a"). See
  // https://url.spec.whatwg.org/#concept-domain-to-ascii
  bool needs_processing = false;
  for (char c : input) {
    needs_processing |=
        !(char_class_table[static_cast<uint8_t>(c)] & CHAR_SIMPLE_HOSTNAME);
  }
  if (!needs_processing && !checkers::is_ipv4(input)) {
    return std::string(input);
  }

  // Let dummyURL be a new URL record.
  // Let parseResult be the result of running the basic URL parser given value
  // with dummyURL as url and hostname state as state override.

  // IMPORTANT: The protocol needs to be a special protocol, otherwise the
  // hostname will not be converted using IDNA.
  auto url = ada::parse<url_aggregator>("https://dummy.test", nullptr);
  ADA_ASSERT_TRUE(url);
  // if (!isValidHostnameInput(hostname)) return kj::none;
  if (!url->set_hostname(input)) {
    // If parseResult is failure, then throw a TypeError.
    return tl::unexpected(errors::type_error);
  }
  // Return dummyURL's host, serialized, or empty string if it is null.
  return std::string(url->get_hostname());
}

inline tl::expected<std::string, errors> canonicalize_ipv6_hostname(
    std::string_view input) {
  ada_log("canonicalize_ipv6_hostname input=", input);
  // TODO: Optimization opportunity: Use lookup table to speed up checking
  if (std::ranges::any_of(input, [](char c) {
        return c != '[' && c != ']' && c != ':' &&
               !unicode::is_ascii_hex_digit(c);
      })) {
    return tl::unexpected(errors::type_error);
  }
  // Append the result of running ASCII lowercase given code point to the end of
  // result.
  auto hostname = std::string(input);
  unicode::to_lower_ascii(hostname.data(), hostname.size());
  return hostname;
}

inline tl::expected<std::string, errors> canonicalize_port(
    std::string_view port_value) {
  // If portValue is the empty string, return portValue.
  if (port_value.empty()) [[unlikely]] {
    return "";
  }

  // Remove ASCII tab or newline characters
  std::string trimmed(port_value);
  helpers::remove_ascii_tab_or_newline(trimmed);

  if (trimmed.empty()) {
    return "";
  }

  // Input should start with a digit character
  if (!unicode::is_ascii_digit(trimmed.front())) {
    return tl::unexpected(errors::type_error);
  }

  // Find the first non-digit character
  auto first_non_digit =
      std::ranges::find_if_not(trimmed, unicode::is_ascii_digit);
  std::string_view digits_to_parse =
      std::string_view(trimmed.data(), first_non_digit - trimmed.begin());

  // Here we have a range of ASCII digit characters identified by
  // digits_to_parse. It is non-empty. The port state of the URL parser reads
  // it as an integer, so leading zeros are part of the number: "0080" is 80
  // and "065535" is 65535, not a six-digit overflow. Only the significant
  // digits count toward the 5-digit maximum, matching the fast path in
  // implementation.cpp.
  size_t first_significant = digits_to_parse.find_first_not_of('0');
  if (first_significant == std::string_view::npos) {
    // The value is all zeros, i.e. port 0.
    return "0";
  }
  digits_to_parse.remove_prefix(first_significant);
  // We want to determine whether it is a valid port number (0-65535).
  // Clearly, if the length is greater than 5, it is invalid.
  // If the length is 5, we need to compare lexicographically to "65535".
  // Otherwise it is valid.
  if (digits_to_parse.size() == 5) {
    if (digits_to_parse > "65535") {
      return tl::unexpected(errors::type_error);
    }
  } else if (digits_to_parse.size() > 5) {
    return tl::unexpected(errors::type_error);
  }
  // It is valid! Most times, we do not need to parse it into an integer.
  return std::string(digits_to_parse);
}

inline tl::expected<std::string, errors> canonicalize_port_with_protocol(
    std::string_view port_value, std::string_view protocol) {
  // If portValue is the empty string, return portValue.
  if (port_value.empty()) [[unlikely]] {
    return "";
  }

  // Handle empty or trailing colon in protocol
  if (protocol.empty()) {
    protocol = "fake";
  } else if (protocol.ends_with(":")) {
    protocol.remove_suffix(1);
  }

  // Remove ASCII tab or newline characters
  std::string trimmed(port_value);
  helpers::remove_ascii_tab_or_newline(trimmed);

  if (trimmed.empty()) {
    return "";
  }

  // Input should start with a digit character
  if (!unicode::is_ascii_digit(trimmed.front())) {
    return tl::unexpected(errors::type_error);
  }

  // Find the first non-digit character
  auto first_non_digit =
      std::ranges::find_if_not(trimmed, unicode::is_ascii_digit);
  std::string_view digits_to_parse =
      std::string_view(trimmed.data(), first_non_digit - trimmed.begin());

  // Parse the port number
  uint16_t parsed_port{};
  // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage)
  auto result = std::from_chars(digits_to_parse.data(),
                                digits_to_parse.data() + digits_to_parse.size(),
                                parsed_port);

  if (result.ec == std::errc::result_out_of_range) {
    return tl::unexpected(errors::type_error);
  }

  if (result.ec == std::errc()) {
    // Check if this is the default port for the scheme
    uint16_t default_port = scheme::get_special_port(protocol);

    // If it's the default port for a special scheme, return empty string
    if (default_port != 0 && default_port == parsed_port) {
      return "";
    }

    // Successfully parsed, return as string
    return std::to_string(parsed_port);
  }

  return tl::unexpected(errors::type_error);
}

inline tl::expected<std::string, errors> canonicalize_pathname(
    std::string_view input) {
  if (input.empty()) [[unlikely]] {
    return "";
  }

  // Fast path: simple pathnames (no . which needs normalization) can be
  // returned as-is
  bool needs_processing = false;
  for (char c : input) {
    needs_processing |=
        !(char_class_table[static_cast<uint8_t>(c)] & CHAR_SIMPLE_PATHNAME);
  }
  if (!needs_processing) {
    return std::string(input);
  }

  // Let leading slash be true if the first code point in value is U+002F (/)
  // and otherwise false.
  const bool leading_slash = input.starts_with("/");
  // Let modified value be "/-" if leading slash is false and otherwise the
  // empty string.
  const auto modified_value =
      (leading_slash ? std::string() : std::string("/-")) + std::string(input);
  // The spec runs the basic URL parser with the path in state override, where
  // '?' and '#' are ordinary path code points (percent-encoded) and leading or
  // trailing C0 control or space is kept. Building a full URL string and
  // parsing it (no state override) instead let '?' and '#' start the
  // query/fragment, so the pathname was silently truncated at the first literal
  // '?' or '#'. set_pathname runs the parser in path state override, matching
  // how canonicalize_hostname uses set_hostname.
  auto url = ada::parse<url_aggregator>("fake://fake-url", nullptr);
  ADA_ASSERT_TRUE(url);
  if (!url->set_pathname(modified_value)) {
    // If parseResult is failure, then throw a TypeError.
    return tl::unexpected(errors::type_error);
  }
  const auto pathname = url->get_pathname();
  // If leading slash is false, then set result to the code point substring
  // from 2 to the end of the string within result.
  if (!leading_slash) {
    // pathname should start with "/-" but path traversal (e.g. "../../")
    // can reduce it to just "/" which is shorter than 2 characters.
    if (pathname.size() < 2) {
      return tl::unexpected(errors::type_error);
    }
    return std::string(pathname.substr(2));
  }
  return std::string(pathname);
}

inline tl::expected<std::string, errors> canonicalize_opaque_pathname(
    std::string_view input) {
  // If value is the empty string, return value.
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // Let dummyURL be a new URL record.
  // Set dummyURL's path to the empty string.
  // Let parseResult be the result of running URL parsing given value with
  // dummyURL as url and opaque path state as state override.
  if (auto url =
          ada::parse<url_aggregator>("fake:" + std::string(input), nullptr)) {
    // Return the result of URL path serializing dummyURL.
    return std::string(url->get_pathname());
  }
  // If parseResult is failure, then throw a TypeError.
  return tl::unexpected(errors::type_error);
}

inline tl::expected<std::string, errors> canonicalize_search(std::string_view input) {
  // If value is the empty string, return value.
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // A leading '?' is a valid query code point here: it is the caller (process a
  // search) that removes a single delimiter, not this step, which mirrors the
  // basic URL parser's query state.
  std::string new_value(input);
  // Remove ASCII tab or newline characters
  helpers::remove_ascii_tab_or_newline(new_value);

  if (new_value.empty()) {
    return "";
  }

  // Percent-encode using QUERY_PERCENT_ENCODE (for non-special URLs)
  // Note: "fake://dummy.test" is not a special URL, so we use
  // QUERY_PERCENT_ENCODE
  size_t idx = ada::unicode::percent_encode_index(
      new_value, character_sets::QUERY_PERCENT_ENCODE);
  if (idx == new_value.size()) {
    // No encoding needed
    return new_value;
  }
  // Percent-encode from the first character that needs encoding
  return ada::unicode::percent_encode(
      new_value, character_sets::QUERY_PERCENT_ENCODE, idx);
}

inline tl::expected<std::string, errors> canonicalize_hash(std::string_view input) {
  // If value is the empty string, return value.
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // A leading '#' is a valid fragment code point here: it is the caller
  // (process a hash) that removes a single delimiter, not this step, which
  // mirrors the basic URL parser's fragment state.
  std::string new_value(input);
  // Remove ASCII tab or newline characters
  helpers::remove_ascii_tab_or_newline(new_value);

  if (new_value.empty()) {
    return "";
  }

  // Percent-encode using FRAGMENT_PERCENT_ENCODE
  size_t idx = ada::unicode::percent_encode_index(
      new_value, character_sets::FRAGMENT_PERCENT_ENCODE);
  if (idx == new_value.size()) {
    // No encoding needed
    return new_value;
  }
  // Percent-encode from the first character that needs encoding
  return ada::unicode::percent_encode(
      new_value, character_sets::FRAGMENT_PERCENT_ENCODE, idx);
}

inline tl::expected<std::vector<token>, errors> tokenize(std::string_view input,
                                                  token_policy policy) {
  ada_log("tokenize input: ", input);
  // Let tokenizer be a new tokenizer.
  // Set tokenizer's input to input.
  // Set tokenizer's policy to policy.
  auto tokenizer = Tokenizer(input, policy);
  // While tokenizer's index is less than tokenizer's input's code point length:
  while (tokenizer.index < tokenizer.input.size()) {
    // Run seek and get the next code point given tokenizer and tokenizer's
    // index.
    tokenizer.seek_and_get_next_code_point(tokenizer.index);

    // Malformed UTF-8 must not stall tokenization: report an invalid-char
    // token (lenient) or fail fast (strict), while always making progress.
    if (tokenizer.had_invalid_code_point()) {
      if (auto error = tokenizer.process_tokenizing_error(tokenizer.next_index,
                                                          tokenizer.index)) {
        return tl::unexpected(*error);
      }
      continue;
    }

    // If tokenizer's code point is U+002A (*):
    if (tokenizer.code_point == '*') {
      // Run add a token with default position and length given tokenizer and
      // "asterisk".
      tokenizer.add_token_with_defaults(token_type::ASTERISK);
      ada_log("add ASTERISK token");
      // Continue.
      continue;
    }

    // If tokenizer's code point is U+002B (+) or U+003F (?):
    if (tokenizer.code_point == '+' || tokenizer.code_point == '?') {
      // Run add a token with default position and length given tokenizer and
      // "other-modifier".
      tokenizer.add_token_with_defaults(token_type::OTHER_MODIFIER);
      // Continue.
      continue;
    }

    // If tokenizer's code point is U+005C (\):
    if (tokenizer.code_point == '\\') {
      // If tokenizer's index is equal to tokenizer's input's code point length
      // - 1:
      if (tokenizer.index == tokenizer.input.size() - 1) {
        // Run process a tokenizing error given tokenizer, tokenizer's next
        // index, and tokenizer's index.
        if (auto error = tokenizer.process_tokenizing_error(
                tokenizer.next_index, tokenizer.index)) {
          ada_log("process_tokenizing_error failed");
          return tl::unexpected(*error);
        }
        continue;
      }

      // Let escaped index be tokenizer's next index.
      auto escaped_index = tokenizer.next_index;
      // Run get the next code point given tokenizer.
      tokenizer.get_next_code_point();
      if (tokenizer.had_invalid_code_point()) {
        if (auto error = tokenizer.process_tokenizing_error(
                tokenizer.next_index, escaped_index)) {
          return tl::unexpected(*error);
        }
        continue;
      }
      // Run add a token with default length given tokenizer, "escaped-char",
      // tokenizer's next index, and escaped index.
      tokenizer.add_token_with_default_length(
          token_type::ESCAPED_CHAR, tokenizer.next_index, escaped_index);
      ada_log("add ESCAPED_CHAR token on next_index ", tokenizer.next_index,
              " with escaped index ", escaped_index);
      // Continue.
      continue;
    }

    // If tokenizer's code point is U+007B ({):
    if (tokenizer.code_point == '{') {
      // Run add a token with default position and length given tokenizer and
      // "open".
      tokenizer.add_token_with_defaults(token_type::OPEN);
      ada_log("add OPEN token");
      continue;
    }

    // If tokenizer's code point is U+007D (}):
    if (tokenizer.code_point == '}') {
      // Run add a token with default position and length given tokenizer and
      // "close".
      tokenizer.add_token_with_defaults(token_type::CLOSE);
      ada_log("add CLOSE token");
      continue;
    }

    // If tokenizer's code point is U+003A (:):
    if (tokenizer.code_point == ':') {
      // Let name position be tokenizer's next index.
      auto name_position = tokenizer.next_index;
      // Let name start be name position.
      auto name_start = name_position;
      bool invalid_name = false;
      // While name position is less than tokenizer's input's code point length:
      while (name_position < tokenizer.input.size()) {
        // Run seek and get the next code point given tokenizer and name
        // position.
        tokenizer.seek_and_get_next_code_point(name_position);
        if (tokenizer.had_invalid_code_point()) {
          if (auto error = tokenizer.process_tokenizing_error(
                  tokenizer.next_index, name_position)) {
            return tl::unexpected(*error);
          }
          invalid_name = true;
          break;
        }
        // Let first code point be true if name position equals name start and
        // false otherwise.
        bool first_code_point = name_position == name_start;
        // Let valid code point be the result of running is a valid name code
        // point given tokenizer's code point and first code point.
        auto valid_code_point =
            idna::valid_name_code_point(tokenizer.code_point, first_code_point);
        ada_log("tokenizer.code_point=", uint32_t(tokenizer.code_point),
                " first_code_point=", first_code_point,
                " valid_code_point=", valid_code_point);
        // If valid code point is false break.
        if (!valid_code_point) break;
        // Set name position to tokenizer's next index.
        name_position = tokenizer.next_index;
      }

      if (invalid_name) {
        continue;
      }

      // If name position is less than or equal to name start:
      if (name_position <= name_start) {
        // Run process a tokenizing error given tokenizer, name start, and
        // tokenizer's index.
        if (auto error = tokenizer.process_tokenizing_error(name_start,
                                                            tokenizer.index)) {
          ada_log("process_tokenizing_error failed");
          return tl::unexpected(*error);
        }
        // Continue
        continue;
      }

      // Run add a token with default length given tokenizer, "name", name
      // position, and name start.
      tokenizer.add_token_with_default_length(token_type::NAME, name_position,
                                              name_start);
      continue;
    }

    // If tokenizer's code point is U+0028 (():
    if (tokenizer.code_point == '(') {
      // Let depth be 1.
      size_t depth = 1;
      // Let regexp position be tokenizer's next index.
      auto regexp_position = tokenizer.next_index;
      // Let regexp start be regexp position.
      auto regexp_start = regexp_position;
      // Let error be false.
      bool error = false;

      // While regexp position is less than tokenizer's input's code point
      // length:
      while (regexp_position < tokenizer.input.size()) {
        // Run seek and get the next code point given tokenizer and regexp
        // position.
        tokenizer.seek_and_get_next_code_point(regexp_position);
        if (tokenizer.had_invalid_code_point()) {
          if (auto process_error = tokenizer.process_tokenizing_error(
                  tokenizer.next_index, regexp_position)) {
            return tl::unexpected(*process_error);
          }
          error = true;
          break;
        }

        // TODO: Optimization opportunity: The next 2 if statements can be
        // merged. If the result of running is ASCII given tokenizer's code
        // point is false:
        if (!unicode::is_ascii(tokenizer.code_point)) {
          // Run process a tokenizing error given tokenizer, regexp start, and
          // tokenizer's index.
          if (auto process_error = tokenizer.process_tokenizing_error(
                  regexp_start, tokenizer.index)) {
            return tl::unexpected(*process_error);
          }
          // Set error to true.
          error = true;
          break;
        }

        // If regexp position equals regexp start and tokenizer's code point is
        // U+003F (?):
        if (regexp_position == regexp_start && tokenizer.code_point == '?') {
          // Run process a tokenizing error given tokenizer, regexp start, and
          // tokenizer's index.
          if (auto process_error = tokenizer.process_tokenizing_error(
                  regexp_start, tokenizer.index)) {
            return tl::unexpected(*process_error);
          }
          // Set error to true;
          error = true;
          break;
        }

        // If tokenizer's code point is U+005C (\):
        if (tokenizer.code_point == '\\') {
          // If regexp position equals tokenizer's input's code point length - 1
          if (regexp_position == tokenizer.input.size() - 1) {
            // Run process a tokenizing error given tokenizer, regexp start, and
            // tokenizer's index.
            if (auto process_error = tokenizer.process_tokenizing_error(
                    regexp_start, tokenizer.index)) {
              return tl::unexpected(*process_error);
            }
            // Set error to true.
            error = true;
            break;
          }
          // Run get the next code point given tokenizer.
          auto escaped_index = tokenizer.next_index;
          tokenizer.get_next_code_point();
          if (tokenizer.had_invalid_code_point()) {
            if (auto process_error = tokenizer.process_tokenizing_error(
                    tokenizer.next_index, escaped_index)) {
              return tl::unexpected(*process_error);
            }
            error = true;
            break;
          }
          // If the result of running is ASCII given tokenizer's code point is
          // false:
          if (!unicode::is_ascii(tokenizer.code_point)) {
            // Run process a tokenizing error given tokenizer, regexp start, and
            // tokenizer's index.
            if (auto process_error = tokenizer.process_tokenizing_error(
                    regexp_start, tokenizer.index);
                process_error.has_value()) {
              return tl::unexpected(*process_error);
            }
            // Set error to true.
            error = true;
            break;
          }
          // Set regexp position to tokenizer's next index.
          regexp_position = tokenizer.next_index;
          continue;
        }

        // If tokenizer's code point is U+0029 ()):
        if (tokenizer.code_point == ')') {
          // Decrement depth by 1.
          depth--;
          // If depth is 0:
          if (depth == 0) {
            // Set regexp position to tokenizer's next index.
            regexp_position = tokenizer.next_index;
            // Break.
            break;
          }
        } else if (tokenizer.code_point == '(') {
          // Otherwise if tokenizer's code point is U+0028 (():
          // Increment depth by 1.
          depth++;
          // If regexp position equals tokenizer's input's code point length -
          // 1:
          if (regexp_position == tokenizer.input.size() - 1) {
            // Run process a tokenizing error given tokenizer, regexp start, and
            // tokenizer's index.
            if (auto process_error = tokenizer.process_tokenizing_error(
                    regexp_start, tokenizer.index)) {
              return tl::unexpected(*process_error);
            }
            // Set error to true.
            error = true;
            break;
          }
          // Let temporary position be tokenizer's next index.
          auto temporary_position = tokenizer.next_index;
          // Run get the next code point given tokenizer.
          tokenizer.get_next_code_point();
          if (tokenizer.had_invalid_code_point()) {
            if (auto process_error = tokenizer.process_tokenizing_error(
                    tokenizer.next_index, temporary_position)) {
              return tl::unexpected(*process_error);
            }
            error = true;
            break;
          }
          // If tokenizer's code point is not U+003F (?):
          if (tokenizer.code_point != '?') {
            // Run process a tokenizing error given tokenizer, regexp start, and
            // tokenizer's index.
            if (auto process_error = tokenizer.process_tokenizing_error(
                    regexp_start, tokenizer.index)) {
              return tl::unexpected(*process_error);
            }
            // Set error to true.
            error = true;
            break;
          }
          // Set tokenizer's next index to temporary position.
          tokenizer.next_index = temporary_position;
        }
        // Set regexp position to tokenizer's next index.
        regexp_position = tokenizer.next_index;
      }

      // If error is true continue.
      if (error) continue;
      // If depth is not zero:
      if (depth != 0) {
        // Run process a tokenizing error given tokenizer, regexp start, and
        // tokenizer's index.
        if (auto process_error = tokenizer.process_tokenizing_error(
                regexp_start, tokenizer.index)) {
          return tl::unexpected(*process_error);
        }
        continue;
      }
      // Let regexp length be regexp position - regexp start - 1.
      auto regexp_length = regexp_position - regexp_start - 1;
      // If regexp length is zero:
      if (regexp_length == 0) {
        // Run process a tokenizing error given tokenizer, regexp start, and
        // tokenizer's index.
        if (auto process_error = tokenizer.process_tokenizing_error(
                regexp_start, tokenizer.index)) {
          ada_log("process_tokenizing_error failed");
          return tl::unexpected(*process_error);
        }
        continue;
      }
      // Run add a token given tokenizer, "regexp", regexp position, regexp
      // start, and regexp length.
      tokenizer.add_token(token_type::REGEXP, regexp_position, regexp_start,
                          regexp_length);
      continue;
    }
    // Run add a token with default position and length given tokenizer and
    // "char".
    tokenizer.add_token_with_defaults(token_type::CHAR);
  }
  // Run add a token with default length given tokenizer, "end", tokenizer's
  // index, and tokenizer's index.
  tokenizer.add_token_with_default_length(token_type::END, tokenizer.index,
                                          tokenizer.index);

  ada_log("tokenizer.token_list size is: ", tokenizer.token_list.size());
  // Return tokenizer's token list.
  return tokenizer.token_list;
}

namespace {
constexpr std::array<uint8_t, 256> escape_pattern_table = []() consteval {
  std::array<uint8_t, 256> out{};
  for (auto& c : {'+', '*', '?', ':', '{', '}', '(', ')', '\\'}) {
    out[c] = 1;
  }
  return out;
}();

constexpr bool should_escape_pattern_char(char c) {
  return escape_pattern_table[static_cast<uint8_t>(c)];
}
}  // namespace

inline std::string escape_pattern_string(std::string_view input) {
  ada_log("escape_pattern_string called with input=", input);
  if (input.empty()) [[unlikely]] {
    return "";
  }
  // Assert: input is an ASCII string.
  ADA_ASSERT_TRUE(ada::idna::is_ascii(input));
  // Let result be the empty string.
  std::string result{};
  // Reserve extra space for potential escapes
  result.reserve(input.size() * 2);

  // While index is less than input's length:
  for (const char c : input) {
    if (should_escape_pattern_char(c)) {
      // Append U+005C (\) to the end of result.
      result.push_back('\\');
    }
    // Append c to the end of result.
    result.push_back(c);
  }
  // Return result.
  return result;
}

namespace {
constexpr std::array<uint8_t, 256> escape_regexp_table = []() consteval {
  std::array<uint8_t, 256> out{};
  for (auto& c : {'.', '+', '*', '?', '^', '$', '{', '}', '(', ')', '[', ']',
                  '|', '/', '\\'}) {
    out[c] = 1;
  }
  return out;
}();

constexpr bool should_escape_regexp_char(char c) {
  return escape_regexp_table[(uint8_t)c];
}
}  // namespace

inline std::string escape_regexp_string(std::string_view input) {
  // Assert: input is an ASCII string.
  ADA_ASSERT_TRUE(idna::is_ascii(input));
  // Let result be the empty string.
  std::string result{};
  // Reserve extra space for potential escapes (worst case: all chars escaped)
  result.reserve(input.size() * 2);
  for (const char c : input) {
    if (should_escape_regexp_char(c)) {
      // Avoid temporary string allocation - directly append characters
      result.push_back('\\');
      result.push_back(c);
    } else {
      result.push_back(c);
    }
  }
  return result;
}

inline std::string process_base_url_string(std::string_view input,
                                    url_pattern_init::process_type type) {
  // If type is not "pattern" return input.
  if (type != url_pattern_init::process_type::pattern) {
    return std::string(input);
  }
  // Return the result of escaping a pattern string given input.
  return escape_pattern_string(input);
}

constexpr bool is_absolute_pathname(
    std::string_view input, url_pattern_init::process_type type) noexcept {
  // If input is the empty string, then return false.
  if (input.empty()) [[unlikely]] {
    return false;
  }
  // If input[0] is U+002F (/), then return true.
  if (input.starts_with("/")) return true;
  // If type is "url", then return false.
  if (type == url_pattern_init::process_type::url) return false;
  // If input's code point length is less than 2, then return false.
  if (input.size() < 2) return false;
  // If input[0] is U+005C (\) and input[1] is U+002F (/), then return true.
  // If input[0] is U+007B ({) and input[1] is U+002F (/), then return true.
  // Return false.
  return input[1] == '/' && (input[0] == '\\' || input[0] == '{');
}

inline std::string generate_pattern_string(
    std::vector<url_pattern_part>& part_list,
    url_pattern_compile_component_options& options) {
  // Let result be the empty string.
  std::string result{};
  // Let index list be the result of getting the indices for part list.
  // For each index of index list:
  for (size_t index = 0; index < part_list.size(); index++) {
    // Let part be part list[index].
    // Use reference to avoid copy
    const auto& part = part_list[index];
    // Let previous part be part list[index - 1] if index is greater than 0,
    // otherwise let it be null.
    // Use pointer to avoid copy
    const url_pattern_part* previous_part =
        index == 0 ? nullptr : &part_list[index - 1];
    // Let next part be part list[index + 1] if index is less than index list's
    // size - 1, otherwise let it be null.
    const url_pattern_part* next_part =
        index < part_list.size() - 1 ? &part_list[index + 1] : nullptr;
    // If part's type is "fixed-text" then:
    if (part.type == url_pattern_part_type::FIXED_TEXT) {
      // If part's modifier is "none" then:
      if (part.modifier == url_pattern_part_modifier::none) {
        // Append the result of running escape a pattern string given part's
        // value to the end of result.
        result.append(escape_pattern_string(part.value));
        continue;
      }
      // Append "{" to the end of result.
      result += "{";
      // Append the result of running escape a pattern string given part's value
      // to the end of result.
      result.append(escape_pattern_string(part.value));
      // Append "}" to the end of result.
      result += "}";
      // Append the result of running convert a modifier to a string given
      // part's modifier to the end of result.
      result.append(convert_modifier_to_string(part.modifier));
      continue;
    }
    // Let custom name be true if part's name[0] is not an ASCII digit;
    // otherwise false.
    bool custom_name = !unicode::is_ascii_digit(part.name[0]);
    // Let needs grouping be true if at least one of the following are true,
    // otherwise let it be false:
    // - part's suffix is not the empty string.
    // - part's prefix is not the empty string and is not options's prefix code
    // point.
    bool needs_grouping =
        !part.suffix.empty() ||
        (!part.prefix.empty() && (options.get_prefix().empty() ||
                                  part.prefix[0] != options.get_prefix()[0]));

    // If all of the following are true:
    // - needs grouping is false; and
    // - custom name is true; and
    // - part's type is "segment-wildcard"; and
    // - part's modifier is "none"; and
    // - next part is not null; and
    // - next part's prefix is the empty string; and
    // - next part's suffix is the empty string
    if (!needs_grouping && custom_name &&
        part.type == url_pattern_part_type::SEGMENT_WILDCARD &&
        part.modifier == url_pattern_part_modifier::none && next_part &&
        next_part->prefix.empty() && next_part->suffix.empty()) {
      // If next part's type is "fixed-text":
      if (next_part->type == url_pattern_part_type::FIXED_TEXT) {
        // Set needs grouping to true if the result of running is a valid name
        // code point given next part's value's first code point and the boolean
        // false is true.
        if (idna::valid_name_code_point(next_part->value[0], false)) {
          needs_grouping = true;
        }
      } else {
        // Set needs grouping to true if next part's name[0] is an ASCII digit.
        needs_grouping = !next_part->name.empty() &&
                         unicode::is_ascii_digit(next_part->name[0]);
      }
    }

    // If all of the following are true:
    // - needs grouping is false; and
    // - part's prefix is the empty string; and
    // - previous part is not null; and
    // - previous part's type is "fixed-text"; and
    // - previous part's value's last code point is options's prefix code point.
    // then set needs grouping to true.
    if (!needs_grouping && part.prefix.empty() && previous_part &&
        previous_part->type == url_pattern_part_type::FIXED_TEXT &&
        !previous_part->value.empty() && !options.get_prefix().empty() &&
        previous_part->value.back() == options.get_prefix()[0]) {
      needs_grouping = true;
    }

    // Assert: part's name is not the empty string or null.
    ADA_ASSERT_TRUE(!part.name.empty());

    // If needs grouping is true, then append "{" to the end of result.
    if (needs_grouping) {
      result.append("{");
    }

    // Append the result of running escape a pattern string given part's prefix
    // to the end of result.
    result.append(escape_pattern_string(part.prefix));

    // If custom name is true:
    if (custom_name) {
      // Append ":" to the end of result.
      result.append(":");
      // Append part's name to the end of result.
      result.append(part.name);
    }

    // If part's type is "regexp" then:
    if (part.type == url_pattern_part_type::REGEXP) {
      // Append "(" to the end of result.
      result.append("(");
      // Append part's value to the end of result.
      result.append(part.value);
      // Append ")" to the end of result.
      result.append(")");
    } else if (part.type == url_pattern_part_type::SEGMENT_WILDCARD &&
               !custom_name) {
      // Otherwise if part's type is "segment-wildcard" and custom name is
      // false: Append "(" to the end of result.
      result.append("(");
      // Append the result of running generate a segment wildcard regexp given
      // options to the end of result.
      result.append(generate_segment_wildcard_regexp(options));
      // Append ")" to the end of result.
      result.append(")");
    } else if (part.type == url_pattern_part_type::FULL_WILDCARD) {
      // Otherwise if part's type is "full-wildcard":
      // If custom name is false and one of the following is true:
      // - previous part is null; or
      // - previous part's type is "fixed-text"; or
      // - previous part's modifier is not "none"; or
      // - needs grouping is true; or
      // - part's prefix is not the empty string
      // - then append "*" to the end of result.
      if (!custom_name &&
          (!previous_part ||
           previous_part->type == url_pattern_part_type::FIXED_TEXT ||
           previous_part->modifier != url_pattern_part_modifier::none ||
           needs_grouping || !part.prefix.empty())) {
        result.append("*");
      } else {
        // Append "(" to the end of result.
        // Append full wildcard regexp value to the end of result.
        // Append ")" to the end of result.
        result.append("(.*)");
      }
    }

    // If all of the following are true:
    // - part's type is "segment-wildcard"; and
    // - custom name is true; and
    // - part's suffix is not the empty string; and
    // - The result of running is a valid name code point given part's suffix's
    // first code point and the boolean false is true then append U+005C (\) to
    // the end of result.
    if (part.type == url_pattern_part_type::SEGMENT_WILDCARD && custom_name &&
        !part.suffix.empty() &&
        idna::valid_name_code_point(part.suffix[0], false)) {
      result.append("\\");
    }

    // Append the result of running escape a pattern string given part's suffix
    // to the end of result.
    result.append(escape_pattern_string(part.suffix));
    // If needs grouping is true, then append "}" to the end of result.
    if (needs_grouping) result.append("}");
    // Append the result of running convert a modifier to a string given part's
    // modifier to the end of result.
    result.append(convert_modifier_to_string(part.modifier));
  }
  // Return result.
  return result;
}
}  // namespace ada::url_pattern_helpers

#endif  // ADA_INCLUDE_URL_PATTERN
/* end file src/url_pattern_helpers.cpp */
/* begin file src/url_pattern_regex.cpp */
#if ADA_INCLUDE_URL_PATTERN


namespace ada::url_pattern_regex {

#ifdef ADA_USE_UNSAFE_STD_REGEX_PROVIDER
inline std::optional<std::regex> std_regex_provider::create_instance(
    std::string_view pattern, bool ignore_case) {
  // Let flags be an empty string.
  // If options's ignore case is true then set flags to "vi".
  // Otherwise set flags to "v"
  auto flags = ignore_case
                   ? std::regex::icase | std::regex_constants::ECMAScript
                   : std::regex_constants::ECMAScript;
  try {
    return std::regex(pattern.data(), pattern.size(), flags);
  } catch (const std::regex_error& e) {
    (void)e;
    ada_log("std_regex_provider::create_instance failed:", e.what());
    return std::nullopt;
  }
}

inline std::optional<std::vector<std::optional<std::string>>>
std_regex_provider::regex_search(std::string_view input,
                                 const std::regex& pattern) {
  // Use iterator-based regex_search to avoid string allocation
  std::match_results<std::string_view::const_iterator> match_result;
  try {
    if (!std::regex_search(input.begin(), input.end(), match_result, pattern,
                           std::regex_constants::match_any)) {
      return std::nullopt;
    }
  } catch (const std::regex_error& e) {
    (void)e;
    ada_log("std_regex_provider::regex_search failed:", e.what());
    return std::nullopt;
  }
  std::vector<std::optional<std::string>> matches;
  // An empty input can still match with capture groups (e.g. "(x*)" or an
  // optional ":a?" against ""), so the group values must be extracted here
  // just like for a non-empty input. A successful regex_search always leaves
  // the full match at index 0, so match_result is never empty at this point.
  if (match_result.empty()) {
    return matches;
  }
  matches.reserve(match_result.size());
  for (size_t i = 1; i < match_result.size(); ++i) {
    if (auto entry = match_result[i]; entry.matched) {
      matches.emplace_back(entry.str());
    } else {
      // A capture group that did not participate in the match is undefined,
      // not absent. Emitting nullopt keeps the result aligned by position with
      // the component's group name list; dropping it shifts every later group
      // onto the wrong name.
      matches.emplace_back(std::nullopt);
    }
  }
  return matches;
}

inline bool std_regex_provider::regex_match(std::string_view input,
                                     const std::regex& pattern) {
  try {
    return std::regex_match(input.begin(), input.end(), pattern);
  } catch (const std::regex_error& e) {
    (void)e;
    ada_log("std_regex_provider::regex_match failed:", e.what());
    return false;
  }
}

#endif  // ADA_USE_UNSAFE_STD_REGEX_PROVIDER

}  // namespace ada::url_pattern_regex

#endif  // ADA_INCLUDE_URL_PATTERN
/* end file src/url_pattern_regex.cpp */
namespace ada {
template <url_pattern_regex::regex_concept regex_provider>
ada_warn_unused tl::expected<url_pattern<regex_provider>, errors>
parse_url_pattern(std::variant<std::string_view, url_pattern_init>&& input,
                  const std::string_view* base_url = nullptr,
                  const url_pattern_options* options = nullptr) {
  return parser::parse_url_pattern_impl<regex_provider>(std::move(input),
                                                        base_url, options);
}
}  // namespace ada

#endif  // VBIND_ADA_URL_PATTERN_H
