/* Differential test of vtext's ICU-shaped C API against the system's ICU.
 *
 *   cargo build --profile release-fat
 *   cc -O2 -Iinclude tests/c/icu_diff.c target/release-fat/libverilith_text.a \
 *      /usr/lib/x86_64-linux-gnu/libicuuc.so.74 -lm -lpthread -ldl -o icu_diff
 *   ./icu_diff [iterations]
 *
 * ICU's headers are not needed: the few functions used are declared below
 * under their versioned names (ICU 74 here; set ICU_SUFFIX for another).
 * ICU 74 implements Unicode 15.1, and vtext Unicode 18.0, so inputs are
 * limited to characters assigned by 15.1. Before the random tests, every such
 * character is run through both on its own, and the ones that differ (IDNA
 * data that changed after 15.1) are printed and left out of the random
 * inputs. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vtext_icu.h"

#ifndef ICU_SUFFIX
#define ICU_SUFFIX _74
#endif
#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)
#define ICU(f) CAT(f, ICU_SUFFIX)

typedef void UNormalizer2;
typedef void UIDNA;
typedef uint8_t UVersionInfo[4];
const UNormalizer2 *ICU(unorm2_getNFCInstance)(int32_t *);
const UNormalizer2 *ICU(unorm2_getNFDInstance)(int32_t *);
const UNormalizer2 *ICU(unorm2_getNFKCInstance)(int32_t *);
const UNormalizer2 *ICU(unorm2_getNFKDInstance)(int32_t *);
int32_t ICU(unorm2_normalize)(const UNormalizer2 *, const uint16_t *, int32_t, uint16_t *, int32_t, int32_t *);
int8_t ICU(unorm2_isNormalized)(const UNormalizer2 *, const uint16_t *, int32_t, int32_t *);
UIDNA *ICU(uidna_openUTS46)(uint32_t, int32_t *);
void ICU(uidna_close)(UIDNA *);
int32_t ICU(uidna_nameToASCII)(const UIDNA *, const uint16_t *, int32_t, uint16_t *, int32_t, vtext_UIDNAInfo *, int32_t *);
int32_t ICU(uidna_nameToUnicode)(const UIDNA *, const uint16_t *, int32_t, uint16_t *, int32_t, vtext_UIDNAInfo *, int32_t *);
int32_t ICU(uidna_nameToASCII_UTF8)(const UIDNA *, const char *, int32_t, char *, int32_t, vtext_UIDNAInfo *, int32_t *);
void ICU(u_charAge)(int32_t, UVersionInfo);

static uint64_t rng = 0x9e3779b97f4a7c15ull;
static uint32_t rnd(uint32_t n) {
    rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
    return (uint32_t)(rng % n);
}

static uint8_t changed[0x110000];

static int assigned_by_15_1(int32_t c) {
    UVersionInfo v;
    ICU(u_charAge)(c, v);
    if (v[0] == 0 && v[1] == 0) return 0;
    return v[0] < 15 || (v[0] == 15 && v[1] <= 1);
}

/* A code point drawn from ranges where normalization and IDNA do something. */
static int32_t pick(void) {
    static const int32_t ranges[][2] = {
        {'a', 'z'}, {'A', 'Z'}, {'0', '9'}, {'-', '.'}, {0x00A0, 0x024F}, {0x0300, 0x036F},
        {0x0370, 0x03FF}, {0x0590, 0x05FF}, {0x0600, 0x06FF}, {0x0900, 0x097F},
        {0x0E00, 0x0E7F}, {0x0F00, 0x0FFF}, {0x1100, 0x11FF}, {0x1E00, 0x1FFF},
        {0x200C, 0x200D}, {0x2100, 0x24FF}, {0x3000, 0x30FF}, {0x3130, 0x33FF},
        {0xAC00, 0xD7A3}, {0xF900, 0xFAFF}, {0xFB00, 0xFDFF}, {0xFE00, 0xFFEF},
        {0x1D100, 0x1D7FF}, {0x1F100, 0x1F2FF}, {0x2F800, 0x2FA1F}, {0, 0x10FFFF},
    };
    for (;;) {
        const int32_t *r = ranges[rnd(sizeof ranges / sizeof ranges[0])];
        int32_t c = r[0] + (int32_t)rnd((uint32_t)(r[1] - r[0] + 1));
        if (c >= 0xD800 && c <= 0xDFFF) continue;
        if (c == 0) continue;
        if (assigned_by_15_1(c) && !changed[c]) return c;
    }
}

static int put16(uint16_t *s, int n, int32_t c) {
    if (c < 0x10000) { s[n] = (uint16_t)c; return n + 1; }
    c -= 0x10000;
    s[n] = (uint16_t)(0xD800 + (c >> 10));
    s[n + 1] = (uint16_t)(0xDC00 + (c & 0x3FF));
    return n + 2;
}

static int has_deviation(const uint16_t *s, int n) {
    for (int i = 0; i < n; i++)
        if (s[i] == 0x200C || s[i] == 0x200D || s[i] == 0x00DF || s[i] == 0x03C2) return 1;
    return 0;
}

/* Whether vtext's ToUnicode of s has a character that ICU 74 does not know
 * or that changed since. */
static int decodes_to_newer(const vtext_UIDNA *idna, const uint16_t *s, int n) {
    uint16_t u[512];
    vtext_UIDNAInfo info = {sizeof info};
    int32_t e = 0;
    int32_t m = vtext_uidna_nameToUnicode(idna, s, n, u, 512, &info, &e);
    for (int i = 0; i < m && i < 512; i++) {
        int32_t c = u[i];
        if (c >= 0xD800 && c < 0xDC00 && i + 1 < m) c = 0x10000 + ((c - 0xD800) << 10) + (u[++i] - 0xDC00);
        if (!(c >= 0xD800 && c <= 0xDFFF) && (!assigned_by_15_1(c) || changed[c])) return 1;
    }
    return 0;
}

static void show(const char *what, const uint16_t *s, int n) {
    fprintf(stderr, "%s:", what);
    for (int i = 0; i < n; i++) fprintf(stderr, " %04X", s[i]);
    fprintf(stderr, "\n");
}

int main(int argc, char **argv) {
    long iters = argc > 1 ? atol(argv[1]) : 200000;
    int32_t e = 0;
    const UNormalizer2 *icu_n[4] = {ICU(unorm2_getNFCInstance)(&e), ICU(unorm2_getNFDInstance)(&e),
                                   ICU(unorm2_getNFKCInstance)(&e), ICU(unorm2_getNFKDInstance)(&e)};
    const vtext_UNormalizer2 *vt_n[4] = {vtext_unorm2_getNFCInstance(&e), vtext_unorm2_getNFDInstance(&e),
                                         vtext_unorm2_getNFKCInstance(&e), vtext_unorm2_getNFKDInstance(&e)};
    static const uint32_t idna_opts[] = {
        0,
        VTEXT_UIDNA_NONTRANSITIONAL_TO_ASCII | VTEXT_UIDNA_NONTRANSITIONAL_TO_UNICODE,
        VTEXT_UIDNA_NONTRANSITIONAL_TO_ASCII | VTEXT_UIDNA_NONTRANSITIONAL_TO_UNICODE |
            VTEXT_UIDNA_CHECK_BIDI | VTEXT_UIDNA_CHECK_CONTEXTJ,
        0x3E,
    };
    enum { NOPTS = sizeof idna_opts / sizeof idna_opts[0] };
    UIDNA *icu_i[NOPTS];
    vtext_UIDNA *vt_i[NOPTS];
    for (int k = 0; k < NOPTS; k++) {
        icu_i[k] = ICU(uidna_openUTS46)(idna_opts[k], &e);
        vt_i[k] = vtext_uidna_openUTS46(idna_opts[k], &e);
    }
    if (e > 0) { fprintf(stderr, "setup failed: %d\n", e); return 2; }

    long nchanged = 0, idna_bad = 0;
    /* Single characters. */
    for (int32_t c = 1; c < 0x110000; c++) {
        if ((c >= 0xD800 && c <= 0xDFFF) || !assigned_by_15_1(c)) continue;
        uint16_t one[2], a1[64], b1[64];
        int n1 = put16(one, 0, c);
        for (int f = 0; f < 4; f++) {
            int32_t ea = 0, eb = 0;
            int32_t la = ICU(unorm2_normalize)(icu_n[f], one, n1, a1, 64, &ea);
            int32_t lb = vtext_unorm2_normalize(vt_n[f], one, n1, b1, 64, &eb);
            if (la != lb || memcmp(a1, b1, 2 * (size_t)la)) {
                fprintf(stderr, "normalize form %d of U+%04X differs\n", f, c);
                changed[c] = 2;
            }
        }
        /* Alone, and after an "a" (so a character mapped to nothing is seen). */
        uint16_t two[3] = {'a'};
        put16(two, 1, c);
        for (int k = 0; k < 2 * NOPTS; k++) {
            const uint16_t *in = k < NOPTS ? one : two;
            int nin = k < NOPTS ? n1 : n1 + 1;
            vtext_UIDNAInfo ia = {sizeof ia}, ib = {sizeof ib};
            int32_t ea = 0, eb = 0;
            int32_t la = ICU(uidna_nameToUnicode)(icu_i[k % NOPTS], in, nin, a1, 64, &ia, &ea);
            int32_t lb = vtext_uidna_nameToUnicode(vt_i[k % NOPTS], in, nin, b1, 64, &ib, &eb);
            if ((ia.errors == 0) != (ib.errors == 0) || (ia.errors == 0 && (la != lb || memcmp(a1, b1, 2 * (size_t)la))))
                changed[c] |= 1;
        }
        if (changed[c] && c < 0x80) {
            fprintf(stderr, "ASCII U+%04X differs on its own\n", c);
            idna_bad++;
        }
        if (changed[c] == 1) {
            if (nchanged < 400) printf("%s%04X", nchanged % 16 ? " " : "\n  ", c);
            nchanged++;
        }
    }
    printf("\nIDNA differs on %ld single characters (shown above, data changed after Unicode 15.1)\n", nchanged);

    long newer_punycode = 0, icu_deviation_ace = 0, icu_utf16_hyphens = 0, norm_bad = 0, norm_checks = 0, idna_checks = 0, err_bits_same = 0, err_cases = 0;
    uint16_t s[64], a[512], b[512];
    for (long it = 0; it < iters; it++) {
        int n = 0, len = 1 + (int)rnd(12);
        int domain = rnd(2);
        if (domain && rnd(8) == 0) { s[n++] = 'x'; s[n++] = 'n'; s[n++] = '-'; s[n++] = '-'; }
        for (int i = 0; i < len && n < 60; i++) {
            if (domain && rnd(5) == 0) s[n++] = '.';
            else if (!domain && rnd(40) == 0) s[n++] = (uint16_t)(0xDC00 + rnd(0x400)); /* an unpaired low surrogate */
            else n = put16(s, n, pick());
        }

        for (int f = 0; f < 4; f++) {
            int32_t ea = 0, eb = 0;
            int32_t la = ICU(unorm2_normalize)(icu_n[f], s, n, a, 512, &ea);
            int32_t lb = vtext_unorm2_normalize(vt_n[f], s, n, b, 512, &eb);
            int8_t qa = ICU(unorm2_isNormalized)(icu_n[f], s, n, &ea);
            int8_t qb = vtext_unorm2_isNormalized(vt_n[f], s, n, &eb);
            norm_checks++;
            if (la != lb || (ea > 0) != (eb > 0) || memcmp(a, b, 2 * (size_t)la) || qa != qb) {
                if (norm_bad++ < 10) {
                    fprintf(stderr, "normalize form %d differs (normalized icu %d vtext %d)\n", f, qa, qb);
                    show("  input", s, n); show("  icu  ", a, la); show("  vtext", b, lb);
                }
            }
        }

        for (int k = 0; k < NOPTS; k++) {
            for (int to_ascii = 0; to_ascii < 2; to_ascii++) {
                vtext_UIDNAInfo ia = {sizeof ia}, ib = {sizeof ib};
                int32_t ea = 0, eb = 0, la, lb;
                if (to_ascii) {
                    la = ICU(uidna_nameToASCII)(icu_i[k], s, n, a, 512, &ia, &ea);
                    lb = vtext_uidna_nameToASCII(vt_i[k], s, n, b, 512, &ib, &eb);
                } else {
                    la = ICU(uidna_nameToUnicode)(icu_i[k], s, n, a, 512, &ia, &ea);
                    lb = vtext_uidna_nameToUnicode(vt_i[k], s, n, b, 512, &ib, &eb);
                }
                idna_checks++;
                int oka = ia.errors == 0, okb = ib.errors == 0;
                if (!oka && !okb) {
                    err_cases++;
                    err_bits_same += ia.errors == ib.errors;
                }
                /* ICU checks for "--" in the third and fourth UTF-16 code
                 * units of a label, not code points as UTS #46 says, so the
                 * two differ when a supplementary character comes first. */
                if ((ia.errors == 0x20 && okb) || (ib.errors == 0x20 && oka)) { icu_utf16_hyphens++; continue; }
                /* A Punycode label can decode to characters added after 15.1. */
                if (oka != okb && decodes_to_newer(vt_i[k], s, n)) { newer_punycode++; continue; }
                /* With transitional processing, ICU checks an xn-- label for
                 * non-ASCII before mapping deviation characters away. */
                if (ia.errors == 0x400 && okb && !(idna_opts[k] & 0x30) && has_deviation(s, n)) { icu_deviation_ace++; continue; }
                if (oka != okb || (oka && (la != lb || memcmp(a, b, 2 * (size_t)la)))) {
                    if (idna_bad++ < 10) {
                        fprintf(stderr, "%s options %#x differs: icu errors %#x, vtext %#x\n",
                                to_ascii ? "nameToASCII" : "nameToUnicode", idna_opts[k], ia.errors, ib.errors);
                        show("  input", s, n); show("  icu  ", a, la); show("  vtext", b, lb);
                    }
                }
            }
        }
    }

    /* ICU conventions: preflighting, NUL termination, failure passthrough. */
    {
        static const uint16_t cafe[] = {'c', 'a', 'f', 'e', 0x0301, 0};
        int32_t ea = 0, eb = 0;
        int32_t la = ICU(unorm2_normalize)(icu_n[0], cafe, -1, NULL, 0, &ea);
        int32_t lb = vtext_unorm2_normalize(vt_n[0], cafe, -1, NULL, 0, &eb);
        if (la != lb || ea != eb) { fprintf(stderr, "preflight differs: %d/%d %d/%d\n", la, lb, ea, eb); norm_bad++; }
        ea = eb = 0;
        la = ICU(unorm2_normalize)(icu_n[0], cafe, -1, a, 4, &ea);
        lb = vtext_unorm2_normalize(vt_n[0], cafe, -1, b, 4, &eb);
        if (la != lb || ea != eb || memcmp(a, b, 8)) { fprintf(stderr, "exact fit differs: %d %d\n", ea, eb); norm_bad++; }
        ea = eb = 15;
        la = ICU(unorm2_normalize)(icu_n[0], cafe, -1, a, 512, &ea);
        lb = vtext_unorm2_normalize(vt_n[0], cafe, -1, b, 512, &eb);
        if (la != lb || ea != eb) { fprintf(stderr, "failure passthrough differs\n"); norm_bad++; }

        vtext_UIDNAInfo ia = {sizeof ia}, ib = {sizeof ib};
        char ca[64], cb[64];
        ea = eb = 0;
        la = ICU(uidna_nameToASCII_UTF8)(icu_i[1], "B\xc3\xbc" "cher.Example", -1, ca, 64, &ia, &ea);
        lb = vtext_uidna_nameToASCII_UTF8(vt_i[1], "B\xc3\xbc" "cher.Example", -1, cb, 64, &ib, &eb);
        if (la != lb || ea != eb || strcmp(ca, cb)) { fprintf(stderr, "UTF-8 ToASCII differs: %s %s\n", ca, cb); idna_bad++; }
    }

    printf("normalization: %ld checks, %ld differences\n", norm_checks, norm_bad);
    printf("idna: %ld checks, %ld differences; error bits equal in %ld of %ld error cases\n",
           idna_checks, idna_bad, err_bits_same, err_cases);
    printf("      %ld ICU HYPHEN_3_4 errors counted in UTF-16 units, skipped\n", icu_utf16_hyphens);
    printf("      %ld Punycode labels decoding to characters newer than ICU's data, skipped\n", newer_punycode);
    printf("      %ld ICU INVALID_ACE_LABEL errors from unmapped deviation characters, skipped\n", icu_deviation_ace);
    for (int k = 0; k < NOPTS; k++) { ICU(uidna_close)(icu_i[k]); vtext_uidna_close(vt_i[k]); }
    return norm_bad || idna_bad;
}
