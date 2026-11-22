/* The C API against the system's ICU 74: unorm2_normalize on 64 KB of
 * UTF-16 text, and uidna_nameToASCII_UTF8 per call. Best of 15 runs.
 *
 *   cargo build --release
 *   cc -O2 -Iinclude bench/c/capi_bench.c target/release/libverilith_text.a \
 *      /usr/lib/x86_64-linux-gnu/libicuuc.so.74 -lm -lpthread -ldl -o capi_bench
 */
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include "vtext_icu.h"

const void *unorm2_getNFCInstance_74(int32_t *);
const void *unorm2_getNFDInstance_74(int32_t *);
int32_t unorm2_normalize_74(const void *, const uint16_t *, int32_t, uint16_t *, int32_t, int32_t *);
void *uidna_openUTS46_74(uint32_t, int32_t *);
int32_t uidna_nameToASCII_UTF8_74(const void *, const char *, int32_t, char *, int32_t, vtext_UIDNAInfo *, int32_t *);

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static uint16_t src[32768], dst[100000];

/* Repeats UTF-8 `unit` as UTF-16 up to 32K code units. */
static int fill(const char *unit) {
    int n = 0;
    while (n < 32000) {
        const unsigned char *p = (const unsigned char *)unit;
        while (*p && n < 32000) {
            uint32_t c = *p++;
            if (c >= 0xC0) {
                int k = c >= 0xF0 ? 3 : c >= 0xE0 ? 2 : 1;
                c &= k == 3 ? 7 : k == 2 ? 0xF : 0x1F;
                while (k--) c = (c << 6) | (*p++ & 0x3F);
            }
            src[n++] = (uint16_t)c;
        }
    }
    return n;
}

int main(void) {
    static const char *samples[][2] = {
        {"ASCII", "The quick brown fox jumps over the lazy dog. 0123456789 "},
        {"French", "Le c\xc5\x93ur d\xc3\xa9\xc3\xa7u mais l'\xc3\xa2me plut\xc3\xb4t na\xc3\xafve, Lou\xc3\xbfs r\xc3\xaava de crapa\xc3\xbcter en cano\xc3\xab au del\xc3\xa0 des \xc3\xaeles. "},
        {"Vietnamese", "Ti\xe1\xba\xbfng Vi\xe1\xbb\x87t l\xc3\xa0 ng\xc3\xb4n ng\xe1\xbb\xaf ch\xc3\xadnh th\xe1\xbb\xa9\x63 c\xe1\xbb\xa7\x61 Vi\xe1\xbb\x87t Nam. "},
        {"Greek", "\xe1\xbc\x98\xce\xbd \xe1\xbc\x80\xcf\x81\xcf\x87\xe1\xbf\x87 \xe1\xbc\xa6\xce\xbd \xe1\xbd\x81 \xce\xbb\xe1\xbd\xb9\xce\xb3\xce\xbf\xcf\x82. "},
        {"Korean", "\xeb\xaa\xa8\xeb\x93\xa0 \xec\x9d\xb8\xea\xb0\x84\xec\x9d\x80 \xed\x83\x9c\xec\x96\xb4\xeb\x82\xa0 \xeb\x95\x8c\xeb\xb6\x80\xed\x84\xb0 \xec\x9e\x90\xec\x9c\xa0\xeb\xa1\x9c\xec\x9a\xb0\xeb\xa9\xb0. "},
    };
    int32_t e = 0;
    const void *icu[2] = {unorm2_getNFCInstance_74(&e), unorm2_getNFDInstance_74(&e)};
    const vtext_UNormalizer2 *vt[2] = {vtext_unorm2_getNFCInstance(&e), vtext_unorm2_getNFDInstance(&e)};
    printf("unorm2_normalize, 64 KB of UTF-16, GB/s (ICU 74 / vtext)\n");
    for (unsigned s = 0; s < sizeof samples / sizeof samples[0]; s++) {
        int n = fill(samples[s][1]);
        printf("  %-10s", samples[s][0]);
        for (int f = 0; f < 2; f++) {
            double best[2] = {1e9, 1e9};
            for (int r = 0; r < 15; r++) {
                double t = now();
                for (int i = 0; i < 20; i++) { e = 0; unorm2_normalize_74(icu[f], src, n, dst, 100000, &e); }
                t = now() - t;
                if (t < best[0]) best[0] = t;
                t = now();
                for (int i = 0; i < 20; i++) { e = 0; vtext_unorm2_normalize(vt[f], src, n, dst, 100000, &e); }
                t = now() - t;
                if (t < best[1]) best[1] = t;
            }
            printf("  %s %5.2f / %5.2f", f ? "NFD" : "NFC", 40.0 * n / best[0] / 1e9, 40.0 * n / best[1] / 1e9);
        }
        printf("\n");
    }
    void *ui = uidna_openUTS46_74(0x30, &e);
    vtext_UIDNA *vi = vtext_uidna_openUTS46(0x30, &e);
    static const char *names[] = {"www.example.com", "WWW.Example.COM", "m\xc3\xbcnchen.de",
                                  "\xe4\xbe\x8b\xe5\xad\x90.\xe6\xb5\x8b\xe8\xaf\x95"};
    printf("uidna_nameToASCII_UTF8 (nontransitional), ns per call (ICU 74 / vtext)\n");
    for (unsigned k = 0; k < sizeof names / sizeof names[0]; k++) {
        char out[256];
        double best[2] = {1e9, 1e9};
        for (int r = 0; r < 15; r++) {
            vtext_UIDNAInfo info = {sizeof info};
            double t = now();
            for (int i = 0; i < 100000; i++) { e = 0; uidna_nameToASCII_UTF8_74(ui, names[k], -1, out, 256, &info, &e); }
            t = now() - t;
            if (t < best[0]) best[0] = t;
            t = now();
            for (int i = 0; i < 100000; i++) { e = 0; vtext_uidna_nameToASCII_UTF8(vi, names[k], -1, out, 256, &info, &e); }
            t = now() - t;
            if (t < best[1]) best[1] = t;
        }
        printf("  %-16s %5.0f / %5.0f\n", names[k], best[0] * 1e4, best[1] * 1e4);
    }
    return 0;
}
