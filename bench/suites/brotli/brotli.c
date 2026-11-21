/* brotli suite. One driver, written against google/brotli's decoder API
 * (brotli/decode.h), linked once with libbrotlidec and once with vbrotli's
 * C ABI (feature brotli-abi), so the only thing that differs between the two
 * runners is the library.
 *
 *   decode-qQ/FILE          decompress FILE.qQ.br (made by google/brotli's
 *                           encoder at quality Q, window 22) in one
 *                           BrotliDecoderDecompress call
 *   decode-chunked-qQ/FILE  the same through BrotliDecoderDecompressStream,
 *                           fed 1 KB of input per call into a 16 KB output
 *                           buffer (how a Node zlib stream drives it)
 *
 * Inputs are the files in $VBENCH_DATA; the .br files, made by mkbr.c during
 * the build, are in $VBENCH_DATA/br. Every case's output is compared with
 * the original file before anything is timed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <brotli/decode.h>
#include "runner.h"

struct item {
    unsigned char *in;
    size_t in_len;
    unsigned char *out;
    size_t out_cap;
};

/* A cheap digest of the output so far, so the check value depends on the
 * bytes and not only on their count. */
static uint64_t mix(uint64_t h, const unsigned char *p, size_t n)
{
    size_t step = n / 64 + 1;
    for (size_t i = 0; i < n; i += step) h = (h ^ p[i]) * 0x100000001b3ull;
    return h;
}

static uint64_t do_decode(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t n = it->out_cap;
    if (BrotliDecoderDecompress(it->in_len, it->in, &n, it->out) != BROTLI_DECODER_RESULT_SUCCESS) abort();
    return mix(n, it->out, n);
}

static uint64_t do_decode_chunked(void *ctx)
{
    struct item *it = (struct item *)ctx;
    BrotliDecoderState *s = BrotliDecoderCreateInstance(0, 0, 0);
    if (!s) abort();
    size_t p = 0, total = 0;
    uint64_t h = 0;
    BrotliDecoderResult r = BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT;
    while (r != BROTLI_DECODER_RESULT_SUCCESS) {
        if (p >= it->in_len) abort();
        size_t m = it->in_len - p < 1024 ? it->in_len - p : 1024;
        const uint8_t *next_in = it->in + p;
        size_t avail_in = m;
        p += m;
        do {
            uint8_t *next_out = it->out;
            size_t avail_out = 16384;
            r = BrotliDecoderDecompressStream(s, &avail_in, &next_in, &avail_out, &next_out, 0);
            if (r == BROTLI_DECODER_RESULT_ERROR) abort();
            size_t got = 16384 - avail_out;
            /* Every 61st byte of the whole output, wherever the pieces end
             * (the two libraries may cut them differently). */
            for (size_t j = (61 - total % 61) % 61; j < got; j += 61) h = (h ^ it->out[j]) * 0x100000001b3ull;
            total += got;
        } while (r == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT);
        if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT && avail_in != 0) abort();
    }
    BrotliDecoderDestroyInstance(s);
    return total ^ (h << 20);
}

int main(void)
{
    static const int qualities[] = {5, 11};
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        size_t len;
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        unsigned char *orig = vb_read_file(p, &len);
        for (int k = 0; k < 2; k++) {
            int q = qualities[k];
            struct item *it = (struct item *)calloc(1, sizeof *it);
            snprintf(p, sizeof p, "%s/br/%s.q%d.br", dir, names[i], q);
            it->in = vb_read_file(p, &it->in_len);
            it->out_cap = len + 1;
            it->out = (unsigned char *)malloc(it->out_cap);
            size_t got = it->out_cap;
            if (BrotliDecoderDecompress(it->in_len, it->in, &got, it->out) != BROTLI_DECODER_RESULT_SUCCESS ||
                got != len || memcmp(it->out, orig, len)) {
                fprintf(stderr, "decoding %s.q%d.br does not give the original\n", names[i], q);
                return 1;
            }
            snprintf(cname, sizeof cname, "decode-q%d/%s", q, names[i]);
            vb_case(cname, len, do_decode, it);

            struct item *ci = (struct item *)calloc(1, sizeof *ci);
            ci->in = it->in;
            ci->in_len = it->in_len;
            ci->out = (unsigned char *)malloc(16384);
            if ((do_decode_chunked(ci) & 0xfffff) != (len & 0xfffff)) {
                fprintf(stderr, "chunked decoding of %s.q%d.br gives the wrong length\n", names[i], q);
                return 1;
            }
            snprintf(cname, sizeof cname, "decode-chunked-q%d/%s", q, names[i]);
            vb_case(cname, len, do_decode_chunked, ci);
        }
    }
    return vb_main();
}
