/* lz4 suite. One driver, written against liblz4's API (lz4.h, lz4frame.h),
 * linked once with liblz4 and once with vlz4's C ABI (feature lz4-abi), so
 * the only thing that differs between the two runners is the library.
 *
 *   lz4 decompress        decompress/FILE: LZ4_decompress_safe of FILE as
 *                         one block
 *   lz4 compress          compress/FILE: LZ4_compress_default of FILE as one
 *                         block (the check value is the compressed size)
 *   lz4 frame-decompress  frame-decompress/FILE: LZ4F_decompress of FILE as
 *                         one frame, input and output buffers whole
 *   lz4 frame-compress    frame-compress/FILE: LZ4F_compressFrame of FILE
 *                         with default preferences
 *   lz4 prepare DIR       writes DIR/lz4/FILE.block and FILE.frame, which
 *                         the decompress cases read. The build runs this
 *                         with liblz4's runner, so both contenders decode
 *                         what liblz4 wrote.
 *
 * Inputs are the files in $VBENCH_DATA. Every case's output is checked
 * against the original file before anything is timed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <lz4.h>
#include <lz4frame.h>
#include "runner.h"

struct item {
    unsigned char *in;
    size_t in_len;
    unsigned char *out;
    size_t out_cap;
    LZ4F_dctx *dctx;
};

/* A cheap digest of the output, so the check value depends on the bytes
 * and not only on their count. */
static uint64_t mix(uint64_t h, const unsigned char *p, size_t n)
{
    size_t step = n / 64 + 1;
    for (size_t i = 0; i < n; i += step) h = (h ^ p[i]) * 0x100000001b3ull;
    return h;
}

static uint64_t do_decompress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    int n = LZ4_decompress_safe((const char *)it->in, (char *)it->out, (int)it->in_len, (int)it->out_cap);
    if (n < 0) abort();
    return mix((uint64_t)n, it->out, (size_t)n);
}

static uint64_t do_compress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    int n = LZ4_compress_default((const char *)it->in, (char *)it->out, (int)it->in_len, (int)it->out_cap);
    if (n <= 0) abort();
    return (uint64_t)n;
}

static uint64_t do_frame_decompress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t ip = 0, op = 0, r = 1;
    while (r != 0) {
        size_t dn = it->out_cap - op, sn = it->in_len - ip;
        r = LZ4F_decompress(it->dctx, it->out + op, &dn, it->in + ip, &sn, NULL);
        if (LZ4F_isError(r)) abort();
        if (dn == 0 && sn == 0 && r != 0) abort();
        ip += sn;
        op += dn;
    }
    return mix(op, it->out, op);
}

static uint64_t do_frame_compress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t n = LZ4F_compressFrame(it->out, it->out_cap, it->in, it->in_len, NULL);
    if (LZ4F_isError(n)) abort();
    return n;
}

static void write_file(const char *p, const unsigned char *b, size_t n)
{
    FILE *f = fopen(p, "wb");
    if (!f || fwrite(b, 1, n, f) != n || fclose(f)) { perror(p); exit(1); }
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "decompress";
    char **names;
    if (!strcmp(mode, "prepare")) {
        const char *dir = argv[2];
        size_t n = vb_list_dir(dir, &names);
        char p[4096];
        snprintf(p, sizeof p, "%s/lz4", dir);
        mkdir(p, 0777);
        for (size_t i = 0; i < n; i++) {
            size_t len;
            snprintf(p, sizeof p, "%s/%s", dir, names[i]);
            unsigned char *b = vb_read_file(p, &len);
            size_t cap = LZ4F_compressFrameBound(len, NULL);
            unsigned char *c = (unsigned char *)malloc(cap);
            int m = LZ4_compress_default((const char *)b, (char *)c, (int)len, (int)cap);
            if (m <= 0) abort();
            snprintf(p, sizeof p, "%s/lz4/%s.block", dir, names[i]);
            write_file(p, c, (size_t)m);
            size_t fm = LZ4F_compressFrame(c, cap, b, len, NULL);
            if (LZ4F_isError(fm)) abort();
            snprintf(p, sizeof p, "%s/lz4/%s.frame", dir, names[i]);
            write_file(p, c, fm);
            free(b);
            free(c);
        }
        fprintf(stderr, "prepared %zu files with %s\n", n, LZ4_versionString());
        return 0;
    }
    const char *dir = vb_data_dir();
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        size_t len;
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        unsigned char *orig = vb_read_file(p, &len);
        struct item *it = (struct item *)calloc(1, sizeof *it);
        uint64_t (*fn)(void *);
        if (!strcmp(mode, "decompress") || !strcmp(mode, "frame-decompress")) {
            int frame = mode[0] == 'f';
            snprintf(p, sizeof p, "%s/lz4/%s.%s", dir, names[i], frame ? "frame" : "block");
            it->in = vb_read_file(p, &it->in_len);
            it->out_cap = len + 1;
            it->out = (unsigned char *)malloc(it->out_cap);
            if (frame && LZ4F_isError(LZ4F_createDecompressionContext(&it->dctx, LZ4F_VERSION))) abort();
            fn = frame ? do_frame_decompress : do_decompress;
            memset(it->out, 0, it->out_cap);
            fn(it);
            if (memcmp(it->out, orig, len) || it->out[len] != 0) {
                fprintf(stderr, "%s of %s does not give the original\n", mode, names[i]);
                return 1;
            }
        } else {
            int frame = mode[0] == 'f';
            it->in = orig;
            it->in_len = len;
            it->out_cap = frame ? LZ4F_compressFrameBound(len, NULL) : (size_t)LZ4_compressBound((int)len);
            it->out = (unsigned char *)malloc(it->out_cap);
            fn = frame ? do_frame_compress : do_compress;
            size_t m = (size_t)fn(it);
            /* Round trip through the same library. */
            struct item back = {it->out, m, (unsigned char *)malloc(len + 1), len + 1, NULL};
            if (frame) {
                if (LZ4F_isError(LZ4F_createDecompressionContext(&back.dctx, LZ4F_VERSION))) abort();
                do_frame_decompress(&back);
                LZ4F_freeDecompressionContext(back.dctx);
            } else if ((size_t)LZ4_decompress_safe((const char *)back.in, (char *)back.out, (int)m, (int)len) != len) {
                abort();
            }
            if (memcmp(back.out, orig, len)) {
                fprintf(stderr, "%s of %s does not round-trip\n", mode, names[i]);
                return 1;
            }
            free(back.out);
        }
        snprintf(cname, sizeof cname, "%s/%s", mode, names[i]);
        vb_case(cname, len, fn, it);
    }
    return vb_main();
}
