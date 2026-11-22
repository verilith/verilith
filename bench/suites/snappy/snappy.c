/* snappy suite. One driver, written against google/snappy's C API
 * (snappy-c.h), linked once with libsnappy and once with vsnappy's C ABI
 * (feature snappy-abi), so the only thing that differs between the two
 * runners is the library.
 *
 *   snappy uncompress    uncompress/FILE: snappy_uncompress
 *   snappy validate      validate/FILE: snappy_validate_compressed_buffer
 *   snappy compress      compress/FILE: snappy_compress (the check value is
 *                        the compressed size)
 *   snappy prepare DIR   writes DIR/snappy/FILE.sz, which the uncompress
 *                        and validate cases read. The build runs this with
 *                        libsnappy's runner, so both contenders decode what
 *                        libsnappy wrote.
 *
 * Inputs are the files in $VBENCH_DATA. Every case's output is checked
 * against the original file before anything is timed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <snappy-c.h>
#include "runner.h"

struct item {
    unsigned char *in;
    size_t in_len;
    unsigned char *out;
    size_t out_cap;
};

static uint64_t mix(uint64_t h, const unsigned char *p, size_t n)
{
    size_t step = n / 64 + 1;
    for (size_t i = 0; i < n; i += step) h = (h ^ p[i]) * 0x100000001b3ull;
    return h;
}

static uint64_t do_uncompress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t n = it->out_cap;
    if (snappy_uncompress((const char *)it->in, it->in_len, (char *)it->out, &n) != SNAPPY_OK) abort();
    return mix(n, it->out, n);
}

static uint64_t do_validate(void *ctx)
{
    struct item *it = (struct item *)ctx;
    if (snappy_validate_compressed_buffer((const char *)it->in, it->in_len) != SNAPPY_OK) abort();
    return 1;
}

static uint64_t do_compress(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t n = it->out_cap;
    if (snappy_compress((const char *)it->in, it->in_len, (char *)it->out, &n) != SNAPPY_OK) abort();
    return n;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "uncompress";
    char **names;
    if (!strcmp(mode, "prepare")) {
        const char *dir = argv[2];
        size_t n = vb_list_dir(dir, &names);
        char p[4096];
        snprintf(p, sizeof p, "%s/snappy", dir);
        mkdir(p, 0777);
        for (size_t i = 0; i < n; i++) {
            size_t len;
            snprintf(p, sizeof p, "%s/%s", dir, names[i]);
            unsigned char *b = vb_read_file(p, &len);
            size_t m = snappy_max_compressed_length(len);
            char *c = (char *)malloc(m);
            if (snappy_compress((const char *)b, len, c, &m) != SNAPPY_OK) abort();
            snprintf(p, sizeof p, "%s/snappy/%s.sz", dir, names[i]);
            FILE *f = fopen(p, "wb");
            if (!f || fwrite(c, 1, m, f) != m || fclose(f)) { perror(p); return 1; }
            free(b);
            free(c);
        }
        fprintf(stderr, "prepared %zu files\n", n);
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
        if (!strcmp(mode, "compress")) {
            it->in = orig;
            it->in_len = len;
            it->out_cap = snappy_max_compressed_length(len);
            it->out = (unsigned char *)malloc(it->out_cap);
            fn = do_compress;
            size_t m = (size_t)fn(it);
            /* Round trip through the same library. */
            size_t bl = len + 1;
            char *back = (char *)malloc(bl);
            if (snappy_uncompress((const char *)it->out, m, back, &bl) != SNAPPY_OK || bl != len || memcmp(back, orig, len)) {
                fprintf(stderr, "compress of %s does not round-trip\n", names[i]);
                return 1;
            }
            free(back);
        } else {
            snprintf(p, sizeof p, "%s/snappy/%s.sz", dir, names[i]);
            it->in = vb_read_file(p, &it->in_len);
            it->out_cap = len + 1;
            it->out = (unsigned char *)malloc(it->out_cap);
            size_t ul = 0;
            if (snappy_uncompressed_length((const char *)it->in, it->in_len, &ul) != SNAPPY_OK || ul != len) abort();
            do_uncompress(it);
            if (memcmp(it->out, orig, len)) {
                fprintf(stderr, "uncompress of %s does not give the original\n", names[i]);
                return 1;
            }
            fn = !strcmp(mode, "validate") ? do_validate : do_uncompress;
        }
        snprintf(cname, sizeof cname, "%s/%s", mode, names[i]);
        vb_case(cname, len, fn, it);
    }
    return vb_main();
}
