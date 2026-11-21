/* zlib suite. One driver, written against zlib's own API, linked once with
 * zlib and once with vzlib's zlib ABI (feature zlib-abi), so the only thing
 * that differs between the two runners is the library.
 *
 *   zlib-run inflate      cases inflate/FILE: decompress FILE.z6 (zlib
 *                         format, made by zlib 1.3.1 at level 6) in one call
 *                         and inflate-chunked/FILE: the same, fed 1 KB of
 *                         input per call into a 16 KB output buffer (how a
 *                         Node zlib stream drives it), plus
 *                         inflate-chunked/rle-16m: 16 MiB of 'a' (Node's
 *                         createInflate benchmark), from chunk/rle-16m.z6
 *   zlib-run deflate      cases deflate-L/FILE for L in 1 6 9: compress FILE
 *                         to zlib format in one call; check = compressed size
 *   zlib-run prepare DIR  writes DIR/z6/FILE.z6 for every file in DIR, and
 *                         DIR/chunk/rle-16m.z6
 *
 * Inputs are the files in $VBENCH_DATA (the .z6 files in $VBENCH_DATA/z6).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include "zlib.h"
#include "runner.h"

struct item {
    unsigned char *in;
    size_t in_len;
    unsigned char *out;
    size_t out_cap;
    size_t expect_len;
    unsigned char *expect;
    int level;
    z_stream s;
};

static uint64_t do_inflate(void *ctx)
{
    struct item *it = (struct item *)ctx;
    z_stream *s = &it->s;
    if (inflateReset(s) != Z_OK) abort();
    s->next_in = it->in;
    s->avail_in = (uInt)it->in_len;
    s->next_out = it->out;
    s->avail_out = (uInt)it->out_cap;
    if (inflate(s, Z_FINISH) != Z_STREAM_END) abort();
    return (uint64_t)s->total_out ^ ((uint64_t)s->adler << 32);
}

static uint64_t do_inflate_chunked(void *ctx)
{
    struct item *it = (struct item *)ctx;
    z_stream *s = &it->s;
    if (inflateReset(s) != Z_OK) abort();
    size_t p = 0;
    int r = Z_OK;
    while (r != Z_STREAM_END) {
        if (p >= it->in_len) abort();
        size_t m = it->in_len - p < 1024 ? it->in_len - p : 1024;
        s->next_in = it->in + p;
        s->avail_in = (uInt)m;
        p += m;
        do {
            s->next_out = it->out;
            s->avail_out = 16384;
            r = inflate(s, Z_NO_FLUSH);
            if (r != Z_OK && r != Z_STREAM_END && r != Z_BUF_ERROR) abort();
        } while (s->avail_out == 0 && r != Z_STREAM_END);
    }
    return (uint64_t)s->total_out ^ ((uint64_t)s->adler << 32);
}

static struct item *chunked_item(unsigned char *z, size_t zlen, size_t len)
{
    struct item *it = (struct item *)calloc(1, sizeof *it);
    it->in = z;
    it->in_len = zlen;
    it->out = (unsigned char *)malloc(16384);
    if (inflateInit(&it->s) != Z_OK) abort();
    uint64_t c = do_inflate_chunked(it);
    if ((c & 0xffffffffu) != (len & 0xffffffffu)) {
        fprintf(stderr, "chunked inflate gives %llu bytes, not %zu\n", (unsigned long long)(c & 0xffffffffu), len);
        exit(1);
    }
    return it;
}

static uint64_t do_deflate(void *ctx)
{
    struct item *it = (struct item *)ctx;
    z_stream *s = &it->s;
    if (deflateReset(s) != Z_OK) abort();
    s->next_in = it->in;
    s->avail_in = (uInt)it->in_len;
    s->next_out = it->out;
    s->avail_out = (uInt)it->out_cap;
    if (deflate(s, Z_FINISH) != Z_STREAM_END) abort();
    return (uint64_t)s->total_out;
}

static size_t compress_buf(const unsigned char *in, size_t n, unsigned char **out, int level)
{
    z_stream s;
    memset(&s, 0, sizeof s);
    if (deflateInit(&s, level) != Z_OK) abort();
    size_t cap = deflateBound(&s, (uLong)n);
    *out = (unsigned char *)malloc(cap);
    s.next_in = (unsigned char *)in;
    s.avail_in = (uInt)n;
    s.next_out = *out;
    s.avail_out = (uInt)cap;
    if (deflate(&s, Z_FINISH) != Z_STREAM_END) abort();
    size_t m = s.total_out;
    deflateEnd(&s);
    return m;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "inflate";
    char **names;
    if (!strcmp(mode, "prepare")) {
        const char *dir = argv[2];
        size_t n = vb_list_dir(dir, &names);
        char p[4096];
        snprintf(p, sizeof p, "%s/z6", dir);
        mkdir(p, 0777);
        for (size_t i = 0; i < n; i++) {
            size_t len;
            snprintf(p, sizeof p, "%s/%s", dir, names[i]);
            unsigned char *b = vb_read_file(p, &len), *c;
            size_t m = compress_buf(b, len, &c, 6);
            snprintf(p, sizeof p, "%s/z6/%s.z6", dir, names[i]);
            FILE *f = fopen(p, "wb");
            if (!f || fwrite(c, 1, m, f) != m || fclose(f)) { perror(p); return 1; }
            free(b);
            free(c);
        }
        {
            size_t rn = (size_t)16 << 20, m;
            unsigned char *a = (unsigned char *)malloc(rn), *c;
            memset(a, 'a', rn);
            m = compress_buf(a, rn, &c, 6);
            snprintf(p, sizeof p, "%s/chunk", dir);
            mkdir(p, 0777);
            snprintf(p, sizeof p, "%s/chunk/rle-16m.z6", dir);
            FILE *f = fopen(p, "wb");
            if (!f || fwrite(c, 1, m, f) != m || fclose(f)) { perror(p); return 1; }
            free(a);
            free(c);
        }
        fprintf(stderr, "prepared %zu files with %s\n", n, zlibVersion());
        return 0;
    }
    const char *dir = vb_data_dir();
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        size_t len;
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        unsigned char *orig = vb_read_file(p, &len);
        if (!strcmp(mode, "inflate")) {
            struct item *it = (struct item *)calloc(1, sizeof *it);
            snprintf(p, sizeof p, "%s/z6/%s.z6", dir, names[i]);
            it->in = vb_read_file(p, &it->in_len);
            it->out_cap = len + 1;
            it->out = (unsigned char *)malloc(it->out_cap);
            if (inflateInit(&it->s) != Z_OK) abort();
            do_inflate(it);
            if (it->s.total_out != len || memcmp(it->out, orig, len)) {
                fprintf(stderr, "inflate of %s does not give the original\n", names[i]);
                return 1;
            }
            snprintf(cname, sizeof cname, "inflate/%s", names[i]);
            vb_case(cname, len, do_inflate, it);
            struct item *ci = chunked_item(it->in, it->in_len, len);
            snprintf(cname, sizeof cname, "inflate-chunked/%s", names[i]);
            vb_case(cname, len, do_inflate_chunked, ci);
        } else {
            static const int levels[] = {1, 6, 9};
            for (int k = 0; k < 3; k++) {
                struct item *it = (struct item *)calloc(1, sizeof *it);
                it->in = orig;
                it->in_len = len;
                it->level = levels[k];
                if (deflateInit(&it->s, it->level) != Z_OK) abort();
                it->out_cap = deflateBound(&it->s, (uLong)len) + 1024;
                it->out = (unsigned char *)malloc(it->out_cap);
                size_t m = (size_t)do_deflate(it);
                /* Round trip through the same library. */
                unsigned char *back = (unsigned char *)malloc(len + 1);
                uLongf bl = (uLongf)len + 1;
                if (uncompress(back, &bl, it->out, (uLong)m) != Z_OK || bl != len || memcmp(back, orig, len)) {
                    fprintf(stderr, "deflate-%d of %s does not round-trip\n", it->level, names[i]);
                    return 1;
                }
                free(back);
                snprintf(cname, sizeof cname, "deflate-%d/%s", it->level, names[i]);
                vb_case(cname, len, do_deflate, it);
            }
        }
    }
    if (!strcmp(mode, "inflate")) {
        char p[4096];
        size_t zlen;
        snprintf(p, sizeof p, "%s/chunk/rle-16m.z6", dir);
        FILE *f = fopen(p, "rb");
        if (f) {
            fclose(f);
            unsigned char *z = vb_read_file(p, &zlen);
            vb_case("inflate-chunked/rle-16m", (size_t)16 << 20, do_inflate_chunked, chunked_item(z, zlen, (size_t)16 << 20));
        }
    }
    return vb_main();
}
