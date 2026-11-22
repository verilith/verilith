/* WebP suites (lossless and lossy). One driver against libwebp's decode API
 * (WebPDecodeRGBAInto into a reused buffer), linked once with libwebp and
 * once with vwebp (feature webp-abi), which exports the same functions.
 *
 * Cases rgba/FILE for every *.webp in $VBENCH_DATA (made from the PNG
 * photos by mkwebp: lossless in data/webp, lossy at quality 75 in
 * data/webp-lossy). check = strided sum of the pixels. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/decode.h"
#include "runner.h"

struct item { unsigned char *buf; size_t len; unsigned char *out; size_t out_len; int stride; };

static uint64_t strided_sum(const unsigned char *p, size_t n)
{
    uint64_t s = n;
    for (size_t i = 0; i < n; i += 61) s = s * 31 + p[i];
    return s;
}

static uint64_t do_decode(void *ctx)
{
    struct item *it = (struct item *)ctx;
    if (!WebPDecodeRGBAInto(it->buf, it->len, it->out, it->out_len, it->stride)) abort();
    return strided_sum(it->out, it->out_len);
}

int main(void)
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 6 || strcmp(names[i] + l - 5, ".webp")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        int w, h;
        if (!WebPGetInfo(it->buf, it->len, &w, &h)) { fprintf(stderr, "not a WebP: %s\n", names[i]); return 1; }
        it->stride = w * 4;
        it->out_len = (size_t)it->stride * h;
        it->out = (unsigned char *)malloc(it->out_len);
        do_decode(it);
        names[i][l - 5] = 0;
        snprintf(cname, sizeof cname, "rgba/%s", names[i]);
        vb_case(cname, it->len, do_decode, it);
    }
    return vb_main();
}
