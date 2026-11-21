/* JPEG suites (baseline, progressive, 4:4:4). One driver against the
 * TurboJPEG API (tj3Decompress8 to RGB into a reused buffer), linked once
 * with libjpeg-turbo's libturbojpeg and once with vjpeg (feature
 * turbojpeg-abi), which exports the same functions.
 *
 * Cases rgb/FILE for every *.jpg in $VBENCH_DATA (made from the PNG photos
 * by mkjpeg: baseline 4:2:0 at quality 75 in data/jpeg, the same as
 * progressive in data/jpeg-prog, baseline 4:4:4 at quality 90 in
 * data/jpeg-444). check = strided sum of the pixels. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <turbojpeg.h>
#include "runner.h"

struct item { unsigned char *buf; size_t len; unsigned char *out; size_t out_len; };

static tjhandle handle;

static uint64_t strided_sum(const unsigned char *p, size_t n)
{
    uint64_t s = n;
    for (size_t i = 0; i < n; i += 61) s = s * 31 + p[i];
    return s;
}

static uint64_t do_decode(void *ctx)
{
    struct item *it = (struct item *)ctx;
    if (tj3Decompress8(handle, it->buf, it->len, it->out, 0, TJPF_RGB) != 0) abort();
    return strided_sum(it->out, it->out_len);
}

int main(void)
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    handle = tj3Init(TJINIT_DECOMPRESS);
    if (!handle) { fprintf(stderr, "tj3Init failed\n"); return 1; }
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 5 || strcmp(names[i] + l - 4, ".jpg")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        if (tj3DecompressHeader(handle, it->buf, it->len) != 0) { fprintf(stderr, "not a JPEG: %s\n", names[i]); return 1; }
        int w = tj3Get(handle, TJPARAM_JPEGWIDTH), h = tj3Get(handle, TJPARAM_JPEGHEIGHT);
        it->out_len = (size_t)w * h * 3;
        it->out = (unsigned char *)malloc(it->out_len);
        do_decode(it);
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "rgb/%s", names[i]);
        vb_case(cname, it->len, do_decode, it);
    }
    return vb_main();
}
