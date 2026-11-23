/* PNG suite: decode a PNG held in memory to 8-bit RGBA through libpng's
 * API. Linked against libpng (png-libpng) and against vpng's libpng API
 * (png-vpng-abi, the drop-in comparison); the native comparison's vpng side
 * is the Rust runner runners/vpng-run, doing the same work.
 *
 * Cases rgba8/FILE for every *.png in $VBENCH_DATA. check = output size
 * plus a strided sum of the pixels (the same function on both sides). */
#include <png.h>
#include <setjmp.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "runner.h"

struct src { const unsigned char *p; size_t n, at; };

static void rd(png_structp png, png_bytep out, size_t n)
{
    struct src *s = (struct src *)png_get_io_ptr(png);
    if (s->n - s->at < n) png_error(png, "eof");
    memcpy(out, s->p + s->at, n);
    s->at += n;
}

static void quiet(png_structp p, png_const_charp m) { (void)p; (void)m; }

static size_t decode(const unsigned char *data, size_t len, unsigned char **out)
{
    struct src s = { data, len, 0 };
    png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, quiet);
    png_infop info = png_create_info_struct(png);
    unsigned char *volatile img = NULL;
    png_bytep *volatile rows = NULL;
    if (setjmp(png_jmpbuf(png))) {
        free(img);
        free(rows);
        png_destroy_read_struct(&png, &info, NULL);
        return 0;
    }
    png_set_read_fn(png, &s, rd);
    png_read_info(png, info);
    png_uint_32 h = png_get_image_height(png, info);
    png_set_expand(png);
    png_set_strip_16(png);
    png_set_gray_to_rgb(png);
    png_set_filler(png, 0xff, PNG_FILLER_AFTER);
    png_set_interlace_handling(png);
    png_read_update_info(png, info);
    size_t rb = png_get_rowbytes(png, info);
    img = (unsigned char *)malloc(h * rb);
    rows = (png_bytep *)malloc(sizeof(png_bytep) * h);
    for (png_uint_32 y = 0; y < h; y++) rows[y] = img + y * rb;
    png_read_image(png, rows);
    png_read_end(png, NULL);
    free(rows);
    png_destroy_read_struct(&png, &info, NULL);
    *out = img;
    return h * rb;
}

/* Must match strided_sum in runners/vpng-run. */
static uint64_t strided_sum(const unsigned char *p, size_t n)
{
    uint64_t s = n;
    for (size_t i = 0; i < n; i += 61) s = s * 31 + p[i];
    return s;
}

struct item { unsigned char *buf; size_t len; };

static uint64_t do_decode(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char *img = NULL;
    size_t n = decode(it->buf, it->len, &img);
    if (!n) abort();
    uint64_t s = strided_sum(img, n);
    free(img);
    return s;
}

int main(void)
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 5 || strcmp(names[i] + l - 4, ".png")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "rgba8/%s", names[i]);
        vb_case(cname, it->len, do_decode, it);
    }
    return vb_main();
}
