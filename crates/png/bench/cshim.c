/* One-shot decoding from memory with libpng and libspng, for the benchmark.
 * Each returns the output size, or 0 on error; the caller frees *out. */
#include <png.h>
#include <spng.h>
#include <setjmp.h>
#include <stdlib.h>
#include <string.h>

struct src { const unsigned char *p; size_t n, at; };

static void rd(png_structp png, png_bytep out, size_t n) {
  struct src *s = png_get_io_ptr(png);
  if (s->n - s->at < n) png_error(png, "eof");
  memcpy(out, s->p + s->at, n);
  s->at += n;
}

static void quiet(png_structp p, png_const_charp m) { (void)p; (void)m; }

size_t libpng_decode(const unsigned char *data, size_t len, int rgba, unsigned char **out) {
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
  if (rgba) {
    png_set_expand(png);
    png_set_strip_16(png);
    png_set_gray_to_rgb(png);
    png_set_filler(png, 0xff, PNG_FILLER_AFTER);
  }
  png_set_interlace_handling(png);
  png_read_update_info(png, info);
  size_t rb = png_get_rowbytes(png, info);
  img = malloc(h * rb);
  rows = malloc(sizeof(png_bytep) * h);
  for (png_uint_32 y = 0; y < h; y++) rows[y] = img + y * rb;
  png_read_image(png, rows);
  png_read_end(png, NULL);
  free(rows);
  png_destroy_read_struct(&png, &info, NULL);
  *out = img;
  return h * rb;
}

size_t spng_decode(const unsigned char *data, size_t len, int rgba, unsigned char **out) {
  spng_ctx *ctx = spng_ctx_new(0);
  int fmt = rgba ? SPNG_FMT_RGBA8 : SPNG_FMT_PNG;
  size_t n = 0;
  unsigned char *img = NULL;
  if (spng_set_png_buffer(ctx, data, len) || spng_decoded_image_size(ctx, fmt, &n)) goto fail;
  img = malloc(n);
  if (spng_decode_image(ctx, img, n, fmt, rgba ? SPNG_DECODE_TRNS : 0)) goto fail;
  spng_ctx_free(ctx);
  *out = img;
  return n;
fail:
  free(img);
  spng_ctx_free(ctx);
  return 0;
}
