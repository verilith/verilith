/* Decodes a PNG file with libpng and writes "w h depth ct interlace" and the
 * pixels to stdout, or "ERR". Usage: refpng FILE [rgba8|native]
 * rgba8: png_set_expand, png_set_strip_16, png_set_gray_to_rgb, opaque
 * filler. native: no transformations; the padding bits at the end of each
 * row are cleared (vpng's native format sets them to 0). */
#include <png.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void quiet(png_structp p, png_const_charp m) { (void)p; (void)m; }

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb");
  int native = argc > 2 && strcmp(argv[2], "native") == 0;
  if (!f) return 2;
  png_structp png = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, quiet);
  png_infop info = png_create_info_struct(png);
  static png_bytep *rows;
  static png_bytep img;
  if (setjmp(png_jmpbuf(png))) {
    printf("ERR\n");
    return 0;
  }
  png_set_user_limits(png, 0x7fffffff, 0x7fffffff);
  png_init_io(png, f);
  png_read_info(png, info);
  png_uint_32 w, h;
  int depth, ct, il;
  png_get_IHDR(png, info, &w, &h, &depth, &ct, &il, NULL, NULL);
  if (!native) {
    png_set_expand(png);
    png_set_strip_16(png);
    png_set_gray_to_rgb(png);
    png_set_filler(png, 0xff, PNG_FILLER_AFTER);
  }
  png_set_interlace_handling(png);
  png_read_update_info(png, info);
  size_t rb = png_get_rowbytes(png, info);
  img = calloc(h, rb);
  rows = malloc(sizeof(png_bytep) * h);
  for (png_uint_32 y = 0; y < h; y++) rows[y] = img + y * rb;
  png_read_image(png, rows);
  png_read_end(png, NULL);
  if (native) {
    int bits = depth * png_get_channels(png, info);
    size_t used = ((size_t)w * bits) % 8;
    if (used)
      for (png_uint_32 y = 0; y < h; y++) rows[y][rb - 1] &= (png_byte)(0xff << (8 - used));
  }
  printf("%u %u %d %d %d\n", w, h, depth, ct, il);
  fwrite(img, 1, (size_t)h * rb, stdout);
  return 0;
}
