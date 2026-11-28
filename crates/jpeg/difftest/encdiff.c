// Differential test of the encoder against libjpeg-turbo: encodes images
// with both and compares the files byte for byte. libjpeg runs with
// jpeg_set_defaults and jpeg_set_quality (the accurate integer DCT, the
// typical Huffman tables), 2x2 luma for 4:2:0 or 1x1 for 4:4:4.
//
//   encdiff                 random and synthetic images at every quality
//   encdiff -b W H [Q]      time both on a W by H image
//   encdiff FILE.ppm ...    the images of binary PPM files
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <jpeglib.h>

uint8_t *vjpeg_encode(const uint8_t *px, uint32_t w, uint32_t h, uint32_t bpp, uint32_t q, int sub,
                      size_t *len);
void vjpeg_free(uint8_t *p, size_t len);

static unsigned char *ref_encode(const uint8_t *px, int w, int h, int bpp, int q, int sub,
                                 unsigned long *len) {
  struct jpeg_compress_struct c;
  struct jpeg_error_mgr e;
  unsigned char *out = NULL;
  *len = 0;
  c.err = jpeg_std_error(&e);
  jpeg_create_compress(&c);
  jpeg_mem_dest(&c, &out, len);
  c.image_width = w;
  c.image_height = h;
  c.input_components = bpp;
  c.in_color_space = bpp == 4 ? JCS_EXT_RGBX : JCS_RGB;
  jpeg_set_defaults(&c);
  jpeg_set_quality(&c, q, TRUE);
  c.comp_info[0].h_samp_factor = sub ? 2 : 1;
  c.comp_info[0].v_samp_factor = sub ? 2 : 1;
  jpeg_start_compress(&c, TRUE);
  while (c.next_scanline < c.image_height) {
    JSAMPROW row = (JSAMPROW)(px + (size_t)c.next_scanline * w * bpp);
    jpeg_write_scanlines(&c, &row, 1);
  }
  jpeg_finish_compress(&c);
  jpeg_destroy_compress(&c);
  return out;
}

static uint64_t rng = 88172645463325252ULL;
static uint32_t rnd(void) {
  rng ^= rng << 13;
  rng ^= rng >> 7;
  rng ^= rng << 17;
  return (uint32_t)rng;
}

static long fails, runs;

static void check(const uint8_t *px, int w, int h, int bpp, int q, int sub, const char *what) {
  unsigned long rl;
  size_t ol;
  unsigned char *r = ref_encode(px, w, h, bpp, q, sub, &rl);
  uint8_t *o = vjpeg_encode(px, w, h, bpp, q, sub, &ol);
  runs++;
  if (!o || ol != rl || memcmp(o, r, rl) != 0) {
    size_t i = 0;
    if (o)
      while (i < ol && i < rl && o[i] == r[i]) i++;
    if (fails++ < 20)
      printf("DIFF %s %dx%d bpp %d q %d sub %d: ours %zu bytes, libjpeg %lu, first difference at %zu\n",
             what, w, h, bpp, q, sub, o ? ol : 0, rl, i);
  }
  vjpeg_free(o, ol);
  free(r);
}

static uint8_t *image(int w, int h, int bpp, int kind) {
  uint8_t *p = malloc((size_t)w * h * bpp);
  for (int y = 0; y < h; y++)
    for (int x = 0; x < w; x++)
      for (int k = 0; k < bpp; k++) {
        uint8_t v;
        switch (kind) {
          case 0: v = rnd(); break;                                   // noise
          case 1: v = (uint8_t)(x * 255 / (w > 1 ? w - 1 : 1) + k * 40 + y); break;  // gradients
          case 2: v = ((x / 3 + y / 5) & 1) ? 255 : 0; break;          // hard edges
          default: v = (uint8_t)(128 + 100 * ((x * 7 + y * 3 + k * 11) % 9 - 4) / 4); break;
        }
        p[((size_t)y * w + x) * bpp + k] = v;
      }
  return p;
}

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

static uint8_t *read_ppm(const char *path, int *w, int *h) {
  FILE *f = fopen(path, "rb");
  int maxv;
  if (!f || fscanf(f, "P6 %d %d %d", w, h, &maxv) != 3 || maxv != 255) {
    if (f) fclose(f);
    return NULL;
  }
  fgetc(f);
  uint8_t *p = malloc((size_t)*w * *h * 3);
  if (fread(p, 1, (size_t)*w * *h * 3, f) != (size_t)*w * *h * 3) {
    free(p);
    p = NULL;
  }
  fclose(f);
  return p;
}

int main(int argc, char **argv) {
  if (argc >= 4 && strcmp(argv[1], "-b") == 0) {
    int w = atoi(argv[2]), h = atoi(argv[3]), q = argc > 4 ? atoi(argv[4]) : 80;
    uint8_t *px = image(w, h, 3, 1);
    for (int i = 0; i < w * h * 3; i++) px[i] ^= rnd() & 15;
    for (int sub = 1; sub >= 0; sub--) {
      int reps = 0;
      double t0 = now(), tr, to;
      unsigned long rl;
      size_t ol;
      do { free(ref_encode(px, w, h, 3, q, sub, &rl)); reps++; } while (now() - t0 < 1.0);
      tr = (now() - t0) / reps;
      reps = 0;
      t0 = now();
      do { vjpeg_free(vjpeg_encode(px, w, h, 3, q, sub, &ol), ol); reps++; } while (now() - t0 < 1.0);
      to = (now() - t0) / reps;
      printf("%dx%d q%d %s: libjpeg-turbo %.2f ms (%.0f MP/s), verilith %.2f ms (%.0f MP/s), %lu vs %zu bytes\n", w, h,
             q, sub ? "4:2:0" : "4:4:4", tr * 1e3, w * h / tr / 1e6, to * 1e3, w * h / to / 1e6, rl, ol);
    }
    return 0;
  }
  if (argc > 1) {
    for (int a = 1; a < argc; a++) {
      int w, h;
      uint8_t *px = read_ppm(argv[a], &w, &h);
      if (!px) { printf("skip %s\n", argv[a]); continue; }
      for (int q = 5; q <= 100; q += 5)
        for (int sub = 0; sub < 2; sub++) check(px, w, h, 3, q, sub, argv[a]);
      free(px);
    }
  } else {
    static const int sizes[][2] = {{1, 1}, {1, 7}, {7, 1}, {8, 8}, {9, 9}, {15, 17}, {16, 16}, {17, 15},
                                   {31, 33}, {33, 31}, {64, 48}, {100, 75}, {257, 3}, {3, 257}, {123, 45}};
    for (unsigned s = 0; s < sizeof sizes / sizeof *sizes; s++)
      for (int kind = 0; kind < 4; kind++)
        for (int bpp = 3; bpp <= 4; bpp++) {
          int w = sizes[s][0], h = sizes[s][1];
          uint8_t *px = image(w, h, bpp, kind);
          for (int q = 1; q <= 100; q += (q < 10 || q > 90) ? 1 : 7)
            for (int sub = 0; sub < 2; sub++) check(px, w, h, bpp, q, sub, "synthetic");
          free(px);
        }
  }
  printf("%ld of %ld encodings differ\n", fails, runs);
  return fails != 0;
}
