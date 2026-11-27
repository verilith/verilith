/* Compares the encoders: google/brotli's BrotliEncoderCompress and
 * vbrotli's, on whole files, the same buffers, the best of N runs each.
 *
 *   bench_enc QUALITY RUNS FILE...
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <brotli/encode.h>
#include <brotli/decode.h>

size_t vbrotli_BrotliEncoderMaxCompressedSize(size_t);
int vbrotli_BrotliEncoderCompress(int, int, int, size_t, const uint8_t *, size_t *, uint8_t *);

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
  int q = atoi(argv[1]), runs = atoi(argv[2]);
  for (int f = 3; f < argc; f++) {
    FILE *fp = fopen(argv[f], "rb");
    fseek(fp, 0, SEEK_END);
    size_t n = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    uint8_t *d = malloc(n);
    if (fread(d, 1, n, fp) != n) return 1;
    fclose(fp);
    size_t cap = BrotliEncoderMaxCompressedSize(n) + 1024;
    uint8_t *c = malloc(cap), *back = malloc(n + 1);
    double bg = 1e9, bv = 1e9;
    size_t gn = 0, vn = 0;
    for (int r = 0; r < runs; r++) {
      size_t k = cap;
      double t = now();
      BrotliEncoderCompress(q, 22, BROTLI_MODE_GENERIC, n, d, &k, c);
      t = now() - t;
      if (t < bg) bg = t;
      gn = k;
      k = cap;
      t = now();
      vbrotli_BrotliEncoderCompress(q, 22, 0, n, d, &k, c);
      t = now() - t;
      if (t < bv) bv = t;
      vn = k;
      size_t bn = n + 1;
      if (BrotliDecoderDecompress(k, c, &bn, back) != BROTLI_DECODER_RESULT_SUCCESS || bn != n) {
        printf("decode failed\n");
        return 1;
      }
    }
    const char *name = argv[f];
    for (const char *p = argv[f]; *p; p++)
      if (*p == '/') name = p + 1;
    printf("%-8s q%-2d %9zu  google %9zu %7.3fs  vbrotli %9zu %7.3fs  size %+.1f%%  speed %.2fx\n", name, q, n, gn, bg,
           vn, bv, 100.0 * ((double)vn / gn - 1), bg / bv);
    free(d);
    free(c);
    free(back);
  }
  return 0;
}
