// Decode benchmark, one decoder per process: full decode to RGBA.
//
//   ./bench {libwebp|vwebp} ITERS FILE...
//
// prints, per file, the decoder, the minimum time in ns over ITERS timed
// decodes (after a warm-up), and megapixels per second. Run each decoder in
// its own process, pinned to one core, and compare only numbers taken in the
// same sitting (scripts/bench.sh does this). Timing the two decoders in one
// process, or interleaved, gives unstable ratios on cloud vCPUs whose turbo
// frequency drifts.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "webp/decode.h"

uint8_t* vwebp_DecodeRGBA(const uint8_t* data, size_t size, int* w, int* h);
void vwebp_Free(void* p);

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}

int main(int argc, char** argv) {
  if (argc < 4 || (strcmp(argv[1], "libwebp") && strcmp(argv[1], "vwebp"))) {
    fprintf(stderr, "usage: %s {libwebp|vwebp} ITERS FILE...\n", argv[0]);
    return 2;
  }
  int v = !strcmp(argv[1], "vwebp");
  int iters = atoi(argv[2]);
  int warm = iters / 4 + 3;
  for (int i = 3; i < argc; i++) {
    FILE* f = fopen(argv[i], "rb");
    if (!f) { perror(argv[i]); return 1; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* buf = malloc(n);
    if (fread(buf, 1, n, f) != (size_t)n) { perror(argv[i]); return 1; }
    fclose(f);
    int w = 0, h = 0;
    double best = 1e30;
    for (int k = 0; k < warm + iters; k++) {
      double t0 = now_ns();
      uint8_t* p = v ? vwebp_DecodeRGBA(buf, n, &w, &h) : WebPDecodeRGBA(buf, n, &w, &h);
      double t1 = now_ns();
      if (!p) { fprintf(stderr, "%s: decode failed\n", argv[i]); return 1; }
      if (v) vwebp_Free(p); else WebPFree(p);
      if (k >= warm && t1 - t0 < best) best = t1 - t0;
    }
    const char* s = strrchr(argv[i], '/');
    printf("%-8s %-24s %12.0f ns %8.1f MP/s\n", argv[1], s ? s + 1 : argv[i], best,
           (double)w * h / best * 1e3);
    free(buf);
  }
  return 0;
}
