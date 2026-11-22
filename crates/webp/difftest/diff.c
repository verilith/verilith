// Differential test of vwebp against libwebp: both decode the same input
// to RGBA; they must agree on whether it decodes and, if so, on every byte.
// Lossless (VP8L) and lossy (VP8, with or without an ALPH chunk) alike.
//
// Built as a command line tool (files as arguments) or, with
// -DFUZZ -fsanitize=fuzzer, as a libFuzzer target that aborts on any
// disagreement.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "webp/decode.h"

uint8_t* vwebp_DecodeRGBA(const uint8_t* data, size_t size, int* w, int* h);
int vwebp_GetInfo(const uint8_t* data, size_t size, int* w, int* h);
void vwebp_Free(void* p);

// The one known departure (README, "Departures"): libwebp decodes alpha
// that uses only a color-indexing transform with a path of its own, which
// accepts a stream whose final symbol runs past the end of the ALPH chunk;
// vwebp rejects it. Such a file is accepted here if libwebp decodes it,
// vwebp fails, and with the ALPH chunk stripped (the VP8 chunk alone) the
// two agree on every byte.
static int le32(const uint8_t* p) { return p[0] | p[1] << 8 | p[2] << 16 | (uint32_t)p[3] << 24; }
static int AlphaTailDeparture(const uint8_t* data, size_t size) {
  if (size < 30 || memcmp(data + 12, "VP8X", 4) != 0) return 0;
  size_t off = 12, vp8 = 0, vp8n = 0;
  int alph_lossless = 0;
  while (off + 8 <= size) {
    size_t n = (size_t)le32(data + off + 4);
    if (memcmp(data + off, "ALPH", 4) == 0 && off + 8 < size) alph_lossless = (data[off + 8] & 3) == 1;
    if (memcmp(data + off, "VP8 ", 4) == 0) { vp8 = off; vp8n = size - off; break; }
    off += 8 + n + (n & 1);
  }
  if (!alph_lossless || vp8 == 0) return 0;
  uint8_t* t = malloc(12 + vp8n);
  memcpy(t, "RIFF\0\0\0\0WEBP", 12);
  memcpy(t + 12, data + vp8, vp8n);
  uint32_t r = (uint32_t)(4 + vp8n);
  t[4] = r; t[5] = r >> 8; t[6] = r >> 16; t[7] = r >> 24;
  int lw, lh, vw, vh;
  uint8_t* l = WebPDecodeRGBA(t, 12 + vp8n, &lw, &lh);
  uint8_t* v = vwebp_DecodeRGBA(t, 12 + vp8n, &vw, &vh);
  int ok = l != NULL && v != NULL && lw == vw && lh == vh && memcmp(l, v, (size_t)lw * lh * 4) == 0;
  WebPFree(l);
  vwebp_Free(v);
  free(t);
  return ok;
}

// 0: agree, 1: disagree. Prints why when verbose.
static int Compare(const uint8_t* data, size_t size, int verbose, const char* name) {
  int lw = 0, lh = 0, vw = 0, vh = 0;
  uint8_t* l = WebPDecodeRGBA(data, size, &lw, &lh);
  uint8_t* v = vwebp_DecodeRGBA(data, size, &vw, &vh);
  int bad = 0;
  if (l != NULL && v == NULL && AlphaTailDeparture(data, size)) {
    if (verbose) printf("%s: known departure (alpha stream ends mid-symbol)\n", name);
  } else if ((l == NULL) != (v == NULL)) {
    bad = 1;
    if (verbose) printf("%s: libwebp %s, vwebp %s\n", name, l ? "ok" : "fails", v ? "ok" : "fails");
  } else if (l != NULL) {
    if (lw != vw || lh != vh) {
      bad = 1;
      if (verbose) printf("%s: size %dx%d vs %dx%d\n", name, lw, lh, vw, vh);
    } else if (memcmp(l, v, (size_t)lw * lh * 4) != 0) {
      bad = 1;
      if (verbose) {
        size_t i = 0;
        while (l[i] == v[i]) ++i;
        printf("%s: pixels differ at byte %zu (pixel %zu): libwebp %d vwebp %d\n", name, i, i / 4, l[i], v[i]);
      }
    }
  }
  WebPFree(l);
  vwebp_Free(v);
  return bad;
}

#ifdef FUZZ
// A 14-byte header can claim a 16384x16384 image. Decoding it is legal, but
// the two decoders' output buffers alone then exceed libFuzzer's 2 GB RSS
// limit, so the run stops on out-of-memory rather than on a disagreement.
// Skip inputs either decoder says are larger than this many pixels.
#define FUZZ_MAX_PIXELS (1 << 22)

static int TooBig(int w, int h) { return (int64_t)w * h > FUZZ_MAX_PIXELS; }

int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  int w, h;
  if (WebPGetInfo(data, size, &w, &h) && TooBig(w, h)) return 0;
  if (vwebp_GetInfo(data, size, &w, &h) && TooBig(w, h)) return 0;
  if (Compare(data, size, 1, "input")) abort();
  return 0;
}
#else
int main(int argc, char** argv) {
  int bad = 0, ok = 0, decoded = 0, lossy = 0;
  for (int i = 1; i < argc; ++i) {
    FILE* f = fopen(argv[i], "rb");
    if (f == NULL) { perror(argv[i]); return 2; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t* buf = malloc(n > 0 ? n : 1);
    if (fread(buf, 1, n, f) != (size_t)n) { perror(argv[i]); return 2; }
    fclose(f);
    if (Compare(buf, n, 1, argv[i])) {
      ++bad;
    } else {
      ++ok;
      int w, h;
      WebPBitstreamFeatures f;
      if (vwebp_GetInfo(buf, n, &w, &h)) {
        ++decoded;
        if (WebPGetFeatures(buf, n, &f) == VP8_STATUS_OK && f.format == 1) ++lossy;
      }
    }
    free(buf);
  }
  printf("%d agree (%d decoded, %d of them lossy), %d disagree\n", ok, decoded, lossy, bad);
  return bad != 0;
}
#endif
