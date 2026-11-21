/* Differential test against google/brotli: encodes generated data with
 * google's encoder at every quality and many window sizes, decodes with
 * both decoders, then flips bits and truncates and checks that both
 * decoders agree on success and output.
 *
 *   tests/c/run.sh [iterations] [seed]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <brotli/decode.h>
#include <brotli/encode.h>

/* vbrotli, under its own names. */
void *vbrotli_BrotliDecoderCreateInstance(void *, void *, void *);
void vbrotli_BrotliDecoderDestroyInstance(void *);
int vbrotli_BrotliDecoderDecompressStream(void *, size_t *, const uint8_t **,
                                          size_t *, uint8_t **, size_t *);
int vbrotli_BrotliDecoderDecompress(size_t, const uint8_t *, size_t *, uint8_t *);

static uint64_t rng;
static uint32_t rnd(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return (uint32_t)(rng >> 16);
}

/* Data with some structure: text-ish runs, repeats, random bytes. */
static size_t gen(uint8_t *p, size_t cap) {
  static const char *words[] = {"the ", "brotli ", "<div class=\"", "\">", "time", "Hello, ",
                                "world", " and ", "\n", "function(", "){return ", "0123"};
  size_t n = rnd() % 5 == 0 ? rnd() % 64 : rnd() % cap;
  size_t i = 0;
  int kind = rnd() % 4;
  while (i < n) {
    uint32_t r = rnd() % 10;
    if (kind == 0 || r < 3) {
      const char *w = words[rnd() % 12];
      for (size_t k = 0; w[k] && i < n; k++) p[i++] = (uint8_t)w[k];
    } else if (r < 6 && i > 0) {
      size_t d = 1 + rnd() % (i < 70000 ? i : 70000), len = 3 + rnd() % 300;
      for (size_t k = 0; k < len && i < n; k++, i++) p[i] = p[i - d];
    } else if (kind == 1) {
      p[i++] = (uint8_t)(rnd() % 4);
    } else {
      p[i++] = (uint8_t)rnd();
    }
  }
  return n;
}

/* Decodes with google, streaming in random pieces. Returns 1 on success. */
static int g_dec(const uint8_t *in, size_t n, uint8_t *out, size_t cap, size_t *outn, int *last) {
  BrotliDecoderState *s = BrotliDecoderCreateInstance(0, 0, 0);
  size_t ai = 0, ao = 0, tot = 0;
  const uint8_t *ni = in;
  uint8_t *no = out;
  int r;
  size_t used = 0;
  for (;;) {
    size_t step = 1 + rnd() % 300;
    ai = n - used < step ? n - used : step;
    size_t a0 = ai;
    ao = cap - tot < 1 + rnd() % 5000 ? cap - tot : 1 + rnd() % 5000;
    no = out + tot;
    size_t ao0 = ao;
    r = BrotliDecoderDecompressStream(s, &ai, &ni, &ao, &no, 0);
    used += a0 - ai;
    tot += ao0 - ao;
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT && used < n) continue;
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT && tot < cap) continue;
    break;
  }
  BrotliDecoderDestroyInstance(s);
  *outn = tot;
  *last = r;
  return r == BROTLI_DECODER_RESULT_SUCCESS;
}

static int v_dec(const uint8_t *in, size_t n, uint8_t *out, size_t cap, size_t *outn, int *last,
                 size_t *unused) {
  void *s = vbrotli_BrotliDecoderCreateInstance(0, 0, 0);
  size_t ai = 0, ao = 0, tot = 0, used = 0;
  const uint8_t *ni = in;
  uint8_t *no;
  int r;
  for (;;) {
    size_t step = 1 + rnd() % 300;
    ai = n - used < step ? n - used : step;
    ni = in + used;
    size_t a0 = ai;
    ao = cap - tot < 1 + rnd() % 5000 ? cap - tot : 1 + rnd() % 5000;
    no = out + tot;
    size_t ao0 = ao;
    r = vbrotli_BrotliDecoderDecompressStream(s, &ai, &ni, &ao, &no, 0);
    if (ni != in + used + (a0 - ai) || no != out + tot + (ao0 - ao)) {
      fprintf(stderr, "pointer bookkeeping wrong\n");
      exit(1);
    }
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT && ai != 0) {
      fprintf(stderr, "NEEDS_MORE_INPUT with input left\n");
      exit(1);
    }
    used += a0 - ai;
    tot += ao0 - ao;
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT && used < n) continue;
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT && tot < cap) continue;
    break;
  }
  vbrotli_BrotliDecoderDestroyInstance(s);
  *outn = tot;
  *last = r;
  *unused = n - used;
  return r == BROTLI_DECODER_RESULT_SUCCESS;
}

#define CAP (1 << 20)

int main(int argc, char **argv) {
  long iters = argc > 1 ? atol(argv[1]) : 1000;
  rng = argc > 2 ? strtoull(argv[2], 0, 10) : 88172645463325252ull;
  if (!rng) rng = 1;
  uint8_t *data = malloc(CAP), *enc = malloc(2 * CAP + 1024), *o1 = malloc(4 * CAP), *o2 = malloc(4 * CAP);
  long ok = 0, bad = 0, mism = 0;
  for (long it = 0; it < iters; it++) {
    size_t n = gen(data, rnd() % 3 == 0 ? CAP : 20000);
    int q = rnd() % 12, w = 10 + rnd() % 15;
    size_t en = 2 * CAP + 1024;
    if (!BrotliEncoderCompress(q, w, BROTLI_MODE_GENERIC + rnd() % 3, n, data, &en, enc)) {
      fprintf(stderr, "encoder failed\n");
      return 1;
    }
    /* Trailing junk after the stream must be left unused. */
    size_t junk = rnd() % 3 == 0 ? 1 + rnd() % 10 : 0;
    for (size_t k = 0; k < junk; k++) enc[en + k] = (uint8_t)rnd();
    size_t n1, n2, un;
    int l1, l2;
    int v = v_dec(enc, en + junk, o2, 4 * CAP, &n2, &l2, &un);
    if (!v || n2 != n || memcmp(o2, data, n) || un != junk) {
      fprintf(stderr, "iter %ld: valid stream (q=%d w=%d n=%zu) not decoded: r=%d n2=%zu unused=%zu\n",
              it, q, w, n, l2, n2, un);
      return 1;
    }
    size_t on = 4 * CAP;
    if (vbrotli_BrotliDecoderDecompress(en, enc, &on, o2) != 1 || on != n || memcmp(o2, data, n)) {
      fprintf(stderr, "iter %ld: one-shot failed\n", it);
      return 1;
    }
    /* Corrupt it a few ways. */
    for (int m = 0; m < 8; m++) {
      size_t mn = en;
      uint8_t save[8];
      size_t at[8];
      int k = 0;
      if (m == 0) {
        mn = rnd() % (en + 1);
      } else {
        for (k = 0; k < 1 + (int)(rnd() % 3); k++) {
          at[k] = rnd() % en;
          save[k] = enc[at[k]];
          enc[at[k]] ^= (uint8_t)(1 << (rnd() % 8));
        }
      }
      int g = g_dec(enc, mn, o1, 4 * CAP, &n1, &l1);
      int vv = v_dec(enc, mn, o2, 4 * CAP, &n2, &l2, &un);
      int same = g == vv && (!g || (n1 == n2 && !memcmp(o1, o2, n1)));
      /* Neither ends with success: both must have failed (error or
         truncated). Output before the failure may differ. */
      if (!same) {
        fprintf(stderr, "iter %ld mut %d: google %d (r=%d, %zu bytes), vbrotli %d (r=%d, %zu bytes)\n",
                it, m, g, l1, n1, vv, l2, n2);
        mism++;
        if (mism > 10) return 1;
      }
      if (vv) ok++; else bad++;
      while (k-- > 0) enc[at[k]] = save[k];
    }
  }
  printf("%ld streams, %ld corrupted decoded the same (%ld accepted, %ld rejected), %ld mismatches\n",
         iters, ok + bad, ok, bad, mism);
  return mism != 0;
}
