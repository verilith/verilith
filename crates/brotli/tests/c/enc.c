/* Tests the encoder's C API (vbrotli_BrotliEncoder*): one-shot and
 * streamed compression of generated data, with random piece sizes,
 * flushes and output buffer sizes. Every stream is decoded with
 * google/brotli's decoder, and after each flush the output so far must
 * decode to the input so far.
 *
 *   tests/c/run_enc.sh [iterations] [seed]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <brotli/decode.h>
#include <brotli/encode.h>

void *vbrotli_BrotliEncoderCreateInstance(void *, void *, void *);
void vbrotli_BrotliEncoderDestroyInstance(void *);
int vbrotli_BrotliEncoderSetParameter(void *, int, uint32_t);
int vbrotli_BrotliEncoderCompressStream(void *, int, size_t *, const uint8_t **, size_t *, uint8_t **, size_t *);
int vbrotli_BrotliEncoderIsFinished(void *);
int vbrotli_BrotliEncoderHasMoreOutput(void *);
const uint8_t *vbrotli_BrotliEncoderTakeOutput(void *, size_t *);
size_t vbrotli_BrotliEncoderMaxCompressedSize(size_t);
int vbrotli_BrotliEncoderCompress(int, int, int, size_t, const uint8_t *, size_t *, uint8_t *);

static uint64_t rng;
static uint32_t rnd(void) {
  rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
  return (uint32_t)(rng >> 16);
}

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
      size_t d = 1 + rnd() % (i < 70000 ? i : 70000), l = 2 + rnd() % 300;
      for (size_t k = 0; k < l && i < n; k++, i++) p[i] = p[i - d];
    } else if (r < 8) {
      p[i++] = (uint8_t)rnd();
    } else {
      uint8_t c = (uint8_t)rnd();
      for (size_t k = rnd() % 100; k && i < n; k--) p[i++] = c;
    }
  }
  return n;
}

/* google/brotli decodes `c` to exactly `d`. */
static int check(const uint8_t *c, size_t cn, const uint8_t *d, size_t dn, int partial) {
  BrotliDecoderState *s = BrotliDecoderCreateInstance(0, 0, 0);
  size_t cap = dn + 1, ai = cn, ao = cap;
  uint8_t *out = malloc(cap), *no = out;
  const uint8_t *ni = c;
  BrotliDecoderResult r = BrotliDecoderDecompressStream(s, &ai, &ni, &ao, &no, 0);
  size_t got = cap - ao;
  int ok = got == dn && memcmp(out, d, dn) == 0 && ai == 0 &&
           (partial ? r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT : r == BROTLI_DECODER_RESULT_SUCCESS);
  free(out);
  BrotliDecoderDestroyInstance(s);
  return ok;
}

int main(int argc, char **argv) {
  int iters = argc > 1 ? atoi(argv[1]) : 200;
  rng = argc > 2 ? strtoull(argv[2], 0, 10) : 12345;
  size_t cap = 1 << 21;
  uint8_t *d = malloc(cap), *c = malloc(2 * cap + 1024);
  for (int it = 0; it < iters; it++) {
    size_t n = gen(d, rnd() % 3 == 0 ? cap : 70000);
    int q = rnd() % 12, w = 10 + rnd() % 15;
    /* One shot. */
    size_t cn = vbrotli_BrotliEncoderMaxCompressedSize(n);
    if (!vbrotli_BrotliEncoderCompress(q, w, 0, n, d, &cn, c) || !check(c, cn, d, n, 0)) {
      printf("FAIL one-shot it=%d n=%zu q=%d w=%d\n", it, n, q, w);
      return 1;
    }
    /* Streamed. */
    void *s = vbrotli_BrotliEncoderCreateInstance(0, 0, 0);
    vbrotli_BrotliEncoderSetParameter(s, BROTLI_PARAM_QUALITY, q);
    vbrotli_BrotliEncoderSetParameter(s, BROTLI_PARAM_LGWIN, w);
    size_t pos = 0, outn = 0;
    int take = rnd() % 2;
    for (;;) {
      size_t piece = rnd() % 3 == 0 ? rnd() % 100 : rnd() % 300000;
      if (piece > n - pos) piece = n - pos;
      int fin = pos + piece == n && rnd() % 2 == 0 ? 1 : 0;
      int op = fin ? BROTLI_OPERATION_FINISH : rnd() % 4 == 0 ? BROTLI_OPERATION_FLUSH : BROTLI_OPERATION_PROCESS;
      size_t ai = piece;
      const uint8_t *ni = d + pos;
      do {
        size_t ao = take ? 0 : 1 + rnd() % 5000;
        uint8_t *no = c + outn;
        if (!vbrotli_BrotliEncoderCompressStream(s, op, &ai, &ni, &ao, &no, 0)) {
          printf("FAIL stream call it=%d\n", it);
          return 1;
        }
        outn = no - c;
        if (take) {
          size_t k = rnd() % 2 ? 0 : 1 + rnd() % 3000;
          const uint8_t *p = vbrotli_BrotliEncoderTakeOutput(s, &k);
          memcpy(c + outn, p, k);
          outn += k;
        }
      } while (ai > 0 || vbrotli_BrotliEncoderHasMoreOutput(s));
      pos += piece;
      if (op == BROTLI_OPERATION_FLUSH && !check(c, outn, d, pos, 1)) {
        printf("FAIL flush it=%d pos=%zu q=%d\n", it, pos, q);
        return 1;
      }
      if (fin) break;
      if (pos == n && rnd() % 2) {
        /* Finish with no more input. */
        size_t ai = 0, ao;
        const uint8_t *ni = 0;
        do {
          ao = 4096;
          uint8_t *no = c + outn;
          vbrotli_BrotliEncoderCompressStream(s, BROTLI_OPERATION_FINISH, &ai, &ni, &ao, &no, 0);
          outn = no - c;
        } while (!vbrotli_BrotliEncoderIsFinished(s));
        break;
      }
    }
    if (!vbrotli_BrotliEncoderIsFinished(s)) {
      size_t ai = 0, ao;
      const uint8_t *ni = 0;
      do {
        ao = 4096;
        uint8_t *no = c + outn;
        vbrotli_BrotliEncoderCompressStream(s, BROTLI_OPERATION_FINISH, &ai, &ni, &ao, &no, 0);
        outn = no - c;
      } while (!vbrotli_BrotliEncoderIsFinished(s));
    }
    vbrotli_BrotliEncoderDestroyInstance(s);
    if (!check(c, outn, d, n, 0)) {
      printf("FAIL streamed it=%d n=%zu q=%d w=%d\n", it, n, q, w);
      return 1;
    }
  }
  printf("ok: %d iterations\n", iters);
  return 0;
}
