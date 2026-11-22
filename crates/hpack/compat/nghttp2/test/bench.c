/* Decoding speed of the inflater: nghttp2's own, or on vhpack.
 *
 *   bench [ROUNDS]
 *
 * Encodes request and response header blocks shaped like a browser's
 * (with nghttp2's deflater: Huffman, indexing, a 4096-byte table) once,
 * then decodes the whole sequence ROUNDS times with a fresh inflater each
 * round, and prints the time per block and the decoded bytes per second.
 * bench.sh builds it both ways. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <nghttp2/nghttp2.h>

#define NB 200
static uint8_t enc[NB][8192];
static size_t enclen[NB];

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}

#define NV(n, v) {(uint8_t *)n, (uint8_t *)v, sizeof(n) - 1, sizeof(v) - 1, 0}

int main(int argc, char **argv) {
  int rounds = argc > 1 ? atoi(argv[1]) : 2000;
  nghttp2_hd_deflater *def;
  nghttp2_hd_deflate_new(&def, 4096);
  char path[NB][64], cookie[NB][200];
  size_t decoded = 0;
  for (int i = 0; i < NB; i++) {
    snprintf(path[i], sizeof(path[i]), "/assets/app.%d.%x.js?v=%d", i, i * 2654435761u, i % 7);
    snprintf(cookie[i], sizeof(cookie[i]), "session=%08x%08x; theme=dark; _ga=GA1.2.%u.%u; consent=yes",
             i * 7919u, i * 104729u, i * 31u + 1000000u, 1700000000u + i);
    nghttp2_nv req[] = {
      NV(":method", "GET"), NV(":scheme", "https"), NV(":authority", "www.example.com"),
      {(uint8_t *)":path", (uint8_t *)path[i], 5, strlen(path[i]), 0},
      NV("user-agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"),
      NV("accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8"),
      NV("accept-encoding", "gzip, deflate, br, zstd"), NV("accept-language", "en-US,en;q=0.9"),
      NV("sec-fetch-mode", "navigate"), NV("sec-fetch-site", "same-origin"),
      {(uint8_t *)"cookie", (uint8_t *)cookie[i], 6, strlen(cookie[i]), 0},
    };
    nghttp2_nv res[] = {
      NV(":status", "200"), NV("content-type", "application/javascript; charset=utf-8"),
      NV("cache-control", "public, max-age=31536000, immutable"), NV("server", "nginx"),
      NV("date", "Tue, 03 Nov 2026 09:00:00 GMT"), NV("vary", "Accept-Encoding"),
      {(uint8_t *)"etag", (uint8_t *)path[i], 4, strlen(path[i]), 0},
    };
    nghttp2_nv *nva = i % 2 ? res : req;
    size_t n = i % 2 ? sizeof(res) / sizeof(res[0]) : sizeof(req) / sizeof(req[0]);
    for (size_t j = 0; j < n; j++) decoded += nva[j].namelen + nva[j].valuelen;
    nghttp2_ssize r = nghttp2_hd_deflate_hd2(def, enc[i], sizeof(enc[i]), nva, n);
    if (r < 0) return 1;
    enclen[i] = (size_t)r;
  }
  size_t total = 0;
  for (int i = 0; i < NB; i++) total += enclen[i];
  double best = 1e9;
  unsigned long long sink = 0;
  for (int rep = 0; rep < 5; rep++) {
    double t0 = now();
    for (int r = 0; r < rounds; r++) {
      nghttp2_hd_inflater *inf;
      nghttp2_hd_inflate_new(&inf);
      for (int i = 0; i < NB; i++) {
        const uint8_t *in = enc[i];
        size_t left = enclen[i];
        for (;;) {
          nghttp2_nv nv;
          int flags = 0;
          nghttp2_ssize k = nghttp2_hd_inflate_hd3(inf, &nv, &flags, in, left, 1);
          if (k < 0) { fprintf(stderr, "error\n"); return 1; }
          in += k;
          left -= (size_t)k;
          if (flags & NGHTTP2_HD_INFLATE_EMIT) sink += nv.valuelen;
          if (flags & NGHTTP2_HD_INFLATE_FINAL) break;
        }
        nghttp2_hd_inflate_end_headers(inf);
      }
      nghttp2_hd_inflate_del(inf);
    }
    double t = now() - t0;
    if (t < best) best = t;
  }
  printf("%.1f ns/block, %.0f MB/s decoded (%zu encoded bytes per %d blocks) [%llu]\n",
         best / rounds / NB * 1e9, decoded * (double)rounds / best / 1e6, total, NB, sink % 7);
  return 0;
}
