/* ns per message through llhttp's API, as Node.js drives it: a fresh
 * parser state per message, and the URL, status and every header name and
 * value delivered to callbacks. Linked once with llhttp and once with
 * vhttp's drop-in, like trace.c.
 *
 *   bench (req|res) FILE...   (prints one line per file) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "llhttp.h"

static size_t spans;
static int on_span(llhttp_t* p, const char* at, size_t len) {
  (void)p;
  (void)at;
  spans += len;
  return 0;
}
static int on_hc(llhttp_t* p) {
  (void)p;
  return 0;
}

static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1e9 + t.tv_nsec;
}

int main(int argc, char** argv) {
  if (argc < 3) return 2;
  llhttp_settings_t s;
  llhttp_settings_init(&s);
  s.on_url = on_span;
  s.on_status = on_span;
  s.on_header_field = on_span;
  s.on_header_value = on_span;
  s.on_headers_complete = on_hc;
  llhttp_type_t type = strcmp(argv[1], "req") == 0 ? HTTP_REQUEST : HTTP_RESPONSE;
  for (int a = 2; a < argc; a++) {
    static char buf[1 << 16];
    FILE* f = fopen(argv[a], "rb");
    if (!f) return 2;
    size_t n = fread(buf, 1, sizeof(buf), f);
    fclose(f);
    double best = 1e30;
    int batches = getenv("BENCH_BATCHES") ? atoi(getenv("BENCH_BATCHES")) : 15;
    int iters = getenv("BENCH_ITERS") ? atoi(getenv("BENCH_ITERS")) : 50000;
    for (int batch = 0; batch < batches; batch++) {
      double t0 = now();
      for (int i = 0; i < iters; i++) {
        llhttp_t p;
        llhttp_init(&p, type, &s);
        if (llhttp_execute(&p, buf, n) != HPE_OK) {
          fprintf(stderr, "%s: %s\n", argv[a], llhttp_errno_name(llhttp_get_errno(&p)));
          return 1;
        }
      }
      double t = (now() - t0) / iters;
      if (t < best) best = t;
    }
    printf("%s %.0f\n", argv[a], best);
  }
  return spans == 0;
}
