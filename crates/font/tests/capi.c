/* Exercises the C interface: capi FONT. Exit status 0 on success. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "vfont.h"

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 2;
  static uint8_t buf[1 << 20];
  size_t n = fread(buf, 1, sizeof buf, f);
  fclose(f);

  uint8_t *out = NULL;
  size_t out_len = 0;
  if (!vfont_sanitize(buf, n, 0, &out, &out_len) || !out || !out_len) {
    fprintf(stderr, "font refused\n");
    return 1;
  }
  /* The output is a fixed point. */
  uint8_t *again = NULL;
  size_t again_len = 0;
  if (!vfont_sanitize(out, out_len, 0, &again, &again_len) ||
      again_len != out_len || memcmp(out, again, out_len) != 0) {
    fprintf(stderr, "not idempotent\n");
    return 1;
  }
  vfont_free(again, again_len);
  vfont_free(out, out_len);

  /* Refusals leave NULL and 0 behind. */
  out = (uint8_t *)1;
  out_len = 1;
  if (vfont_sanitize(buf, 10, 0, &out, &out_len) || out || out_len) return 1;
  if (vfont_sanitize(NULL, 0, 0, &out, &out_len) || out || out_len) return 1;
  if (vfont_sanitize(NULL, 5, 0, &out, &out_len)) return 1;
  if (vfont_sanitize(buf, n, 0, NULL, &out_len)) return 1;
  vfont_free(NULL, 0);
  puts("capi ok");
  return 0;
}
