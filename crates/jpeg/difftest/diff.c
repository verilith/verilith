// Differential test against libjpeg-turbo: decodes each file with both and
// compares every byte of the output. libjpeg runs with its defaults (the
// accurate integer DCT, fancy upsampling) except block smoothing, which
// vjpeg does not do: it only changes progressive files whose scans stop
// early.
//
//   diff FILE...        compare, print a line per difference and a summary
//   (built with -DFUZZ) a libFuzzer target that aborts on a difference
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <jpeglib.h>

uint8_t *vjpeg_decode(const uint8_t *data, size_t len, uint32_t *w, uint32_t *h, uint32_t *nc);
void vjpeg_free(uint8_t *p, size_t len);

struct err {
  struct jpeg_error_mgr pub;
  jmp_buf jb;
};
static void on_error(j_common_ptr c) { longjmp(((struct err *)c->err)->jb, 1); }
static void on_message(j_common_ptr c, int level) { (void)c; (void)level; }

// Returns the pixels (malloc), or NULL if libjpeg rejects the file or it is
// of a kind vjpeg does not take (*unsupported set).
static uint8_t *ref_decode(const uint8_t *data, size_t len, uint32_t *w, uint32_t *h, uint32_t *nc,
                           int *unsupported) {
  struct jpeg_decompress_struct c;
  struct err e;
  uint8_t *volatile out = NULL;
  *unsupported = 0;
  c.err = jpeg_std_error(&e.pub);
  e.pub.error_exit = on_error;
  e.pub.emit_message = on_message;
  if (setjmp(e.jb)) {
    jpeg_destroy_decompress(&c);
    free(out);
    return NULL;
  }
  jpeg_create_decompress(&c);
  jpeg_mem_src(&c, data, len);
  jpeg_read_header(&c, TRUE);
  if (c.arith_code || c.data_precision != 8 || (c.num_components != 1 && c.num_components != 3) ||
      c.master == NULL) {
    *unsupported = 1;
    jpeg_destroy_decompress(&c);
    return NULL;
  }
  c.do_block_smoothing = FALSE;
  // Keep memory bounded when fuzzing.
  if ((uint64_t)c.image_width * c.image_height > (1u << 24)) {
    *unsupported = 1;
    jpeg_destroy_decompress(&c);
    return NULL;
  }
  jpeg_start_decompress(&c);
  *w = c.output_width;
  *h = c.output_height;
  *nc = c.output_components;
  out = malloc((size_t)*w * *h * *nc + 1);
  while (c.output_scanline < c.output_height) {
    JSAMPROW row = out + (size_t)c.output_scanline * *w * *nc;
    jpeg_read_scanlines(&c, &row, 1);
  }
  jpeg_finish_decompress(&c);
  jpeg_destroy_decompress(&c);
  return out;
}

// 0 same, 1 both reject, 2 differ, 3 skipped.
static int compare(const uint8_t *data, size_t len, const char *name) {
  uint32_t rw = 0, rh = 0, rn = 0, vw = 0, vh = 0, vn = 0;
  int unsupported;
  uint8_t *r = ref_decode(data, len, &rw, &rh, &rn, &unsupported);
  if (unsupported) return 3;
  uint8_t *v = vjpeg_decode(data, len, &vw, &vh, &vn);
  int res;
  if (!r && !v) {
    res = vn == 2 ? 3 : 1;
  } else if (!r || !v) {
    if (!v && vn == 2) {
      res = 3;
    } else {
      fprintf(stderr, "%s: libjpeg %s, vjpeg %s\n", name, r ? "decodes" : "rejects", v ? "decodes" : "rejects");
      res = 2;
    }
  } else if (rw != vw || rh != vh || rn != vn) {
    fprintf(stderr, "%s: size %ux%ux%u vs %ux%ux%u\n", name, rw, rh, rn, vw, vh, vn);
    res = 2;
  } else if (memcmp(r, v, (size_t)rw * rh * rn) != 0) {
    size_t i = 0, n = (size_t)rw * rh * rn, cnt = 0;
    size_t first = n;
    for (i = 0; i < n; i++)
      if (r[i] != v[i]) {
        if (first == n) first = i;
        cnt++;
      }
    fprintf(stderr, "%s: %zu of %zu bytes differ, first at %zu (%u vs %u)\n", name, cnt, n, first, r[first],
            v[first]);
    res = 2;
  } else {
    res = 0;
  }
  free(r);
  if (v) vjpeg_free(v, (size_t)vw * vh * vn);
  return res;
}

#ifdef FUZZ
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (compare(data, size, "input") == 2) abort();
  return 0;
}
#else
int main(int argc, char **argv) {
  long counts[4] = {0, 0, 0, 0};
  for (int i = 1; i < argc; i++) {
    FILE *f = fopen(argv[i], "rb");
    if (!f) {
      perror(argv[i]);
      return 2;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *d = malloc(n + 1);
    if (fread(d, 1, n, f) != (size_t)n) return 2;
    fclose(f);
    counts[compare(d, n, argv[i])]++;
    free(d);
  }
  printf("same %ld, both reject %ld, differ %ld, skipped %ld\n", counts[0], counts[1], counts[2], counts[3]);
  return counts[2] != 0;
}
#endif
