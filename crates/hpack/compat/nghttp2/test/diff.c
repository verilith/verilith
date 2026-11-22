/* Differential test of vhpack's nghttp2 inflater against nghttp2's own.
 *
 *   diff SEED COUNT
 *
 * Linked once with stock nghttp2 and once with nghttp2 patched by
 * compat/nghttp2/patch.py (plus libverilith_hpack.a); run.sh compares the outputs,
 * which must be identical. For each case it encodes random header lists
 * with nghttp2's deflater (the same code in both builds), with random
 * SETTINGS_HEADER_TABLE_SIZE changes, optionally corrupts the encoded
 * block, then decodes it with the inflater in random pieces, and prints
 * every emitted field (name, value, never-indexed flag), the dynamic
 * table's size, and errors. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <nghttp2/nghttp2.h>

static unsigned long long rs;
static unsigned rnd(unsigned n) {
  rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
  return (unsigned)((rs * 0x2545F4914F6CDD1DULL) >> 33) % (n ? n : 1);
}

static const char *NAMES[] = {":method", ":path", ":authority", "content-type", "cookie",
                              "user-agent", "x-custom", "set-cookie", "accept-encoding",
                              "x-a-much-longer-header-name-for-tests", "authorization"};
static const char *VALUES[] = {"GET", "/", "/index.html?q=1", "example.com", "text/html",
                               "a=b; c=d", "", "Mozilla/5.0 (X11; Linux x86_64)", "gzip, br",
                               "\x01\x7f\xff binary", "Bearer abc.def"};

static void pr(const char *tag, const uint8_t *s, size_t n) {
  printf("%s %zu:", tag, n);
  for (size_t i = 0; i < n; i++) printf("%02x", s[i]);
  printf("\n");
}

int main(int argc, char **argv) {
  unsigned long long seed = (unsigned long long)atoll(argv[1]);
  int count = atoi(argv[2]);
  static uint8_t buf[1 << 20];
  static char vals[64][3000];
  for (int c = 0; c < count; c++) {
    /* Each case has its own stream of random numbers, so that how a
       decoder fails in one case cannot change the next. */
    rs = (seed * 1000003ULL + (unsigned long long)c) * 0x9E3779B97F4A7C15ULL + 1;
    nghttp2_hd_deflater *def;
    nghttp2_hd_inflater *inf;
    nghttp2_hd_deflate_new(&def, 4096);
    nghttp2_hd_inflate_new(&inf);
    printf("case %d\n", c);
    int blocks = 1 + rnd(5);
    for (int b = 0; b < blocks; b++) {
      if (rnd(4) == 0) {
        size_t ts = rnd(3) == 0 ? rnd(300) : rnd(8192);
        int r1 = nghttp2_hd_deflate_change_table_size(def, ts);
        int r2 = nghttp2_hd_inflate_change_table_size(inf, ts);
        printf("settings %zu -> %d %d\n", ts, r1, r2);
      }
      nghttp2_nv nva[64];
      int n = rnd(20);
      for (int i = 0; i < n; i++) {
        const char *nm = NAMES[rnd(11)];
        nva[i].name = (uint8_t *)nm;
        nva[i].namelen = strlen(nm);
        if (rnd(6) == 0) {
          size_t l = rnd(10) == 0 ? rnd(3000) : rnd(60);
          for (size_t j = 0; j < l; j++) vals[i][j] = (char)(rnd(3) ? 'a' + rnd(26) : rnd(256));
          nva[i].value = (uint8_t *)vals[i];
          nva[i].valuelen = l;
        } else {
          const char *v = VALUES[rnd(11)];
          nva[i].value = (uint8_t *)v;
          nva[i].valuelen = strlen(v);
        }
        nva[i].flags = rnd(8) == 0 ? NGHTTP2_NV_FLAG_NO_INDEX : NGHTTP2_NV_FLAG_NONE;
      }
      nghttp2_ssize len = nghttp2_hd_deflate_hd2(def, buf, sizeof(buf), nva, (size_t)n);
      if (len < 0) { printf("deflate error %zd\n", (ssize_t)len); break; }
      /* Corrupt some blocks. */
      if (rnd(3) == 0 && len > 0) {
        int k = 1 + rnd(3);
        for (int j = 0; j < k; j++) {
          size_t at = rnd((unsigned)len);
          switch (rnd(3)) {
          case 0: buf[at] = (uint8_t)rnd(256); break;
          case 1: buf[at] ^= (uint8_t)(1 << rnd(8)); break;
          default: len = (nghttp2_ssize)at; break; /* truncate */
          }
        }
      }
      /* Decode in random pieces. */
      size_t off = 0;
      int done = 0, failed = 0;
      while (!done) {
        size_t piece = rnd(2) ? (size_t)len - off : rnd(9);
        if (off + piece > (size_t)len) piece = (size_t)len - off;
        int fin = off + piece == (size_t)len;
        const uint8_t *in = buf + off;
        size_t left = piece;
        for (;;) {
          nghttp2_nv nv;
          int flags = 0;
          nghttp2_ssize r = nghttp2_hd_inflate_hd3(inf, &nv, &flags, in, left, fin);
          if (r < 0) { printf("error %s\n", nghttp2_strerror((int)r)); failed = 1; done = 1; break; }
          in += r;
          left -= (size_t)r;
          if (flags & NGHTTP2_HD_INFLATE_EMIT) {
            pr("n", nv.name, nv.namelen);
            pr("v", nv.value, nv.valuelen);
            printf("f %d\n", nv.flags & NGHTTP2_NV_FLAG_NO_INDEX ? 1 : 0);
          }
          if (flags & NGHTTP2_HD_INFLATE_FINAL) { done = 1; break; }
          if (left == 0 && !(flags & NGHTTP2_HD_INFLATE_EMIT)) break;
        }
        off += piece;
        if (fin && !done) { printf("no final\n"); done = 1; }
      }
      if (failed) break;
      nghttp2_hd_inflate_end_headers(inf);
      printf("table %zu/%zu entries %zu\n", nghttp2_hd_inflate_get_dynamic_table_size(inf),
             nghttp2_hd_inflate_get_max_dynamic_table_size(inf),
             nghttp2_hd_inflate_get_num_table_entries(inf));
      size_t ne = nghttp2_hd_inflate_get_num_table_entries(inf);
      for (size_t i = 62; i <= ne; i++) {
        const nghttp2_nv *e = nghttp2_hd_inflate_get_table_entry(inf, i);
        pr(" e", e->name, e->namelen);
        pr(" ev", e->value, e->valuelen);
      }
    }
    nghttp2_hd_deflate_del(def);
    nghttp2_hd_inflate_del(inf);
  }
  return 0;
}
