/* The same TurboJPEG calls against whichever library this is linked with:
 * libjpeg-turbo's libturbojpeg.a, or vjpeg built with --features
 * turbojpeg-abi. For each file it prints one line: the header fields and a
 * checksum of the pixels in every pixel format, top-down and bottom-up, with
 * a row pitch wider than the row. `make tjcheck` compares the two outputs. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <turbojpeg.h>

static uint64_t fnv(uint64_t h, const unsigned char *p, size_t n) {
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ULL; }
  return h;
}

int main(int argc, char **argv) {
  static const int fmts[] = { TJPF_RGB, TJPF_BGR, TJPF_RGBX, TJPF_BGRX, TJPF_XBGR, TJPF_XRGB,
                              TJPF_RGBA, TJPF_BGRA, TJPF_ABGR, TJPF_ARGB, TJPF_GRAY };
  for (int a = 1; a < argc; a++) {
    FILE *f = fopen(argv[a], "rb");
    if (!f) { perror(argv[a]); return 2; }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    unsigned char *buf = malloc(n ? n : 1);
    if (fread(buf, 1, n, f) != (size_t)n) return 2;
    fclose(f);
    const char *name = strrchr(argv[a], '/'); name = name ? name + 1 : argv[a];

    tjhandle h = tj3Init(TJINIT_DECOMPRESS);
    int w, ht, ss, cs;
    tjhandle old = tjInitDecompress();
    int r = tjDecompressHeader3(old, buf, n, &w, &ht, &ss, &cs);
    /* A warning (a damaged file) is not something vjpeg reports. */
    int oldfails = r != 0 && tjGetErrorCode(old) == TJERR_FATAL;
    if (tj3DecompressHeader(h, buf, n) != 0 && tj3GetErrorCode(h) == TJERR_FATAL) {
      printf("%s: header fails%s\n", name, oldfails ? "" : " (v3 only)"); goto next;
    }
    if (oldfails) {
      /* tjDecompressHeader3 refuses sampling it has no name for. */
      printf("(old header fails) ");
      w = tj3Get(h, TJPARAM_JPEGWIDTH); ht = tj3Get(h, TJPARAM_JPEGHEIGHT);
      ss = tj3Get(h, TJPARAM_SUBSAMP); cs = tj3Get(h, TJPARAM_COLORSPACE);
    }
    if (tj3Get(h, TJPARAM_JPEGWIDTH) != w || tj3Get(h, TJPARAM_JPEGHEIGHT) != ht ||
        tj3Get(h, TJPARAM_SUBSAMP) != ss || tj3Get(h, TJPARAM_COLORSPACE) != cs) {
      printf("%s: tj3Get disagrees with tjDecompressHeader3\n", name); goto next;
    }
    printf("%s: %dx%d ss=%d cs=%d prog=%d", name, w, ht, ss, cs, tj3Get(h, TJPARAM_PROGRESSIVE));
    for (unsigned k = 0; k < sizeof fmts / sizeof *fmts; k++) {
      int pf = fmts[k];
      if (pf == TJPF_GRAY && cs != TJCS_GRAY) continue;
      /* A padded pitch, then the exact one: vjpeg decodes straight into
       * the caller's buffer when it can. */
      for (int pad = 5; pad >= 0; pad -= 5) {
        int pitch = w * tjPixelSize[pf] + pad;
        size_t sz = (size_t)pitch * ht;
        unsigned char *px = malloc(sz), *px2 = malloc(sz);
        memset(px, 0x5A, sz); memset(px2, 0x5A, sz);
        for (int bu = 0; bu < 2; bu++) {
          tj3Set(h, TJPARAM_BOTTOMUP, bu);
          int r1 = tj3Decompress8(h, buf, n, px, pitch, pf);
          int r2 = tjDecompress2(old, buf, n, px2, bu ? w : 0, pitch, ht, pf, bu ? TJFLAG_BOTTOMUP : 0);
          int f1 = r1 != 0 && tj3GetErrorCode(h) == TJERR_FATAL;
          int f2 = r2 != 0 && tjGetErrorCode(old) == TJERR_FATAL;
          if (f1 || f2) { printf(" pf%d:fails", pf); continue; }
          if (memcmp(px, px2, sz)) { printf(" pf%d:v3-and-v2-differ", pf); continue; }
          printf(" %016llx", (unsigned long long)fnv(1469598103934665603ULL, px, sz));
        }
        free(px); free(px2);
      }
    }
    printf("\n");
  next:
    tj3Destroy(h); tjDestroy(old); free(buf);
  }
  return 0;
}
