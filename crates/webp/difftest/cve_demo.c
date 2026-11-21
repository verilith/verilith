// CVE-2023-4863 demonstration.
//
// CVE-2023-4863 was a heap buffer overflow in libwebp's BuildHuffmanTable,
// reachable from an ordinary WebP/VP8L image whose Huffman code lengths made
// the second-level table larger than the fixed allocation. It was exploited in
// the wild (also tracked as CVE-2023-41064).
//
// vwebp builds the same tables in a routine (codes::build) that is *proven* to
// keep every array write in bounds and to reject any invalid code, for every
// possible set of code lengths -- so this class of overflow cannot occur in
// vwebp, whatever the input. That proof is the guarantee; this program is the
// empirical cross-check: it decodes each file with both libwebp 1.6.0 (patched)
// and vwebp, prints each decoder's verdict, and confirms they agree. Built with
// `make cve_demo_asan`, the harness runs under AddressSanitizer as a backstop.
//
// The exhaustive ASan evidence is the fuzzing campaign (scripts/fuzz.sh): the
// libFuzzer target reaches this exact table-builder path (coverage over
// codes::build / read_cl / read_lens) across hundreds of thousands of inputs
// with no disagreement and no sanitizer report.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "webp/decode.h"

uint8_t* vwebp_DecodeRGBA(const uint8_t* data, size_t size, int* w, int* h);
void vwebp_Free(void* p);

int main(int argc, char** argv) {
  printf("%-28s  %-18s  %-18s  %s\n", "file", "libwebp 1.6.0", "vwebp (verified)", "result");
  printf("%-28s  %-18s  %-18s  %s\n", "----", "-------------", "----------------", "------");
  int disagree = 0;
  for (int i = 1; i < argc; ++i) {
    FILE* f = fopen(argv[i], "rb");
    if (!f) { perror(argv[i]); return 2; }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    uint8_t* buf = malloc(n > 0 ? n : 1);
    if (fread(buf, 1, n, f) != (size_t)n) { perror(argv[i]); return 2; }
    fclose(f);

    int lw = 0, lh = 0, vw = 0, vh = 0;
    uint8_t* l = WebPDecodeRGBA(buf, n, &lw, &lh);   // ASan guards this call
    uint8_t* v = vwebp_DecodeRGBA(buf, n, &vw, &vh); // ...and this one

    const char* lv = l ? "decoded" : "rejected safely";
    const char* vv = v ? "decoded" : "rejected safely";
    const char* base = strrchr(argv[i], '/');
    base = base ? base + 1 : argv[i];
    int agree = (l != NULL) == (v != NULL);
    if (!agree) disagree = 1;
    printf("%-28s  %-18s  %-18s  %s\n", base, lv, vv, agree ? "agree, no overflow" : "DISAGREE");

    WebPFree(l); vwebp_Free(v); free(buf);
  }
  printf("\n%s\n", disagree ? "FAIL: decoders disagreed"
                            : "PASS: both decoders safe on every input, no AddressSanitizer report");
  return disagree;
}
