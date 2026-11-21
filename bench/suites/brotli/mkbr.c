/* mkbr IN OUT QUALITY: compresses IN with google/brotli's encoder at QUALITY
 * (window 22, generic mode) into OUT. Makes the inputs of the brotli suite. */
#include <stdio.h>
#include <stdlib.h>
#include <brotli/encode.h>

int main(int argc, char **argv)
{
    if (argc != 4) { fprintf(stderr, "usage: mkbr IN OUT QUALITY\n"); return 2; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror(argv[1]); return 1; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *in = (unsigned char *)malloc(n ? (size_t)n : 1);
    if (fread(in, 1, (size_t)n, f) != (size_t)n) { perror(argv[1]); return 1; }
    fclose(f);
    size_t m = BrotliEncoderMaxCompressedSize((size_t)n);
    if (m == 0) m = (size_t)n + 1024;
    unsigned char *out = (unsigned char *)malloc(m);
    if (!BrotliEncoderCompress(atoi(argv[3]), 22, BROTLI_MODE_GENERIC, (size_t)n, in, &m, out)) {
        fprintf(stderr, "mkbr: cannot compress %s\n", argv[1]);
        return 1;
    }
    f = fopen(argv[2], "wb");
    if (!f || fwrite(out, 1, m, f) != m || fclose(f)) { perror(argv[2]); return 1; }
    return 0;
}
