/* mbedtls_x509_crt_parse_der timed the way bench/src/main.rs times the Rust
 * parsers. Build it twice, once against stock mbedTLS and once against the
 * vx509-backed build (see bench/README.md), and run each in its own process. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "mbedtls/x509_crt.h"

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static int once(const unsigned char *b, size_t n, int copy)
{
    mbedtls_x509_crt c;
    mbedtls_x509_crt_init(&c);
    int r = copy ? mbedtls_x509_crt_parse_der(&c, b, n) : mbedtls_x509_crt_parse_der_nocopy(&c, b, n);
    if (r != 0) {
        fprintf(stderr, "parse failed: -0x%04x\n", -r);
        exit(1);
    }
    r = (int) c.serial.len;
    mbedtls_x509_crt_free(&c);
    return r;
}

int main(int argc, char **argv)
{
    const char *label = argc > 1 ? argv[1] : "mbedTLS";
    const char *certs[] = { "leaf", "root-rsa", "root-ecdsa" };
    for (int k = 0; k < 3; k++) {
        char path[512];
        snprintf(path, sizeof path, "%s/%s.der", DATA_DIR, certs[k]);
        FILE *f = fopen(path, "rb");
        static unsigned char b[1 << 16];
        size_t n = fread(b, 1, sizeof b, f);
        fclose(f);
        for (int copy = 1; copy >= 0; copy--) {
            volatile int sink = 0;
            for (int i = 0; i < 1000; i++) sink += once(b, n, copy);
            double best = 1e9;
            for (int r = 0; r < 30; r++) {
                int iters = 20000;
                double t = now();
                for (int i = 0; i < iters; i++) sink += once(b, n, copy);
                double d = (now() - t) / iters;
                if (d < best) best = d;
            }
            printf("%s\t%s %s\t%.0f\n", certs[k], label,
                   copy ? "mbedtls_x509_crt_parse_der" : "mbedtls_x509_crt_parse_der_nocopy", best * 1e9);
        }
    }
    return 0;
}
