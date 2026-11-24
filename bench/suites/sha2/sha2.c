/* sha2 suite. One driver, written against OpenSSL's SHA-2 API (sha.h),
 * linked once with OpenSSL's libcrypto and once with verilith-sha2's C ABI
 * (feature openssl-abi), so the only thing that differs between the two
 * runners is the library.
 *
 *   sha2 MODE   MODE is one of
 *     sha256          sha256/FILE: SHA256() of the whole file
 *     sha512          sha512/FILE: SHA512() of the whole file
 *     sha256-stream   sha256-stream/FILE: SHA256_Init, SHA256_Update in
 *                     pieces of 1000 bytes, SHA256_Final
 *     sha512-stream   the same with SHA512_*
 *
 * The check value is taken from the digest, so the two libraries must
 * agree on every input. Inputs are the files in $VBENCH_DATA: messages of
 * 16, 64, 256 and 1024 bytes, and 4 KiB, 64 KiB and the whole of dickens.
 */
#define OPENSSL_SUPPRESS_DEPRECATED
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <openssl/sha.h>
#include "runner.h"

struct item {
    const unsigned char *in;
    size_t len;
};

static uint64_t check(const unsigned char *md, size_t n)
{
    uint64_t h = 0xcbf29ce484222325ull;
    for (size_t i = 0; i < n; i++) h = (h ^ md[i]) * 0x100000001b3ull;
    return h;
}

static uint64_t do_sha256(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char md[32];
    SHA256(it->in, it->len, md);
    return check(md, sizeof md);
}

static uint64_t do_sha512(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char md[64];
    SHA512(it->in, it->len, md);
    return check(md, sizeof md);
}

#define PIECE 1000

static uint64_t do_sha256_stream(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char md[32];
    SHA256_CTX c;
    if (!SHA256_Init(&c)) abort();
    for (size_t i = 0; i < it->len; i += PIECE) {
        size_t n = it->len - i < PIECE ? it->len - i : PIECE;
        if (!SHA256_Update(&c, it->in + i, n)) abort();
    }
    if (!SHA256_Final(md, &c)) abort();
    return check(md, sizeof md);
}

static uint64_t do_sha512_stream(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char md[64];
    SHA512_CTX c;
    if (!SHA512_Init(&c)) abort();
    for (size_t i = 0; i < it->len; i += PIECE) {
        size_t n = it->len - i < PIECE ? it->len - i : PIECE;
        if (!SHA512_Update(&c, it->in + i, n)) abort();
    }
    if (!SHA512_Final(md, &c)) abort();
    return check(md, sizeof md);
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "sha256";
    uint64_t (*fn)(void *), (*whole)(void *);
    if (!strcmp(mode, "sha256")) fn = whole = do_sha256;
    else if (!strcmp(mode, "sha512")) fn = whole = do_sha512;
    else if (!strcmp(mode, "sha256-stream")) { fn = do_sha256_stream; whole = do_sha256; }
    else if (!strcmp(mode, "sha512-stream")) { fn = do_sha512_stream; whole = do_sha512; }
    else { fprintf(stderr, "sha2: unknown mode %s\n", mode); return 2; }
    char **names;
    const char *dir = vb_data_dir();
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->in = vb_read_file(p, &it->len);
        /* Streamed and whole must agree, within the same library. */
        if (fn(it) != whole(it)) {
            fprintf(stderr, "sha2: streamed and one-shot %s of %s differ\n", mode, names[i]);
            return 1;
        }
        snprintf(cname, sizeof cname, "%s/%s", mode, names[i]);
        vb_case(cname, it->len, fn, it);
    }
    return vb_main();
}
