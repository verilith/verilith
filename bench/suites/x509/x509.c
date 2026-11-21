/* X.509 suite. One driver against mbedTLS's certificate API, linked once
 * with stock mbedTLS and once with mbedTLS patched to use vx509 as its
 * certificate decoder (vx509/mbedtls), the 20-line swap embedded users
 * would make.
 *
 *   parse/NAME     mbedtls_x509_crt_parse_der of NAME.der, then free
 *   parse/roots    every root in roots/ (Mozilla's bundle, via certifi)
 *                  parsed into one chain, then freed
 * check = certificates parsed * 1000 + total serial length.
 *
 *   x509-run read  cases read/NAME and read/roots: the task the native
 *                  comparison uses (runners/vx509-run read). Parse with
 *                  mbedtls_x509_crt_parse_der_nocopy, mbedTLS's cheapest
 *                  entry point, then read what a TLS client reads: serial,
 *                  every issuer and subject attribute, both validity times,
 *                  key usage, the CA flag, the DNS subjectAltNames and the
 *                  extended key usages; then free.
 * check = certificates * 1000003 + a sum over everything read. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* key_usage and ca_istrue are private fields in 3.x; this is mbedTLS's own
 * switch for reading them. */
#define MBEDTLS_ALLOW_PRIVATE_ACCESS
#include "mbedtls/x509_crt.h"
#include "runner.h"

struct item { size_t n; unsigned char **buf; size_t *len; };

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    mbedtls_x509_crt c;
    mbedtls_x509_crt_init(&c);
    for (size_t i = 0; i < it->n; i++)
        if (mbedtls_x509_crt_parse_der(&c, it->buf[i], it->len[i]) != 0) abort();
    uint64_t k = 0, s = 0;
    for (mbedtls_x509_crt *p = &c; p; p = p->next) { k++; s += p->serial.len; }
    mbedtls_x509_crt_free(&c);
    return k * 1000 + s;
}

static uint64_t name_bytes(const mbedtls_x509_name *n)
{
    uint64_t s = 0;
    for (; n; n = n->next) s += n->val.len;
    return s;
}

/* Entries of a list; with TAG >= 0 only those with that tag. An absent
 * extension leaves one entry with no data. */
static uint64_t seq_count(const mbedtls_x509_sequence *q, int tag)
{
    uint64_t k = 0;
    for (; q; q = q->next)
        if (q->buf.p && (tag < 0 || q->buf.tag == tag)) k++;
    return k;
}

static uint64_t do_read(void *ctx)
{
    struct item *it = (struct item *)ctx;
    mbedtls_x509_crt c;
    mbedtls_x509_crt_init(&c);
    for (size_t i = 0; i < it->n; i++)
        if (mbedtls_x509_crt_parse_der_nocopy(&c, it->buf[i], it->len[i]) != 0) abort();
    uint64_t k = 0, s = 0;
    for (mbedtls_x509_crt *p = &c; p; p = p->next) {
        k++;
        s += p->serial.len + name_bytes(&p->issuer) + name_bytes(&p->subject);
        s += (uint64_t)p->valid_from.year + p->valid_from.sec + p->valid_to.year + p->valid_to.sec;
        s += (uint64_t)__builtin_popcount(p->key_usage) + (p->ca_istrue != 0);
        s += seq_count(&p->subject_alt_names, MBEDTLS_ASN1_CONTEXT_SPECIFIC | 2);
        s += seq_count(&p->ext_key_usage, -1);
    }
    mbedtls_x509_crt_free(&c);
    return k * 1000003u + s;
}

static struct item *load(const char *dir, char **names, size_t n)
{
    struct item *it = (struct item *)calloc(1, sizeof *it);
    it->buf = (unsigned char **)calloc(n, sizeof *it->buf);
    it->len = (size_t *)calloc(n, sizeof *it->len);
    for (size_t i = 0; i < n; i++) {
        char p[4096];
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf[it->n] = vb_read_file(p, &it->len[it->n]);
        mbedtls_x509_crt c;
        mbedtls_x509_crt_init(&c);
        int r = mbedtls_x509_crt_parse_der(&c, it->buf[it->n], it->len[it->n]);
        mbedtls_x509_crt_free(&c);
        if (r != 0) { fprintf(stderr, "skipping %s: mbedTLS error -0x%04x\n", names[i], -r); continue; }
        it->n++;
    }
    return it;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "parse";
    vb_fn fn = strcmp(mode, "read") ? do_parse : do_read;
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 5 || strcmp(names[i] + l - 4, ".der")) continue;
        struct item *it = load(dir, &names[i], 1);
        if (!it->n) continue;
        char cname[512];
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "%s/%s", mode, names[i]);
        vb_case(cname, it->len[0], fn, it);
    }
    char rdir[4096];
    snprintf(rdir, sizeof rdir, "%s/roots", dir);
    char **roots;
    size_t nr = vb_list_dir(rdir, &roots);
    struct item *all = load(rdir, roots, nr);
    uint64_t total = 0;
    for (size_t i = 0; i < all->n; i++) total += all->len[i];
    char rname[64];
    snprintf(rname, sizeof rname, "%s/roots", mode);
    vb_case(rname, total, fn, all);
    return vb_main();
}
