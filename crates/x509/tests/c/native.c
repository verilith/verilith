/* Tests of the native C API (include/vx509.h), for ASan and UBSan: parses
 * each DER file named on the command line, reads everything in it, and
 * prints a line per certificate. Then every truncation of each file must be
 * rejected without reading past its end. */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vx509.h"

static size_t walk_name(vx509_span name) {
    vx509_span rdn;
    vx509_atv a;
    size_t n = 0;
    while (vx509_rdn_next(&name, &rdn))
        while (vx509_atv_next(&rdn, &a)) {
            assert(a.oid.len > 0 && a.value.tag.len == 1);
            for (size_t i = 0; i < a.value.content.len; i++) n += a.value.content.p[i] == 0;
            n++;
        }
    return n;
}

static size_t walk_names(vx509_span l, bool subtrees) {
    vx509_general_name g;
    size_t n = 0;
    while (subtrees ? vx509_subtree_next(&l, &g) : vx509_general_name_next(&l, &g)) {
        assert(g.kind >= VX509_GN_OTHER && g.kind <= VX509_GN_REGISTERED_ID);
        if (g.kind == VX509_GN_DIRECTORY) walk_name(g.value);
        for (size_t i = 0; i < g.value.len; i++) n += g.value.p[i] == 0;
        n++;
    }
    return n;
}

static void walk(const vx509_cert *c, const char *file) {
    char text[64];
    vx509_span l, oid;
    vx509_ext e, f;
    vx509_basic_constraints bc;
    vx509_authority_key_id aki;
    vx509_name_constraints nc;
    uint16_t ku = 0;
    size_t exts = 0, sans = 0;

    assert(c->version >= 1 && c->version <= 3);
    assert(vx509_time_unix(&c->not_before) <= vx509_time_unix(&c->not_after) || c->not_after.year < c->not_before.year);
    size_t subject = walk_name(c->subject);
    walk_name(c->issuer);
    vx509_oid_text(c->signature_alg.oid.p, c->signature_alg.oid.len, text, sizeof text);

    l = c->extensions;
    while (vx509_ext_next(&l, &e)) {
        assert(vx509_ext_find(c, e.oid.p, e.oid.len, &f) && f.value.p == e.value.p && f.critical == e.critical);
        exts++;
    }
    bool is_ca = vx509_get_basic_constraints(c, &bc) && bc.ca;
    vx509_get_key_usage(c, &ku);
    if (vx509_get_ext_key_usage(c, &l)) while (vx509_oid_next(&l, &oid)) assert(oid.len > 0);
    if (vx509_get_certificate_policies(c, &l)) while (vx509_policy_next(&l, &oid)) assert(oid.len > 0);
    if (vx509_get_subject_alt_names(c, &l)) sans = walk_names(l, false);
    if (vx509_get_issuer_alt_names(c, &l)) walk_names(l, false);
    if (vx509_get_subject_key_id(c, &l)) assert(l.p);
    if (vx509_get_authority_key_id(c, &aki) && aki.issuer.p) walk_names(aki.issuer, false);
    if (vx509_get_name_constraints(c, &nc)) {
        if (nc.permitted.p) walk_names(nc.permitted, true);
        if (nc.excluded.p) walk_names(nc.excluded, true);
    }
    printf("%s: v%d sig=%s %04d-%02d-%02d..%04d-%02d-%02d subject_attrs=%zu exts=%zu sans=%zu ca=%d ku=0x%x\n", file,
           c->version, text, c->not_before.year, c->not_before.month, c->not_before.day, c->not_after.year,
           c->not_after.month, c->not_after.day, subject, exts, sans, is_ca, ku);
}

int main(int argc, char **argv) {
    vx509_cert c;
    size_t off;
    assert(argc > 1);
    for (int a = 1; a < argc; a++) {
        FILE *f = fopen(argv[a], "rb");
        if (!f) { perror(argv[a]); return 2; }
        fseek(f, 0, SEEK_END);
        size_t n = ftell(f);
        fseek(f, 0, SEEK_SET);
        uint8_t *buf = malloc(n);
        if (fread(buf, 1, n, f) != n) return 2;
        fclose(f);
        assert(vx509_cert_parse(buf, n, &c, &off) == VX509_OK);
        assert(c.tbs.p > buf && c.signature.p + c.signature.len == buf + n);
        walk(&c, argv[a]);
        assert(vx509_cert_parse(buf, n, NULL, NULL) == VX509_OK);
        /* Truncations, each in an allocation of exactly its size. */
        for (size_t i = 0; i < n; i++) {
            uint8_t *t = malloc(i ? i : 1);
            memcpy(t, buf, i);
            off = (size_t)-1;
            int r = vx509_cert_parse(t, i, &c, &off);
            assert(r >= VX509_E_OUTER && r <= VX509_E_SIGNATURE_VALUE && off <= i);
            free(t);
        }
        /* A changed signature algorithm outside the TBSCertificate. */
        buf[c.signature.p - buf - 8] ^= 1;
        assert(vx509_cert_parse(buf, n, &c, &off) != VX509_OK);
        free(buf);
    }
    assert(vx509_cert_parse(NULL, 0, &c, &off) == VX509_E_OUTER);
    assert(vx509_cert_parse(NULL, 4, &c, &off) == VX509_E_ARGUMENT);
    assert(vx509_oid_text((const uint8_t *)"\x55\x04\x03", 3, NULL, 0) == 7);
    puts("native C API: ok");
    return 0;
}
