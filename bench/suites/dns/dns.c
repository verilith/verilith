/* DNS suite. One driver against c-ares's record API, linked once with stock
 * c-ares and once with c-ares patched to use vdns for every message it
 * parses or writes (vdns/cares), which is exactly how c-ares users and
 * Node.js would get vdns.
 *
 *   dns-run parse   cases parse/MSG: ares_dns_parse + ares_dns_record_destroy;
 *                   check = records in all sections
 *   dns-run write   cases write/MSG: ares_dns_write of the record parsed
 *                   from MSG (check = bytes written)
 *   dns-run read    cases read/MSG: the task the native comparison uses
 *                   (runners/vdns-run): ares_dns_parse, then read every
 *                   question and every record (owner name, type, class,
 *                   TTL and each RDATA field), then destroy;
 *                   check = questions and records * 1000003 + the sum of
 *                   their types and classes and the records' TTLs
 *                   (for an OPT record, its type only)
 *
 * Messages are the *.dns files in $VBENCH_DATA (data/dns/make.py).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ares.h>
#include "runner.h"

struct item { unsigned char *buf; size_t len; ares_dns_record_t *rec; };

static uint64_t count(const ares_dns_record_t *r)
{
    return ares_dns_record_rr_cnt(r, ARES_SECTION_ANSWER) + ares_dns_record_rr_cnt(r, ARES_SECTION_AUTHORITY) +
           ares_dns_record_rr_cnt(r, ARES_SECTION_ADDITIONAL) + ares_dns_record_query_cnt(r);
}

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    ares_dns_record_t *r = NULL;
    if (ares_dns_parse(it->buf, it->len, 0, &r) != ARES_SUCCESS) abort();
    uint64_t n = count(r);
    ares_dns_record_destroy(r);
    return n;
}

/* Where values that are read but not part of the check go. */
static volatile uint64_t sink;

static uint64_t read_rr(const ares_dns_rr_t *rr)
{
    ares_dns_rec_type_t t = ares_dns_rr_get_type(rr);
    uint64_t seen = strlen(ares_dns_rr_get_name(rr));
    size_t nk = 0, len;
    const ares_dns_rr_key_t *keys = ares_dns_rr_get_keys(t, &nk);
    for (size_t i = 0; i < nk; i++) {
        ares_dns_rr_key_t k = keys[i];
        switch (ares_dns_rr_key_datatype(k)) {
        case ARES_DATATYPE_INADDR: seen += ares_dns_rr_get_addr(rr, k)->s_addr; break;
        case ARES_DATATYPE_INADDR6: seen += ((const unsigned char *)ares_dns_rr_get_addr6(rr, k))[15]; break;
        case ARES_DATATYPE_U8: seen += ares_dns_rr_get_u8(rr, k); break;
        case ARES_DATATYPE_U16: seen += ares_dns_rr_get_u16(rr, k); break;
        case ARES_DATATYPE_U32: seen += ares_dns_rr_get_u32(rr, k); break;
        case ARES_DATATYPE_NAME:
        case ARES_DATATYPE_STR: seen += strlen(ares_dns_rr_get_str(rr, k)); break;
        case ARES_DATATYPE_BIN:
        case ARES_DATATYPE_BINP: (void)ares_dns_rr_get_bin(rr, k, &len); seen += len; break;
        case ARES_DATATYPE_ABINP: seen += ares_dns_rr_get_abin_cnt(rr, k); break;
        case ARES_DATATYPE_OPT: seen += ares_dns_rr_get_opt_cnt(rr, k); break;
        default: break;
        }
    }
    sink += seen;
    /* An OPT record's class and TTL fields carry EDNS values, which c-ares
     * reports as RDATA fields (read above), so they stay out of the check. */
    if (t == ARES_REC_TYPE_OPT) return (uint64_t)t;
    return (uint64_t)t + ares_dns_rr_get_class(rr) + ares_dns_rr_get_ttl(rr);
}

static uint64_t do_read(void *ctx)
{
    struct item *it = (struct item *)ctx;
    ares_dns_record_t *r = NULL;
    if (ares_dns_parse(it->buf, it->len, 0, &r) != ARES_SUCCESS) abort();
    uint64_t k = 0, s = 0;
    for (size_t i = 0; i < ares_dns_record_query_cnt(r); i++) {
        const char *name;
        ares_dns_rec_type_t qt;
        ares_dns_class_t qc;
        if (ares_dns_record_query_get(r, i, &name, &qt, &qc) != ARES_SUCCESS) abort();
        sink += strlen(name);
        s += (uint64_t)qt + qc;
        k++;
    }
    static const ares_dns_section_t sect[3] = {ARES_SECTION_ANSWER, ARES_SECTION_AUTHORITY, ARES_SECTION_ADDITIONAL};
    for (int j = 0; j < 3; j++)
        for (size_t i = 0; i < ares_dns_record_rr_cnt(r, sect[j]); i++) {
            s += read_rr(ares_dns_record_rr_get_const(r, sect[j], i));
            k++;
        }
    ares_dns_record_destroy(r);
    return k * 1000003u + s;
}

static uint64_t do_write(void *ctx)
{
    struct item *it = (struct item *)ctx;
    unsigned char *out = NULL;
    size_t n = 0;
    if (ares_dns_write(it->rec, &out, &n) != ARES_SUCCESS) abort();
    ares_free_string(out);
    return n;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "parse";
    if (ares_library_init(ARES_LIB_INIT_ALL) != ARES_SUCCESS) return 1;
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 5 || strcmp(names[i] + l - 4, ".dns")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        if (ares_dns_parse(it->buf, it->len, 0, &it->rec) != ARES_SUCCESS) {
            fprintf(stderr, "c-ares rejects %s\n", names[i]);
            return 1;
        }
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "%s/%s", mode, names[i]);
        vb_case(cname, it->len, !strcmp(mode, "write") ? do_write : !strcmp(mode, "read") ? do_read : do_parse, it);
    }
    return vb_main();
}
