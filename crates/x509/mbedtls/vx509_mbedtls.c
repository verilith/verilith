/*
 * vx509 as mbedTLS's certificate parser.
 *
 * This file is #included into mbedTLS's library/x509_crt.c by
 * mbedtls-use-vx509.patch, which makes x509_crt_parse_der_core() call
 * vx509_crt_parse_der_core() below. Every byte range stored in the
 * mbedtls_x509_crt comes from vx509's verified parser (through the C ABI in
 * vx509's src/mbedtls.rs); this file only copies those ranges into
 * mbedTLS's structure and applies mbedTLS's own policies on top (which
 * extensions it supports, the extension callback, the signature algorithm
 * table). The SubjectPublicKeyInfo is still decoded by mbedTLS's key parser,
 * on the SPKI TLV vx509 has checked.
 *
 * SPDX-License-Identifier: MIT
 */

typedef struct { const unsigned char *p; size_t len; } vx509_span;
typedef struct { int year, mon, day, hour, min, sec; } vx509_time;
typedef struct { vx509_span oid; int val_tag; vx509_span val; int merged; } vx509_atv;
#define VX509_NAME_CAP 8
/* An extension and what vx509's verified check decoded from its value
 * (src/mbedtls.rs VExtOut): kind is the id-ce arc (2.5.29.kind) whose
 * fields are set, or 0. */
typedef struct {
    vx509_span oid;
    int critical;
    vx509_span value;
    int kind, ca, has_len;
    uint64_t path_len;
    vx509_span a, b, c;
    /* ExtKeyUsage, SubjectAltName, certificatePolicies: the list's entries
     * are item_n of vx509_crt's items from item0, or VX509_NO_ITEMS. */
    uint32_t item0, item_n;
} vx509_ext_out;
#define VX509_EXT_CAP 10
#define VX509_ITEM_CAP 24
#define VX509_NO_ITEMS UINT32_MAX
/* One entry of a list: an OID (tag 0x06) or a GeneralName. */
typedef struct { int tag; vx509_span item; } vx509_item;
typedef struct {
    vx509_span raw, tbs;
    int version;
    vx509_span serial, sig_oid;
    int sig_params_tag;
    vx509_span sig_params, issuer_raw, issuer, subject_raw, subject;
    vx509_time valid_from, valid_to;
    vx509_span pk_raw, pk_oid;
    int pk_params_tag;
    vx509_span pk_params, pk_key;
    int issuer_id_tag;
    vx509_span issuer_id;
    int subject_id_tag;
    vx509_span subject_id, v3_ext, extensions, sig;
    /* The attributes of each Name as vx509's verified check read them; n
     * more than VX509_NAME_CAP: only the first VX509_NAME_CAP are here. */
    uint32_t issuer_n;
    vx509_atv issuer_atvs[VX509_NAME_CAP];
    uint32_t subject_n;
    vx509_atv subject_atvs[VX509_NAME_CAP];
    /* More than VX509_EXT_CAP: only the first VX509_EXT_CAP are in exts. */
    uint32_t ext_n;
    vx509_ext_out exts[VX509_EXT_CAP];
    vx509_item items[VX509_ITEM_CAP];
} vx509_crt;
typedef struct {
    int code, stage;
    vx509_span sig_oid;
    int sig_params_tag;
    vx509_span sig_params, spki;
} vx509_err;
typedef struct { vx509_span oid; int critical; vx509_span value; } vx509_ext;

int vx509_parse_crt(const unsigned char *buf, size_t len, vx509_crt *out, vx509_err *err);
int vx509_name_next(vx509_span *rdns, vx509_span *set, vx509_atv *out);
int vx509_ext_next(vx509_span *rest, vx509_ext *out);
size_t vx509_name_atvs(vx509_span rdns, vx509_atv *out, size_t cap);
size_t vx509_ext_all(vx509_span list, vx509_ext *out, size_t cap);
int vx509_basic_constraints(vx509_span v, int *ca, int *has_len, uint64_t *path_len);
int vx509_bit_string(vx509_span v, vx509_span *bits);
int vx509_ext_list(vx509_span v, int kind, vx509_span *list);
int vx509_list_next(vx509_span *rest, int kind, int *tag, vx509_span *out);
size_t vx509_list_all(vx509_span list, int kind, vx509_item *out, size_t cap);
int vx509_subject_key_id(vx509_span v, vx509_span *out);
int vx509_authority_key_id(vx509_span v, vx509_span *key_id, vx509_span *issuer,
                           vx509_span *serial);

/* Spans point into the caller's buffer; with make_copy, into our copy. */
typedef struct { const unsigned char *from; unsigned char *to; } vx509_rebase;

static unsigned char *vx509_ptr(const vx509_rebase *rb, vx509_span s)
{
    return s.p == NULL ? NULL : rb->to + (s.p - rb->from);
}

static void vx509_buf(const vx509_rebase *rb, mbedtls_x509_buf *dst, int tag, vx509_span s)
{
    dst->tag = tag;
    dst->len = s.len;
    dst->p = vx509_ptr(rb, s);
}

/* The same for a span that is never null: a slice of the certificate. */
static unsigned char *vx509_at(const vx509_rebase *rb, vx509_span s)
{
    return rb->to + (s.p - rb->from);
}

static void vx509_slice(const vx509_rebase *rb, mbedtls_x509_buf *dst, int tag, vx509_span s)
{
    dst->tag = tag;
    dst->len = s.len;
    dst->p = vx509_at(rb, s);
}

/* mbedTLS only accepts these attribute value types. */
static int vx509_name_tag_ok(int t)
{
    return t == MBEDTLS_ASN1_BMP_STRING || t == MBEDTLS_ASN1_UTF8_STRING ||
           t == MBEDTLS_ASN1_T61_STRING || t == MBEDTLS_ASN1_PRINTABLE_STRING ||
           t == MBEDTLS_ASN1_IA5_STRING || t == MBEDTLS_ASN1_UNIVERSAL_STRING ||
           t == MBEDTLS_ASN1_BIT_STRING;
}

static int vx509_name_atv(const vx509_rebase *rb, mbedtls_x509_name *cur, const vx509_atv *a)
{
    if (!vx509_name_tag_ok(a->val_tag)) {
        return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_NAME, MBEDTLS_ERR_ASN1_UNEXPECTED_TAG);
    }
    vx509_slice(rb, &cur->oid, MBEDTLS_ASN1_OID, a->oid);
    vx509_slice(rb, &cur->val, a->val_tag, a->val);
    cur->next_merged = a->merged;
    return 0;
}

#define VX509_BATCH 32

static int vx509_name(const vx509_rebase *rb, vx509_span rdns, uint32_t pre_n,
                      const vx509_atv *pre, mbedtls_x509_name *cur)
{
    vx509_atv batch[VX509_BATCH];
    const vx509_atv *atvs = batch;
    size_t i, n;
    int ret;

    if (rdns.len == 0) {
        return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_NAME, MBEDTLS_ERR_ASN1_OUT_OF_DATA);
    }
    if (pre_n <= VX509_NAME_CAP) {
        atvs = pre;
        n = pre_n;
    } else {
        n = vx509_name_atvs(rdns, batch, VX509_BATCH);
    }
    if (n <= VX509_BATCH) {
        for (i = 0; i < n; i++) {
            if ((ret = vx509_name_atv(rb, cur, &atvs[i])) != 0) {
                return ret;
            }
            if (i + 1 < n) {
                cur->next = mbedtls_calloc(1, sizeof(mbedtls_x509_name));
                if (cur->next == NULL) {
                    return MBEDTLS_ERR_X509_ALLOC_FAILED;
                }
                cur = cur->next;
            }
        }
        return 0;
    }
    /* More attributes than fit in one batch. */
    {
        vx509_span set = { NULL, 0 };
        vx509_atv a;
        while (vx509_name_next(&rdns, &set, &a)) {
            if ((ret = vx509_name_atv(rb, cur, &a)) != 0) {
                return ret;
            }
            if (rdns.len == 0 && set.len == 0) {
                break;
            }
            cur->next = mbedtls_calloc(1, sizeof(mbedtls_x509_name));
            if (cur->next == NULL) {
                return MBEDTLS_ERR_X509_ALLOC_FAILED;
            }
            cur = cur->next;
        }
    }
    return 0;
}

/* Appends one entry of a verified list to an mbedtls_x509_sequence. */
static int vx509_seq_item(const vx509_rebase *rb, int tag, vx509_span item,
                          mbedtls_x509_sequence **curp, int check_san)
{
    mbedtls_x509_sequence *cur = *curp;
    int ret;

    if (cur->buf.p != NULL) {
        cur->next = mbedtls_calloc(1, sizeof(mbedtls_asn1_sequence));
        if (cur->next == NULL) {
            return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                     MBEDTLS_ERR_ASN1_ALLOC_FAILED);
        }
        cur = cur->next;
        *curp = cur;
    }
    vx509_slice(rb, &cur->buf, tag, item);
    /* mbedTLS's own per-entry checks, on an entry vx509 has proven
     * well formed. Only otherName (supported forms) and directoryName
     * (mbedTLS's string types) can fail them: vx509 has already
     * required the iPAddress lengths mbedTLS checks. */
    if (check_san && (tag == (MBEDTLS_ASN1_CONTEXT_SPECIFIC | MBEDTLS_ASN1_CONSTRUCTED | 0) ||
                      tag == (MBEDTLS_ASN1_CONTEXT_SPECIFIC | MBEDTLS_ASN1_CONSTRUCTED | 4))) {
        mbedtls_x509_subject_alternative_name san;
        memset(&san, 0, sizeof(san));
        ret = mbedtls_x509_parse_subject_alt_name(&cur->buf, &san);
        mbedtls_x509_free_subject_alt_name(&san);
        if (ret != 0 && ret != MBEDTLS_ERR_X509_FEATURE_UNAVAILABLE) {
            return ret;
        }
    }
    return 0;
}

/* Appends entries of a verified list to an mbedtls_x509_sequence. With
 * `other`, also reports whether any entry is not the anyPolicy OID. */
static int vx509_seq_items(const vx509_rebase *rb, const vx509_item *items, size_t n,
                           mbedtls_x509_sequence **curp, int check_san, int *other)
{
    static const unsigned char any_policy[] = MBEDTLS_OID_ANY_POLICY;
    size_t i;
    int ret;

    for (i = 0; i < n; i++) {
        if ((ret = vx509_seq_item(rb, items[i].tag, items[i].item, curp, check_san)) != 0) {
            return ret;
        }
        if (other != NULL && (items[i].item.len != sizeof(any_policy) - 1 ||
                              memcmp(items[i].item.p, any_policy, sizeof(any_policy) - 1) != 0)) {
            *other = 1;
        }
    }
    return 0;
}

#define VX509_ITEMS 16

/* The same for a whole list, framing its entries here: one call for a list
 * that fits, entry by entry otherwise. */
static int vx509_seq(const vx509_rebase *rb, vx509_span list, int kind,
                     mbedtls_x509_sequence *cur, int check_san, int *other)
{
    vx509_item items[VX509_ITEMS];
    size_t n;
    int ret;

    n = vx509_list_all(list, kind, items, VX509_ITEMS);
    if (n <= VX509_ITEMS) {
        return vx509_seq_items(rb, items, n, &cur, check_san, other);
    }
    while (vx509_list_next(&list, kind, &items[0].tag, &items[0].item)) {
        if ((ret = vx509_seq_items(rb, items, 1, &cur, check_san, other)) != 0) {
            return ret;
        }
    }
    return 0;
}

/* The list of a list-valued extension: its entries as vx509_parse_crt left
 * them in `items` when they are there, framed here otherwise. */
static int vx509_ext_seq(const vx509_rebase *rb, const vx509_ext_out *d, int decoded,
                         const vx509_item *items, int arc, int kind,
                         mbedtls_x509_sequence *cur, int check_san, int *other)
{
    vx509_span l;

    if (decoded && d->kind == arc) {
        if (d->item_n != VX509_NO_ITEMS) {
            return vx509_seq_items(rb, items + d->item0, d->item_n, &cur, check_san, other);
        }
        l = d->a;
    } else if (vx509_ext_list(d->value, kind, &l) != 0) {
        return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
    }
    return vx509_seq(rb, l, kind, cur, check_san, other);
}

/* mbedtls_oid_get_x509_ext_type() without the table search: the extensions
 * mbedTLS supports are id-ce arcs plus Netscape's nsCertType. */
static int vx509_ext_type(vx509_span oid)
{
    static const unsigned char ns_cert_type[] = MBEDTLS_OID_NS_CERT_TYPE;
    if (oid.len == 3 && oid.p[0] == 0x55 && oid.p[1] == 0x1D) {
        switch (oid.p[2]) {
            case 14: return MBEDTLS_X509_EXT_SUBJECT_KEY_IDENTIFIER;
            case 15: return MBEDTLS_X509_EXT_KEY_USAGE;
            case 17: return MBEDTLS_X509_EXT_SUBJECT_ALT_NAME;
            case 19: return MBEDTLS_X509_EXT_BASIC_CONSTRAINTS;
            case 32: return MBEDTLS_X509_EXT_CERTIFICATE_POLICIES;
            case 35: return MBEDTLS_X509_EXT_AUTHORITY_KEY_IDENTIFIER;
            case 37: return MBEDTLS_X509_EXT_EXTENDED_KEY_USAGE;
        }
        return 0;
    }
    if (oid.len == sizeof(ns_cert_type) - 1 && memcmp(oid.p, ns_cert_type, oid.len) == 0) {
        return MBEDTLS_X509_EXT_NS_CERT_TYPE;
    }
    return 0;
}

/* One extension. `decoded`: vx509's verified check filled in what the
 * value decodes to (d->kind and the fields after it). */
static int vx509_one_ext(const vx509_rebase *rb, mbedtls_x509_crt *crt, const vx509_ext_out *d,
                         int decoded, const vx509_item *items,
                         mbedtls_x509_crt_ext_cb_t cb, void *p_ctx)
{
    int ret, ext_type;

    if ((ext_type = vx509_ext_type(d->oid)) == 0) {
        mbedtls_x509_buf oid;
        unsigned char *v;
        if (cb != NULL) {
            vx509_buf(rb, &oid, MBEDTLS_ASN1_OID, d->oid);
            v = vx509_ptr(rb, d->value);
            ret = cb(p_ctx, crt, &oid, d->critical, v, v + d->value.len);
            if (ret != 0 && d->critical) {
                return ret;
            }
            return 0;
        }
        if (d->critical) {
            return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                     MBEDTLS_ERR_ASN1_UNEXPECTED_TAG);
        }
        return 0;
    }
    /* vx509 has proven the OIDs distinct. */
    crt->ext_types |= ext_type;

    switch (ext_type) {
        case MBEDTLS_X509_EXT_BASIC_CONSTRAINTS: {
            int ca, has_len;
            uint64_t path_len;
            if (decoded && d->kind == 19) {
                ca = d->ca;
                has_len = d->has_len;
                path_len = d->path_len;
            } else if (vx509_basic_constraints(d->value, &ca, &has_len, &path_len) != 0) {
                return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
            }
            crt->ca_istrue = ca;
            crt->max_pathlen = 0;
            if (has_len) {
                /* mbedTLS stores pathLenConstraint + 1 in an int. */
                if (path_len >= INT_MAX) {
                    return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                             MBEDTLS_ERR_ASN1_INVALID_LENGTH);
                }
                crt->max_pathlen = (int) path_len + 1;
            }
            break;
        }
        case MBEDTLS_X509_EXT_KEY_USAGE: {
            vx509_span bits;
            size_t i;
            if (decoded && d->kind == 15) {
                bits = d->a;
            } else if (vx509_bit_string(d->value, &bits) != 0) {
                return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
            }
            crt->key_usage = 0;
            for (i = 0; i < bits.len && i < sizeof(unsigned int); i++) {
                crt->key_usage |= (unsigned int) bits.p[i] << (8 * i);
            }
            break;
        }
        case MBEDTLS_X509_EXT_NS_CERT_TYPE: {
            vx509_span bits;
            if (vx509_bit_string(d->value, &bits) != 0) {
                return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
            }
            if (bits.len > 1) {
                return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                         MBEDTLS_ERR_ASN1_INVALID_LENGTH);
            }
            crt->ns_cert_type = bits.len == 1 ? bits.p[0] : 0;
            break;
        }
        case MBEDTLS_X509_EXT_EXTENDED_KEY_USAGE:
            if ((ret = vx509_ext_seq(rb, d, decoded, items, 37, 0,
                                     &crt->ext_key_usage, 0, NULL)) != 0) {
                return ret;
            }
            break;
        case MBEDTLS_X509_EXT_SUBJECT_ALT_NAME:
            if ((ret = vx509_ext_seq(rb, d, decoded, items, 17, 1,
                                     &crt->subject_alt_names, 1, NULL)) != 0) {
                return ret;
            }
            break;
        case MBEDTLS_X509_EXT_SUBJECT_KEY_IDENTIFIER: {
            vx509_span k;
            if (decoded && d->kind == 14) {
                k = d->a;
            } else if (vx509_subject_key_id(d->value, &k) != 0) {
                return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
            }
            vx509_slice(rb, &crt->subject_key_id, MBEDTLS_ASN1_OCTET_STRING, k);
            break;
        }
        case MBEDTLS_X509_EXT_AUTHORITY_KEY_IDENTIFIER: {
            vx509_span k, iss, sn;
            if (decoded && d->kind == 35) {
                k = d->a;
                iss = d->b;
                sn = d->c;
            } else if (vx509_authority_key_id(d->value, &k, &iss, &sn) != 0) {
                return MBEDTLS_ERR_X509_INVALID_EXTENSIONS;
            }
            /* mbedTLS requires the issuer and serial together. */
            if (iss.p != NULL && sn.p == NULL) {
                return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                         MBEDTLS_ERR_ASN1_OUT_OF_DATA);
            }
            if (iss.p == NULL && sn.p != NULL) {
                return MBEDTLS_ERROR_ADD(MBEDTLS_ERR_X509_INVALID_EXTENSIONS,
                                         MBEDTLS_ERR_ASN1_UNEXPECTED_TAG);
            }
            if (k.p != NULL) {
                vx509_buf(rb, &crt->authority_key_id.keyIdentifier,
                          MBEDTLS_ASN1_OCTET_STRING, k);
            }
            if (iss.p != NULL) {
                if ((ret = vx509_seq(rb, iss, 1,
                                     &crt->authority_key_id.authorityCertIssuer, 1, NULL)) != 0) {
                    return ret;
                }
                vx509_buf(rb, &crt->authority_key_id.authorityCertSerialNumber,
                          MBEDTLS_ASN1_INTEGER, sn);
            }
            break;
        }
        case MBEDTLS_X509_EXT_CERTIFICATE_POLICIES: {
            int other = 0;
            /* mbedTLS only enforces anyPolicy. */
            if ((ret = vx509_ext_seq(rb, d, decoded, items, 32, 2,
                                     &crt->certificate_policies, 0, &other)) != 0) {
                return ret;
            }
            if (other) {
                if (cb != NULL) {
                    mbedtls_x509_buf oid;
                    unsigned char *v = vx509_ptr(rb, d->value);
                    vx509_buf(rb, &oid, MBEDTLS_ASN1_OID, d->oid);
                    if (cb(p_ctx, crt, &oid, d->critical, v, v + d->value.len) == 0) {
                        break;
                    }
                }
                if (d->critical) {
                    return MBEDTLS_ERR_X509_FEATURE_UNAVAILABLE;
                }
            }
            break;
        }
        default:
            if (d->critical) {
                return MBEDTLS_ERR_X509_FEATURE_UNAVAILABLE;
            }
    }
    return 0;
}

/* The extensions, as vx509's verified check read and decoded them when
 * there are at most VX509_EXT_CAP, or walked here otherwise. */
static int vx509_exts(const vx509_rebase *rb, mbedtls_x509_crt *crt, vx509_span list,
                      const vx509_crt *v, mbedtls_x509_crt_ext_cb_t cb, void *p_ctx)
{
    vx509_ext e;
    vx509_ext_out d;
    uint32_t i;
    int ret;

    if (v->ext_n <= VX509_EXT_CAP) {
        for (i = 0; i < v->ext_n; i++) {
            if ((ret = vx509_one_ext(rb, crt, &v->exts[i], 1, v->items, cb, p_ctx)) != 0) {
                return ret;
            }
        }
        return 0;
    }
    while (vx509_ext_next(&list, &e)) {
        d.oid = e.oid;
        d.critical = e.critical;
        d.value = e.value;
        if ((ret = vx509_one_ext(rb, crt, &d, 0, NULL, cb, p_ctx)) != 0) {
            return ret;
        }
    }
    return 0;
}

/* mbedtls_pk_parse_subpubkey() on the SubjectPublicKeyInfo vx509 has
 * checked, so the key, and the error for one mbedTLS does not support, are
 * mbedTLS's. */
static int vx509_pk(const vx509_rebase *rb, const vx509_crt *v, mbedtls_pk_context *pk)
{
    unsigned char *p = vx509_at(rb, v->pk_raw);
    return mbedtls_pk_parse_subpubkey(&p, p + v->pk_raw.len, pk);
}

static int vx509_crt_parse_der_core(mbedtls_x509_crt *crt,
                                    const unsigned char *buf,
                                    size_t buflen,
                                    int make_copy,
                                    mbedtls_x509_crt_ext_cb_t cb,
                                    void *p_ctx)
{
    int ret;
    vx509_crt v;
    vx509_err err;
    vx509_rebase rb;
    mbedtls_x509_buf sig_params;
    unsigned char *p;

    /* mbedTLS's own parser, which this replaces, stays compiled. */
    (void) x509_crt_parse_der_core;

    if (crt == NULL || buf == NULL) {
        return MBEDTLS_ERR_X509_BAD_INPUT_DATA;
    }

    if ((ret = vx509_parse_crt(buf, buflen, &v, &err)) != 0) {
        /* Rejected. Run the steps mbedTLS would have run before reaching
         * the fault, so the error is the one mbedTLS would report. */
        if (err.stage >= 1) {
            mbedtls_x509_buf oid;
            rb.from = buf;
            rb.to = (unsigned char *) buf;
            vx509_buf(&rb, &oid, MBEDTLS_ASN1_OID, err.sig_oid);
            vx509_buf(&rb, &sig_params, err.sig_params_tag, err.sig_params);
            if ((ret = mbedtls_x509_get_sig_alg(&oid, &sig_params, &crt->sig_md,
                                                &crt->sig_pk)) != 0) {
                mbedtls_x509_crt_free(crt);
                return ret;
            }
        }
        if (err.stage >= 2) {
            p = (unsigned char *) err.spki.p;
            if ((ret = mbedtls_pk_parse_subpubkey(&p, p + err.spki.len, &crt->pk)) != 0) {
                mbedtls_x509_crt_free(crt);
                return ret;
            }
        }
        mbedtls_x509_crt_free(crt);
        return err.code;
    }

    rb.from = v.raw.p;
    if (make_copy != 0) {
        rb.to = mbedtls_calloc(1, v.raw.len);
        if (rb.to == NULL) {
            return MBEDTLS_ERR_X509_ALLOC_FAILED;
        }
        memcpy(rb.to, v.raw.p, v.raw.len);
        crt->own_buffer = 1;
    } else {
        rb.to = (unsigned char *) v.raw.p;
        crt->own_buffer = 0;
    }

    crt->raw.len = v.raw.len;
    crt->raw.p = rb.to;
    crt->tbs.len = v.tbs.len;
    crt->tbs.p = vx509_at(&rb, v.tbs);
    crt->version = v.version;
    vx509_slice(&rb, &crt->serial, MBEDTLS_ASN1_INTEGER, v.serial);
    vx509_slice(&rb, &crt->sig_oid, MBEDTLS_ASN1_OID, v.sig_oid);
    vx509_buf(&rb, &sig_params, v.sig_params_tag, v.sig_params);

    if ((ret = mbedtls_x509_get_sig_alg(&crt->sig_oid, &sig_params,
                                        &crt->sig_md, &crt->sig_pk)) != 0) {
        goto fail;
    }

    crt->issuer_raw.len = v.issuer_raw.len;
    crt->issuer_raw.p = vx509_at(&rb, v.issuer_raw);
    if ((ret = vx509_name(&rb, v.issuer, v.issuer_n, v.issuer_atvs, &crt->issuer)) != 0) {
        goto fail;
    }

    crt->valid_from.year = v.valid_from.year;
    crt->valid_from.mon = v.valid_from.mon;
    crt->valid_from.day = v.valid_from.day;
    crt->valid_from.hour = v.valid_from.hour;
    crt->valid_from.min = v.valid_from.min;
    crt->valid_from.sec = v.valid_from.sec;
    crt->valid_to.year = v.valid_to.year;
    crt->valid_to.mon = v.valid_to.mon;
    crt->valid_to.day = v.valid_to.day;
    crt->valid_to.hour = v.valid_to.hour;
    crt->valid_to.min = v.valid_to.min;
    crt->valid_to.sec = v.valid_to.sec;

    crt->subject_raw.len = v.subject_raw.len;
    crt->subject_raw.p = vx509_at(&rb, v.subject_raw);
    if (v.subject.len != 0 && (ret = vx509_name(&rb, v.subject, v.subject_n, v.subject_atvs, &crt->subject)) != 0) {
        goto fail;
    }

    crt->pk_raw.len = v.pk_raw.len;
    crt->pk_raw.p = vx509_at(&rb, v.pk_raw);
    if ((ret = vx509_pk(&rb, &v, &crt->pk)) != 0) {
        goto fail;
    }

    if (v.issuer_id_tag != 0) {
        vx509_buf(&rb, &crt->issuer_id, v.issuer_id_tag, v.issuer_id);
    }
    if (v.subject_id_tag != 0) {
        vx509_buf(&rb, &crt->subject_id, v.subject_id_tag, v.subject_id);
    }
    if (v.v3_ext.p != NULL) {
        vx509_buf(&rb, &crt->v3_ext,
                  MBEDTLS_ASN1_CONTEXT_SPECIFIC | MBEDTLS_ASN1_CONSTRUCTED | 3, v.v3_ext);
        if ((ret = vx509_exts(&rb, crt, v.extensions, &v, cb, p_ctx)) != 0) {
            goto fail;
        }
    }

    vx509_slice(&rb, &crt->sig, MBEDTLS_ASN1_BIT_STRING, v.sig);
    return 0;

fail:
    mbedtls_x509_crt_free(crt);
    return ret;
}
