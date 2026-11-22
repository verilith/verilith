/* vx509's native C API: the verified X.509 parser behind the same zero-copy
 * interface the Rust API has. For the mbedTLS drop-in, see mbedtls/.
 *
 * Build with `cargo build --profile release-fat --features capi` and link
 * target/release-fat/libverilith_x509.a.
 *
 *     vx509_cert c;
 *     if (vx509_cert_parse(der, len, &c, NULL) == VX509_OK) {
 *         vx509_span names;
 *         vx509_general_name g;
 *         if (vx509_get_subject_alt_names(&c, &names))
 *             while (vx509_general_name_next(&names, &g))
 *                 if (g.kind == VX509_GN_DNS) fwrite(g.value.p, 1, g.value.len, stdout);
 *     }
 *
 * Nothing is allocated and nothing is copied: vx509_cert_parse fills a
 * struct of spans that point into the certificate, so they are valid for as
 * long as the certificate's bytes are alive and unchanged. There is nothing
 * to free, and no state: every function may be called from any thread.
 *
 * Lists (names, extensions, alternative names) are read with a cursor: copy
 * the list's span, then call its next function until it returns false. Each
 * call moves the cursor past the element it returned.
 *
 * Only pass spans that this API wrote, unchanged, to this API. They are
 * read without being checked again.
 *
 * What is checked. vx509_cert_parse accepts exactly the certificates of the
 * RFC 5280 profile in vx509's specification (see the README): strict DER,
 * and the contents of every extension it knows. It does not verify the
 * signature or build a chain. */
#ifndef VX509_H
#define VX509_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Bytes of the certificate. p is NULL when an optional field is absent. */
typedef struct vx509_span {
    const uint8_t *p;
    size_t len;
} vx509_span;

/* A DER element: its identifier octets (one byte for every tag below 31)
 * and its contents octets. */
typedef struct vx509_tlv {
    vx509_span tag;
    vx509_span content;
} vx509_tlv;

/* An AlgorithmIdentifier. oid is the OID's contents octets (see
 * vx509_oid_text). params.tag.p is NULL when there are no parameters. */
typedef struct vx509_alg {
    vx509_span oid;
    vx509_tlv params;
} vx509_alg;

/* UTC. */
typedef struct vx509_time {
    uint16_t year;
    uint8_t month, day, hour, minute, second;
} vx509_time;

typedef struct vx509_cert {
    vx509_span tbs;          /* the TBSCertificate's DER: what the signature covers */
    vx509_span serial;       /* the INTEGER's contents: two's complement, minimal */
    vx509_alg signature_alg; /* the same in the TBSCertificate and outside it */
    vx509_span issuer;       /* a Name, for vx509_rdn_next */
    vx509_span subject;
    vx509_time not_before;
    vx509_time not_after;
    vx509_span spki; /* the whole SubjectPublicKeyInfo element, for hashing and pinning */
    vx509_alg public_key_alg;
    vx509_span public_key;  /* the subjectPublicKey BIT STRING's octets */
    vx509_span issuer_uid;  /* absent (p NULL) in most certificates */
    vx509_span subject_uid;
    vx509_span extensions; /* for vx509_ext_next; empty when there are none */
    vx509_span signature;
    uint8_t version; /* 1, 2 or 3 */
    uint8_t issuer_uid_unused_bits;
    uint8_t subject_uid_unused_bits;
} vx509_cert;

enum {
    VX509_OK = 0,
    VX509_E_OUTER = 1, /* not one DER SEQUENCE spanning the whole input */
    VX509_E_TBS_CERTIFICATE = 2,
    VX509_E_VERSION = 3,
    VX509_E_SERIAL = 4,
    VX509_E_SIGNATURE_ALGORITHM = 5,
    VX509_E_ISSUER = 6,
    VX509_E_VALIDITY = 7,
    VX509_E_SUBJECT = 8,
    VX509_E_SUBJECT_PUBLIC_KEY_INFO = 9,
    VX509_E_UNIQUE_ID = 10,
    VX509_E_EXTENSIONS = 11,
    VX509_E_EXTENSION_CONTENTS = 12, /* a known extension with malformed contents */
    VX509_E_DUPLICATE_EXTENSION = 13,
    VX509_E_ALGORITHM_MISMATCH = 14, /* signatureAlgorithm differs inside and outside the TBSCertificate */
    VX509_E_SIGNATURE_VALUE = 15,
    VX509_E_ARGUMENT = -1 /* null der with len != 0 */
};

/* Parses one DER certificate. Returns VX509_OK and fills *out, or returns
 * an error code and sets *err_offset to the offset of the element at fault.
 * out and err_offset may be NULL (to validate only). */
int vx509_cert_parse(const uint8_t *der, size_t len, vx509_cert *out, size_t *err_offset);

/* Seconds since 1970-01-01T00:00:00Z. */
int64_t vx509_time_unix(const vx509_time *t);

/* An OID's dotted-decimal text ("2.5.4.3"), NUL-terminated, as much as fits
 * in cap bytes. Returns the length of the whole text, like snprintf. */
size_t vx509_oid_text(const uint8_t *oid, size_t oid_len, char *buf, size_t cap);

/* Names. A Name is a list of RelativeDistinguishedNames, each a set of
 * attributes (nearly always one).
 *
 *     vx509_span name = c.subject, rdn;
 *     vx509_atv a;
 *     while (vx509_rdn_next(&name, &rdn))
 *         while (vx509_atv_next(&rdn, &a)) { ... a.oid, a.value.content ... }
 */
typedef struct vx509_atv {
    vx509_span oid;
    vx509_tlv value; /* tag 0x0C is UTF8String, 0x13 PrintableString, ... */
} vx509_atv;

bool vx509_rdn_next(vx509_span *name, vx509_span *rdn);
bool vx509_atv_next(vx509_span *rdn, vx509_atv *out);

/* Extensions. */
typedef struct vx509_ext {
    vx509_span oid;
    vx509_span value; /* the contents of the extnValue OCTET STRING */
    bool critical;
} vx509_ext;

/* Steps through cert.extensions (copy the span first). */
bool vx509_ext_next(vx509_span *exts, vx509_ext *out);
/* The extension with this OID (contents octets), if present. */
bool vx509_ext_find(const vx509_cert *cert, const uint8_t *oid, size_t oid_len, vx509_ext *out);

/* The decoded extensions. Each returns false when the certificate does not
 * have the extension. Their contents were checked by vx509_cert_parse. */
typedef struct vx509_basic_constraints {
    uint64_t path_len; /* meaningful when has_path_len */
    bool ca;
    bool has_path_len;
} vx509_basic_constraints;

bool vx509_get_basic_constraints(const vx509_cert *cert, vx509_basic_constraints *out);

enum {
    VX509_KU_DIGITAL_SIGNATURE = 1 << 0,
    VX509_KU_NON_REPUDIATION = 1 << 1,
    VX509_KU_KEY_ENCIPHERMENT = 1 << 2,
    VX509_KU_DATA_ENCIPHERMENT = 1 << 3,
    VX509_KU_KEY_AGREEMENT = 1 << 4,
    VX509_KU_KEY_CERT_SIGN = 1 << 5,
    VX509_KU_CRL_SIGN = 1 << 6,
    VX509_KU_ENCIPHER_ONLY = 1 << 7,
    VX509_KU_DECIPHER_ONLY = 1 << 8
};

bool vx509_get_key_usage(const vx509_cert *cert, uint16_t *bits);

/* Lists of OIDs: step with vx509_oid_next and vx509_policy_next. */
bool vx509_get_ext_key_usage(const vx509_cert *cert, vx509_span *oids);
bool vx509_oid_next(vx509_span *oids, vx509_span *oid);
bool vx509_get_certificate_policies(const vx509_cert *cert, vx509_span *policies);
bool vx509_policy_next(vx509_span *policies, vx509_span *oid);

/* GeneralName kinds: the CHOICE's tag numbers (RFC 5280, 4.2.1.6). */
enum {
    VX509_GN_OTHER = 0,
    VX509_GN_RFC822 = 1, /* an email address */
    VX509_GN_DNS = 2,
    VX509_GN_X400 = 3,
    VX509_GN_DIRECTORY = 4, /* value is a Name, for vx509_rdn_next */
    VX509_GN_EDI_PARTY = 5,
    VX509_GN_URI = 6,
    VX509_GN_IP = 7, /* 4 or 16 bytes (8 or 32, with a mask, in name constraints) */
    VX509_GN_REGISTERED_ID = 8
};

typedef struct vx509_general_name {
    int kind;
    vx509_span value;
    /* For VX509_GN_OTHER only: the type-id OID, and the tag of the value
     * whose contents are in value. */
    vx509_span other_type_id;
    vx509_span other_value_tag;
} vx509_general_name;

bool vx509_get_subject_alt_names(const vx509_cert *cert, vx509_span *names);
bool vx509_get_issuer_alt_names(const vx509_cert *cert, vx509_span *names);
bool vx509_general_name_next(vx509_span *names, vx509_general_name *out);

bool vx509_get_subject_key_id(const vx509_cert *cert, vx509_span *id);

/* Each field is absent (p NULL) when the extension leaves it out. */
typedef struct vx509_authority_key_id {
    vx509_span key_id;
    vx509_span issuer; /* GeneralNames, for vx509_general_name_next */
    vx509_span serial;
} vx509_authority_key_id;

bool vx509_get_authority_key_id(const vx509_cert *cert, vx509_authority_key_id *out);

/* Lists of subtrees, absent (p NULL) when the extension leaves one out.
 * vx509_subtree_next yields each subtree's base name. */
typedef struct vx509_name_constraints {
    vx509_span permitted;
    vx509_span excluded;
} vx509_name_constraints;

bool vx509_get_name_constraints(const vx509_cert *cert, vx509_name_constraints *out);
bool vx509_subtree_next(vx509_span *subtrees, vx509_general_name *out);

#ifdef __cplusplus
}
#endif

#endif
