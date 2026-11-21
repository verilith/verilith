/* vdns's native C API: the verified DNS message parser behind the interface
 * the Rust API has. For the c-ares drop-in, see cares/.
 *
 * Build with `cargo build --release --features capi` and link
 * target/release/libverilith_dns.a (plus -lpthread -ldl).
 *
 *     vdns_message *m = vdns_message_new();
 *     if (vdns_parse(m, packet, len, NULL) == VDNS_OK) {
 *         vdns_record r;
 *         for (size_t i = 0; vdns_get_record(m, VDNS_ANSWER, i, &r); i++)
 *             if (r.rtype == 1 && r.rdata_len == 4) { ... r.rdata is an IPv4 address ... }
 *     }
 *     vdns_message_free(m);
 *
 * A message keeps its buffers between packets, so a long-lived message
 * parses without allocating, and reading a question or a record copies
 * nothing: names and RDATA are pointers into the message. They are valid
 * until the message is parsed into again or freed. The packet itself is
 * copied by vdns_parse and need not outlive the call.
 *
 * Names are in uncompressed wire form (length-prefixed labels, then a zero
 * octet): compression pointers are already resolved, so a name can be
 * compared with memcmp, or case-insensitively (see RFC 4343). RDATA is given
 * with the names inside it uncompressed as well (for NS, CNAME, SOA, PTR,
 * MX, SIG, SRV and NAPTR records), so every RDATA can be decoded on its own,
 * without the rest of the packet: for example an MX RDATA is two bytes of
 * preference and then a name for vdns_name_text.
 *
 * Threads. A message is parsed into by one thread at a time. Once
 * vdns_parse has returned, any number of threads may read it.
 *
 * What is accepted. Exactly the messages of vdns's specification (see the
 * README): RFC 1035 with the RFC 9267 rules, so no compression pointer loops
 * or forward pointers, no names over 255 octets, no bytes after the last
 * record. */
#ifndef VDNS_H
#define VDNS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct vdns_message vdns_message;

typedef struct vdns_question {
    const uint8_t *name; /* uncompressed wire form, root octet included */
    size_t name_len;
    uint16_t qtype;
    uint16_t qclass;
} vdns_question;

typedef struct vdns_record {
    const uint8_t *name;
    size_t name_len;
    const uint8_t *rdata; /* with the names inside it uncompressed */
    size_t rdata_len;
    uint32_t ttl;
    uint16_t rtype;
    uint16_t rclass;
} vdns_record;

enum { VDNS_ANSWER = 0, VDNS_AUTHORITY = 1, VDNS_ADDITIONAL = 2 };

enum {
    VDNS_OK = 0,
    VDNS_E_SHORT_HEADER = 1, /* shorter than the 12-byte header */
    VDNS_E_TRUNCATED = 2,    /* ends inside a name, a fixed field or RDATA */
    VDNS_E_RESERVED_LABEL_TYPE = 3,
    VDNS_E_POINTER_NOT_PRIOR = 4, /* includes every compression pointer loop */
    VDNS_E_POINTER_TO_POINTER = 5,
    VDNS_E_NAME_TOO_LONG = 6, /* over 255 octets once decompressed */
    VDNS_E_BAD_RDATA = 7,     /* RDATA with names in it that does not decode as its type */
    VDNS_E_TRAILING_BYTES = 8,
    VDNS_E_ARGUMENT = -1, /* a null pointer */
    VDNS_E_NAME = -2,     /* vdns_write_query: not a valid name */
    VDNS_E_SPACE = -3     /* vdns_write_query: the buffer is too small */
};

/* Which part of a rejected message is at fault. */
enum {
    VDNS_PART_HEADER = 0,
    VDNS_PART_QUESTION = 1,
    VDNS_PART_ANSWER = 2,
    VDNS_PART_AUTHORITY = 3,
    VDNS_PART_ADDITIONAL = 4,
    VDNS_PART_END = 5
};

typedef struct vdns_error {
    int code;
    int part;      /* VDNS_PART_* */
    size_t index;  /* the question or record at fault, within its section */
    size_t offset; /* offset of the byte that breaks the rule */
} vdns_error;

vdns_message *vdns_message_new(void);
void vdns_message_free(vdns_message *m);

/* Parses one complete DNS message into m, replacing what m held. Returns
 * VDNS_OK, or an error code, filling *err (which may be NULL); m is then
 * an empty message. */
int vdns_parse(vdns_message *m, const uint8_t *wire, size_t len, vdns_error *err);

uint16_t vdns_id(const vdns_message *m);
/* The 16 bits after the ID: QR, opcode, AA, TC, RD, RA, Z and RCODE. */
uint16_t vdns_flags(const vdns_message *m);

size_t vdns_question_count(const vdns_message *m);
/* section is VDNS_ANSWER, VDNS_AUTHORITY or VDNS_ADDITIONAL. */
size_t vdns_record_count(const vdns_message *m, int section);

/* The i-th question, or the i-th record of a section; false when there is
 * none. Constant time. */
bool vdns_get_question(const vdns_message *m, size_t i, vdns_question *out);
bool vdns_get_record(const vdns_message *m, int section, size_t i, vdns_record *out);

/* A wire-form name as text ("www.example.com", special characters escaped
 * as c-ares does, the root name as the empty string), NUL-terminated, as
 * much as fits in cap bytes. Returns the length of the whole text, like
 * snprintf; 1020 bytes always suffice. */
size_t vdns_name_text(const uint8_t *name, size_t name_len, char *buf, size_t cap);

/* Writes a query with one question. name is text ("example.com", with an
 * optional trailing dot and \. and \DDD escapes), name_len bytes long.
 * flags are the 16 bits after the ID (0x0100 asks for recursion). Sets
 * *len to the query's length and returns VDNS_OK; VDNS_E_NAME if the name
 * is not valid; or VDNS_E_SPACE if cap is too small, with the length needed
 * in *len. */
int vdns_write_query(uint16_t id, uint16_t flags, const char *name, size_t name_len, uint16_t qtype,
                     uint16_t qclass, uint8_t *out, size_t cap, size_t *len);

#ifdef __cplusplus
}
#endif

#endif
