/* vhttp's native C API: the verified HTTP/1.1 parser behind the interface
 * the Rust API has. For the drop-ins, see picohttpparser.h and compat/.
 *
 * Build with `cargo build --profile release-abort --features capi` and link
 * target/release-abort/libverilith_http.a (plus -lpthread -ldl -lm).
 *
 *     vhttp_header h[64];
 *     size_t n = 64;
 *     vhttp_request r;
 *     switch (vhttp_parse_request(buf, len, 0, h, &n, &r)) {
 *     case VHTTP_OK:      ... r.head_len, r.body, h[0..n] ...
 *     case VHTTP_PARTIAL: ... read more into buf and call again ...
 *     default:            ... reject: respond 400 and close ...
 *     }
 *
 * Compared with the picohttpparser shape, this API also returns how the
 * body is framed (the decision that vhttp's request smuggling proofs are
 * about) and says why a message was rejected.
 *
 * Nothing is allocated per call and nothing is copied: methods, targets and
 * field lines are spans, byte offsets start..end into the buffer that was
 * parsed, so they stay meaningful if the buffer is moved or grown.
 * VHTTP_STR(buf, span) gives a pointer and vhttp_len(span) a length.
 *
 * Threads. There is no shared state: every function may be called from any
 * thread. A vhttp_chunked decoder belongs to one body.
 *
 * What is accepted. Exactly RFC 9112 as vhttp's specification states it
 * (see the README): lines end in CRLF, no whitespace before a colon, no
 * obsolete line folding, and a head whose framing is ambiguous is an
 * error. */
#ifndef VHTTP_H
#define VHTTP_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Bytes start..end of the buffer. */
typedef struct vhttp_span {
    size_t start;
    size_t end;
} vhttp_span;

#define VHTTP_STR(buf, span) ((buf) + (span).start)
#define vhttp_len(span) ((span).end - (span).start)

typedef struct vhttp_header {
    vhttp_span name;
    vhttp_span value; /* without leading and trailing whitespace */
} vhttp_header;

/* How the body that follows a head is delimited. */
enum {
    VHTTP_BODY_EMPTY = 0,   /* no body */
    VHTTP_BODY_LENGTH = 1,  /* exactly content_length bytes */
    VHTTP_BODY_CHUNKED = 2, /* the chunked coding: see vhttp_chunked_decode */
    VHTTP_BODY_CLOSE = 3    /* everything until the connection closes (responses only) */
};

typedef struct vhttp_request {
    vhttp_span method;
    vhttp_span target;
    size_t head_len; /* length of the head; the body starts here */
    uint64_t content_length;
    int body;              /* VHTTP_BODY_* */
    uint8_t minor_version; /* x in HTTP/1.x */
} vhttp_request;

typedef struct vhttp_response {
    vhttp_span reason;
    size_t head_len;
    uint64_t content_length;
    int body;
    uint16_t status;
    uint8_t minor_version;
} vhttp_response;

/* Results. Errors are negative. */
enum {
    VHTTP_OK = 0,
    VHTTP_PARTIAL = 1, /* the buffer ends before the head (or body) does */
    VHTTP_E_METHOD = -1,
    VHTTP_E_TARGET = -2,
    VHTTP_E_VERSION = -3,
    VHTTP_E_STATUS = -4,
    VHTTP_E_NEWLINE = -5,      /* a bare LF or CR instead of CRLF */
    VHTTP_E_HEADER_NAME = -6,  /* includes whitespace before the colon and line folding */
    VHTTP_E_HEADER_VALUE = -7,
    VHTTP_E_TOO_MANY_HEADERS = -8,
    /* Framing errors (vhttp_error_is_framing): the head is well formed but
     * recipients could disagree about where the message ends. */
    VHTTP_E_CONTENT_LENGTH = -9,
    VHTTP_E_TRANSFER_ENCODING = -10,
    VHTTP_E_CONTENT_LENGTH_AND_TRANSFER_ENCODING = -11,
    VHTTP_E_TRANSFER_ENCODING_HTTP10 = -12,
    VHTTP_E_HOST = -13, /* no Host in an HTTP/1.1 request, or more than one */
    VHTTP_E_CHUNKED = -14,
    VHTTP_E_ARGUMENT = -100 /* a null pointer, or an invalid decoder */
};

/* Parses a request head at the start of buf.
 *
 * *num_headers is the capacity of headers on entry and the number of field
 * lines on return; a head with more is VHTTP_E_TOO_MANY_HEADERS. last_len is
 * the buffer length at the previous VHTTP_PARTIAL call on the same growing
 * buffer, or 0: with it, a head that arrives in many small reads costs
 * linear time in total. out may be NULL. Nothing but *num_headers is
 * written unless the result is VHTTP_OK. */
int vhttp_parse_request(const char *buf, size_t len, size_t last_len, vhttp_header *headers, size_t *num_headers,
                        vhttp_request *out);

/* Parses a response head. head_request and connect_request say whether the
 * request it answers was HEAD or CONNECT, which changes the framing
 * (RFC 9112, 6.3). At most 100 field lines are accepted. */
int vhttp_parse_response(const char *buf, size_t len, bool head_request, bool connect_request,
                         vhttp_header *headers, size_t *num_headers, vhttp_response *out);

/* A static, NUL-terminated description of a result code. */
const char *vhttp_error_message(int code);
bool vhttp_error_is_framing(int code);

/* A decoder for one chunked body. Zero it before the first call
 * (`vhttp_chunked d = {0};`). Set keep_trailers before the first call to
 * have the decoder stop at the trailer section and leave it, with the final
 * CRLF, for the caller; otherwise the decoder consumes it. The other fields
 * are private. */
typedef struct vhttp_chunked {
    size_t n_;
    uint8_t state_;
    bool keep_trailers;
} vhttp_chunked;

/* Decodes len bytes of chunked body in place; call it with each piece of
 * the body as it arrives. The result does not depend on how the body is
 * split into pieces.
 *
 * VHTTP_PARTIAL: all input was consumed; *out_len body bytes are at the
 * front of buf. VHTTP_OK: the body ended; *out_len body bytes are at the
 * front of buf, followed by the *rest bytes that came after the body.
 * VHTTP_E_CHUNKED: the body is malformed. */
int vhttp_chunked_decode(vhttp_chunked *d, char *buf, size_t len, size_t *out_len, size_t *rest);

/* Whether the decoder is inside chunk data. */
bool vhttp_chunked_in_data(const vhttp_chunked *d);

#ifdef __cplusplus
}
#endif

#endif
