/* vhttp's picohttpparser-compatible C API.
 *
 * Build with `cargo build --profile release-abort --features phr-abi` and link
 * target/release-abort/libverilith_http.a (plus -lpthread -ldl -lm). The declarations
 * match picohttpparser's, so existing callers compile unchanged. Without
 * the phr-abi feature the same functions are exported with a vhttp_ prefix
 * (vhttp_phr_parse_request, ...).
 *
 * Differences from picohttpparser are listed in the vhttp README: the
 * grammar is strict (CRLF line endings, no obsolete line folding, no
 * whitespace before a colon, single spaces in the start line), messages
 * with ambiguous framing are rejected with -1, and out-parameters are not
 * written on a -2 (partial) result. */
#ifndef picohttpparser_h
#define picohttpparser_h

#include <stddef.h>
#include <stdint.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

struct phr_header {
    const char *name;
    size_t name_len;
    const char *value;
    size_t value_len;
};

/* Returns the length of the head on success, -2 if the head is incomplete,
 * -1 if it is invalid. *num_headers is the capacity of headers on entry and
 * the number of headers on return. last_len is the buffer length at the
 * previous call on the same growing buffer, or 0. */
int phr_parse_request(const char *buf, size_t len, const char **method, size_t *method_len, const char **path,
                      size_t *path_len, int *minor_version, struct phr_header *headers, size_t *num_headers,
                      size_t last_len);

int phr_parse_response(const char *buf, size_t len, int *minor_version, int *status, const char **msg, size_t *msg_len,
                       struct phr_header *headers, size_t *num_headers, size_t last_len);

int phr_parse_headers(const char *buf, size_t len, struct phr_header *headers, size_t *num_headers, size_t last_len);

/* Zero-fill before the first call. Set consume_trailer to 1 to have the
 * decoder consume the trailer section too. */
struct phr_chunked_decoder {
    size_t bytes_left_in_chunk;
    char consume_trailer;
    char _hex_count;
    char _state;
    uint64_t _total_read;
    uint64_t _total_overhead;
};

/* Decodes chunked data in place. Returns -1 on error, -2 if the body is not
 * finished (*bufsz is then the number of decoded bytes at the front of buf),
 * or, once the body ends, the number of bytes after it, which follow the
 * *bufsz decoded bytes. */
ssize_t phr_decode_chunked(struct phr_chunked_decoder *decoder, char *buf, size_t *bufsz);

int phr_decode_chunked_is_in_data(struct phr_chunked_decoder *decoder);

#ifdef __cplusplus
}
#endif

#endif
