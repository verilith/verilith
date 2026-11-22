/*
 * vbind.h: the C ABI of libvbind, one static library holding the
 * Verilith parsers.
 *
 * vurl_*        vurl's C API. It is ada's ada_c.h with the ada_ prefix
 *               replaced by vurl_ (see vurl's README); only the calls the
 *               C++ headers use are declared here.
 * vbind_json_*  vjson documents: the verified parser's token tape and
 *               accessors for strings, numbers and raw text.
 *
 * Link with -lverilith_bind -lpthread -ldl -lm.
 */
#ifndef VBIND_H
#define VBIND_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- vurl ------------------------------------------------------------ */

typedef struct {
  const char* data;
  size_t length;
} vurl_string;

typedef struct {
  const char* data;
  size_t length;
} vurl_owned_string;

/* The same layout as ada::url_components. */
typedef struct {
  uint32_t protocol_end;
  uint32_t username_end;
  uint32_t host_start;
  uint32_t host_end;
  uint32_t port;
  uint32_t pathname_start;
  uint32_t search_start;
  uint32_t hash_start;
} vurl_url_components;

typedef void* vurl_url;

/* Always returns a handle; check vurl_is_valid, and free it either way. */
vurl_url vurl_parse(const char* input, size_t length);
vurl_url vurl_parse_with_base(const char* input, size_t input_length,
                              const char* base, size_t base_length);
bool vurl_can_parse(const char* input, size_t length);
bool vurl_can_parse_with_base(const char* input, size_t input_length,
                              const char* base, size_t base_length);
void vurl_free(vurl_url url);
vurl_url vurl_copy(vurl_url url);
/* set_hostname on a copy of url, which is left as it is: the setter's result
 * goes to *ok, and the edited URL is returned as a new handle, or NULL when
 * it is the same as url's. */
vurl_url vurl_with_hostname(vurl_url url, const char* input, size_t length,
                            bool* ok);
/* The host set_hostname would give url, without making the new URL: 1 when
 * the setter succeeds, with the host in *host (valid until the next call of
 * this function on this thread) and its type, as vurl_get_host_type, in
 * *host_type; 0 when it fails; -1 when this does not apply, and
 * vurl_with_hostname is needed. */
int vurl_hostname_after_set(vurl_url url, const char* input, size_t length,
                            vurl_string* host, uint8_t* host_type);
bool vurl_is_valid(vurl_url url);
void vurl_free_owned_string(vurl_owned_string s);

/* Views into the URL's href, valid until the URL changes or is freed. */
vurl_string vurl_get_href(vurl_url url);
vurl_string vurl_get_username(vurl_url url);
vurl_string vurl_get_password(vurl_url url);
vurl_string vurl_get_port(vurl_url url);
vurl_string vurl_get_hash(vurl_url url);
vurl_string vurl_get_host(vurl_url url);
vurl_string vurl_get_hostname(vurl_url url);
vurl_string vurl_get_pathname(vurl_url url);
vurl_string vurl_get_search(vurl_url url);
vurl_string vurl_get_protocol(vurl_url url);
vurl_owned_string vurl_get_origin(vurl_url url);
uint8_t vurl_get_host_type(vurl_url url);
uint8_t vurl_get_scheme_type(vurl_url url);
const vurl_url_components* vurl_get_components(vurl_url url);

bool vurl_set_href(vurl_url url, const char* input, size_t length);
bool vurl_set_host(vurl_url url, const char* input, size_t length);
bool vurl_set_hostname(vurl_url url, const char* input, size_t length);
bool vurl_set_protocol(vurl_url url, const char* input, size_t length);
bool vurl_set_username(vurl_url url, const char* input, size_t length);
bool vurl_set_password(vurl_url url, const char* input, size_t length);
bool vurl_set_port(vurl_url url, const char* input, size_t length);
bool vurl_set_pathname(vurl_url url, const char* input, size_t length);
void vurl_set_search(vurl_url url, const char* input, size_t length);
void vurl_set_hash(vurl_url url, const char* input, size_t length);
void vurl_clear_port(vurl_url url);
void vurl_clear_hash(vurl_url url);
void vurl_clear_search(vurl_url url);

bool vurl_has_credentials(vurl_url url);
bool vurl_has_empty_hostname(vurl_url url);
bool vurl_has_hostname(vurl_url url);
bool vurl_has_non_empty_username(vurl_url url);
bool vurl_has_non_empty_password(vurl_url url);
bool vurl_has_port(vurl_url url);
bool vurl_has_password(vurl_url url);
bool vurl_has_hash(vurl_url url);
bool vurl_has_search(vurl_url url);

vurl_owned_string vurl_idna_to_unicode(const char* input, size_t length);
vurl_owned_string vurl_idna_to_ascii(const char* input, size_t length);

/* ---- vjson ----------------------------------------------------------- */

typedef struct vbind_json_doc vbind_json_doc;

enum {
  VBIND_JSON_NULL = 0,
  VBIND_JSON_TRUE,
  VBIND_JSON_FALSE,
  VBIND_JSON_NUMBER,
  VBIND_JSON_STRING,
  VBIND_JSON_KEY,
  VBIND_JSON_ARRAY_START,
  VBIND_JSON_ARRAY_END,
  VBIND_JSON_OBJECT_START,
  VBIND_JSON_OBJECT_END
};

/*
 * One token of the verified parser's tape, in document order.
 * Numbers, strings and keys: [a, b) is the number's bytes, or the string's
 * body between the quotes; `escaped` is nonzero if the body has escapes.
 * '[' and '{': `a` is the index of the matching ']' or '}' token.
 */
typedef struct {
  uint8_t kind;
  uint8_t escaped;
  uint16_t pad;
  uint32_t a;
  uint32_t b;
} vbind_json_tok;

/* vbind_json_doc_parse results. */
enum {
  VBIND_JSON_OK = 0,
  VBIND_JSON_E_UNEXPECTED_END,
  VBIND_JSON_E_UNTERMINATED_STRING,
  VBIND_JSON_E_UNEXPECTED_BYTE,
  VBIND_JSON_E_CONTROL_CHARACTER,
  VBIND_JSON_E_INVALID_ESCAPE,
  VBIND_JSON_E_INVALID_NUMBER,
  VBIND_JSON_E_INVALID_LITERAL,
  VBIND_JSON_E_TOO_DEEP,
  VBIND_JSON_E_TRAILING_DATA,
  VBIND_JSON_E_INVALID_UTF8,
  VBIND_JSON_E_TOO_LARGE,
  VBIND_JSON_E_EMPTY
};

/* Accessor results. */
enum { VBIND_JSON_GET_OK = 0, VBIND_JSON_GET_WRONG_TYPE, VBIND_JSON_GET_OUT_OF_RANGE };

/*
 * A document is reused across parses. Everything it hands out stays valid
 * until the next parse into it or vbind_json_doc_free. The input is not
 * copied and must outlive those results.
 */
vbind_json_doc* vbind_json_doc_new(void);
void vbind_json_doc_free(vbind_json_doc* doc);
int vbind_json_doc_parse(vbind_json_doc* doc, const uint8_t* input,
                         size_t length, size_t* err_offset);
const vbind_json_tok* vbind_json_doc_tokens(const vbind_json_doc* doc,
                                            size_t* count);
int vbind_json_doc_string(vbind_json_doc* doc, size_t token,
                          const uint8_t** data, size_t* length);
int vbind_json_doc_raw(vbind_json_doc* doc, size_t token,
                       const uint8_t** data, size_t* length);
int vbind_json_doc_f64(vbind_json_doc* doc, size_t token, double* value);
int vbind_json_doc_i64(vbind_json_doc* doc, size_t token, int64_t* value);
int vbind_json_doc_u64(vbind_json_doc* doc, size_t token, uint64_t* value);

#ifdef __cplusplus
}
#endif

#endif /* VBIND_H */
