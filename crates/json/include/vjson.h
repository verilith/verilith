/* vjson's native C API: the verified parser behind the same zero-copy
 * interface the Rust API has. For the cJSON-compatible drop-in, see cJSON.h.
 *
 * Build with `cargo build --profile release-abort --features capi` and link
 * target/release-abort/libverilith_json.a (plus -lm -lpthread -ldl).
 *
 *     vjson_parser *p = vjson_parser_new();
 *     vjson_value root, v;
 *     if (vjson_parse(p, buf, len, &root, NULL) == 0 &&
 *         vjson_object_get(root, "name", 4, &v)) {
 *         const char *s; size_t n;
 *         if (vjson_get_string(v, &s, &n)) fwrite(s, 1, n, stdout);
 *     }
 *     vjson_parser_free(p);
 *
 * Lifetimes. A value is a view into its parser's last document, and strings
 * without escapes point into the input itself. Values, iterators and the
 * strings read through them are valid until the parser parses again or is
 * freed, and only while the input buffer is alive and unchanged. Nothing
 * needs to be freed except the parser.
 *
 * Threads. A parser parses on one thread at a time. Once vjson_parse has
 * returned, any number of threads may read the document's values.
 *
 * Strings and keys are decoded (escapes resolved) UTF-8, given as a pointer
 * and a length. They are not NUL-terminated and may contain NUL bytes. */
#ifndef VJSON_H
#define VJSON_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct vjson_parser vjson_parser;

/* Pass these by value. Treat the fields as private: only values and
 * iterators that this API returned may be passed back to it. */
typedef struct vjson_value {
    const void *doc;
    size_t idx;
} vjson_value;

typedef struct vjson_iter {
    const void *doc;
    size_t idx;
} vjson_iter;

enum {
    VJSON_INVALID = 0, /* not a value: zeroed, or from a failed parse */
    VJSON_NULL = 1,
    VJSON_BOOL = 2,
    VJSON_NUMBER = 3,
    VJSON_STRING = 4,
    VJSON_ARRAY = 5,
    VJSON_OBJECT = 6
};

enum {
    VJSON_OK = 0,
    VJSON_E_UNEXPECTED_END = 1,
    VJSON_E_UNTERMINATED_STRING = 2,
    VJSON_E_UNEXPECTED_BYTE = 3,
    VJSON_E_CONTROL_CHARACTER = 4,
    VJSON_E_INVALID_ESCAPE = 5,
    VJSON_E_INVALID_NUMBER = 6,
    VJSON_E_INVALID_LITERAL = 7,
    VJSON_E_TOO_DEEP = 8, /* nesting deeper than 1000 levels */
    VJSON_E_TRAILING_DATA = 9,
    VJSON_E_INVALID_UTF8 = 10,
    VJSON_E_TOO_LARGE = 11, /* input of 256 TiB or more */
    VJSON_E_ARGUMENT = -1   /* null parser, or null input with len != 0 */
};

typedef struct vjson_error {
    int code;
    uint8_t byte;  /* for UNEXPECTED_BYTE and CONTROL_CHARACTER */
    size_t offset; /* byte offset of the problem */
    size_t line;   /* 1-based */
    size_t column; /* 1-based, in bytes */
} vjson_error;

/* A parser keeps its buffers between documents, so parsing many documents
 * with one parser does not allocate each time. */
vjson_parser *vjson_parser_new(void);
void vjson_parser_free(vjson_parser *p);

/* Parses one complete JSON text (RFC 8259; a leading UTF-8 BOM is skipped).
 * Returns VJSON_OK and sets *root, or returns an error code and fills *err.
 * root and err may be NULL. The parser's previous document ends here. */
int vjson_parse(vjson_parser *p, const char *json, size_t len, vjson_value *root, vjson_error *err);

/* A static, NUL-terminated description of an error code. */
const char *vjson_error_message(int code);

int vjson_type(vjson_value v);
bool vjson_is_null(vjson_value v);

/* Each getter returns false, leaving its out-parameters alone, if the value
 * is not of that type. Out-parameters may be NULL. */
bool vjson_get_bool(vjson_value v, bool *out);
/* The nearest double. */
bool vjson_get_double(vjson_value v, double *out);
/* False also for a number with a fraction or exponent, or outside int64. */
bool vjson_get_int64(vjson_value v, int64_t *out);
/* The number as written, e.g. "-1.5e3". */
bool vjson_get_number_text(vjson_value v, const char **s, size_t *len);
bool vjson_get_string(vjson_value v, const char **s, size_t *len);

/* Number of elements or members. Walks the container. */
bool vjson_length(vjson_value v, size_t *out);

/*     vjson_iter it; vjson_value e;
 *     if (vjson_array_iter(v, &it))
 *         while (vjson_array_next(&it, &e)) { ... }
 *
 * The next functions return the type of the value they yield (VJSON_NULL
 * to VJSON_OBJECT, all nonzero), or 0 at the end, so a loop that switches
 * on the type needs no separate vjson_type call. */
bool vjson_array_iter(vjson_value v, vjson_iter *it);
int vjson_array_next(vjson_iter *it, vjson_value *out);

/* Members come in document order, duplicates included. */
bool vjson_object_iter(vjson_value v, vjson_iter *it);
int vjson_object_next(vjson_iter *it, const char **key, size_t *key_len, vjson_value *out);

/* The first member named key. Walks the object. */
bool vjson_object_get(vjson_value v, const char *key, size_t key_len, vjson_value *out);
/* The index-th element. Walks the array. */
bool vjson_array_at(vjson_value v, size_t index, vjson_value *out);

#ifdef __cplusplus
}
#endif

#endif
