/*
 * vtext: verified transcoding and forgiving base64, with simdutf's
 * semantics. Each function is simdutf's function of the same name with a
 * `vtext_` prefix; a `simdutf::result` is returned as its error code, with
 * the count written through `count` (which may be NULL).
 *
 * Output buffers must hold simdutf's documented output size for the input
 * (for example `vtext_utf16_length_from_utf8` units for
 * `vtext_convert_utf8_to_utf16`), as with simdutf.
 */
#ifndef VTEXT_UTF_H
#define VTEXT_UTF_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* simdutf::error_code */
enum {
  VTEXT_SUCCESS = 0,
  VTEXT_HEADER_BITS,
  VTEXT_TOO_SHORT,
  VTEXT_TOO_LONG,
  VTEXT_OVERLONG,
  VTEXT_TOO_LARGE,
  VTEXT_SURROGATE,
  VTEXT_INVALID_BASE64_CHARACTER,
  VTEXT_BASE64_INPUT_REMAINDER,
  VTEXT_BASE64_EXTRA_BITS,
  VTEXT_OUTPUT_BUFFER_TOO_SMALL,
  VTEXT_OTHER
};

bool vtext_validate_utf8(const char *buf, size_t len);
int vtext_validate_utf8_with_errors(const char *buf, size_t len, size_t *count);
bool vtext_validate_ascii(const char *buf, size_t len);
int vtext_validate_ascii_with_errors(const char *buf, size_t len, size_t *count);

size_t vtext_utf8_length_from_latin1(const char *buf, size_t len);
size_t vtext_utf16_length_from_utf8(const char *buf, size_t len);
size_t vtext_latin1_length_from_utf8(const char *buf, size_t len);
size_t vtext_utf8_length_from_utf16(const uint16_t *buf, size_t len);

/* UTF-16 well-formedness and UTF-32, unverified. `out` may be `buf`.
 * utf8_length_from_utf16_with_replacement returns VTEXT_SURROGATE when the
 * text has any surrogate, paired or not; the length is right either way. */
bool vtext_validate_utf16(const uint16_t *buf, size_t len);
int vtext_validate_utf16_with_errors(const uint16_t *buf, size_t len, size_t *count);
void vtext_to_well_formed_utf16(const uint16_t *buf, size_t len, uint16_t *out);
int vtext_utf8_length_from_utf16_with_replacement(const uint16_t *buf, size_t len, size_t *count);
size_t vtext_convert_utf32_to_utf8(const uint32_t *buf, size_t len, char *out);

size_t vtext_convert_latin1_to_utf8(const char *buf, size_t len, char *out);
size_t vtext_convert_latin1_to_utf8_safe(const char *buf, size_t len, char *out, size_t out_len);
size_t vtext_convert_latin1_to_utf16(const char *buf, size_t len, uint16_t *out);
size_t vtext_convert_utf8_to_utf16(const char *buf, size_t len, uint16_t *out);
int vtext_convert_utf8_to_utf16_with_errors(const char *buf, size_t len, uint16_t *out, size_t *count);
size_t vtext_convert_utf16_to_utf8(const uint16_t *buf, size_t len, char *out);
size_t vtext_convert_utf16_to_latin1(const uint16_t *buf, size_t len, char *out);
int vtext_convert_utf8_to_latin1_with_errors(const char *buf, size_t len, char *out, size_t *count);

/* `options` is a simdutf::base64_options value. */
size_t vtext_base64_length_from_binary(size_t len, uint64_t options);
size_t vtext_binary_to_base64(const char *buf, size_t len, char *out, uint64_t options);
size_t vtext_maximal_binary_length_from_base64(const char *buf, size_t len);
size_t vtext_maximal_binary_length_from_base64_utf16(const uint16_t *buf, size_t len);
/* `last` is a simdutf::last_chunk_handling_options value. A loose decode of
 * valid text is the verified forgiving decoder's; strict and
 * stop_before_partial, invalid text and short buffers are decoded by an
 * unverified transliteration of simdutf's scalar decoder. */
int vtext_base64_to_binary(const char *buf, size_t len, char *out, uint64_t options, uint64_t last,
                           size_t *count);
int vtext_base64_to_binary_utf16(const uint16_t *buf, size_t len, char *out, uint64_t options,
                                 uint64_t last, size_t *count);
/* `count` receives the number of input units read. With `up_to_bad_char`,
 * the bytes before an invalid character are decoded. */
int vtext_base64_to_binary_safe(const char *buf, size_t len, char *out, size_t *out_len, uint64_t options,
                                uint64_t last, bool up_to_bad_char, size_t *count);
int vtext_base64_to_binary_safe_utf16(const uint16_t *buf, size_t len, char *out, size_t *out_len,
                                      uint64_t options, uint64_t last, bool up_to_bad_char,
                                      size_t *count);

#ifdef __cplusplus
}
#endif

#endif
