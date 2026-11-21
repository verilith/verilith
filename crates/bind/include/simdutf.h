/*
 * simdutf.h: a drop-in for the part of simdutf 6.4.2 that Node.js uses,
 * backed by vtext (verified UTF-8/UTF-16/Latin-1 transcoding and forgiving
 * base64) through libvbind's vtext_* C API (vtext_utf.h).
 *
 * The declarations follow simdutf 6.4.2's signatures and results, so
 * `--shared-simdutf --shared-simdutf-includes=<this directory>` builds Node
 * against it without a patch. Only the functions Node calls are here; the
 * runtime implementation selection of simdutf (get_active_implementation and
 * friends) is not, since vtext picks its AVX2 kernels by itself.
 *
 * Little-endian only: the utf16le functions are the native ones.
 * last_chunk_handling_options other than `loose` are not supported and
 * return error_code::OTHER (Node does not use them).
 */
#ifndef SIMDUTF_H
#define SIMDUTF_H

// The standard headers real simdutf.h includes, which code built against it
// (Node's js2c among it) relies on.
#include <atomic>
#include <cfloat>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <type_traits>
#include <vector>

#include "vtext_utf.h"

#define SIMDUTF_VERSION "6.4.2"
#define SIMDUTF_IS_VTEXT 1

#ifndef simdutf_warn_unused
#define simdutf_warn_unused [[nodiscard]]
#endif
#ifndef simdutf_really_inline
#define simdutf_really_inline inline __attribute__((always_inline))
#endif

#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "the vtext simdutf.h supports little-endian targets only"
#endif

namespace simdutf {

enum {
  SIMDUTF_VERSION_MAJOR = 6,
  SIMDUTF_VERSION_MINOR = 4,
  SIMDUTF_VERSION_REVISION = 2
};

enum error_code {
  SUCCESS = 0,
  HEADER_BITS,
  TOO_SHORT,
  TOO_LONG,
  OVERLONG,
  TOO_LARGE,
  SURROGATE,
  INVALID_BASE64_CHARACTER,
  BASE64_INPUT_REMAINDER,
  BASE64_EXTRA_BITS,
  OUTPUT_BUFFER_TOO_SMALL,
  OTHER
};

struct result {
  error_code error;
  size_t count;

  simdutf_really_inline result() : error{error_code::SUCCESS}, count{0} {}
  simdutf_really_inline result(error_code err, size_t pos)
      : error{err}, count{pos} {}
  simdutf_really_inline bool is_ok() const {
    return error == error_code::SUCCESS;
  }
  simdutf_really_inline bool is_err() const {
    return error != error_code::SUCCESS;
  }
};

enum base64_options : uint64_t {
  base64_default = 0,
  base64_url = 1,
  base64_reverse_padding = 2,
  base64_default_no_padding = base64_default | base64_reverse_padding,
  base64_url_with_padding = base64_url | base64_reverse_padding,
  base64_default_accept_garbage = 4,
  base64_url_accept_garbage = 5,
};

enum last_chunk_handling_options : uint64_t {
  loose = 0,
  strict = 1,
  stop_before_partial = 2,
};

namespace vtext_detail {
inline const uint16_t *u16(const char16_t *p) {
  return reinterpret_cast<const uint16_t *>(p);
}
inline uint16_t *u16(char16_t *p) { return reinterpret_cast<uint16_t *>(p); }
inline result res(int e, size_t n) {
  return result(static_cast<error_code>(e), n);
}
} // namespace vtext_detail

/* ---- validation ------------------------------------------------------ */

simdutf_warn_unused inline bool validate_utf8(const char *buf,
                                              size_t len) noexcept {
  return vtext_validate_utf8(buf, len);
}
simdutf_warn_unused inline result
validate_utf8_with_errors(const char *buf, size_t len) noexcept {
  size_t n = 0;
  int e = vtext_validate_utf8_with_errors(buf, len, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline bool validate_ascii(const char *buf,
                                               size_t len) noexcept {
  return vtext_validate_ascii(buf, len);
}
simdutf_warn_unused inline result
validate_ascii_with_errors(const char *buf, size_t len) noexcept {
  size_t n = 0;
  int e = vtext_validate_ascii_with_errors(buf, len, &n);
  return vtext_detail::res(e, n);
}

/* ---- lengths --------------------------------------------------------- */

simdutf_warn_unused inline size_t
utf8_length_from_latin1(const char *input, size_t length) noexcept {
  return vtext_utf8_length_from_latin1(input, length);
}
simdutf_warn_unused inline size_t
utf16_length_from_utf8(const char *input, size_t length) noexcept {
  return vtext_utf16_length_from_utf8(input, length);
}
simdutf_warn_unused inline size_t
latin1_length_from_utf8(const char *input, size_t length) noexcept {
  return vtext_latin1_length_from_utf8(input, length);
}
simdutf_warn_unused inline size_t
utf8_length_from_utf16(const char16_t *input, size_t length) noexcept {
  return vtext_utf8_length_from_utf16(vtext_detail::u16(input), length);
}
simdutf_warn_unused inline size_t
utf8_length_from_utf16le(const char16_t *input, size_t length) noexcept {
  return vtext_utf8_length_from_utf16(vtext_detail::u16(input), length);
}
simdutf_warn_unused inline size_t
utf16_length_from_latin1(size_t length) noexcept {
  return length;
}
simdutf_warn_unused inline size_t
latin1_length_from_utf16(size_t length) noexcept {
  return length;
}

/* ---- conversions ----------------------------------------------------- */

simdutf_warn_unused inline size_t
convert_latin1_to_utf8(const char *input, size_t length,
                       char *utf8_output) noexcept {
  return vtext_convert_latin1_to_utf8(input, length, utf8_output);
}
simdutf_warn_unused inline size_t
convert_latin1_to_utf8_safe(const char *input, size_t length,
                            char *utf8_output, size_t utf8_len) noexcept {
  return vtext_convert_latin1_to_utf8_safe(input, length, utf8_output,
                                           utf8_len);
}
simdutf_warn_unused inline size_t
convert_latin1_to_utf16(const char *input, size_t length,
                        char16_t *utf16_output) noexcept {
  return vtext_convert_latin1_to_utf16(input, length,
                                       vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline size_t
convert_latin1_to_utf16le(const char *input, size_t length,
                          char16_t *utf16_output) noexcept {
  return vtext_convert_latin1_to_utf16(input, length,
                                       vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline size_t
convert_utf8_to_utf16(const char *input, size_t length,
                      char16_t *utf16_output) noexcept {
  return vtext_convert_utf8_to_utf16(input, length,
                                     vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline size_t
convert_utf8_to_utf16le(const char *input, size_t length,
                        char16_t *utf16_output) noexcept {
  return vtext_convert_utf8_to_utf16(input, length,
                                     vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline size_t
convert_utf16_to_utf8(const char16_t *input, size_t length,
                      char *utf8_buffer) noexcept {
  return vtext_convert_utf16_to_utf8(vtext_detail::u16(input), length,
                                     utf8_buffer);
}
simdutf_warn_unused inline size_t
convert_utf16le_to_utf8(const char16_t *input, size_t length,
                        char *utf8_buffer) noexcept {
  return vtext_convert_utf16_to_utf8(vtext_detail::u16(input), length,
                                     utf8_buffer);
}
simdutf_warn_unused inline size_t
convert_utf16_to_latin1(const char16_t *input, size_t length,
                        char *latin1_buffer) noexcept {
  return vtext_convert_utf16_to_latin1(vtext_detail::u16(input), length,
                                       latin1_buffer);
}
simdutf_warn_unused inline size_t
convert_utf16le_to_latin1(const char16_t *input, size_t length,
                          char *latin1_buffer) noexcept {
  return vtext_convert_utf16_to_latin1(vtext_detail::u16(input), length,
                                       latin1_buffer);
}
simdutf_warn_unused inline result
convert_utf8_to_latin1_with_errors(const char *input, size_t length,
                                   char *latin1_output) noexcept {
  size_t n = 0;
  int e = vtext_convert_utf8_to_latin1_with_errors(input, length,
                                                   latin1_output, &n);
  return vtext_detail::res(e, n);
}

/* ---- base64 ---------------------------------------------------------- */

simdutf_warn_unused inline size_t
maximal_binary_length_from_base64(const char *input, size_t length) noexcept {
  return vtext_maximal_binary_length_from_base64(input, length);
}
simdutf_warn_unused inline size_t
maximal_binary_length_from_base64(const char16_t *input,
                                  size_t length) noexcept {
  return vtext_maximal_binary_length_from_base64_utf16(vtext_detail::u16(input),
                                                       length);
}
simdutf_warn_unused inline size_t
base64_length_from_binary(size_t length,
                          base64_options options = base64_default) noexcept {
  return vtext_base64_length_from_binary(length, options);
}
inline size_t binary_to_base64(const char *input, size_t length, char *output,
                               base64_options options = base64_default) noexcept {
  return vtext_binary_to_base64(input, length, output, options);
}

simdutf_warn_unused inline result
base64_to_binary(const char *input, size_t length, char *output,
                 base64_options options = base64_default,
                 last_chunk_handling_options last_chunk_options =
                     loose) noexcept {
  if (last_chunk_options != loose) return result(OTHER, 0);
  size_t n = 0;
  int e = vtext_base64_to_binary(input, length, output, options, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
base64_to_binary(const char16_t *input, size_t length, char *output,
                 base64_options options = base64_default,
                 last_chunk_handling_options last_chunk_options =
                     loose) noexcept {
  if (last_chunk_options != loose) return result(OTHER, 0);
  size_t n = 0;
  int e = vtext_base64_to_binary_utf16(vtext_detail::u16(input), length,
                                       output, options, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
base64_to_binary_safe(const char *input, size_t length, char *output,
                      size_t &outlen, base64_options options = base64_default,
                      last_chunk_handling_options last_chunk_options =
                          loose) noexcept {
  if (last_chunk_options != loose) return result(OTHER, 0);
  size_t n = 0;
  int e = vtext_base64_to_binary_safe(input, length, output, &outlen, options,
                                      &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
base64_to_binary_safe(const char16_t *input, size_t length, char *output,
                      size_t &outlen, base64_options options = base64_default,
                      last_chunk_handling_options last_chunk_options =
                          loose) noexcept {
  if (last_chunk_options != loose) return result(OTHER, 0);
  size_t n = 0;
  int e = vtext_base64_to_binary_safe_utf16(vtext_detail::u16(input), length,
                                            output, &outlen, options, &n);
  return vtext_detail::res(e, n);
}

} // namespace simdutf

#endif // SIMDUTF_H
