/*
 * simdutf.h: a drop-in for the part of simdutf 7.7.0 that Node.js and V8 use,
 * backed by vtext (verified UTF-8/UTF-16/Latin-1 transcoding and forgiving
 * base64) through libvbind's vtext_* C API (vtext_utf.h).
 *
 * The declarations follow simdutf 7.7.0's signatures and results, so
 * `--shared-simdutf --shared-simdutf-includes=<this directory>` builds Node
 * against it without a patch. Only the functions Node calls are here; the
 * runtime implementation selection of simdutf (get_active_implementation and
 * friends) is not, since vtext picks its AVX2 kernels by itself.
 *
 * Little-endian only: the utf16le functions are the native ones. The
 * accept-garbage base64 options are not supported (Node does not use them).
 *
 * The atomic_ base64 functions, which V8 calls for a SharedArrayBuffer, go
 * through a private buffer in blocks and touch the shared memory one byte at
 * a time with relaxed atomic operations, as simdutf's do.
 */
#ifndef SIMDUTF_H
#define SIMDUTF_H

// The standard headers real simdutf.h includes, which code built against it
// (Node's js2c among it) relies on.
#include <algorithm>
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

#define SIMDUTF_VERSION "7.7.0"
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
  SIMDUTF_VERSION_MAJOR = 7,
  SIMDUTF_VERSION_MINOR = 7,
  SIMDUTF_VERSION_REVISION = 0
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

#define SIMDUTF_ATOMIC_REF 1

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

simdutf_warn_unused inline bool validate_utf16(const char16_t *buf,
                                               size_t len) noexcept {
  return vtext_validate_utf16(vtext_detail::u16(buf), len);
}
simdutf_warn_unused inline bool validate_utf16le(const char16_t *buf,
                                                 size_t len) noexcept {
  return vtext_validate_utf16(vtext_detail::u16(buf), len);
}
simdutf_warn_unused inline result
validate_utf16_with_errors(const char16_t *buf, size_t len) noexcept {
  size_t n = 0;
  int e = vtext_validate_utf16_with_errors(vtext_detail::u16(buf), len, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
validate_utf16le_with_errors(const char16_t *buf, size_t len) noexcept {
  return validate_utf16_with_errors(buf, len);
}
/* Unpaired surrogates become U+FFFD; output may be the input. */
inline void to_well_formed_utf16(const char16_t *input, size_t len,
                                 char16_t *output) noexcept {
  vtext_to_well_formed_utf16(vtext_detail::u16(input), len,
                             vtext_detail::u16(output));
}
inline void to_well_formed_utf16le(const char16_t *input, size_t len,
                                   char16_t *output) noexcept {
  to_well_formed_utf16(input, len, output);
}
simdutf_warn_unused inline const char *find(const char *start, const char *end,
                                            char character) noexcept {
  const void *p = std::memchr(start, character, size_t(end - start));
  return p ? static_cast<const char *>(p) : end;
}
simdutf_warn_unused inline const char16_t *
find(const char16_t *start, const char16_t *end, char16_t character) noexcept {
  return std::find(start, end, character);
}

/* ---- lengths --------------------------------------------------------- */
/* The count is the UTF-8 length with unpaired surrogates read as U+FFFD;
 * the error is SURROGATE when the text has any surrogate, paired or not. */
simdutf_warn_unused inline result
utf8_length_from_utf16_with_replacement(const char16_t *input,
                                        size_t length) noexcept {
  size_t n = 0;
  int e = vtext_utf8_length_from_utf16_with_replacement(
      vtext_detail::u16(input), length, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
utf8_length_from_utf16le_with_replacement(const char16_t *input,
                                          size_t length) noexcept {
  return utf8_length_from_utf16_with_replacement(input, length);
}

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
convert_valid_utf8_to_utf16(const char *input, size_t length,
                            char16_t *utf16_output) noexcept {
  return vtext_convert_utf8_to_utf16(input, length,
                                     vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline size_t
convert_valid_utf8_to_utf16le(const char *input, size_t length,
                              char16_t *utf16_output) noexcept {
  return vtext_convert_utf8_to_utf16(input, length,
                                     vtext_detail::u16(utf16_output));
}
simdutf_warn_unused inline result
convert_utf8_to_utf16_with_errors(const char *input, size_t length,
                                  char16_t *utf16_output) noexcept {
  size_t n = 0;
  int e = vtext_convert_utf8_to_utf16_with_errors(
      input, length, vtext_detail::u16(utf16_output), &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
convert_utf8_to_utf16le_with_errors(const char *input, size_t length,
                                    char16_t *utf16_output) noexcept {
  return convert_utf8_to_utf16_with_errors(input, length, utf16_output);
}
/* 0 if a unit is not a Unicode scalar value. */
simdutf_warn_unused inline size_t
convert_utf32_to_utf8(const char32_t *input, size_t length,
                      char *utf8_buffer) noexcept {
  return vtext_convert_utf32_to_utf8(
      reinterpret_cast<const uint32_t *>(input), length, utf8_buffer);
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
  size_t n = 0;
  int e = vtext_base64_to_binary(input, length, output, options,
                                 last_chunk_options, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
base64_to_binary(const char16_t *input, size_t length, char *output,
                 base64_options options = base64_default,
                 last_chunk_handling_options last_chunk_options =
                     loose) noexcept {
  size_t n = 0;
  int e = vtext_base64_to_binary_utf16(vtext_detail::u16(input), length,
                                       output, options, last_chunk_options,
                                       &n);
  return vtext_detail::res(e, n);
}
/* The count is the number of input units read, or the position of the
 * error. outlen comes back as the number of bytes written. */
simdutf_warn_unused inline result
base64_to_binary_safe(const char *input, size_t length, char *output,
                      size_t &outlen, base64_options options = base64_default,
                      last_chunk_handling_options last_chunk_options = loose,
                      bool decode_up_to_bad_char = false) noexcept {
  size_t n = 0;
  int e = vtext_base64_to_binary_safe(input, length, output, &outlen, options,
                                      last_chunk_options,
                                      decode_up_to_bad_char, &n);
  return vtext_detail::res(e, n);
}
simdutf_warn_unused inline result
base64_to_binary_safe(const char16_t *input, size_t length, char *output,
                      size_t &outlen, base64_options options = base64_default,
                      last_chunk_handling_options last_chunk_options = loose,
                      bool decode_up_to_bad_char = false) noexcept {
  size_t n = 0;
  int e = vtext_base64_to_binary_safe_utf16(vtext_detail::u16(input), length,
                                            output, &outlen, options,
                                            last_chunk_options,
                                            decode_up_to_bad_char, &n);
  return vtext_detail::res(e, n);
}

/* ---- base64 on memory other threads may be writing --------------------- */
namespace vtext_detail {
inline void atomic_read(char *dst, const char *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    dst[i] = __atomic_load_n(src + i, __ATOMIC_RELAXED);
}
inline void atomic_write(char *dst, const char *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    __atomic_store_n(dst + i, src[i], __ATOMIC_RELAXED);
}
inline bool base64_space(char16_t c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f';
}
template <class char_type>
inline result atomic_base64_to_binary_safe(
    const char_type *input, size_t length, char *output, size_t &outlen,
    base64_options options, last_chunk_handling_options last_chunk_options,
    bool decode_up_to_bad_char) {
  char block[4096];
  const char_type *const input_init = input;
  const size_t length_init = length;
  size_t actual_out = 0;
  bool last_block = false;
  result r;
  while (!last_block) {
    last_block |= sizeof(block) >= outlen - actual_out;
    size_t block_out = (std::min)(sizeof(block), outlen - actual_out);
    r = base64_to_binary_safe(input, length, block, block_out, options,
                              last_chunk_options, decode_up_to_bad_char);
    atomic_write(output + actual_out, block, block_out);
    actual_out += block_out;
    length -= r.count;
    input += r.count;
    if (r.error != OUTPUT_BUFFER_TOO_SMALL) break;
  }
  if (size_t(input - input_init) != length_init) {
    /* Not all of the input was read: do not end on whitespace. */
    while (input > input_init && base64_space(char16_t(*(input - 1)))) --input;
  }
  outlen = actual_out;
  return result(r.error, size_t(input - input_init));
}
} // namespace vtext_detail

inline size_t
atomic_binary_to_base64(const char *input, size_t length, char *output,
                        base64_options options = base64_default) noexcept {
  char block[1024 * 3];
  size_t written = 0;
  for (size_t i = 0; i < length; i += sizeof(block)) {
    size_t n = (std::min)(sizeof(block), length - i);
    vtext_detail::atomic_read(block, input + i, n);
    written += binary_to_base64(block, n, output + written, options);
  }
  return written;
}
simdutf_warn_unused inline result atomic_base64_to_binary_safe(
    const char *input, size_t length, char *output, size_t &outlen,
    base64_options options = base64_default,
    last_chunk_handling_options last_chunk_options = loose,
    bool decode_up_to_bad_char = false) noexcept {
  return vtext_detail::atomic_base64_to_binary_safe(
      input, length, output, outlen, options, last_chunk_options,
      decode_up_to_bad_char);
}
simdutf_warn_unused inline result atomic_base64_to_binary_safe(
    const char16_t *input, size_t length, char *output, size_t &outlen,
    base64_options options = base64_default,
    last_chunk_handling_options last_chunk_options = loose,
    bool decode_up_to_bad_char = false) noexcept {
  return vtext_detail::atomic_base64_to_binary_safe(
      input, length, output, outlen, options, last_chunk_options,
      decode_up_to_bad_char);
}
} // namespace simdutf

#endif // SIMDUTF_H
