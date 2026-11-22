/* vfont: a formally verified OpenType font sanitizer. C interface. */
#ifndef VFONT_H_
#define VFONT_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Sanitizes the `len` bytes at `input`: OpenType/TrueType, WOFF, WOFF2, or
 * a TrueType Collection, of which `index` picks one font (it is ignored
 * for other files).
 *
 * Returns 1 if the font was accepted: `*out` is then a newly allocated,
 * rebuilt font of `*out_len` bytes, to be released with vfont_free().
 * Returns 0 if the font was refused: `*out` is NULL and `*out_len` is 0. */
int vfont_sanitize(const uint8_t *input, size_t len, uint32_t index,
                   uint8_t **out, size_t *out_len);

/* Releases a font returned by vfont_sanitize(); `len` is the length that
 * call stored. NULL is ignored. */
void vfont_free(uint8_t *ptr, size_t len);

#ifdef __cplusplus
}
#endif

#endif /* VFONT_H_ */
