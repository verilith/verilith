/* vtext's ICU-shaped C API: unorm2 (normalization) and uidna (UTS #46).
 *
 * Every function is exported as vtext_<ICU name>. Built with the `icu-abi`
 * feature, the library also exports ICU's own unversioned names, so a program
 * compiled against ICU with U_DISABLE_RENAMING=1 can link vtext instead.
 *
 * Conventions follow ICU: a length of -1 means NUL-terminated; outputs are
 * NUL-terminated when there is room; the full length is always returned, with
 * U_BUFFER_OVERFLOW_ERROR (15) when it does not fit, so callers can preflight;
 * a function does nothing if *pErrorCode is already a failure (> 0). */
#ifndef VTEXT_ICU_H
#define VTEXT_ICU_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint16_t vtext_UChar;
typedef int32_t vtext_UErrorCode;
typedef int8_t vtext_UBool;

typedef struct vtext_UNormalizer2 vtext_UNormalizer2;
typedef struct vtext_UIDNA vtext_UIDNA;

/* ICU's UIDNAInfo. Set size = sizeof(vtext_UIDNAInfo) before a call. */
typedef struct vtext_UIDNAInfo {
    int16_t size;
    vtext_UBool isTransitionalDifferent;
    vtext_UBool reservedB3;
    uint32_t errors;
    int32_t reservedI2;
    int32_t reservedI3;
} vtext_UIDNAInfo;

enum {
    VTEXT_UIDNA_DEFAULT = 0,
    VTEXT_UIDNA_USE_STD3_RULES = 2,
    VTEXT_UIDNA_CHECK_BIDI = 4,
    VTEXT_UIDNA_CHECK_CONTEXTJ = 8,
    VTEXT_UIDNA_NONTRANSITIONAL_TO_ASCII = 0x10,
    VTEXT_UIDNA_NONTRANSITIONAL_TO_UNICODE = 0x20
};

const vtext_UNormalizer2 *vtext_unorm2_getNFCInstance(vtext_UErrorCode *pErrorCode);
const vtext_UNormalizer2 *vtext_unorm2_getNFDInstance(vtext_UErrorCode *pErrorCode);
const vtext_UNormalizer2 *vtext_unorm2_getNFKCInstance(vtext_UErrorCode *pErrorCode);
const vtext_UNormalizer2 *vtext_unorm2_getNFKDInstance(vtext_UErrorCode *pErrorCode);
int32_t vtext_unorm2_normalize(const vtext_UNormalizer2 *norm2, const vtext_UChar *src,
                               int32_t length, vtext_UChar *dest, int32_t capacity,
                               vtext_UErrorCode *pErrorCode);
vtext_UBool vtext_unorm2_isNormalized(const vtext_UNormalizer2 *norm2, const vtext_UChar *s,
                                      int32_t length, vtext_UErrorCode *pErrorCode);
/* Returns UNORM_YES (1) or UNORM_NO (0); never UNORM_MAYBE. */
int32_t vtext_unorm2_quickCheck(const vtext_UNormalizer2 *norm2, const vtext_UChar *s,
                                int32_t length, vtext_UErrorCode *pErrorCode);

vtext_UIDNA *vtext_uidna_openUTS46(uint32_t options, vtext_UErrorCode *pErrorCode);
void vtext_uidna_close(vtext_UIDNA *idna);
int32_t vtext_uidna_nameToASCII(const vtext_UIDNA *idna, const vtext_UChar *name, int32_t length,
                                vtext_UChar *dest, int32_t capacity, vtext_UIDNAInfo *pInfo,
                                vtext_UErrorCode *pErrorCode);
int32_t vtext_uidna_nameToUnicode(const vtext_UIDNA *idna, const vtext_UChar *name,
                                  int32_t length, vtext_UChar *dest, int32_t capacity,
                                  vtext_UIDNAInfo *pInfo, vtext_UErrorCode *pErrorCode);
int32_t vtext_uidna_nameToASCII_UTF8(const vtext_UIDNA *idna, const char *name, int32_t length,
                                     char *dest, int32_t capacity, vtext_UIDNAInfo *pInfo,
                                     vtext_UErrorCode *pErrorCode);
int32_t vtext_uidna_nameToUnicodeUTF8(const vtext_UIDNA *idna, const char *name, int32_t length,
                                      char *dest, int32_t capacity, vtext_UIDNAInfo *pInfo,
                                      vtext_UErrorCode *pErrorCode);

#ifdef __cplusplus
}
#endif

#endif
