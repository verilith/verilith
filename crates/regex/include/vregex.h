/* vregex: a linear-time regular expression engine, verified with Verus.
 *
 * Text and patterns are bytes with a length; patterns are UTF-8. A compiled
 * pattern may be used from several threads at once. */
#ifndef VREGEX_H
#define VREGEX_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct vregex vregex;

enum {
    VREGEX_OK = 0,
    VREGEX_SYNTAX = 1,      /* not a pattern: see vregex_error_offset */
    VREGEX_BAD_UTF8 = 2,    /* the pattern is not UTF-8 */
    VREGEX_TOO_BIG = 3,     /* too long, too deep, or too large a program */
    VREGEX_UNSUPPORTED = 4  /* a cre2 option vregex does not have */
};

/* Compiles pattern[0..len). Never returns NULL: check vregex_error. */
vregex *vregex_new(const char *pattern, size_t len);
void vregex_free(vregex *re);
int vregex_error(const vregex *re);
size_t vregex_error_offset(const vregex *re);

/* Number of groups, counting group 0 (the whole match). */
size_t vregex_groups(const vregex *re);
/* The number of the group called name[0..len), or -1. */
int vregex_group_index(const vregex *re, const char *name, size_t len);

/* Searches text[0..len) from byte `from` for the leftmost match (among
 * matches at one start, the one the pattern prefers, as in Perl and RE2).
 * Returns 1 and fills slots[0..nslots): slots[2k] and slots[2k+1] are the
 * start and end of group k, SIZE_MAX if the group took no part. Returns 0
 * if there is no match. Time is linear in len for a fixed pattern. */
int vregex_search(const vregex *re, const char *text, size_t len, size_t from,
                  size_t *slots, size_t nslots);

#ifdef __cplusplus
}
#endif
#endif
