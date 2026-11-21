/* The native C API, by example. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "vregex.h"

int main(void)
{
    const char *pat = "(?P<year>\\d{4})-(?P<month>\\d{2})";
    vregex *re = vregex_new(pat, strlen(pat));
    assert(vregex_error(re) == VREGEX_OK);
    assert(vregex_groups(re) == 3);
    assert(vregex_group_index(re, "month", 5) == 2);
    assert(vregex_group_index(re, "day", 3) == -1);
    const char *text = "on 2026-11 and 1999-01";
    size_t s[6];
    assert(vregex_search(re, text, strlen(text), 0, s, 6) == 1);
    assert(s[0] == 3 && s[1] == 10 && s[2] == 3 && s[3] == 7 && s[4] == 8 && s[5] == 10);
    assert(vregex_search(re, text, strlen(text), 4, s, 6) == 1);
    assert(s[0] == 15 && s[1] == 22);
    assert(vregex_search(re, text, strlen(text), 16, s, 6) == 0);
    vregex_free(re);

    re = vregex_new("a(b", 3);
    assert(vregex_error(re) == VREGEX_SYNTAX);
    assert(vregex_groups(re) == 0);
    assert(vregex_search(re, "ab", 2, 0, s, 2) == 0);
    vregex_free(re);

    re = vregex_new("\xff", 1);
    assert(vregex_error(re) == VREGEX_BAD_UTF8);
    vregex_free(re);

    /* An optional group that takes no part. */
    re = vregex_new("(a)|b", 5);
    assert(vregex_search(re, "b", 1, 0, s, 4) == 1);
    assert(s[0] == 0 && s[1] == 1 && s[2] == SIZE_MAX && s[3] == SIZE_MAX);
    vregex_free(re);
    puts("capi ok");
    return 0;
}
