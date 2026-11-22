/* One driver for cre2's API, linked once with cre2 + RE2 and once with
 * vregex (feature cre2-abi). Reads "hexpattern hextext" lines and prints,
 * for each, what cre2_match reports under every anchor from position 0
 * and from position 1, with options that vary from line to line:
 * case-insensitive on every 3rd line, dot_nl on every 4th, literal on
 * every 7th. */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cre2.h"

static int unhex(const char *h, size_t n, char *out)
{
    for (size_t i = 0; i + 1 < n; i += 2) {
        unsigned v;
        sscanf(h + i, "%2x", &v);
        out[i / 2] = (char)v;
    }
    return (int)(n / 2);
}

int main(void)
{
    static char line[1 << 16], pat[1 << 15], text[1 << 15];
    unsigned long lineno = 0;
    while (fgets(line, sizeof line, stdin)) {
        size_t n = strcspn(line, "\n");
        line[n] = 0;
        char *sp = strchr(line, ' ');
        int plen = unhex(line, sp ? (size_t)(sp - line) : n, pat);
        int tlen = sp ? unhex(sp + 1, strlen(sp + 1), text) : 0;
        cre2_options_t *opt = cre2_opt_new();
        cre2_opt_set_log_errors(opt, 0);
        if (lineno % 3 == 2) cre2_opt_set_case_sensitive(opt, 0);
        if (lineno % 4 == 3) cre2_opt_set_dot_nl(opt, 1);
        if (lineno % 7 == 6) cre2_opt_set_literal(opt, 1);
        lineno++;
        cre2_regexp_t *re = cre2_new(pat, plen, opt);
        cre2_opt_delete(opt);
        int code = cre2_error_code(re);
        if (code) {
            puts("ERR");
            cre2_delete(re);
            continue;
        }
        int ng = cre2_num_capturing_groups(re) + 1;
        cre2_string_t *m = calloc((size_t)ng + 1, sizeof *m);
        printf("g%d", ng);
        for (int start = 0; start <= 1 && start <= tlen; start++) {
            for (int anchor = CRE2_UNANCHORED; anchor <= CRE2_ANCHOR_BOTH; anchor++) {
                printf(" |");
                if (!cre2_match(re, text, tlen, start, tlen, (cre2_anchor_t)anchor, m, ng + 1)) {
                    printf(" no");
                    continue;
                }
                for (int i = 0; i <= ng; i++) {
                    if (!m[i].data) printf(" -");
                    else printf(" %d,%d", (int)(m[i].data - text), (int)(m[i].data - text) + m[i].length);
                }
            }
        }
        putchar('\n');
        free(m);
        cre2_delete(re);
    }
    return 0;
}
