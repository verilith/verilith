/* Regex suite. One driver against cre2's C API (cre2.h, the C wrapper of
 * RE2), linked once with cre2 + RE2 and once with vregex (feature
 * cre2-abi), which exports the same functions.
 *
 * Cases NAME/FILE for every pattern below and every file in $VBENCH_DATA:
 * one call finds every match of the pattern in the file, one after another
 * (cre2_match, unanchored, asking for the whole match and the groups).
 * check = matches * 2^32 + total length of the matches and groups. */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cre2.h"
#include "runner.h"

static const struct { const char *name, *pattern; } PATTERNS[] = {
    { "literal", "Copperfield" },
    { "literal-nocase", "(?i)copperfield" },
    { "alternation", "Agnes|Dora|Steerforth|Peggotty|Micawber" },
    { "class-run", "[A-Z][a-z]+ [A-Z][a-z]+" },
    { "word-suffix", "\\b\\w+ing\\b" },
    { "unicode-words", "\\p{Lu}\\p{Ll}+" },
    { "digits", "[0-9]{2,4}" },
    { "url-host", "https?://([^/?#\\s]+)" },
    { "tld", "\\.(?:com|org|net)\\b" },
    { "email", "[\\w.+-]+@[\\w-]+\\.[\\w.-]+" },
    { "captures", "(\\w+)=(\\w*)(&|$)" },
    { "no-match", "\\x{2603}zzz" },
};
#define NPAT (sizeof PATTERNS / sizeof PATTERNS[0])
#define MAXG 4

struct item { cre2_regexp_t *re; const char *text; int len; int ng; };

static uint64_t do_find(void *ctx)
{
    struct item *it = (struct item *)ctx;
    cre2_string_t m[MAXG];
    uint64_t n = 0, total = 0;
    int pos = 0;
    while (pos <= it->len && cre2_match(it->re, it->text, it->len, pos, it->len, CRE2_UNANCHORED, m, it->ng)) {
        n++;
        for (int g = 0; g < it->ng; g++) total += (uint64_t)m[g].length;
        int end = (int)(m[0].data - it->text) + m[0].length;
        pos = m[0].length ? end : end + 1;
    }
    return (n << 32) + total;
}

int main(void)
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        size_t len;
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        char *text = (char *)vb_read_file(p, &len);
        for (size_t k = 0; k < NPAT; k++) {
            struct item *it = (struct item *)calloc(1, sizeof *it);
            cre2_options_t *opt = cre2_opt_new();
            cre2_opt_set_log_errors(opt, 0);
            it->re = cre2_new(PATTERNS[k].pattern, (int)strlen(PATTERNS[k].pattern), opt);
            cre2_opt_delete(opt);
            if (cre2_error_code(it->re)) {
                fprintf(stderr, "regex: pattern %s does not compile\n", PATTERNS[k].name);
                return 1;
            }
            it->text = text;
            it->len = (int)len;
            it->ng = cre2_num_capturing_groups(it->re) + 1;
            if (it->ng > MAXG) it->ng = MAXG;
            snprintf(cname, sizeof cname, "%s/%s", PATTERNS[k].name, names[i]);
            vb_case(cname, len, do_find, it);
        }
    }
    return vb_main();
}
