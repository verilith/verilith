/* URL suite. One driver against ada's C API (ada_c.h), linked once with ada
 * and once with vurl (feature ada-abi), which exports the same functions.
 *
 * Cases parse/FILE for every *.txt in $VBENCH_DATA (one URL per line): one
 * call parses every URL, reads href of the valid ones and frees them, as
 * ada's own benchmarks do. check = valid URLs * 2^32 + total href length. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "ada_c.h"
#include "runner.h"

struct item { size_t n; const char **p; size_t *l; };

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    uint64_t ok = 0, href = 0;
    for (size_t i = 0; i < it->n; i++) {
        ada_url u = ada_parse(it->p[i], it->l[i]);
        if (ada_is_valid(u)) {
            ok++;
            href += ada_get_href(u).length;
        }
        ada_free(u);
    }
    return (ok << 32) + href;
}

int main(void)
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]), len;
        if (l < 5 || strcmp(names[i] + l - 4, ".txt")) continue;
        char p[4096], cname[512];
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        char *text = (char *)vb_read_file(p, &len);
        struct item *it = (struct item *)calloc(1, sizeof *it);
        size_t cap = 1024;
        it->p = (const char **)malloc(cap * sizeof *it->p);
        it->l = (size_t *)malloc(cap * sizeof *it->l);
        for (char *s = text; s < text + len;) {
            char *e = memchr(s, '\n', (size_t)(text + len - s));
            if (!e) e = text + len;
            size_t k = (size_t)(e - s);
            if (k && s[k - 1] == '\r') k--;
            if (k) {
                if (it->n == cap) {
                    cap *= 2;
                    it->p = (const char **)realloc(it->p, cap * sizeof *it->p);
                    it->l = (size_t *)realloc(it->l, cap * sizeof *it->l);
                }
                it->p[it->n] = s;
                it->l[it->n++] = k;
            }
            s = e + 1;
        }
        names[i][l - 4] = 0;
        snprintf(cname, sizeof cname, "parse/%s", names[i]);
        vb_case(cname, len, do_parse, it);
    }
    return vb_main();
}
