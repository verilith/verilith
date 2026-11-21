/* JSON through cJSON's API, linked once with cJSON and once with vjson's
 * cJSON ABI (feature cjson), which embedded C code would relink against.
 *
 *   cjson-run parse   cases cjson-parse/FILE: cJSON_ParseWithLength, then
 *                     visit every value (numbers as double, string and key
 *                     lengths), then cJSON_Delete
 *   cjson-run print   cases cjson-print/FILE: cJSON_PrintUnformatted of the
 *                     parsed document, then free (check = output length;
 *                     number formatting may differ, so lengths may too)
 *
 * cjson-parse is also the task of the native comparison: runners/vjson-run
 * does the same job through vjson's own API, with the same check.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cJSON.h"
#include "runner.h"

struct acc { double sum; uint64_t bytes, nums; };

static void walk(const cJSON *v, struct acc *a)
{
    for (; v; v = v->next) {
        if (v->string) a->bytes += strlen(v->string);
        if (cJSON_IsNumber(v)) { a->sum += v->valuedouble; a->nums++; }
        else if (cJSON_IsString(v)) a->bytes += strlen(v->valuestring);
        else if (cJSON_IsArray(v) || cJSON_IsObject(v)) walk(v->child, a);
    }
}

struct item { char *buf; size_t len; cJSON *doc; };

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    cJSON *d = cJSON_ParseWithLength(it->buf, it->len);
    if (!d) abort();
    struct acc a = {0, 0, 0};
    walk(d, &a);
    cJSON_Delete(d);
    return a.bytes * 1000003u + a.nums;
}

static uint64_t do_print(void *ctx)
{
    struct item *it = (struct item *)ctx;
    char *s = cJSON_PrintUnformatted(it->doc);
    if (!s) abort();
    uint64_t n = strlen(s);
    cJSON_free(s);
    return n;
}

int main(int argc, char **argv)
{
    const char *mode = argc > 1 ? argv[1] : "parse";
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 6 || strcmp(names[i] + l - 5, ".json")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = (char *)vb_read_file(p, &it->len);
        it->doc = cJSON_ParseWithLength(it->buf, it->len);
        if (!it->doc) { fprintf(stderr, "cJSON rejects %s\n", names[i]); return 1; }
        names[i][l - 5] = 0;
        if (!strcmp(mode, "print")) {
            snprintf(cname, sizeof cname, "cjson-print/%s", names[i]);
            vb_case(cname, it->len, do_print, it);
        } else {
            snprintf(cname, sizeof cname, "cjson-parse/%s", names[i]);
            vb_case(cname, it->len, do_parse, it);
        }
    }
    return vb_main();
}
