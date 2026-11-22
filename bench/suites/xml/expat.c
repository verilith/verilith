/* XML through expat's SAX API (libexpat, built here from source).
 *
 *   expat-run read    cases read/FILE: parse, with handlers for elements
 *                     and character data that visit every element, every
 *                     attribute (name and normalized value) and every run
 *                     of character data (check: counts and byte totals)
 *   expat-run check   cases check/FILE: parse with no handlers, the
 *                     well-formedness check alone (check: 1 if accepted)
 *
 * runners/vxml-run does the same two jobs through verilith-xml's own API,
 * with the same check values.
 */
#include <expat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runner.h"

struct acc { uint64_t elems, attrs, text, values; };

static void XMLCALL start(void *u, const XML_Char *name, const XML_Char **atts) {
    struct acc *a = u;
    a->elems++;
    for (; *atts; atts += 2) {
        a->attrs++;
        a->values += strlen(atts[1]);
    }
}
static void XMLCALL text(void *u, const XML_Char *s, int len) { ((struct acc *)u)->text += (uint64_t)len; }

struct item { unsigned char *buf; size_t len; };

static uint64_t do_read(void *ctx) {
    struct item *it = ctx;
    XML_Parser x = XML_ParserCreate(NULL);
    struct acc a = {0, 0, 0, 0};
    XML_SetUserData(x, &a);
    XML_SetElementHandler(x, start, NULL);
    XML_SetCharacterDataHandler(x, text);
    if (XML_Parse(x, (const char *)it->buf, (int)it->len, 1) != XML_STATUS_OK) abort();
    XML_ParserFree(x);
    return a.elems * 1000003u + a.attrs * 1009u + a.text * 31u + a.values;
}

static uint64_t do_check(void *ctx) {
    struct item *it = ctx;
    XML_Parser x = XML_ParserCreate(NULL);
    int ok = XML_Parse(x, (const char *)it->buf, (int)it->len, 1) == XML_STATUS_OK;
    XML_ParserFree(x);
    return (uint64_t)ok;
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "read";
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char *dot = strrchr(names[i], '.');
        if (!dot || (strcmp(dot, ".xml") && strcmp(dot, ".svg") && strcmp(dot, ".plist"))) continue;
        char p[4096], cname[512];
        struct item *it = calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        *dot = 0;
        int check = !strcmp(mode, "check");
        snprintf(cname, sizeof cname, "%s/%s", check ? "check" : "read", names[i]);
        vb_case(cname, it->len, check ? do_check : do_read, it);
    }
    return vb_main();
}
