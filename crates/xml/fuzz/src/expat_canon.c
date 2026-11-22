/* A document through expat's SAX API, written in James Clark's canonical
 * form (as tests/canonical.rs writes verilith-xml's): elements with their
 * attributes sorted, character data and PIs, no comments. */
#include <expat.h>
#include <stdlib.h>
#include <string.h>

struct buf { char *p; size_t n, cap; int in_dtd; };

static void put(struct buf *b, const char *s, size_t n) {
    if (b->n + n > b->cap) {
        b->cap = (b->n + n) * 2 + 64;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n);
    b->n += n;
}
static void puts0(struct buf *b, const char *s) { put(b, s, strlen(s)); }

static void esc(struct buf *b, const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) {
        switch (s[i]) {
        case '&': puts0(b, "&amp;"); break;
        case '<': puts0(b, "&lt;"); break;
        case '>': puts0(b, "&gt;"); break;
        case '"': puts0(b, "&quot;"); break;
        case '\t': puts0(b, "&#9;"); break;
        case '\n': puts0(b, "&#10;"); break;
        case '\r': puts0(b, "&#13;"); break;
        default: put(b, s + i, 1);
        }
    }
}

static int cmp(const void *a, const void *b) {
    return strcmp(*(const char *const *)a, *(const char *const *)b);
}

static void XMLCALL start(void *u, const XML_Char *name, const XML_Char **atts) {
    struct buf *b = u;
    size_t n = 0;
    while (atts[2 * n]) n++;
    const char **pairs = malloc((n + 1) * 2 * sizeof *pairs);
    memcpy(pairs, atts, n * 2 * sizeof *pairs);
    qsort(pairs, n, 2 * sizeof *pairs, cmp);
    puts0(b, "<");
    puts0(b, name);
    for (size_t i = 0; i < n; i++) {
        puts0(b, " ");
        puts0(b, pairs[2 * i]);
        puts0(b, "=\"");
        esc(b, pairs[2 * i + 1], strlen(pairs[2 * i + 1]));
        puts0(b, "\"");
    }
    puts0(b, ">");
    free(pairs);
}
static void XMLCALL end(void *u, const XML_Char *name) {
    struct buf *b = u;
    puts0(b, "</");
    puts0(b, name);
    puts0(b, ">");
}
static void XMLCALL text(void *u, const XML_Char *s, int len) { esc(u, s, (size_t)len); }
static void XMLCALL pi(void *u, const XML_Char *t, const XML_Char *d) {
    struct buf *b = u;
    puts0(b, "<?");
    puts0(b, t);
    puts0(b, " ");
    puts0(b, d);
    puts0(b, "?>");
}

/* 1 and the canonical form in *out (malloc'd), or 0 if expat rejects,
 * with its error code in *code. */
int expat_canon(const char *p, size_t n, char **out, size_t *outn, int *code) {
    XML_Parser x = XML_ParserCreate(NULL);
    struct buf b = {0, 0, 0, 0};
    XML_SetUserData(x, &b);
    XML_SetElementHandler(x, start, end);
    XML_SetCharacterDataHandler(x, text);
    XML_SetProcessingInstructionHandler(x, pi);
    int ok = XML_Parse(x, p, (int)n, 1) == XML_STATUS_OK;
    *code = (int)XML_GetErrorCode(x);
    XML_ParserFree(x);
    if (!ok) {
        free(b.p);
        return 0;
    }
    *out = b.p;
    *outn = b.n;
    return 1;
}

const char *expat_error(int code) { return (const char *)XML_ErrorString((enum XML_Error)code); }
