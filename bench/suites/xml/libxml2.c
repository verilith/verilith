/* XML through libxml2's SAX2 API (libxml2, built here from source).
 *
 *   libxml2-run read    cases read/FILE: parse, with handlers for elements
 *                       and character data that visit every element, every
 *                       attribute (name and normalized value) and every run
 *                       of character data (check: counts and byte totals)
 *   libxml2-run check   cases check/FILE: parse with no content handlers,
 *                       the well-formedness check alone (check: 1 if
 *                       accepted)
 *
 * The jobs and check values of expat.c. libxml2 keeps the internal subset's
 * declarations through its default SAX2 handlers (xmlSAXVersion), which is
 * how a SAX caller gets entities expanded and attribute defaults supplied:
 * with no DTD handlers it would take a reference to a declared entity for an
 * undeclared one. Only the content handlers below are ours. Options for read:
 * entities substituted (as expat reports them) and DTD defaults added; for
 * check, neither, which libxml2 checks faster (a replacement text is still
 * checked where it is referenced); for both, nothing external loaded. One
 * parser context is reused from call to call, as libxml2's xmlCtxtReadMemory
 * allows. SAX2 also processes namespaces, which neither
 * expat (as used here) nor verilith-xml does: a namespace declaration is
 * counted as the attribute it is written as.
 */
#include <libxml/parser.h>
#include <libxml/SAX2.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runner.h"

struct acc { uint64_t elems, attrs, text, values; };

static struct acc *acc_of(void *ctx) { return ((xmlParserCtxtPtr)ctx)->_private; }

static void start(void *ctx, const xmlChar *local, const xmlChar *prefix, const xmlChar *uri,
                  int nb_ns, const xmlChar **ns, int nb_attrs, int nb_defaulted, const xmlChar **atts) {
    struct acc *a = acc_of(ctx);
    (void)local; (void)prefix; (void)uri; (void)nb_defaulted;
    a->elems++;
    /* (prefix, URI) pairs: xmlns and xmlns:p attributes. */
    for (int i = 0; i < nb_ns; i++) {
        a->attrs++;
        if (ns[2 * i + 1]) a->values += strlen((const char *)ns[2 * i + 1]);
    }
    /* (localname, prefix, URI, value, end) quintuples, defaults included. */
    for (int i = 0; i < nb_attrs; i++) {
        a->attrs++;
        a->values += (uint64_t)(atts[5 * i + 4] - atts[5 * i + 3]);
    }
}
static void text(void *ctx, const xmlChar *s, int len) { (void)s; acc_of(ctx)->text += (uint64_t)len; }

struct item { unsigned char *buf; size_t len; xmlParserCtxtPtr ctxt; };

static const int OPTS_READ = XML_PARSE_NOENT | XML_PARSE_DTDATTR | XML_PARSE_NO_XXE | XML_PARSE_NOERROR |
                             XML_PARSE_NOWARNING;
static const int OPTS_CHECK = XML_PARSE_NO_XXE | XML_PARSE_NOERROR | XML_PARSE_NOWARNING;

static uint64_t do_read(void *p) {
    struct item *it = p;
    struct acc a = {0, 0, 0, 0};
    it->ctxt->_private = &a;
    xmlDocPtr d = xmlCtxtReadMemory(it->ctxt, (const char *)it->buf, (int)it->len, NULL, NULL, OPTS_READ);
    if (d == NULL || (xmlCtxtGetStatus(it->ctxt) & XML_STATUS_NOT_WELL_FORMED)) abort();
    xmlFreeDoc(d);
    return a.elems * 1000003u + a.attrs * 1009u + a.text * 31u + a.values;
}

static uint64_t do_check(void *p) {
    struct item *it = p;
    xmlDocPtr d = xmlCtxtReadMemory(it->ctxt, (const char *)it->buf, (int)it->len, NULL, NULL, OPTS_CHECK);
    int ok = !(xmlCtxtGetStatus(it->ctxt) & XML_STATUS_NOT_WELL_FORMED);
    xmlFreeDoc(d);
    return (uint64_t)ok;
}

/* libxml2's SAX2 handlers for the prolog and the DTD; ours, or none, for content. */
static xmlSAXHandler handlers(int read) {
    xmlSAXHandler h;
    xmlSAXVersion(&h, 2);
    h.startElementNs = read ? start : NULL;
    h.endElementNs = NULL;
    /* xmlSAXVersion also sets the SAX1 element handlers, which build a tree;
     * with them set and the SAX2 ones not, libxml2 would parse as SAX1. */
    h.startElement = NULL;
    h.endElement = NULL;
    h.characters = read ? text : NULL;
    h.cdataBlock = read ? text : NULL;
    h.ignorableWhitespace = read ? text : NULL;
    h.comment = NULL;
    h.processingInstruction = NULL;
    h.reference = NULL;
    return h;
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "read";
    int check = !strcmp(mode, "check");
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    xmlSAXHandler h = handlers(!check);
    for (size_t i = 0; i < n; i++) {
        char *dot = strrchr(names[i], '.');
        if (!dot || (strcmp(dot, ".xml") && strcmp(dot, ".svg") && strcmp(dot, ".plist"))) continue;
        char p[4096], cname[512];
        struct item *it = calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        it->ctxt = xmlNewSAXParserCtxt(&h, NULL);
        if (it->ctxt == NULL) abort();
        *dot = 0;
        snprintf(cname, sizeof cname, "%s/%s", check ? "check" : "read", names[i]);
        vb_case(cname, it->len, check ? do_check : do_read, it);
    }
    return vb_main();
}
