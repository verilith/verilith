/* Parses one request (or response) head with llhttp, recording the spans
 * of the URL and of each header name and value, as a server would. */
#include <string.h>
#include "llhttp.h"

struct spans { const char *p[256]; size_t n[256]; int k; };

static int on_span(llhttp_t *h, const char *at, size_t len) {
    struct spans *s = h->data;
    if (s->k < 256) { s->p[s->k] = at; s->n[s->k] = len; s->k++; }
    return 0;
}
static int on_headers_complete(llhttp_t *h) { (void)h; return HPE_PAUSED; }

static llhttp_settings_t settings;
static int ready;

int llwrap_parse(const char *buf, size_t len, int response) {
    if (!ready) {
        llhttp_settings_init(&settings);
        settings.on_url = on_span;
        settings.on_status = on_span;
        settings.on_header_field = on_span;
        settings.on_header_value = on_span;
        settings.on_headers_complete = on_headers_complete;
        ready = 1;
    }
    struct spans s; s.k = 0;
    llhttp_t p;
    llhttp_init(&p, response ? HTTP_RESPONSE : HTTP_REQUEST, &settings);
    p.data = &s;
    enum llhttp_errno e = llhttp_execute(&p, buf, len);
    if (e != HPE_PAUSED) return -1;
    return s.k;
}
