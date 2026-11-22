/* HTTP/1.1 through llhttp's API, the way Node.js drives it: every callback
 * Node uses records its span, bodies included. Linked once with llhttp and
 * once with llhttp's api.c and http.c over vhttp (feature llhttp-abi), the
 * same swap compat/llhttp/node.sh makes inside Node. The callbacks are the
 * ones Node registers (src/node_http_parser.cc); Node sets no on_method or
 * on_version, and vhttp does not call those.
 *
 * Cases http/MSG for every *.http file in $VBENCH_DATA (req-* are requests,
 * resp-* responses). One call: llhttp_init, llhttp_execute on the whole
 * message, llhttp_finish. check = spans and events * 1000003 + span bytes.
 *
 * `llhttp-run read` is the same work with the check the native comparison
 * (runners/vhttp-run) can also compute: header fields * 1000003 + the
 * bytes of the target or reason, every header name and value, and the
 * body. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "llhttp.h"
#include "runner.h"

struct spans { uint64_t n, bytes, done, fields; };

static int on_span(llhttp_t *h, const char *at, size_t len)
{
    struct spans *s = (struct spans *)h->data;
    (void)at;
    s->n++;
    s->bytes += len;
    return 0;
}
static int on_field(llhttp_t *h, const char *at, size_t len)
{
    ((struct spans *)h->data)->fields++;
    return on_span(h, at, len);
}
static int on_event(llhttp_t *h) { ((struct spans *)h->data)->n++; return 0; }
static int on_complete(llhttp_t *h) { ((struct spans *)h->data)->done++; return 0; }

static llhttp_settings_t settings;
static int read_check;

struct item { unsigned char *buf; size_t len; int response; };

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    struct spans s = {0, 0, 0, 0};
    llhttp_t p;
    llhttp_init(&p, it->response ? HTTP_RESPONSE : HTTP_REQUEST, &settings);
    p.data = &s;
    if (llhttp_execute(&p, (const char *)it->buf, it->len) != HPE_OK) abort();
    if (!s.done) abort();
    if (read_check) return s.fields * 1000003u + s.bytes;
    return s.n * 1000003u + s.bytes;
}

int main(int argc, char **argv)
{
    read_check = argc > 1 && !strcmp(argv[1], "read");
    llhttp_settings_init(&settings);
    settings.on_url = on_span;
    settings.on_status = on_span;
    settings.on_header_field = on_field;
    settings.on_header_value = on_span;
    settings.on_body = on_span;
    settings.on_headers_complete = on_event;
    settings.on_message_begin = on_event;
    settings.on_chunk_header = on_event;
    settings.on_chunk_complete = on_event;
    settings.on_message_complete = on_complete;
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        size_t l = strlen(names[i]);
        if (l < 6 || strcmp(names[i] + l - 5, ".http")) continue;
        char p[4096], cname[512];
        struct item *it = (struct item *)calloc(1, sizeof *it);
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        it->buf = vb_read_file(p, &it->len);
        it->response = !strncmp(names[i], "resp", 4);
        do_parse(it);
        names[i][l - 5] = 0;
        snprintf(cname, sizeof cname, "llhttp/%s", names[i]);
        vb_case(cname, it->len, do_parse, it);
    }
    return vb_main();
}
