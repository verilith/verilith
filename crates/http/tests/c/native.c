/* Tests of the native C API (include/vhttp.h), for ASan and UBSan. */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vhttp.h"

#define IS(buf, span, lit) (vhttp_len(span) == sizeof(lit) - 1 && !memcmp(VHTTP_STR(buf, span), lit, sizeof(lit) - 1))

/* Parses a copy of s in an allocation of exactly its size. */
static int request(const char *s, size_t len, vhttp_header *h, size_t *n, vhttp_request *r) {
    char *b = (char *)malloc(len ? len : 1);
    memcpy(b, s, len);
    int rc = vhttp_parse_request(b, len, 0, h, n, r);
    free(b);
    return rc;
}

static int req(const char *s, vhttp_request *r) {
    vhttp_header h[16];
    size_t n = 16;
    return request(s, strlen(s), h, &n, r);
}

int main(void) {
    vhttp_header h[16];
    vhttp_request r;
    vhttp_response p;
    size_t n;

    static const char get[] =
        "GET /index.html?x=1 HTTP/1.1\r\nHost: example.com\r\nAccept:  */* \r\nX-Empty:\r\n\r\nBODY";
    n = 16;
    assert(vhttp_parse_request(get, sizeof get - 1, 0, h, &n, &r) == VHTTP_OK);
    assert(n == 3 && IS(get, r.method, "GET") && IS(get, r.target, "/index.html?x=1") && r.minor_version == 1);
    assert(IS(get, h[0].name, "Host") && IS(get, h[0].value, "example.com"));
    assert(IS(get, h[1].name, "Accept") && IS(get, h[1].value, "*/*"));
    assert(IS(get, h[2].name, "X-Empty") && vhttp_len(h[2].value) == 0);
    assert(r.body == VHTTP_BODY_EMPTY && !memcmp(get + r.head_len, "BODY", 4));

    /* Every proper prefix of the head is partial, with and without last_len. */
    size_t head = r.head_len, last = 0;
    for (size_t i = 0; i < head; i++) {
        n = 16;
        assert(request(get, i, h, &n, &r) == VHTTP_PARTIAL && n == 0);
        char *b = (char *)malloc(i ? i : 1);
        memcpy(b, get, i);
        n = 16;
        assert(vhttp_parse_request(b, i, last, h, &n, &r) == VHTTP_PARTIAL);
        free(b);
        last = i;
    }
    n = 16;
    assert(vhttp_parse_request(get, head, last, h, &n, &r) == VHTTP_OK && n == 3 && r.head_len == head);

    /* Framing. */
    assert(req("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 12\r\n\r\n", &r) == VHTTP_OK);
    assert(r.body == VHTTP_BODY_LENGTH && r.content_length == 12);
    assert(req("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n", &r) == VHTTP_OK);
    assert(r.body == VHTTP_BODY_CHUNKED);
    int rc = req("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n", &r);
    assert(rc == VHTTP_E_CONTENT_LENGTH_AND_TRANSFER_ENCODING && vhttp_error_is_framing(rc));
    rc = req("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\nContent-Length: 7\r\n\r\n", &r);
    assert(rc == VHTTP_E_CONTENT_LENGTH && vhttp_error_is_framing(rc));
    rc = req("GET / HTTP/1.1\r\n\r\n", &r);
    assert(rc == VHTTP_E_HOST && strstr(vhttp_error_message(rc), "Host"));
    assert(req("POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n", &r) == VHTTP_E_TRANSFER_ENCODING_HTTP10);

    /* Grammar. */
    rc = req("GET / HTTP/1.1\nHost: a\n\n", &r);
    assert(rc == VHTTP_E_NEWLINE && !vhttp_error_is_framing(rc));
    assert(req("GET / HTTP/1.1\r\nHost : a\r\n\r\n", &r) == VHTTP_E_HEADER_NAME);
    assert(req("GET / HTTP/1.1\r\nHost: a\r\n folded\r\n\r\n", &r) == VHTTP_E_HEADER_NAME);
    assert(req("GET  / HTTP/1.1\r\nHost: a\r\n\r\n", &r) == VHTTP_E_TARGET);
    assert(req("GET / HTTP/2.0\r\nHost: a\r\n\r\n", &r) == VHTTP_E_VERSION);
    assert(req("G(T / HTTP/1.1\r\nHost: a\r\n\r\n", &r) == VHTTP_E_METHOD);
    assert(req("GET / HTTP/1.1\r\nHost: a\r\nX: a\x01" "b\r\n\r\n", &r) == VHTTP_E_HEADER_VALUE);

    /* The header array's capacity is the limit. */
    n = 2;
    assert(vhttp_parse_request(get, sizeof get - 1, 0, h, &n, &r) == VHTTP_E_TOO_MANY_HEADERS && n == 0);
    n = 3;
    assert(vhttp_parse_request(get, sizeof get - 1, 0, h, &n, NULL) == VHTTP_OK && n == 3);

    /* Arguments. */
    n = 1;
    assert(vhttp_parse_request(NULL, 4, 0, h, &n, &r) == VHTTP_E_ARGUMENT);
    assert(vhttp_parse_request(get, 4, 0, NULL, &n, &r) == VHTTP_E_ARGUMENT);
    assert(vhttp_parse_request(get, 4, 0, h, NULL, &r) == VHTTP_E_ARGUMENT);
    n = 0;
    assert(vhttp_parse_request(NULL, 0, 0, NULL, &n, &r) == VHTTP_PARTIAL);

    /* Responses. */
    static const char ok[] = "HTTP/1.1 200 OK\r\nContent-Length: 5\r\nServer: x\r\n\r\nhello";
    n = 16;
    assert(vhttp_parse_response(ok, sizeof ok - 1, false, false, h, &n, &p) == VHTTP_OK);
    assert(n == 2 && p.status == 200 && p.minor_version == 1 && IS(ok, p.reason, "OK"));
    assert(p.body == VHTTP_BODY_LENGTH && p.content_length == 5 && !memcmp(ok + p.head_len, "hello", 5));
    assert(IS(ok, h[1].name, "Server") && IS(ok, h[1].value, "x"));
    n = 16; /* The response to a HEAD has no body. */
    assert(vhttp_parse_response(ok, sizeof ok - 1, true, false, h, &n, &p) == VHTTP_OK && p.body == VHTTP_BODY_EMPTY);
    static const char close[] = "HTTP/1.0 404 \r\n\r\n";
    n = 16;
    assert(vhttp_parse_response(close, sizeof close - 1, false, false, h, &n, &p) == VHTTP_OK);
    assert(n == 0 && p.status == 404 && vhttp_len(p.reason) == 0 && p.body == VHTTP_BODY_CLOSE);
    n = 1;
    assert(vhttp_parse_response(ok, sizeof ok - 1, false, false, h, &n, &p) == VHTTP_E_TOO_MANY_HEADERS && n == 0);
    n = 16;
    assert(vhttp_parse_response(ok, 20, false, false, h, &n, &p) == VHTTP_PARTIAL);
    n = 16;
    assert(vhttp_parse_response("HTTP/1.1 20 OK\r\n\r\n", 18, false, false, h, &n, &p) == VHTTP_E_STATUS);

    /* The chunked decoder: whole, and split at every position. */
    static const char body[] = "4\r\nWiki\r\n6;ext=1\r\npedia \r\nA\r\nin chunks.\r\n0\r\nX-T: 1\r\n\r\nNEXT";
    const size_t blen = sizeof body - 1;
    for (size_t cut = 0; cut <= blen; cut++) {
        vhttp_chunked d;
        memset(&d, 0, sizeof d);
        char *a = (char *)malloc(cut ? cut : 1), *b = (char *)malloc(blen - cut ? blen - cut : 1);
        memcpy(a, body, cut);
        memcpy(b, body + cut, blen - cut);
        char out[64];
        size_t o = 0, got = 0, rest = 99;
        rc = vhttp_chunked_decode(&d, a, cut, &got, &rest);
        memcpy(out, a, got);
        o = got;
        if (rc == VHTTP_PARTIAL) {
            /* "4\r\nWiki": inside the data after 3 to 6 bytes. */
            if (cut < 9) assert(vhttp_chunked_in_data(&d) == (cut >= 3 && cut < 7));
            rc = vhttp_chunked_decode(&d, b, blen - cut, &got, &rest);
            memcpy(out + o, b, got);
            o += got;
            assert(rc == VHTTP_OK && rest == 4 && !memcmp(b + got, "NEXT", 4));
        } else {
            assert(rc == VHTTP_OK && cut >= blen - 4 && rest == cut - (blen - 4));
        }
        assert(o == 20 && !memcmp(out, "Wikipedia in chunks.", 20));
        free(a);
        free(b);
    }
    {
        /* Keeping the trailer section. */
        vhttp_chunked d;
        memset(&d, 0, sizeof d);
        d.keep_trailers = true;
        char b[sizeof body];
        memcpy(b, body, blen);
        size_t got, rest;
        assert(vhttp_chunked_decode(&d, b, blen, &got, &rest) == VHTTP_OK && got == 20);
        assert(rest == 14 && !memcmp(b + got, "X-T: 1\r\n\r\nNEXT", 14));
        /* Malformed bodies, and a decoder that was never zeroed. */
        memset(&d, 0, sizeof d);
        char bad[] = "4\r\nWikiX\r\n";
        assert(vhttp_chunked_decode(&d, bad, sizeof bad - 1, &got, &rest) == VHTTP_E_CHUNKED);
        memset(&d, 0, sizeof d);
        char neg[] = "-1\r\n";
        assert(vhttp_chunked_decode(&d, neg, sizeof neg - 1, &got, &rest) == VHTTP_E_CHUNKED);
        memset(&d, 0xEE, sizeof d);
        assert(vhttp_chunked_decode(&d, bad, 1, &got, &rest) == VHTTP_E_ARGUMENT && !vhttp_chunked_in_data(&d));
        assert(vhttp_chunked_decode(NULL, bad, 1, &got, &rest) == VHTTP_E_ARGUMENT && !vhttp_chunked_in_data(NULL));
    }
    puts("native C API: ok");
    return 0;
}
