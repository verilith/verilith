/* Tests of the native C API (include/vdns.h), for ASan and UBSan. */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vdns.h"

/* A response for `example.com MX`, the answer's owner name and the name in
 * its RDATA compressed, and an A record for the exchange. */
static const uint8_t RESPONSE[] = {
    0x12, 0x34, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 1,
    7, 'e', 'x', 'a', 'm', 'p', 'l', 'e', 3, 'c', 'o', 'm', 0, 0, 15, 0, 1,
    0xC0, 12, 0, 15, 0, 1, 0, 0, 0x0E, 0x10, 0, 9, 0, 10, 4, 'm', 'a', 'i', 'l', 0xC0, 12,
    0xC0, 43, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 192, 0, 2, 7,
};

/* Parses a copy of the first n bytes, in an allocation of exactly n. */
static int parse(vdns_message *m, const uint8_t *b, size_t n, vdns_error *e) {
    uint8_t *c = (uint8_t *)malloc(n ? n : 1);
    memcpy(c, b, n);
    int r = vdns_parse(m, c, n, e);
    free(c);
    return r;
}

int main(void) {
    vdns_message *m = vdns_message_new();
    vdns_question q;
    vdns_record r;
    vdns_error e;
    char text[64];

    /* The packet is freed before the message is read. */
    assert(parse(m, RESPONSE, sizeof RESPONSE, &e) == VDNS_OK && e.code == 0);
    assert(vdns_id(m) == 0x1234 && vdns_flags(m) == 0x8180);
    assert(vdns_question_count(m) == 1 && vdns_record_count(m, VDNS_ANSWER) == 1);
    assert(vdns_record_count(m, VDNS_AUTHORITY) == 0 && vdns_record_count(m, VDNS_ADDITIONAL) == 1);
    assert(vdns_record_count(m, 3) == 0 && vdns_record_count(m, -1) == 0);

    assert(vdns_get_question(m, 0, &q) && q.qtype == 15 && q.qclass == 1);
    assert(q.name_len == 13 && !memcmp(q.name, "\7example\3com", 13));
    assert(vdns_name_text(q.name, q.name_len, text, sizeof text) == 11 && !strcmp(text, "example.com"));
    assert(!vdns_get_question(m, 1, &q));

    assert(vdns_get_record(m, VDNS_ANSWER, 0, &r) && r.rtype == 15 && r.rclass == 1 && r.ttl == 3600);
    assert(r.name_len == 13 && !memcmp(r.name, "\7example\3com", 13));
    /* The exchange is uncompressed: the RDATA decodes on its own. */
    assert(r.rdata_len == 2 + 18 && r.rdata[0] == 0 && r.rdata[1] == 10);
    assert(vdns_name_text(r.rdata + 2, r.rdata_len - 2, text, sizeof text) == 16 && !strcmp(text, "mail.example.com"));
    assert(!vdns_get_record(m, VDNS_ANSWER, 1, &r) && !vdns_get_record(m, VDNS_AUTHORITY, 0, &r) && !vdns_get_record(m, 7, 0, &r));
    assert(vdns_get_record(m, VDNS_ADDITIONAL, 0, &r) && r.rtype == 1 && r.ttl == 60);
    assert(r.rdata_len == 4 && !memcmp(r.rdata, "\xC0\x00\x02\x07", 4));
    assert(vdns_name_text(r.name, r.name_len, text, sizeof text) == 16 && !strcmp(text, "mail.example.com"));

    /* Text that does not fit is cut, and still NUL-terminated. */
    memset(text, 'x', sizeof text);
    assert(vdns_name_text(r.name, r.name_len, text, 5) == 16 && !strcmp(text, "mail"));
    assert(vdns_name_text(r.name, r.name_len, NULL, 0) == 16);
    assert(vdns_name_text((const uint8_t *)"", 1, text, sizeof text) == 0 && text[0] == 0);

    /* Every truncation is rejected, and leaves an empty message. */
    for (size_t n = 0; n < sizeof RESPONSE; n++) {
        int rc = parse(m, RESPONSE, n, &e);
        assert(rc == (n < 12 ? VDNS_E_SHORT_HEADER : VDNS_E_TRUNCATED) && e.code == rc && e.offset <= n);
        assert(vdns_question_count(m) == 0 && vdns_record_count(m, VDNS_ANSWER) == 0 && !vdns_get_question(m, 0, &q));
    }

    /* A pointer loop in the answer's owner name, and trailing bytes. */
    uint8_t bad[sizeof RESPONSE + 1];
    memcpy(bad, RESPONSE, sizeof RESPONSE);
    bad[30] = 29;
    assert(parse(m, bad, sizeof RESPONSE, &e) == VDNS_E_POINTER_NOT_PRIOR);
    assert(e.part == VDNS_PART_ANSWER && e.index == 0 && e.offset == 29);
    memcpy(bad, RESPONSE, sizeof RESPONSE);
    bad[sizeof RESPONSE] = 0;
    assert(parse(m, bad, sizeof bad, &e) == VDNS_E_TRAILING_BYTES && e.part == VDNS_PART_END);
    assert(vdns_parse(NULL, RESPONSE, sizeof RESPONSE, &e) == VDNS_E_ARGUMENT);
    assert(vdns_parse(m, NULL, 4, NULL) == VDNS_E_ARGUMENT);
    assert(vdns_parse(m, NULL, 0, NULL) == VDNS_E_SHORT_HEADER);

    /* The message is reusable. */
    assert(parse(m, RESPONSE, sizeof RESPONSE, NULL) == VDNS_OK && vdns_get_record(m, VDNS_ANSWER, 0, &r));

    /* A query, and its parse. */
    uint8_t out[64];
    size_t len = 0;
    assert(vdns_write_query(0xBEEF, 0x0100, "www.Example.com.", 16, 28, 1, out, sizeof out, &len) == VDNS_OK);
    assert(len == 12 + 17 + 4 && out[0] == 0xBE && out[1] == 0xEF && out[2] == 1 && out[5] == 1);
    assert(parse(m, out, len, &e) == VDNS_OK && vdns_id(m) == 0xBEEF && vdns_flags(m) == 0x0100);
    assert(vdns_get_question(m, 0, &q) && q.qtype == 28 && q.name_len == 17 && !memcmp(q.name, "\3www\7Example\3com", 17));
    size_t need = 0;
    assert(vdns_write_query(1, 0, "a.b", 3, 1, 1, out, 10, &need) == VDNS_E_SPACE && need == 12 + 5 + 4);
    assert(vdns_write_query(1, 0, "a..b", 4, 1, 1, out, sizeof out, &len) == VDNS_E_NAME);
    assert(vdns_write_query(1, 0, NULL, 3, 1, 1, out, sizeof out, &len) == VDNS_E_ARGUMENT);
    assert(vdns_write_query(1, 0, "", 0, 2, 1, out, sizeof out, &len) == VDNS_OK && len == 17);

    /* Null messages read as empty. */
    assert(vdns_id(NULL) == 0 && vdns_question_count(NULL) == 0 && !vdns_get_record(NULL, 0, 0, &r));
    vdns_message_free(m);
    vdns_message_free(NULL);
    puts("native C API: ok");
    return 0;
}
