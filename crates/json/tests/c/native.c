/* Tests of the native C API (include/vjson.h).
 *
 * With no arguments, runs the checks below. With file arguments, parses each
 * file, reads every value in it, and prints "ACCEPT <file>" or
 * "REJECT <file>" (for JSONTestSuite, under ASan and UBSan). */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vjson.h"

static size_t walk(vjson_value v) {
    size_t n = 1, len;
    const char *s;
    double d;
    vjson_iter it;
    vjson_value e;
    switch (vjson_type(v)) {
    case VJSON_ARRAY:
        assert(vjson_array_iter(v, &it));
        while (vjson_array_next(&it, &e)) n += walk(e);
        break;
    case VJSON_OBJECT:
        assert(vjson_object_iter(v, &it));
        while (vjson_object_next(&it, &s, &len, &e)) {
            for (size_t i = 0; i < len; i++) n += (unsigned char)s[i] == 0xFF;
            n += walk(e);
        }
        break;
    case VJSON_STRING:
        assert(vjson_get_string(v, &s, &len));
        for (size_t i = 0; i < len; i++) n += (unsigned char)s[i] == 0xFF;
        break;
    case VJSON_NUMBER:
        assert(vjson_get_double(v, &d));
        assert(vjson_get_number_text(v, &s, &len) && len > 0);
        break;
    case VJSON_BOOL:
    case VJSON_NULL:
        break;
    default:
        assert(!"invalid value in a parsed document");
    }
    return n;
}

#define STR(v, lit) (vjson_get_string(v, &s, &len) && len == sizeof(lit) - 1 && !memcmp(s, lit, len))

static void checks(void) {
    vjson_parser *p = vjson_parser_new();
    vjson_value root, v, e;
    vjson_error err;
    vjson_iter it;
    const char *s;
    size_t len;
    double d;
    int64_t i;
    bool b;

    static const char doc[] =
        "{\"name\": \"vjson\", \"esc\": \"a\\n\\u00e9\\u0000b\", \"n\": -12, \"x\": 1.5e3,"
        " \"t\": true, \"z\": null, \"k\\\"ey\": [1, [2, 3], {\"a\": []}], \"name\": 2}";
    assert(vjson_parse(p, doc, sizeof doc - 1, &root, &err) == VJSON_OK);
    assert(err.code == 0 && vjson_type(root) == VJSON_OBJECT);
    assert(vjson_length(root, &len) && len == 8);

    /* The first of two members with the same name. */
    assert(vjson_object_get(root, "name", 4, &v) && STR(v, "vjson"));
    assert(vjson_object_get(root, "esc", 3, &v) && STR(v, "a\n\xc3\xa9\0b"));
    assert(vjson_object_get(root, "n", 1, &v) && vjson_get_int64(v, &i) && i == -12);
    assert(vjson_get_double(v, &d) && d == -12.0);
    assert(vjson_object_get(root, "x", 1, &v) && vjson_get_double(v, &d) && d == 1500.0);
    assert(!vjson_get_int64(v, &i));
    assert(vjson_get_number_text(v, &s, &len) && len == 5 && !memcmp(s, "1.5e3", 5));
    assert(vjson_object_get(root, "t", 1, &v) && vjson_get_bool(v, &b) && b);
    assert(vjson_object_get(root, "z", 1, &v) && vjson_is_null(v) && vjson_type(v) == VJSON_NULL);
    assert(!vjson_object_get(root, "missing", 7, &v));

    /* Wrong-type getters fail and leave the out-parameter alone. */
    d = 7;
    assert(!vjson_get_double(root, &d) && d == 7);
    assert(!vjson_get_string(root, &s, &len) && !vjson_get_bool(root, &b));
    assert(!vjson_array_iter(root, &it) && !vjson_array_at(root, 0, &v));

    /* An escaped key, and nested containers. */
    assert(vjson_object_get(root, "k\"ey", 4, &v) && vjson_type(v) == VJSON_ARRAY);
    assert(vjson_length(v, &len) && len == 3);
    assert(vjson_array_at(v, 1, &e) && vjson_length(e, &len) && len == 2);
    assert(vjson_array_at(v, 2, &e) && vjson_type(e) == VJSON_OBJECT);
    assert(!vjson_array_at(v, 3, &e));
    assert(vjson_array_iter(v, &it));
    assert(vjson_array_next(&it, &e) && vjson_get_int64(e, &i) && i == 1);
    assert(vjson_array_next(&it, &e) && vjson_type(e) == VJSON_ARRAY);
    assert(vjson_array_next(&it, &e) && vjson_type(e) == VJSON_OBJECT);
    assert(!vjson_array_next(&it, &e) && !vjson_array_next(&it, &e));

    /* Members in order, duplicates included. */
    size_t members = 0;
    assert(vjson_object_iter(root, &it));
    while (vjson_object_next(&it, &s, &len, &e)) {
        if (members == 6) assert(len == 4 && !memcmp(s, "k\"ey", 4));
        if (members == 7) assert(len == 4 && !memcmp(s, "name", 4) && vjson_get_int64(e, &i) && i == 2);
        members++;
    }
    assert(members == 8);
    assert(walk(root) == 15);

    /* Errors. */
    static const char bad[] = "[1,\n  2,, 3]";
    assert(vjson_parse(p, bad, sizeof bad - 1, &root, &err) == VJSON_E_UNEXPECTED_BYTE);
    assert(err.code == VJSON_E_UNEXPECTED_BYTE && err.byte == ',' && err.offset == 8 && err.line == 2 &&
           err.column == 5);
    assert(vjson_type(root) == VJSON_INVALID && !vjson_get_double(root, &d));
    assert(strstr(vjson_error_message(err.code), "unexpected"));
    assert(vjson_parse(p, "", 0, &root, NULL) == VJSON_E_UNEXPECTED_END);
    assert(vjson_parse(p, NULL, 0, NULL, NULL) == VJSON_E_UNEXPECTED_END);
    assert(vjson_parse(p, "[1] x", 5, NULL, NULL) == VJSON_E_TRAILING_DATA);
    assert(vjson_parse(NULL, "1", 1, &root, &err) == VJSON_E_ARGUMENT);
    assert(vjson_parse(p, NULL, 3, &root, &err) == VJSON_E_ARGUMENT);

    /* Zeroed values and iterators are invalid, not undefined. */
    memset(&v, 0, sizeof v);
    memset(&it, 0, sizeof it);
    assert(vjson_type(v) == VJSON_INVALID && !vjson_is_null(v) && !vjson_array_next(&it, &e));
    assert(!vjson_object_next(&it, &s, &len, &e) && !vjson_length(v, &len));

    /* The parser is reusable, and a value of the old document is invalid
     * or names a value of the new one, never freed memory. */
    assert(vjson_parse(p, "[10, 20]", 8, &root, &err) == VJSON_OK);
    assert(vjson_array_at(root, 1, &v) && vjson_get_int64(v, &i) && i == 20);
    assert(vjson_parse(p, "3", 1, &root, &err) == VJSON_OK);
    assert(vjson_type(v) == VJSON_INVALID);
    assert(vjson_get_int64(root, &i) && i == 3);

    vjson_parser_free(p);
    vjson_parser_free(NULL);
    puts("native C API: ok");
}

int main(int argc, char **argv) {
    if (argc == 1) {
        checks();
        return 0;
    }
    vjson_parser *p = vjson_parser_new();
    for (int a = 1; a < argc; a++) {
        FILE *f = fopen(argv[a], "rb");
        if (!f) { perror(argv[a]); return 2; }
        fseek(f, 0, SEEK_END);
        long n = ftell(f);
        fseek(f, 0, SEEK_SET);
        /* Exactly n bytes, so that ASan sees any read past the input. */
        char *buf = malloc(n ? n : 1);
        if (fread(buf, 1, n, f) != (size_t)n) { return 2; }
        fclose(f);
        vjson_value root;
        vjson_error err;
        int r = vjson_parse(p, buf, n, &root, &err);
        if (r == VJSON_OK) walk(root); else assert(err.code == r && err.offset <= (size_t)n);
        printf("%s %s\n", r == VJSON_OK ? "ACCEPT" : "REJECT", argv[a]);
        free(buf);
    }
    vjson_parser_free(p);
    return 0;
}
