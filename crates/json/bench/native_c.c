/* The native C API side of the like-for-like benchmark: for each file,
 * MB/s to parse and then read every value (every number as a double, every
 * string and key decoded), with one reused parser. The same work as the
 * second column of examples/like_for_like.rs, through include/vjson.h.
 *
 *   cargo build --release --features capi
 *   cc -O3 -Iinclude bench/native_c.c target/release/libverilith_json.a -lm -lpthread -ldl -o native_c
 */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "vjson.h"

typedef struct { double sum; size_t bytes; } acc;

static void walk(vjson_value v, int type, acc *a) {
    vjson_iter it;
    vjson_value e;
    const char *s;
    size_t len;
    double d;
    int t;
    switch (type) {
    case VJSON_ARRAY:
        vjson_array_iter(v, &it);
        while ((t = vjson_array_next(&it, &e))) walk(e, t, a);
        break;
    case VJSON_OBJECT:
        vjson_object_iter(v, &it);
        while ((t = vjson_object_next(&it, &s, &len, &e))) {
            a->bytes += len;
            walk(e, t, a);
        }
        break;
    case VJSON_NUMBER:
        vjson_get_double(v, &d);
        a->sum += d;
        break;
    case VJSON_STRING:
        vjson_get_string(v, &s, &len);
        a->bytes += len;
        break;
    default:
        break;
    }
}

static double now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
    vjson_parser *p = vjson_parser_new();
    for (int i = 1; i < argc; i++) {
        FILE *f = fopen(argv[i], "rb");
        if (!f) { perror(argv[i]); return 2; }
        fseek(f, 0, SEEK_END);
        size_t n = ftell(f);
        fseek(f, 0, SEEK_SET);
        char *buf = malloc(n ? n : 1);
        if (fread(buf, 1, n, f) != n) return 2;
        fclose(f);
        size_t reps = 2000000 / (n ? n : 1), keep = 0;
        if (reps == 0) reps = 1;
        double best = 1e30;
        for (int round = 0; round < 200; round++) {
            double t = now();
            for (size_t r = 0; r < reps; r++) {
                vjson_value root;
                if (vjson_parse(p, buf, n, &root, NULL) != VJSON_OK) return 1;
                acc a = {0, 0};
                walk(root, vjson_type(root), &a);
                keep += a.bytes + (a.sum != 0);
            }
            double dt = (now() - t) / reps;
            if (dt < best) best = dt;
        }
        printf("%s %.0f %zu\n", argv[i], n / 1e6 / best, keep % 7);
        free(buf);
    }
    vjson_parser_free(p);
    return 0;
}
