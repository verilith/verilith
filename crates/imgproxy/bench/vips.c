// The same job on libvips (imgproxy's engine), one thread:
//   thumbnail: vips_thumbnail_buffer (shrink-on-load for JPEG and WebP,
//              as imgproxy does) then pngsave at compression 6.
//   resize:    load at full size, vips_resize (lanczos3), pngsave.
//   vips-bench MODE WIDTH HEIGHT ROUNDS FILE...
#include <vips/vips.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
static int cmp(const void *a, const void *b) { double x = *(double *)a, y = *(double *)b; return x < y ? -1 : x > y; }

static size_t once(const char *mode, void *buf, size_t len, int w, int h) {
    VipsImage *out = NULL;
    if (!strcmp(mode, "thumbnail")) {
        if (vips_thumbnail_buffer(buf, len, &out, w, "height", h, NULL)) vips_error_exit(NULL);
    } else {
        VipsImage *in = vips_image_new_from_buffer(buf, len, "", "access", VIPS_ACCESS_SEQUENTIAL, NULL);
        if (!in) vips_error_exit(NULL);
        double s = (double)w / in->Xsize, t = (double)h / in->Ysize;
        if (t < s) s = t;
        if (vips_resize(in, &out, s, NULL)) vips_error_exit(NULL);
        g_object_unref(in);
    }
    void *png; size_t n;
    if (vips_pngsave_buffer(out, &png, &n, "compression", 6, NULL)) vips_error_exit(NULL);
    g_free(png);
    g_object_unref(out);
    return n;
}

int main(int argc, char **argv) {
    if (VIPS_INIT(argv[0])) vips_error_exit(NULL);
    vips_concurrency_set(1);
    vips_cache_set_max(0);
    const char *mode = argv[1];
    int w = atoi(argv[2]), h = atoi(argv[3]), rounds = atoi(argv[4]);
    for (int i = 5; i < argc; i++) {
        gchar *buf; gsize len;
        if (!g_file_get_contents(argv[i], &buf, &len, NULL)) return 1;
        size_t n = once(mode, buf, len, w, h);
        double *ts = malloc(sizeof(double) * rounds);
        for (int r = 0; r < rounds; r++) { double t = now(); once(mode, buf, len, w, h); ts[r] = now() - t; }
        qsort(ts, rounds, sizeof(double), cmp);
        const char *base = strrchr(argv[i], '/');
        printf("%s\tvips-%s\t%.2f\t%.2f\t%zu\n", base ? base + 1 : argv[i], mode, ts[rounds / 2], ts[0], n);
        free(ts); g_free(buf);
    }
    return 0;
}
