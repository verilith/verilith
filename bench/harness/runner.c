#include "runner.h"
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

struct vb_case_t { char *name; uint64_t bytes; vb_fn fn; void *ctx; };
static struct vb_case_t *cases;
static size_t ncases, capcases;

void vb_case(const char *name, uint64_t bytes, vb_fn fn, void *ctx)
{
    if (ncases == capcases) {
        capcases = capcases ? capcases * 2 : 16;
        cases = (struct vb_case_t *)realloc(cases, capcases * sizeof *cases);
    }
    cases[ncases].name = strdup(name);
    cases[ncases].bytes = bytes;
    cases[ncases].fn = fn;
    cases[ncases].ctx = ctx;
    ncases++;
}

const char *vb_data_dir(void)
{
    const char *d = getenv("VBENCH_DATA");
    return d && *d ? d : "data";
}

unsigned char *vb_read_file(const char *path, size_t *len)
{
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "vbench: cannot open %s\n", path); exit(2); }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *b = (unsigned char *)calloc((size_t)n + 64, 1);
    if (!b || fread(b, 1, (size_t)n, f) != (size_t)n) { fprintf(stderr, "vbench: cannot read %s\n", path); exit(2); }
    fclose(f);
    *len = (size_t)n;
    return b;
}

static int cmp(const void *a, const void *b) { return strcmp(*(char *const *)a, *(char *const *)b); }

size_t vb_list_dir(const char *dir, char ***out)
{
    DIR *d = opendir(dir);
    if (!d) { fprintf(stderr, "vbench: cannot open directory %s\n", dir); exit(2); }
    size_t n = 0, cap = 16;
    char **v = (char **)malloc(cap * sizeof *v);
    struct dirent *e;
    while ((e = readdir(d))) {
        if (e->d_name[0] == '.') continue;
        char p[4096];
        struct stat st;
        snprintf(p, sizeof p, "%s/%s", dir, e->d_name);
        if (stat(p, &st) != 0 || !S_ISREG(st.st_mode)) continue;
        if (n == cap) v = (char **)realloc(v, (cap *= 2) * sizeof *v);
        v[n++] = strdup(e->d_name);
    }
    closedir(d);
    qsort(v, n, sizeof *v, cmp);
    *out = v;
    return n;
}

int vb_main(void)
{
    int have = vb_counters_init();
    char line[4096];
    setvbuf(stdout, NULL, _IOLBF, 0);
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!strcmp(line, "quit")) break;
        if (!strcmp(line, "info")) {
            printf("counters %d\n", have);
        } else if (!strcmp(line, "cases")) {
            for (size_t i = 0; i < ncases; i++) printf("%s\t%llu\n", cases[i].name, (unsigned long long)cases[i].bytes);
            printf(".\n");
        } else if (!strncmp(line, "run ", 4)) {
            char *sp = strrchr(line, ' ');
            unsigned long long iters = strtoull(sp + 1, NULL, 10);
            *sp = 0;
            const char *name = line + 4;
            struct vb_case_t *c = NULL;
            for (size_t i = 0; i < ncases; i++) if (!strcmp(cases[i].name, name)) c = &cases[i];
            if (!c) { printf("error unknown case %s\n", name); continue; }
            volatile uint64_t sink = 0;
            uint64_t check = 0;
            int64_t i0, c0, i1, c1;
            vb_counters_read(&i0, &c0);
            uint64_t t0 = vb_now_ns();
            for (unsigned long long k = 0; k < iters; k++) { check = c->fn(c->ctx); sink += check; }
            uint64_t t1 = vb_now_ns();
            vb_counters_read(&i1, &c1);
            (void)sink;
            printf("%llu\t%lld\t%lld\t%llu\n", (unsigned long long)(t1 - t0),
                   (long long)(i0 < 0 || i1 < 0 ? -1 : i1 - i0), (long long)(c0 < 0 || c1 < 0 ? -1 : c1 - c0),
                   (unsigned long long)check);
        } else {
            printf("error unknown command\n");
        }
    }
    return 0;
}
