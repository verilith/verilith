/* HTTP/1.1 heads through picohttpparser's API (phr_parse_request /
 * phr_parse_response), linked once with picohttpparser and once with vhttp
 * (feature phr-abi), which exports the same functions.
 *
 * Cases pico/MSG for every *.http file in $VBENCH_DATA. One call parses the
 * head into a reused array of 100 headers; check = head length * 1000 +
 * header count. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "picohttpparser.h"
#include "runner.h"

struct item { unsigned char *buf; size_t len; int response; struct phr_header h[100]; };

static uint64_t do_parse(void *ctx)
{
    struct item *it = (struct item *)ctx;
    size_t nh = 100;
    int r;
    if (it->response) {
        int minor, status;
        const char *msg;
        size_t msg_len;
        r = phr_parse_response((const char *)it->buf, it->len, &minor, &status, &msg, &msg_len, it->h, &nh, 0);
    } else {
        const char *method, *path;
        size_t ml, pl;
        int minor;
        r = phr_parse_request((const char *)it->buf, it->len, &method, &ml, &path, &pl, &minor, it->h, &nh, 0);
    }
    if (r <= 0) abort();
    return (uint64_t)r * 1000 + nh;
}

int main(void)
{
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
        snprintf(cname, sizeof cname, "pico/%s", names[i]);
        vb_case(cname, it->len, do_parse, it);
    }
    return vb_main();
}
