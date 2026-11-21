// Font suite. One driver, written against OTS's API (opentype-sanitiser.h
// and ots-memory-stream.h), compiled once with OTS's headers and library
// and once with vfont's headers of the same names over its C ABI, so the
// only thing that differs between the two runners is the sanitizer.
//
//   sanitize/FILE   ots::OTSContext::Process on the whole file, into a
//                   fresh ots::ExpandingMemoryStream (how Firefox and
//                   Chrome call it for a web font)
//
// Inputs are the files in $VBENCH_DATA: one face as OpenType/CFF,
// TrueType, and each of them wrapped as WOFF and WOFF2. Both sanitizers
// must accept every file before anything is timed. The check value is the
// size of the sanitized font, which may differ between the two: each
// writes its own serialization of the same tables.
#include <cstdio>
#include <cstdlib>
#include "opentype-sanitiser.h"
#include "ots-memory-stream.h"
#include "runner.h"

struct Item {
    unsigned char *in;
    size_t len;
};

static uint64_t do_sanitize(void *ctx)
{
    Item *it = (Item *)ctx;
    ots::OTSContext context;
    ots::ExpandingMemoryStream out(it->len, 256u << 20);
    if (!context.Process(&out, it->in, it->len)) abort();
    return (uint64_t)out.Tell();
}

int main()
{
    const char *dir = vb_data_dir();
    char **names;
    size_t n = vb_list_dir(dir, &names);
    for (size_t i = 0; i < n; i++) {
        char p[4096], cname[512];
        snprintf(p, sizeof p, "%s/%s", dir, names[i]);
        Item *it = new Item;
        it->in = vb_read_file(p, &it->len);
        ots::OTSContext context;
        ots::ExpandingMemoryStream out(it->len, 256u << 20);
        if (!context.Process(&out, it->in, it->len)) {
            fprintf(stderr, "%s is refused\n", names[i]);
            return 1;
        }
        snprintf(cname, sizeof cname, "sanitize/%s", names[i]);
        vb_case(cname, it->len, do_sanitize, it);
    }
    return vb_main();
}
