/* archive suite. One driver, written against libarchive's read API
 * (archive.h), linked once with libarchive and once with varchive's C ABI
 * (feature libarchive-abi), so the only thing that differs between the two
 * runners is the library.
 *
 *   read/ARCHIVE   open the archive from memory, walk every member and read
 *                  all of its data (archive_read_data_block)
 *   list/ARCHIVE   open and walk every header, skipping the data
 *
 * The archives are in $VBENCH_DATA; scripts/build.sh makes them with
 * libarchive's own bsdtar from the Silesia files and from a tree of 2000
 * small files. The check value mixes the member count, the names and the
 * data, so both libraries must find the same members and the same bytes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <archive.h>
#include <archive_entry.h>
#include "runner.h"

struct item {
    unsigned char *in;
    size_t len;
    int read;
};

static uint64_t mix(uint64_t h, const unsigned char *p, size_t n)
{
    size_t step = n / 64 + 1;
    for (size_t i = 0; i < n; i += step) h = (h ^ p[i]) * 0x100000001b3ull;
    return h;
}

static uint64_t walk(void *ctx)
{
    struct item *it = (struct item *)ctx;
    struct archive *a = archive_read_new();
    if (!a) abort();
    archive_read_support_filter_all(a);
    archive_read_support_format_all(a);
    if (archive_read_open_memory(a, it->in, it->len) != ARCHIVE_OK) abort();
    struct archive_entry *e;
    uint64_t h = 0, members = 0;
    int r;
    while ((r = archive_read_next_header(a, &e)) == ARCHIVE_OK) {
        const char *name = archive_entry_pathname(e);
        h = mix(h + (uint64_t)archive_entry_size(e), (const unsigned char *)name, strlen(name));
        members++;
        if (it->read) {
            const void *buf;
            size_t n;
            la_int64_t off;
            uint64_t total = 0, d = 0;
            int rr;
            while ((rr = archive_read_data_block(a, &buf, &n, &off)) == ARCHIVE_OK) {
                /* Every 4093rd byte of the member, wherever the blocks end
                 * (the two libraries cut them differently). */
                for (size_t j = (4093 - total % 4093) % 4093; j < n; j += 4093) d = (d ^ ((const unsigned char *)buf)[j]) * 0x100000001b3ull;
                total += n;
            }
            if (rr != ARCHIVE_EOF) abort();
            h = (h ^ total ^ d) * 0x100000001b3ull;
        }
    }
    if (r != ARCHIVE_EOF) abort();
    archive_read_free(a);
    return h ^ (members << 48);
}

int main(void)
{
    char **names;
    size_t n = vb_list_dir(vb_data_dir(), &names);
    for (size_t i = 0; i < n; i++) {
        char path[4096], name[512];
        snprintf(path, sizeof path, "%s/%s", vb_data_dir(), names[i]);
        for (int read = 1; read >= 0; read--) {
            struct item *it = malloc(sizeof *it);
            it->in = vb_read_file(path, &it->len);
            it->read = read;
            snprintf(name, sizeof name, "%s/%s", read ? "read" : "list", names[i]);
            vb_case(name, it->len, walk, it);
        }
    }
    return vb_main();
}
