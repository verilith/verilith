/* A small libarchive client, written only against <archive.h>: lists every
 * member of each archive named on the command line and prints a checksum of
 * its data. run.sh builds it twice, against libarchive and against varchive
 * (feature libarchive-abi), and compares the output. */
#include <archive.h>
#include <archive_entry.h>
#include <locale.h>
#include <stdio.h>

int main(int argc, char **argv)
{
    setlocale(LC_ALL, "C.UTF-8");
    for (int i = 1; i < argc; i++) {
        struct archive *a = archive_read_new();
        archive_read_support_filter_all(a);
        archive_read_support_format_all(a);
        if (archive_read_open_filename(a, argv[i], 10240) != ARCHIVE_OK) {
            printf("%s: cannot open\n", argv[i]);
            archive_read_free(a);
            continue;
        }
        struct archive_entry *e;
        int r;
        while ((r = archive_read_next_header(a, &e)) == ARCHIVE_OK || r == ARCHIVE_WARN) {
            const void *buf;
            size_t n;
            la_int64_t off;
            unsigned long long sum = 1469598103934665603ull, total = 0;
            while (archive_read_data_block(a, &buf, &n, &off) == ARCHIVE_OK) {
                for (size_t k = 0; k < n; k++) sum = (sum ^ ((const unsigned char *)buf)[k]) * 1099511628211ull;
                total += n;
            }
            const char *sl = archive_entry_symlink(e), *hl = archive_entry_hardlink(e);
            printf("%s\t%o\t%lld\t%llu\t%016llx\t%s\t%s\n", archive_entry_pathname(e), (unsigned)archive_entry_mode(e),
                   (long long)archive_entry_size(e), total, sum, sl ? sl : "-", hl ? hl : "-");
        }
        printf("%s: %s\n", argv[i], r == ARCHIVE_EOF ? "end" : "error");
        archive_read_free(a);
    }
    return 0;
}
