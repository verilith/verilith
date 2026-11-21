/* Decompresses stdin (zlib, gzip or raw per argv[1]) to stdout with zlib's
 * streaming API, in small chunks. Linked once against zlib and once against
 * libverilith_zlib.a (zlib-abi) to check the drop-in. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>
#define CHUNK 3000
int main(int argc, char **argv) {
    int wbits = argc > 1 ? atoi(argv[1]) : 47;
    z_stream s;
    unsigned char in[CHUNK], out[CHUNK / 2];
    memset(&s, 0, sizeof s);
    if (inflateInit2(&s, wbits) != Z_OK) return 2;
    int ret = Z_OK;
    do {
        s.avail_in = fread(in, 1, CHUNK, stdin);
        if (s.avail_in == 0) break;
        s.next_in = in;
        do {
            s.avail_out = sizeof out;
            s.next_out = out;
            ret = inflate(&s, Z_NO_FLUSH);
            if (ret == Z_DATA_ERROR || ret == Z_STREAM_ERROR || ret == Z_MEM_ERROR || ret == Z_NEED_DICT) {
                fprintf(stderr, "error %d\n", ret);
                return 1;
            }
            fwrite(out, 1, sizeof out - s.avail_out, stdout);
        } while (s.avail_out == 0);
    } while (ret != Z_STREAM_END);
    fprintf(stderr, "ret %d total_in %lu total_out %lu adler %08lx left %u\n", ret, s.total_in, s.total_out, s.adler, s.avail_in);
    inflateEnd(&s);
    return ret == Z_STREAM_END ? 0 : 1;
}
