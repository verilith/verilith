/* Compresses stdin to stdout with zlib's streaming deflate API, in small
 * chunks, the way zlib's zpipe example does. argv[1]: level, argv[2]:
 * windowBits. Linked against libverilith_zlib.a (zlib-abi), its output is checked
 * by decompressing it with the system zlib. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zlib.h>
#define CHUNK 16384
int main(int argc, char **argv) {
    int level = argc > 1 ? atoi(argv[1]) : Z_DEFAULT_COMPRESSION;
    int wbits = argc > 2 ? atoi(argv[2]) : 15;
    z_stream s;
    unsigned char in[CHUNK], out[CHUNK];
    memset(&s, 0, sizeof s);
    if (deflateInit2(&s, level, Z_DEFLATED, wbits, 8, Z_DEFAULT_STRATEGY) != Z_OK) return 2;
    int flush;
    do {
        s.avail_in = fread(in, 1, CHUNK, stdin);
        flush = feof(stdin) ? Z_FINISH : Z_NO_FLUSH;
        s.next_in = in;
        do {
            s.avail_out = CHUNK;
            s.next_out = out;
            if (deflate(&s, flush) == Z_STREAM_ERROR) return 3;
            fwrite(out, 1, CHUNK - s.avail_out, stdout);
        } while (s.avail_out == 0);
        if (s.avail_in != 0) return 4;
    } while (flush != Z_FINISH);
    return deflateEnd(&s) == Z_OK ? 0 : 5;
}
