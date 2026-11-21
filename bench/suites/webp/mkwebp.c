/* mkwebp IN.png OUT.webp [QUALITY]: encodes a PNG as WebP with libwebp's
 * defaults, lossless (WebPEncodeLosslessRGBA), or lossy at QUALITY (0-100,
 * WebPEncodeRGBA; an opaque image gets no alpha chunk). Builds the webp
 * suites' inputs. */
#include <png.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/encode.h"

int main(int argc, char **argv)
{
    if (argc != 3 && argc != 4) { fprintf(stderr, "usage: mkwebp IN.png OUT.webp [QUALITY]\n"); return 2; }
    png_image img;
    memset(&img, 0, sizeof img);
    img.version = PNG_IMAGE_VERSION;
    if (!png_image_begin_read_from_file(&img, argv[1])) { fprintf(stderr, "%s: %s\n", argv[1], img.message); return 1; }
    img.format = PNG_FORMAT_RGBA;
    unsigned char *px = (unsigned char *)malloc(PNG_IMAGE_SIZE(img));
    if (!png_image_finish_read(&img, NULL, px, 0, NULL)) { fprintf(stderr, "%s: %s\n", argv[1], img.message); return 1; }
    uint8_t *out = NULL;
    size_t n = argc == 4
        ? WebPEncodeRGBA(px, (int)img.width, (int)img.height, (int)img.width * 4, (float)atof(argv[3]), &out)
        : WebPEncodeLosslessRGBA(px, (int)img.width, (int)img.height, (int)img.width * 4, &out);
    if (!n) { fprintf(stderr, "encoding failed\n"); return 1; }
    FILE *f = fopen(argv[2], "wb");
    if (!f || fwrite(out, 1, n, f) != n || fclose(f)) { perror(argv[2]); return 1; }
    WebPFree(out);
    free(px);
    return 0;
}
