/* mkjpeg IN.png OUT.jpg QUALITY 420|444 [progressive]: encodes a PNG as a
 * JPEG with libjpeg-turbo (tj3Compress8), baseline unless "progressive" is
 * given. Builds the jpeg suites' inputs. */
#include <png.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <turbojpeg.h>

int main(int argc, char **argv)
{
    if (argc != 5 && argc != 6) { fprintf(stderr, "usage: mkjpeg IN.png OUT.jpg QUALITY 420|444 [progressive]\n"); return 2; }
    png_image img;
    memset(&img, 0, sizeof img);
    img.version = PNG_IMAGE_VERSION;
    if (!png_image_begin_read_from_file(&img, argv[1])) { fprintf(stderr, "%s: %s\n", argv[1], img.message); return 1; }
    img.format = PNG_FORMAT_RGB;
    unsigned char *px = (unsigned char *)malloc(PNG_IMAGE_SIZE(img));
    if (!png_image_finish_read(&img, NULL, px, 0, NULL)) { fprintf(stderr, "%s: %s\n", argv[1], img.message); return 1; }
    tjhandle h = tj3Init(TJINIT_COMPRESS);
    if (!h) { fprintf(stderr, "tj3Init failed\n"); return 1; }
    tj3Set(h, TJPARAM_QUALITY, atoi(argv[3]));
    tj3Set(h, TJPARAM_SUBSAMP, strcmp(argv[4], "444") ? TJSAMP_420 : TJSAMP_444);
    tj3Set(h, TJPARAM_PROGRESSIVE, argc == 6);
    unsigned char *out = NULL;
    size_t n = 0;
    if (tj3Compress8(h, px, (int)img.width, 0, (int)img.height, TJPF_RGB, &out, &n) != 0) {
        fprintf(stderr, "encoding failed: %s\n", tj3GetErrorStr(h));
        return 1;
    }
    FILE *f = fopen(argv[2], "wb");
    if (!f || fwrite(out, 1, n, f) != n || fclose(f)) { perror(argv[2]); return 1; }
    tj3Free(out);
    tj3Destroy(h);
    free(px);
    return 0;
}
