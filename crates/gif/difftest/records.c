/* Walks a GIF file with giflib's record-by-record API and prints what it
 * reads: each record, each image descriptor and colour map, a hash of each
 * row from DGifGetLine (or, with -c, of each block from DGifGetCode, or,
 * with -z, of the codes from DGifGetLZCodes), and each extension's blocks.
 * Linked once with giflib and once with verilith-gif (difftest/abi.sh), the
 * two must print the same.
 *   records [-c|-z] FILE */
#include <gif_lib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t fnv(uint64_t h, const unsigned char *b, size_t n) {
	for (size_t i = 0; i < n; i++) {
		h ^= b[i];
		h *= 0x100000001b3ULL;
	}
	return h;
}

static int fail(GifFileType *g, const char *what) {
	printf("error %s %d\n", what, g->Error);
	int e;
	DGifCloseFile(g, &e);
	return 0;
}

int main(int argc, char **argv) {
	const char *mode = argc > 2 ? argv[1] : "";
	const char *file = argv[argc - 1];
	int err;
	GifFileType *g = DGifOpenFileName(file, &err);
	if (!g) {
		printf("open error %d\n", err);
		return 0;
	}
	printf("screen %d %d res %d bg %d aspect %d version %s\n", g->SWidth, g->SHeight, g->SColorResolution,
	       g->SBackGroundColor, g->AspectByte, DGifGetGifVersion(g));
	if (g->SColorMap)
		printf("gct %d %d %d %016llx\n", g->SColorMap->ColorCount, g->SColorMap->BitsPerPixel, g->SColorMap->SortFlag,
		       (unsigned long long)fnv(0xcbf29ce484222325ULL, (unsigned char *)g->SColorMap->Colors,
		                               3 * g->SColorMap->ColorCount));
	for (;;) {
		GifRecordType t;
		if (DGifGetRecordType(g, &t) == GIF_ERROR) return fail(g, "record");
		if (t == TERMINATE_RECORD_TYPE) break;
		if (t == EXTENSION_RECORD_TYPE) {
			int code;
			GifByteType *ext;
			if (DGifGetExtension(g, &code, &ext) == GIF_ERROR) return fail(g, "extension");
			printf("extension %d\n", code);
			while (ext) {
				printf(" block %d %016llx\n", ext[0], (unsigned long long)fnv(0xcbf29ce484222325ULL, ext + 1, ext[0]));
				if (DGifGetExtensionNext(g, &ext) == GIF_ERROR) return fail(g, "extension next");
			}
			continue;
		}
		if (DGifGetImageDesc(g) == GIF_ERROR) return fail(g, "image");
		GifImageDesc *d = &g->Image;
		printf("image %d %d %d %d il %d count %d\n", d->Left, d->Top, d->Width, d->Height, d->Interlace, g->ImageCount);
		if (d->ColorMap)
			printf(" lct %d %016llx\n", d->ColorMap->ColorCount,
			       (unsigned long long)fnv(0xcbf29ce484222325ULL, (unsigned char *)d->ColorMap->Colors,
			                               3 * d->ColorMap->ColorCount));
		if (!strcmp(mode, "-c")) {
			int size;
			GifByteType *b;
			if (DGifGetCode(g, &size, &b) == GIF_ERROR) return fail(g, "code");
			printf(" code size %d\n", size);
			while (b) {
				printf(" code block %d %016llx\n", b[0], (unsigned long long)fnv(0xcbf29ce484222325ULL, b + 1, b[0]));
				if (DGifGetCodeNext(g, &b) == GIF_ERROR) return fail(g, "code next");
			}
		} else if (!strcmp(mode, "-z")) {
			uint64_t h = 0xcbf29ce484222325ULL;
			long n = 0;
			int c;
			do {
				if (DGifGetLZCodes(g, &c) == GIF_ERROR) return fail(g, "lz");
				h = fnv(h, (unsigned char *)&c, sizeof c);
				n++;
			} while (c != -1);
			printf(" codes %ld %016llx\n", n, (unsigned long long)h);
		} else {
			GifPixelType *row = malloc(d->Width > 0 ? d->Width : 1);
			for (int y = 0; y < d->Height; y++) {
				if (DGifGetLine(g, row, d->Width) == GIF_ERROR) {
					free(row);
					return fail(g, "line");
				}
				printf(" row %d %016llx\n", y, (unsigned long long)fnv(0xcbf29ce484222325ULL, row, d->Width));
			}
			free(row);
		}
	}
	printf("end images %d\n", g->ImageCount);
	DGifCloseFile(g, &err);
	return 0;
}
