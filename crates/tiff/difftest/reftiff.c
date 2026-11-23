/* Prints a summary of the first image of a TIFF file as libtiff reads it
 * (TIFFReadEncodedStrip or TIFFReadEncodedTile on every strip or tile,
 * assembled as verilith-tiff assembles them), in the format
 * examples/vtiffcat.rs prints, so the two can be compared. */
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <tiffio.h>

/* The first error, and whether libtiff second-guessed StripByteCounts:
 * printed to stderr when the file is rejected, so that difftest/compare.sh
 * can tell the README's departures from new differences. */
static char first[256];
static int bytecounts;
static void on_error(const char *m, const char *f, va_list a) {
	(void)m;
	if (!first[0]) vsnprintf(first, sizeof first, f, a);
}
static void on_warning(const char *m, const char *f, va_list a) {
	(void)m;
	char w[256];
	vsnprintf(w, sizeof w, f, a);
	if (strstr(w, "StripByteCounts")) bytecounts = 1;
}
static int reject(void) {
	printf("invalid\n");
	fprintf(stderr, "%s%s\n", bytecounts ? "[bytecounts] " : "", first);
	return 0;
}

int main(int argc, char **argv) {
	TIFFSetErrorHandler(on_error);
	TIFFSetWarningHandler(on_warning);
	TIFF *t = TIFFOpen(argv[1], "r");
	if (!t) return reject();
	uint32_t w = 0, h = 0;
	uint16_t bps = 1, spp = 1, comp = 1, planar = 1;
	TIFFGetField(t, TIFFTAG_IMAGEWIDTH, &w);
	TIFFGetField(t, TIFFTAG_IMAGELENGTH, &h);
	TIFFGetFieldDefaulted(t, TIFFTAG_BITSPERSAMPLE, &bps);
	TIFFGetFieldDefaulted(t, TIFFTAG_SAMPLESPERPIXEL, &spp);
	TIFFGetFieldDefaulted(t, TIFFTAG_COMPRESSION, &comp);
	TIFFGetFieldDefaulted(t, TIFFTAG_PLANARCONFIG, &planar);
	uint64_t planes = planar == 2 ? spp : 1, sc = planar == 2 ? 1 : spp;
	uint64_t rb = ((uint64_t)w * sc * bps + 7) / 8;
	uint64_t size = planes * h * rb;
	if (size > (1ULL << 32)) return reject();
	unsigned char *out = calloc(size ? size : 1, 1);
	if (TIFFIsTiled(t)) {
		uint32_t tw = 0, th = 0;
		TIFFGetField(t, TIFFTAG_TILEWIDTH, &tw);
		TIFFGetField(t, TIFFTAG_TILELENGTH, &th);
		uint64_t trb = (uint64_t)tw * sc * bps / 8, ts = th * trb;
		uint64_t ta = (w + tw - 1) / tw, td = (h + th - 1) / th;
		unsigned char *buf = malloc(ts ? ts : 1);
		uint32_t n = TIFFNumberOfTiles(t);
		for (uint32_t k = 0; k < n; k++) {
			tmsize_t r = TIFFReadEncodedTile(t, k, buf, ts);
			if (r < 0 || (uint64_t)r != ts) return reject();
			uint64_t pl = k / (ta * td), m = k % (ta * td), ty = m / ta, tx = m % ta;
			uint64_t len = trb <= rb - tx * trb ? trb : rb - tx * trb;
			for (uint64_t yy = 0; yy < th && ty * th + yy < h; yy++)
				memcpy(out + pl * h * rb + (ty * th + yy) * rb + tx * trb, buf + yy * trb, len);
		}
	} else {
		uint32_t n = TIFFNumberOfStrips(t);
		uint64_t pos = 0;
		for (uint32_t k = 0; k < n; k++) {
			tmsize_t ss = TIFFStripSize(t);
			if (pos + ss > size) ss = size - pos;
			tmsize_t r = TIFFReadEncodedStrip(t, k, out + pos, ss);
			if (r < 0) return reject();
			pos += r;
		}
		if (pos != size) return reject();
	}
	uint64_t hh = 0xcbf29ce484222325ULL;
	for (uint64_t i = 0; i < size; i++) { hh ^= out[i]; hh *= 0x100000001b3ULL; }
	printf("image %s %ux%u bps %u spp %u comp %u planar %u bytes %llu px %016llx\n",
	       TIFFIsBigEndian(t) ? "MM" : "II", w, h, bps, spp, comp, planar,
	       (unsigned long long)size, (unsigned long long)hh);
	if (argc > 2) { FILE *f = fopen(argv[2], "wb"); fwrite(out, 1, size, f); fclose(f); }
	return 0;
}
