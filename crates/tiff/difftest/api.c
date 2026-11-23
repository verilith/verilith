/* Exercises libtiff's reading API on a file and prints what it gives: the
 * fields (TIFFGetField and TIFFGetFieldDefaulted on the baseline tags), the
 * sizes and counts, a hash of every scanline (TIFFReadScanline) or tile
 * (TIFFReadTile), and a hash of the image from TIFFReadRGBAImage, from
 * TIFFReadRGBAImageOriented (top-left), and from TIFFReadRGBAStrip or
 * TIFFReadRGBATile. Linked once with libtiff and once with verilith-tiff
 * (difftest/abi.sh), the two must print the same for files both read.
 * Last, it prints the warnings that explain a known difference (libtiff
 * replacing StripByteCounts with its own estimate, making up ExtraSamples,
 * guessing that a ColorMap is 8-bit), so that abi.sh can tell them apart;
 * verilith-tiff gives none of them. The file is opened in mode $API_MODE
 * ("r" if it is not set).
 *   api FILE */
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <tiffio.h>

static int estimated, extras, cmap8;

static void quiet(const char *m, const char *f, va_list a) {
	(void)m;
	(void)a;
	if (strstr(f, "StripByteCounts")) estimated = 1;
	if (strstr(f, "Defining non-color channels as ExtraSamples")) extras = 1;
	if (strstr(f, "Assuming 8-bit colormap")) cmap8 = 1;
}

static uint64_t fnv(uint64_t h, const void *p, size_t n) {
	const unsigned char *b = p;
	for (size_t i = 0; i < n; i++) {
		h ^= b[i];
		h *= 0x100000001b3ULL;
	}
	return h;
}

static void u16tag(TIFF *t, const char *name, uint32_t tag) {
	uint16_t v = 0xEEEE, d = 0xEEEE;
	int r = TIFFGetField(t, tag, &v);
	int rd = TIFFGetFieldDefaulted(t, tag, &d);
	printf("%s %d %u %d %u\n", name, r, r ? v : 0, rd, rd ? d : 0);
}

static void u32tag(TIFF *t, const char *name, uint32_t tag) {
	uint32_t v = 0xEEEEEEEE, d = 0xEEEEEEEE;
	int r = TIFFGetField(t, tag, &v);
	int rd = TIFFGetFieldDefaulted(t, tag, &d);
	printf("%s %d %u %d %u\n", name, r, r ? v : 0, rd, rd ? d : 0);
}

int main(int argc, char **argv) {
	TIFFSetErrorHandler(quiet);
	TIFFSetWarningHandler(quiet);
	const char *mode = getenv("API_MODE");
	TIFF *t = TIFFOpen(argv[argc - 1], mode ? mode : "r");
	if (!t) {
		printf("open failed\n");
		return 0;
	}
	uint32_t w = 0, h = 0;
	TIFFGetField(t, TIFFTAG_IMAGEWIDTH, &w);
	TIFFGetField(t, TIFFTAG_IMAGELENGTH, &h);
	printf("size %u %u tiled %d bigendian %d\n", w, h, TIFFIsTiled(t), TIFFIsBigEndian(t));
	u16tag(t, "bps", TIFFTAG_BITSPERSAMPLE);
	u16tag(t, "spp", TIFFTAG_SAMPLESPERPIXEL);
	u16tag(t, "compression", TIFFTAG_COMPRESSION);
	u16tag(t, "photometric", TIFFTAG_PHOTOMETRIC);
	u16tag(t, "planar", TIFFTAG_PLANARCONFIG);
	u16tag(t, "fillorder", TIFFTAG_FILLORDER);
	u16tag(t, "orientation", TIFFTAG_ORIENTATION);
	u16tag(t, "sampleformat", TIFFTAG_SAMPLEFORMAT);
	u16tag(t, "resunit", TIFFTAG_RESOLUTIONUNIT);
	u16tag(t, "maxsample", TIFFTAG_MAXSAMPLEVALUE);
	u32tag(t, "rps", TIFFTAG_ROWSPERSTRIP);
	u32tag(t, "subfiletype", TIFFTAG_SUBFILETYPE);
	u32tag(t, "tilewidth", TIFFTAG_TILEWIDTH);
	u32tag(t, "tilelength", TIFFTAG_TILELENGTH);
	float xr = 0;
	printf("xres %d %g\n", TIFFGetField(t, TIFFTAG_XRESOLUTION, &xr), xr);
	char *s = NULL;
	printf("software %d %s\n", TIFFGetField(t, TIFFTAG_SOFTWARE, &s), s ? s : "");
	uint16_t n = 0, *info = NULL;
	if (TIFFGetFieldDefaulted(t, TIFFTAG_EXTRASAMPLES, &n, &info)) {
		printf("extrasamples %u", n);
		for (int i = 0; i < n; i++) printf(" %u", info[i]);
		printf("\n");
	}
	uint16_t *r = NULL, *g = NULL, *b = NULL;
	uint16_t bps = 1;
	TIFFGetFieldDefaulted(t, TIFFTAG_BITSPERSAMPLE, &bps);
	if (TIFFGetField(t, TIFFTAG_COLORMAP, &r, &g, &b) && bps <= 16) {
		uint64_t hh = 0xcbf29ce484222325ULL;
		hh = fnv(hh, r, 2 << bps);
		hh = fnv(hh, g, 2 << bps);
		hh = fnv(hh, b, 2 << bps);
		printf("colormap %016llx\n", (unsigned long long)hh);
	}
	uint64_t *offs = NULL;
	if (TIFFGetField(t, TIFFIsTiled(t) ? TIFFTAG_TILEBYTECOUNTS : TIFFTAG_STRIPBYTECOUNTS, &offs)) {
		uint32_t k = TIFFIsTiled(t) ? TIFFNumberOfTiles(t) : TIFFNumberOfStrips(t);
		printf("bytecounts %016llx\n", (unsigned long long)fnv(0xcbf29ce484222325ULL, offs, 8 * (size_t)k));
	}
	printf("scanline %lld raster %lld strip %lld strips %u tiles %u tilesize %lld\n", (long long)TIFFScanlineSize(t),
	       (long long)TIFFRasterScanlineSize(t), (long long)TIFFStripSize(t), TIFFNumberOfStrips(t),
	       TIFFNumberOfTiles(t), (long long)TIFFTileSize(t));
	uint16_t spp = 1, planar = 1;
	TIFFGetFieldDefaulted(t, TIFFTAG_SAMPLESPERPIXEL, &spp);
	TIFFGetFieldDefaulted(t, TIFFTAG_PLANARCONFIG, &planar);
	uint64_t hh = 0xcbf29ce484222325ULL;
	int ok = 1;
	if (!TIFFIsTiled(t)) {
		tmsize_t sl = TIFFScanlineSize(t);
		unsigned char *buf = malloc(sl > 0 ? sl : 1);
		for (uint16_t smp = 0; smp < (planar == 2 ? spp : 1) && ok; smp++)
			for (uint32_t y = 0; y < h && ok; y++) {
				if (TIFFReadScanline(t, buf, y, smp) < 0) ok = 0;
				else hh = fnv(hh, buf, sl);
			}
		free(buf);
	} else {
		uint32_t tw = 0, th = 0;
		TIFFGetField(t, TIFFTAG_TILEWIDTH, &tw);
		TIFFGetField(t, TIFFTAG_TILELENGTH, &th);
		tmsize_t ts = TIFFTileSize(t);
		unsigned char *buf = malloc(ts > 0 ? ts : 1);
		for (uint16_t smp = 0; smp < (planar == 2 ? spp : 1) && ok; smp++)
			for (uint32_t y = 0; y < h && ok; y += th)
				for (uint32_t x = 0; x < w && ok; x += tw) {
					if (TIFFReadTile(t, buf, x, y, 0, smp) < 0) ok = 0;
					else hh = fnv(hh, buf, ts);
				}
		free(buf);
	}
	printf("data %s %016llx\n", ok ? "ok" : "error", ok ? (unsigned long long)hh : 0ULL);
	if ((uint64_t)w * h < (1u << 26)) {
		uint32_t *ras = malloc(sizeof(uint32_t) * (size_t)w * h + 4);
		char emsg[1024];
		printf("rgbaok %d\n", TIFFRGBAImageOK(t, emsg));
		if (TIFFReadRGBAImage(t, w, h, ras, 0))
			printf("rgba %016llx\n", (unsigned long long)fnv(0xcbf29ce484222325ULL, ras, 4 * (size_t)w * h));
		else
			printf("rgba error\n");
		if (TIFFReadRGBAImageOriented(t, w, h, ras, ORIENTATION_TOPLEFT, 0))
			printf("rgba topleft %016llx\n", (unsigned long long)fnv(0xcbf29ce484222325ULL, ras, 4 * (size_t)w * h));
		else
			printf("rgba topleft error\n");
		free(ras);
		if (TIFFIsTiled(t)) {
			uint32_t tw = 0, th = 0;
			TIFFGetField(t, TIFFTAG_TILEWIDTH, &tw);
			TIFFGetField(t, TIFFTAG_TILELENGTH, &th);
			uint32_t *tr = malloc(sizeof(uint32_t) * (size_t)tw * th);
			uint64_t th2 = 0xcbf29ce484222325ULL;
			int tok = 1;
			for (uint32_t y = 0; y < h && tok; y += th)
				for (uint32_t x = 0; x < w && tok; x += tw) {
					if (!TIFFReadRGBATile(t, x, y, tr)) tok = 0;
					else th2 = fnv(th2, tr, 4 * (size_t)tw * th);
				}
			printf("rgba tiles %s %016llx\n", tok ? "ok" : "error", tok ? (unsigned long long)th2 : 0ULL);
			free(tr);
		} else {
			uint32_t rps = 0;
			TIFFGetFieldDefaulted(t, TIFFTAG_ROWSPERSTRIP, &rps);
			if (rps > h) rps = h;
			uint32_t *sr = malloc(sizeof(uint32_t) * (size_t)w * (rps ? rps : 1));
			uint64_t sh = 0xcbf29ce484222325ULL;
			int sok = 1;
			for (uint32_t y = 0; y < h && sok; y += rps) {
				uint32_t rows = h - y < rps ? h - y : rps;
				if (!TIFFReadRGBAStrip(t, y, sr)) sok = 0;
				else sh = fnv(sh, sr, 4 * (size_t)w * rows);
			}
			printf("rgba strips %s %016llx\n", sok ? "ok" : "error", sok ? (unsigned long long)sh : 0ULL);
			free(sr);
		}
	}
	TIFFClose(t);
	if (estimated) printf("warning bytecounts estimated\n");
	if (extras) printf("warning extrasamples made up\n");
	if (cmap8) printf("warning colormap taken as 8-bit\n");
	return 0;
}
