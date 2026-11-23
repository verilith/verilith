/* Times libtiff on a file already in memory (TIFFClientOpen over a buffer),
 * reading every strip or tile of the first image with TIFFReadEncodedStrip
 * or TIFFReadEncodedTile, as difftest/reftiff.c does:
 *   tbench FILE ROUNDS   prints the best time per decode in milliseconds. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <tiffio.h>

static unsigned char *buf;
static toff_t len, pos;
static tmsize_t rd(thandle_t h, void *b, tmsize_t n) {
	(void)h;
	if (pos >= len) return 0;
	if ((toff_t)n > len - pos) n = len - pos;
	memcpy(b, buf + pos, n);
	pos += n;
	return n;
}
static tmsize_t wr(thandle_t h, void *b, tmsize_t n) { (void)h; (void)b; (void)n; return 0; }
static toff_t sk(thandle_t h, toff_t o, int w) {
	(void)h;
	pos = w == SEEK_SET ? o : w == SEEK_CUR ? pos + o : len + o;
	return pos;
}
static int cl(thandle_t h) { (void)h; return 0; }
static toff_t sz(thandle_t h) { (void)h; return len; }
static int mp(thandle_t h, void **b, toff_t *n) { (void)h; *b = buf; *n = len; return 1; }
static void um(thandle_t h, void *b, toff_t n) { (void)h; (void)b; (void)n; }

int main(int argc, char **argv) {
	FILE *f = fopen(argv[1], "rb");
	fseek(f, 0, SEEK_END);
	len = ftell(f);
	fseek(f, 0, SEEK_SET);
	buf = malloc(len);
	if (fread(buf, 1, len, f) != len) return 1;
	int rounds = atoi(argv[2]);
	double best = 1e9;
	for (int r = 0; r < rounds; r++) {
		struct timespec t0, t1;
		clock_gettime(CLOCK_MONOTONIC, &t0);
		pos = 0;
		TIFF *t = TIFFClientOpen("mem", "rm", NULL, rd, wr, sk, cl, sz, mp, um);
		if (!t) return 2;
		int tiled = TIFFIsTiled(t);
		uint32_t n = tiled ? TIFFNumberOfTiles(t) : TIFFNumberOfStrips(t);
		tmsize_t cs = tiled ? TIFFTileSize(t) : TIFFStripSize(t);
		unsigned char *o = malloc(cs);
		for (uint32_t k = 0; k < n; k++)
			if ((tiled ? TIFFReadEncodedTile(t, k, o, cs) : TIFFReadEncodedStrip(t, k, o, cs)) < 0) return 3;
		free(o);
		TIFFClose(t);
		clock_gettime(CLOCK_MONOTONIC, &t1);
		double ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;
		if (ms < best) best = ms;
	}
	printf("%.3f\n", best);
	return 0;
}
