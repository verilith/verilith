/* Times giflib's DGifSlurp on a file already in memory:
 *   cbench FILE ROUNDS   prints the best time per decode in milliseconds. */
#include <gif_lib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static const unsigned char *buf;
static size_t len, pos;

static int rd(GifFileType *g, GifByteType *out, int n) {
	(void)g;
	size_t k = len - pos < (size_t)n ? len - pos : (size_t)n;
	memcpy(out, buf + pos, k);
	pos += k;
	return (int)k;
}

int main(int argc, char **argv) {
	FILE *f = fopen(argv[1], "rb");
	fseek(f, 0, SEEK_END);
	len = ftell(f);
	fseek(f, 0, SEEK_SET);
	unsigned char *b = malloc(len);
	if (fread(b, 1, len, f) != len) return 1;
	buf = b;
	int rounds = atoi(argv[2]);
	double best = 1e9;
	unsigned long check = 0;
	for (int r = 0; r < rounds; r++) {
		struct timespec t0, t1;
		clock_gettime(CLOCK_MONOTONIC, &t0);
		pos = 0;
		int err;
		GifFileType *g = DGifOpen(NULL, rd, &err);
		if (!g || DGifSlurp(g) != GIF_OK) return 2;
		check += g->ImageCount;
		DGifCloseFile(g, &err);
		clock_gettime(CLOCK_MONOTONIC, &t1);
		double ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;
		if (ms < best) best = ms;
	}
	printf("%.3f\n", best);
	return check == 0;
}
