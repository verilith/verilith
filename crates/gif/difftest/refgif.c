/* Prints a summary of a GIF file as giflib's DGifSlurp reads it, in the
 * format examples/vgifcat.rs prints, so the two can be compared. */
#include <gif_lib.h>
#include <stdint.h>
#include <stdio.h>

static void fnv(uint64_t *h, const unsigned char *b, size_t n) {
	for (size_t i = 0; i < n; i++) {
		*h ^= b[i];
		*h *= 0x100000001b3ULL;
	}
}

static void table(const ColorMapObject *m) {
	if (!m) {
		printf("-");
		return;
	}
	uint64_t h = 0xcbf29ce484222325ULL;
	for (int i = 0; i < m->ColorCount; i++) {
		unsigned char c[3] = {m->Colors[i].Red, m->Colors[i].Green, m->Colors[i].Blue};
		fnv(&h, c, 3);
	}
	printf("%d:%016llx", m->ColorCount, (unsigned long long)h);
}

int main(int argc, char **argv) {
	int err;
	GifFileType *g = DGifOpenFileName(argv[1], &err);
	if (!g) {
		printf("invalid\n");
		return 0;
	}
	if (DGifSlurp(g) != GIF_OK) {
		printf("invalid\n");
		DGifCloseFile(g, &err);
		return 0;
	}
	printf("screen %d %d bg %d gct ", g->SWidth, g->SHeight, g->SBackGroundColor);
	table(g->SColorMap);
	printf("\n");
	for (int i = 0; i < g->ImageCount; i++) {
		SavedImage *s = &g->SavedImages[i];
		GifImageDesc *d = &s->ImageDesc;
		uint64_t h = 0xcbf29ce484222325ULL;
		fnv(&h, s->RasterBits, (size_t)d->Width * d->Height);
		printf("image %d %d %d %d il %d lct ", d->Left, d->Top, d->Width, d->Height, d->Interlace ? 1 : 0);
		table(d->ColorMap);
		GraphicsControlBlock gcb;
		if (DGifSavedExtensionToGCB(g, i, &gcb) == GIF_OK)
			printf(" gce %d %d %d %d", gcb.DisposalMode, gcb.UserInputFlag ? 1 : 0, gcb.DelayTime,
			       gcb.TransparentColor);
		else
			printf(" gce -");
		printf(" px %016llx\n", (unsigned long long)h);
	}
	DGifCloseFile(g, &err);
	return 0;
}
