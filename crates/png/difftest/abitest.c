/* Reads a PNG file through libpng's API and prints what it got: the
 * header after the transformations, the info chunks, a hash of every row,
 * warnings and errors. Built twice, against libpng and against
 * verilith-png's libpng API (difftest/abibuild.sh), so that the two
 * outputs can be compared (difftest/abicompare.sh).
 *
 * Usage: abitest FILE MODE TRANSFORMS [CHUNK]
 *   MODE: seq (png_read_row with interlace handling), dsp (the same into
 *         display rows), nil (no interlace handling: the passes' rows),
 *         img (png_read_image), png (png_read_png), prog (progressive, fed
 *         CHUNK bytes at a time)
 *   TRANSFORMS: a hex mask of the transformations below.
 */
#include <png.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static FILE *out;
static unsigned long long hash = 1469598103934665603ULL;
static unsigned long user_calls, user_bytes;

static void h(const unsigned char *p, size_t n)
{
   for (size_t i = 0; i < n; i++) { hash ^= p[i]; hash *= 1099511628211ULL; }
}

/* Hashes a row of w pixels of d bits, without the padding bits of the
 * last byte, which libpng leaves as they were. */
static void hrow(const unsigned char *p, size_t w, unsigned d)
{
   size_t bits = w * d, n = bits / 8;
   h(p, n);
   if (bits & 7) { unsigned char c = p[n] & (unsigned char)(0xff << (8 - (bits & 7))); h(&c, 1); }
}

static unsigned out_bits;

static void err(png_structp p, png_const_charp m)
{
   fprintf(out, "ERR %s\n", m);
   png_longjmp(p, 1);
}

static void wrn(png_structp p, png_const_charp m)
{
   (void)p;
   fprintf(out, "W %s\n", m);
}

static void user_xform(png_structp p, png_row_infop ri, png_bytep row)
{
   (void)p;
   user_calls++;
   user_bytes += ri->rowbytes;
   hrow(row, ri->width, ri->pixel_depth);
   h(&ri->color_type, 1); h(&ri->bit_depth, 1); h(&ri->channels, 1);
}

static unsigned tmask;

static void set_transforms(png_structp p, png_infop info)
{
   unsigned t = tmask;
   if (t & 0x1) png_set_expand(p);
   if (t & 0x2) png_set_strip_16(p);
   if (t & 0x4) png_set_scale_16(p);
   if (t & 0x8) png_set_strip_alpha(p);
   if (t & 0x10) png_set_gray_to_rgb(p);
   if (t & 0x20) png_set_filler(p, 0xff, PNG_FILLER_AFTER);
   if (t & 0x40) png_set_filler(p, 0x1234, PNG_FILLER_BEFORE);
   if (t & 0x80) png_set_add_alpha(p, 0xffff, PNG_FILLER_AFTER);
   if (t & 0x100) png_set_bgr(p);
   if (t & 0x200) png_set_swap_alpha(p);
   if (t & 0x400) png_set_invert_alpha(p);
   if (t & 0x800) png_set_invert_mono(p);
   if (t & 0x1000) png_set_packing(p);
   if (t & 0x2000) png_set_packswap(p);
   if (t & 0x4000) png_set_swap(p);
   if (t & 0x8000) png_set_expand_16(p);
   if (t & 0x10000)
   {
      png_color_8p sb;
      if (png_get_sBIT(p, info, &sb)) png_set_shift(p, sb);
   }
   if (t & 0x20000) png_set_tRNS_to_alpha(p);
   if (t & 0x40000) png_set_palette_to_rgb(p);
   if (t & 0x80000) png_set_expand_gray_1_2_4_to_8(p);
   if (t & 0x100000) png_set_read_user_transform_fn(p, user_xform);
}

static void print_info(png_structp p, png_infop info, const char *what)
{
   png_uint_32 w, ht;
   int bd, ct, il, cm, fm;
   png_textp text;
   int nt = 0;
   png_unknown_chunkp unk;
   int nu;
   /* png_get_IHDR is an error on an info with no IHDR (the end info). */
   if (!strcmp(what, "end") || !png_get_IHDR(p, info, &w, &ht, &bd, &ct, &il, &cm, &fm)) fprintf(out, "%s valid=%x\n", what, png_get_valid(p, info, 0xffffffff));
   else fprintf(out, "%s %ux%u bd=%d ct=%d il=%d ch=%d rb=%zu valid=%x\n", what, w, ht, bd, ct, il,
       png_get_channels(p, info), png_get_rowbytes(p, info), png_get_valid(p, info, 0xffffffff));
   png_get_text(p, info, &text, &nt);
   for (int i = 0; i < nt; i++)
      fprintf(out, "  text %d [%s] %zu %zu [%.40s]\n", text[i].compression, text[i].key,
          text[i].text_length, text[i].itxt_length, text[i].text);
   nu = png_get_unknown_chunks(p, info, &unk);
   for (int i = 0; i < nu; i++)
      fprintf(out, "  unknown %.4s %zu loc=%d\n", unk[i].name, unk[i].size, unk[i].location);
   {
      png_colorp pal; int np;
      if (png_get_PLTE(p, info, &pal, &np)) { fprintf(out, "  plte %d\n", np); h((void *)pal, 3 * np); }
   }
   {
      png_bytep ta; int ntr; png_color_16p tc;
      if (png_get_tRNS(p, info, &ta, &ntr, &tc))
         fprintf(out, "  trns %d %u %u %u %u\n", ntr, tc->red, tc->green, tc->blue, tc->gray);
   }
   {
      png_color_16p bg;
      if (png_get_bKGD(p, info, &bg))
         fprintf(out, "  bkgd %u %u %u %u %u\n", bg->index, bg->red, bg->green, bg->blue, bg->gray);
   }
   {
      png_fixed_point g;
      if (png_get_gAMA_fixed(p, info, &g)) fprintf(out, "  gama %d\n", g);
   }
   {
      png_timep tm;
      if (png_get_tIME(p, info, &tm)) fprintf(out, "  time %u-%u-%u\n", tm->year, tm->month, tm->day);
   }
   {
      png_charp name; int comp; png_bytep prof; png_uint_32 len;
      if (png_get_iCCP(p, info, &name, &comp, &prof, &len)) { fprintf(out, "  iccp %s %u\n", name, len); h(prof, len); }
   }
   {
      png_color_8p sb;
      if (png_get_sBIT(p, info, &sb)) fprintf(out, "  sbit %u %u %u %u %u\n", sb->red, sb->green, sb->blue, sb->gray, sb->alpha);
   }
   {
      png_uint_32 x, y; int u;
      if (png_get_pHYs(p, info, &x, &y, &u)) fprintf(out, "  phys %u %u %d\n", x, y, u);
   }
}

/* Progressive reading. */
static png_bytep *prog_rows;
static int prog_done, prog_info;
static size_t prog_rb;

static void p_info(png_structp p, png_infop info)
{
   prog_info = 1;
   set_transforms(p, info);
   (void)png_set_interlace_handling(p);
   png_read_update_info(p, info);
   print_info(p, info, "info");
   prog_rb = png_get_rowbytes(p, info);
   out_bits = png_get_channels(p, info) * png_get_bit_depth(p, info);
   png_uint_32 ht = png_get_image_height(p, info);
   prog_rows = calloc(ht ? ht : 1, sizeof *prog_rows);
   for (png_uint_32 y = 0; y < ht; y++) prog_rows[y] = calloc(prog_rb + 1, 1);
}

static void p_row(png_structp p, png_bytep row, png_uint_32 n, int pass)
{
   (void)pass;
   png_progressive_combine_row(p, prog_rows[n], row);
}

static void p_end(png_structp p, png_infop info)
{
   (void)p; (void)info;
   prog_done = 1;
}

int main(int argc, char **argv)
{
   if (argc < 4) return 2;
   out = stdout;
   const char *mode = argv[2];
   tmask = (unsigned)strtoul(argv[3], NULL, 16);
   size_t chunk = argc > 4 ? (size_t)atoi(argv[4]) : 4096;
   FILE *f = fopen(argv[1], "rb");
   if (!f) return 2;
   png_structp p = png_create_read_struct(PNG_LIBPNG_VER_STRING, NULL, err, wrn);
   png_infop info = png_create_info_struct(p);
   png_infop end = png_create_info_struct(p);
   png_bytep *rows = NULL;
   png_uint_32 ht = 0;
   static volatile int stage;
   if (setjmp(png_jmpbuf(p)))
   {
      fprintf(out, "stage %d hash %016llx\n", stage, hash);
      return 0;
   }
   png_set_keep_unknown_chunks(p, PNG_HANDLE_CHUNK_IF_SAFE, NULL, 0);
   if (!strcmp(mode, "prog"))
   {
      unsigned char *buf = malloc(chunk);
      size_t n;
      png_set_progressive_read_fn(p, NULL, p_info, p_row, p_end);
      stage = 1;
      while ((n = fread(buf, 1, chunk, f)) > 0)
         png_process_data(p, info, buf, n);
      if (prog_info)
      {
         ht = png_get_image_height(p, info);
         for (png_uint_32 y = 0; y < ht; y++) hrow(prog_rows[y], png_get_image_width(p, info), out_bits);
      }
      fprintf(out, "done=%d\n", prog_done);
      print_info(p, info, "end");
      fprintf(out, "hash %016llx\n", hash);
      return 0;
   }
   png_init_io(p, f);
   if (!strcmp(mode, "png"))
   {
      /* The png_read_png transform bits that match ours. */
      int t = 0;
      if (tmask & 0x1) t |= PNG_TRANSFORM_EXPAND;
      if (tmask & 0x2) t |= PNG_TRANSFORM_STRIP_16;
      if (tmask & 0x4) t |= PNG_TRANSFORM_SCALE_16;
      if (tmask & 0x8) t |= PNG_TRANSFORM_STRIP_ALPHA;
      if (tmask & 0x10) t |= PNG_TRANSFORM_GRAY_TO_RGB;
      if (tmask & 0x100) t |= PNG_TRANSFORM_BGR;
      if (tmask & 0x200) t |= PNG_TRANSFORM_SWAP_ALPHA;
      if (tmask & 0x400) t |= PNG_TRANSFORM_INVERT_ALPHA;
      if (tmask & 0x800) t |= PNG_TRANSFORM_INVERT_MONO;
      if (tmask & 0x1000) t |= PNG_TRANSFORM_PACKING;
      if (tmask & 0x2000) t |= PNG_TRANSFORM_PACKSWAP;
      if (tmask & 0x4000) t |= PNG_TRANSFORM_SWAP_ENDIAN;
      if (tmask & 0x8000) t |= PNG_TRANSFORM_EXPAND_16;
      if (tmask & 0x10000) t |= PNG_TRANSFORM_SHIFT;
      stage = 1;
      png_read_png(p, info, t, NULL);
      print_info(p, info, "png");
      rows = png_get_rows(p, info);
      ht = png_get_image_height(p, info);
      out_bits = png_get_channels(p, info) * png_get_bit_depth(p, info);
      for (png_uint_32 y = 0; y < ht; y++) hrow(rows[y], png_get_image_width(p, info), out_bits);
      fprintf(out, "hash %016llx\n", hash);
      return 0;
   }
   stage = 1;
   png_read_info(p, info);
   print_info(p, info, "file");
   set_transforms(p, info);
   int passes = 1;
   if (strcmp(mode, "nil")) passes = png_set_interlace_handling(p);
   png_read_update_info(p, info);
   print_info(p, info, "out");
   ht = png_get_image_height(p, info);
   png_uint_32 w = png_get_image_width(p, info);
   size_t rb = png_get_rowbytes(p, info);
   out_bits = png_get_channels(p, info) * png_get_bit_depth(p, info);
   rows = calloc(ht ? ht : 1, sizeof *rows);
   for (png_uint_32 y = 0; y < ht; y++) rows[y] = calloc(rb + 1, 1);
   stage = 2;
   if (!strcmp(mode, "nil"))
   {
      int il = png_get_interlace_type(p, info);
      if (il == PNG_INTERLACE_NONE)
      {
         for (png_uint_32 y = 0; y < ht; y++) { png_read_row(p, rows[0], NULL); hrow(rows[0], w, out_bits); }
      }
      else
      {
         for (int pass = 0; pass < 7; pass++)
         {
            png_uint_32 pw = PNG_PASS_COLS(w, pass), ph = PNG_PASS_ROWS(ht, pass);
            if (pw == 0 || ph == 0) continue;
            for (png_uint_32 y = 0; y < ph; y++)
            {
               png_read_row(p, rows[0], NULL);
               hrow(rows[0], pw, out_bits);
            }
         }
      }
   }
   else if (!strcmp(mode, "img"))
   {
      png_read_image(p, rows);
      for (png_uint_32 y = 0; y < ht; y++) hrow(rows[y], w, out_bits);
   }
   else
   {
      int dsp = !strcmp(mode, "dsp");
      for (int pass = 0; pass < passes; pass++)
         for (png_uint_32 y = 0; y < ht; y++)
            png_read_row(p, dsp ? NULL : rows[y], dsp ? rows[y] : NULL);
      for (png_uint_32 y = 0; y < ht; y++) hrow(rows[y], w, out_bits);
   }
   fprintf(out, "user %lu %lu\n", user_calls, user_bytes);
   stage = 3;
   png_read_end(p, end);
   print_info(p, end, "end");
   fprintf(out, "hash %016llx\n", hash);
   png_destroy_read_struct(&p, &info, &end);
   return 0;
}
