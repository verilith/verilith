#!/usr/bin/env bash
# gen.sh DIR: writes a corpus of TIFF files for the differential tests with
# ImageMagick (`convert`): grey, RGB, RGBA, 16-bit, bilevel, palette and
# CMYK images, uncompressed, LZW, Deflate and PackBits, in both byte
# orders, in strips (default and 5 rows per strip), in tiles, planar, and
# with the horizontal predictor; 2-, 4-, 12- and 32-bit samples, 32-bit
# floating point, and three 2000 x 1500 images. Deterministic.
set -euo pipefail
out=$1
mkdir -p "$out"
cd "$out"
src="-size 123x77 plasma:fractal -seed 1"
for c in none lzw zip rle; do
  for t in gray rgb rgba gray16 rgb16 bw pal cmyk; do
    case $t in
      gray) o="-colorspace gray -depth 8" ;;
      rgb) o="-depth 8" ;;
      rgba) o="-alpha set -channel A -evaluate set 50% +channel -depth 8" ;;
      gray16) o="-colorspace gray -depth 16" ;;
      rgb16) o="-depth 16" ;;
      bw) o="-monochrome" ;;
      pal) o="-colors 16 -type palette" ;;
      cmyk) o="-colorspace cmyk -depth 8" ;;
    esac
    convert -seed 1 $src $o -compress $c ${c}_${t}.tif
    convert -seed 1 $src $o -compress $c -endian MSB ${c}_${t}_mm.tif
    convert -seed 1 $src $o -compress $c -define tiff:tile-geometry=32x48 ${c}_${t}_tile.tif
    convert -seed 1 $src $o -compress $c -interlace plane ${c}_${t}_planar.tif
    convert -seed 1 $src $o -compress $c -define tiff:rows-per-strip=5 ${c}_${t}_rps.tif
    if [ $c = lzw ] || [ $c = zip ]; then
      # (ImageMagick refuses the predictor for the 4-bit palette images.)
      convert -seed 1 $src $o -compress $c -define tiff:predictor=2 ${c}_${t}_pred.tif 2> /dev/null || true
      convert -seed 1 $src $o -compress $c -define tiff:predictor=2 -endian MSB -interlace plane ${c}_${t}_pred_mm_planar.tif 2> /dev/null || true
    fi
  done
done
for d in 2 4 12; do
  convert -seed 1 -size 99x55 plasma: -colorspace gray -depth $d gd$d.tif
  convert -seed 1 -size 99x55 plasma: -colorspace gray -depth $d -compress lzw gd${d}l.tif
  convert -seed 1 -size 99x55 plasma: -depth $d -endian MSB gd${d}rgbmm.tif
done
convert -seed 1 -size 200x100 plasma: -depth 32 -define quantum:format=floating-point f32.tif
convert -seed 1 -size 200x100 plasma: -depth 32 -define quantum:format=floating-point -compress zip -define tiff:predictor=2 f32p.tif
convert -seed 1 -size 200x100 plasma: -depth 32 -compress lzw -define tiff:predictor=2 -endian MSB i32p.tif
convert -seed 1 -size 2000x1500 plasma:fractal -compress lzw big_lzw.tif
convert -seed 1 -size 2000x1500 plasma:fractal -compress zip -define tiff:predictor=2 big_zip.tif
convert -seed 1 -size 2000x1500 plasma:fractal -compress rle -define tiff:tile-geometry=256x256 big_tile_pb.tif
