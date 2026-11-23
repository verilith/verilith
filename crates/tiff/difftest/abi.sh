#!/usr/bin/env bash
# Checks the libtiff-compatible C API (src/capi.rs and capi/tiffshim.c,
# built with --features tiff-abi) through programs written for libtiff,
# compiled against libtiff's own tiffio.h:
#  - difftest/reftiff.c (TIFFOpen, TIFFGetField, TIFFReadEncodedStrip/Tile)
#    linked with verilith-tiff must print what examples/vtiffcat.rs prints,
#    for every file: the C API gives what the verified decoder gives.
#  - difftest/api.c (every tag TIFFGetField and TIFFGetFieldDefaulted
#    report, the size functions, TIFFReadScanline, TIFFReadTile,
#    TIFFReadRGBAImage(Oriented), TIFFReadRGBAStrip and TIFFReadRGBATile),
#    linked once with verilith-tiff and once with libtiff, must print the
#    same for every file both decode to the same samples, but for three
#    things libtiff does, which are counted (see the README):
#     - RGBA from a tiled greyscale image, 16-bit or with extra samples,
#       whose width is not a multiple of the tile width: tif_getimage.c's
#       put16bitbwtile, putgreytile and putagreytile do not scale fromskew
#       by the size of a pixel, so the rows of the right-hand tiles are
#       read from the wrong place. Only the RGBA lines may differ.
#     - TIFFReadScanline on PackBits: libtiff decodes a strip one scanline
#       at a time and cuts a run that crosses into the next scanline short
#       (warning "Discarding ... bytes"). Only the scanline hash may differ.
#     - libtiff replacing the StripByteCounts of the file with its own
#       estimate (warning "... StripByteCounts ..."). Only RowsPerStrip, the
#       byte counts and RGBA may differ.
# Files where verilith-tiff and libtiff decode different samples are the
# departures difftest/compare.sh counts; api.c's output is not compared on
# them, but the number of files where it differs is printed.
#   difftest/abi.sh FILES...
# LIBTIFF_INCLUDE and LIBTIFF_LIB as for difftest/build.sh.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
P=${PROFILE:-release}
A=$root/target/$P/libverilith_tiff.a
v=${VTIFFCAT:-$root/target/$P/examples/vtiffcat}
inc=${LIBTIFF_INCLUDE:+-I $LIBTIFF_INCLUDE}
out=${TMPDIR:-/tmp}/vtiff-abi.$$
mkdir -p "$out"
libs="-lpthread -lm -ldl"
gcc -O2 $inc "$here/reftiff.c" "$A" $libs -o "$out/reftiff_v" || exit 1
gcc -O2 $inc "$here/api.c" "$A" $libs -o "$out/api_v" || exit 1
gcc -O2 $inc "$here/api.c" ${LIBTIFF_LIB:--ltiff} -o "$out/api_r" || exit 1
gcc -O2 $inc "$here/reftiff.c" ${LIBTIFF_LIB:--ltiff} -o "$out/reftiff_r" || exit 1
cat=0 api=0 edge=0 runs=0 counts=0 depart=0 departdiff=0 bad=0
for f in "$@"; do
  a=$("$v" "$f" 2>&1)
  case "$a" in invalid*) a=invalid ;; esac
  if [ "$("$out/reftiff_v" "$f" 2> /dev/null)" != "$a" ]; then
    bad=$((bad + 1)); echo "REFTIFF $f"
  else
    cat=$((cat + 1))
  fi
  [ "$a" = invalid ] && continue
  "$out/api_v" "$f" > "$out/v.txt" 2>&1
  timeout 20 "$out/api_r" "$f" > "$out/r.txt" 2>&1
  if [ "$(timeout 20 "$out/reftiff_r" "$f" 2> /dev/null)" != "$a" ]; then
    depart=$((depart + 1))
    cmp -s "$out/v.txt" "$out/r.txt" || departdiff=$((departdiff + 1))
    continue
  fi
  if cmp -s "$out/v.txt" "$out/r.txt"; then
    api=$((api + 1))
    continue
  fi
  # The first words of the lines that differ, less those a known libtiff
  # behaviour explains.
  # (Without Photometric, the RGBA functions take an image with one colour
  # channel for greyscale.)
  edgebug=$(awk '{d[$1] = $5}
    /^size /{w = $2; tiled = $5}
    /^photometric /{phset = $4}
    /^extrasamples /{extra = $2}
    END {ph = d["photometric"]; b = d["bps"]; n = d["spp"]; tw = d["tilewidth"]
         grey = phset ? (ph == 0 || ph == 1) : (n - extra == 1)
         print (tiled == 1 && grey && tw > 0 && w % tw != 0 &&
                (b == 16 || (b == 8 && n > 1))) ? 1 : 0}' "$out/v.txt")
  grep -q "^warning packbits" "$out/r.txt"; cut=$((1 - $?))
  grep -q "^warning bytecounts" "$out/r.txt"; est=$((1 - $?))
  left=$(diff "$out/v.txt" "$out/r.txt" | sed -n 's/^[<>] \([a-z]*\).*/\1/p' | sort -u |
    awk -v e="$edgebug" -v c="$cut" -v s="$est" '
      $1 == "warning" {next}
      $1 == "rgba" && (e || s) {next}
      $1 == "data" && c {next}
      ($1 == "rps" || $1 == "bytecounts") && s {next}
      {print}')
  if [ -z "$left" ]; then
    [ "$edgebug" = 1 ] && edge=$((edge + 1))
    [ "$cut" = 1 ] && runs=$((runs + 1))
    [ "$est" = 1 ] && counts=$((counts + 1))
  else
    bad=$((bad + 1)); echo "API $f:" $left
    [ -n "${VERBOSE:-}" ] && diff "$out/v.txt" "$out/r.txt" | head -8
  fi
done
rm -rf "$out"
echo "reftiff.c as the Rust API: $cat files; api.c as with libtiff: $api;" \
  "libtiff's edge-tile RGBA bug: $edge, PackBits runs cut at a scanline: $runs," \
  "StripByteCounts estimated: $counts; decoded differently by libtiff: $depart" \
  "(api.c differs on $departdiff); wrong $bad"
[ "$bad" = 0 ]
