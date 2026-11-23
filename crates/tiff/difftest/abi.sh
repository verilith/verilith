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
#    same for every file both decode to the same samples, but where one of
#    the libtiff behaviours the README lists explains the difference
#    (difftest/apiclass.py tells them apart, by libtiff's own warnings or by
#    the image's layout and fields; each is counted). libtiff is run in mode
#    "rc", without its "strip chopping", which shows a single uncompressed
#    strip as many: verilith-tiff shows the file's strips.
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
cat=0 api=0 known=0 depart=0 departdiff=0 bad=0
: > "$out/reasons"
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
  API_MODE=rc timeout 20 "$out/api_r" "$f" > "$out/r.txt" 2>&1
  if [ "$(timeout 20 "$out/reftiff_r" "$f" 2> /dev/null)" != "$a" ]; then
    depart=$((depart + 1))
    cmp -s "$out/v.txt" "$out/r.txt" || departdiff=$((departdiff + 1))
  elif cmp -s "$out/v.txt" "$out/r.txt"; then
    api=$((api + 1))
  elif why=$(python3 "$here/apiclass.py" "$out/v.txt" "$out/r.txt" "$f"); then
    known=$((known + 1))
    echo "$why" | tr ' ' '\n' >> "$out/reasons"
  else
    bad=$((bad + 1)); echo "API $f: $why"
    [ -n "${VERBOSE:-}" ] && diff "$out/v.txt" "$out/r.txt" | head -8
  fi
done
reasons=$(sort "$out/reasons" | uniq -c | awk '{printf "%s%s %s", (NR > 1 ? ", " : ""), $2, $1}')
rm -rf "$out"
echo "reftiff.c as the Rust API: $cat files; api.c as with libtiff: $api;" \
  "differing only by libtiff's behaviours: $known (${reasons:-none});" \
  "decoded differently by libtiff: $depart (api.c differs on $departdiff); wrong $bad"
[ "$bad" = 0 ]
