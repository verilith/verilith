#!/usr/bin/env bash
# Checks the giflib-compatible C API (src/capi.rs, built with --features
# gif-abi) through programs written for giflib, compiled against giflib's
# own gif_lib.h:
#  - difftest/refgif.c (DGifOpenFileName, DGifSlurp, DGifSavedExtensionToGCB)
#    linked with verilith-gif must print what examples/vgifcat.rs prints,
#    for every file: the C API gives what the verified decoder gives.
#  - difftest/records.c (the record-by-record API: rows from DGifGetLine,
#    blocks from DGifGetCode, codes from DGifGetLZCodes, extension blocks),
#    linked once with verilith-gif and once with giflib, must print the same
#    for every file the specification accepts.
#  - giflib's giftext (the record-by-record API: DGifGetRecordType,
#    DGifGetImageDesc, DGifGetLine, DGifGetExtension, DGifGetCode,
#    DGifGetLZCodes), linked once with verilith-gif and once with giflib,
#    with each of its dump options, must print the same for every file
#    it runs on with both.
#   [GIFLIB_SRC=giflib-source-tree] difftest/abi.sh FILES...
# Without GIFLIB_SRC, giftext is left out and the system gif_lib.h is used.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
P=${PROFILE:-release}
A=$root/target/$P/libverilith_gif.a
v=${VGIFCAT:-$root/target/$P/examples/vgifcat}
G=${GIFLIB_SRC:-}
inc=${G:+-I $G}
out=${TMPDIR:-/tmp}/vgif-abi.$$
mkdir -p "$out"
libs="-lpthread -lm -ldl"
gcc -O2 $inc "$here/refgif.c" "$A" $libs -o "$out/refgif_v"
gcc -O2 $inc "$here/records.c" "$A" $libs -o "$out/records_v"
gcc -O2 $inc "$here/records.c" ${GIFLIB_LIB:--lgif} -o "$out/records_r"
if [ -n "$G" ]; then
  gcc -O2 -w -I "$G" "$G/giftext.c" "$G/getarg.c" "$G/qprintf.c" "$A" $libs -o "$out/giftext_v"
  gcc -O2 -w -I "$G" "$G/giftext.c" "$G/getarg.c" "$G/qprintf.c" ${GIFLIB_LIB:--lgif} -o "$out/giftext_r"
fi
slurp=0 rec=0 text=0 both=0 textskip=0 bad=0
for f in "$@"; do
  if [ "$("$out/refgif_v" "$f")" != "$("$v" "$f")" ]; then
    bad=$((bad + 1)); echo "SLURP $f"
  else
    slurp=$((slurp + 1))
  fi
  ok=$("$v" "$f" 2> /dev/null)
  if [ "$ok" != invalid ]; then
    for o in "" -c -z; do
      if cmp -s <("$out/records_v" $o "$f") <("$out/records_r" $o "$f"); then rec=$((rec + 1)); else bad=$((bad + 1)); echo "RECORDS $o $f"; fi
    done
  fi
  [ -n "$G" ] || continue
  # giftext, with each dump option, must print the same with both
  # libraries where it succeeds with both, and fail with both or neither.
  # Where only one fails: if the
  # specification rejects the file, that is a departure in the README
  # (giflib prints made-up pixels for a defective image); otherwise it is
  # wrong. (On some files with comment or application extensions giftext
  # overflows its own HexForm buffer and aborts, with either library.)
  for o in "" -c -e -z -p; do
    "$out/giftext_v" $o "$f" > "$out/v.txt" 2>&1; sv=$?
    "$out/giftext_r" $o "$f" > "$out/r.txt" 2>&1; sr=$?
    if [ $sv = 0 ] && [ $sr = 0 ]; then
      if cmp -s "$out/v.txt" "$out/r.txt"; then text=$((text + 1)); else bad=$((bad + 1)); echo "GIFTEXT $o $f"; fi
    elif [ $sv != 0 ] && [ $sr != 0 ]; then
      both=$((both + 1))
    elif [ "$ok" = invalid ] || grep -q "buffer overflow" "$out/r.txt" "$out/v.txt"; then
      textskip=$((textskip + 1))
    else
      bad=$((bad + 1)); echo "GIFTEXT $o $f (exit $sv, giflib $sr)"
    fi
  done
done
rm -rf "$out"
echo "DGifSlurp as the Rust API: $slurp files; records.c as with giflib: $rec runs; giftext runs as with giflib: $text, failing with both: $both; giftext runs on files the spec rejects or that overflow giftext: $textskip; wrong $bad"
[ "$bad" = 0 ]
