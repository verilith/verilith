#!/usr/bin/env bash
# Builds libpng's own read tests against the libpng API here and runs them:
# the pngunknown and pngimage scripts of libpng's test suite, and readpng
# on every file of PngSuite, whose exit status must match readpng built
# with libpng. (The other programs in libpng's suite need the write API or
# the simplified API, which are not here.)
#   LIBPNG_DIR=... LIBPNG_BUILD=... difftest/upstream.sh
# LIBPNG_DIR is libpng's source; LIBPNG_BUILD a build of it with this
# crate's include/vpng.dfa (see difftest/abibuild.sh). Run abibuild.sh first.
set -euo pipefail
cd "$(dirname "$0")/.."
U=${LIBPNG_DIR:?set LIBPNG_DIR to libpng source}
B=${LIBPNG_BUILD:-$U/build-vpng}
T=$(cargo metadata --format-version 1 --no-deps | python3 -c 'import json,sys; print(json.load(sys.stdin)["target_directory"])')
lib=$T/release/libverilith_png.a
out=difftest/upstream
mkdir -p "$out"
for t in pngimage pngunknown readpng; do
  cc -O1 -w -Iinclude -I"$U" "$U/contrib/libtests/$t.c" "$lib" -lm -lpthread -ldl -lz -o "$out/$t"
done
cc -O1 -w -I"$B" -I"$U" "$U/contrib/libtests/readpng.c" "$B/libpng16.a" -lz -lm -o "$out/readpng-libpng"

status=0
for t in "$U"/tests/pngunknown-* "$U"/tests/pngimage-quick "$U"/tests/pngimage-full; do
  if (cd "$out" && srcdir=$U sh "$t" > "$(basename "$t").log" 2>&1); then
    echo "ok   $(basename "$t")"
  else
    echo "FAIL $(basename "$t") (see $out/$(basename "$t").log)"; status=1
  fi
done
bad=0
for f in "$U"/contrib/pngsuite/*.png; do
  a=0; "$out/readpng-libpng" < "$f" > /dev/null 2>&1 || a=$?
  b=0; "$out/readpng" < "$f" > /dev/null 2>&1 || b=$?
  if [ "$a" != "$b" ]; then echo "FAIL readpng $(basename "$f"): libpng exit $a, here $b"; bad=1; fi
done
[ $bad = 0 ] && echo "ok   readpng on $(ls "$U"/contrib/pngsuite/*.png | wc -l) PngSuite files" || status=1
exit $status
