#!/bin/bash
# Compares vpng with libpng on every file given, in both output formats.
# Prints one line per disagreement and a summary. Exits 1 if the two decode
# a file differently, or vpng decodes a file libpng rejects; files only
# libpng decodes are reported (see the README's departures) but allowed.
# Usage: difftest/compare.sh FILES...
cd "$(dirname "$0")/.."
V=${CARGO_TARGET_DIR:-$PWD/../../target}/release/examples/vpngcat
R=difftest/refpng
# The reference runs under a 2 GB address-space limit: libpng allocates what
# a corrupt header asks for (14 GB for one mutant), which takes a CI runner
# down. A reference that hits the limit prints nothing and counts as ERR.
ref() { (ulimit -v 2097152; exec "$R" "$@"); }
same=0; both_err=0; mismatch=0; vpng_only=0; libpng_only=0
for f in "$@"; do
  for fmt in rgba8 native; do
    a=$($V "$f" $fmt 2>/dev/null | md5sum); ah=$($V "$f" $fmt 2>/dev/null | head -c 40 | head -1)
    b=$(ref "$f" $fmt 2>/dev/null | md5sum); bh=$(ref "$f" $fmt 2>/dev/null | head -c 40 | head -1)
    # No output at all means the reference itself failed (e.g. out of memory).
    [[ -z "$bh" ]] && bh=ERR
    if [[ "$ah" == ERR* && "$bh" == ERR* ]]; then
      both_err=$((both_err+1))
    elif [[ "$a" == "$b" ]]; then
      same=$((same+1))
    elif [[ "$ah" == ERR* ]]; then
      libpng_only=$((libpng_only+1)); echo "LIBPNG-ONLY $fmt $f: vpng=[$ah] libpng=[$bh]"
    elif [[ "$bh" == ERR* ]]; then
      vpng_only=$((vpng_only+1)); echo "VPNG-ONLY $fmt $f: vpng=[$ah] libpng=[$bh]"
    else
      mismatch=$((mismatch+1)); echo "MISMATCH $fmt $f: vpng=[$ah] libpng=[$bh]"
    fi
  done
done
echo "same=$same both_rejected=$both_err mismatch=$mismatch vpng_only=$vpng_only libpng_only=$libpng_only"
[[ $mismatch -eq 0 && $vpng_only -eq 0 ]]
