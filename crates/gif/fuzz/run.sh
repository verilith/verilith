#!/usr/bin/env bash
# Mutation fuzzing against giflib: writes N mutants of the seed files
# (fuzz/mutate.py) and decodes each with verilith-gif and giflib.
#   fuzz/run.sh OUT N SEED FILES...
# A mutant that both decode to different results, or that only verilith-gif
# accepts, fails the run, except one with an extension that has no data
# sub-blocks, which giflib misreads (fuzz/emptyext.py). Mutants that only
# giflib accepts are counted: the README lists why giflib accepts files the
# specification rejects.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
v=${VGIFCAT:-$root/target/release/examples/vgifcat}
r=${REFGIF:-$here/../difftest/refgif}
out=$1 n=$2 seed=$3
shift 3
rm -rf "$out"
python3 "$here/mutate.py" "$out" "$n" "$seed" "$@"
same=0 bothbad=0 onlyref=0 emptyext=0 bad=0
for f in "$out"/*.gif; do
  a=$("$v" "$f" 2>&1)
  b=$(timeout 10 "$r" "$f" 2>&1)
  if [ "$a" = "$b" ]; then
    if [ "$a" = invalid ]; then bothbad=$((bothbad + 1)); else same=$((same + 1)); fi
  elif [ "$a" = invalid ]; then
    onlyref=$((onlyref + 1))
    [ -n "${KEEP:-}" ] && cp "$f" "$KEEP/"
  elif [ "$b" = invalid ] && python3 "$here/emptyext.py" "$f"; then
    emptyext=$((emptyext + 1))
  else
    bad=$((bad + 1))
    echo "DIFF $f"
    [ -n "${VERBOSE:-}" ] && diff <(echo "$a") <(echo "$b") | head -6
  fi
done
echo "identical $same, rejected by both $bothbad, only giflib accepts $onlyref, empty extension (giflib misreads) $emptyext, wrong $bad"
[ "$bad" = 0 ]
