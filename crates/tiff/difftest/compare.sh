#!/usr/bin/env bash
# Decodes each file with verilith-tiff (examples/vtiffcat.rs) and with
# libtiff (difftest/reftiff.c, built by difftest/build.sh) and compares the
# summaries: byte order, size, samples, compression, planar configuration
# and a hash of the decoded samples.
#   difftest/compare.sh FILES...
# A file that only libtiff decodes is counted. So is each departure the
# README lists where verilith-tiff decodes a file libtiff does not, or
# decodes it differently: libtiff second-guessing StripByteCounts and then
# failing, and a Deflate strip longer than the strip needs. Anything else
# that differs is printed and fails the run.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
v=${VTIFFCAT:-$root/target/release/examples/vtiffcat}
r=${REFTIFF:-$here/reftiff}
same=0 bothbad=0 onlyref=0 counts=0 overlong=0 bad=0
for f in "$@"; do
  a=$("$v" "$f" 2>&1)
  b=$(timeout 20 "$r" "$f" 2> "${TMPDIR:-/tmp}/reftiff.$$")
  why=$(cat "${TMPDIR:-/tmp}/reftiff.$$")
  case "$a" in invalid*) a=invalid ;; esac
  if [ "$a" = "$b" ]; then
    if [ "$a" = invalid ]; then bothbad=$((bothbad + 1)); else same=$((same + 1)); fi
  elif [ "$a" = invalid ]; then
    onlyref=$((onlyref + 1))
    [ -n "${KEEP:-}" ] && cp "$f" "$KEEP/"
  elif [ "$b" = invalid ] && [[ "$why" == "[bytecounts]"* ]]; then
    counts=$((counts + 1))
  elif [ "$b" != invalid ] && python3 "$here/overlong.py" "$f"; then
    overlong=$((overlong + 1))
  else
    bad=$((bad + 1))
    echo "DIFF $f ${why}"
    [ -n "${VERBOSE:-}" ] && diff <(echo "$a") <(echo "$b") | head -6
  fi
done
rm -f "${TMPDIR:-/tmp}/reftiff.$$"
echo "identical $same, rejected by both $bothbad, only libtiff decodes $onlyref," \
  "libtiff second-guesses StripByteCounts $counts, Deflate strip too long $overlong, wrong $bad"
[ "$bad" = 0 ]
