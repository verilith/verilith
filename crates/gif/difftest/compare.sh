#!/usr/bin/env bash
# Decodes each file with verilith-gif (examples/vgifcat.rs) and with giflib
# (difftest/refgif.c, built by difftest/build.sh) and compares the summaries:
# the screen, and each image's descriptor, colour table, graphic control and
# pixels (by hash).
#   difftest/compare.sh FILES...
# Prints one line per file that differs, then the counts.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
v=${VGIFCAT:-$root/target/release/examples/vgifcat}
r=${REFGIF:-$here/refgif}
same=0 bothbad=0 diff=0
for f in "$@"; do
  a=$("$v" "$f" 2>&1)
  b=$("$r" "$f" 2>&1)
  if [ "$a" = "$b" ]; then
    if [ "$a" = invalid ]; then bothbad=$((bothbad + 1)); else same=$((same + 1)); fi
  else
    diff=$((diff + 1))
    echo "DIFF $f"
    if [ -n "${VERBOSE:-}" ]; then diff <(echo "$a") <(echo "$b") | head -6; fi
  fi
done
echo "identical $same, rejected by both $bothbad, different $diff"
[ "$diff" = 0 ]
