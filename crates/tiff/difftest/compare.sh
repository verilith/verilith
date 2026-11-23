#!/usr/bin/env bash
# Decodes each file with verilith-tiff (examples/vtiffcat.rs) and with
# libtiff (difftest/reftiff.c, built by difftest/build.sh) and compares the
# summaries: byte order, size, samples, compression, planar configuration
# and a hash of the decoded samples.
#   difftest/compare.sh FILES...
# A file that only libtiff decodes is counted (libtiff reads many files
# that TIFF 6.0 does not allow; the README lists them). So is each
# departure the README lists where verilith-tiff decodes a file libtiff
# does not, or decodes it differently: libtiff second-guessing
# StripByteCounts and then failing, and a field of an unexpected type,
# which TIFF says to skip and libtiff converts or rejects. Anything else
# that differs is printed and fails the run.
# Every file is also checked against difftest/rules.py, an independent
# reading of TIFF 6.0: a file verilith-tiff rejects must break one of the
# standard's rules (or use a part of TIFF not read here), and a file it
# decodes must break none. The rules libtiff's extra files break are
# counted.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
v=${VTIFFCAT:-$root/target/release/examples/vtiffcat}
r=${REFTIFF:-$here/reftiff}
same=0 bothbad=0 onlyref=0 counts=0 skipped=0 bad=0
: > "${TMPDIR:-/tmp}/rules.$$"
for f in "$@"; do
  a=$("$v" "$f" 2>&1)
  rule=$(python3 "$here/rules.py" "$f"); status=$?
  if [ $status != 0 ] && [ $status != 3 ]; then
    bad=$((bad + 1)); echo "RULES.PY failed ($status): $f"; continue
  fi
  conforming=$((status == 3))
  if [[ "$a" == invalid* ]] && [ $conforming = 1 ]; then
    bad=$((bad + 1)); echo "REJECTED, BUT CONFORMING $f"; continue
  elif [[ "$a" != invalid* ]] && [ $conforming = 0 ]; then
    bad=$((bad + 1)); echo "DECODED, BUT $rule: $f"; continue
  fi
  b=$(timeout 20 "$r" "$f" 2> "${TMPDIR:-/tmp}/reftiff.$$")
  why=$(cat "${TMPDIR:-/tmp}/reftiff.$$")
  case "$a" in invalid*) a=invalid ;; esac
  if [ "$a" = "$b" ]; then
    if [ "$a" = invalid ]; then bothbad=$((bothbad + 1)); else same=$((same + 1)); fi
  elif [ "$a" = invalid ]; then
    onlyref=$((onlyref + 1))
    echo "$rule" >> "${TMPDIR:-/tmp}/rules.$$"
    [ -n "${KEEP:-}" ] && cp "$f" "$KEEP/"
  elif [ "$b" = invalid ] && [[ "$why" == "[bytecounts]"* ]]; then
    counts=$((counts + 1))
  elif python3 "$here/skipped.py" "$f"; then
    skipped=$((skipped + 1))
  else
    bad=$((bad + 1))
    echo "DIFF $f ${why}"
    [ -n "${VERBOSE:-}" ] && diff <(echo "$a") <(echo "$b") | head -6
  fi
done
echo "identical $same, rejected by both $bothbad, only libtiff decodes $onlyref," \
  "libtiff second-guesses StripByteCounts $counts, a field of an unexpected type skipped $skipped, wrong $bad"
if [ -s "${TMPDIR:-/tmp}/rules.$$" ]; then
  echo "what the files only libtiff decodes break:"
  sort "${TMPDIR:-/tmp}/rules.$$" | uniq -c | sort -rn
fi
rm -f "${TMPDIR:-/tmp}/reftiff.$$" "${TMPDIR:-/tmp}/rules.$$"
[ "$bad" = 0 ]
