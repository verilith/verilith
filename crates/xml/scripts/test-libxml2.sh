#!/usr/bin/env bash
# libxml2's own regression tests (runtest.c) against verilith-xml's libxml2
# ABI (feature libxml2-abi): runtest, built from libxml2 2.15.4's sources
# with the parts this ABI has (tree, output, push, SAX1, the parser's
# validity flags), under ASan and UBSan, and linked against
# libverilith_xml.a in place of libxml2.
# It runs the suites those parts cover; each compares the parser's events,
# errors and serialized trees with libxml2's expected files.
#
# A test outside tests/c/libxml2-known-failures.txt that fails, fails this
# script; so does one in that list that now passes (remove it).
#   scripts/test-libxml2.sh
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
X=$(scripts/fetch-libxml2.sh)
P=$(../../scripts/profile xml)
cargo build -q --profile "$P" --features libxml2-abi 2>/dev/null || cargo build --profile "$P" --features libxml2-abi
LIB=${CARGO_TARGET_DIR:-$ROOT/../../target}/$P/libverilith_xml.a
OUT=$ROOT/target/libxml2-tests
rm -rf "$OUT"
mkdir -p "$OUT/libxml" "$OUT/tmp"
CC=${CC:-cc}
# libxml2's build configuration: what this ABI has on, the rest off.
on="THREADS OUTPUT PUSH SAX1 VALID"
args=()
for w in $(grep -o '@WITH_[A-Z0-9_]*@' "$X/include/libxml/xmlversion.h.in" | sort -u | tr -d @); do
  v=0
  for o in $on; do [ "$w" = "WITH_$o" ] && v=1; done
  args+=(-e "s/@$w@/$v/")
done
sed "${args[@]}" -e 's/@VERSION@/2.15.4/' -e 's/@LIBXML_VERSION_NUMBER@/21504/' \
  -e 's/@LIBXML_VERSION_EXTRA@//' -e 's/@MODULE_EXTENSION@/.so/' \
  "$X/include/libxml/xmlversion.h.in" > "$OUT/libxml/xmlversion.h"
cat > "$OUT/config.h" <<'EOC'
#define HAVE_UNISTD_H 1
#define HAVE_FCNTL_H 1
#define HAVE_SYS_STAT_H 1
#define HAVE_STDINT_H 1
#define HAVE_GLOB_H 1
#define HAVE_DECL_GLOB 1
#define XML_SYSCONFDIR "/etc"
EOC
SAN="-fsanitize=address,undefined -g"
# stdbuf preloads a library, which ASan would otherwise refuse.
export ASAN_OPTIONS=detect_leaks=0:verify_asan_link_order=0
$CC $SAN -O1 -w -DHAVE_CONFIG_H -I"$OUT" -I"$X/include" -I"$X" -o "$OUT/runtest" "$X/runtest.c" "$LIB" -lm -lpthread -ldl
# The struct layouts: libxml2's headers against the ABI's.
$CC -w -I"$OUT" -I"$X/include" -o "$OUT/layout" tests/c/libxml2_layout.c "$LIB" -lm -lpthread -ldl
"$OUT/layout" || exit 1
# The suites this ABI covers (runtest matches each name as a substring).
suites=(
  "XML regression tests"
  "XML regression tests on memory"
  "XML entity subst regression tests"
  "XML Namespaces regression tests"
  "Error cases regression tests"
  "Error cases regression tests from file descriptor"
  "Error cases regression tests with entity substitution"
  "Error cases regression tests (old 1.0)"
  "SAX1 callbacks regression tests"
  "SAX2 callbacks regression tests"
  "SAX2 callbacks regression tests with entity substitution"
  "XML push regression tests"
  "XML push boundary tests"
  "xmlCopyEntity children test"
  "xml Entity values normalization"
)
: > "$OUT/failed.txt"
total=0
failed=0
for s in "${suites[@]}"; do
  log="$OUT/$(echo "$s" | tr -c 'A-Za-z0-9\n' _).log"
  # runtest picks every suite whose name holds the argument; keep the one
  # whose name is the argument.
  (cd "$X" && timeout 900 stdbuf -o0 -e0 "$OUT/runtest" -v --out "$OUT/tmp" "$s" > "$log" 2>&1) || true
  awk -v s="$s" '
    /^## / { cur = substr($0, 4); next }
    cur != s { next }
    /^File .* generated an error$/ { print s "\t" $2; bad = 1 }
    /^File .* leaked [0-9]* bytes$/ { print s "\t" $2 " (leak)"; bad = 1 }
    /^Ran [0-9]* tests, [0-9]* errors/ { if (!bad) print s "\t(whole suite)" }
    /^Ran [0-9]* tests/ { n = $2 }
    /^(Segmentation|Aborted|AddressSanitizer)/ { print s "\t(crashed)" }
    END { if (n == "") print s "\t(did not finish)" }
  ' "$log" >> "$OUT/failed.txt"
  n=$(awk -v s="$s" '/^## / { cur = substr($0, 4); next } cur == s && /^Ran [0-9]* tests/ { print $2 }' "$log")
  total=$((total + ${n:-0}))
done
sort -u -o "$OUT/failed.txt" "$OUT/failed.txt"
failed=$(wc -l < "$OUT/failed.txt")
echo "libxml2 runtest: $((total - failed)) of $total tests pass (${#suites[@]} suites)"
{ grep -v '^#' tests/c/libxml2-known-failures.txt 2>/dev/null || true; } | grep . | sort -u > "$OUT/known.txt"
new=$(comm -23 "$OUT/failed.txt" "$OUT/known.txt")
fixed=$(comm -13 "$OUT/failed.txt" "$OUT/known.txt")
status=0
if [ -n "$new" ]; then echo "  failing, not in tests/c/libxml2-known-failures.txt:"; echo "$new" | sed 's/^/    /'; status=1; fi
if [ -n "$fixed" ]; then echo "  passing now, remove from tests/c/libxml2-known-failures.txt:"; echo "$fixed" | sed 's/^/    /'; status=1; fi
exit $status
