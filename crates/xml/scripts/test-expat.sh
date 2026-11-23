#!/usr/bin/env bash
# libexpat's own tests against verilith-xml's expat ABI (feature expat-abi):
#
#  1. tests/runtests: expat's unit tests (443 tests, each run at six chunk
#     sizes, with reparse deferral on and off), built from libexpat 2.10.0's
#     sources and linked against libverilith_xml.a in place of libexpat.
#     tests/c/expat_internals.c stands in for the few libexpat internals the
#     suite also links (each fails the test that calls it).
#  2. tests/xmltest.sh: xmlwf, libexpat's command-line tool, built the same
#     way, over the W3C XML Conformance Test Suite (verdicts, and canonical
#     output against expat's expected files).
#
# A test outside tests/c/expat-known-failures.txt that fails, fails this
# script; so does one in that list that now passes (remove it).
#   scripts/test-expat.sh XMLCONF_DIR
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
XMLCONF=${1:?usage: scripts/test-expat.sh XMLCONF_DIR}
E=$(scripts/fetch-expat.sh)
P=$(../../scripts/profile xml)
cargo build -q --profile "$P" --features expat-abi
LIB=${CARGO_TARGET_DIR:-$ROOT/../../target}/$P/libverilith_xml.a
LIBS="-lm -lpthread -ldl"
OUT=$ROOT/target/expat-tests
rm -rf "$OUT"
mkdir -p "$OUT"
CC=${CC:-cc}
SAN="-fsanitize=address,undefined -g"
# expat's build configuration, as its CMake build writes it for this system.
cat > "$OUT/expat_config.h" <<'EOF'
#define XML_DTD 1
#define XML_GE 1
#define XML_NS 1
#define XML_CONTEXT_BYTES 1024
#define BYTEORDER 1234
#define HAVE_UNISTD_H 1
#define HAVE_FCNTL_H 1
#define HAVE_MMAP 1
#define HAVE_GETPAGESIZE 1
#define PACKAGE_NAME "expat"
#define PACKAGE_VERSION "2.10.0"
EOF
CFLAGS="-O1 -w -DHAVE_EXPAT_CONFIG_H -I$OUT -I$E/lib -I$E/tests"
status=0

# 1. runtests
t=$E/tests
$CC $SAN $CFLAGS -DXML_TESTING -o "$OUT/runtests" \
  "$t"/{runtests,acc_tests,alloc_tests,basic_tests,chardata,common,dummy,entities_tests,handlers,hash_tests}.c \
  "$t"/{memcheck,minicheck,misc_tests,ns_tests,nsalloc_tests,props_tests,structdata,xcs_tests}.c \
  "$E/lib/xcs.c" tests/c/expat_internals.c "$LIB" $LIBS
(cd "$OUT" && ASAN_OPTIONS=detect_leaks=0 ./runtests -v > runtests.log 2> runtests.err) || true
{ grep -o '^FAIL \[[^]]*\]: [a-z0-9_]*' "$OUT/runtests.log" || true; } | awk '{print $NF}' | sort -u > "$OUT/runtests-failed.txt"
{ grep -o '^PASS: [a-z0-9_]*' "$OUT/runtests.log" || true; } | awk '{print $2}' | sort -u > "$OUT/runtests-passed.txt"
total=$(cat "$OUT/runtests-failed.txt" "$OUT/runtests-passed.txt" | sort -u | wc -l)
failed=$(wc -l < "$OUT/runtests-failed.txt")
echo "expat runtests: $((total - failed)) of $total tests pass in every mode"
{ grep -v '^#' tests/c/expat-known-failures.txt || true; } | awk -F'\t' '$1 == "runtests" {print $2}' | sort -u > "$OUT/runtests-known.txt"
new=$(comm -23 "$OUT/runtests-failed.txt" "$OUT/runtests-known.txt")
fixed=$(comm -13 "$OUT/runtests-failed.txt" "$OUT/runtests-known.txt")
if [ -n "$new" ]; then echo "  failing, not in tests/c/expat-known-failures.txt:"; echo "$new" | sed 's/^/    /'; status=1; fi
if [ -n "$fixed" ]; then echo "  passing now, remove from tests/c/expat-known-failures.txt:"; echo "$fixed" | sed 's/^/    /'; status=1; fi

# 2. xmltest.sh, through xmlwf
w=$E/xmlwf
$CC $SAN $CFLAGS -o "$OUT/xmlwf" "$w"/{xmlwf,xmlfile,codepage,unixfilemap}.c "$E/lib/xcs.c" "$LIB" $LIBS
mkdir -p "$OUT/xt/tests"
cp "$t/xmltest.sh" "$t/udiffer.py" "$OUT/xt/tests/"
ln -s "$XMLCONF" "$OUT/xt/tests/xmlconf"
(cd "$OUT/xt" && ASAN_OPTIONS=detect_leaks=0 bash tests/xmltest.sh "$OUT/xmlwf" > "$OUT/xmltest.log" 2>&1) || true
tail -2 "$OUT/xmltest.log" | sed 's/^/expat xmltest.sh: /'
{ grep -E '^(Expected not well-formed|Output differs|In )' "$OUT/xmltest.log" || true; } | sed 's/^In \([^:]*\):.*/In \1/' | sort -u > "$OUT/xmltest-failed.txt"
{ grep -v '^#' tests/c/expat-known-failures.txt || true; } | awk -F'\t' '$1 == "xmltest" {print $2}' | sort -u > "$OUT/xmltest-known.txt"
new=$(comm -23 "$OUT/xmltest-failed.txt" "$OUT/xmltest-known.txt")
fixed=$(comm -13 "$OUT/xmltest-failed.txt" "$OUT/xmltest-known.txt")
if [ -n "$new" ]; then echo "  failing, not in tests/c/expat-known-failures.txt:"; echo "$new" | sed 's/^/    /'; status=1; fi
if [ -n "$fixed" ]; then echo "  passing now, remove from tests/c/expat-known-failures.txt:"; echo "$fixed" | sed 's/^/    /'; status=1; fi
exit $status
