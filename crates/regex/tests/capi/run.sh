#!/usr/bin/env bash
# Tests the C API. With RE2_PREFIX (an install prefix holding RE2 and
# Abseil) and CRE2_SRC (a checkout of github.com/marcomaggi/cre2), also
# builds tests/capi/cre2diff.c twice, against cre2 + RE2 and against vregex
# with the cre2-abi feature, and compares what they print on the fixed and
# N random cases (default 100000).
set -euo pipefail
cd "$(dirname "$0")/../.."
N=${1:-100000}
OUT=target/capi
mkdir -p "$OUT"
CC=${CC:-cc}
CXX=${CXX:-c++}
SYS="-lpthread -ldl -lm"

cargo build --profile release-abort
$CC -O1 -Iinclude tests/capi/test.c "${CARGO_TARGET_DIR:-$PWD/../../target}/release-abort/libverilith_regex.a" $SYS -o "$OUT/test"
"$OUT/test"

if [ -z "${RE2_PREFIX:-}" ] || [ -z "${CRE2_SRC:-}" ]; then
  echo "RE2_PREFIX and CRE2_SRC not set: skipping the comparison with cre2"
  exit 0
fi
cargo build --profile release-abort --features cre2-abi --target-dir target/cre2
export PKG_CONFIG_PATH="$RE2_PREFIX/lib/pkgconfig:$RE2_PREFIX/lib64/pkgconfig:${PKG_CONFIG_PATH:-}"
$CC -O1 -I"$CRE2_SRC/src" -c tests/capi/cre2diff.c -o "$OUT/cre2diff.o"
$CXX -O1 -std=c++17 -I"$CRE2_SRC/src" $(pkg-config --cflags re2) \
  -Dcre2_VERSION_INTERFACE_CURRENT=0 -Dcre2_VERSION_INTERFACE_REVISION=0 \
  -Dcre2_VERSION_INTERFACE_AGE=0 -Dcre2_VERSION_INTERFACE_STRING='"0.0.0"' \
  -c "$CRE2_SRC/src/cre2.cpp" -o "$OUT/cre2.o"
$CXX "$OUT/cre2diff.o" "$OUT/cre2.o" $(pkg-config --libs --static re2) -o "$OUT/cre2diff-re2"
$CC "$OUT/cre2diff.o" target/cre2/release-abort/libverilith_regex.a $SYS -o "$OUT/cre2diff-vregex"
python3 tests/diff/diff.py "$OUT/cre2diff-re2" "$OUT/cre2diff-vregex" --fuzz "$N" --seed "${SEED:-1}"
