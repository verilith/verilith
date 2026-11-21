#!/bin/sh
# Builds and runs the differential test against google/brotli.
#   BROTLI=/path/to/brotli (source tree, built with cmake into $BROTLI/out)
#   tests/c/run.sh [iterations] [seed]
set -e
cd "$(dirname "$0")/../.."
B=${BROTLI:-$HOME/build/brotli}
cargo build --release --quiet
OUT=${CARGO_TARGET_DIR:-$PWD/../../target}/release
cc -O2 -g -I"$B/c/include" tests/c/diff.c "$OUT/libverilith_brotli.a" \
  "$B/out/libbrotlienc.a" "$B/out/libbrotlidec.a" "$B/out/libbrotlicommon.a" \
  -lpthread -ldl -lm -o "$OUT/diff"
"$OUT/diff" "$@"
