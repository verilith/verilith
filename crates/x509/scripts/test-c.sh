#!/usr/bin/env bash
# Builds the library with the native C API (include/vx509.h) and runs
# tests/c/native.c over the seed certificates, under ASan and UBSan.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --profile release-fat --features capi
OUT=target/ctest
mkdir -p "$OUT"
SAN="-fsanitize=address,undefined -fno-sanitize-recover=undefined -g -Wall -Wextra -Werror"
${CC:-cc} $SAN -std=c99 -I include -o "$OUT/native" tests/c/native.c "${CARGO_TARGET_DIR:-$PWD/../../target}/release-fat/libverilith_x509.a"
"$OUT/native" fuzz/seeds/*.der
# The header is valid C++ too.
${CXX:-c++} -fsyntax-only -Wall -Wextra -Werror -x c++ include/vx509.h
