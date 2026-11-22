#!/usr/bin/env bash
# Builds the library with the native C API (include/vdns.h) and runs
# tests/c/native.c under ASan and UBSan.
set -euo pipefail
cd "$(dirname "$0")/.."
T=${CARGO_TARGET_DIR:-$PWD/../../target}
cargo build --release --features capi
OUT=$T/ctest-dns
mkdir -p "$OUT"
${CC:-cc} -std=c99 -fsanitize=address,undefined -fno-sanitize-recover=undefined -g -Wall -Wextra -Werror \
    -I include -o "$OUT/native" tests/c/native.c "$T/release/libverilith_dns.a" -lpthread -ldl
"$OUT/native"
# The header is valid C++ too.
${CXX:-c++} -fsyntax-only -Wall -Wextra -Werror -x c++ include/vdns.h
