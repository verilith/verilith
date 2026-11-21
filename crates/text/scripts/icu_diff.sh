#!/bin/sh
# Builds the C API and diffs it against the system's ICU (libicuuc.so.74 by
# default; set ICU_LIB and ICU_SUFFIX for another version).
set -e
cd "$(dirname "$0")/.."
ICU_LIB=${ICU_LIB:-/usr/lib/x86_64-linux-gnu/libicuuc.so.74}
ICU_SUFFIX=${ICU_SUFFIX:-_74}
cargo build --profile release-fat
T=${CARGO_TARGET_DIR:-$PWD/../../target}/release-fat
cc -O2 -Wall -Iinclude -DICU_SUFFIX="$ICU_SUFFIX" tests/c/icu_diff.c \
    "$T/libverilith_text.a" "$ICU_LIB" -lm -lpthread -ldl -o "$T/icu_diff"
"$T/icu_diff" "${1:-200000}"
