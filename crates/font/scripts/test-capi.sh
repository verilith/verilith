#!/usr/bin/env bash
# Builds libverilith_font.a and runs the C and C++ interface tests against it.
set -euo pipefail
cd "$(dirname "$0")/.."
T=${CARGO_TARGET_DIR:-$PWD/../../target}
cargo build --release
cargo build --release --example testfont
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
"$T/release/examples/testfont" "$dir/font.ttf"
libs="$T/release/libverilith_font.a -lpthread -ldl -lm"
${CC:-cc} -std=c99 -Wall -Wextra -Werror -Iinclude tests/capi.c $libs -o "$dir/capi"
"$dir/capi" "$dir/font.ttf"
${CXX:-c++} -std=c++11 -Wall -Wextra -Werror -Iinclude tests/ots_shim.cc $libs -o "$dir/ots_shim"
"$dir/ots_shim" "$dir/font.ttf"
