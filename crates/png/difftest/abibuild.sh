#!/bin/bash
# Builds difftest/abitest twice: abitest-libpng against libpng (LIBPNG_DIR, a
# libpng 1.6.59 tree, built with CMake into LIBPNG_BUILD with the drop-in's
# configuration, -DDFA_XTRA=include/vpng.dfa, so that both have the same
# pnglibconf.h) and
# abitest-vpng against verilith-png's libpng API (the static library built
# with the libpng-abi feature, and include/).
set -euo pipefail
cd "$(dirname "$0")"
: "${LIBPNG_DIR:=$HOME/ext/lp16}"
: "${LIBPNG_BUILD:=$LIBPNG_DIR/build-vpng}"
cmp -s "$LIBPNG_BUILD/pnglibconf.h" ../include/pnglibconf.h || { echo "$LIBPNG_BUILD is not configured with include/vpng.dfa" >&2; exit 1; }
T=${CARGO_TARGET_DIR:-$PWD/../../../target}
cargo build --release --features libpng-abi -q
gcc -O2 -Wall -I "$LIBPNG_DIR" -I "$LIBPNG_BUILD" abitest.c "$LIBPNG_BUILD/libpng16.a" -lz -lm -o abitest-libpng
gcc -O2 -Wall -I ../include abitest.c "$T/release/libverilith_png.a" -lm -lpthread -ldl -o abitest-vpng
