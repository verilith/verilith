#!/bin/bash
# Builds the libpng reference decoder. LIBPNG_DIR is a libpng source tree
# configured with CMake into $LIBPNG_DIR/build (libpng16.a, pnglibconf.h).
# The differential tests are run against libpng 1.6.59.
set -euo pipefail
cd "$(dirname "$0")"
: "${LIBPNG_DIR:=$HOME/ext/lp16}"
gcc -O2 -I "$LIBPNG_DIR" -I "$LIBPNG_DIR/build" refpng.c "$LIBPNG_DIR/build/libpng16.a" -lz -lm -o refpng
