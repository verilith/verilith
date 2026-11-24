#!/bin/bash
# Builds the giflib reference decoder against the system giflib (the
# libgif-dev package; GIFLIB_INCLUDE and GIFLIB_LIB to use another).
# The differential tests are run against giflib 5.2.2 as Debian and Ubuntu
# ship it, with the 2026 security fixes.
set -euo pipefail
cd "$(dirname "$0")"
gcc -O2 ${GIFLIB_INCLUDE:+-I "$GIFLIB_INCLUDE"} refgif.c ${GIFLIB_LIB:--lgif} -o refgif
