#!/bin/bash
# Builds the libtiff reference decoder against the system libtiff (the
# libtiff-dev package; LIBTIFF_INCLUDE and LIBTIFF_LIB to use another). The
# differential tests are run against libtiff 4.5.1 as Ubuntu 24.04 ships it.
set -euo pipefail
cd "$(dirname "$0")"
gcc -O2 ${LIBTIFF_INCLUDE:+-I "$LIBTIFF_INCLUDE"} reftiff.c ${LIBTIFF_LIB:--ltiff} -o reftiff
