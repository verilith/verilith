#!/bin/sh
# Builds vurl's C API and ada (single-header, from $EXT/ada, default ~/ext),
# then runs the differential test. Usage: tests/capi/run.sh [corpus.txt]
set -e
here=$(cd "$(dirname "$0")" && pwd)
ada=${EXT:-$HOME/ext}/ada/singleheader
out=${OUT:-$here/../../target/capi}
mkdir -p "$out"
(cd "$here/../.." && cargo build --profile release-fat -q)
python3 "$here/vurl_h.py" "$ada/ada_c.h" > "$out/vurl_c.h"
[ "$out/ada.o" -nt "$ada/ada.cpp" ] || c++ -std=c++20 -O2 -DNDEBUG -c "$ada/ada.cpp" -I"$ada" -o "$out/ada.o"
cc -O1 -g -c "$here/diff.c" -I"$ada" -I"$out" -o "$out/diff.o"
c++ "$out/diff.o" "$out/ada.o" "${CARGO_TARGET_DIR:-$here/../../../../target}/release-fat/libverilith_url.a" -lpthread -ldl -o "$out/diff"
python3 "$here/gen_inputs.py" "$out/cases.bin" "$@"
"$out/diff" "$out/cases.bin" ${LIMIT:-200}
