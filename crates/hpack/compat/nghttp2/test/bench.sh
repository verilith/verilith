#!/usr/bin/env bash
# Builds bench.c against stock nghttp2 and against nghttp2 on vhpack and
# runs both. For numbers worth reporting, run on a quiet machine.
#
#   compat/nghttp2/test/bench.sh NGHTTP2_LIB_DIR [ROUNDS]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
lib=$(cd "$1" && pwd)
T=${CARGO_TARGET_DIR:-$root/../../target}
out=$T/nghttp2-bench
rm -rf "$out" && mkdir -p "$out/stock" "$out/vh"
cp -r "$lib"/. "$out/stock/"
cp -r "$lib"/. "$out/vh/"
python3 "$here/../patch.py" "$out/vh" > /dev/null
cargo build -q --profile release-abort --manifest-path "$root/Cargo.toml"
CC=${CC:-cc}
FLAGS="-O2 -DNDEBUG -DNGHTTP2_STATICLIB -DHAVE_ARPA_INET_H -DHAVE_NETINET_IN_H -w"
$CC $FLAGS -I"$out/stock/includes" -I"$out/stock" "$here/bench.c" "$out"/stock/*.c -o "$out/bench-stock"
$CC $FLAGS -DNGHTTP2_VHPACK -I"$out/vh/includes" -I"$out/vh" "$here/bench.c" "$out"/vh/*.c \
    "$T/release-abort/libverilith_hpack.a" -lpthread -ldl -lm -o "$out/bench-vhpack"
echo -n "nghttp2: "; "$out/bench-stock" "${2:-500}"
echo -n "vhpack:  "; "$out/bench-vhpack" "${2:-500}"
