#!/usr/bin/env bash
# Builds diff.c against stock nghttp2 and against nghttp2 on vhpack, runs
# both on the same seeds and fails unless every output is identical.
#
#   compat/nghttp2/test/run.sh NGHTTP2_LIB_DIR [SEEDS] [CASES]
#
# NGHTTP2_LIB_DIR: nghttp2's lib/ (1.70.0, or Node 24's deps/nghttp2/lib).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
lib=$(cd "$1" && pwd)
seeds=${2:-20}
cases=${3:-500}
T=${CARGO_TARGET_DIR:-$root/../../target}
out=$T/nghttp2-diff
rm -rf "$out" && mkdir -p "$out/stock" "$out/vh"
cp -r "$lib"/. "$out/stock/"
cp -r "$lib"/. "$out/vh/"
python3 "$here/../patch.py" "$out/vh" > /dev/null
cargo build -q --profile release-abort --manifest-path "$root/Cargo.toml"
CC=${CC:-cc}
FLAGS="-O1 -g -fsanitize=address,undefined -DNGHTTP2_STATICLIB -DHAVE_ARPA_INET_H -DHAVE_NETINET_IN_H -w"
srcs() { ls "$1"/*.c; }
$CC $FLAGS -I"$out/stock/includes" -I"$out/stock" "$here/diff.c" $(srcs "$out/stock") -o "$out/diff-stock"
$CC $FLAGS -DNGHTTP2_VHPACK -I"$out/vh/includes" -I"$out/vh" "$here/diff.c" $(srcs "$out/vh") \
    "$T/release-abort/libverilith_hpack.a" -lpthread -ldl -lm -o "$out/diff-vhpack"
status=0
for s in $(seq 1 "$seeds"); do
    "$out/diff-stock" "$s" "$cases" > "$out/a.txt"
    "$out/diff-vhpack" "$s" "$cases" > "$out/b.txt"
    if ! cmp -s "$out/a.txt" "$out/b.txt"; then
        echo "seed $s: outputs differ"; diff "$out/a.txt" "$out/b.txt" | head -20; status=1
    fi
done
echo "seeds: $seeds x $cases cases; fields emitted: $(grep -c '^n ' "$out/a.txt") (last seed); errors: $(grep -c '^error' "$out/a.txt") (last seed)"
exit $status
