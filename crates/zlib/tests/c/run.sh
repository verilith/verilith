#!/bin/sh
# Builds tests/c/zpipe.c against the system zlib and against libverilith_zlib.a
# (zlib-abi) and checks they agree on every file given.
set -e
cd "$(dirname "$0")/../.."
cargo build --release --features zlib-abi
T=$(mktemp -d)
gcc -O2 tests/c/zpipe.c -o "$T/sys" -lz
gcc -O2 tests/c/zpipe.c -o "$T/vz" "${CARGO_TARGET_DIR:-$PWD/../../target}/release/libverilith_zlib.a" -lpthread -ldl -lm
for f in "$@"; do
    a=$("$T/sys" < "$f" 2>&1 | md5sum)
    b=$("$T/vz" < "$f" 2>&1 | md5sum)
    [ "$a" = "$b" ] && echo "ok   $f" || { echo "DIFF $f"; exit 1; }
done
