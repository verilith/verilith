#!/bin/sh
# Builds tests/c/zdef.c against libverilith_zlib.a (zlib-abi), compresses every file
# given at several levels and window sizes, and checks the system zlib
# (tests/c/zpipe.c) decompresses each back to the file.
set -e
cd "$(dirname "$0")/../.."
cargo build --release --features zlib-abi
T=$(mktemp -d)
gcc -O2 tests/c/zpipe.c -o "$T/inf" -lz
gcc -O2 tests/c/zdef.c -o "$T/def" "${CARGO_TARGET_DIR:-$PWD/../../target}/release/libverilith_zlib.a" -lpthread -ldl -lm
for f in "$@"; do
    for opt in "-1 15" "0 15" "1 -15" "6 31" "9 15" "6 9"; do
        set -- $opt
        "$T/def" "$1" "$2" < "$f" > "$T/c"
        "$T/inf" "$2" < "$T/c" > "$T/d" 2>/dev/null
        cmp -s "$f" "$T/d" || { echo "DIFF $f level $1 wbits $2"; exit 1; }
    done
    echo "ok   $f"
done
