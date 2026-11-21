#!/bin/sh
# Builds the wasm-c-api examples against libverilith_wasm.a and runs them.
set -e
cd "$(dirname "$0")/.."
cargo build -q --release
out=$(mktemp -d)
for e in hello callback multi trap; do
    ${CC:-cc} -O1 -Iinclude examples/c/$e.c "${CARGO_TARGET_DIR:-$PWD/../../target}/release/libverilith_wasm.a" -lpthread -ldl -lm -o "$out/$e"
    (cd examples/c && "$out/$e" > "$out/$e.log" 2>&1) || { cat "$out/$e.log"; exit 1; }
    tail -1 "$out/$e.log" | grep -q "^Done.$" || { cat "$out/$e.log"; exit 1; }
    echo "$e: ok"
done
