#!/usr/bin/env bash
# WebAssembly (wasm32): every crate is proven for 32-bit targets as well
# as 64-bit ones, and builds for wasm32-unknown-unknown (browsers,
# Cloudflare Workers). text, url, regex, json, xxhash, snappy, lz4, zstd,
# archive, png, font and wasm also pass their tests on wasm32-wasip1,
# under wasmtime (on PATH).
#   scripts/wasm32.sh             the builds and the tests
#   scripts/wasm32.sh build       the build checks only
#   (Verus for wasm32: each crate's scripts/verify-narrow.sh.)
set -euo pipefail
cd "$(dirname "$0")/.."

# Tested on wasm32-wasip1. (The tests that compare with a C library load it
# with dlopen, which wasip1 does not have, so there they skip; each of the
# compressors has round trips, and zstd libzstd's frames, that need no
# library. sync's tests spawn threads, which wasip1 does not have, so it
# is built only.)
TESTED="text url regex json xxhash snappy lz4 zstd archive png font wasm"

rustup target add wasm32-unknown-unknown wasm32-wasip1 > /dev/null

narrow=()
for d in crates/*/Cargo.toml; do
  c=$(basename "$(dirname "$d")")
  # The facade comes below.
  case "$c" in verilith) continue ;; esac
  narrow+=("$c")
done

echo "== build for wasm32-unknown-unknown: ${narrow[*]}"
cargo build --release --target wasm32-unknown-unknown $(printf -- '-p verilith-%s ' "${narrow[@]}")
# The facade crate, with every feature that builds there.
features=$(cargo metadata --format-version 1 --no-deps | python3 -c '
import json, sys
have = next(p for p in json.load(sys.stdin)["packages"] if p["name"] == "verilith")["features"]
print(",".join(c for c in sys.argv[1:] if c in have))' "${narrow[@]}")
cargo build --release --target wasm32-unknown-unknown -p verilith --features "$features"

[ "${1:-all}" = build ] && exit 0

# The tests read their data by absolute path (CARGO_MANIFEST_DIR), so the
# runner sees the whole file system. json's parser recurses once per
# nesting level, and its tests go to the 1000 levels RFC 8259 parsers
# commonly allow: about 400 KiB of native stack under wasmtime, close to
# wasmtime's 512 KiB default, so the tests run with 8 MiB (browsers give
# wasm about 1 MiB).
export CARGO_TARGET_WASM32_WASIP1_RUNNER="wasmtime run -W max-wasm-stack=8388608 --dir=/::/"
for c in $TESTED; do
  echo "== test $c on wasm32-wasip1"
  cargo test --release --target wasm32-wasip1 -p "verilith-$c" --lib --tests
done
