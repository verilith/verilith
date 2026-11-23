#!/usr/bin/env bash
# WebAssembly (wasm32): the crates proven without a fixed pointer width
# build for wasm32-unknown-unknown (browsers, Cloudflare Workers), and the
# ones proven for 64-bit targets only stop with their own compile_error!.
# text, url and regex also pass their tests on wasm32-wasip1, under
# wasmtime (on PATH).
#   scripts/wasm32.sh             the builds and the tests
#   scripts/wasm32.sh build       the build checks only
#   (Verus for wasm32: each crate's scripts/verify-narrow.sh.)
set -euo pipefail
cd "$(dirname "$0")/.."

# Proven with `global size_of usize == 8`: 64-bit targets only.
WIDE="archive font json lz4 png snappy sync wasm xxhash zstd"
# Tested on wasm32-wasip1.
TESTED="text url regex"

rustup target add wasm32-unknown-unknown wasm32-wasip1 > /dev/null

narrow=()
for d in crates/*/Cargo.toml; do
  c=$(basename "$(dirname "$d")")
  # The facade, and bind (its JSON part is 64-bit only), come below.
  case "$c" in verilith | bind) continue ;; esac
  case " $WIDE " in *" $c "*) ;; *) narrow+=("$c") ;; esac
done

echo "== build for wasm32-unknown-unknown: ${narrow[*]}"
cargo build --release --target wasm32-unknown-unknown $(printf -- '-p verilith-%s ' "${narrow[@]}")
cargo build --release --target wasm32-unknown-unknown -p verilith-bind --no-default-features --features url,text
# The facade crate, with every feature that builds there.
features=$(cargo metadata --format-version 1 --no-deps | python3 -c '
import json, sys
have = next(p for p in json.load(sys.stdin)["packages"] if p["name"] == "verilith")["features"]
print(",".join(c for c in sys.argv[1:] if c in have))' "${narrow[@]}")
cargo build --release --target wasm32-unknown-unknown -p verilith --features "$features"

status=0
for c in $WIDE; do
  log=$(cargo build --target wasm32-unknown-unknown -p "verilith-$c" 2>&1 || true)
  if echo "$log" | grep -q "error: .* is proven for 64-bit targets only"; then
    echo "ok   $c: refused with its compile_error!"
  else
    echo "FAIL $c: a wasm32 build did not stop at the 64-bit compile_error!"
    echo "$log" | grep -E "^error" | head -5
    status=1
  fi
done
[ $status -eq 0 ] || exit 1
[ "${1:-all}" = build ] && exit 0

# The tests read their data by absolute path (CARGO_MANIFEST_DIR), so the
# runner sees the whole file system.
export CARGO_TARGET_WASM32_WASIP1_RUNNER="wasmtime run --dir=/::/"
for c in $TESTED; do
  echo "== test $c on wasm32-wasip1"
  cargo test --release --target wasm32-wasip1 -p "verilith-$c" --lib --tests
done
