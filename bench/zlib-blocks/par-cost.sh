#!/usr/bin/env bash
# Instruction counts of par::compress by chunk size (results/par-chunk-work.tsv):
#   bench/zlib-blocks/par-cost.sh FILE...   (each file's first 4 MiB, level 6)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cargo build -q --release --manifest-path "$here/Cargo.toml" --bins
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
for f in "$@"; do
  head -c 4194304 "$f" > "$tmp/in"
  for c in 64 128 256 512 1024 4096; do
    ir=$(valgrind --tool=cachegrind --cache-sim=no --cachegrind-out-file=/dev/null \
      "$here/target/release/parone" "$tmp/in" 6 "$c" 2>&1 | grep -oP 'I\s+refs:\s+\K[0-9,]+' | tr -d ,)
    printf '%s\t%s\t%s\n' "$(basename "$f")" "$c" "$ir"
  done
done
