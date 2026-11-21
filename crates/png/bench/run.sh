#!/bin/bash
# Runs every decoder in its own process over DIR, one after another.
# Usage: bench/run.sh DIR [ROUNDS]
cd "$(dirname "$0")"
cargo build --release -q || exit 1
for fmt in rgba8 native; do
  for d in vpng libpng spng png zune; do
    taskset -c 2 target/release/vpng-bench $d $fmt "$1" ${2:-10}
  done
done
