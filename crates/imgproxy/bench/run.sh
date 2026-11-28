#!/usr/bin/env bash
# Builds both benchmarks and runs them on the files given, one thread
# each: a 300x300 fit thumbnail as PNG.
#   bench/run.sh [ROUNDS] FILE...
set -euo pipefail
cd "$(dirname "$0")"
rounds=${1:-15}; shift
cargo build --release -q
cc -O2 -o target/vips-bench vips.c $(pkg-config --cflags --libs vips)
printf 'file\tengine\tmedian_ms\tmin_ms\tpng_bytes\n'
taskset -c 1 ./target/release/imgproxy-bench 300 300 "$rounds" "$@"
taskset -c 1 ./target/vips-bench thumbnail 300 300 "$rounds" "$@"
taskset -c 1 ./target/vips-bench resize 300 300 "$rounds" "$@"
