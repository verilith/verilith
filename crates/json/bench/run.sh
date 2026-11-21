#!/usr/bin/env bash
# Like-for-like benchmark against simdjson: parse only, and parse then read
# every value. Usage: SIMDJSON=/path/to/simdjson bench/run.sh FILE...
# Runs the two alternately five times; take the best of each.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${SIMDJSON:?set SIMDJSON to a simdjson checkout}"
mkdir -p target/bench
g++ -O3 -march=native -std=c++17 -I"$SIMDJSON/singleheader" bench/simdjson_bench.cpp \
    "$SIMDJSON/singleheader/simdjson.cpp" -o target/bench/simdjson_bench
cargo build -q --profile release-abort --example like_for_like
echo "file  MB/s(parse)  MB/s(parse+read)"
for _ in 1 2 3 4 5; do
    echo "-- simdjson"; target/bench/simdjson_bench "$@" | cut -d' ' -f1-3
    echo "-- vjson";    "${CARGO_TARGET_DIR:-$PWD/../../target}/release-abort/examples/like_for_like" "$@" | cut -d' ' -f1-3
done
