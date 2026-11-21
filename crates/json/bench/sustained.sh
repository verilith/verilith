#!/usr/bin/env bash
# Like bench/run.sh, but each tool runs five times back to back before the
# other takes its turn (three rounds), so neither is measured right after
# the other on a vCPU whose clock drifts. Prints the best MB/s per tool.
# Both are pinned to one core (CPU, default 2).
# Usage: SIMDJSON=/path/to/simdjson bench/sustained.sh FILE...
set -euo pipefail
cd "$(dirname "$0")/.."
: "${SIMDJSON:?set SIMDJSON to a simdjson checkout}"
mkdir -p target/bench
g++ -O3 -march=native -std=c++17 -I"$SIMDJSON/singleheader" bench/simdjson_bench.cpp \
    "$SIMDJSON/singleheader/simdjson.cpp" -o target/bench/simdjson_bench
cargo build -q --profile release-abort --example like_for_like
for _ in 1 2 3; do
    for _ in 1 2 3 4 5; do taskset -c "${CPU:-2}" target/bench/simdjson_bench "$@" | sed 's/^/simdjson /'; done
    for _ in 1 2 3 4 5; do taskset -c "${CPU:-2}" "${CARGO_TARGET_DIR:-$PWD/../../target}/release-abort/examples/like_for_like" "$@" | sed 's/^/vjson /'; done
done | awk '{k=$1" "$2; if ($3>p[k]) p[k]=$3; if ($4>r[k]) r[k]=$4}
    END {printf "%-10s %-40s %10s %16s\n", "tool", "file", "parse MB/s", "parse+read MB/s";
         for (k in p) {split(k, a, " "); printf "%-10s %-40s %10d %16d\n", a[1], a[2], p[k], r[k]}}' | sort -k2,2 -k1,1
