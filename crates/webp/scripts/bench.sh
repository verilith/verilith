#!/usr/bin/env bash
# Benchmarks vwebp against libwebp: each decoder in its own process, pinned to
# one core, best of ITERS. Needs difftest/bench built (make -C difftest bench).
#   scripts/bench.sh [CORE] [ITERS] FILE...
set -euo pipefail
cd "$(dirname "$0")/.."
core=${1:-2}; iters=${2:-20}; shift 2
taskset -c "$core" ./difftest/bench libwebp "$iters" "$@"
taskset -c "$core" ./difftest/bench vwebp "$iters" "$@"
