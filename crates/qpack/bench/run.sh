#!/usr/bin/env bash
# vqpack against ls-qpack (v2.7.1): compressed size, encode and decode time
# per field section. Fetches ls-qpack into bench/ext on first use, builds
# both with the native CPU's instructions, and runs pinned to one core when
# taskset is there. BENCH_REPS=<n> (default 200) and BENCH_ONLY=<substring>
# pass through; BENCH_PORTABLE=1 builds without -march=native.
set -euo pipefail
cd "$(dirname "$0")"
if [ ! -f ext/ls-qpack/lsqpack.c ]; then
    mkdir -p ext
    git clone -q --depth 1 --branch v2.7.1 --recurse-submodules \
        https://github.com/litespeedtech/ls-qpack ext/ls-qpack
fi
if [ -z "${BENCH_PORTABLE:-}" ]; then
    export RUSTFLAGS="${RUSTFLAGS:-} -C target-cpu=native"
fi
cargo build -q --release
pin=()
if command -v taskset >/dev/null; then pin=(taskset -c "${BENCH_CPU:-2}"); fi
"${pin[@]}" target/release/vqpack-bench
