#!/bin/bash
# Differential fuzzing of vwebp against libwebp with libFuzzer.
# Usage: scripts/fuzz.sh SECONDS CORPUS_DIR [SEED_DIR...]
# Needs clang, and LIBWEBP_SRC / LIBWEBP_BUILD as in difftest/Makefile.
set -e
cd "$(dirname "$0")/.."
secs=${1:-60}; corpus=${2:-fuzz-corpus}; shift 2 || true
LIBWEBP_SRC=${LIBWEBP_SRC:-$HOME/ext/libwebp}
LIBWEBP_BUILD=${LIBWEBP_BUILD:-$HOME/ext/lwbuild}
# vwebp with libFuzzer's coverage instrumentation and overflow checks.
RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=3 \
  -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table \
  -Cllvm-args=-sanitizer-coverage-trace-compares -Cdebug-assertions -Coverflow-checks" \
  cargo build --release --target-dir target/fuzz --target x86_64-unknown-linux-gnu
clang -O1 -g -DFUZZ -fsanitize=fuzzer,address -I"$LIBWEBP_SRC/src" -o target/fuzz/fuzz_diff difftest/diff.c \
  target/fuzz/x86_64-unknown-linux-gnu/release/libverilith_webp.a "$LIBWEBP_BUILD/libwebp.a" "$LIBWEBP_BUILD/libsharpyuv.a" -lpthread -lm -ldl
mkdir -p "$corpus"
target/fuzz/fuzz_diff ${FUZZ_FLAGS:-} -max_total_time="$secs" -max_len=65536 -rss_limit_mb=4096 -timeout=30 \
  -print_final_stats=1 "$corpus" "$@"
