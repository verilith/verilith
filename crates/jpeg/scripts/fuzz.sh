#!/bin/bash
# Differential fuzzing of vjpeg against libjpeg-turbo with libFuzzer.
# Usage: scripts/fuzz.sh SECONDS CORPUS_DIR [SEED_DIR...]
# Needs clang, and LIBJPEG_SRC / LIBJPEG_BUILD as in difftest/Makefile.
# libjpeg-turbo runs its C code, not its SIMD code (JSIMD_FORCENONE): the two
# differ on coefficients too large for 16-bit arithmetic, and vjpeg's
# specification is the C code's.
set -e
cd "$(dirname "$0")/.."
secs=${1:-60}; corpus=${2:-fuzz-corpus}; shift 2 || true
LIBJPEG_SRC=${LIBJPEG_SRC:-$HOME/ext/libjpeg-turbo}
LIBJPEG_BUILD=${LIBJPEG_BUILD:-$HOME/ext/ljtbuild}
# vjpeg with libFuzzer's coverage instrumentation and overflow checks.
RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-level=3 \
  -Cllvm-args=-sanitizer-coverage-inline-8bit-counters -Cllvm-args=-sanitizer-coverage-pc-table \
  -Cllvm-args=-sanitizer-coverage-trace-compares -Cdebug-assertions -Coverflow-checks" \
  cargo build --release --target-dir target/fuzz --target x86_64-unknown-linux-gnu
clang -O1 -g -DFUZZ -fsanitize=fuzzer,address -I"$LIBJPEG_SRC/src" -I"$LIBJPEG_BUILD" -o target/fuzz/fuzz_diff \
  difftest/diff.c target/fuzz/x86_64-unknown-linux-gnu/release/libverilith_jpeg.a "$LIBJPEG_BUILD/libjpeg.a" -lpthread -lm -ldl
mkdir -p "$corpus"
JSIMD_FORCENONE=1 target/fuzz/fuzz_diff ${FUZZ_FLAGS:-} -max_total_time="$secs" -max_len=65536 -rss_limit_mb=4096 \
  -timeout=30 -print_final_stats=1 "$corpus" "$@"
