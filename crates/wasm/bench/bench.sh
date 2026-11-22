#!/bin/sh
# Runs the benchmark kernels on vwasm, wasmi, Wasmtime, wasm3 and WAMR and
# prints a Markdown table of the best of $RUNS wall-clock times (whole
# process: decode, validate/compile, instantiate, run).
#
# Pinned engines: wasmi 2.0.2 and Wasmtime 51.0.0 (Cranelift) through
# runner/, wasm3 v0.9.0, WAMR WAMR-2.4.6 (fast interpreter, no JIT/AOT).
set -e
cd "$(dirname "$0")"
RUNS=${RUNS:-3}
ENGINES=${ENGINES:-/tmp/vwasm-engines}
mkdir -p "$ENGINES"
if [ ! -x "$ENGINES/wasm3/build/wasm3" ]; then
    git clone -q --depth 1 --branch v0.9.0 https://github.com/wasm3/wasm3.git "$ENGINES/wasm3"
    (cd "$ENGINES/wasm3" && mkdir -p build && cd build &&
        cmake -DCMAKE_BUILD_TYPE=Release -DBUILD_WASI=simple .. >/dev/null && make -j8 >/dev/null)
fi
IWASM="$ENGINES/wasm-micro-runtime/product-mini/platforms/linux/build/iwasm"
if [ ! -x "$IWASM" ]; then
    git clone -q --depth 1 --branch WAMR-2.4.6 https://github.com/bytecodealliance/wasm-micro-runtime.git \
        "$ENGINES/wasm-micro-runtime"
    (cd "$ENGINES/wasm-micro-runtime/product-mini/platforms/linux" && mkdir -p build && cd build &&
        cmake -DCMAKE_BUILD_TYPE=Release -DWAMR_BUILD_FAST_INTERP=1 -DWAMR_BUILD_JIT=0 -DWAMR_BUILD_AOT=0 \
            -DWAMR_BUILD_LIBC_WASI=0 .. >/dev/null && make -j8 >/dev/null)
fi
(cd kernels && RUSTFLAGS="-C target-cpu=mvp" cargo build -q --release --target wasm32-unknown-unknown)
# vwasm with the repository's flags (.cargo/config.toml); wasmi and
# Wasmtime as their users build them, with no extra flags.
(cd runner && cargo build -q --release)
(cd runner && RUSTFLAGS="" CARGO_TARGET_DIR=target/plain cargo build -q --release)
K=kernels/target/wasm32-unknown-unknown/release/kernels.wasm
R=runner/target/release/runner
RP=runner/target/plain/release/runner

best() {
    b=""
    for _ in $(seq "$RUNS"); do
        s=$(date +%s%N)
        "$@" >/dev/null 2>&1 || { echo "fail"; return; }
        e=$(date +%s%N)
        t=$(( (e - s) / 1000000 ))
        if [ -z "$b" ] || [ "$t" -lt "$b" ]; then b=$t; fi
    done
    echo "$b"
}

echo "| kernel | vwasm | wasmi | wasm3 | WAMR (fast interp) | Wasmtime (JIT) |"
echo "|---|---:|---:|---:|---:|---:|"
for spec in "fib 32" "sieve 4000000 10" "matmul 200 2" "sort 1000000 2" "crc32 10" "sha256 2"; do
    set -- $spec
    f=$1
    shift
    v=$(best $R vwasm $K $f "$@")
    wi=$(best $RP wasmi $K $f "$@")
    wt=$(best $RP wasmtime $K $f "$@")
    w3=$(best "$ENGINES/wasm3/build/wasm3" --func $f $K "$@")
    iw=$(best "$IWASM" -f $f $K "$@")
    echo "| $spec | $v ms | $wi ms | $w3 ms | $iw ms | $wt ms |"
done
