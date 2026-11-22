# Benchmarks

`bench.sh` builds the kernels in `kernels/` (Rust, `no_std`, compiled to
`wasm32-unknown-unknown` with `-C target-cpu=mvp`), the `runner/` command
line for verilith-wasm, wasmi 2.0.2 and Wasmtime 51.0.0, and the C engines at
pinned tags (wasm3 v0.9.0; WAMR WAMR-2.4.6 built as a fast interpreter
without JIT or AOT), then prints the best of `RUNS` (default 3) wall-clock
times of the whole process for each kernel and engine. Every engine is
timed the same way, so the numbers include decoding, validation or
compilation and instantiation; the kernels are sized so that these are
small next to the run itself, except for Wasmtime, whose compile time is
part of its numbers.

The table in the top-level README was produced by `RUNS=3 ./bench.sh`
on an Intel Xeon @ 2.10GHz (4 vCPUs), Ubuntu 24.04, rustc 1.97.0.
