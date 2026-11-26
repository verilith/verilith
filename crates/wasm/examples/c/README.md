# C API examples

`hello.c`, `callback.c`, `multi.c` and `trap.c` (with their `.wasm`
files) are unmodified copies of the examples in
[WebAssembly/wasm-c-api](https://github.com/WebAssembly/wasm-c-api) at
commit 9d6b93764ac96cdd9db51081c363e09d2d488b4d (Apache-2.0), as is
`include/wasm.h`. `scripts/capi.sh` builds each against `libverilith_wasm.a` and
checks that it runs to completion.

`limits.c` is ours: it uses the fuel and memory limits that
`include/verilith.h` adds to the API.
