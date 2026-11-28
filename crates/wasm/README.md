# verilith-wasm

A WebAssembly interpreter in Rust whose sandbox is proven with
[Verus](https://github.com/verus-lang/verus). A guest module can only
reach its own linear memory, globals, tables and value stack, and every
step the interpreter takes is the step a formal semantics of WebAssembly
takes. Neither fact depends on the binary decoder, the validator or the
linker being correct: their output is checked by verified code before
anything runs. An embedder can bound how long a guest runs (fuel) and how
much memory it takes (a cap), so an untrusted module can neither hang the
host nor exhaust its memory ([Resource limits](#resource-limits)).

The WebAssembly 2.0 spec tests pass where verilith-wasm implements the feature
(24,295 of 24,721 directives), and differential testing against wasmi on
87,000 generated modules found no difference. It runs a register form of
each function, translated by unverified code and checked by verified code,
at 0.81 to 1.03 times wasmi's time and 1.04 to 1.47 times wasm3's on the
benchmarks below (the stack interpreter it replaced took 2.5 to 3.4 times
wasmi's, in an earlier run).

**Verification status.** `cargo verus verify` checks 779 functions with
no errors (about 5 minutes with two threads on a 4-core Linux VM, for
both a 64-bit and a 32-bit target). The translation to register form (`src/reg.rs`) is mostly marked
`external_body` (its small leaf helpers are verified for panics and
overflow): it is untrusted, and only the checker's verdict on its
output matters.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety of the interpreter: every access to linear memory, the value stack, globals, tables and code is in bounds; no overflow, no panics | every verified function (Verus checks all indexing and arithmetic; raw accesses go through `src/prims.rs`, whose `requires` is the bounds check) |
| Checker soundness: if `check_certs` accepts a module's stack-height certificates, every function satisfies `func_cert_ok` | `check::check_certs` |
| Progress and preservation: from any configuration satisfying the invariant, the semantics never gets stuck, and the next configuration satisfies the invariant again (or is a host call with well-typed arguments, which resumes to one) | `preserve::lemma_step`, `preserve::lemma_resume` |
| Refinement: the interpreter computes what the semantics computes. `execute` returns ghost `(hs, n)` such that running the semantics for `n` steps, with `hs` the host's responses (the store each host call left behind), ends with exactly the interpreter's result values or trap and exactly its store. `hs` also records whether each `memory.grow` got its memory. If the interpreter stops with `Exhausted` (call depth, stack limit or fuel), the semantics is still running with that store | `run::execute`, against `sem::run` (`run::executed`) |
| Branch resolution: the compiled code's precomputed branch targets, frame sizes and arities are the certificate's | `compile::compile_all` ensures `interp::codes_ok` |
| Register form: every operation computes, on every value stack, what the run of instructions it stands for computes on the flat machine; runs partition the body and start at every branch target | `rcheck::check_rcode` ensures `rcheck::rcode_ok` (part of `codes_ok`); `mach::lemma_msteps` carries the flat machine over to the semantics |
| Snapshots: `Checked::snapshot` copies the store, and `Checked::restore` puts it back (memory contents and size, globals, tables, dropped segments), so an embedder can start every call from the same state ([verilith-serverless](../serverless) does, per request) | `instance::Checked::restore` ensures `view() == snap.view()` |
| The boundary holds for any caller: a `Checked` instance can only be built by `Checked::new`, which runs the checker, compiles, and checks the initial store; its type invariant (checked certificates, compiled code, a well-formed store, a fixed-size value stack) is what `execute` requires, so every call from unverified code runs under the theorems above | `instance::Checked` (`#[verifier::type_invariant]`) |

The semantics (`src/sem.rs`) is a small-step machine over the decoded
module: per-frame operand stacks and label stacks, untyped 64-bit value
slots (an `i32` is the low half of its slot), structured control with
`end`/`else` positions resolved by the decoder, and host calls as a step
that waits for the embedder. A `memory.grow` within the maximum is a
step with two outcomes, the grown memory or -1, because the
specification (§4.4.7) lets it fail whenever the host cannot provide the
memory; the interpreter takes the second when allocation fails, and the
run's `hs` records which one each grow took. It follows the WebAssembly 2.0 core
specification (§4) for the instructions verilith-wasm implements. It is written
for this project and is not mechanically related to the official
specification or to WasmCert; the spec tests are what tie it to the
standard.

Why certificates: the validator, which is the most intricate part of a
WebAssembly engine, is not verified. It produces, for every function, the
operand-stack height and innermost label at each instruction (or marks it
dead), and `src/check.rs` checks that table one instruction at a time. The
progress/preservation proof is about certified code, so a validator bug
can make verilith-wasm reject a valid module, or accept an invalid one that then
still runs inside the sandbox, but never let a guest out. The same
certificate is what lets the interpreter run without a label stack and
without a bounds check on any operand push or pop: a call checks once
that the callee's whole frame fits.

### Trusted base

What the proofs assume rather than prove:

- `src/sem.rs`: the semantics. Review it against the WebAssembly 2.0
  specification.
- `src/fops.rs`: floating point. The semantics leaves float operations
  uninterpreted (`f_un`, `f_bin`, `f_cmp`, `cvt`), so the proofs say the
  interpreter applies the right operation to the right operands; that the
  Rust implementation of each operation (NaN propagation, `min`/`max`,
  rounding, the trapping and saturating truncations) matches IEEE 754 and
  WebAssembly is checked by the spec tests (`f32`, `f64`, `conversions`,
  `float_exprs`, `float_misc` all pass).
- `src/sint.rs`: nothing of its own. Signed division and remainder,
  arithmetic shifts, signed comparison, sign extension, `clz`, `ctz` and
  `popcnt` are verified against `src/num.rs` and vstd's specs of
  `leading_zeros`, `trailing_zeros` and `count_ones`. `tests/sint.rs` checks
  every function against an independent evaluation of the spec.
- `src/prims.rs`: unchecked loads and stores on linear memory (`load`,
  `store`, 1 to 8 bytes little-endian); each `requires` is the bounds
  check Verus proves at the call site. (The single-element reads and
  writes are verified against vstd's spec of `get_unchecked`; the copies
  and fills `scopy_down`, `szero`, `fill`, `copy_within` and `copy_in`
  against its specs of `copy_within`, `copy_from_slice` and
  `get_unchecked_mut`; and `try_grow`, which appends zeroed pages or
  reports that the allocation failed and leaves the memory unchanged,
  against its specs of `try_reserve_exact` and `resize`.)
- `interp::call_host` (it calls the embedder's host function, catching a
  panic as a trap, and is trusted to leave the lengths of the result
  buffer and memory unchanged, which a `&mut [T]` guarantees) and
  `Checked::memory_mut` (hands out the memory as `&mut [u8]`, which cannot
  change its length).
- Verus, Z3 and the Rust compiler.

Not trusted (their output is checked, so a bug costs correctness, not
isolation): the decoder (`src/decode.rs`), the validator
(`src/validate.rs`), the translation to register form (`src/reg.rs`,
whose output `check_rcode` checks; a rejected translation falls back to
running every instruction as a stack instruction), linking and
instantiation (`src/api.rs`, which builds the initial store that
`check_store` then checks), and the C API adapter (`src/capi.rs`).

## Using it

```rust
use verilith_wasm::{Instance, Linker, Module, Val, ValType};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // (module (import "env" "log" (func (param i32)))
    //   (func (export "run") (param i32) (result i32)
    //     (call 0 (local.get 0)) (i32.add (local.get 0) (i32.const 1))))
    let wasm_bytes = [
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // magic, version
        0x01, 0x0a, 0x02, 0x60, 0x01, 0x7f, 0x00, 0x60, 0x01, 0x7f, 0x01, 0x7f, // types
        0x02, 0x0b, 0x01, 0x03, b'e', b'n', b'v', 0x03, b'l', b'o', b'g', 0x00, 0x00, // import
        0x03, 0x02, 0x01, 0x01, // functions
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x01, // export
        0x0a, 0x0d, 0x01, 0x0b, 0x00, 0x20, 0x00, 0x10, 0x00, 0x20, 0x00, 0x41, 0x01, 0x6a, 0x0b, // code
    ];
    let module = Module::new(&wasm_bytes)?; // decode + validate
    let mut linker = Linker::new();
    linker.func("env", "log", &[ValType::I32], &[], |args, _results, memory| {
        println!("{:?} ({} bytes of memory)", args[0], memory.len());
        Ok(())
    });
    let mut instance = Instance::new(module, &linker)?; // check, compile, instantiate
    let r = instance.call("run", &[Val::I32(7)])?;
    assert_eq!(r, [Val::I32(8)]);
    Ok(())
}
```

Host functions get the arguments, a buffer for their results and the
guest's linear memory. A host function returning `Err` (or panicking)
traps the guest.

The proofs hold for 64-bit and for 32-bit hosts (wasm32 included):
`scripts/verify.sh wasm` checks the first and `crates/wasm/scripts/verify-narrow.sh`
the second. A 32-bit host has room for at most `interp::MAX_PAGES`
(32767) pages of guest memory, under the 2 GiB a `Vec` can hold there,
rather than the 65536 a 64-bit one allows: past that, instantiation
fails and `memory.grow` returns -1, as WebAssembly lets a host do.

### Resource limits

By default a guest may run forever and grow its memory to 4 GiB (2 GiB
on a 32-bit host). To run
untrusted code, set limits on the linker:

```rust
# use verilith_wasm::{Error, Instance, Linker, Module, ast::Trap};
# fn main() -> Result<(), Box<dyn std::error::Error>> {
# // (module (func (export "run") (loop br 0)))
# let module = Module::new(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x04, 0x01, 0x60, 0x00, 0x00,
#     0x03, 0x02, 0x01, 0x00, 0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
#     0x0a, 0x09, 0x01, 0x07, 0x00, 0x03, 0x40, 0x0c, 0x00, 0x0b, 0x0b])?;
let mut linker = Linker::new();
linker.fuel(10_000_000);     // each instance starts with this much fuel
linker.max_memory(64 << 20); // and gets at most 64 MiB of memory
let mut instance = Instance::new(module, &linker)?;
let r = instance.call("run", &[]); // an infinite loop
assert_eq!(r, Err(Error::Trap(Trap::Exhausted)));
assert_eq!(instance.fuel(), Some(0));
instance.set_fuel(Some(1_000_000)); // refuel (None: unmetered)
# Ok(())
# }
```

- **Fuel.** Each branch, call and return costs one unit; straight-line
  code between them is free. Every loop iteration and every call pays, so
  a metered call always ends. When a call runs out it traps with
  `Trap::Exhausted` and the fuel is 0; the instance stays usable, and
  fuel left over carries into the next call. The start function is
  metered too. The proof covers this: stopping for lack of fuel is one of
  the outcomes `run::executed` allows, with the semantics still running
  and the store as the interpreter left it.

  Unmetered instances pay nothing for this: they run `run::execute`, the
  loop without fuel, and metered ones run `run::execute_metered` (both
  proven). The metered loop checks fuel on each branch, call and return,
  and sends every branch code through one arm that charges and then
  dispatches again (`rsteps::s_branch`). On the benchmarks below that
  costs nothing measurable: metered runs execute 1 to 13% fewer
  instructions than unmetered ones (`fib` 7%, `sieve` 13%, `matmul` 5%,
  `sort` 5%, `crc32` 1%, `sha256` 4%; `runner vwasm-fuel` in `bench/`),
  as the shared arm compiles to tighter code, and take about the same
  time. A charge in each branch arm instead proves in 13 minutes rather
  than under 5 and executes 1 to 5% more instructions than unmetered
  runs. Checking fuel before every operation made the benchmarks up to
  1.65 times slower.
- **Memory cap.** `max_memory(bytes)` caps every instance's memory
  (rounded down to whole pages). A module whose memory starts above the
  cap fails to instantiate, and `memory.grow` past the cap returns -1, as
  it does past the module's own maximum.
- **Allocation failure.** If the host cannot allocate the pages a
  `memory.grow` asks for, the grow returns -1 instead of aborting the
  process. (On Linux with overcommit, allocation rarely fails; the
  process can still be killed later when the pages are touched. Use the
  memory cap to bound what a guest can take.)

### C API

`include/wasm.h` is the standard [wasm-c-api](https://github.com/WebAssembly/wasm-c-api)
header; `libverilith_wasm.a` implements the part of it needed to load modules,
provide host functions (`wasm_func_new`, `wasm_func_new_with_env`),
instantiate, call exports, read exported memories and globals, and
report traps. The upstream `hello`, `callback`, `multi` and `trap`
examples build and run unmodified (`scripts/capi.sh`).
`include/verilith.h` adds the resource limits:
`verilith_store_set_fuel` and `verilith_store_limit_memory` set them for
instances created in a store, and `verilith_instance_set_fuel` and
`verilith_instance_get_fuel` refuel an instance and read what it has
left; a call that runs out of fuel traps with "all fuel consumed"
(`examples/c/limits.c`). Not implemented:
tables and references as externs, global and memory objects created by
the embedder, trap traces, serialization, and import/export type
reflection.

### Supported WebAssembly

WebAssembly 2.0 without SIMD and reference types: all numeric
instructions including the saturating truncations and sign extension,
multi-value, bulk memory instructions (`memory.copy`, `memory.fill`,
`memory.init`, `data.drop`), one memory, `funcref` tables used by
`call_indirect` and filled by element segments, imports and exports of
functions, globals, memories and tables.

Not supported: SIMD, `externref`/`funcref` values, the table instructions
(`table.get/set/grow/size/fill/copy/init`, `elem.drop`), multiple
memories, memory64, threads, tail calls, exceptions, GC. An imported
memory or table is a fresh one with the import's limits, not shared with
the exporting instance. Implementation limits: 100,000 nested calls,
1M value-stack slots (8 MiB) per instance, 50,000 locals per function.

## Testing

- `scripts/verify.sh`: the proofs.
- `cargo test --release`: the spec tests (after
  `scripts/fetch-testsuite.sh`, which checks out WebAssembly/testsuite at
  a pinned commit) compared against `tests/spec-expected.txt`, and the
  trusted integer primitives (`tests/sint.rs`), and the resource limits
  (`tests/limits.rs`).

  | spec test files | result |
  | --- | --- |
  | 79 of the 90 non-SIMD files run (the 11 files that test only table instructions or reference values are skipped, as are the SIMD files) | 24,295 directives pass, 426 fail |
  | failures | every one needs reference-type values (`funcref`/`externref` globals, parameters, `select`, `ref.func`), a table instruction, or a memory, table or mutable global shared between instances; plus `names.wast`, whose text the `wast` parser rejects |

  The tests caught one bug in the semantics during development: `end`
  went through the label's arity, which for a `loop` is its parameter
  count, so a loop with results lost them. The semantics, the proofs and
  the checker were fixed together.
- `fuzz/`: differential testing against wasmi 2.0.3. wasm-smith 0.263.0
  generates modules using only the features above (NaNs canonicalized,
  loops fuel-bounded); every exported function is called with three
  argument sets in both engines, comparing results, traps, linear memory
  and exported globals after every call. 100,000 seeds (register
  interpreter): 87,380 modules run, 192,963 calls compared, no
  differences.
- `scripts/capi.sh`: the C API examples, and `examples/c/limits.c`.

## Performance

Best of 12 wall-clock times (two runs of the script) for the whole process (decode, validate or
compile, instantiate, run) on one core of an Intel Xeon @ 2.10GHz, for
Rust kernels compiled to wasm32 (`bench/kernels`, `bench/bench.sh`).
verilith-wasm is built with the repository's `.cargo/config.toml`, which passes
LLVM `-tail-dup-size=20` so every operation's handler ends in its own copy
of the dispatch jump, and `-enable-tail-merge=false` so LLVM does not merge
those copies back together (a crate depending on verilith-wasm needs the same flags
in its own config); wasmi and Wasmtime are built without extra flags, as their
users get them:

| kernel | verilith-wasm | wasmi 0.40 | wasm3 0.5.0 | WAMR 2.2.0 fast interp | Wasmtime 33 (JIT) |
| --- | ---: | ---: | ---: | ---: | ---: |
| fib(32), calls | 75 ms | 95 ms | 78 ms | 70 ms | 16 ms |
| sieve, 4M, x10 | 726 ms | 701 ms | 723 ms | 663 ms | 167 ms |
| matmul f64 200x200, x2 | 109 ms | 138 ms | 110 ms | 99 ms | 17 ms |
| sort 1M u32, x2 | 505 ms | 509 ms | 465 ms | 563 ms | 47 ms |
| crc32 4 MiB, x10 | 344 ms | 502 ms | 384 ms | 459 ms | 132 ms |
| sha256 4 MiB, x2 | 471 ms | 617 ms | 499 ms | 439 ms | 46 ms |

This machine is noisy (single runs of a kernel vary by 10 to 15%), so
comparisons between two builds are made interleaved on one pinned core,
best of 11. Against the previous release (no accumulator), that gives
fib 81 to 77 ms, sieve 676 to 630, matmul 125 to 106, sort 555 to 448,
crc32 504 to 343 and sha256 505 to 462 (wasm3 in the same runs: 69, 614,
114, 398, 385, 559).

The machine's timings drift between sessions (wasmi's crc32 time was
869 ms in an earlier run), so compare within one table. The stack
interpreter this replaced took 2.5 to 3.4 times wasmi's time in that
earlier run (fib 312 ms, sieve 4004 ms, matmul 835 ms, sort 2728 ms, crc32 2445 ms,
sha256 2747 ms on the same kernels).

How it gets there: the certificate fixes the operand-stack height at every
live position, so each operand-stack slot is a fixed offset from the frame
pointer, like a local. `src/reg.rs` turns each function into a dense array
of three-address operations on frame slots; one operation stands for a
short run (`local.get a; local.get b; i32.add; local.set c` is one
operation, `i32.lt_u; br_if` another), and about 340 specialized op codes
(`scripts/gen-rops.py`) give a single jump-table dispatch per operation.
Runs never cross a branch target, so a branch lands on an operation, and
branches that move no values jump straight to their target operation.
A `local.get` whose value is used by a later operation (rather than the
next instruction) would be a copy of its own; instead it is folded into
the next operation as a pre-copy (the `P_` codes), which takes sort from
27 to 21 dispatches per inner-loop iteration. The checker checks such an
operation as the `local.get` followed by the operation without it
(`rcheck::lemma_pre_sem`). `select` is an operation too (`Sel`), so the
branch-free comparisons in sort and sha256 stay on the fast path.
Like wasm3's register, the interpreter loop keeps the previous operation's
result in a local variable, the accumulator, which the compiler keeps in a
machine register. An operation whose first operand is that result, and
which nothing jumps to, reads it from the accumulator instead of the frame
(the `A_` codes, for the common 32-bit operations, loads, stores and
compare-and-branch): about a fifth fewer instructions executed on five of
the six kernels. Results are still written to the frame, so the
accumulator is only ever a copy; the loop invariant (`rrun::acc_ok`) says
it equals the slot the next operation reads, and the checker checks that
an `A_` operation follows one that writes that slot (`rcheck::acc_src`).
Each code's step is its own verified function (`src/rsteps.rs`), and the
loop calls them from one flat `match`, so the dispatch stays a single
jump table; the `A_` codes are limited to the common operations because
the proof of the loop is one solver query, which stops finishing at about
330 cases.
`src/rcheck.rs` checks the translation against the body and certificate
one operation at a time; anything it does not cover (calls, `br_table`,
branches that carry values, memory and table instructions) runs as before.

## Prior work

- **vWasm** and **rWasm** (Bosamiya, Lim and Parno, USENIX Security
  2022): vWasm is an ahead-of-time compiler to x86-64 written and verified
  in F*, proving that the generated code stays in its sandbox; rWasm
  translates WebAssembly to safe Rust and gets isolation from the Rust
  type system. verilith-wasm proves the same kind of isolation for an interpreter,
  in Rust, and in addition proves functional correctness (refinement of a
  semantics), which vWasm's proof does not cover.
- **WasmCert-Isabelle / WasmRef-Isabelle** (Watt et al.) and
  **WasmCert-Coq**: mechanizations of the official specification with
  type soundness proofs, and verified reference interpreters extracted to
  OCaml. Their semantics is the official one, and much more complete;
  verilith-wasm's is its own, smaller, and validated by testing. verilith-wasm's
  interpreter is ordinary Rust with a C API, meant to be embedded.
- **WaVe** (Johnson et al., IEEE S&P 2023): a verified WASI runtime layer,
  checking that the system-call interface a guest uses stays within its
  sandbox. That is the layer around an engine, and complements verilith-wasm,
  which has no WASI.

## Layout

- `src/ast.rs`: the decoded module, read directly by the semantics.
- `src/sem.rs`: the semantics, and `run` (multi-step execution with host
  responses).
- `src/num.rs`, `src/sint.rs`, `src/fops.rs`, `src/exec_num.rs`: numeric
  instructions (`exec_num` is verified equal to the semantics).
- `src/cert.rs`, `src/check.rs`: certificates and the verified checker.
- `src/preserve.rs`: progress and preservation.
- `src/interp.rs`, `src/run.rs`: the interpreter and its refinement proof.
- `src/compile.rs`: resolves branch targets from the certificate, then
  translates to register form and checks the translation.
- `src/reg.rs`, `src/reg_ops.rs`: the (unverified) translation to register
  form and its op codes (`reg_ops.rs` is generated by
  `scripts/gen-rops.py`, which also writes the dispatch arms in `run.rs`).
- `src/mach.rs`: the flat machine for straight-line code, and the proof
  that it takes the semantics' steps.
- `src/rcheck.rs`: what a correct register form is, and its verified
  checker.
- `src/rrun.rs`: the register loop's invariant and the step for each kind
  of operation.
- `src/rsteps.rs`: one verified step function per op code, generated by
  `scripts/gen-rops.py`.
- `src/instance.rs`: the checked instance (the verified boundary).
- `src/decode.rs`, `src/validate.rs`, `src/api.rs`, `src/capi.rs`:
  unverified decoder, validator, Rust API and C API.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/wasm/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/wasm/LICENSE-MIT), at your option.

`include/wasm.h` and `examples/c/` are from WebAssembly/wasm-c-api,
under the Apache License 2.0 in [LICENSE-wasm-c-api](https://github.com/verilith/verilith/blob/main/crates/wasm/LICENSE-wasm-c-api).
