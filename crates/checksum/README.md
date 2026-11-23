# verilith-checksum

Formally verified ([Verus](https://github.com/verus-lang/verus)) CRC-32
(RFC 1952), CRC-32C (RFC 3720) and Adler-32 (RFC 1950), with the fast
kernels verified too: carry-less-multiply folding for CRC-32 (PCLMULQDQ,
and VPCLMULQDQ on 256- and 512-bit vectors), three interleaved `crc32x`
chains on AArch64, and byte dot products for Adler-32 (AVX-512 VNNI, AVX2,
and `udot` on AArch64). It is what
[verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib),
[verilith-png](https://github.com/verilith/verilith/tree/main/crates/png),
[verilith-snappy](https://github.com/verilith/verilith/tree/main/crates/snappy) and
[verilith-archive](https://github.com/verilith/verilith/tree/main/crates/archive)
use. It used to be the `checksum` module of
[verilith-core](https://github.com/verilith/verilith/tree/main/crates/core).

```rust
let c = verilith_checksum::crc32(b"123456789");        // 0xcbf4_3926
let a = verilith_checksum::adler32(b"Wikipedia");      // 0x11e6_0398
let k = verilith_checksum::crc32c(b"123456789");       // 0xe306_9283
```

`crc32`, `adler32` and `crc32c` pick the fastest kernel the CPU has, at
run time (`cpu`). `crc32_update`, `adler32_update` and `crc32c_update` are
the portable verified kernels, and take a running register for streaming.

`cargo verus verify` checks 386 functions with no errors.

## What is proven

| | where |
| --- | --- |
| Adler-32 and CRC-32 (slicing-by-16, all 4096 table entries, the 32-lane Adler block) equal the RFC definitions | `adler32_update`, `crc32_update` against `spec::adler32`, `spec::crc32` |
| CRC-32C, by table, equals its definition | `crc32c::crc32c_update` against `spec::crc32c` |
| The CPU dispatch returns the same as the portable kernels | `cpu::adler32_update`, `cpu::crc32_update` |
| Folding a block with `fold_k(n) = crc_steps(POLY, n) << 1` advances its CRC effect `n` bits; runs of blocks fold onto the next run; four blocks fold into one; the final reduction to the 32-bit register; and the fold constants, computed by the compiler with the verified `lanes::steps_exec` | `fold` |
| The three-lane `crc32x` CRC-32, the tables that combine the lanes, and the combination | `lanes` |
| The lanes' byte sums, the sums before each row and the weighted sums give Adler-32's two sums; no lane overflows in a block of 1024 rows; the reduction modulo 65521 | `adlerv` |

## Trusted base

What the proofs here assume rather than prove:

- `src/cpu.rs`: CPU dispatch. `adler32_update` and `crc32_update` are
  themselves verified; trusted are the run-time feature checks and the
  one-line trampolines that compile the verified kernels (`adlerv`,
  `fold`, `lanes`) with the target features their instructions need. The
  AArch64 Adler-32 kernel needs none: NEON is baseline and its `udot`
  names the dot-product extension in the assembly. `crc32c_update` runs
  the CPU's CRC-32C instruction (SSE4.2's `crc32` on x86-64,
  `crc32cb`/`crc32cd` on AArch64) eight bytes at a time: trusted is that
  the instruction computes this CRC on the raw register, as it is defined
  to, and the eight-line loops around it. `tests/crc32c.rs` compares it
  with the verified table kernel at every length up to 300 and at eight
  alignments, and the table kernel with a bit-at-a-time reference.
- The vector instructions, from
  [verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd),
  where every trusted instruction wrapper lives:
  - `verilith_simd::clmul` (x86-64): the instructions the CRC-32 folding
    kernels use, one safe wrapper each with a contract on the vector's
    128-bit blocks (`xv`, `yl`, `zl`): the 16-, 32- and 64-byte loads,
    XOR, AND, byte shifts, broadcasts, extracting a block, and the
    carry-less products of `pclmulqdq`/`vpclmulqdq` (immediates 0x00 and
    0x11), stated with the spec `clmul`; the CPU-feature predicates
    `pclmul()`, `vpclmul256()`, `vpclmul()` and their detection. Each is
    one intrinsic, except `x_fold`/`y_fold`/`z_fold` (two products and an
    XOR). `tests/vclmul.rs` here checks every one against the verified
    reference `fold::clmul_ref` (itself checked against a naive product)
    on random inputs, and the three kernels against the table code at
    every length to 1100 and random lengths to 64 KiB. The 512-bit checks
    need AVX-512F and VPCLMULQDQ and are skipped, with a message, on a CPU
    without them.
  - `verilith_simd::vdot` (x86-64): the instructions the Adler-32 kernels
    use, one safe wrapper each with a contract on the vector's bytes
    (`zb`, `yb`) or 32-bit lanes (`zd`, `yd`): the 64- and 32-byte loads,
    zero, lane-wise add, store, and the dot product of four unsigned bytes
    with four small weights added to each lane, stated with the spec
    `verilith_simd::dot::dot4`; the predicates `vnni512()`, `avx2()` and
    their detection. Each is one intrinsic, except `yd_dot`, which is
    AVX2's `vpmaddubsw`, `vpmaddwd` by ones and an add: its `requires`
    keeps the weights at most 64, so the 16-bit sums cannot saturate.
    `tests/vdot.rs` here checks every one on random inputs, the saturation
    edge with all bytes 255, and both kernels against the portable code at
    every length to 1100 and random lengths to 200 KB.
  - `verilith_simd::vudot`: the same operations for AArch64 on 64-byte
    rows of four NEON registers (`nb`, `nd`), the dot product being `udot`
    (written as inline assembly, `vdotq_u32` not being stable Rust), and
    `dotprod()` with its detection. On other CPUs detection is false and
    the bodies are plain-Rust stand-ins, so `tests/vudot.rs` here checks
    the verified kernel `adlerv::udot` everywhere and the instructions
    themselves on AArch64.
- `src/lanes.rs`, the one `external_body` function `crc_word`: on
  AArch64, that the `crc32x` instruction computes this CRC-32 over its
  eight bytes. `tests/basic.rs` runs the three-lane kernel against the
  table kernel at every length around its block boundaries; on other CPUs
  `crc_word` is the table kernel, so the same test covers the lanes there.
- The specs: `src/spec.rs`.
- Verus, Z3 and the Rust compiler.

The crate needs `std`, for run-time CPU detection (as verilith-simd does).

## Verifying

```sh
./scripts/verify.sh
```

needs `cargo-verus` from the Verus release in `scripts/verus-version` at
the repository root on `PATH`, and z3 (via `VERUS_Z3_PATH` or next to the
verus binary).

## Speed

`cargo run --release --example crc32_speed` times the dispatched CRC-32
against the portable table kernel.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/checksum/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/checksum/LICENSE-MIT), at your option.
