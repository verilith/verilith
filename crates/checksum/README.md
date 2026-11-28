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

`cargo verus verify` checks 391 functions with no errors.

## What is proven

| | where |
| --- | --- |
| Adler-32 and CRC-32 (slicing-by-16, all 4096 table entries, the 32-lane Adler block) equal the RFC definitions | `adler32_update`, `crc32_update` against `spec::adler32`, `spec::crc32` |
| CRC-32C, by table, equals its definition | `crc32c::crc32c_update` against `spec::crc32c` |
| CRC-32C with the CPU's instruction, eight bytes at a time, equals its definition | `crc32c::crc32c_words` against `spec::crc32c` |
| The CPU dispatch returns the same as the portable kernels | `cpu::adler32_update`, `cpu::crc32_update`, `cpu::crc32c_update` |
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
  names the dot-product extension in the assembly. `crc32c_update` is
  verified too; trusted is the trampoline that compiles the verified
  `crc32c::crc32c_words` with SSE4.2 or the CRC extension enabled.
- The CRC instructions, through verilith-simd's `crc` module (its trusted
  base): `crc32c_u64`, `crc32c_u8` and `crc32_u64` (SSE4.2's `crc32` on
  x86-64, `crc32cx`/`crc32cb`/`crc32x` on AArch64), each specified there
  as the reflected CRC with its polynomial over its operand, and the CPU
  checks `has_crc32c` and `has_crc_arm`. `crc32c::crc32c_word`,
  `crc32c_byte_hw` and `lanes::crc_word` are now verified: they prove this
  crate's `crc32c_from` and `crc_from` equal to that specification
  (`lemma_from_simd`). verilith-simd's `tests/crc.rs` checks the
  instructions against the definition bit by bit; `tests/crc32c.rs` here
  still runs the whole kernel against the table kernel at every length up to 300 and at eight alignments (on x86-64,
  and on AArch64 under qemu), and the table kernel against a
  bit-at-a-time reference.
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
- `tests/basic.rs` runs the three-lane CRC-32 kernel (`lanes`) against
  the table kernel at every length around its block boundaries; off
  AArch64 `crc32_u64` is verilith-simd's bit-by-bit definition, so the
  same test covers the lanes there.
- The specs: `src/spec.rs`.
- Verus, Z3 and the Rust compiler.

## Without `std`

```toml
verilith-checksum = { ..., default-features = false }
```

makes the crate `no_std` (it needs only `alloc`, for vstd), for embedded
and kernel targets: it builds for `thumbv7em-none-eabihf`,
`aarch64-unknown-none` and `x86_64-unknown-none`. Run-time CPU detection
needs `std`, so without it each kernel is chosen from the features the
target is compiled for: build with `-C target-feature=+pclmulqdq,+avx2`
(or `-C target-cpu=...`) on x86-64, or `+crc,+dotprod` on AArch64, to get
the vector kernels; otherwise the table kernels run. The verified code is
the same either way; only the trusted detection differs. On
`x86_64-unknown-none`, which has no SSE registers, the x86-64 vector
kernels are not compiled at all, so CRC-32 and Adler-32 use the table
kernels; CRC-32C's `crc32` instruction is scalar and is still used when
SSE4.2 is enabled.

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
