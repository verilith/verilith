# What verilith-jpeg's proofs assume

The theorem is `decode::decode`: for every byte string, the result is the
image `spec::jpeg_decode` gives, or `Invalid` exactly when it gives none, or
`OutOfMemory`. This file lists everything that theorem rests on without
proving it. If something here is wrong, the proofs still check, and the
decoder can still be wrong.

## 1. The specification: `src/spec.rs`

About 1,950 lines, all of it definitions; this is the file to audit. It says
what a JPEG file decodes to as total functions over `Seq<u8>`. The proofs
show the decoder equals it; nothing shows it equals the standard.

It has two kinds of source, and each definition names its own:

- **ITU-T T.81** for the marker syntax (B.2), Huffman code construction and
  the DECODE, RECEIVE and EXTEND procedures (Annex C, F.2.2), and the
  coefficient decoding of baseline and of the four progressive scan types
  (F.2, G.1.2, G.2).
- **libjpeg-turbo 3.2.1** for everything T.81 leaves open or does not fix to
  the bit. These are the parts most worth reading against the C source:
  - what a decoder sees past the end of the input (`byte`: the bytes of an
    EOI marker, as `fill_mem_input_buffer` supplies), and zero bits once a
    marker is reached inside entropy-coded data (`jpeg_fill_bit_buffer`);
  - a Huffman code that is not in the table: 17 bits are taken and the
    symbol is 0 (`jpeg_huff_decode`);
  - restart handling and resynchronization (`jpeg_resync_to_restart`), and
    what is left in the MCUs that are skipped;
  - which headers are accepted: frame limits (65,500 per side, sampling
    factors 1 to 4), scan parameter checks (`get_sos`,
    `start_pass_phuff_decoder`), quantization and Huffman table checks, the
    DAC segment check (`get_dac`), and the standard Huffman tables used when
    a sequential file defines none;
  - how the colour space is chosen from the JFIF and Adobe segments and the
    component identifiers (`default_decompress_parms`);
  - the integer inverse DCT (`jidctint.c`, `jpeg_idct_islow`), including the
    32-bit workspace and the 10-bit range limit;
  - "fancy" chroma upsampling (`jdsample.c`): the triangle filters for 2:1
    horizontal, 2:1 vertical and 2:1 both ways, replication for every other
    ratio and for components at most two samples wide;
  - YCbCr to RGB conversion (`jdcolor.c`, 16-bit fixed point).

  Block smoothing (`jdcoefct.c`) is deliberately not in the specification;
  see the README's table of departures.

The specification's support limits are also assumptions about what "a JPEG
this decoder takes" means: 8-bit samples, one or three components, Huffman
coding, SOF0, SOF1 and SOF2 only.

The evidence that the specification matches libjpeg-turbo is empirical, not
proven: byte-identical output on 1,368 intact files and 496 damaged ones,
agreement on which of 900 damaged files to reject, and differential fuzzing
(see the README).

## 2. Trusted code inside the verified crate

Two functions are marked `#[verifier::external_body]`, so Verus takes their
contracts on faith. Both are in `src/parse.rs`:

- `alloc_i16(n)` and `alloc_u8(n)`: return `None`, or a vector of exactly
  `n` zeros. They call `std::alloc::alloc_zeroed` and build the `Vec` with
  `Vec::from_raw_parts`, so that large buffers come from `calloc` and are
  not written twice. About 15 lines each; the trust is that the layout
  matches what `Vec` expects and that the allocator returns zeroed memory.

Nothing else in `src/` uses `external_body`, `assume` or `admit`.

## 2a. NEON intrinsics, through verilith-simd (AArch64 only)

`src/idct_neon.rs`, `src/idct16.rs` and `src/color_neon.rs` are verified, but
they call 46 NEON intrinsics through
[verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd) (a path dependency in
this repository), and each of those is an `external_body` wrapper there: Verus
takes on faith that the instruction computes what verilith-simd's specification
says. The specifications are lane-by-lane functions in verilith-simd's `src/ops.rs`;
verilith-simd tests each instruction against a verified implementation of its
specification on random and edge inputs. The ones verilith-jpeg uses:

- loads and a store: `vld1q_s16_at`, `vld1q_u16_at`, `vst1q_u8_at`;
- the size test: `vabsq_s16`, `vmaxq_u16`, `vmaxvq_u16`;
- dequantization: `vmull_lo_s16`, `vmull_hi_s16` (`smull`, `smull2`);
- the passes: `vaddq_u32`, `vsubq_u32`, `vmulq_u32`, `vdupq_n_u32`,
  `vshlq_n_u32`, `vrshrq_n_s32`;
- the transposes: `vzip1q`/`vzip2q` at 8, 16, 32 and 64 bits (eight
  wrappers);
- the 16-bit inverse DCT, besides some of the above and below: `vmulq_u16`
  (dequantization), `vmull_lo_laneq_s16`, `vmull_hi_laneq_s16`,
  `vmlal_lo_laneq_s16`, `vmlal_hi_laneq_s16` (`smull`, `smull2`, `smlal`,
  `smlal2` by one lane of a vector of constants), `vrshrn_lo_n_s32`,
  `vrshrn2_n_s32` (`rshrn`, `rshrn2`), and for its size test `vqaddq_u16`,
  `vaddlvq_u16` (`uaddlv`), `vgetq_lane_u64_0`, `vgetq_lane_u64_1`;
- the range limit: `vuzp2q_u16`, `vqshrn2_n_s16` (`sqshrn`, `sqshrn2`),
  `veorq_u8`, `vdupq_n_u8`;
- colour conversion, besides some of the above: `vld1q_u8_at`,
  `vshll_low_n_u8`, `vshll_high_n_u8` (`ushll`, `ushll2`), `vaddq_s16`,
  `vsubq_s16`, `vdupq_n_s16`, `vqdmulhq_s16` (`sqdmulh`), `vqshrun2_n_s16`
  (`sqshrun`, `sqshrun2`) and the interleaved store `vst3q_u8_at` (`st3`);

and `has_neon()`, which is true exactly on AArch64, with verilith-simd's byte model
of a vector (`n8`, sixteen bytes). On other targets none of this runs:
`has_neon()` is false and the decoder takes `idct::idct_fast` and the plain
loop of `render::ycc_row`, which use no intrinsics.

## 3. Unchecked indexing, verified against vstd

`src/prims.rs` (`sget`, `sref`, `sset`, `vget`, `vset`) indexes with
`get_unchecked` and `get_unchecked_mut`. These are verified, not trusted:
each has the bounds as a `requires` clause, which Verus proves at every
call. What is trusted is vstd's own specification of those two methods
(that in-bounds unchecked access behaves as indexing does).

## 4. vstd specifications the proofs rely on

vstd's specifications of standard-library functions are axioms. The ones
verilith-jpeg uses beyond ordinary slice, array and `Vec` indexing:

- `get_unchecked`, `get_unchecked_mut` (above);
- `Vec::as_slice`, `Vec::as_mut_slice`, `slice_subrange`,
  `copy_from_slice`, `split_at`, `split_at_mut`;
- `i32::wrapping_add`, `wrapping_sub`, `wrapping_mul` (the 32-bit inverse
  DCT's second pass);
- vstd's arithmetic, bit-vector and `pow2` lemma libraries, which are
  themselves proven in vstd.

## 5. Unverified code

These files are compiled out when Verus runs (`#[cfg(not(verus_only))]`) and
carry no proof. They are glue between C pointers and the verified decoder,
and they contain `unsafe` code whose safety depends on the caller keeping
the documented contract (valid pointers and lengths).

- `src/capi.rs` (about 45 lines): `vjpeg_decode`, `vjpeg_free`.
- `src/tj.rs` (about 835 lines): the TurboJPEG decode API. Besides pointer
  handling it does unverified work of its own: it copies the verified RGB or
  grey result into the caller's buffer in the requested pixel order, pitch
  and direction, and it fills in header fields from `read_header`. A bug
  here could write wrong pixels or, with a bad pitch calculation, write
  outside the caller's buffer. It is exercised by `make -C difftest tjcheck`
  against libturbojpeg in every pixel format, with and without row padding.
  When the caller asks for the decoder's own layout (RGB or grey, rows top
  to bottom, no padding) it instead hands the verified `decode_to` a slice
  over the caller's whole buffer, `pitch * height` bytes, and copies
  nothing; `decode_to` is proven to write the picture only if the slice is
  exactly the picture's size, so here the trust is in that one length.

`decode::read_header` is inside the verified crate but has no correctness
contract: Verus proves it memory-safe and terminating, not that the fields
it reports are the specification's. The pixel path does not use it.

`examples/`, `difftest/` and `scripts/` are unverified tools.

## 6. What `OutOfMemory` means

`decode` may return `OutOfMemory` for any input; the theorem makes no claim
about when. In the code it is returned when an allocation fails or when a
size does not fit in `usize`. A decoder that always returned `OutOfMemory`
would satisfy the theorem, so that it does not is checked only by tests.

## 7. The toolchain

- Verus (`0.2026.11.22.1ce6a59`) and Z3: that a proof Verus accepts is a
  proof.
- The Rust compiler and LLVM: that the compiled code does what the source
  says. This includes auto-vectorization: the vector code in upsampling,
  and in colour conversion and the inverse DCT off AArch64, is produced by the
  compiler from verified scalar source, so no SIMD intrinsics are trusted
  there, but the compiler's transformation is.
- The differences between what Verus checks and what is compiled: ghost
  code is erased, and the build uses `--release` (overflow checks off;
  Verus proves no arithmetic overflows, apart from the three wrapping
  operations named above, which are specified as wrapping).
