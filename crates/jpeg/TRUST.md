# What verilith-jpeg's proofs assume

The theorem is `decode::decode`: for every byte string, the result is the
image `spec::jpeg_decode` gives, or `Invalid` exactly when it gives none, or
`OutOfMemory`. The encoder's is `encode::encode_rgb`: the file it returns
decodes, under `spec::jpeg_coded`, to `enc_spec::enc_coded` of its input
(section 1a). This file lists everything those theorems rest on without
proving them. If something here is wrong, the proofs still check, and the
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

### And `src/spec_scaled.rs`, for reduced-size decoding

About 230 lines, the theorem of `scaled::decode_scaled`. It reuses
`spec.rs`'s coefficients, range limit, upsampling filters and colour
conversion, and adds what libjpeg-turbo 3.2.1 does differently when it
decodes at 1/2, 1/4 or 1/8: the reduced inverse DCTs (`jidctred.c`:
`jpeg_idct_4x4`, `jpeg_idct_2x2`, `jpeg_idct_1x1`, with their 32-bit
workspaces), the inverse DCT size of each component (`jdmaster.c`, which
scales chroma up through the inverse DCT rather than upsampling where the
sampling factors allow), the component and output sizes, and the
upsampler's choice (`jdsample.c`: no triangle filters at 1/8). The evidence
that it matches libjpeg-turbo is empirical: `difftest/scaled.sh` gives
byte-identical output to `djpeg -scale` at all four scales on 860 pairs of
file and scale (every sampling factor combination cjpeg writes, sizes from
1x1 up, baseline, progressive and with restart markers, greyscale and RGB),
with libjpeg-turbo's SIMD code on x86-64.

## 1a. The encoder's specification: `src/enc_spec.rs`

About 300 lines of definitions: what the encoder codes, after
libjpeg-turbo 3.2.1 with `jpeg_set_defaults` and `jpeg_set_quality(q,
TRUE)`: RGB to YCbCr in 16-bit fixed point (`rgb_ycc_convert`), the last
row and column repeated to whole blocks (`expand_right_edge`,
`expand_bottom_edge`), `h2v2_downsample` with its alternating rounding
bias, `jpeg_fdct_islow`, quantization rounding to nearest
(`quantize`), `jpeg_quality_scaling` and `jpeg_add_quant_table` with the
Annex K tables, and the dummy blocks `compress_data` codes past the
image's edge. It is read together with `spec.rs`, whose `jpeg_coded` (the
decoder's own) says what the written file means; the encoder's theorem
does not depend on the decoder's code, only on that specification.

The evidence that `enc_spec.rs` matches libjpeg-turbo is empirical:
`difftest/encdiff` finds the files byte-identical (see the README). The
coefficients are clamped to baseline's range in the specification; for
8-bit input they always are in it, so the clamp never changes one.

## 2. Trusted code inside the verified crate

Nothing in `src/` uses `external_body`, `assume` or `admit`. The zeroed
allocations, `alloc_i16(n)` and `alloc_u8(n)` (`None`, or a vector of
exactly `n` zeros, from `calloc` for large buffers), are verilith-core's,
re-exported from `src/parse.rs`, and are trusted there: see
[verilith-core's trusted base](../core#trusted-base).

## 2a. NEON intrinsics, through verilith-simd (AArch64, and x86-64 through SSE)

`src/idct_neon.rs`, `src/idct16.rs` and `src/color_neon.rs` are verified, but
they call 47 NEON intrinsics through
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
  `vrshrn2_n_s32` (`rshrn`, `rshrn2`), `vdotq_s16` (the pairwise
  multiply-add of x86's `pmaddwd`, used in place of the `vmull`/`vmlal`
  pairs when `neon_emulated()` says the NEON runs on SSE), and for its size test `vqaddq_u16`,
  `vaddlvq_u16` (`uaddlv`), `vgetq_lane_u64_0`, `vgetq_lane_u64_1`;
- the range limit: `vuzp2q_u16`, `vqshrn2_n_s16` (`sqshrn`, `sqshrn2`),
  `veorq_u8`, `vdupq_n_u8`;
- colour conversion, besides some of the above: `vld1q_u8_at`,
  `vshll_low_n_u8`, `vshll_high_n_u8` (`ushll`, `ushll2`), `vaddq_s16`,
  `vsubq_s16`, `vdupq_n_s16`, `vqdmulhq_s16` (`sqdmulh`), `vqshrun2_n_s16`
  (`sqshrun`, `sqshrun2`) and the interleaved store `vst3q_u8_at` (`st3`);

and `has_neon_sse()`, which is true on AArch64 and, on x86-64, when the CPU
has SSE4.1 and SSSE3, with verilith-simd's byte model of a vector (`n8`,
sixteen bytes).

On x86-64 these wrappers are not trusted on their own: each forwards to
verilith-simd's `src/wasm_neon.rs`, proven on its SIMD128 contracts, and
the 49 SIMD128 instructions those use forward to `src/wasm_x86.rs`, proven
from the specifications of the SSE2, SSSE3 and SSE4.1 intrinsics it calls
(verilith-simd's `src/x86.rs`, the same ones the crates' AVX2 kernels rely
on). What x86-64 trusts instead is those intrinsic specifications, the
16- and 8-byte loads and stores, two transmutes between `uint8x16_t` and
`__m128i`, `axiom_neon_x86` and `has_neon_sse()`'s CPU check: see
[verilith-simd's trusted base](../simd#trusted-base).
`tools/check_wasm_neon.py` there checks that each proven contract is word for
word the one the wrapper states. On other targets none of this runs:
`has_neon_sse()` is false and the decoder takes `idct::idct_fast` and the
plain loop of `render::ycc_row`, which use no intrinsics.

`render::ycc_row`, `h2v1_mid` and `h2v2_mid` also call a copy of themselves
compiled with AVX2 enabled (`#[target_feature]`) when `has_avx2()` says the
CPU has it. Those copies are verified like the originals, use no
intrinsics, and are `unsafe` to call only because of the attribute.

## 2b. AVX2 intrinsics (x86-64)

`src/idct_avx2.rs` is verified against `spec::idct` like `idct16.rs`, with
the same 16-bit size test (magnitudes summing to at most 2120), but it calls
verilith-simd's AVX2 intrinsics directly (its safe wrappers in `src/safe.rs`),
whose behaviour Verus takes from the `assume_specification`s in its
`src/x86.rs`, lane-by-lane functions of `src/ops.rs` written from Intel's
descriptions and checked against the CPU by its tests. It trusts those
specifications for
`_mm256_madd_epi16` (magnitudes and the passes' products),
`_mm256_mullo_epi16`, `_mm256_mulhi_epi16`, `_mm256_srai_epi16`
(dequantization and its overflow check), `_mm256_add_epi16`,
`_mm256_add_epi32`, `_mm256_sub_epi32`, `_mm256_srai_epi32`,
`_mm256_and_si256`, `_mm256_or_si256`, `_mm256_xor_si256`,
`_mm256_testz_si256`, `_mm256_unpacklo_epi16`, `_mm256_unpacklo/hi_epi32`,
`_mm256_unpacklo/hi_epi8`, `_mm256_permute2x128_si256`,
`_mm256_permutevar8x32_epi32`, `_mm256_packs_epi32`, `_mm256_packs_epi16`,
`_mm256_shuffle_epi8`, `_mm256_set1_epi8/16/32`, `_mm256_setr_epi8`,
`_mm256_setr_epi32`, `_mm256_castsi256_si128`, `_mm256_extracti128_si256`
and `_mm_srli_si128`; the loads `load256_i16` and `load256_u16`, the stores
`store256_u32` and `storel64_u8`; and `has_avx2()`'s CPU check. The kernel
is compiled with AVX2 enabled (`#[target_feature]`) and called only when
`has_avx2()` is true; a block it declines as too large goes to `idct_neon`
on SSE, or to `idct_fast`.

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

- `src/capi.rs` (about 80 lines): `vjpeg_decode`, `vjpeg_encode`,
  `vjpeg_free`.
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

## 6a. The work bound's unit

`decode::decode_counted` bounds the decoder's steps with a ghost counter
(`work::Meter`). What is assumed is the unit: that a zeroed allocation of
`n` elements (`alloc_i16`, `alloc_u8`) costs on the order of `n` steps,
and that a loop whose length the format fixes (64 coefficients, 16 code
lengths, the rows of one inverse DCT) costs a constant per turn of the
loop around it. The counter counts
what the verified loops do; the primitives' cost is assumed.

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
