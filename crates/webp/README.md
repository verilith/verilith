# verilith-webp

A verified WebP decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus): lossless (VP8L, RFC 9649) and
lossy (VP8, RFC 6386, with or without an `ALPH` alpha chunk). It decodes
only; there is no encoder. It is a hardened, drop-in-compatible replacement
for the still-image decode path of
[libwebp](https://chromium.googlesource.com/webm/libwebp/), not for libwebp as
a whole, and its output is byte-identical with libwebp 1.6.0's.

The two formats are proven to different depths. The lossless decoder is
proven correct against a specification of the format, in linear time. The
lossy decoder is proven memory-safe, overflow-free, panic-free and
terminating. Its first stages, the boolean entropy decoder, the frame header, the intra
prediction modes and the coefficients of a macroblock, are also proven
against a specification written from RFC 6386; the
rest of its agreement with libwebp is tested (differential tests and
fuzzing), not yet proven.

For lossless, the bit reader, the Huffman table builder, the color cache, the
backward references, the four image transforms, the container parser and the
top-level decode are all proven against a specification of the format. `cargo verus
verify` checks the functions here, in
[verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (the shared bit and
canonical-code proofs) and in [verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd),
with no errors. The CI workflow (`.github/workflows/ci.yml`, manual runs only)
reruns the proofs, the differential tests against libwebp, and the fuzzer.

WebP lossless is where [CVE-2023-4863](#cve-2023-4863) lived — a heap overflow
in the Huffman table builder, exploited in the wild. In verilith-webp that class of bug
is proven impossible for every input.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no integer overflow, no panics | every function, lossless and lossy (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function, lossless and lossy (`decreases`) |
| Lossless correctness: the decoded image equals the specification's for every valid file; `Bitstream` is returned exactly when the spec rejects the file; `Unsupported` exactly when the file is lossy (and the lossy decoder takes over) | `container::webp_decode_exec` against `spec::webp_decode` / `spec::parse_headers` |
| Lossy boolean decoder: every bit, literal and signed value read from a partition is the one RFC 6386 section 7's decoder returns, 56-bit refills included, for as long as the reads stay inside the partition and the partition's code word starts inside the coder's range (its first byte is not `0xff`) | `vp8bool::BoolReader::{new, get_bit, get_value, get_signed, get_signed_value}` against `vp8spec::{bool_init, bool_next, bool_bit, bool_literal}` |
| Lossy frame header: the segment, loop filter, partition, quantizer and token probability fields are the ones the specification of RFC 6386 sections 9 and 19.2 reads, and the dequantization factors, filter limits and partition byte ranges are the specification's functions of them | `vp8parse::parse_header` against `vp8spec::frame_header` (`Header::matches`) |
| Lossy intra modes: each macroblock's segment, skip flag, 16x16 or sixteen 4x4 luma modes and chroma mode are the ones the specification of RFC 6386 sections 9.3, 9.11 and 11 reads, with the above and left subblock modes as context, row after row through the first partition | `vp8parse::parse_intra_mode` against `vp8spec::mb_modes`; `parse_mode_row` against `row_modes`; the row loop of `vp8frame::decode_frame` against `mode_rows` (a loop invariant) |
| Lossy coefficient tokens: the tokens of a 4x4 block (end of block, zero runs, ones, `DCT_2` to `dct_cat6` with their extra bits, signs), dequantized and placed in zigzag order, are the ones the specification of RFC 6386 section 13 reads for that block's type, context and probabilities | `vp8parse::get_coeffs` against `vp8spec::block_tokens` |
| Lossy macroblock residuals: the 24 (or 25) blocks of a macroblock are read in the order, with the block types, first positions and neighbour contexts of RFC 6386 section 13, and the Y2 block's inverse Walsh-Hadamard transform (section 14.3) gives each luma block its DC | `vp8parse::parse_residuals` against `vp8spec::mb_residuals` |
| Lossy coefficients of the frame: every macroblock's coefficients are read from the token partition of its row (section 9.5), with the nonzero contexts handed along the row and down the columns, and none for a macroblock flagged as skipped (section 9.11) | the loops of `vp8frame::decode_frame` and `decode_mb_row` against `vp8spec::tok_rows` and `row_tokens` |
| Lossy inverse DCT: each of the four transform routines (the 16-bit SIMD-style one for one block and for two, the three-coefficient one and the DC one) adds to the prediction the residual of RFC 6386 section 14.4, clipped. For the 16-bit routine this holds for blocks whose intermediate values fit in 16 bits, which coefficients below 2048 in size always do | `vp8dsp::transform_one`, `transform_two`, `transform_ac3`, `transform_dc`, `do_transform`, `do_uv_transform` against `vp8spec::idct`; `vp8spec::lemma_idct_small` |
| Lossy intra prediction: each prediction routine replaces its block with the prediction of RFC 6386 section 12 from the pixels above and to the left. That is the four 16x16 and 8x8 modes, with the three forms `DC_PRED` takes on the frame's edge, and the ten 4x4 subblock modes | `vp8dsp::pred_block` against `vp8spec::pred_big`, `vp8dsp::pred4` against `vp8spec::pred4_px` |
| Lossy macroblock reconstruction: with the macroblock's modes and coefficients as the specification has them, and coefficients whose inverse DCT fits in 16 bits, the scratch block after reconstruction is the specification's: prediction of each block from its neighbours, then its residual. This includes the parser's per-block transform selectors (full, three coefficients, DC only, none), proven to claim no more than each block's coefficients bear out | `vp8frame::reconstruct_mb` against `vp8spec::mb_recon` and `mb_setup`; `vp8parse::mb_coeffs` (`sels_ok`), `vp8frame::lemma_mb_res_ok` |
| Lossy frames: the Y, U and V planes are the specification's, macroblock by macroblock in raster order, each predicted from the reconstructed pixels above and to its left, each row then loop-filtered with the strengths of its macroblocks' segments and kinds | `vp8frame::decode_frame` against `vp8spec::vp8_frame` (`row_recon`, `lf_row`, `frame_recon`), for frames that satisfy `vp8_plain`; `vp8parse::mb_coeffs` for the inner-edge choice |
| Lossy loop filter of one macroblock: the simple and normal filters of RFC 6386 section 15, on the macroblock's left, top and inner edges, in exact integer arithmetic, including the 16-lane SIMD versions | `vp8frame::filter_mb` against `vp8spec::lf_mb`; `vp8dsp::simple_filter`, `filter_loop`, `filter_loop_uv` against `lf_run` |
| Lossy planes to RGB: every output pixel is libwebp's fancy-upsampled chroma (9-3-3-1, with its two rounding steps and edge rules) through its fixed-point YUV to RGB conversion, in ARGB words or any of the byte layouts, on the scalar, SSE2 and NEON paths | `vp8yuv::planes_to_argb`, `planes_to_bytes` against `vp8spec::rgb_image_argb`, `rgb_image_bytes`; `lossy::layout_argb` (`lossy_argb`) for the decoded file |
| Lossy container and alpha: the frame offset and the `ALPH` payload are the container specification's, and the alpha plane is the specification's decoding of that payload (raw or VP8L-coded, filters undone) | `lossy::lossy_layout` against `container::lossy_off`, `lossy_alpha`; `lossy::decode_alpha` against `spec::alpha_plane`; `lossy::decode_lossy` (`lossy_argb`) |
| Lossy decode shape: the planes cover the frame, `1 <= w, h < 16384`, and the output has exactly `w * h` pixels | `vp8frame::decode_frame` (`Planes::ok`), `vp8yuv::planes_to_argb`, `vp8yuv::planes_to_bytes` |
| Output shape: a decoded image has exactly `w * h` pixels, with `1 <= w, h <= 16384` | `webp_decode_exec`, `decode::undo_all_exec` |
| The only non-spec result is `OutOfMemory`, and only on a failed allocation | `webp_decode_exec` ensures (`Ok` or `OutOfMemory` whenever the spec decodes) |
| Lossless linear time: at most `decode_cost(n+8, 16384, 16384)` decoder steps for an `n`-byte file — linear in the file size and in the pixel count, with the dimensions capped at the format's 16384 limit | `webp_decode_exec` ensures, via the ghost counter `BitReader::work` |
| Huffman tables decode exactly as the canonical prefix code, and building a table of `n` symbols with root bits `r` takes a bounded number of steps (Kraft's inequality) | `huffman::build` |
| Each transform (predictor, color, subtract-green, color-indexing) inverts its spec exactly, and restores the pre-transform width | `undo::*`, `decode::undo_all_exec` against `transform::tviews` |
| The color cache, backward references and literals reproduce the spec's pixel stream, in bounded work per pixel | `pixels::decode_image_data` against `spec::decode_with` |

For lossy, the Y, U and V planes are proven: the planes `vp8frame::decode_frame` returns are
`vp8spec::vp8_frame`, for every frame that satisfies `vp8_plain`. That asks three things of the file: its
partitions begin as a boolean decoder can, every block's inverse DCT fits in 16 bits (`frame_tame`), and, when the
frame has a loop filter, no block is zeros spelled out as tokens (`frame_solid`). `src/vp8spec.rs`
specifies RFC 6386 through the frame header, the intra modes (section 11), the dequantized coefficients of every
macroblock (sections 9.5, 9.11 and 13, with the inverse WHT of section 14.3), the inverse DCT (section 14.4), the
prediction of each block from its neighbours (section 12), the loop filter (section 15), and the frame built
macroblock row by macroblock row, in a scratch block laid out as libwebp's and the reference decoder's are. The conversion of those planes to RGB is proven too: `vp8yuv::planes_to_argb` and `planes_to_bytes` return
`vp8spec::rgb_image_argb` and `rgb_image_bytes` of the planes, the image of libwebp 1.6.0's "fancy" chroma
upsampler and its fixed-point `VP8YuvToRgb`, SIMD paths included. No standard fixes that stage (RFC 6386 ends at the
planes), so its specification is libwebp's arithmetic, compared with `src/dsp/yuv.h` and `src/dsp/upsampling.c`.

The container and the alpha plane are proven as well. `lossy::lossy_layout` finds the frame where the container
specification puts it (`container::lossy_off`, built on the same `spec::parse_headers` the lossless path is proven
against) and takes the last `ALPH` chunk before it (`spec::find_alph`). `lossy::decode_alpha` returns
`spec::alpha_plane` of that chunk: the raw bytes or the green channel of a VP8L image stream (the proven lossless
decoder, without its header), with libwebp's horizontal, vertical or gradient filter undone (`alph_unf`, compared
with `src/dsp/filters.c`). `lossy::decode_lossy` joins it all: the image it returns has the size in the frame header,
and, for a frame that satisfies `vp8_plain`, every pixel is the RGB specification's image of `vp8_frame` with that
alpha plane (`lossy_argb`). One judgement call: a bare bitstream with no chunk header that also passes the VP8L
signature check is lossless to `parse_headers`, so `lossy_layout`'s contract leaves that case out; its callers reach
it only after `parse_headers` said lossy.

Two things about that theorem. The specification filters each macroblock row right after reconstructing it, as the
decoder does, rather than the whole frame at the end; the two are the same because prediction reads only unfiltered
copies, but that equivalence is argued, not proven. And `frame_solid` is there because libwebp decides a macroblock's
inner-edge filtering from its per-block transform selectors; the specification says "it is `B_PRED` or has a nonzero
coefficient", and the hypothesis excludes the blocks where the selectors and the coefficients could disagree
(explicit zeros past a block's second position).

The loop filter specification was compared with libvpx's source (`vp8/common/loopfilter_filters.c`,
`vp8_loopfilter.c`, `vp8/decoder/decodeframe.c` and `detokenize.c`), not with the RFC's text. The kernels, the
edge and interior limits, the hev thresholds and the order of edges agree. Two rules follow libwebp where libwebp
and libvpx differ, on streams no ordinary encoder writes:

- libvpx filters a macroblock's inner edges when it is `B_PRED` or has any token (`eobtotal != 0`). That differs
  from "has a nonzero coefficient" for a block of explicit zero tokens, and for a coefficient that wraps to zero in
  16 bits.
- With segments on, libvpx clamps the segment's filter level to 0..63 before it adds the reference and mode deltas,
  and again after. libwebp, and `vp8spec::seg_filter_level`, clamp once, at the end. The two differ when the
  segment's level leaves 0..63 and the deltas are enabled.

The inverse DCT theorem is exact arithmetic: libwebp's SIMD code, like libvpx, keeps intermediate
values in 16 bits, and the two differ from each other and from exact arithmetic on blocks that overflow them, which
no encoder produces from an image. The header theorem is also conditional, as the table says:
it speaks for decodes that never read past the end of the first partition,
of files whose first partition does not begin with `0xff` (no encoder emits
one; libwebp and verilith-webp still decode such a file, identically in the tests). Nor is there a work bound, though every
loop is proven to terminate and each one is bounded by the macroblock count,
the 16 coefficients of a block or the pixels of a row.

The work counter is ghost state, erased at compile time; it counts every loop
iteration in the reader, the table builder and the pixel loop, and charges a
fixed cost per output pixel. The constants
(`decode_cost(len, w, h) = bit_cost * 8·len + 4·xform_cost(w, h) +
pix_cost · 3wh + 3·bit_cost + 5·refill_cost`, with `pix_cost = 110`,
`refill_cost = 9`) pay for the worst case; real files run far below it. The
bound is what rules out a decompression-bomb or quadratic-blowup input: output
and running time are both linear in the input.

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification itself — the VP8L format as total functions
  over `Seq<u8>`. Review it against RFC 9649. If the spec is wrong, the proofs
  still hold, against the wrong thing; this file is the one to audit.
- `src/vp8spec.rs`, down to its "Lemmas" heading: the lossy specification so
  far (RFC 6386's boolean decoder, key frame header and intra modes; modes
  carry libwebp's numbers, listed there next to the RFC's names). Review it against
  the RFC. Two things in it follow libwebp where the RFC leaves a choice or
  libwebp differs: a token partition whose size runs past the end of the
  file is cut short, and a frame that enables segmentation without sending
  segment data gets absolute zeros (`ResetSegmentHeader`). The constant
  tables it names (`spec_dc_table` and the like) are tied to the tables in
  `src/vp8tables.rs` by trusted one-line readers.
- [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s trusted base:
  the memory primitives in `verilith_core::prims` (verilith-webp uses its unaligned
  little-endian load, the slice copies `copy_in` and `copy_within`, and
  fallible `Vec<u32>` allocation; the unchecked `get`/`set` accessors at 8,
  16 and 32 bits are proven there), and the spec functions for bits and
  canonical codes in `verilith_core::bits` and `verilith_core::huffman`, which `src/spec.rs`
  re-exports. Each primitive's `requires` clause is the bounds/size fact
  Verus proves at every call site.
- Target-feature trampolines: Verus rejects `#[target_feature]` on verified
  code (verus-lang/verus#3362), so the AVX2 entry points `unpredict_avx2`
  (`src/vpred.rs`), `undo_sg_avx2` and `uncolor_run_avx2` (`src/vx.rs`) are
  `external_body` wrappers that call a one-line `unsafe` trampoline in
  `mod tf`, which carries the attribute and calls the verified `*_body`
  function. The contracts are the `*_body` functions', checked by Verus,
  and require `avx2()`. What is trusted is that the two calls forward.
  `vp8yuv::yuv_pack4_avx2` takes a different route with no wrapper: the
  verified function itself carries
  `#[cfg_attr(all(not(verus_only), target_arch = "x86_64"), target_feature(enable = "avx2"))]`,
  so Verus checks the same body the compiler builds, minus the attribute.
  What is trusted there is that the attribute changes code generation
  only; its one `unsafe` call site is under a proven `avx2()`.
- The SIMD intrinsics, specified in
  [verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd) (a git dependency,
  pinned by commit in `Cargo.toml`):
  - `vsimd/src/x86.rs`: about 118 `assume_specification`s, one per
    `core::arch` intrinsic, each stating the intrinsic's result as a
    function of its input bytes (`vsimd/src/ops.rs`). These are
    trusted; verilith-simd checks each one against the real CPU on a million random
    inputs (its `tests/difftest.rs`), but that is testing, not proof.
  - `vsimd/src/neon.rs`: the AArch64 NEON wrappers the lossy decoder uses
    (loads and stores of 16 and of 8 bytes, `zip1`/`zip2` at 8 to 64 bits,
    signed 16-bit arithmetic with `sqdmulh`, byte averages, widening and
    saturating narrowing shifts, and the loop filter's byte operations:
    saturating adds and subtracts, `uabd`, `umax`, `cmhs`, `bic` and
    `sshr`, and for 4x4 prediction `tbl`, `ext`, a vector from two
    64-bit halves and a 4-byte store of one 32-bit lane), specified the same
    way and tested against the same references on AArch64
    (`tests/neon.rs`).
  - `vsimd/src/mem.rs`: unaligned vector loads and stores from slices
    (and the 4-byte store of a vector's low 32 bits the 4x4 predictor
    uses on x86), with bounds `requires`.
  - `vsimd/src/cpu.rs`: CPU feature detection, the assumption that
    AVX2 implies SSE4.1 and SSSE3, and `compiled_with_ssse3()`, which is
    `cfg!(target_feature = "ssse3")`: true only in a build whose every
    target CPU has SSSE3.
- Two trusted helpers of the lossy decoder: `vp8frame::alloc_u8`, a
  zeroed `Vec<u8>` of a given length that returns `None` when the
  allocation fails (`external_body`, five lines), and the accessors for the
  five large constant tables in `src/vp8tables.rs` (the token and mode
  probabilities and the quantizer steps), kept outside `verus!` so their
  thousands of entries stay out of the solver's context. The accessors
  state only an index bound and, for the quantizer tables, a value range,
  which the `table_bounds` unit test checks.
- `src/capi.rs`: the C ABI and the safe-Rust wrapper. Unverified glue that
  calls the verified decoder, allocates the output (`calloc`, so the slice
  it hands the decoder is initialized), and converts lossless `u32` ARGB
  output to the requested pixel layout; a lossy image is written in the
  requested layout by the verified `vp8yuv::planes_to_bytes` instead. It is exercised by the differential tests and the
  fuzzer (below), both under AddressSanitizer.
- Verus, Z3 and the Rust compiler.

Everything else in `src/` is verified.

### Departures from libwebp

verilith-webp decodes the same bitstreams as libwebp and, where it decodes, produces
byte-identical RGBA (the differential tests check this). It is not a complete
libwebp: the C API is present so existing callers link, but some paths are
intentionally unsupported and report an error rather than doing the work.

| area | libwebp | verilith-webp |
| --- | --- | --- |
| Animated images (`ANIM`/`ANMF`) | decoded by the demux library; `WebPDecode` rejects them | rejected, as `WebPDecode` does |
| Cropping, rescaling | supported via `WebPDecoderOptions` | `UNSUPPORTED_FEATURE` |
| YUV / `WebPDecodeYUV` | supported | returns null / `UNSUPPORTED_FEATURE` |
| Incremental / streaming decode (`WebPIDecoder`) | supported | not provided |
| Vertical flip, output into a caller buffer and stride | supported | supported |
| `WebPGetFeatures` / `WebPGetInfo` | parse any WebP header | lossless and lossy; report failure on truncated headers; `format` is 1 (lossy) or 2 (lossless); for lossy, `has_alpha` is set by the VP8X alpha flag or an `ALPH` chunk |
| Lossy IDCT on overflowing coefficients | each build uses its own inverse DCT (plain C, SSE2, NEON); they agree on every real stream but not on corrupt ones whose coefficients overflow 16 bits | follows libwebp's x86-64 (SSE2) build, which is what the tests compare against |
| Lossless alpha whose last symbol runs past the end of the `ALPH` chunk | accepted when the alpha uses only a color-indexing transform (libwebp's 8-bit alpha path stops reading at the last pixel and checks the end of input only for pixels still missing); rejected otherwise | rejected (`Bitstream`). Only corrupt or truncated files hit this; the fuzz harness recognizes it (`AlphaTailDeparture` in `difftest/diff.c`) |
| Exact failure status codes | libwebp's | may differ; verilith-webp distinguishes `Bitstream` (rejected), `Unsupported` and `OutOfMemory` |
| Allocation failure building Huffman tables | returns an error | Rust aborts if a `Vec` growth fails (the one place the proof's `OutOfMemory` path is not threaded through; all image-sized allocations use the checked primitives and return `OutOfMemory`) |

## Design

- `src/spec.rs`: the format as total functions — the container (RIFF/VP8X/VP8L
  chunks), the VP8L header, the prefix codes, the color cache, the backward
  references, and the four transforms — plus the dimension caps the format
  imposes.
- `src/bitreader.rs`: a 64-bit little-endian bit window, proven to read exactly
  `spec::bits` and to decode exactly `spec::read_symbol`, charging ghost work
  on every refill.
- `src/huffman.rs`: canonical prefix-code tables built from code lengths
  (on the code spec and table lemmas shared with verilith-zlib in `verilith_core::huffman`), proven to accept exactly the well-formed codes and to decode
  each symbol as the canonical code requires — the CVE-2023-4863 site, here
  proven overflow-free.
- `src/codes.rs`: reading the code-length code and the per-symbol code lengths
  (simple and normal), and the five prefix codes of a Huffman group.
- `src/pixels.rs`: the pixel loop — literals, backward references with the
  distance-mapping plane table, and the color cache — proven to reproduce
  `spec::decode_with` in bounded work per pixel.
- `src/image.rs`: the entropy-coded image, with the color cache size and the
  meta-prefix-code image that selects a Huffman group per block.
- `src/transform.rs`, `src/undo.rs`, `src/pxops.rs`: the four transforms and
  their inverses — predictor (14 modes), color, subtract-green and
  color-indexing (with pixel bundling) — each proven to invert its spec and
  restore the pre-transform width.
- `src/container.rs`: RIFF/WebP parsing (`VP8 `, `VP8L`, `VP8X`, chunk
  skipping, padding, size checks), proven to locate the VP8L payload or to
  classify the file as lossy or malformed exactly as the spec says.
- `src/decode.rs`: the top-level VP8L decode — header, transform chain, main
  image, transform inversion — with the linear-work theorem.
- `src/capi.rs` (trusted): the libwebp-compatible C ABI (`vwebp_Decode*`,
  `WebPGetInfo`, `WebPGetFeatures`, the decode-buffer and decoder-config entry
  points) and a safe Rust API (`decode`, `decode_to`, `get_features`). Exported
  as `vwebp_*`, or under the original libwebp names with the `webp-abi`
  feature.
- `src/vx.rs`, `src/vpred.rs`, `src/vpx.rs`, `src/vlemmas.rs`: the SIMD
  inverse transforms (see [Verified SIMD](#verified-simd)).

The lossy decoder (libwebp's `src/dec/vp8_dec.c`, `tree_dec.c`,
`quant_dec.c`, `frame_dec.c`, `src/dsp/dec*.c`, `upsampling.c` and
`alpha_dec.c`, file for file):

- `src/vp8spec.rs`: the specification of RFC 6386 written so far, and the
  lemmas about it (a refilled or renormalized window is the same number).
- `src/vp8bool.rs`: the boolean decoder, with libwebp's 56-bit refills and
  its exact end-of-input and corrupt-input behaviour (`VP8GetSigned`'s sign
  mask included). Its invariant holds on any input, valid or not, and
  `BoolReader::rel` ties its window to the specification's decoder state.
  The range is kept as the last decision left it, not yet normalized: with
  `s` its normalization shift, RFC 6386's split
  `1 + ((((range << s) - 1) * prob) >> 8)` equals
  `(((range * prob) << s) + 256 - prob) >> 8`, so the multiply starts
  before the shift count is known and the dependency chain from one
  decision to the next is shorter (`lemma_lazy_split`). The shift count
  itself (`sh`, the range's leading zeros) is kept from the step that
  produced the range, an invariant of the reader (`sh_ok`).
- `src/vp8parse.rs`: the frame header (segments, loop filter, partitions,
  quantizers, token probabilities), the intra modes and the DCT/WHT tokens.
- `src/vp8dsp.rs`: the inverse transforms (the SSE2 IDCT's 16-bit lane
  arithmetic, two blocks at a time, and the C AC3, DC and WHT), the 16x16,
  8x8 and ten 4x4 intra predictors, and the simple and normal loop filters
  (sixteen lanes at a time, in the byte arithmetic of libwebp's SSE2
  filters; both chroma planes' edges as one block).
- `src/vp8p4.rs`: the 4x4 intra predictors as byte shuffles from one
  table, with the proof that the table selects each mode's pixels, and
  the choice between them and `vp8dsp::pred4` (`pred4_fast`).
- `src/vp8frame.rs`: the macroblock loop, in libwebp's scratch layout and
  order (parse a row, reconstruct each macroblock, then filter the row), into
  `Planes` whose shape is proven to cover the frame.
- `src/vp8yuv.rs`: libwebp's "fancy" upsampler (two output lines per pair
  of chroma lines, as `UpsampleRgbaLinePair` does) and its 14-bit YUV to
  RGB, written straight to RGBA, BGRA, ARGB, RGB or BGR.
- `src/lossy.rs`: the lossy container (`VP8X`, `ALPH`, chunk walking with
  libwebp's size checks) and the alpha plane (raw or VP8L-coded through the
  verified lossless decoder, then unfiltered).

## Tests

`difftest/` compares verilith-webp against libwebp 1.6.0: `diff.c` decodes a file with
both `WebPDecodeRGBA` and `vwebp_DecodeRGBA` and asserts that both reject it or
both decode it to the same bytes. verilith-webp agrees with libwebp on every file of:

- synthetic lossless images and container variants (`scripts/make_images.py`,
  `scripts/make_containers.py`);
- the same images encoded lossy by cwebp under six option sets that cover the
  loop filter types and strengths, segments, partition limits, sharp YUV and
  the alpha methods and filters (`scripts/make_lossy.sh`);
- all 131 files of [libwebp-test-data](https://github.com/webmproject/libwebp-test-data),
  among them the VP8 conformance vectors and lossy files with alpha;
- the fuzzer's regression files in `difftest/regress/`.

`examples/vdwebp.rs` decodes a `.webp` to a PAM image and is byte-identical to
`dwebp -pam`.

`scripts/fuzz.sh` builds `difftest/diff.c` as a libFuzzer target
(`-fsanitize=fuzzer,address`) that aborts on any disagreement with libwebp, and
runs it coverage-guided, with the Rust side built with overflow checks. With
lossy and lossless seeds, a 30-minute three-worker run (1.2 million inputs)
finds no disagreement and no sanitizer report. Earlier runs found two lossy
disagreements, both on corrupt streams (libwebp's `VP8GetSigned` sign mask
when the bool decoder's value outgrows its range), now fixed and kept in
`difftest/regress/`, and the one documented alpha departure above.

The proofs found one bug the fuzzer had not: the lossy container read the
frame size one byte past the end of a file whose VP8 data is exactly ten
bytes (`difftest/regress/vp8-10-byte-frame.webp`).

## CVE-2023-4863

CVE-2023-4863 (also tracked as CVE-2023-41064) was a heap buffer overflow in
libwebp's `BuildHuffmanTable`: a lossless WebP whose Huffman code lengths made
the second-level table larger than the fixed allocation wrote past the buffer.
It was exploited in the wild against browsers and messaging apps.

verilith-webp builds those tables in `huffman::build`, proven to keep every write in
bounds and to reject any invalid code, for every possible set of code lengths —
so this class of overflow cannot occur, whatever the input. That proof is the
guarantee; the fuzzing and the differential tests are the empirical
cross-check.

`scripts/make_cve_trigger.py` emits WebP files that drive exactly that path
(a maximally deep valid code-length code, an over-subscribed one, and an
incomplete one). `difftest/cve_demo` decodes each with both libwebp 1.6.0 and
verilith-webp and confirms they agree — both reject the malformed tables safely:

```
$ make -C difftest cve_demo
$ python3 scripts/make_cve_trigger.py /tmp/cve && ./difftest/cve_demo /tmp/cve/*.webp
file                          libwebp 1.6.0       verilith-webp (verified)    result
cve_depth.webp                rejected safely     rejected safely     agree, no overflow
cve_incomplete.webp           rejected safely     rejected safely     agree, no overflow
cve_oversub.webp              rejected safely     rejected safely     agree, no overflow

PASS: both decoders safe on every input, no AddressSanitizer report
```

## Performance

Full decode to RGBA against libwebp 1.6.0, in decode megapixels per second
(higher is better). Each decoder ran alone in its own process, pinned to one
core with `taskset`, best of 20 decodes after a warm-up, with both measured
in the same sitting (`scripts/bench.sh`). verilith-webp is built with no `target-cpu`
flag: it detects AVX2 at run time, as libwebp does. Both decoders produce
byte-identical output on every file.

| file | pixels | libwebp MP/s | verilith-webp MP/s | verilith-webp / libwebp | SIMD transforms only | before SIMD |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ss (1310x1191 screenshot) | 1.56 M | 176 | 168 | 0.96 | 0.92 | 0.35 |
| verus-demo (1660x588) | 0.98 M | 194 | 188 | 0.97 | 0.92 | 0.33 |
| header (3000x200) | 0.60 M | 100 | 97 | 0.97 | 0.96 | 0.49 |
| intro-highres (1000x256) | 0.26 M | 117 | 107 | 0.92 | 0.86 | 0.43 |
| pridosaurus (512x512) | 0.26 M | 98 | 80 | 0.82 | 0.76 | 0.47 |
| big (4000x3000, noisy) | 12.0 M | 44 | 40 | 0.90 | 0.82 | 0.59 |

**libwebp is still faster, by 3% to 18%.** verilith-webp does not beat it on any
file in this corpus. The inverse transforms are vectorised and verified
(below). The pixel decode now has a fast path for the two common symbols, a
literal pixel and a color cache hit: when at least 8 input bytes remain, it
refills the bit reader once and does up to four table lookups with no
per-symbol input checks (`pixels::try_lit`, `bitreader::peek`). That is
proven equal to the spec's `read_symbol` like the general path, and gained
3% to 10%. What is left is mostly the serial chain of Huffman lookups
(each one needs the previous one's length), the backward-reference copies,
and page faults on the freshly allocated output, which both decoders pay.
On `pridosaurus`, most pixels are color cache hits and backward references,
and libwebp's packed tables decode those in fewer steps.

All numbers come from one sitting. Each decoder ran in its own process,
pinned to one core, and the table shows its best of three runs of 20
decodes. "SIMD transforms only" is the ratio without the fast path, in
the same sitting; "before SIMD" is the ratio for the all-scalar release.
Absolute numbers vary with the machine; run `scripts/bench.sh` to reproduce
on yours.

### Lossy

The same harness on lossy files (VP8, some with `ALPH`), decoding to RGBA.
Best of three runs of 20 decodes each, one x86-64 core, both decoders
built for SSE2/AVX2 with run-time dispatch:

| file | size | libwebp MP/s | verilith-webp MP/s | verilith-webp / libwebp |
| --- | ---: | ---: | ---: | ---: |
| bryce (photo, q≈80) | 11158x2156 | 92.9 | 73.7 | 0.79 |
| photo-q75 | 2400x1800 | 92.4 | 73.5 | 0.80 |
| photo-q95 | 2400x1800 | 55.3 | 46.9 | 0.85 |
| lossy_extreme_probabilities | 800x534 | 64.3 | 55.9 | 0.87 |
| vp80-00-comprehensive-008 | 1432x888 | 298.7 | 198.3 | 0.66 |
| lossy_alpha1 (with alpha) | 1000x307 | 141.4 | 172.7 | 1.22 |
| pridosaurus-q75-alpha | 512x512 | 105.7 | 142.2 | 1.35 |

That table predates the changes below marked "later". On the 24 Kodak
photos at quality 75 (vbench's `webp-lossy` suite, 768x512 each, RGBA,
best of repeated decodes, same machine, a Xeon with AVX-512), the plain
lossy decoder went from 0.74x libwebp to **level with it (1.00x to 1.03x
across runs) when both are built for the host CPU** (`-C target-cpu=native`),
and to 0.89x with no `target-cpu` flag, where the boolean decoder's shifts
and bit counts compile to slower instructions. Output is byte-identical.
On an Apple M3 Pro the same files measured 0.87x before any NEON work,
0.88x to 0.89x with the NEON inverse transform, 0.92x with the NEON color
conversion and chroma upsampling, and **0.98x** with the NEON loop filter
(instructions 1.08x and cycles 1.02x libwebp's; 0.92x to 1.02x per photo;
a noisier full-suite sitting the same night read 0.96x). A time profile
there shows coefficient parsing level with libwebp, the loop filter and
color conversion ahead of it, and 4x4 prediction behind, with 2.7% of a
decode on the branch that picks the prediction mode. A table-driven
4x4 predictor that removes that branch was then measured there and was
slower (0.965x against 0.98x, 1.7% more cycles in each of three sittings),
so AArch64 keeps the branch and stays at 0.98x.

On the table's files **libwebp was faster on plain lossy files, by 13% to
34%; verilith-webp is faster on lossy files with alpha** (its alpha plane goes
through the vectorized lossless decoder). The first lossy release ran at
about 0.57x libwebp on the photos. Since then:

- the loop filters run sixteen lanes at a time, with libwebp's SSE2 byte
  arithmetic;
- the transposes are verilith-simd interleaves;
- the inverse transform does two blocks at a time;
- the chroma of a line pair is upsampled together;
- on x86 the YUV conversion is SSE2;
- the output is written straight in the caller's layout;
- later: the boolean decoder keeps its range unnormalized and its shift
  count from the step before, so a decision's multiply does not wait for
  either (see Design), reads its sign bits without a branch and refills
  with one byte swap;
- later: on x86 the loop filters are SSE2 intrinsics that keep a block's
  rows in registers from load to store (`filter16_vec`, `filter8uv_vec`),
  where the lane code went through memory between steps;
- later: with AVX2, RGBA, BGRA and ARGB rows are converted and interleaved
  in one pass, 32 pixels per step (`yuv_pack4_avx2`);
- later, on AArch64: each pass of the inverse transform is NEON
  intrinsics (`idct_pass_neon`), with `sqdmulh` and a halving shift for
  `_mm_mulhi_epi16`; LLVM had left most of the lane code scalar there
  (459 instructions for a pair of blocks, 101 now);
- later, on AArch64: RGBA, BGRA and ARGB rows are converted and
  interleaved in one pass, 16 pixels per step (`yuv_pack4_neon`: `sqdmulh`
  on the bytes shifted left by 7, and saturating narrowing shifts), and
  the two chroma lines between a pair of chroma rows are upsampled 16
  pairs per step with byte averages (`upsample_pair_neon`, libwebp's
  `UPSAMPLE_16PIXELS`), written straight into the lines;
- later, on AArch64: the loop filters are NEON intrinsics, the same
  kernels as the SSE2 ones (they are generic over the vector type, `Lfv`)
  with NEON's single instructions where it has them (`uabd`, `cmhs`,
  `sshr` on bytes, `sqshrn`); counted under emulation on one photo this
  removes 4.9% of the decode's instructions (the filters' own count drops
  by about a quarter) (measured on an M3: 0.92x to 0.98x of libwebp);
- later: the inverse transform's passes are inlined, the 4x4 DC predictor
  sums its eight neighbours in one expression, and the 4x4 modes dispatch
  through a jump table;
- later, in x86 builds for SSSE3 (for example `-C target-cpu=native`):
  the 4x4 modes other than TM are not dispatched at all. Each block is
  three `pshufb` shuffles of its edge bytes and their averages, the
  shuffles loaded from a table by mode (`pred4_tbl`), about 1.5% faster
  there. Chosen at run time it would sit behind a call into a
  `#[target_feature]` function, so a plain x86-64 build keeps the jump
  table. The same kernel is proven for NEON (`tbl`) but is not used: on
  an Apple M3 it cost 1.7% more cycles per decode than the jump, which
  that core evidently predicts well, even though a time profile had put
  2.7% of a decode on that line.

Before the later changes, counted with callgrind on photo-q75, verilith-webp ran about 476M instructions
per decode against libwebp's 397M (it was 1,107M). Coefficient decoding is
level with libwebp, at about 200M each. The remaining gap is spread across
the loop filters' gathers and transposes, zeroing the frame planes and the
output buffer (`calloc`), and the intra predictors. These numbers are
from x86; NEON (AArch64) takes the same structure through verilith-simd's NEON
wrappers.

### Verified SIMD

The lossless inverse transforms use SSE2/SSSE3/AVX2 through
[verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd), a set of Verus specifications for the x86 intrinsics
that models each vector as its sequence of bytes. The kernels are proven
against the same `spec.rs` functions as the scalar code, so the theorem about
the decoder is unchanged:

- `src/vx.rs`: subtract-green (`pshufb` + `paddb`, 8 pixels per step) and the
  color transform (`pmulhw` on the green byte shifted to the high half, 8
  pixels per step).
- `src/vpred.rs`, `src/vpx.rs`: the predictor transform. Modes 2, 3, 4, 8, 9
  and the constant modes run 8 pixels per AVX2 step (rows above are already
  decoded); mode 1 is an in-register prefix sum; the modes that depend on the
  pixel to the left (5, 6, 7, 10–13) are sequential, with the left pixel kept
  in a register and SWAR averaging and `psadbw` for the select predictor.
- `src/vlemmas.rs`: the bridge between the byte view of a vector and the
  spec's ARGB pixel functions.

The lossy decoder's SIMD is proven to the same depth as the rest of the
lossy path (memory safety, no overflow, termination); its agreement with
libwebp is tested. Most of it is plain Rust written so that LLVM vectorizes
it (sixteen byte lanes in the loop filters, eight 16-bit lanes in the
inverse transform), and the rest calls verilith-simd on both SSE2 and NEON:

- the normal loop filter, on SSE2 and on NEON: the mask and
  high-variance tests and the inner and macroblock-edge filters in
  libwebp's signed saturating byte arithmetic (`mask_hev_vec`,
  `lanes4_vec`, `lanes6_vec`), proven lane for lane equal to the scalar
  filter of RFC 6386 section 15. The kernels, the transposes and the loads
  and stores are written once over a vector trait (`Lfv`) whose operations
  state what they do to each byte; `__m128i` and `uint8x16_t` each
  implement it, with each operation proven from its intrinsics' specs;
- on x86 in a build for SSSE3 (`-C target-cpu` or
  `-C target-feature=+ssse3`; proven for AArch64 too, but not used
  there because it measured slower), 4x4 intra prediction
  (`vp8p4::pred4_tbl`): every mode but
  TM is three `tbl` (`pshufb`) shuffles of the block's edge bytes and their
  two- and three-byte averages, ORed together, the shuffles read from a table
  indexed by the mode. The kernel is written once over a vector trait
  (`P4v`), as the loop filter is. The table is data the proof reads, not trusted:
  for each mode and each of the sixteen pixels Verus checks that the
  entry selects the value RFC 6386 section 12.3 gives that pixel
  (`lemma_p4_table`). The entry point `vp8p4::pred4_fast` has the
  contract of `vp8dsp::pred4`, the ten-way match, which stays for TM and
  for every other target;
- on AArch64, the inverse transform's passes (`idct_pass_neon`), proven
  lane for lane equal to the 16-bit lane arithmetic the x86 code keeps;
- with AVX2, the fused YUV-to-RGB conversion and four-channel interleave
  (`yuv_pack4_avx2`), proven equal to the scalar conversion per pixel;

- the transposes: the vertical-edge loop filters turn sixteen 8-byte lanes
  into eight 16-byte rows and back with byte-interleave rounds
  (`shuffle_block`), and the inverse transform's 4x4 transposes are 16-,
  32- and 64-bit interleaves (`transpose_halves`);
- the output: chroma lines are interleaved from their even and odd pixels
  (`interleave2`), and RGBA, BGRA and ARGB pixels from four channel lines
  (`pack4`);
- on x86 only, the YUV-to-RGB arithmetic, sixteen pixels per step as
  `ConvertYUV444ToRGB_SSE2` does it (`yuv_to_rgb_sse2`); on AArch64 that
  loop is left to LLVM.

Dispatch happens at run time (`is_x86_feature_detected!("avx2")`). Without
AVX2 (AArch64, older x86) the predictor and color transforms still go a run
of one block at a time, with the same SWAR mode kernels and a scalar loop
for the rest (`unpredict_swar`, `uncolor_run_swar`), rather than one pixel
at a time with a division per pixel.

## Building

```
cargo build --release                 # the library and C ABI (libverilith_webp.a)
cargo build --release --example vdwebp # a dwebp-style decoder to PAM
cargo verus verify                     # re-check every proof (needs Verus + Z3)
```

No `target-cpu` flag is needed: the SIMD kernels are selected at run time.
The differential tests and benchmarks need a libwebp checkout and CMake build;
point `LIBWEBP_SRC` and `LIBWEBP_BUILD` at them (see `difftest/Makefile`).
