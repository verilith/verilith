# verilith-jpeg

A verified JPEG decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus). It decodes baseline, extended
sequential and progressive Huffman JPEG files (8 bits per sample, greyscale or
three components) to 8-bit grey or RGB, and gives the same pixels as
libjpeg-turbo 3.1.2 does with its default settings. It can be linked in place
of libjpeg-turbo's decode path through the TurboJPEG C API. It decodes only;
there is no encoder.

The marker parser, Huffman decoding, every baseline and progressive scan
type, restart handling, dequantization, the inverse DCT, chroma upsampling
and colour conversion are proven against a specification of the format,
down to the value of every output byte. `cargo verus verify` checks 523
functions with no errors.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no integer overflow, no panics | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness: for every byte string, `decode` returns the image `spec::jpeg_decode` gives it, pixel for pixel, and returns `Invalid` exactly when the specification gives it none | `decode::decode` |
| The only other result is `OutOfMemory` (a failed allocation, or an image too large for the machine's address space) | `decode::decode` |
| The coefficients after all scans are the specification's | `decode::decode_coefs` against `spec::jpeg_coded` |
| Each scan type writes exactly the coefficients T.81 says: baseline, DC first and refinement, AC first and refinement, with end-of-band runs | `block::*` against `spec::base_block`, `dc_first`, `ac_first`, `ac_refine` |
| The Huffman decoder, with its 10-bit lookahead table and 16-bit window, returns the symbol of T.81's DECODE procedure | `huff::decode` against `spec::huff` |
| The inverse DCT equals the specification's (libjpeg's `jidctint.c`) on all its paths: on AArch64, NEON intrinsics in 16-bit lanes for blocks whose magnitudes sum to at most 2120 (nearly every block of a photograph) and in 32-bit lanes for the others whose dequantized values fit in 15 bits; elsewhere 32-bit arithmetic that compilers vectorize; and 64-bit arithmetic for the rest | `idct::idct_into`, `idct16::idct16_neon`, `idct_neon::idct_neon` against `spec::idct` |
| Upsampling and colour conversion equal the specification's, including the branch-free kernels compilers vectorize and, on AArch64, colour conversion with NEON intrinsics | `render::up_row`, `render::ycc_row`, `color_neon::ycc16` |

`read_header` (used by the TurboJPEG header calls) is verified for memory
safety and termination only; it reuses the verified segment parser.

[TRUST.md](TRUST.md) lists everything the proofs assume rather than prove.
In short: the specification (`src/spec.rs`), two allocation primitives, the
specifications of 35 NEON intrinsics in
[verilith-simd](https://github.com/verilith/verilith/tree/main/crates/simd) (AArch64 only), the
unverified C glue (`src/capi.rs`, `src/tj.rs`), and Verus, vstd, Z3 and the
Rust compiler.

## What is not covered

verilith-jpeg returns `Invalid` for all of these; none of them is decoded
approximately.

- Arithmetic-coded, lossless and hierarchical JPEG (SOF3, SOF5 to SOF15).
- 12-bit and 16-bit samples.
- Four-component files (CMYK and YCCK), and two-component files.
- Sampling factors where some component's factor does not divide the
  largest evenly (libjpeg-turbo rejects these too).
- Scaled decoding (1/2, 1/4, 1/8), cropping, colour quantization, and output
  other than grey or RGB at the image's own size. The TurboJPEG layer derives
  the other RGB pixel orders from the RGB result.
- Embedded metadata (EXIF, ICC profiles, comments) is skipped, not returned.
- Streaming input and output: the whole file is decoded from memory in one
  call.

### Departures from libjpeg-turbo

verilith-jpeg is checked against libjpeg-turbo 3.1.2 decoding with its defaults
(accurate integer DCT, fancy upsampling, block smoothing on). Where both
decode a file the output is byte-identical; the differential tests and the
fuzzer check this.

| area | libjpeg-turbo 3.1.2 | verilith-jpeg |
| --- | --- | --- |
| Damaged entropy-coded data, truncated files, missing or misplaced restart markers | a warning, then a best-effort image | the same image, byte for byte; no warning is reported |
| Progressive files that end before every coefficient has arrived | block smoothing estimates the missing AC coefficients | no smoothing: the coefficients that arrived are used as they are. Complete progressive files are identical. |
| Coefficients too large for 16-bit arithmetic (damaged files only) | the SIMD inverse DCT and the C inverse DCT give different pixels | the C code's pixels. Tests of damaged files run libjpeg-turbo with `JSIMD_FORCENONE=1`. |
| Arithmetic-conditioning (DAC) segments | validated, used only by arithmetic coding | validated the same way, then ignored |
| A sequential file with no Huffman tables | standard tables are used | the same, for the first scan |
| Warnings (`TJPARAM_STOPONWARNING`, `tj3GetErrorCode`) | reported | never reported: a file libjpeg-turbo decodes with a warning decodes here with a plain success |

## The C API

`vjpeg_decode` and `vjpeg_free` (`src/capi.rs`) are the small API: bytes in,
a grey or RGB buffer out.

`src/tj.rs` is the TurboJPEG decode API, exported as `vjpeg_tj*` and, with
`--features turbojpeg-abi`, under TurboJPEG's own names, so a program built
against `turbojpeg.h` links with `libverilith_jpeg.a` unchanged: `tj3Init`,
`tj3Destroy`, `tj3DecompressHeader`, `tj3Decompress8`, `tj3Set`, `tj3Get`,
`tj3GetErrorStr`, `tj3GetErrorCode`, `tj3Alloc`, `tj3Free`,
`tj3GetScalingFactors`, `tj3SetScalingFactor`, and the older
`tjInitDecompress`, `tjDecompressHeader`, `tjDecompressHeader2`,
`tjDecompressHeader3`, `tjDecompress2`, `tjDestroy`, `tjGetErrorStr`,
`tjGetErrorStr2`, `tjGetErrorCode`, `tjAlloc`, `tjFree`,
`tjGetScalingFactors`.

What it does not do: scaling factors other than 1/1, cropping, YUV plane
output, 12- and 16-bit output, CMYK, ICC profile extraction, and a colour
image to `TJPF_GRAY` (an error here). `TJPARAM_FASTUPSAMPLE` and
`TJPARAM_FASTDCT` are accepted and ignored, so the output is always the
accurate one. All RGB pixel formats, alpha and filler bytes, bottom-up
output and row pitch are supported.

## Design

`decode` runs two stages, each proven against the matching part of the spec:

1. **Coefficients** (`parse`, `scan`, `block`, `huff`, `bits`): the marker
   segments are walked to EOI, tables are installed, and each scan's
   entropy-coded data is decoded into one array of coefficients per
   component, as libjpeg's coefficient controller does for progressive
   files. The bit reader holds up to 64 bits and removes byte stuffing as it
   refills, four bytes at a time when none of them is 0xFF, and using bits
   only lowers a count (used bits stay above the live ones until they are
   shifted out, and reading past the end of the data is noticed from the
   count alone); a Huffman code
   of 10 bits or fewer takes one table lookup, and the value after it comes
   out of the buffer in the same read.
2. **Pixels** (`idct`, `render`, `decode::render_x`): each component is
   dequantized and transformed to a plane of samples, then rows are
   upsampled and colour-converted into the output.

A file whose frame is sequential and whose first scan holds every component
(most baseline files) is streamed (`src/stream.rs`): the scan is decoded one
MCU row at a time into a window of each component's coefficients, and the
row's samples are computed from the window before it is reused. The whole
coefficient arrays that the specification speaks of exist only as ghost
state. The proof shows that a block decoded into the window is the block
decoded into the whole array, that later blocks leave earlier samples'
coefficients alone, and so that each plane ends up as the samples of the
final coefficients. The specification makes a second scan of such a file an
error, so nothing is ever needed from the coefficients again.

The inverse DCT works on all eight columns, then all eight rows, of a block
at once in 32-bit arithmetic (the second pass wraps, and the proof shows the
ten bits the range limit reads are still exact). On AArch64 that is
hand-written NEON (`src/idct_neon.rs`): the intrinsics come from verilith-simd, which
gives each one a specification, and the proof follows the block lane by lane
from the widening multiply that dequantizes it to the saturating narrow that
clamps it. A block with nothing in rows 4 to 7 takes a first pass
with those inputs left out, and one with nothing in columns 4 to 7 either
sends only half its columns through it and takes the short pass again in
the other direction; both are proven to give what the full passes would.

Nearly every block of a photograph is smaller still, and takes a path in
16-bit lanes (`src/idct16.rs`) that does about a fifth less work: the block
is dequantized by a 16-bit multiply, each pass is widening multiplies and
multiply-adds by one lane of a table of constants, the first pass's results
are narrowed back to 16 bits, and the second pass's sums need only their
high halves. The proof rests on one test made at run time, that the
magnitudes of the dequantized block sum to at most 2120. From that it shows
the first pass's results fit 16 bits with room for the second pass's sums,
and that the second pass's results are inside the ten bits the range limit
reads, so a saturating narrow is the same as the limit's table. A block that
fails the test (one or two in a hundred in photographs) takes the 32-bit
path above and gets the same proof of the same result. Elsewhere the same arithmetic is plain Rust (`idct::idct_fast`)
written so the compiler vectorizes it, with no intrinsics. Colour
conversion on AArch64 is NEON too (`src/color_neon.rs`), sixteen pixels at a
time in 16-bit lanes, with the same branch-free Rust loop for the last
pixels of a row and for other targets. The upsampling kernels are
branch-free loops over slices that the compiler vectorizes on every target.

## Tests

- `difftest/diff FILES...` (`make -C difftest`) decodes each file with verilith-jpeg
  and with libjpeg-turbo and compares dimensions and every byte. 1,368
  files (libjpeg-turbo's and other decoders' test images, and 144 files made
  from the Kodak photographs in baseline, progressive, 4:4:4, 4:2:2, 4:2:0
  and grey): all identical. 900 damaged files (truncations, flipped bits,
  bad restart markers), against libjpeg-turbo's C code: 496 identical, 404
  rejected by both, none different.
- `make -C difftest tjcheck FILES="..."` runs the same TurboJPEG calls
  against `libturbojpeg.a` and against verilith-jpeg in every pixel format, top-down
  and bottom-up, through both the v3 and the older API: the same on those
  1,368 files.
- `scripts/fuzz.sh SECONDS CORPUS [SEEDS...]` is a libFuzzer differential
  fuzzer: a file is a failure if one decoder accepts it and the other does
  not, or the pixels differ. It found one rule the specification had missed
  (libjpeg-turbo rejects a DAC segment with a bad table index), now in the
  specification; about nine million executions since then found nothing.

- `scripts/armcheck.sh DIR...` builds verilith-jpeg for AArch64, decodes every file
  under qemu and compares the pixels with the x86-64 build's, which is how
  the NEON path is tested from an x86-64 machine: the same on all 2,295
  files above (intact and damaged).

GitHub Actions is not used; the proofs and the tests above are run locally.

## Performance

Total time to decode 24 photographs (768×512, the Kodak set) to RGB, best of
15 runs each, on a 4-core x86-64 cloud VM. Lower is better. These numbers are
noisy; treat them as a rough guide.

| files | verilith-jpeg | libjpeg-turbo, C code only | libjpeg-turbo, SIMD |
| --- | ---: | ---: | ---: |
| baseline 4:2:0 | 74 ms | 54 ms | 28 ms |
| progressive 4:2:0 | 132 ms | 102 ms | 74 ms |
| baseline 4:4:4 | 139 ms | 79 ms | 47 ms |
| baseline grey | 59 ms | 33 ms | 27 ms |

On this machine verilith-jpeg is about 1.3 to 1.8 times slower than
libjpeg-turbo's C code and 1.8 to 3 times slower than its hand-written SIMD.

On an Apple Silicon Mac, measured with
[vbench](https://github.com/verilith/verilith/tree/main/bench) against
libjpeg-turbo 3.1.2 with NEON (geometric mean over the 24 photos, all
outputs equal, at commit 122d22c): baseline 4:2:0 runs at about 0.87 times
libjpeg-turbo's speed, baseline 4:4:4 at about 0.855 times and progressive
at about 0.95 times. A profile of one baseline photo there puts entropy
decoding at 1.04 times libjpeg-turbo's cycles, the inverse DCT at 1.23
times, colour conversion at 1.18 times and chroma upsampling at 1.35 times,
1.11 times in all. Those figures do not yet include the current inverse
DCT in 16-bit lanes. Counting instructions under emulation, it took
dequantization and the inverse DCT from 9.2 to 7.2 million for three decodes
of one 4:2:0 photo, and a whole decode is now about 5% more instructions
than libjpeg-turbo built with clang, as on the Mac.

Where the instructions go on a baseline 4:2:0 photo on AArch64: about 51%
Huffman decoding and the bit reader, 29% dequantization and the inverse DCT,
20% upsampling and colour conversion.
Progressive and multi-scan files are decoded to whole-image coefficient
arrays first, as in libjpeg-turbo. Every file still gets whole planes of
samples before upsampling, where libjpeg-turbo keeps a few rows.

## Building

```sh
cargo build --release                            # libverilith_jpeg.a and the Rust library
cargo build --release --features turbojpeg-abi   # with TurboJPEG's symbol names
cargo build --release --example djpeg            # djpeg FILE > out.ppm
./scripts/verify.sh                              # needs cargo-verus and z3 on PATH
```

The proofs are checked with Verus `0.2026.11.02.8bf68ee` (vstd
`0.0.0-2026-11-01-0251`).
