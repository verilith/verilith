# verilith-png

A verified PNG decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus). It reads every PNG image type
(grey, RGB, palette, grey-alpha and RGBA, at every bit depth, interlaced or
not) into 8-bit RGBA or into the image's own pixel format. It decodes only;
there is no encoder, and it does not interpret ancillary chunks other than
tRNS (no gamma, colour profiles, text or animation).

The chunk parser, the image-data decompression (through
[verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib), itself verified), the
five row filters, Adam7 deinterlacing and both output formats are proven
against a specification of the format. `cargo verus verify` checks 302
functions with no errors.

libpng's security history is mostly memory-safety bugs in exactly these
places: chunk lengths ([CVE-2017-12652](#cves)), palette and transparency
sizes (CVE-2004-0597, CVE-2015-8126), row-size arithmetic (CVE-2014-9495,
CVE-2015-0973, CVE-2018-13785) and pixel conversion (the 2025 simplified-API
CVEs). In verilith-png that class of bug is ruled out for every input by the proofs.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no integer overflow, no panics | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness: the decoded header and pixels equal the specification's for every file the spec accepts; `Invalid` is returned exactly when the spec rejects the file | `top::decode` against `spec::decode` |
| The only other results are `TooLarge` (the caller's memory limit) and `OutOfMemory` (a failed allocation) | `top::decode` ensures |
| No allocation is sized from the header alone: image data larger than the compressed data could ever produce (1032 bytes per input byte) is rejected before allocating | `decode::inflate_exec`, via verilith-zlib's `theorem_output_bound` |
| The chunk walk follows the specification's rules for CRCs, chunk order, PLTE, tRNS and IDAT | `chunks::walk_exec` against `spec::walk` |
| Each row filter reconstructs exactly `spec::recon`, in place | `unfilter::unfilter_row`, `unfilter::unfilter_rows` |
| Every Adam7 pass is reconstructed at the right place | `passes::reconstruct` against `spec::pass_images` |
| RGBA and native output equal `spec::rgba8` and `spec::native` pixel for pixel, on the general (sub-byte) path, the direct non-interlaced paths and the row-by-row deinterlacer | `output::to_rgba8`, `output::to_native`, `fast::*`, `deint::*` |

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification — PNG (ISO/IEC 15948, W3C PNG 3rd
  edition) as total functions over `Seq<u8>`. Review it against the PNG
  standard; if the spec is wrong, the proofs still hold, against the wrong
  thing. Every place it follows libpng rather than a strict reading of the
  standard is marked `libpng:` in a comment.
- `src/prims.rs`: two `#[verifier::external_body]` primitives — a
  non-overlapping copy and a zeroed allocation. Each `requires` clause is
  the bounds fact Verus proves at every call site. (The unchecked byte get
  and set next to them are verified against vstd's spec of
  `get_unchecked`.)
- verilith-zlib's trusted base (its specification of zlib/DEFLATE and its own
  primitives), Verus, Z3 and the Rust compiler.

Everything else in `src/` is verified. `examples/vpngcat.rs` (a command-line
decoder for the tests) and `bench/` are unverified tools.

### Departures from libpng

verilith-png is checked against libpng 1.6.59, decoding with `png_set_expand`,
`png_set_strip_16`, `png_set_gray_to_rgb` and an opaque filler for RGBA, and
with no transformations for the native format. Where both decode a file the
output is byte-identical; the differential tests and the fuzzer check this.

| area | libpng 1.6.59 | verilith-png |
| --- | --- | --- |
| Image data whose zlib stream is damaged after the last byte the image needs (bad Adler-32, truncated end, corrupt trailing blocks) | decodes the image; reads stop once the image is complete | `Invalid`: the whole stream must decompress |
| Image data longer than the image needs | warning, extra bytes ignored | extra bytes ignored (same) |
| Ancillary chunks (gAMA, iCCP, sRGB, text, ...) | parsed, applied on request | skipped unparsed; never change the pixels |
| A PLTE in an RGB image that is a second one, follows tRNS or bKGD, or has a bad CRC or length | ignored | ignored (same); an empty one is an error in both |
| Chunks after the image data | PLTE and unknown critical chunks ignored | same |
| A chunk type whose third letter is lowercase (the reserved bit) | error | error (same) |
| IEND with a bad CRC or with data | CRC checked as for an ancillary chunk, so ignored; data ignored | same |
| Output conversions (gamma, background composition, scaling) | many | 8-bit RGBA or native only |
| Width and height | up to 2^31 − 1, with a default limit of 1,000,000 each | up to 2^31 − 1; memory is bounded by the caller's `limit` instead |
| Streaming / progressive decode, C API | yes | libpng's read API, over the same decoder (below) |

## The libpng API

`src/libpng/` is libpng 1.6.59's read API over the verified decoder, so a C
program written for libpng can decode with verilith-png. Every function is
exported as `vpng_<name>` (`vpng_read_info`); built with `--features
libpng-abi`, under libpng's own names, and `libverilith_png.a` is then a
drop-in libpng for reading: compile against `include/png.h` (libpng's
headers, with a `pnglibconf.h` that says what is here) and link with
`libverilith_png.a` instead of `libpng16.a`. The module is not verified: it
reads the chunks through the caller's I/O functions, does libpng's chunk
handling, and at the first row hands the signature, IHDR, PLTE, tRNS and the
image data to `top::decode`. The pixels then go to the caller the way libpng
gives them.

What is there:

- The sequential reader (`png_read_info`, `png_read_update_info`,
  `png_read_row(s)`, `png_read_image`, `png_read_end`), `png_read_png`, and
  the progressive reader (`png_process_data`, the info, row and end
  callbacks, `png_progressive_combine_row`, pausing).
- The transformations that need no gamma: expand (palette, low-bit grey,
  tRNS), expand 16, strip 16 and scale 16, strip alpha, grey to RGB, filler
  and add alpha, BGR, swap alpha, invert alpha, invert mono, shift (sBIT),
  packing, packswap, swap, and user transforms; interlace handling, with
  the sparkle and rectangle display rows.
- The ancillary chunks of `include/pnglibconf.h` (bKGD, cHRM, eXIf, gAMA,
  hIST, iCCP, iTXt, oFFs, pHYs, sBIT, sRGB, tEXt, tIME, tRNS, zTXt) with
  their `png_get_*` and `png_set_*` functions, unknown chunks (keep lists,
  `png_set_keep_unknown_chunks`, the user chunk callback), CRC actions,
  user limits, benign errors, and the caller's memory, error, warning and
  I/O functions, `setjmp`/`longjmp` included.

What is not: writing (the write functions do nothing and
`png_create_write_struct` returns NULL), the simplified API
(`png_image_*`), gamma correction, background composition, alpha modes, RGB
to grey, quantizing, and the pCAL, sCAL, sPLT, cICP, cLLI and mDCV chunks (read as unknown chunks).

It is checked against libpng 1.6.59 built with the same `pnglibconf.h`
(`include/vpng.dfa`). `difftest/abitest.c` reads a file through every
reader (sequential, rows with a display buffer, `png_read_image`,
`png_read_png`, and the progressive reader fed 1, 7 and 4096 bytes at a
time), with each of 21 transformations, every pair of them and some larger
sets, and prints the header, every `png_get_*` value, each warning and error,
and a hash of the rows; `difftest/abicompare.py` runs it linked with libpng
and with verilith-png and compares the output. On PngSuite and libpng's
test images, crashers and bad-palette files (88,830 cases) and 3,000
damaged files from `fuzz/mutate.py` (27,000 cases), the two print the same,
apart from the departures below. libpng's own read tests (`pngunknown`,
`pngimage`, `readpng`) pass against it (`difftest/upstream.sh`); its other
tests need writing or the simplified API.

Where it departs from libpng:

| area | libpng 1.6.59 | verilith-png |
| --- | --- | --- |
| Damaged image data | an error at the row where it is found, with zlib's message | an error at the first row: `IDAT: invalid image data` |
| Image data damaged after the last byte the image needs | a warning; the image decodes | an error (as for `top::decode` above) |
| Progressive reader | rows as the image data arrives | rows once all of it has arrived; a file that ends inside the image data gets none, and damaged or short image data is an error where libpng gives the rows before the damage |
| Progressive reader, data after the image | "Extra compressed data" warnings, as many as the caller's calls | no warning |
| Damaged compressed text or iCCP | a warning with zlib's message | a warning: "bad compressed data"; the chunk is dropped in both |
| An IDAT chunk with a bad CRC | the error comes after the rows before it are read | the error comes at the first row |
| A caller's read function failing on the chunk header after the image data | at the end of the image | at the first row (with libpng's own I/O, at the same point as libpng) |
| `png_struct` | allocated with the caller's allocator | allocated by Rust; the caller's allocator is used for what `png_malloc` returns |

## Design

`top::decode` runs four stages, each proven against the matching part of
the spec:

1. **Container** (`chunks`, `decode::container_exec`): the signature, IHDR
   and the chunk walk to IEND, checking CRCs (critical chunks, tRNS and bKGD;
   other ancillary chunks are skipped without reading them) and recording the
   palette, tRNS and the ranges of the first run of IDAT chunks.
2. **Inflate** (`decode::inflate_exec`): the IDAT data is gathered and
   decompressed by verilith-zlib straight into a buffer of the exact raw size.
3. **Reconstruct** (`unfilter`, `passes`): rows are unfiltered in place in
   that buffer, each pass's rows compacted forward over their filter bytes.
   The filter loops are specialised per filter type and pixel size, carry
   the left and upper-left pixels in registers, and use the `png` crate's
   short-dependency form of the Paeth predictor (proven equal to the
   standard's).
4. **Output** (`fast`, `output`): for a non-interlaced image whose pixels are
   whole bytes, the native format *is* the reconstructed buffer (truncated,
   no copy), and so is RGBA for an 8-bit RGBA image; other 8- and 16-bit
   images are converted in one linear pass (palette and grey through a
   256-entry table). Interlaced images of 8 or 16 bits are deinterlaced row
   by row (`deint`: odd rows are copied whole from pass 7, even rows take
   each pixel from its pass with shifts instead of divisions), and RGBA is
   then made from that image by the non-interlaced conversion, proven to
   give the same pixels. Sub-byte interlaced images take the general path,
   which computes each output pixel from the pass that holds it.

## Tests

- `cargo test --release` runs `tests/cves.rs`: files shaped like the inputs
  of libpng's CVEs (oversized tRNS and PLTE, palette indices past the
  palette, huge widths, 16-bit conversion, chunk lengths of 2^31, bad CRCs,
  wrong image-data length), each checked against the spec's answer.
- `difftest/compare.sh FILES...` decodes each file with verilith-png and with libpng
  (`difftest/refpng.c`, built by `difftest/build.sh`) in both formats and
  compares the bytes. On 649 files (PngSuite, libpng's and libspng's test
  images and a corpus of photographs and screenshots), in both formats:
  1128 identical, 170 rejected by both, none different.
- `difftest/abicompare.py` and `difftest/upstream.sh` check the libpng
  API (above).
- `fuzz/run.sh OUT N SEED FILES...` writes `N` mutants of the seed files
  (byte flips, mutated and recompressed image data, changed IHDR fields,
  duplicated, dropped and reordered chunks, random PLTE/tRNS; CRCs repaired
  so the mutations get past the CRC check) and compares them the same way.
  Four runs of 3000 mutants found no file that both decoders decode
  differently. The last two found one rule each that the spec had missed (a
  lowercase third letter in a chunk type; IEND's CRC is not enforced), both
  fixed; after that, no file only verilith-png accepts, and the files only libpng
  accepts are the damaged-stream departure above.

CI (`.github/workflows/ci.yml` at the repository root) reruns the proofs, the tests, the
differential tests against libpng built from source, and 2000 fresh mutants, on every
pull request and push to `main` that touches this crate or a crate it depends on.

## Performance

Milliseconds per decode (best of 9 rounds, each decoder in its own
process pinned to one core, file already in memory) on a 4-core cloud VM.
Lower is better; bold marks the fastest. libpng 1.6.59 and libspng 0.7.4 are
built with `-O3 -march=native` against the system zlib; `png` is the Rust
`png` crate 0.18 and `zune-png` 0.5. Photos are 2400×1800 (4.3 MP);
`fractal` and `screen` are 1920×1080; files are compressed at zlib level 6
unless named `_z1`/`_z9`. `bench/run.sh DIR ROUNDS` reproduces it.

8-bit RGBA output:

| file | verilith-png | libpng | spng | png | zune-png |
| --- | ---: | ---: | ---: | ---: | ---: |
| photo_rgb8 | **56.4** | 91.7 | 92.7 | 57.1 | 73.0 |
| photo_rgb8_z1 | **59.4** | 99.6 | 101.5 | 71.5 | 74.3 |
| photo_rgb8_z9 | **55.6** | 90.6 | 95.5 | 57.8 | 74.5 |
| photo_rgba8 | 61.0 | 105.5 | 116.1 | **53.7** | 64.3 |
| photo_gray8 | **24.4** | 53.6 | 67.8 | 33.9 | 35.2 |
| photo_pal8 | **12.2** | 33.4 | 30.0 | 13.6 | 12.7 |
| photo_rgb16 | 76.5 | 183.0 | 212.4 | **72.6** | 104.4 |
| photo_rgb8_interlaced | **65.0** | 123.3 | 108.9 | 69.5 | 106.0 |
| fractal_rgb8 | 9.4 | 16.7 | 16.6 | 13.6 | **8.0** |
| screen_rgb8 | 9.0 | 8.5 | 9.2 | 10.8 | **7.2** |
| logo_rgba8 (500×500) | 2.2 | 4.3 | 4.3 | **2.2** | 2.3 |
| text_gray8 | **0.4** | 1.1 | 1.4 | 0.6 | 0.6 |

Native output:

| file | verilith-png | libpng | spng | png | zune-png |
| --- | ---: | ---: | ---: | ---: | ---: |
| photo_rgb8 | 49.2 | 87.8 | 87.7 | **46.0** | 69.0 |
| photo_rgb8_z1 | **54.5** | 97.3 | 95.2 | 58.5 | 71.2 |
| photo_rgb8_z9 | 48.1 | 86.8 | 86.1 | **44.7** | 69.3 |
| photo_rgba8 | 61.0 | 106.7 | 106.3 | **54.1** | 65.1 |
| photo_gray8 | 22.4 | 45.9 | 53.6 | **19.6** | 32.4 |
| photo_pal8 | **10.5** | 25.0 | 24.5 | 10.8 | 19.6 |
| photo_rgb16 | 73.5 | 172.6 | 191.5 | **64.1** | 94.9 |
| photo_rgb8_interlaced | 58.3 | 117.1 | 101.2 | **56.2** | 82.3 |
| fractal_rgb8 | **6.3** | 15.1 | 15.8 | 6.9 | 11.0 |
| screen_rgb8 | 5.9 | 7.0 | 7.1 | **5.6** | 5.9 |
| logo_rgba8 | 2.3 | 4.3 | 4.4 | **2.1** | 2.3 |
| text_gray8 | **0.4** | 1.0 | 1.1 | 0.4 | 0.5 |

On these images verilith-png is 1.6 to 2.8 times as fast as libpng and libspng on every
photograph, interlaced ones included, and level with them on the screenshot.
Against the Rust `png` crate it is faster on the RGB photos to RGBA at
every compression level (interlaced too), the palette and level-1 photos,
grey to RGBA and the fractal, and 2 to 15% behind on the rest. Interlaced images used to be the slowest
of the five decoders; 8- and 16-bit ones are now deinterlaced row by row
and converted by the non-interlaced paths.

On the repository's benchmark (`png-libpng`: the 24 Kodak photos decoded
to RGBA8, Apple M3 Pro, 2026-11-22) it is 1.41x libpng as a geometric mean;
see the [benchmark table](https://github.com/verilith/verilith#benchmarks).

Where the remaining time goes, on the RGB photo in native format: about
two thirds is decompression (verilith-zlib 31 ms against 26 ms for fdeflate, which
`png` uses, and 63 ms for zlib) and a third is unfiltering, which runs at
the same speed as `png`'s on the same rows. So the remaining gap to `png`
is verilith-zlib's inflate speed. Three things were tried and measured without a
gain, so they are not in the code: SIMD Paeth and Average filters (verilith-simd
intrinsics; slower, because each pixel depends on the one before it),
decoding two literals per table lookup in verilith-zlib (most output bytes on these
images come from matches), and unfiltering each row as verilith-zlib's streaming
decoder delivers it (level with the one-shot path).

## Building

64-bit targets only: the proofs fix `usize` at 64 bits, so a 32-bit build
(wasm32 included) stops with a `compile_error!`.

```sh
cargo build --release                       # the library
cargo build --release --example vpngcat     # vpngcat FILE [rgba8|native]
./scripts/verify.sh                         # needs cargo-verus and z3 on PATH
```

The proofs are checked with Verus at commit `1ce6a59b` (vstd
`0.0.0-2026-11-22-0344`) and Rust 1.100.0.

```rust,no_run
use verilith_png::{decode, PixelFormat};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bytes = std::fs::read("image.png")?;
    let (header, rgba) = decode(&bytes, PixelFormat::Rgba8, 1 << 30)?; // Invalid, TooLarge or OutOfMemory
    println!("{} x {}, {} bytes of RGBA", header.width, header.height, rgba.len());
    Ok(())
}
```

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/png/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/png/LICENSE-MIT), at your option.
