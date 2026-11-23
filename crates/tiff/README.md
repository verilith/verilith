# verilith-tiff

A verified TIFF decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus). It reads the first image of
a classic TIFF file into its samples as stored: strips or tiles, samples
together or one plane per sample, 1 to 32 bits per sample, uncompressed,
PackBits, LZW or Deflate, with horizontal differencing undone. Multi-byte
samples come out little-endian whatever the file's byte order. It decodes
only, and it does not convert colours: a palette, CMYK or floating-point
image comes out as its samples, with the photometric interpretation and
sample format to say what they are. It has no C API yet.

The IFD reader, the image parameters, each of the four compression
schemes, the byte swap, the predictor, and where each strip or tile lands
in the output are proven against a specification of the format. `cargo
verus focus` checks 131 functions with no errors.

libtiff's long CVE list is mostly memory-safety bugs in exactly these
places: the arithmetic on strip and tile sizes and offsets, the predictor
on unusual tile and sample sizes, and the decoders of the compression
schemes. In verilith-tiff that class of bug is ruled out for every input
by the proofs.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no integer overflow, no panics | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness: the image's parameters and samples equal the specification's for every file the spec accepts; `Invalid` or `Unsupported` is returned exactly when the spec rejects the file | `decode::decode` against `spec::decode` |
| The only other results are `TooLarge` (the caller's memory limit) and `OutOfMemory` (a failed allocation); the output is allocated only once its size is known to be within the limit | `decode::decode` ensures |
| IFD entries and their values are read as the spec reads them, inline or at an offset, in either byte order | `ifd::field_exec`, `ifd::scalar_exec` against `spec::field`, `spec::scalar` |
| The parameters are the spec's, and the checks libtiff makes on the fields that do not change the samples are made the same way | `params::params_exec` against `spec::params`, `params::extras_exec` against `spec::extras` |
| PackBits, LZW (most significant bit first, early change, libtiff's 5119-entry table) and Deflate (through verilith-zlib) decode exactly the spec's bytes | `packbits::packbits_exec`, `lzw::lzw_exec`, `chunk::decompress_exec` |
| Byte swapping and horizontal differencing are undone as the spec says, in place | `chunk::swap_exec`, `predict::unpredict_exec` against `spec::to_le`, `spec::unpredict` |
| Every byte of the output is written by exactly the strip or tile that the spec says it comes from, at the offset it says | `place::lemma_strip_a`/`_b`, `place::lemma_tile_a`/`_b`, `decode::place_strip`, `decode::place_tile` |

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification, TIFF 6.0 as total functions over
  `Seq<u8>`. Review it against the TIFF specification; if the spec is
  wrong, the proofs still hold, about the wrong thing. Every place it
  follows libtiff rather than a strict reading of the standard is marked
  `libtiff:` in a comment.
- `src/prims.rs`: one `#[verifier::external_body]` primitive, a zeroed
  allocation.
- verilith-zlib's trusted base (its specification of zlib and DEFLATE and
  its own primitives), and verilith-core's (the memory primitives used
  here: unchecked loads and stores, `copy_in`, `copy_match`'s chunks,
  `alloc_u32`).
- Verus, Z3 and the Rust compiler.

Everything else in `src/` is verified. `examples/` (a command-line decoder
for the tests and a timer), `difftest/`, `fuzz/` and `bench/` are
unverified tools.

### Departures from libtiff

verilith-tiff is checked against libtiff 4.5.1 as Ubuntu 24.04 ships it
(with libdeflate), reading every strip with `TIFFReadEncodedStrip` or every
tile with `TIFFReadEncodedTile`. Where both decode a file the samples are
identical; the differential tests and the fuzzer check this.

libtiff guesses at what a damaged file meant in many places; the
specification does not. Files libtiff decodes and verilith-tiff rejects:

| area | libtiff 4.5.1 | verilith-tiff |
| --- | --- | --- |
| No StripByteCounts | estimated from the image size | `Invalid` |
| Offsets or byte counts with the wrong number of values | padded or cut | `Invalid` |
| An uncompressed single strip shorter than it should be | byte count recomputed from the file size | `Invalid` |
| Field types other than BYTE, SHORT and LONG for the fields used (signed, 64-bit, ...) | converted where the value fits | `Invalid` |
| A Deflate or LZW stream damaged after the last byte the strip needs | not read that far | `Invalid`: the Deflate stream must be whole (LZW, like libtiff, stops at the last byte) |
| BigTIFF | read | `Unsupported` |
| Compression other than none, PackBits, LZW and Deflate (CCITT, JPEG, ...) | read | `Invalid` |
| FillOrder 2, the floating-point predictor, YCbCr images, complex sample formats | read | `Invalid` |
| "Old-style" LZW (libtiff before 1993) | read | `Invalid` |
| Tiles whose rows do not end on a byte | read | `Invalid` (TIFF requires tile widths that are multiples of 16) |

Files verilith-tiff decodes, or decodes differently, where libtiff does
not:

| area | libtiff 4.5.1 | verilith-tiff |
| --- | --- | --- |
| Uncompressed strips whose byte counts differ from what libtiff expects | "Wrong StripByteCounts field, ignoring and calculating", then fails for lack of data | the byte counts in the file are used |
| A Deflate strip or tile that decompresses to more bytes than it needs | libdeflate stops for lack of room and libtiff accepts that, leaving the last bytes of the strip unwritten | the first bytes the strip needs, from a stream that must be whole |

The same in both: the predictor is ignored for uncompressed and PackBits
data; LZW stops at the last byte the strip needs, without an end code; of
two entries with the same tag the first is used, and entries need not be
sorted; SampleFormat, ExtraSamples, SMinSampleValue and SMaxSampleValue are
checked as libtiff checks them; a palette image of fewer than 8 bits needs
a ColorMap of 3 × 2^bits values, after BitsPerSample in the IFD.

## Design

`decode::decode` reads the header and IFD 0 (`params`), checks the image's
size against the caller's limit, allocates the output, and then decodes the
strips or tiles one at a time:

1. **Fields** (`ifd`): an entry is found by tag and its values read on
   demand, inline or at their offset; the strip and tile offsets and byte
   counts are never copied out of the file.
2. **Decompression** (`chunk`, `packbits`, `lzw`): each strip or tile is
   decompressed into a buffer of exactly the bytes it should hold. The LZW
   decoder is verilith-gif's design, with TIFF's bit order and code
   widths: each table entry is a run of output already written, and a code
   is one LZ77 match copy. Deflate is verilith-zlib's decompressor.
3. **Post-processing** (`chunk::swap_exec`, `predict`): in a big-endian
   file 16-, 24- and 32-bit samples are byte-swapped in place, then
   horizontal differencing is undone row by row in place.
4. **Placement** (`place`, `decode::place_strip`, `decode::place_tile`):
   a strip is one copy into the output; a tile is one copy per row, cut at
   the image's right and bottom edges.

## Tests

- `cargo test --release` runs `tests/cases.rs`: uncompressed strips (and
  ones too short or missing), a big-endian 16-bit image, PackBits, LZW and
  stored-block Deflate round trips, an LZW table grown past 4096 entries
  without a clear code, the predictor at 8 and 16 bits, tiles cut at both
  edges, a planar image, and the files the specification rejects.
- `difftest/compare.sh FILES...` decodes each file with verilith-tiff and
  with libtiff (`difftest/reftiff.c`, built by `difftest/build.sh`) and
  compares the byte order, size, samples, compression, planar
  configuration and a hash of the decoded samples. On 429 files
  (`difftest/gen.sh`'s ImageMagick corpus in every byte order, layout and
  compression, and Pillow's TIFFs of every mode): 407 identical, 2
  rejected by both, 20 decoded only by libtiff (all YCbCr), none
  different.
- `fuzz/run.sh OUT N SEED FILES...` writes `N` mutants of the seed files
  (`fuzz/mutate.py`: entry values, counts and types changed, entries
  dropped, duplicated and moved, strip data with bit flips, header bytes,
  and random byte edits) and compares them the same way. On 21,000 mutants
  in six runs: 5,384 decoded identically, 16,855 rejected by both, 1,261
  decoded only by libtiff, 41 that are the two departures in the second
  table, none different. The first runs found the rules libtiff applies to
  SampleFormat, ExtraSamples, SMin/SMaxSampleValue and ColorMap that the
  spec had missed, and they are in it now.

## Performance

Milliseconds per decode (best of 15, one core, file already in memory) on
a cloud VM, against Ubuntu's libtiff 4.5.1 package (with libdeflate). The
images are 2000 × 1500 RGB at 16 bits per sample (18 MB decoded), 80 rows
per strip or 256 × 256 tiles. Lower is better. `bench/tbench.c` and
`examples/vtiffbench.rs` are the timers.

| file | verilith-tiff | libtiff |
| --- | ---: | ---: |
| uncompressed | 2.19 | **0.73** |
| LZW, predictor | 98.0 | **64.8** |
| LZW 16-bit, predictor | 99.3 | **66.7** |
| Deflate, predictor | 57.1 | **46.4** |
| Deflate, tiles | 59.4 | **46.0** |
| PackBits | 4.94 | **3.17** |
| PackBits, tiles | 4.55 | **2.01** |

libtiff is faster on every file: 1.2 to 1.5 times on Deflate and LZW,
more on the cheap schemes. The comparison is not quite equal work:
`tbench.c` decodes every strip into one reused buffer, while verilith-tiff
allocates the 18 MB image and copies each strip into place, which is most
of the time for the uncompressed and PackBits files. On LZW the gap is the
decoder itself (libtiff's has had decades of tuning); on Deflate it is
verilith-zlib against libdeflate.

## Building

```sh
cargo build --release                        # the library
cargo build --release --example vtiffcat     # vtiffcat FILE [OUT]
./scripts/verify.sh                          # needs cargo-verus and z3 on PATH
```

```rust
use verilith_tiff::decode::decode;
match decode(&bytes, 1 << 30) {
    Ok(t) => { /* t.width x t.height, t.samples_per_pixel, t.pixels */ }
    Err(e) => { /* Invalid, Unsupported, TooLarge or OutOfMemory */ }
}
```
