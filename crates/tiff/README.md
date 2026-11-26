# verilith-tiff

A verified TIFF decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus). It reads the first image of
a classic TIFF file into its samples as stored: strips or tiles, samples
together or one plane per sample, 1 to 32 bits per sample, uncompressed,
PackBits, LZW or Deflate, with horizontal differencing undone. Multi-byte
samples come out little-endian whatever the file's byte order. It decodes
only, and it does not convert colours: a palette, CMYK or floating-point
image comes out as its samples, with the photometric interpretation and
sample format to say what they are.

It reads TIFF as the TIFF 6.0 standard defines it. libtiff, the reference
implementation, reads many files the standard does not allow, by guessing
what they meant, and reads a few others differently from the standard;
verilith-tiff follows the standard. See
[Following TIFF 6.0](#following-tiff-60-not-libtiff).

It also has libtiff's reading API for C (`src/capi.rs` and
`capi/tiffshim.c`): built with the `tiff-abi` feature,
`libverilith_tiff.a` replaces libtiff at link time for programs that read
TIFF files through libtiff 4's `tiffio.h`, `TIFFReadRGBAImage` included.
See [C API](#c-api).

The IFD reader, the image parameters, each of the four compression
schemes, the byte swap, the predictor, and where each strip or tile lands
in the output are proven against a specification of the format, written
from the standard, and so is a bound on the decoder's work that is linear
in the file and the bytes it allocates. `cargo verus focus` checks 150
functions with no errors.

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
| Correctness: the image's parameters and samples equal the specification's for every file the spec accepts; `Unsupported` is returned exactly for the TIFF files that use a part of TIFF not read here, and `Invalid` for the other files the spec rejects | `decode::decode` against `spec::decode` and `spec::unsupported` |
| The only other results are `TooLarge` (the caller's memory limit) and `OutOfMemory` (a failed allocation); the output is allocated only once its size is known to be within the limit | `decode::decode` ensures |
| Linear work: at most `tiff_work(n, px) = 50,000n + 10,000px + 50,000` steps for an `n`-byte file that allocates `px` bytes for the image and its strips or tiles, with `px` at most twice the caller's `limit` | `decode::decode_counted` ensures (`decode` is the same code without the count) |
| Linear work per strip or tile: at most `9600c + 149s + 36,549` steps for one that reads `c` bytes and decodes to `s`, Deflate's bound from verilith-zlib included; the IFD reader at most 38 walks of the IFD or of a field's values | `decode::chunk_counted`, `chunk::decompress_exec`, `params::params_counted` ensures |
| IFD entries and their values are read as the spec reads them, inline or at an offset, in either byte order; the entries are in ascending order of tag; a field of a type other than BYTE, SHORT or LONG is skipped | `ifd::field_exec`, `ifd::scalar_exec`, `ifd::sorted_exec` against `spec::field`, `spec::scalar`, `spec::sorted` |
| The parameters are the spec's, and the standard's rules on the fields that must agree with the samples (PhotometricInterpretation, ExtraSamples, ColorMap, SampleFormat, SMin/SMaxSampleValue, tiles) are checked | `params::params_exec` against `spec::params`, `params::extras_exec` against `spec::extras` |
| PackBits (row by row), LZW (most significant bit first, early change, a 4096-entry table, to the end code) and Deflate (through verilith-zlib) decode exactly the spec's bytes | `packbits::packbits_exec`, `lzw::lzw_exec`, `chunk::decompress_exec` |
| Byte swapping and horizontal differencing are undone as the spec says, in place | `chunk::swap_exec`, `predict::unpredict_exec` against `spec::to_le`, `spec::unpredict` |
| Every byte of the output is written by exactly the strip or tile that the spec says it comes from, at the offset it says | `place::lemma_strip_a`/`_b`, `place::lemma_tile_a`/`_b`, `decode::place_strip`, `decode::place_tile` |

A step of the work bound is a loop turn, or a byte copied, compared or
zeroed; a copy of `n` bytes by a verilith-core primitive is charged `n`,
and a Deflate strip or tile is charged verilith-zlib's own count of its
steps plus 4096 for setting up its decoder. The counter is ghost state
(`work::Meter`), erased at compile time. The constants are mostly
verilith-zlib's Deflate bound, which is written for the worst case; real
files run far below it.

Strips and tiles can share bytes of the file, and a strip can be all
clear codes, or empty Deflate blocks, that decode to nothing. A file of
`n` bytes with `n / 4` strips pointing at the same data would make the
decoder read it `n / 4` times, so the work would grow with the square of
the file's size. To rule that out the decoder also returns `TooLarge`,
before decoding a strip or tile, when (1) the strips or tiles decoded so
far and this one would take more than `limit` bytes in all, or (2) they
would read more bytes than the file has and than they decode to, together.
No file whose strips and tiles do not overlap is affected by (2), and for
a striped image (1) is the check on the image's size the decoder already
made; a tiled image whose tiles, padding included, take more than `limit`
is newly `TooLarge`. Both are departures from libtiff, which has neither
limit. `TooLarge` is outside the correctness theorem, which says nothing
about a file it is returned for beyond that the spec does not call the file
`Unsupported`.

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification, TIFF 6.0 as total functions over
  `Seq<u8>`, quoting the standard (section numbers are TIFF 6.0's). Review
  it against the standard; if the spec is wrong, the proofs still hold,
  about the wrong thing. Where the standard leaves the reader a choice,
  the choice is marked `choice:` in a comment. `difftest/rules.py` is a
  second, independent reading of the standard, which the differential
  tests check the spec against.
- The work bound's unit: that a verilith-core copy, a zeroed allocation
  and `slice_to_vec` of `n` bytes cost on the order of `n` steps, that
  `Decompressor::new` costs at most 4096, and verilith-zlib's own count of
  its steps (its work bound, proven there). The counters count what the
  verified loops do; the primitives' cost is assumed.
- verilith-zlib's trusted base (its specification of zlib and DEFLATE and
  its own primitives), and verilith-core's (the memory primitives used
  here: unchecked loads and stores, `copy_in`, `copy_match`'s chunks,
  and the zeroed allocations `alloc_u8` and `alloc_u32`).
- Verus, Z3 and the Rust compiler.

- `src/capi.rs` and `capi/tiffshim.c`: libtiff's C API. Unverified glue:
  it calls the verified decoder for every strip and tile, and does around
  it what libtiff's API does (the fields `TIFFGetField` reports, the size
  functions, scanlines, and `tif_getimage.c`'s conversion to RGBA) in
  ordinary Rust. `tiffshim.c` holds the variadic functions
  (`TIFFGetField`, `TIFFSetField`, `TIFFError`, ...), which stable Rust
  cannot define. Its pointer arithmetic over the caller's buffers is as
  trusted as the caller's.

Everything else in `src/` is verified. `examples/` (a command-line decoder
for the tests and a timer), `difftest/`, `fuzz/` and `bench/` are
unverified tools.

### Following TIFF 6.0, not libtiff

verilith-tiff reads TIFF as the TIFF 6.0 standard (Adobe, 1992) defines
it, with Deflate (Compression 8) from Adobe's TIFF technical notes. It is
checked against libtiff 4.5.1 as Ubuntu 24.04 ships it (with libdeflate),
reading every strip with `TIFFReadEncodedStrip` or every tile with
`TIFFReadEncodedTile`: where both decode a file the samples are identical,
but for the departure at the end of this section. Where libtiff and
the standard disagree, verilith-tiff follows the standard.

Files the standard does not allow, which libtiff reads (guessing what they
meant) and verilith-tiff rejects as `Invalid`:

| the file | TIFF 6.0 | libtiff 4.5.1 |
| --- | --- | --- |
| IFD entries out of order, or a tag twice | "The entries in an IFD must be sorted in ascending order by Tag" (§2) | warns, and uses the first of two |
| The IFD at an odd offset, or inside the header | it "may be at any location in the file after the header but must begin on a word boundary" (§2) | reads it |
| No PhotometricInterpretation | "There is no default for PhotometricInterpretation, and it is required" (§8) | guesses from the samples |
| A value TIFF does not define: a PhotometricInterpretation, a Compression (libtiff's own 32946 for Deflate), an ExtraSamples value (Corel Draw's 999), a Predictor | the values each field lists (§8, §14, §16, §19, §23) | reads several |
| A palette image without a ColorMap of 3 × 2^BitsPerSample values | "ColorMap must be included in all palette-color images", N = 3 * (2**BitsPerSample) (§5, §8) | from 8 bits up, reads it as grey or RGB |
| A palette image with more than one sample; a transparency mask that is not one 1-bit sample | "SamplesPerPixel must be 1"; "SamplesPerPixel and BitsPerSample must be 1" (§8) | reads it |
| Fewer samples than the photometric interpretation's colours, or an ExtraSamples count that does not match | "If SamplesPerPixel is, say, 5 then ExtraSamples will contain 2 values" (§8; NumberOfInks for separated images, §16; 1 or 3 for CIELab, §23) | reads it, making up ExtraSamples |
| BitsPerSample or SampleFormat with one value for several samples | N = SamplesPerPixel, "the writer must write all three values" (§8, §19) | uses the one value for all |
| No StripByteCounts; offsets or byte counts with the wrong number of values | StripByteCounts: "No default"; N = StripsPerImage (§8) | estimates them, pads or cuts |
| Tiles not a multiple of 16 wide or long; strip fields in a tiled file | "TileWidth must be a multiple of 16", as must TileLength; "Do not use both strip-oriented and tile-oriented fields" (§15) | reads it |
| A PackBits run or literal that crosses a row | "Pack each row separately. Do not compress across row boundaries" (§9) | decodes across rows, or in `TIFFReadScanline` cuts the run short |
| An LZW strip without its end code, or with more or fewer bytes than the strip | "each strip begins with a ClearCode and ends with an EndOfInformation code" (§13) | stops at the last byte it needs |
| An LZW table grown past 4096 entries without a clear code | "our table can have at most 4096 entries. The table should not be any larger" (§13) | grows it to 5119 |
| A Deflate strip or tile with more or fewer bytes than it holds, or a stream damaged after them | "The data in the last strip is not padded" (§3); tiles are all the tile's size (§15) | stops once it has enough (and, through libdeflate, leaves the end of the strip unwritten when the stream is longer) |
| An uncompressed strip or tile whose byte count is not its size | the byte count is "the number of bytes in that strip after any compression" (§8) | reads a longer one (and in `TIFFReadRGBATile` rejects it); recomputes a shorter one from the file's size |
| "Old-style" LZW (libtiff before 1993) | not TIFF | reads it |

Files that are TIFF, but use a part of it that verilith-tiff does not read,
are `Unsupported` (the spec's `unsupported`): BigTIFF; CCITT (2, 3, 4) and
JPEG (6, 7) compression; YCbCr; FillOrder 2 ("Support for FillOrder=2 is
not required in a Baseline TIFF compliant reader"); the floating-point
predictor; horizontal differencing of samples other than 8, 16 or 32 bits;
BitsPerSample above 32 or differing between samples; SampleFormat differing
between samples. libtiff reads most of them.

Files that are TIFF, where libtiff does not do what the standard says and
verilith-tiff does:

| the file | TIFF 6.0 | libtiff 4.5.1 | verilith-tiff |
| --- | --- | --- | --- |
| A field of a type other than BYTE, SHORT or LONG where an integer is expected (Compression as SSHORT, ...) | "TIFF readers should accept BYTE, SHORT, or LONG values for any unsigned integer field"; "Readers should skip over fields containing an unexpected field type" (§2) | converts the value where it fits, and rejects the file where it does not | skips the field, so its default applies |

Where the standard leaves the reader a choice (`choice:` in `spec.rs`): the
output is little-endian whatever the file's byte order; values need not
start at an even offset ("The Value is expected to begin on a word
boundary" asks it of writers, and ASCII strings "will often begin on an odd
byte"); compressed data after a strip's last row, end code or the end of its
zlib stream is not read; the Predictor is
read only for LZW and Deflate ("Currently this field is used only with
LZW"); SMinSampleValue and SMaxSampleValue, which may be of "the field type
that best matches the sample data" (§19), must be of a numeric type (not
ASCII, UNDEFINED or a type TIFF 6.0 does not define) with their values
inside the file, so a file where they are not is `Invalid`, as libtiff
rejects it.

## C API

`src/capi.rs` has the reading half of libtiff 4.5's API, with its types,
return values and memory rules:

- opening and closing: `TIFFOpen`, `TIFFClientOpen`, `TIFFFdOpen` (Unix),
  `TIFFClose`, `TIFFCleanup`, `TIFFFileName`, `TIFFFileno`,
  `TIFFClientdata`, `TIFFGetMode`, `TIFFGetVersion`, `TIFFIsTiled`,
  `TIFFIsBigEndian`, `TIFFIsByteSwapped`, `TIFFIsMSB2LSB`,
  `TIFFIsUpSampled`, `TIFFIsBigTIFF`, `TIFFIsCODECConfigured`;
- fields: `TIFFGetField`, `TIFFGetFieldDefaulted` and their `V` forms, for
  the baseline and extension tags libtiff knows (the strip and tile
  offsets and byte counts as `uint64_t` arrays, as libtiff 4 gives them),
  the text tags, and the ICC profile, XMP, IPTC and Photoshop blobs;
- sizes: `TIFFScanlineSize`, `TIFFRasterScanlineSize`, `TIFFStripSize`,
  `TIFFVStripSize`, `TIFFRawStripSize`, `TIFFTileSize`, `TIFFVTileSize`,
  `TIFFTileRowSize` (each also as `...64`), `TIFFNumberOfStrips`,
  `TIFFNumberOfTiles`, `TIFFComputeStrip`, `TIFFComputeTile`,
  `TIFFCheckTile`;
- data: `TIFFReadEncodedStrip`, `TIFFReadEncodedTile`, `TIFFReadTile`,
  `TIFFReadScanline`, `TIFFReadRawStrip`, `TIFFReadRawTile`;
- RGBA: `TIFFRGBAImageOK`, `TIFFReadRGBAImage`,
  `TIFFReadRGBAImageOriented`, `TIFFReadRGBAStrip(Ext)` and
  `TIFFReadRGBATile(Ext)`, for greyscale, RGB, palette and CMYK images,
  with or without alpha, converted as `tif_getimage.c` converts them
  (TIFF does not define the conversion);
- directories (`TIFFCurrentDirectory`, `TIFFSetDirectory`,
  `TIFFReadDirectory`, `TIFFNumberOfDirectories`, ...), errors and
  warnings (`TIFFError`, `TIFFWarning`, their `Ext` forms and their
  handlers), `_TIFFmalloc` and the other memory functions, and the
  `TIFFSwab*` and `TIFFReverseBits` helpers.

They are exported as `vtiff_*`, and with the `tiff-abi` feature also
under libtiff's names:

```sh
cargo build --release -p verilith-tiff --features tiff-abi
cc prog.c target/release/libverilith_tiff.a -lpthread -lm -ldl   # instead of -ltiff
```

Every strip and tile is decoded by the verified decoder
(`decode::chunk_exec`). Around it the C API does what libtiff's API does
where libtiff follows the standard, so that a program sees what it would see
with libtiff on a file that is TIFF: `TIFFGetField` reports what libtiff
reports, and the RGBA functions do `tif_getimage.c`'s conversions, rounding
included. Where libtiff does not follow the standard, the C API does:

- Fields are reported as the file has them. A field of a type other than
  BYTE, SHORT or LONG where an integer is expected is skipped (libtiff
  converts it); an absent field has the standard's default (libtiff sets
  RowsPerStrip to ImageLength when it is absent or estimated, and makes up
  ExtraSamples for samples the file does not describe: "The default is no
  extra samples").
- The strips are the file's. libtiff's "strip chopping", which shows an
  uncompressed image in one strip as strips of about 8 KB and reports a
  RowsPerStrip the file does not have, is not done (libtiff does not do it
  in mode `c` either).
- An extra sample is alpha only if ExtraSamples says so (1, associated, or
  2, unassociated); libtiff also takes "0 = Unspecified data" as alpha.
  Alpha is the first extra sample marked as alpha; extra samples are "the
  last components" of a pixel.
- A ColorMap is 16-bit: "black is represented by 0,0,0 and white is
  represented by 65535, 65535, 65535". libtiff takes a ColorMap whose values
  are all below 256 as 8-bit, so a dark palette comes out bright.

And where the C API differs from libtiff otherwise:

- It reads. `TIFFOpen` in any mode but `r` fails, as does `TIFFSetField`
  on a tag (codec options are accepted and ignored). Only the first image
  is read: `TIFFReadDirectory` returns 0.
- The file is read in full when it is opened, and checked then: a file the
  decoder rejects fails at `TIFFOpen`, where libtiff fails at the first
  read, or reads it.
- `TIFFReadRGBAImage` and `TIFFReadRGBATile` on a tiled greyscale image
  that is 16-bit or has extra samples, and whose width is not a multiple
  of the tile width, give the image. libtiff's `put16bitbwtile`,
  `putgreytile` and `putagreytile` do not scale the skew from one tile row
  to the next by the size of a pixel, so libtiff reads the rows of the
  right-hand tiles from the wrong place.
- YCbCr, CIELab and LogLuv images are not converted to RGBA
  (`TIFFRGBAImageOK` says so), and the wording of error messages differs.
- The rest of libtiff's API (writing, `TIFFPrintDirectory`, the
  `TIFFField` functions, EXIF and custom directories) is not provided.
- It is not built for WebAssembly, which has no C library for
  `capi/tiffshim.c`; the decoder is.

`difftest/abi.sh` checks it with programs written for libtiff, compiled
against libtiff's `tiffio.h`: `difftest/reftiff.c` (`TIFFOpen`,
`TIFFGetField`, `TIFFReadEncodedStrip` and `TIFFReadEncodedTile`) linked
with verilith-tiff prints what `examples/vtiffcat.rs` prints, for every
file; and `difftest/api.c` (`TIFFGetField` and `TIFFGetFieldDefaulted` on
every baseline tag, the size functions, every scanline or tile, and every
RGBA function), linked once with verilith-tiff and once with libtiff (in
mode `rc`, without strip chopping), prints the same for every file both
decode to the same samples, but where one of the differences above
explains it (`difftest/apiclass.py` tells them apart, by libtiff's own
warnings or by the image's layout and fields). On the 429 corpus files: `reftiff.c` printed what the Rust API prints on
all of them; `api.c` printed the same as with libtiff on 394, and differed
on 13 only as above (8 edge tiles, 5 ColorMaps libtiff took as 8-bit). On
19,000 mutants: `reftiff.c` agreed on all; of the files both decode to the
same samples, `api.c` printed the same as with libtiff on 2,223 and differed
on 133 only as above (29 made-up ExtraSamples, 39 skipped fields, 43 edge
tiles, 23 ColorMaps), none otherwise. On the 38 edge-tile files of an
earlier run, the RGBA verilith-tiff gives matched libtiff's own, correct,
RGBA of the same image stored in strips.

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
  ones too short or missing), a big-endian 16-bit image, PackBits (and
  runs across rows), LZW (without an end code, with too much data, and a
  table grown past 4096 entries) and stored-block Deflate (of the wrong
  size), the predictor at 8 and 16 bits, tiles cut at both edges and tiles
  not a multiple of 16, a planar image, a field of an unexpected type, and
  each rule of the standard above that a file can break, `Invalid` or
  `Unsupported`.
- `difftest/compare.sh FILES...` decodes each file with verilith-tiff and
  with libtiff (`difftest/reftiff.c`, built by `difftest/build.sh`) and
  compares the byte order, size, samples, compression, planar
  configuration and a hash of the decoded samples. It also checks each
  file against `difftest/rules.py`, an independent reading of TIFF 6.0
  (written from the standard, with its own PackBits and LZW decoders): a
  file verilith-tiff rejects must break one of the standard's rules or use
  a part of TIFF not read here, and a file it decodes must break none. On
  429 files (`difftest/gen.sh`'s ImageMagick corpus in every byte order,
  layout and compression, and Pillow's TIFFs of every mode): 407
  identical, 2 rejected by both, 20 decoded only by libtiff (all YCbCr,
  `Unsupported`), none different.
- `fuzz/run.sh OUT N SEED FILES...` writes `N` mutants of the seed files
  (`fuzz/mutate.py`: entry values, counts and types changed, entries
  dropped, duplicated and moved, strip data with bit flips, header bytes,
  and random byte edits) and compares them the same way. On 19,000 mutants in five runs: 2,356 decoded
  identically, 13,378 rejected by both, 3,201 decoded only by libtiff, and
  65 that are the departure at the end of
  [Following TIFF 6.0](#following-tiff-60-not-libtiff) (a field of an
  unexpected type), none different. Every file only libtiff decodes breaks
  a rule of the standard by `rules.py`'s reading, or uses a part of TIFF
  not read here; most often unsorted IFD entries (1,196), a
  PhotometricInterpretation TIFF does not define (256) or none at all
  (169), an uncompressed byte count that is not the strip's size (242),
  PackBits across rows (156), LZW or Deflate data of the wrong size (244),
  and offsets or byte counts missing or of the wrong number (206). Every
  file verilith-tiff decodes breaks none.
- `difftest/abi.sh FILES...` checks the C API (see [C API](#c-api)).

## Performance

Milliseconds per decode (best of 15, one core, file already in memory) on
a cloud VM, against Ubuntu's libtiff 4.5.1 package (with libdeflate). The
images are one 2000 × 1500 RGB image (ImageMagick's `plasma:fractal`), 80
rows per strip or 256 × 256 tiles. Lower is better. `bench/tbench.c` and
`examples/vtiffbench.rs` are the timers.

| file | verilith-tiff | libtiff |
| --- | ---: | ---: |
| uncompressed, 16-bit | 3.02 | **1.00** |
| LZW, predictor, 8-bit | 59.9 | **37.3** |
| LZW, predictor, 16-bit | 137.1 | **89.7** |
| Deflate, predictor, 16-bit | 74.3 | **61.1** |
| Deflate, predictor, 16-bit, tiles | 76.3 | **61.3** |
| PackBits, 8-bit | 1.64 | **1.21** |
| PackBits, 8-bit, tiles | 1.92 | **1.06** |

libtiff is faster on every file: 1.2 times on Deflate, 1.5 to 1.6 on LZW,
more on the cheap schemes. The comparison is not quite equal work:
`tbench.c` decodes every strip into one reused buffer, while verilith-tiff
allocates the whole image and copies each strip into place, which is most
of the time for the uncompressed and PackBits files. On LZW the gap is the
decoder itself (libtiff's has had decades of tuning, and verilith-tiff's
checks each code against the end of the strip and the table's 4096
entries); on Deflate it is verilith-zlib against libdeflate.

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

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.
