# verilith-gif

A verified GIF decoder in Rust, proven with
[Verus](https://github.com/verus-lang/verus). It reads GIF87a and GIF89a
files into what giflib's `DGifSlurp` gives: the logical screen, the global
colour table, and every image with its descriptor, local colour table,
graphic control extension and colour indices (deinterlaced). It decodes
only. It does not composite the images of an animation into frames or
turn indices into RGBA, and it has no C API yet.

The sub-block chains, the record walk, LZW decompression, interlacing and
the graphic control extension are proven against a specification of the
format. `cargo verus verify` checks 37 functions with no errors.

giflib's security history is mostly memory-safety bugs in exactly these
places: the LZW table (CVE-2018-11490, a write past `Suffix` as the table
fills), image sizes (CVE-2019-15133, a division by a zero height;
CVE-2005-2974 and CVE-2005-3350, allocations from unchecked sizes), and the
2026 integer overflows in pixel counts. In verilith-gif that class of bug
is ruled out for every input by the proofs.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no integer overflow, no panics | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness: the screen and the images equal the specification's for every file the spec accepts; `Invalid` is returned exactly when the spec rejects the file | `decode::decode` against `spec::decode` |
| The only other results are `TooLarge` (the caller's memory limit) and `OutOfMemory` (a failed allocation) | `decode::decode` ensures |
| LZW decoding produces exactly the spec's pixels, and rejects exactly the streams the spec rejects | `lzw::lzw_exec` against `spec::lzw` |
| Each table entry is a run of the output already written, so a code is one LZ77 match copy, the code about to be added (KwKwK) included | `lzw::table_ok`, `lzw::code_next` |
| Sub-block chains are read exactly as the spec reads them | `blocks::skip_blocks`, `blocks::gather` against `spec::sub_blocks` |
| Interlaced rows are put back in order; the row map never leaves the image | `interlace::deinterlace_exec` against `spec::deinterlace`, `interlace::lemma_pass_rows` |
| The specification's record walk terminates on every input | `spec::walk_decreases` |

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification, GIF89a as total functions over
  `Seq<u8>`. Review it against the GIF specification; if the spec is
  wrong, the proofs still hold, about the wrong thing. Every place it
  follows giflib rather than a strict reading of the standard is marked
  `giflib:` in a comment.
- `src/prims.rs`: one `#[verifier::external_body]` primitive, a zeroed
  allocation.
- verilith-core's trusted base (its memory primitives, used here for
  unchecked loads and stores, the copies `copy_in` and `copy_match`'s
  chunks, and `alloc_u32`), and its bit-string definitions (`bits`), which
  the spec uses for LZW codes.
- Verus, Z3 and the Rust compiler.

Everything else in `src/` is verified. `examples/` (a command-line decoder
for the tests and a timer), `difftest/`, `fuzz/` and `bench/` are
unverified tools.

### Departures from giflib

verilith-gif is checked against giflib 5.2.2 as Debian and Ubuntu ship it
(with the 2026 security fixes), reading with `DGifSlurp`. Where both decode
a file the output is identical; the differential tests and the fuzzer check
this.

| area | giflib 5.2.2 | verilith-gif |
| --- | --- | --- |
| An LZW code past the end of the table (other than the one about to be added) | decoded from stale table entries into made-up pixels | `Invalid` |
| An extension with no data sub-blocks (`21 xx 00`) | reads one more sub-block past the terminator, so the rest of the file is misread | an extension with no data, as GIF89a defines it |
| LZW minimum code size outside 2 to 8 | rejected (sizes 0 and 1 only since the 2026 fixes) | rejected (same) |
| An end code, or the end of the data, before the last pixel | error | `Invalid` (same) |
| Codes after the last pixel, bytes after the trailer | not read | not read (same) |
| Several graphic control extensions before one image | the first is used (`DGifSavedExtensionToGCB`) | the first is used (same) |
| A graphic control block that is not 4 bytes long | not used, and hides later ones | same |
| The version in the header ("87a", "89a") | not checked | not checked (same) |
| Images outside the logical screen, indices past the colour table | returned as they are | returned as they are (same) |
| Width or height 0, more than 2^31 − 1 pixels | rejected | rejected (same) |
| Memory | allocates what the header asks for | bounded by the caller's `limit` (`TooLarge`) |
| Extension blocks other than graphic control | returned, raw | skipped |
| C API (`DGifOpen`, `DGifSlurp`) | yes | not provided yet |

## Design

`decode::decode` reads the screen, then walks the blocks to the trailer:

1. **Extensions** are skipped by following their sub-block chain
   (`blocks::skip_blocks`); a graphic control extension is parsed on the
   way and kept for the next image.
2. **Images**: the descriptor and local colour table are read, the image's
   sub-blocks are gathered into one buffer (`blocks::gather`), and the LZW
   decoder (`lzw::lzw_exec`) writes the pixels into a buffer with room for
   one more string than the image needs, so that no copy is ever cut short.
3. **LZW**: the table keeps, for each code, where its string is in the
   output and how long it is: an entry is the previous code's output and
   the byte after it, so it is always a run of output already written.
   Decoding a code is one LZ77 match copy, 16 bytes at a time
   (`verilith_core::lz::copy_match`); the code about to be added is the one
   copy that overlaps itself. The table lives in two 4096-entry arrays that
   every image reuses.
4. **Interlaced images** are put back in row order with one row copy per
   row.

## Tests

- `cargo test --release` runs `tests/cases.rs`: LZW round trips at every
  minimum code size, with and without clear codes when the table fills;
  the code about to be added; codes after the last pixel; early end codes;
  codes past the table; interlacing for every height up to 20; graphic
  control extensions; the block structure; the memory limit; and files
  shaped like the inputs of giflib's CVEs.
- `difftest/compare.sh FILES...` decodes each file with verilith-gif and
  with giflib (`difftest/refgif.c`, built by `difftest/build.sh`) and
  compares the screen, each image's descriptor and colour table, its
  graphic control and a hash of its pixels. On 508 files (giflib's test
  images, the GIFs shipped in an Ubuntu install, `difftest/gen.py`'s
  corpus of every palette size, interlaced and animated images, and GIFs
  from ImageMagick and ffmpeg): 508 identical, none different.
- `fuzz/run.sh OUT N SEED FILES...` writes `N` mutants of the seed files
  (`fuzz/mutate.py`: the image data cut into new sub-blocks, bit flips in
  the LZW codes, truncated codes, changed descriptor fields and code sizes,
  graphic control extensions of every length added, blocks dropped and
  duplicated, bytes after the trailer, and random byte edits) and compares
  them the same way. On 3000 mutants: 1670 decoded identically, 1274
  rejected by both, none decoded differently. 34 were accepted only by
  giflib, every one for a code past the table; 22 only by verilith-gif,
  every one for an extension with no sub-blocks. Those are the first two
  departures above. The first runs found one more: giflib rejects minimum
  code sizes 0 and 1 since its 2026 fixes, and now so does the spec.

## Performance

Milliseconds per decode (best of 30, one core, file already in memory) on
a cloud VM, against Ubuntu's giflib 5.2.2 package. Lower is better.
`bench/cbench.c` and `examples/vgifbench.rs` are the timers.

| file | verilith-gif | giflib |
| --- | ---: | ---: |
| plasma, 1200×900, 256 colours (ImageMagick) | **3.57** | 7.65 |
| noise, 1200×900, 256 colours (ImageMagick) | **4.49** | 6.19 |
| gradient, 4000×50, 2 colours | **0.02** | 1.01 |
| testsrc, 320×240, 20 frames (ffmpeg) | **0.98** | 7.02 |
| mandelbrot, 320×240, 25 frames (ffmpeg) | **5.40** | 12.93 |
| smooth, 640×480, 256 colours (Pillow) | **1.08** | 2.23 |
| noise, 640×480, 16 colours (Pillow) | **0.74** | 1.69 |

giflib decodes a code by walking its prefix chain onto a stack and popping
the stack into the output, one byte at a time; verilith-gif copies the
string from where it already is in the output.

## Building

```sh
cargo build --release                       # the library
cargo build --release --example vgifcat     # vgifcat FILE
./scripts/verify.sh                         # needs cargo-verus and z3 on PATH
```

```rust
use verilith_gif::decode::decode;
match decode(&bytes, 1 << 30) {
    Ok(gif) => { /* gif.width x gif.height screen; gif.frames[i].pixels */ }
    Err(e) => { /* Invalid, TooLarge or OutOfMemory */ }
}
```
