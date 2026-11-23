# verilith-lz4

A verified LZ4 compressor and decompressor in Rust, proven with
[Verus](https://github.com/verus-lang/verus): the block format and the
frame format (with its xxHash32 checksums), behind liblz4's C API. It is
meant as a drop-in replacement for liblz4 where memory safety and
correct output have to be certain.

`cargo verus verify` (or `scripts/verify.sh`) checks 135 functions and
lemmas with no errors, no `assume` and no `external_body` in this crate.
Everything assumed is listed in [TRUST.md](https://github.com/verilith/verilith/blob/main/crates/lz4/TRUST.md).

## Using it from Rust

```rust
use verilith_lz4::{compress, decompress, Prefs};

fn main() -> Result<(), verilith_lz4::Error> {
    let data = b"hello hello hello hello hello hello".repeat(100);
    // A frame with independent 64 KiB blocks and a content checksum.
    let prefs = Prefs { block_id: 4, indep: true, bsum: false, csum: true, csize: true, accel: 1 };
    let frame = compress(&data, &prefs);
    assert_eq!(decompress(&frame, 1 << 30)?, data); // up to the limit
    Ok(())
}
```

`compress_block` and `decompress_block` work on single LZ4 blocks
(liblz4's `LZ4_compress_default` and `LZ4_decompress_safe`), with
`compress_bound` for the room a block needs.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read or write, no overflow, no panic | every function in `block`, `compress`, `frame`, `fcompress` (Verus checks all indexing and arithmetic, and the bounds each raw copy needs) |
| Termination of every loop | every function (`decreases`) |
| Block decoding: `Some(n)` exactly when the block is valid and fits, with the spec's output in `out[start..n]`; nothing before `start` is touched; `None` only when the spec rejects the block or its output does not fit | `block::decode_block` against `spec::block` |
| The decoder's wild copies: literals and matches are copied 16 or 24 bytes at a time past their end when there is room, and matches of any offset (overlapping ones too) give what a byte-by-byte copy gives | `verilith_core::lz::copy_match`, `copy_match24`, `copy_lits` against `verilith_core::lz::lz_copy` |
| Block compression round-trips: what `compress_block` writes decodes, by the spec, to the input, whatever the hash table held; and it follows the end-of-block rules liblz4's decoder insists on | `compress::compress_block` against `spec::block_strict` |
| XXH32 | `verilith_xxhash::xxh32_exec` against `spec::xxh32` (both from [verilith-xxhash](https://github.com/verilith/verilith/tree/main/crates/xxhash)) |
| Frame decoding into a buffer the caller already has (what `LZ4F_decompress` uses when a whole frame and enough room are given): `Some` only for a valid frame, with the spec's content, nothing allocated | `frame::decode_frame_into` against `spec::frame` |
| Frame decoding: `Ok` exactly when the input is one or more valid frames (and skippable frames), with the spec's content: header, header checksum, block sizes, stored and compressed blocks, linked blocks reaching into earlier ones, block checksums, content size, content checksum | `frame::decompress` against `spec::frames`, `frame::decode_frame` against `spec::frame` |
| Frame decoding with a dictionary (`LZ4F_decompress_usingDict`): the dictionary's last 64 KiB come before every block, linked or independent, as history its matches may reach into; the content, sizes and checksums are the spec's | `frame::decode_frame_dict` against `spec::frame_dict` |
| Frame compression round-trips, for every choice of block size, linked or independent blocks, and checksums | `fcompress::compress` against `spec::frame` |
| Linear work, block decoding: at most `block_work(n, m) = 151n + m + 400` steps for an `n`-byte block that writes `m` bytes (or, if it fails, has `m` bytes of room) | `block::decode_block_counted` ensures (`decode_block` is the same code without the count) |
| Linear work, frame decoding into a buffer: at most `frame_work(n, m) = 153n + 2m + 1000` steps, both checksums included | `frame::decode_frame_into_counted` ensures |
| A block can decode to at most 255 bytes for each of its bytes, so the frame decoder makes no more room than that for one | `block::lemma_seqs_max`, used by `frame::decode_one` |

The compressor uses a real match finder: liblz4's hash of four bytes (five
on inputs of 64 KiB and more), a 16 KiB table, its skip acceleration and
backward match extension. The table's contents are never trusted: a
candidate is used only after its four bytes are compared, which is what
the proof rests on. On the Silesia files it produces blocks of the same
size as liblz4 1.9.4 to within 0.05%.

Also proven: `compress_bound(n)` bytes are always enough. Given that
much room, `compress_block` and `compress_into` cannot fail, which is
what lets the compressor write sequences without testing for room. The
frame compressor (`fcompress::compress_into`) writes straight into the
caller's buffer and is proven to produce a frame that decodes to the input.

A step of the work bounds is a loop turn or a byte copied (wide copies
count what they write past the end, and a checksum one step a byte). The
counters are ghost state, erased at compile time.

Not yet proven: bounds on the compressors' work, and on the frame
decoder's that appends to a `Vec` (`frame::decompress`). Its room for a
block is limited the same way, so a run of tiny frames no longer zeroes
4 MiB each.

## Departures from liblz4

[DEPARTURES.md](https://github.com/verilith/verilith/blob/main/crates/lz4/DEPARTURES.md) lists every case. In short: an offset of 0
is rejected (liblz4 lets it through and copies whatever the buffer held);
the decoder does not enforce the end-of-block rules, which depend on the
size of the caller's buffer; `LZ4F_decompress` collects a whole frame
before decoding it unless it is given one in a single call; and the
high-compression levels, the legacy frame format and the streaming
compression API are not here.

## Layout

- `src/spec.rs`: the formats as total functions over `Seq<u8>`: sequences
  and blocks, frame headers, blocks, frames, skippable frames. XXH32 is
  verilith-xxhash's `spec::xxh32`.
- `src/block.rs`: the block decoder.
- `src/compress.rs`: the block compressor.
- `src/frame.rs`: the frame decoder.
- `src/fcompress.rs`: the frame compressor.
- `src/capi.rs`: the C API (an unverified adapter, see TRUST.md).

The copy loops are [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s
`lz` module, shared with verilith-snappy. verilith-core's `Tail` is not used: it owns a
`Vec`, and here both the C API and the frame decoder write into a buffer
that already exists, so `lz` has the same copies over `&mut [u8]`.

## C API

From `lz4.h`: `LZ4_versionNumber`, `LZ4_versionString`,
`LZ4_compressBound`, `LZ4_compress_default`, `LZ4_compress_fast`,
`LZ4_sizeofState`, `LZ4_compress_fast_extState`, `LZ4_decompress_safe`,
`LZ4_decompress_safe_usingDict`.

From `lz4frame.h`: `LZ4F_isError`, `LZ4F_getErrorName`,
`LZ4F_getErrorCode`, `LZ4F_getVersion`, `LZ4F_compressionLevel_max`,
`LZ4F_compressFrameBound`, `LZ4F_compressFrame`,
`LZ4F_createDecompressionContext`, `LZ4F_freeDecompressionContext`,
`LZ4F_resetDecompressionContext`, `LZ4F_headerSize`, `LZ4F_getFrameInfo`,
`LZ4F_decompress`, `LZ4F_decompress_usingDict`.

They are exported as `vlz4_*` and `vlz4f_*` (for example
`vlz4_compress_default`, `vlz4f_decompress`). With the `lz4-abi` feature
they take liblz4's own names, so the static library can be linked in
liblz4's place.

## Tests

`cargo test --release` loads the system liblz4 (`liblz4.so.1`, or
`VLZ4_LIBLZ4`) with `dlopen` and compares:

- `tests/liblz4.rs`: blocks both ways over seven kinds of data up to
  1.5 MB (liblz4 decodes what verilith-lz4 compresses and the reverse), and
  40,000 corrupted blocks: the same output whenever both accept, and
  every block that only liblz4 accepts has an offset of 0.
- `tests/frames.rs`: XXH32 test vectors; 2196 frames each way over every
  block size, block mode and checksum choice; several frames and
  skippable frames in one input; 30,000 corrupted frames, with the same
  rule.
- `tests/capi.rs`: the C API against liblz4's: block calls with too
  little, exact and spare room (and nothing written past the room
  given), `LZ4_compressBound`, dictionaries, frames streamed through
  `LZ4F_decompress` in random pieces of input and output (same content,
  same frame ends), `LZ4F_getFrameInfo`, and 20,000 corrupted frames.

## Performance

[vbench](https://github.com/verilith/verilith/tree/main/bench) has the
comparison (`lz4-*`): one C driver linked with liblz4 1.11.1 and with
verilith-lz4, both built with the same flags, over five Silesia files and 4 KiB
and 64 KiB pieces. On an Apple Silicon Mac (M3 Pro, the run in the
[repository's benchmark table](https://github.com/verilith/verilith#benchmarks), 2026-11-22),
geometric means of liblz4's time over verilith-lz4's: block decompression
1.10x, frame decompression 1.09x, block compression 0.97x (compressed
sizes within a few bytes) and frame compression 0.94x. The widest gap
left is frame compression of a 4 KiB input.

`cargo run --release --example bench -- FILES` is a quicker check
against the system liblz4.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/lz4/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/lz4/LICENSE-MIT), at your option.
