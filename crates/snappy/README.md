# verilith-snappy

A verified Snappy compressor and decompressor in Rust, proven with
[Verus](https://github.com/verus-lang/verus): the raw format behind
google/snappy's C API (`snappy-c.h`), and the framing format with its
CRC-32C checksums. It is meant as a drop-in replacement for libsnappy
where memory safety and correct output have to be certain.

`cargo verus verify` (or `scripts/verify.sh`) checks 112 functions and
lemmas with no errors, no `assume` and no `external_body` in this crate.
CRC-32C is verilith-core's. Everything assumed is listed in
[TRUST.md](https://github.com/verilith/verilith/blob/main/crates/snappy/TRUST.md).

## Using it from Rust

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let data = b"hello hello hello hello hello hello".repeat(100);
    let c = verilith_snappy::compress(&data).ok_or("4 GiB or more")?;
    assert_eq!(verilith_snappy::uncompressed_length(&c), Some(data.len()));
    assert_eq!(verilith_snappy::decompress(&c, 1 << 30)?, data); // up to the limit

    // The framing format (`.sz` files and streams), with CRC-32C checksums.
    let f = verilith_snappy::frame_encode(&data);
    assert_eq!(verilith_snappy::frame_decode(&f, 1 << 30)?, data);
    Ok(())
}
```

`compress_into` and `decompress_into` write into a buffer of the caller's,
sized with `max_compressed_length` and `uncompressed_length`.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read or write, no overflow, no panic | every function in `decode`, `compress`, `frame` (Verus checks all indexing and arithmetic, and the bounds each raw copy needs) |
| Termination of every loop | every function (`decreases`) |
| Decompression: `Ok(n)` exactly when the input is valid, with the spec's output in `out[..n]`; `Err(Corrupt)` only when the spec rejects the input; `Err(TooSmall)` only when it does or the output does not fit | `decode::decompress_into` against `spec::decompress` |
| The wild copies: literals and matches are copied 16 bytes at a time past their end when there is room, and matches of any offset (overlapping ones too) give what a byte-by-byte copy gives | `verilith_core::lz::copy_match`, `copy_lits` against `verilith_core::lz::lz_copy` |
| Validation without decompressing gives the decompressor's verdict | `decode::validate` against `spec::decompress` |
| Compression round-trips: what `compress_into` writes decompresses, by the spec, to the input, whatever the hash table held | `compress::compress_into` against `spec::decompress` |
| `max_compressed_length(n)` bytes are always enough: given that much room, `compress_into` returns `Some` for every input under 4 GiB | `compress::compress_into` ensures, via `compress::slack` |
| Linear work, decompressing: at most `50n + m + 40` steps for `n` input bytes and `m` output bytes (or, if it fails, `m` bytes of room) | `decode::decompress_counted` ensures (`decompress_into` is the same code without the count) |
| CRC-32C, by table | `verilith_core::checksum::crc32c_update` against `checksum::spec::crc32c_reg`, in [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (every table entry is checked against the bit-by-bit definition) |
| Framing format decoding: `Ok` exactly when the stream is valid, with the spec's content: stream identifier, compressed and uncompressed chunks, masked checksums, the 64 KiB chunk limit, padding and skippable chunks, reserved chunks refused | `frame::frame_decode` against `spec::stream` |
| Framing format encoding round-trips | `frame::frame_encode` against `spec::stream` |

The compressor uses a real match finder, google/snappy's: 64 KiB
fragments, its hash of four bytes into a 16384-entry table, and its skip
acceleration. The table's contents are never trusted: a candidate is used
only after its four bytes are compared. On the Silesia files it produces
output of the same size as libsnappy 1.1.10 to within 0.6%.

The room proof counts in sixths of a byte (`compress::slack`): the room
left less 7/6 of a byte for each input byte still to compress. A copy of
4 or more bytes costs at most 3 and raises it by at least 10. A literal
lowers it by at most 5, and only a literal of 1 to 16 bytes does. Inside
a fragment, literals and copies alternate, and every fragment but the
last ends with at least 16 literals. So it never falls more than 5 below
where it started, which `32 + n + n/6` leaves room for.

A step of the work bound is a loop turn or a byte copied, counting what
the wide copies write past the end. The counter is ghost state, erased
at compile time.

Not yet proven: bounds on the compressor's work.

## Departures from google/snappy

On the raw format there are none that the tests can find: on 100,000
corrupted inputs verilith-snappy and libsnappy 1.1.10 give the same verdict, the
same status code and the same bytes. [DEPARTURES.md](https://github.com/verilith/verilith/blob/main/crates/snappy/DEPARTURES.md) has
the few things that are not provided.

## Layout

- `src/spec.rs`: the formats as total functions over `Seq<u8>`: the
  varint preamble, elements, chunks and streams. CRC-32C is
  verilith-core's `checksum::spec::crc32c`.
- `src/decode.rs`: the decompressor and the validator.
- `src/compress.rs`: the compressor.
- `src/frame.rs`: the framing format.
- `src/capi.rs`: the C API (an unverified adapter, see TRUST.md).

The copy loops are [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s
`lz` module, shared with verilith-lz4. verilith-core's `Tail` is not used: it owns a
`Vec`, and the C API writes into the caller's buffer, so `lz` has the
same copies over `&mut [u8]`.

## C API

All of `snappy-c.h`: `snappy_compress`, `snappy_uncompress`,
`snappy_max_compressed_length`, `snappy_uncompressed_length`,
`snappy_validate_compressed_buffer`, with snappy's status codes. They are
exported as `vsnappy_*` (for example `vsnappy_compress`). With the
`snappy-abi` feature they take snappy's own names, so the static library
can be linked in libsnappy's place by C callers. The C++ API
(`snappy::Compress` and the rest) is not provided.

The framing format is in the Rust API only (`frame::frame_encode`,
`frame::frame_decode`): google/snappy's library has no functions for it.

## Tests

`cargo test --release` loads the system libsnappy (`libsnappy.so.1`, or
`VSNAPPY_LIBSNAPPY`) with `dlopen` and compares:

- `tests/libsnappy.rs`: both ways over seven kinds of data up to 1.5 MB,
  60,000 corrupted inputs (the same verdict and the same bytes), and
  hand-built inputs with every kind of element.
- `tests/capi.rs`: the C API against libsnappy's: too little, exact and
  spare room (and nothing written past the result), the same status and
  lengths from every call on 40,000 corrupted inputs.
- `tests/framing.rs`: the framing format against the `snap` crate, an
  independent implementation: both ways, concatenated streams, skippable
  and reserved chunks, 30,000 corrupted streams (the same verdict).
  CRC-32C's own tests are verilith-core's `tests/crc32c.rs`.

## Performance

[vbench](https://github.com/verilith/verilith/tree/main/bench) has the
comparison (`snappy-*`): one C driver linked with libsnappy 1.3.1 and
with verilith-snappy, both built with the same flags, over five Silesia files
and 4 KiB and 64 KiB pieces. On an Apple Silicon Mac (M3 Pro, the run in
the [repository's benchmark table](https://github.com/verilith/verilith#benchmarks),
2026-11-22), geometric means of libsnappy's time over verilith-snappy's:
uncompress 0.93x, validate 0.97x, compress 0.91x (the compressed size
within 1.5%).

What the speed rests on:

- The decoder's inner loop takes literals and copies alike with no
  branch on the kind of element. An element's length and offset come
  from one lookup in a 256-entry table indexed by the tag, and every
  entry of that table is proved to agree with the format. The next tag
  comes from a conditional move between the two places it can be, and the element's 32 bytes are
  copied once, from the input or from earlier output, with the source
  chosen the same way. The two choices are verilith-core's `pick` and
  `copy16_pick`, which are trusted (see [TRUST.md](https://github.com/verilith/verilith/blob/main/crates/snappy/TRUST.md)); the loop
  around them is verified.
- `validate` walks the tags with the same loop, without the copies.
- The compressor clears a table sized to the input for each fragment, as
  google/snappy does, so every entry is a position before the one being
  looked at and only its four bytes need comparing; and it writes a copy
  element without a branch on which of the two forms it takes (`pick`
  again). After a match it tries the very next position before it goes
  back to searching, since one match often follows another, and it
  writes a literal of up to 16 bytes as one tag and one 16-byte copy.
  The four bytes after a match are taken from the words that measured
  it, so the next table lookup does not wait for another load.

`cargo run --release --example bench -- FILES` is a quicker check
against the system libsnappy.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/snappy/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/snappy/LICENSE-MIT), at your option.
