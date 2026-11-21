# verilith-snappy

A verified Snappy compressor and decompressor in Rust, proven with
[Verus](https://github.com/verus-lang/verus): the raw format behind
google/snappy's C API (`snappy-c.h`), and the framing format with its
CRC-32C checksums. It is meant as a drop-in replacement for libsnappy
where memory safety and correct output have to be certain.

`cargo verus verify` (or `scripts/verify.sh`) checks 87 functions and
lemmas with no errors and no `assume`. The one `external_body` function
in this crate is the CPU dispatch for CRC-32C. Everything assumed is
listed in [TRUST.md](TRUST.md).

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds read or write, no overflow, no panic | every function in `decode`, `compress`, `crc`, `frame` (Verus checks all indexing and arithmetic, and the bounds each raw copy needs) |
| Termination of every loop | every function (`decreases`) |
| Decompression: `Ok(n)` exactly when the input is valid, with the spec's output in `out[..n]`; `Err(Corrupt)` only when the spec rejects the input; `Err(TooSmall)` only when it does or the output does not fit | `decode::decompress_into` against `spec::decompress` |
| The wild copies: literals and matches are copied 16 bytes at a time past their end when there is room, and matches of any offset (overlapping ones too) give what a byte-by-byte copy gives | `verilith_core::lz::copy_match`, `copy_lits` against `verilith_core::lz::lz_copy` |
| Validation without decompressing gives the decompressor's verdict | `decode::validate` against `spec::decompress` |
| Compression round-trips: what `compress_into` writes decompresses, by the spec, to the input, whatever the hash table held | `compress::compress_into` against `spec::decompress` |
| CRC-32C, by table | `crc::crc_update` against `spec::crc_reg` (every table entry is checked against the bit-by-bit definition) |
| Framing format decoding: `Ok` exactly when the stream is valid, with the spec's content: stream identifier, compressed and uncompressed chunks, masked checksums, the 64 KiB chunk limit, padding and skippable chunks, reserved chunks refused | `frame::frame_decode` against `spec::stream` |
| Framing format encoding round-trips | `frame::frame_encode` against `spec::stream` |

The compressor uses a real match finder, google/snappy's: 64 KiB
fragments, its hash of four bytes into a 16384-entry table, and its skip
acceleration. The table's contents are never trusted: a candidate is used
only after its four bytes are compared. On the Silesia files it produces
output of the same size as libsnappy 1.1.10 to within 0.6%.

Not yet proven: that `max_compressed_length(n)` bytes are always enough
(the tests have never seen it fail, and `compress_into` reports a buffer
that is too small rather than overrunning it); and bounds on work.

## Departures from google/snappy

On the raw format there are none that the tests can find: on 100,000
corrupted inputs verilith-snappy and libsnappy 1.1.10 give the same verdict, the
same status code and the same bytes. [DEPARTURES.md](DEPARTURES.md) has
the few things that are not provided.

## Layout

- `src/spec.rs`: the formats as total functions over `Seq<u8>`: the
  varint preamble, elements, CRC-32C, chunks and streams.
- `src/decode.rs`: the decompressor and the validator.
- `src/compress.rs`: the compressor.
- `src/crc.rs`: CRC-32C.
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
  and reserved chunks, 30,000 corrupted streams (the same verdict); and
  the CPU's CRC-32C instruction against the verified table code.

## Performance

[vbench](https://github.com/verilith/verilith/tree/main/bench) has the
comparison (`snappy-*`): one C driver linked with libsnappy 1.2.2 and
with verilith-snappy, both built with the same flags, over five Silesia files
and 4 KiB and 64 KiB pieces. On an Apple Silicon Mac (M3 Pro), geometric
means of verilith-snappy's speed against libsnappy's (with the range over the
cases): uncompress 0.93 (0.85 to 0.96), validate 0.97 (0.94 to 0.98),
compress 0.92 (0.86 to 1.18, the compressed size within 1.5%).

What the speed rests on:

- The decoder's inner loop takes literals and copies alike with no
  branch on the kind of element. An element's length and offset come
  from one lookup in a 256-entry table indexed by the tag, and every
  entry of that table is proved to agree with the format. The next tag
  comes from a conditional move between the two places it can be, and the element's 32 bytes are
  copied once, from the input or from earlier output, with the source
  chosen the same way. The two choices are verilith-core's `pick` and
  `copy16_pick`, which are trusted (see [TRUST.md](TRUST.md)); the loop
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
