# What verilith-lz4 trusts

Verus checks every proof in verilith-lz4, but a proof means something only
relative to what it starts from. This is everything assumed rather than
proven.

## The specification

`src/spec.rs`. It is what "correct" means here, so it has to be read
against the format documents:

- `seqs`, `block`: the block format (lz4_Block_format.md): the token, the
  length extensions, the 2-byte offset, the minimum match of 4, and that
  a block ends with literals. `block_strict` adds the end-of-block rules
  (the last 5 bytes are literals, the last match starts at least 12
  bytes before the end), which the compressor is proven to follow.
- `xxh32`: XXH32 (xxhash_spec.md), with seed 0.
- `header`, `blocks`, `frame`, `skippable`, `frames`: the frame format
  (lz4_Frame_format.md), version 1.

Where the spec is stricter or looser than liblz4, it says so, and
[DEPARTURES.md](DEPARTURES.md) lists the cases. One guard in `frames`
exists only so that Verus accepts the recursion (`j <= i || j > s.len()`);
`frame` can never return such an index.

The tests compare the code, and so the spec, with liblz4 on tens of
thousands of valid and corrupted inputs.

## verilith-core's trusted primitives

verilith-lz4 has no `external_body` function and no `unsafe` of its own outside
`src/capi.rs`. It uses these from
[verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (`src/prims.rs`),
each one line whose `requires` is its bounds check, proven here at every
call:

- `load_u64_le`: an unaligned 8-byte load.
- `copy8`, `copy16`: copy 8 or 16 bytes forward inside one slice, from a
  source that ends before the destination starts.
- `move8`: load 8 bytes, then store them, inside one slice. The ranges
  may overlap. New with this crate.
- `copy16_in`: copy 16 bytes from one slice into another. New with this
  crate.
- `copy_in`: copy `n` bytes from one slice into another.

`copy16`, `move8` and `copy16_in` were added to verilith-core for verilith-lz4 and
verilith-snappy. Trusted is that each does what its `ensures` says within the
bounds its `requires` gives. `get` and `set` (unchecked indexing) are
verified in verilith-core against vstd's specs of `get_unchecked`.

## The C API adapter

`src/capi.rs` is not verified. It turns pointers and lengths into slices
(the caller's promise, as with liblz4), maps preferences and error codes,
and calls the proven functions for every byte it produces. Two parts do
more than that:

- `LZ4F_decompress` hands a frame that arrives whole, with room for its
  content, to the proven `frame::decode_frame_into`, which writes into
  the caller's buffer. Otherwise it collects the bytes of one frame
  before handing them to the proven `frame::decode_frame`. To know where the frame ends it
  reads the block sizes itself. If it got that wrong the proven decoder
  would reject the frame (or the adapter would, since it checks that the
  decoder used exactly the bytes collected); it cannot produce wrong
  content.
- `LZ4_decompress_safe_usingDict` copies the dictionary's last 64 KiB and
  the output into one buffer, decodes there with the proven decoder, and
  copies the result out.

`tests/capi.rs` runs all of it against liblz4.

## Tools

Verus, Z3 and the Rust compiler, and vstd's specifications of the
standard library (`Vec`, slices, `trailing_zeros`).
