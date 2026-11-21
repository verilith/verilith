# What verilith-snappy trusts

Verus checks every proof in verilith-snappy, but a proof means something only
relative to what it starts from. This is everything assumed rather than
proven.

## The specification

`src/spec.rs`. It is what "correct" means here, so it has to be read
against the format documents:

- `varint`, `elems`, `decompress`: the raw format
  (format_description.txt): the length preamble (at most 2^32 - 1, so at
  most 5 bytes), literals with their 1 to 4 extra length bytes, and the
  three kinds of copy. An offset of 0, or one that reaches before the
  start of the output, is invalid, and the elements must produce exactly
  the length the preamble gives.
- `crc_step` to `crc32c`: CRC-32C bit by bit, with the Castagnoli
  polynomial (RFC 3720 appendix B.4), and `mask`, the framing format's
  rotation and constant.
- `chunks`, `stream`: the framing format (framing_format.txt). One
  choice the document does not make: a stream of no bytes at all holds
  nothing, which is what the Go and Rust implementations read and write.

What a match copy means (`lz_copy`) is verilith-core's definition.

The tests compare the code, and so the spec, with libsnappy on 100,000
valid and corrupted inputs, and the framing format with the `snap`
crate.

## The CPU's CRC-32C instruction

`crc::cpu::crc_update` (in `src/crc.rs`) is the one `external_body`
function here. On x86-64 with SSE4.2 it uses the `crc32` instruction, on
AArch64 with the CRC extension `crc32cb`/`crc32cd`, eight bytes at a
time; otherwise it calls the verified table code. Trusted is that the
instruction computes this CRC on the raw register (it is defined to) and
that the eight-line loops around it are right. `tests/framing.rs` checks
it against the verified `crc_update` on 3000 inputs of every length up to
300 with random starting registers.

## verilith-core's trusted primitives

From [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)
(`src/prims.rs`), each one line whose `requires` is its bounds check,
proven here at every call:

- `load_u64_le`: an unaligned 8-byte load.
- `copy8`, `copy16`: copy 8 or 16 bytes forward inside one slice, from a
  source that ends before the destination starts.
- `move8`: load 8 bytes, then store them, inside one slice. The ranges
  may overlap. New with this crate and verilith-lz4.
- `copy16_in`: copy 16 bytes from one slice into another. New likewise.
- `copy_in`: copy `n` bytes from one slice into another.
- `pick`: one of two numbers, chosen without a branch (a wrapper of
  `core::hint::select_unpredictable`). The decoder uses it for the next
  tag and its position.
- `copy16_pick`: `copy16_in` or `copy16`, with the source chosen without
  a branch. Six lines rather than one: it forms both source addresses,
  selects one, reads 16 bytes and writes 16. Only the chosen source has
  to be in range, which is what its `requires` asks. A source inside the
  output may overlap the destination, since the bytes are read before
  any is written.

Trusted is that each does what its `ensures` says within the bounds its
`requires` gives. `get` and `set` (unchecked indexing) are verified in
verilith-core against vstd's specs of `get_unchecked`.

## The C API adapter

`src/capi.rs` is not verified. It turns pointers and lengths into slices
(the caller's promise, as with libsnappy), calls the proven functions,
and maps their results to `snappy_status`. Every byte and every verdict
comes from a proven function. `tests/capi.rs` runs it against libsnappy.

## Tools

Verus, Z3 and the Rust compiler, and vstd's specifications of the
standard library (`Vec`, slices, `trailing_zeros`).
