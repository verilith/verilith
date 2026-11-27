# verilith-zstd

A verified Zstandard (RFC 8878) decompressor and compressor in Rust,
proven with [Verus](https://github.com/verus-lang/verus), with libzstd's C
API. It is meant to replace libzstd in hardened builds (Node.js first):
the decoder on its own alongside libzstd's compressor, or both.

`cargo verus verify` (or `scripts/verify.sh`) checks 338 functions and
lemmas with no errors and no `assume`; the only `external_body` functions
in this crate are the three wild-copy primitives in
`src/prims.rs` and the three CPU-feature wrappers in `src/cpu.rs`.

The proofs are checked once per pointer width: CI also runs Verus
compiling for `wasm32-unknown-unknown`, where `usize` is 32 bits
(`scripts/verify-narrow.sh`), so the crate builds for wasm32 (browsers,
Cloudflare Workers) and is proven as built there. Its tests also pass on
`wasm32-wasip1` under wasmtime (`scripts/wasm32.sh` at the root).
On a 32-bit target the limits are smaller: see the last rows of
[DEPARTURES.md](https://github.com/verilith/verilith/blob/main/crates/zstd/DEPARTURES.md).

## Using it from Rust

```rust
fn main() -> Result<(), verilith_zstd::Error> {
    // A Zstandard frame holding "hello" in one raw block.
    let frame = [0x28, 0xb5, 0x2f, 0xfd, 0x20, 0x05, 0x29, 0x00, 0x00, b'h', b'e', b'l', b'l', b'o'];
    let out = verilith_zstd::decompress(&frame, 1 << 30)?; // every frame, up to the limit
    assert_eq!(out, b"hello");
    Ok(())
}
```

Compressing, at a libzstd level (1 to 22):

```rust
let text = b"the more it repeats, the more it repeats, the smaller it gets".repeat(100);
let frame = verilith_zstd::compress(&text, 3, true); // level 3, with a checksum
assert!(frame.len() < text.len() / 10);
assert_eq!(verilith_zstd::decompress(&frame, 1 << 30).unwrap(), text);
```

`DictDecoder` decompresses with a dictionary, `Stream` decompresses in
pieces, and with the feature `zstd-abi` the static library exports
libzstd's decompression API (`zstd-abi-compress`: the compression API).

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no overflow, no panics | every function in `bits`, `fse`, `huf`, `seq`, `frame` (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness, one-shot: `Ok(v)` exactly when the input is valid, with the spec's output; `Err(Corrupt)` only when the spec rejects the input; `Err(TooLarge)` only when the spec rejects it or its output is longer than the limit | `frame::decompress_exec` against `spec::decompress` |
| Correctness, one block: a raw, RLE or compressed block decodes to the spec's output and decoder state (repeat offsets, Huffman table, FSE tables) | `frame::block_exec`, `seq::compressed_block_exec` against `spec::blocks`, `spec::compressed_block` |
| Literals sections, Huffman tree descriptions (direct and FSE-compressed weights), 1- and 4-stream Huffman decoding | `huf::lit_section_exec` against `spec::lit_section` |
| FSE table descriptions and tables (spread, low-probability symbols, state rows), predefined and repeat modes | `fse::read_ncount`, `fse::build_table`, `seq::seq_table_exec` |
| Sequences: decoding, repeat offsets, execution with overlapping matches | `seq::seq_run_exec` against `spec::seq_run` |
| XXH64 (the content checksum), one-shot and fed in pieces | `verilith_xxhash::Xxh64::update`/`digest` against `spec::xxh64` (both from [verilith-xxhash](https://github.com/verilith/verilith/tree/main/crates/xxhash)) |
| Streaming, input and output in pieces of any size, with or without a dictionary: a frame end (0) is returned only when the input taken is a whole frame and the output handed out is its content, whatever input follows; before that, all output handed out is the start of the frame's content; the loop terminates | `stream::Stream::stream` against `spec::frame_d` with the stream's dictionary (`frame_ok`), `Stream::lemma_emitted_prefix` |
| Streaming accepts every frame the spec accepts: it fails only when the spec rejects every frame (Zstandard or skippable) that starts with the frame's input so far. The two exceptions are limits: a window larger than the caller allows (or than 1 TiB), and output near 256 TiB | `stream::Stream::stream` ensures (`fail_ok`, `rejected`) |
| Streaming keeps only the last window of output (with a dictionary, the last window plus the dictionary's size of dictionary and output), and that gives the same output (a match reaches back no further) | `stream::lemma_compressed_block_shift`, `lemma_block_step_shift` |
| Streaming memory: the output kept is at most two windows (each with the dictionary's size added) and three blocks, and a unit being collected at most one block | `stream::Stream::inv` (`mem_ok`, `need`) |
| Dictionaries, loaded: a formatted dictionary (magic number, ID, Huffman table, offset, match length and literals length FSE tables, three repeat offsets, content) is accepted exactly when the spec accepts it, with the spec's tables and offsets; anything shorter than 8 bytes or without the magic number is raw content | `dict::load_dict` against `spec::dict_load`, `dict::raw_dict_exec` against `spec::raw_dict` |
| Decompression with a dictionary, one-shot: `Ok(v)` exactly when every frame is valid with the dictionary's content as the history before it and its tables and repeat offsets as the starting state, and no frame names another dictionary; the same `Err` cases as without one. The decoder keeps the dictionary's content between calls (a type invariant), so a call copies only the frames' content | `dict::DictDecoder::decompress` against `spec::decompress_d` |

| Linear work, one-shot: at most `6537·n + 10·v + 1` steps for `n` bytes of input and `v` of output; a failure takes at most `6537·n + 10·limit + 1179648` | `frame::decompress_metered` (`BYTE_WORK`, `BLOCK_FAIL_WORK`) |
| Linear work with a dictionary: loading takes at most `19546 + 26·d` steps for `d` bytes; decompressing at most `6537·n + 12·v + 1`, and a failure at most `6537·n + 12·limit + 1179648 + c` for `c` bytes of content | `dict::DictDecoder::load_metered`, `DictDecoder::decompress_metered` |

The output limit is checked as the output grows, so a decompression bomb
stops at the limit, not after.

### The compressor

| property | where it is stated |
| --- | --- |
| Round trip: the specification decodes every frame the compressor makes back to its input, at every level and window size, with or without a checksum | `compress::compress_exec` (`decompress(r@) == Some(src@)`, against `spec::decompress`) |
| Memory safety: no out-of-bounds access, no overflow, no panics, in the match finders, the entropy coders (FSE tables and states, Huffman code lengths and codes, bit writer) and the frame writer | every function in `compress`, `enc`, `ent` |
| Termination of every loop | every function (`decreases`) |

The frame header, block headers, raw and RLE blocks and the checksum are
proven correct as they are written. A compressed block is checked
instead: the match finder and entropy coders are proven safe but not
correct, and each compressed block they make is decoded by the proven
`frame::block_exec`, from the decoder state the frame has reached, and
compared with the input. A block that does not decode to its input is
stored raw, and the rest of the frame is written raw too. So a bug in the
encoder can make the output larger, never wrong. libzstd's decoder is
then only a second check: the tests decode every frame with it as well.

Work is not bounded by a proof for the compressor yet: the match finders
look at a fixed number of candidates per position (the level's search
depth), but the work per candidate is not metered.

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification. Review it against RFC 8878. Where it
  departs from the RFC or from libzstd, it says so, and
  [DEPARTURES.md](https://github.com/verilith/verilith/blob/main/crates/zstd/DEPARTURES.md) lists every case.
- [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s trusted
  primitives: `tail::Tail`, the vector
  the sequence loop appends to. `Tail::take` reserves room for the whole
  block once; each append (`append_from`, `append_within` and their
  32-byte forms) copies 16 bytes at a time through a raw pointer, and
  its `requires`, proven here at each call, says the bytes and 32 more
  fit in what was reserved. Trusted is that each append stays within
  those bounds.
- `src/prims.rs`: `extend_from` (append a range of a slice, copying 16
  bytes at a time where there is room) and `put_pairs4` (store four
  symbol pairs at a position with eight raw stores, leaving the rest of
  the vector as it was); each `requires` is the bounds check, proven at
  the call site. `grow`, `put`, `put4` and `drop_front` are verified
  against vstd's specs of `resize`, `copy_from_slice`, `copy_within`,
  `get_unchecked_mut` and `truncate`, and `row` and `at` against its spec
  of `get_unchecked`. Copying a range into the caller's output buffer is
  verilith-core's `prims::copy_in`, and `load_u64_le` is verilith-core's
  too; both are verified there.
- `src/cpu.rs`: `run_seqs`, `run_huf4` and `run_huf1` call the verified
  `seq_run_exec`, `huf_4streams_exec` and `huf_stream_exec`, through a copy
  compiled with BMI2 when the CPU has it (Verus rejects `#[target_feature]`
  on verified code, so the dispatch sits outside it). Each wrapper's
  contract is a copy of its target's; trusted is that the copy is exact
  and that the compiler's BMI2 code generation is correct. No decoding
  logic lives there.
- `src/capi.rs`: an unverified adapter for the C API. One-shot calls run
  `decompress_exec` and copy the result out; streaming calls run the
  proven `stream::Stream::stream` on the caller's buffers. With a
  dictionary, one-shot calls run `dict::DictDecoder::decompress`, and
  streaming gives the dictionary to the proven stream at a frame's start
  (`stream::Stream::set_dict`). Which
  dictionary applies to which frame (a loaded one for every frame, a
  prefix for the next call or frame only) is the adapter's. It also maps
  rejections to libzstd's error codes and handles the parameters. It is
  tested against libzstd's own decoders.
- `src/ccapi.rs`: an unverified adapter for the compression C API. Every
  frame comes from the proven `compress_exec`; the adapter maps
  parameters, copies frames into the caller's buffer, and in streaming
  collects input and makes a frame on each flush, at the end, and every
  eight windows of input.
- Verus, Z3 and the Rust compiler.

Each of the stream's failures is proven to be the spec's, from the bytes
already taken, whatever follows them. That covers a magic number that
is neither kind of frame, a skippable frame too large, a header the spec
rejects, the wrong dictionary, a block header or block the spec rejects,
a content size that does not match, and a checksum that does not match.

### Work

The one-shot decoder is proven to run in time linear in its input and
output. The `_metered` functions carry a ghost step counter
(`work::Meter`), erased at compile time. It ticks once per turn of every
loop, however small its bound, and once per byte that a library or
trusted copy moves (`extend_from_slice`, `resize`, a `Tail` append, the
copies in `prims`) or that the checksum hashes. The bound is assembled
from the inside out:

- FSE: reading a table description takes at most `3·maxsv + 8·len + 6`
  steps, and building the table `3·symbols + 3·2^log`. The spread's walk
  is proven to visit each row at most once: the step is odd, so `size`
  steps reach `size` distinct rows (`fse::lemma_walk_inj`), and the
  probabilities read always sum to `2^log` (`fse::lemma_nc_run_psum`).
- Huffman: a tree description takes at most `HUF_DESC_WORK` (12400)
  steps, and decoding a literals section at most that plus 6 a literal.
- Sequences: each sequence writes at least 3 bytes (`seq::lemma_ml_base_min`),
  so its fixed cost is paid by the output; a compressed block takes at
  most `CBLOCK_WORK + 24·size + 9·growth` (`CBLOCK_WORK` is 19603).
- Blocks and frames: the three bytes of a block's header pay for its
  fixed cost (`frame::BLOCK_BYTE_WORK`, 6535 a byte), one more step a byte
  of output hashes it, and the four bytes of a frame's magic number pay
  for copying a dictionary's tables.

A step is a loop turn or a byte moved, not an instruction. The bound
also takes allocation and `Vec::push` to be amortized O(1), and the
XXH64 update (verified in verilith-xxhash, not metered) to be linear in
the bytes it is given. The streaming decoder (`Stream`) is not metered:
its work per call is not bounded yet.

## Departures from libzstd

verilith-zstd accepts only what the spec accepts, and the spec is stricter than
libzstd in a few corners. Every valid stream that libzstd's encoder produces
decodes the same. [DEPARTURES.md](https://github.com/verilith/verilith/blob/main/crates/zstd/DEPARTURES.md) lists the cases. In short:
matches may not reach beyond the window, block sizes are limited to the
window in one-shot decoding too, Huffman and sequence bitstreams must be
consumed exactly, reserved bits must be zero, and legacy (pre-v0.8)
frames are not supported. With a dictionary, matches reach the window
plus the dictionary's content throughout the frame (libzstd's one-shot
rule; the RFC drops the dictionary once the output passes the window),
so streaming keeps the window plus the dictionary's size.

## Layout

- `src/spec.rs`: the format as total functions over `Seq<u8>`: FSE and
  Huffman descriptions and tables, literals, sequences, blocks, frames,
  skippable frames. XXH64 is verilith-xxhash's `spec::xxh64`.
- `src/bits.rs`: the backward bit reader (8-byte loads, zero-filled below
  the start of the stream) and the bit arithmetic.
- `src/fse.rs`: FSE table descriptions and table construction.
- `src/huf.rs`: Huffman tree descriptions, the decoding table, Huffman
  streams and the literals section.
- `src/seq.rs`: the sequences section and compressed blocks.
- `src/frame.rs`: frame headers, blocks, frames and `decompress_exec`.
- `src/stream.rs`: streaming decompression, input and output in pieces.
- `src/dict.rs`: dictionaries, loaded, and decompression with one.
- `src/capi.rs`: the C API (unverified adapter, above).
- `src/compress.rs`: the frame writer, `compress_exec` and its round-trip
  proof.
- `src/enc.rs`: the match finders (fast, double fast, greedy, lazy and
  lazy2 on hash chains) and libzstd's level parameters.
- `src/ent.rs`: the entropy coders: FSE normalization (libzstd's two
  methods), table descriptions and encoding tables, Huffman code lengths
  and tree descriptions (direct or FSE-compressed weights), the literals
  and sequences sections.
- `src/ccapi.rs`: the compression C API (unverified adapter, above).

## C API

`ZSTD_decompress`, `ZSTD_decompressDCtx`, `ZSTD_getFrameContentSize`,
`ZSTD_getDecompressedSize`, `ZSTD_findFrameCompressedSize`,
`ZSTD_decompressBound`, `ZSTD_getDictID_fromFrame`, `ZSTD_isFrame`,
`ZSTD_createDCtx`, `ZSTD_freeDCtx`, `ZSTD_createDStream`,
`ZSTD_freeDStream`, `ZSTD_initDStream`, `ZSTD_DCtx_reset`,
`ZSTD_DCtx_setParameter` / `ZSTD_DCtx_getParameter` (`ZSTD_d_windowLogMax`,
`ZSTD_d_format` = `ZSTD_f_zstd1` only), `ZSTD_dParam_getBounds`,
`ZSTD_DCtx_setMaxWindowSize`, `ZSTD_decompressStream`,
`ZSTD_decompressStream_simpleArgs`, `ZSTD_DStreamInSize`,
`ZSTD_DStreamOutSize`, `ZSTD_sizeof_DCtx`; with a dictionary,
`ZSTD_decompress_usingDict`, `ZSTD_DCtx_loadDictionary`,
`ZSTD_DCtx_loadDictionary_byReference`, `ZSTD_DCtx_refPrefix`,
`ZSTD_createDDict`, `ZSTD_createDDict_byReference`, `ZSTD_freeDDict`,
`ZSTD_sizeof_DDict`, `ZSTD_decompress_usingDDict`, `ZSTD_DCtx_refDDict`,
`ZSTD_getDictID_fromDict`, `ZSTD_getDictID_fromDDict`,
`ZSTD_initDStream_usingDict`, `ZSTD_initDStream_usingDDict`; for
compression, `ZSTD_compress`, `ZSTD_compressBound`, `ZSTD_compressCCtx`,
`ZSTD_compress2`, `ZSTD_createCCtx`, `ZSTD_freeCCtx`, `ZSTD_sizeof_CCtx`,
`ZSTD_CCtx_setParameter` / `ZSTD_CCtx_getParameter`, `ZSTD_cParam_getBounds`,
`ZSTD_CCtx_setPledgedSrcSize`, `ZSTD_CCtx_reset`, `ZSTD_createCStream`,
`ZSTD_freeCStream`, `ZSTD_initCStream`, `ZSTD_compressStream`,
`ZSTD_compressStream2`, `ZSTD_compressStream2_simpleArgs`,
`ZSTD_flushStream`, `ZSTD_endStream`, `ZSTD_CStreamInSize`,
`ZSTD_CStreamOutSize`, `ZSTD_maxCLevel`, `ZSTD_minCLevel`,
`ZSTD_defaultCLevel`; and from libzstd's `common/`:
`ZSTD_isError`, `ZSTD_getErrorCode`, `ZSTD_getErrorName`,
`ZSTD_getErrorString`, `ZSTD_versionNumber`, `ZSTD_versionString`.

They are exported as `vzstd_*`. With the `zstd-abi` feature the
decompression functions take libzstd's names, so a libzstd built without
its decompressor (`ZSTD_LIB_DECOMPRESSION=0`) can be linked alongside for
compression. `zstd-abi-compress` gives the compression functions
libzstd's names, and `zstd-abi-common` the `common/` functions; with all
three, no libzstd is needed at all.

The compressor takes the level, the window log and the checksum flag.
Levels below 1 compress as level 1, and 0 is the default (3). The
content size is always written, and the other parameters (match finder
details, long-distance matching, workers) are accepted and left to the
level. A stream is written as a series of whole frames, one per flush,
one at the end, and one every eight windows of input (at least 1 MiB);
zstd decoders decode the series to the whole input. Dictionaries are not
supported for compression yet. Error codes follow
`zstd_errors.h`; on corrupt input the code can differ from libzstd's, since
libzstd's depends on how far its decoder got (`DEPARTURES.md`).

## Tests

`cargo test --release` loads the system libzstd (`libzstd.so.1`) with
`dlopen` and compares:

- `tests/libzstd.rs`: round trips through libzstd's compressor at levels
  -5 to 19, every strategy, window logs 10 to 17, with and without
  checksums and content sizes, up to 1.5 MB; concatenated and skippable
  frames; the output limit; and 3000 corrupted frames, where verilith-zstd must
  never accept what libzstd rejects and must give the same output whenever
  both accept (12 of the 3000 are accepted by libzstd only, each one of the
  departures).
- `tests/capi.rs`: the C API against libzstd's: streaming in random input
  and output pieces (same output, same frame ends, same verdict), one-shot
  results with small and large destinations, content sizes and frame
  sizes.
- `tests/dict.rs`: dictionaries trained by libzstd (`ZDICT_trainFromBuffer`,
  1 KiB to 110 KiB) and raw-content prefixes (1 byte to 300 KiB), with
  frames libzstd compressed at levels -3 to 19: the proven decoder and
  every C entry point that takes a dictionary (one-shot, DDict, loaded,
  prefix, streaming in random pieces) give libzstd's output; a frame
  naming another dictionary fails with `dictionary_wrong`; 3000 damaged
  dictionaries are loaded exactly when libzstd loads them; 300 streams
  (pairs of frames, 30 of them 3 MB, window logs 10 to 17, a third of them
  corrupted) through the proven stream give libzstd's streaming output
  and frame ends, and none is accepted that libzstd rejects; and of 4000
  corrupted frames, none is accepted that libzstd rejects (90 are
  accepted by libzstd only: 85 are departures, 81 of them Huffman literal
  streams not consumed exactly, and 5 are empty input, below).
- `tests/compress.rs`: the compressor at levels -5 to 22, window logs 10
  to 31, with and without checksums, on empty, tiny, block-boundary,
  run, random, text-like and 1.2 MB inputs: every frame decodes to its
  input with the proven decoder and with libzstd's, and fits
  `ZSTD_compressBound`; the C API one-shot, with parameters, and
  streaming in random pieces with random flushes; and the compression
  fuzz target's checks.
- `tests/stress.rs` (`--ignored`): the fuzz target's checks on random and
  mutated inputs; `fuzz/` has the same as a cargo-fuzz target (and the
  compressor's checks as a second one, `compress`) for runs
  under AddressSanitizer.
- `tests/diag.rs`: says where verilith-zstd rejects the frames in a directory
  (`VZSTD_DIAG=dir`), to classify differences from libzstd.

## Performance

On an Apple M3 Pro, over Silesia (dickens, mozilla, nci, x-ray, xml at
levels 1, 3 and 19, with checksums), verilith-zstd decodes at about 0.68× the
speed of libzstd 1.5.7 one-shot and 0.70× streaming (`bench/`, best of
10 rounds per file; it takes the shared machine's `~/vf-bench.lock`).
The baseline was 0.27×. What closed the gap, all of it inside the proofs:

- match and literal copies in fixed 16-byte chunks (`src/prims.rs`), one
  copy when a match does not overlap itself;
- one bit read per sequence for the extra bits and one for the state
  updates, with FSE states proven in range so tables are read unchecked;
- the four Huffman streams decoded in lockstep, four symbols per stream
  from one read, with code lengths proven at most the table log so the
  four need no length checks, each stream decoded straight into its part
  of the output;
- the content size reserved up front, and in streaming each block hashed
  and decoded without copying it, with old output trimmed in place.

Sequence execution is now most of the time (60 to 80% of samples).

A second round, measured on Linux x86-64 only (a 4-core cloud Xeon VM,
libzstd 1.5.7 built from source, one pinned core, best of 15 rounds, run
to run noise about 3 to 5%), over the same 15 files:

| | before | after |
| --- | --- | --- |
| one-shot, fresh output vector each call | 0.50× | 0.61× |
| one-shot into a reused buffer (`decompress_reuse`) | | 0.73× |
| streaming, 128 KiB pieces | 0.62× | 0.73× |

libzstd is handed a preallocated buffer in the one-shot row, so the
reused-buffer row is the like-for-like one; a fresh vector over 32 MB
pays page faults on every call. What changed, all inside the proofs:

- the three FSE sequence tables are baked at table-build time into rows
  holding each code's base value and extra-bit count, so a sequence is
  one 56-bit load whose position does not depend on the table rows, and
  the three table rows are read independently of it (`seq::seq_fast`,
  proven against the same `spec::seq_run`);
- Huffman rows are also kept as one 16-bit word, and the four-symbol step
  keeps the unread bits at the top of a word, so a symbol is a shift, a
  load and a shift (`huf::huf_dec4`);
- the sequence and Huffman loops are also compiled with BMI2 and chosen
  at run time (`src/cpu.rs`, trusted wrappers, above);
- `frame::decompress_reuse` decodes into a vector the caller keeps.

These have not been measured on the M3; earlier x86 wins did not always
carry over to it, so the Apple figures above are from before this round.

A third round, same machine and method (best of 11 rounds):

| | before | after |
| --- | --- | --- |
| one-shot, fresh output vector each call | 0.61× | 0.66× |
| one-shot into a reused buffer (`decompress_reuse`) | 0.73× | 0.81× |
| streaming, 128 KiB pieces | 0.73× | 0.80× |

- the content checksum is fed block by block while the block is still in
  cache, instead of in one pass over the finished output
  (`frame::blocks_exec`, proven against the same whole-output hash);
- the Huffman table is filled from per-weight chains of symbols rather
  than by scanning all 256 symbols per weight, about five times fewer
  instructions per table;
- two-symbol Huffman lookups use the same shifted word as the
  single-symbol ones, and the two-symbol table is built only when the
  literals are at least eight times its size;
- the literals buffer is reused across blocks without being zeroed;
- FSE tables are built with the per-symbol counters on the stack and
  without the skip test when no rows are reserved.

By instruction count the decoder is now at about 1.3× libzstd on
mozilla.3 (831M against 642M). Sequence execution is 162 instructions
per sequence against libzstd's 124 on x-ray.19, and its time follows
that ratio. Ten restructurings of that loop were prototyped outside the
proofs first (two-phase decode and execute, repeat offsets from a table,
branch-free extra bits, one combined table, prefetching and others);
none removed more than 2% of the instructions, so none was carried into
the verified code. What is left is mostly values the compiler keeps on
the stack and the capacity check on each append to the output vector.

A fourth round removed that capacity check (same machine, best of 11):

| | before | after |
| --- | --- | --- |
| one-shot, fresh output vector each call | 0.66× | 0.68× |
| one-shot into a reused buffer (`decompress_reuse`) | 0.81× | 0.83× |
| streaming, 128 KiB pieces | 0.80× | 0.82× |

The sequence loop now appends to a `verilith_core::tail::Tail`: room for the
whole block (at most 128 KiB, and 64 bytes) is reserved once before the
loop, and the proof carries `len + room >= limit + 64` through it, so no
append tests the capacity. On top of that, a sequence with at most 32
literals and a match of at most 32 bytes from at least 16 back, which is
67 to 99% of sequences in these files, passes one combined test and is
then four 16-byte copies with no further decisions (`seq::seq_fast`,
`seq::copy_match_short`). Per file the decoder got 1 to 7% faster, most
on text and on level 19. This trades one trusted primitive of this crate
(`extend_within`, now gone) for `Tail` in verilith-core, which is larger; it is
in the list of what the proofs assume, above.

Two smaller steps after it, about 1% together (5% on x-ray.1, which is
nearly all literals):

- a Huffman table the spec accepts is proven to have exactly `2^log`
  rows (`huf::lemma_huf_full`: the weights sum to `2^log`, and summing
  the rows level by level is summing them weight by weight), so the
  per-symbol test that the row exists is gone;
- a short sequence tests its match offset against one bound, the smaller
  of the window and the output so far, worked out when the general case
  last ran; the output only grows, so it stays safe.

mozilla.3 is at 779M instructions against libzstd's 642M. The Huffman
loop is close to what its dependency chain allows (a shift, a table
load and a shift per symbol, four streams interleaved), so what remains
is the sequence loop and table building.

### Compression

The first version of the compressor, against libzstd 1.5.5's
`ZSTD_compress` at the same level (Linux x86-64 cloud VM, `bench/`'s
`cbench`, one-shot, seven compressible files from 1.6 to 35 MB: docs,
Rust source, JSON, text, low-entropy bytes, two binaries; geometric
means; every frame checked by libzstd's decoder):

| level | ratio vs libzstd | speed vs libzstd |
| --- | --- | --- |
| 1 | 0.96× | 0.33× |
| 3 | 0.98× | 0.39× |
| 19 | 0.87× | 0.50× |

Levels 1 to 9 come within 2 to 8% of libzstd's ratio. About a third of
the time goes to checking each compressed block with the proven decoder;
the rest is the match finders and the sequence encoder, not yet tuned.
Levels 16 to 22 use lazy2 matching where libzstd uses its optimal
parsers (btopt, btultra), hence the larger gap there.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/zstd/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/zstd/LICENSE-MIT), at your option.
