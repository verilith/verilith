# verilith-zlib

A verified DEFLATE (RFC 1951), zlib (RFC 1950) and gzip (RFC 1952)
decompressor and compressor in Rust, proven with
[Verus](https://github.com/verus-lang/verus), with zlib's C API for both
directions. The decompressor is a hardened, faster replacement for zlib's
inflate; the compressor, one-shot or streaming, is proven to produce
output that decompresses back to its input.

The decoder, the Huffman table builder, the zlib/gzip wrappers, the
streaming API, both checksums and the compressor are proven against a
specification of the RFCs. `cargo verus verify` checks the functions here
and in [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (the shared
Huffman, bit and checksum proofs), with no errors. The CI workflow
(`.github/workflows/ci.yml` at the repository root) reruns the proofs and the tests
against the system zlib on every pull request and push to `main` that touches this
crate or one it depends on, and the fuzzers when a run is started by hand.

## Using it from Rust

```rust
fn main() -> Result<(), verilith_zlib::Error> {
    let data = b"hello hello hello hello hello hello".repeat(100);
    let z = verilith_zlib::zlib_compress(&data, 6); // level 0 to 9
    assert_eq!(verilith_zlib::zlib_decompress(&z)?, data);

    let gz = verilith_zlib::gzip_compress(&data, 9);
    assert_eq!(verilith_zlib::gzip_decompress(&gz)?, data);

    let raw = verilith_zlib::deflate(&data, 1); // raw DEFLATE
    assert_eq!(verilith_zlib::inflate(&raw)?, data);
    Ok(())
}
```

The one-shot decompressors stop at 1 GiB of output (`DEFAULT_LIMIT`);
`Decompressor::decompress_vec` takes a limit of the caller's. `Deflater`
compresses in pieces, and the static library exports zlib's C API.

## What is proven

| property | where it is stated |
| --- | --- |
| Memory safety: no out-of-bounds access, no overflow, no panics | every function (Verus checks all indexing and arithmetic) |
| Termination of every loop | every function (`decreases`) |
| Correctness: `Ok` exactly when the input is a valid stream, with the spec's output and length; `BadData`/`Truncated` only when the spec rejects it | `Decompressor::decompress_into`, `decompress_vec` against `wrap::spec_decompress`; `Inflater::run` against `spec::inflate_blocks` |
| Output bound: at most 1032 output bytes per input byte, for raw, zlib and gzip | `ilemmas::theorem_output_bound` against `spec::max_output` |
| Linear work: at most `work_bound(n, m) = 1200 * 8n + 131m + 32,301` decoder steps for `n` input bytes and `m` output bytes | `decompress_into`, `decompress_vec` ensures, via the ghost counter `Inflater::work` |
| Huffman tables decode exactly as the canonical code; table building takes at most `18n + 2 * 2^bits + 73` steps (Kraft's equality) | `huffman::build` |
| Adler-32 and CRC-32 (slicing-by-16, all 4096 table entries, the 32-lane Adler block) equal the RFC definitions | `checksum::adler32_update`, `checksum::crc32_update` |
| Resumable decoding: when the input runs out, the decoder stops in a state consistent with every continuation of the input, with its remaining work unchanged, so it resumes correctly when more input arrives | `Inflater::run` ensures for `Truncated`, against a ghost full stream `b` of which the input is a prefix |
| Streaming: fed a stream in input pieces of any size with output buffers of any size, the output delivered is always a prefix of the spec's output; `End` means the spec accepts the stream with exactly the output delivered and input used; `BadData` means the spec rejects it. Memory safety holds for any sequence of calls | `stream::Stream::inflate`, against a ghost full stream fixed at `Stream::new` and `wrap::spec_decompress` |
| Preset dictionaries: a zlib stream with FDICT stops with `NeedDict` until given the dictionary whose Adler-32 it names; a raw stream can be given one before its first input. The streaming theorem above then holds against the spec with that dictionary | `Stream::set_dictionary`, `Stream::inflate` against `spec::zlib_decompress_dict` and `spec::inflate_dict` |
| Compression round trip: for every input and level, the compressor's raw, zlib and gzip output decompresses, under the same spec, to exactly the input, using all of the output | `deflate::compress_raw`, `deflate::zlib_compress`, `deflate::gzip_compress` against `spec::inflate`, `spec::zlib_decompress`, `spec::gzip_decompress` |
| Streaming compression: input in pieces of any size, with any sequence of `Block`, `Sync` and `Full` flushes and level changes, in bounded memory (a window of at most 384 KiB); everything handed out, once finished, decompresses to all the input | `dstream::Deflater::finish` against `wrap::spec_decompress`; the window lemma `dlemmas::lemma_expand_shift` |
| Compression window: every match the streaming compressor emits reaches back at most `2^windowBits` bytes, the window its zlib header declares | `deflate::Matcher::fill` ensures (`tok_within`), with the `Deflater` invariant tying the matcher's window to `Deflater::window_bits` |
| C ABI bookkeeping: `deflate()` hands the caller exactly the compressor's output, in order, none lost or repeated, whatever the output buffer sizes; `inflateSync` stops only just after a `00 00 FF FF` marker, which may span calls; `adler32_combine` of the checksums of A and B (and B's length) is the checksum of A followed by B | `glue::Pending`, `glue::SyncSearch`, `glue::adler32_combine` against verilith-checksum's `spec::adler32` |
| Compression with a preset dictionary (raw or zlib): the same theorem, against the spec with that dictionary. Matches may refer back into the dictionary's last 32 KiB, and a zlib header sets FDICT and names the dictionary's Adler-32 | `dstream::Deflater::new_with_dict`, `Deflater::finish` against `dstream::spec_decompress_dict` (`spec::inflate_dict`, `spec::zlib_decompress_dict`) |
| Parallel compression: the input cut into chunks, each compressed on its own thread after the 32 KiB before it, the pieces joined into one stream. The same theorem as the serial compressor: the raw, zlib or gzip output decompresses to exactly the input, using all of it, whichever thread did which chunk and whether or not any thread ran | `par::compress` against `wrap::spec_decompress`; `Deflater::piece` (a piece adds its chunk to any output that ends with its window), `par::lemma_piece_join`, `par::lemma_joined` |
| Streaming foundations: decoding with the first bytes dropped is a shift of decoding the whole stream, and decoding after output `P ++ w` is `P ++` decoding after `w` once `w` holds the 32 KiB window | `slemmas::lemma_shift_rest`, `slemmas::lemma_win_rest` |
| Streaming progress: on a valid stream `inflate` never fails, and a call that does not end has filled the output or used all its input while the stream still needs more; the input used and output delivered never pass the spec's. So a valid stream fed in pieces of any size, with output space of any size, always reaches `End` | `Stream::inflate` ensures, `Stream::lemma_bounds`; `stream::feed_in_pieces` checks the whole loop |
| Streaming linear work, for any input: each call to `inflate` adds at most 10,000 decoder steps per input byte it uses, 2 per output byte it delivers, and 600,000 per call; summed over calls, the decoder's steps are at most that much for the whole stream | `Stream::inflate` ensures on `Stream::work`, with `Stream::lemma_steps` (`steps() <= work()`) |

When the input runs out inside a symbol or block header, the decoder
proves that the spec's end of the stream lies past the input it was given,
and the stream keeps the bytes from that unit's start to read again on the
next call. Held-back bytes are therefore always ones the stream still
needs, which rules out the trailer starting inside them: `inflate` returns
`Truncated` there only when the caller's input is not the stream.

The streaming work bound pays for re-reading held-back bytes in advance:
`Stream::work` is the decoder's step counter plus a potential (8 bits'
worth of work for each byte held back, the decoder's own credit, and the
window's slide), so a caller feeding one byte at a time through a large
block header costs a constant per call, not the header's length per call.
The per-call constant is large because it is priced at the worst-case
per-bit rate; real calls run far below it.

The compressor's theorem covers its output only, not its ratio: the
choices that affect size (which matches to take, the Huffman code lengths)
are made by ordinary code whose results are checked before they are used.
Every match is compared byte by byte, and code lengths go through
`huffman::build`, the decoder's own table builder, which accepts exactly
the lengths the spec accepts. A block whose codes fail the check, or would
be larger than the data, is stored instead.

The work counter counts every loop iteration in the decoder and the table
builder, and bulk copies one per byte; it is ghost state, erased at compile
time. The per-bit constant pays for the worst case, a block header that
rebuilds its tables (about 21,000 steps for a dynamic header of at least 29
bits, 10,834 to rebuild the fixed tables). Real inputs run far below it.

### Trusted base

What the proofs assume rather than prove:

- `src/spec.rs`: the specification itself. Review it against RFC 1950,
  1951 and 1952.
- [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)'s trusted base:
  the memory primitives in `verilith_core::prims` (unaligned loads, 8-byte copies
  and fills, slice copies; each `requires` is the bounds check that Verus
  proves at the call site), and the specs of bits and canonical Huffman
  codes, which `src/spec.rs` re-exports.
- [verilith-checksum](https://github.com/verilith/verilith/tree/main/crates/checksum)'s
  trusted base (its CPU dispatch, and the vector instructions it takes from
  verilith-simd), and its specs of Adler-32 and CRC-32, which `src/spec.rs`
  also re-exports.
- verilith-core's `spare` (`reserve_spare`, and `append8_spare`, which
  `src/prims.rs`'s `push_word` uses to append the low bytes of a word with
  one 8-byte store); its `requires` is proven at the call site.
- `src/deflate.rs`: `sort_keys`, which calls the standard library's
  `sort_unstable` to order symbols by frequency. Nothing is assumed about
  its result: `huff_lens` bounds-checks every symbol it reads back, and the
  code lengths are checked afterwards as before.
- `src/par.rs`: `run`, 25 lines of safe Rust (no `unsafe`) that hand the
  compression jobs to scoped threads and collect what they return. Its
  one assumption is that the bytes it stores in slot `k` are the ones the
  verified `job` returned for `k`; a slot may also be empty, and
  `par::compress` then does that job itself, so nothing is assumed about
  threads starting, finishing or scheduling. Everything else in parallel
  compression is verified: cutting the chunks, the pieces, the header,
  the checksum and trailer, and the join. It runs only when threads are
  turned on.
- `src/simd.rs`: CPU dispatch. It reruns the verified decoder compiled
  with BMI2 (same code, different instruction selection).
- `src/capi.rs` (C ABIs): an unverified adapter that maps `z_stream`
  fields onto the verified `Stream` and `Deflater`, copies gzip header
  fields out for `inflateGetHeader`, and computes the `crc32_combine*`
  helpers. Its buffer of pending deflate output, `inflateSync`'s marker
  search and `adler32_combine` are verified, in `src/glue.rs`. It is
  tested against the system zlib and fuzzed under AddressSanitizer
  (below).
- Verus, Z3 and the Rust compiler.

### Where the spec makes a choice

RFC 1951 leaves some cases open, and `src/spec.rs` follows zlib in each.
These are the points where verilith-zlib accepts or rejects differently from what
the RFCs alone imply, or from zlib:

| case | verilith-zlib | zlib |
| --- | --- | --- |
| Over-subscribed or incomplete Huffman codes | rejected, except an empty code or a single one-bit literal/length or distance code | same (inftrees.c) |
| More than 286 literal/length or 30 distance codes in a dynamic header | rejected | same |
| Literal/length code with no end-of-block code | rejected | same |
| Symbols 286, 287 and distances 30, 31 | rejected | same |
| Match distance beyond the output so far | rejected | same ("invalid distance too far back") |
| zlib header window size (CINFO) | any value up to 7 accepted; the window is always 32 KiB, so a match farther back than CINFO allows is accepted if it stays within the output | same by default (distances are checked against CINFO only when built with `INFLATE_STRICT`); a CINFO larger than `inflateInit2`'s `windowBits` is rejected, which verilith-zlib's C API does not do |
| zlib preset dictionary (FDICT) | supported (`Stream::set_dictionary`, `inflateSetDictionary`); one-shot calls without a dictionary reject it | same |
| raw preset dictionary | must be set before the first input | may be set at any time |
| gzip reserved flag bits, header CRC (FHCRC) | rejected / checked | same |
| gzip multi-member files | one member per call; the input length used is exact, so the caller can continue | `inflate` also stops after one member; `gunzip` loops |
| Data after the end of the stream | ignored; the used length excludes it | same |

## Design

- `src/spec.rs`: the formats as total functions over `Seq<u8>`, following
  zlib wherever the RFCs leave a choice, plus an explicit output bound
  (at most 1032 bytes of output per input byte).
- `src/huffman.rs`: table-driven canonical Huffman decoding. Tables are
  filled longest code first so each entry holds the shortest matching code,
  which is the spec's definition. The code spec and the table lemmas are
  shared with verilith-webp in `verilith_core::huffman`.
- `src/inflate.rs`: a fast loop (8-byte refills, packed table entries, up to
  three literals per refill, 8-byte match copies) and a careful loop for the
  tail. The decoder can stop when the output buffer is full and resume.
- `src/checksum.rs`: re-exports `verilith_checksum`: Adler-32 and CRC-32,
  with the verified vector kernels (dot products for Adler-32, carry-less
  multiplication for CRC-32) when the CPU has them. `src/simd.rs` (trusted) runs the decoder with BMI2.
- `src/stream.rs`: streaming (input and output in pieces of any size) on
  top of the resumable decoder, with incremental header and trailer
  parsing and a 32 KiB sliding window. A byte the decoder has only partly
  used is copied into `pending`, so the decoder's state only refers to
  bytes the stream owns. Verus callers pass the ghost full stream to
  `Stream::new`; plain Rust callers use `Stream::open`.
- `src/capi.rs`: C ABIs for zlib (both directions) and libdeflate's
  decompressor (`libdeflate_*_decompress[_ex]`). zlib compression:
  `deflateInit[2]_`, `deflate` (every flush mode), `deflateEnd`,
  `deflateReset[Keep]`, `deflateParams`, `deflateBound`, `deflatePending`,
  `deflateCopy`, `deflateTune`, `compress[2]`, `compressBound`.
  Decompression: `inflateInit[2]_`,
  `inflate`, `inflateEnd`, `inflateReset[2]`, `inflateResetKeep`,
  `inflateSetDictionary` (`Z_NEED_DICT`), `inflateGetDictionary`,
  `inflateGetHeader`, `inflateSync`, `inflateCopy`, `inflateBack[Init_|End]`,
  `uncompress[2]`, `adler32[_z]`, `crc32[_z]`, `adler32_combine[64]`,
  `crc32_combine[64]`, `crc32_combine_gen[64]`, `crc32_combine_op`,
  `get_crc_table`, `zError`, `zlibCompileFlags`. Exported as `vz_*` and
  `vzlib_*`, or under the original names with the `zlib-abi` /
  `libdeflate-abi` features. Differences: `zalloc`/`zfree` are accepted
  but not called (memory comes from the Rust allocator); `inflatePrime` is
  not supported; `inflateValidate` cannot turn checksum checks off;
  `inflateSyncPoint` and `inflateMark` report nothing; after
  `inflateSync` the rest is decoded as raw DEFLATE. On the compression
  side `deflateSetDictionary` works for zlib and raw streams before the
  first `deflate()` (zlib also allows it later on raw streams; verilith-zlib
  returns `Z_STREAM_ERROR` there); `deflateSetHeader` works before the
  first `deflate()` (zlib also allows it later, until the header is
  written); `deflatePrime` is not supported (`Z_STREAM_ERROR`); the strategy
  and `deflateTune` parameters are accepted and not used; `deflate()` may
  hold up to a few hundred KiB of output internally when the caller's
  output buffer is small, and `deflateBound` is a little larger than
  zlib's. The compressed bytes are not zlib's: they decompress to the
  same data with any inflater, but a test that compares compressed output
  with a file zlib wrote will see a difference.
- `src/par.rs`: parallel compression, the scheme pigz uses. The input is
  cut into 256 KiB chunks. Each chunk becomes a piece: raw DEFLATE blocks
  from a `Deflater` whose preset dictionary is the 32 KiB before the
  chunk, closed by a sync flush so the piece ends on a byte boundary and
  has no final block. The output is one header, the pieces in order, an
  empty final block and one trailer, so it is an ordinary stream that any
  decoder reads, and it is the same bytes for any number of threads. The
  checksum of the whole input is one more job, done first. Off by
  default: `par::set_threads` (C: `vzlib_set_threads(n)`, 0 for one per
  CPU) or the environment variable `VZLIB_THREADS` turns it on for
  `compress`, `compress2` and a `deflate()` call that is given the whole
  stream at once (`Z_FINISH` on the first call), for inputs of 512 KiB
  and up at levels 1 to 9. Streams fed to `deflate()` in pieces, streams
  with a preset dictionary and smaller inputs are compressed on the
  calling thread as before. A parallel stream is a few bytes per chunk
  larger than the serial one and stays within `compressBound`.
- `verilith_core::prims` (trusted): unchecked loads and copies whose `requires`
  clause is the bounds check Verus proves at each call site.
- `src/deflate.rs`, `src/dstream.rs`, `src/bitwriter.rs`, `src/dlemmas.rs`:
  the compressor, one-shot (`deflate`) and streaming (`dstream`).
  An LZ77 matcher with 4-byte hash chains, 8-byte match comparison and
  zlib's search parameters per level (greedy at levels 1 to 3, lazy
  above), Huffman code lengths from a Huffman tree limited
  to 15 bits, and one dynamic block per 16K tokens, with stored blocks
  as the fallback. The bit writer keeps the bits written as ghost state;
  `dlemmas` proves that decoding those bits with the spec replays the
  tokens, block by block, so the output inflates to the input.

## Tests

`cargo test --release` compares against the system zlib: round trips at
every level and strategy for raw, zlib and gzip, 20k mutated streams and 50k
random inputs (same accept/reject verdict, output and input length),
streaming in random-sized pieces, and the C ABIs (preset dictionaries,
gzip headers, `inflateSync`, `inflateCopy`, `inflateBack` and the combine
helpers, each against zlib's answer). `tests/c/run.sh FILES`
builds a small `inflate()` program against zlib and against `libverilith_zlib.a`
and checks they print the same output, totals and checksum.

`tests/deflate.rs` round-trips the compressor's raw, zlib and gzip output
at levels 0, 1, 6 and 9 through both verilith-zlib and the system zlib.
`tests/capi_deflate.rs` drives `deflate()` with random input and output
pieces and random flushes for every wrapper and window size and checks
zlib decompresses the result; it also checks that after each
`Z_SYNC_FLUSH` zlib can decode all input so far, `compress2` and one-call
`deflate()` within the bounds, `deflateParams`, `deflateCopy`,
`deflateReset` and `deflatePending`, and that every match stays inside
the window `windowBits` declares (zlib, given the same `windowBits`,
inflates 100 bytes at a time, so it copies matches from its own window). `tests/c/run_deflate.sh FILES`
compresses with a zpipe-style C program linked against `libverilith_zlib.a`
(zlib-abi) and decompresses with the system zlib.

`tests/par.rs` round-trips parallel compression through verilith-zlib and the
system zlib for raw, zlib and gzip at levels 0, 1, 6 and 9, with chunk
sizes down to 32 KiB, 1 to 8 threads and every window size; checks the
output is the same bytes for any thread count; and drives `compress2` and
one-call `deflate()` with threads on, within `compressBound`, against the
totals and check value the serial path reports.

`fuzz/` has five cargo-fuzz targets that the CI workflow runs:
`compress_vs_zlib` compresses arbitrary bytes with verilith-zlib and checks zlib
decompresses them to the same bytes; `c_deflate` drives the compression C
API with fuzzer-chosen pieces, flushes, level changes and stream copies
under AddressSanitizer and checks zlib decompresses the result;
`stream_vs_zlib` feeds zlib-compressed data (optionally with a flipped bit)
through the streaming C API in random chunks and checks the output, input
used and verdict against zlib; `c_abi_bytes` feeds arbitrary bytes to every
one-shot and `inflate()` entry point under AddressSanitizer; `c_abi_state` drives header
capture, dictionaries, `inflateSync`, `inflateCopy` and
`inflateGetDictionary` on arbitrary bytes under AddressSanitizer.

## Performance

Measured with `bench/` (a separate crate: `bench/corpus.sh DIR` builds the
files, then `bench/run1.sh inflate|deflate DIR [rounds]`) against zlib 1.3,
zlib-ng 2.3.3 (native API) and libdeflate 1.19 on a cloud VM (Intel Xeon,
AVX2 and AVX-512). `run1.sh` runs each library alone in its own process,
pinned to one core with `taskset`, with a warm-up round and then the best
of the rest; all four were measured in the same sitting, since the VM's
clock speed drifts.

### Decompression

One-shot into a buffer of known size, best of 9, MB/s of output (input
compressed by zlib at level 6):

| file | format | verilith-zlib | zlib | zlib-ng | libdeflate | verilith-zlib / libdeflate |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| bin (8 MB of libLLVM) | raw | 914 | 536 | 857 | 1273 | 0.72 |
| html (2.6 MB) | raw | 840 | 373 | 747 | 1144 | 0.73 |
| js (9.1 MB) | raw | 1120 | 462 | 1051 | 1563 | 0.72 |
| text (4.8 MB) | raw | 838 | 362 | 775 | 1146 | 0.73 |
| xml (1 MB) | raw | 1852 | 857 | 1686 | 2593 | 0.71 |
| small (4 KB text) | raw | 457 | 403 | 412 | 616 | 0.74 |
| js | zlib | 1045 | 392 | 948 | 1380 | 0.76 |
| text | gzip | 780 | 325 | 747 | 1097 | 0.71 |
| xml | zlib | 1684 | 658 | 1509 | 2417 | 0.70 |

On raw DEFLATE, verilith-zlib decodes 1.7 to 2.4 times as fast as zlib on the
large files (1.13x on 4 KB), slightly faster than zlib-ng, and at 0.71 to
0.74 of libdeflate's speed. Matches with a distance of at least 8 always
copy their first 40 bytes with five unconditional 8-byte moves, which
covers most matches without a length-dependent branch (as libdeflate does).
That gained 2% to 10%. libdeflate is still faster everywhere here. Its
instruction count per byte is close to verilith-zlib's (callgrind), so the difference
is in how well the decode loop overlaps its table lookups and copies.

Each dynamic block rebuilds its Huffman tables. `huffman::build` fills a
table the way libdeflate does: it starts from one entry, and for each code
length doubles the table by copying it (one `memmove`) and then writes one
entry per code of that length. Writing every entry of every code with a
strided loop instead made table building about 1.5 times as slow, and the
4 KB file 9% slower overall.

With zlib or gzip framing, verilith-zlib decodes 64 KB of output at a time and
updates the checksum over each chunk right away, while the chunk is still in
cache. Summing the whole output after decoding was 3% to 10% slower on the
large files, and left verilith-zlib behind zlib-ng on js zlib and text gzip. verilith-zlib is
now ahead of zlib-ng on every row.

### Compression

One-shot raw DEFLATE, best of 5, MB/s of input, and compressed size over
input size:

| file | level | verilith-zlib | zlib | zlib-ng | libdeflate | verilith-zlib ratio | zlib ratio | zlib-ng ratio | libdeflate ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| bin | 1 | 240 | 160 | 342 | 303 | 0.238 | 0.251 | 0.314 | 0.239 |
| bin | 6 | 82 | 37 | 100 | 128 | 0.227 | 0.224 | 0.227 | 0.224 |
| bin | 9 | 16 | 6 | 29 | 18 | 0.225 | 0.223 | 0.223 | 0.222 |
| html | 1 | 168 | 142 | 282 | 240 | 0.270 | 0.295 | 0.353 | 0.270 |
| html | 6 | 71 | 49 | 87 | 112 | 0.246 | 0.245 | 0.247 | 0.245 |
| html | 9 | 33 | 27 | 38 | 43 | 0.244 | 0.244 | 0.245 | 0.242 |
| js | 1 | 177 | 132 | 412 | 299 | 0.210 | 0.237 | 0.288 | 0.210 |
| js | 6 | 86 | 43 | 73 | 131 | 0.183 | 0.181 | 0.181 | 0.183 |
| js | 9 | 26 | 15 | 32 | 28 | 0.179 | 0.179 | 0.179 | 0.179 |
| text | 1 | 158 | 116 | 306 | 232 | 0.291 | 0.322 | 0.392 | 0.291 |
| text | 6 | 61 | 36 | 72 | 84 | 0.259 | 0.258 | 0.258 | 0.259 |
| text | 9 | 21 | 24 | 40 | 29 | 0.253 | 0.255 | 0.255 | 0.253 |
| xml | 1 | 340 | 235 | 585 | 469 | 0.119 | 0.133 | 0.161 | 0.121 |
| xml | 6 | 147 | 84 | 133 | 226 | 0.109 | 0.113 | 0.109 | 0.109 |
| xml | 9 | 19 | 13 | 40 | 31 | 0.108 | 0.108 | 0.109 | 0.108 |
| small | 1 | 181 | 180 | 278 | 325 | 0.440 | 0.459 | 0.592 | 0.435 |
| small | 6 | 131 | 110 | 115 | 199 | 0.433 | 0.431 | 0.430 | 0.428 |
| small | 9 | 119 | 117 | 91 | 146 | 0.432 | 0.431 | 0.431 | 0.427 |

The compressor uses libdeflate's match finder design and parameters. Level
1 uses a hash table with two candidates per hash and no chains. Levels 2 to
4 parse greedily. Higher levels use hash chains with libdeflate's
per-level search depth, "nice" length and lazy matching, and levels 8 and 9
look two bytes ahead. Compressed sizes now track libdeflate's, within 1.5%
on every row, and are 4% to 11% smaller than zlib's at level 1. verilith-zlib is
faster than zlib on every row except text at level 9 (21 vs 24 MB/s). It is
1.2 to 2.2x zlib's speed at level 6, and ahead of zlib-ng at level 6 on js,
xml and 4 KB inputs. libdeflate is still faster. verilith-zlib runs at 0.56 to 0.79x
its speed at level 1, 0.63 to 0.73x at level 6 and 0.61 to 0.93x at level 9.
Under callgrind, level 1 on 1 MB of html runs 42M instructions to
libdeflate's 30M. The length and distance symbols now come from
libdeflate's lookup tables, each entry proven against the spec, and each
block builds the bits for every length once. That took the token writer
from 10.3M to 8.7M instructions (libdeflate's is 5.6M) and the whole run
from 47.4M to 41.8M. On an Apple Silicon Mac, it is 5% to 7% faster at
level 1 and 1% to 3% faster at levels 6 and 9, with byte-identical output.
Most of what is left is in the match finder.

Against the previous version on this VM, level 1 is 1.3 to 1.8x faster and
level 6 is 1.65 to 2.3x faster. Level 9 is up to 4x faster (bin went from 4
to 16 MB/s). Run-to-run noise is about 10%.

### Parallel compression

`par::compress` against the serial `gzip_compress`, both producing gzip,
on an Apple M3 Pro (6 performance and 6 efficiency cores), with
`examples/par_bench.rs`: best run in 3 seconds, MB/s of input, 256 KiB
chunks. The machine was not idle (load average 7 to 9), so read the
ratios, not the MB/s.

| file | level | serial | 1 thread | 2 | 4 | 6 | 12 | 12 threads / serial | size against serial |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| samba (21.6 MB) | 6 | 133 | 121 | 241 | 471 | 684 | 1007 | 7.6x | +0.01% |
| dickens (10.2 MB) | 6 | 71 | 69 | 132 | 258 | 367 | 535 | 7.6x | +0.06% |
| mozilla (51.2 MB) | 1 | 205 | 164 | | | 870 | 1354 | 6.6x | +0.08% |
| mozilla | 6 | 115 | 100 | 193 | 379 | 528 | 834 | 7.2x | -0.02% |
| mozilla | 9 | 31 | 29 | | | 167 | 257 | 8.4x | -0.01% |
| xml (5.3 MB) | 6 | 207 | 193 | 383 | 715 | 941 | 1351 | 6.5x | +0.14% |

With 6 threads it is 4.3 to 5.4x the serial compressor, with 12 it is 6.5
to 8.4x (the second six cores are the slower ones). On one thread the
chunked path is 3% to 20% slower than the serial one, so a parallel run
spends about that much more CPU in total. There is no gain below two
chunks (512 KiB), where the serial compressor runs instead, and none for
a caller that feeds `deflate()` in pieces. What this costs in trust is
the 25 lines of `par::run` (see "Trusted base").

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/zlib/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/zlib/LICENSE-MIT), at your option.
