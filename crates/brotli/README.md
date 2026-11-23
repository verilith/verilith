# verilith-brotli

A Brotli (RFC 7932) decompressor written in Rust and verified with
[Verus](https://github.com/verus-lang/verus), with a C ABI that matches
google/brotli's decoder (`brotli/decode.h`), so that programs such as
Node.js can link it in place of `libbrotlidec`.

It follows the layout of [verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib)
and reuses [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (bit
sequences, canonical prefix codes, and the verified Huffman table builder
it shares with verilith-webp, `verilith_core::htable`).

**Status:** the decoder and the streaming wrapper are verified against
the spec (`cargo verus verify`: 372 functions, 0 errors, plus the Huffman
table builder it shares with verilith-webp, verified in verilith-core), including that
streaming always finishes. It passes google/brotli's test vectors and
a differential test against google/brotli on valid and corrupted streams.

**Speed:** measured with [vbench](https://github.com/verilith/verilith/tree/main/bench)'s
`brotli-decode` comparison (the same C driver linked with each library,
Silesia files compressed at quality 5 and 11, one-shot and streamed, 28
cases). On an Apple M3 Pro, verilith-brotli runs at 0.94x of google/brotli 1.2.0
as a geometric mean (three sittings, 0.946, 0.942 and 0.939, 31 pairs per
case): 0.98x to 0.99x on whole files at quality 5, 0.96x on whole files at
quality 11, 0.87x to 0.92x on 64 KiB inputs and 0.83x to 0.85x on 4 KiB
inputs, where set-up cost dominates. It is faster than google/brotli
on sao at both qualities and on x-ray at
quality 5. On a 4-core Xeon Linux VM, which is noisy (95% intervals about
+/-0.05), the geometric mean was 0.83x before the side-by-side tables
(below) and has not been re-measured since.

## What is proven

The format is written as a small-step machine in `src/spec.rs`
(`spec::step`), one item at a time: a header field, a code length, a
context map entry, a block switch, a command, a literal, a distance, one
copied byte. `spec::decodes(b, out, used)` says the stream `b` decodes to
`out`, using the first `used` bytes; `spec::rejects(b)` says it is
malformed.

- `Decoder::run` (`src/decoder.rs`): every state it stops in is one the
  spec reaches on the stream (`reached`), with the output so far in its
  ring buffer. `Bad` only when the spec rejects the stream; `Short` only
  when the input window ends, and when the window holds the rest of the
  stream, only when the spec runs out too. Every phase is covered: stream
  and meta-block headers, metadata, uncompressed blocks, block types and
  counts, prefix codes (simple and complex, with the Kraft-sum argument
  in `src/codes.rs` that the table builder accepts every code the spec
  does), context maps with run lengths and inverse move-to-front, commands,
  literals with their context, distances, backward copies through the
  ring, and static dictionary words with their transforms
  (`src/words.rs`).
- `stream::Stream::decompress` (`src/stream.rs`): stated, as in verilith-zlib, for
  a ghost `full` stream fixed when the `Stream` is made. As long as each
  call's input is the next piece of `full`, in pieces of any size and with
  output buffers of any size, every byte handed out is output the spec
  reaches on `full`; `Success` means the spec decodes `full` to exactly
  the output handed out; `Error` means the spec rejects `full`, or its
  output would pass 2^62 bytes.
- Termination and completeness (`src/rank.rs`, `src/stream.rs`): every
  call to `decompress` returns, with no exemption from Verus's termination
  check. The loop's measure is a lexicographic rank of the spec state
  (input bits left, then the phase, then what counts down inside it:
  meta-block bytes, command block count, code lengths or context map
  entries still to read), then output handed out, input taken and bytes
  kept; every decoder step strictly lowers the rank (`lemma_rank1`). And if
  the spec decodes `full`, a call given all of the remaining input and
  room for all of the remaining output returns `Success`.
- `bitread`, `items`, `prefix`: every read agrees with the spec's reading
  of the same bits; `huffman` (from verilith-webp): table construction and lookup
  agree with canonical decoding of the code lengths.

Not proven: anything about speed.

The hot path is `Decoder::fast_loop` in `src/decoder.rs`: it decodes whole
commands (insert-and-copy symbol, literals, distance, copy) with the
decoder's fields held in local variables and writes them back when it
leaves, which it does for anything unusual (a block switch, the end of the
input or of the output window). Its loop invariant says
that the locals describe a state the spec machine reaches from where the
loop was entered, so it is proven like the rest, with no assumptions.
Distance codes are looked up in a table built once per meta-block
(`mk_dtab`), proven equal to the spec's extra-bit count and distance value
for every code.

While a prefix code's lengths are read, the decoder keeps only the list of
symbols that got a length and a count per length; the full array of
lengths the spec talks about exists in the proof alone. verilith-core's
`build_sparse` builds the decoding table from that list, with the same
postcondition as the builder that walks the whole alphabet, which matters
on small inputs where most of the 704 command symbols have no code.

With context modeling, the tree for the next literal or distance depends
on the symbol just decoded, so the address of its table entry must not
wait on more loads than it has to. For a meta-block with at least 4 KiB of
output per tree, the tables of the literal trees, and of the distance
trees, are laid side by side at one width (`mk_flat`), and the entry is at
`tree * 2^width + bits`. `flat_ok` is part of the decoder invariant, and
the lookup (`sym_winf`) is proven to read the same entry as the lookup in
the tree's own table. The loop body is written once, with the choice of
lookup as a parameter, and compiled for each choice.

## Trusted

- `src/spec.rs`, the specification.
- `src/tables.rs`, generated from google/brotli's sources by
  `tools/gen_tables.c` (transforms, prefix/suffix strings, context lookup).
- `src/dictionary.bin` and `src/dict.rs`, the static dictionary (sha256
  `20e42eb1b511c21806d4d227d07e5dd06877d8ce7b3a817f378f313653f35c70`,
  which `tests/tables.rs` checks).
- `src/capi.rs`, the C adapter, and `Stream::open`, which gives callers
  outside Verus a stream without a ghost `full`.
- Slicing wrappers (`slice_subrange`, `slice_sub`, `slice_from`) and
  `dict_bytes`, each a one-line `&s[a..b]` with its contract.
- Verus, Rust and verilith-core's trusted base.

## Differences from google/brotli

- Large-window Brotli is not supported
  (`BROTLI_DECODER_PARAM_LARGE_WINDOW` = 1 fails).
- Shared dictionaries (`BrotliDecoderAttachDictionary`) and metadata
  callbacks are not supported.
- Every malformed stream reports the same error code.
- A command whose insert length runs past the end of its meta-block is
  rejected when the command is read; google/brotli decodes the literals
  first. On a truncated malformed stream the result can be `ERROR` where
  google/brotli says `NEEDS_MORE_INPUT`.
- `alloc_func`/`free_func` are accepted but not called.
- Output past 2^62 bytes is an error.
- When the input runs out partway through a byte, that byte is reported
  as not used, so the caller passes it again. If a stream ends inside
  bytes held back from an earlier call, those bytes still count as used.

## Building and testing

```sh
cargo build --release                 # target/release/libverilith_brotli.a
cargo build --release --features brotli-abi   # export BrotliDecoder* names
cargo test --release                  # google/brotli's test vectors
tests/c/run.sh 1000                   # differential test (needs google/brotli built with cmake)
scripts/verify.sh                     # the proofs
```

CI (`.github/workflows/ci.yml` at the repository root) verifies the proofs and runs `ci.sh` on every pull request and push to `main` that touches this crate or a crate it depends on.

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

`tests/data` and `src/dictionary.bin` come from google/brotli and are
under its MIT license, whose notice is in [LICENSE-brotli](LICENSE-brotli).
