# verilith-qpack

A sans-I/O QPACK (RFC 9204) encoder and decoder for HTTP/3, written in Rust
and proven correct with [Verus](https://github.com/verus-lang/verus). It
covers both halves of a connection: the decoder (field sections, the
peer's encoder stream, the decoder stream it writes back) and the encoder
(field sections, the encoder stream it writes, the peer's decoder stream).
That includes the dynamic table with Insert Count and Base, and the limit
on blocked streams on both sides.

Sans-I/O means the crate never reads or writes a socket. The caller hands
it bytes and takes bytes from it:

```rust
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};

// Settings: table capacity 4096, 16 blocked streams.
let mut enc = Encoder::new(4096, 16, 4096).unwrap();
let mut dec = Decoder::new(4096, 16, 1 << 16).unwrap();

let mut fields = Fields::new();
fields.push(b":method", b"GET", false);
fields.push(b":path", b"/index.html", false);

let mut section = Vec::new();              // goes in a HEADERS frame
enc.encode(0, &fields, &mut section);
let mut es = Vec::new();                   // goes on the encoder stream
enc.take_output(&mut es);

let mut unblocked = Vec::new();
assert!(dec.feed_encoder(&es, &mut unblocked));
let mut out = Fields::new();
assert_eq!(dec.decode(0, &section, &mut out), Res::Done);

let mut ds = Vec::new();                   // goes on the decoder stream
dec.take_output(&mut ds);
assert!(enc.feed_decoder(&ds));
```

The Huffman decoder and encoder and their proofs come from
[`verilith-hpack`](../hpack), since QPACK uses HPACK's code.

## What is proven

`src/spec.rs` is the specification, written as pure functions from RFC
9204. It covers prefixed integers (§4.1.1), string literals (§4.1.2), the
static and dynamic tables (§3, Appendix A), encoder instructions (§4.3) and
the encoder stream, field sections with Required Insert Count and Base
(§4.5), decoder instructions (§4.4) and the decoder stream, and blocked
streams (§2.1.2, §2.2.1). Where the RFC leaves a choice, the spec makes one
and says so. The proofs show:

- **The decoder decodes a field section exactly as the spec does**
  (`Decoder::decode`, `spec::dec_section`). It returns the field lines,
  reports that the stream is blocked (and records it), or reports an error
  exactly when the spec does. It also emits the Section Acknowledgment the
  spec emits. A section that would go over the limit on blocked streams is
  an error, as §2.1.2 requires. `cancel` follows `spec::dec_cancel`.
- **The encoder stream can be split anywhere** (`Decoder::feed_encoder`,
  `spec::dec_feed`). The result is stated against everything received so
  far, not against the pieces. The table, the streams this unblocks, and
  the Insert Count Increment it emits are what `spec::erun` gives on the
  concatenation. This rests on an extension and a split lemma
  (`lemmas::lemma_erun_split`). The same holds for the decoder stream on
  the encoder side (`Encoder::feed_decoder`, `lemmas::lemma_drun_split`).
- **Linear work, however the input is split.** The decoder counts its work
  in ghost state, with a potential (16 per byte of a held partial
  instruction, plus 1 per table entry to pay for evicting it). Over any
  sequence of `feed_encoder_metered` calls, the work is at most 18 steps
  per input byte, plus 1 and the number of blocked streams per call.
  `decode_metered` is at most 13 steps per byte of the section, plus the
  size limit, plus twice the number of blocked streams.
- **Encode then decode gives back the fields.** `Encoder::encode`'s
  postcondition says that the spec decoder (`spec::section`), given the
  encoder's table, decodes the bytes it wrote to exactly the fields it was
  given. This holds under any SETTINGS_MAX_FIELD_SECTION_SIZE that allows
  those fields. The encoder's table is in turn exactly `spec::erun` over
  everything the encoder has written to the encoder stream
  (`Encoder::inv`), which is what a decoder that has read the stream will
  hold. The lemmas are in `rt.rs`: one per field line kind and encoder
  instruction, then a theorem for whole sections (`lemma_section_rt`).
  Huffman coding is part of it: the encoder uses Huffman only when it is
  shorter, and `verilith_hpack::henc::encode` is proven to produce bytes that `hpack`'s
  verified decoder decodes back to the input.
- **The encoder keeps its obligations to the decoder** (`spec::enc_ok`,
  part of `Encoder::inv`, kept by every method). The table capacity stays
  within the decoder's maximum. No entry is evicted while an
  unacknowledged section refers to it, or before the decoder has
  acknowledged inserting it (the Known Received Count). The streams that
  could block never number more than SETTINGS_QPACK_BLOCKED_STREAMS. The
  lemmas `rt::lemma_keeps_*` and `lemma_item_keeps` show that a field line
  stays correct under any later table that keeps the entry it refers to.
- No panics, overflows or out-of-bounds accesses in any of the above.
  The crate has no `assume` and no `admit`.

The connection-level property, that a decoder which receives the streams
late, in pieces and in any order decodes every section to the fields
encoded, is tested rather than stated as one theorem
(`tests/roundtrip.rs`, 300 random connections with random capacities and
blocked-stream limits). It follows from the pieces above.

## Trusted computing base

What the proofs do not cover, and what is done about each:

- **The spec** (`spec.rs`). Read it against RFC 9204. The RFC's examples
  (Appendix B) are tests (`tests/rfc.rs`), along with blocking and error
  cases.
- **The static table.** `stable.rs` is generated by `tools/gen_tables.py`
  from two independent sources, the RFC's Markdown source and ls-qpack. The
  script fails unless they agree entry for entry. `table::static_entry` is
  the `external_body` function that reads it. `tests/tables.rs` checks
  entries quoted from the RFC.
- **The Huffman tables.** Both are `verilith-hpack`'s: the decoder's,
  whose layout is checked at run time against the RFC code, and the
  encoder's byte-pair table, built once behind a `OnceLock` (see that
  crate's README).
- **Hints** (`hints.rs`, plain Rust). The encoder looks fields up in a hash
  index and a static-table index to find candidates. These are not trusted
  for correctness: every candidate is compared byte for byte against the
  table before it is used. A wrong hint can cost compression, never
  correctness. `encoder.rs` reaches them through small `external_body`
  functions (`static_find`, `field_hash`, `Hints`) whose contracts promise
  nothing about their results. The code is safe Rust.
- **Shared primitives** from `verilith-core`: `extend` and
  `load_u64_le`, both verified there against vstd's specs.
- **Verus and Z3**, and the Rust compiler.

## Performance

`bench/run.sh` compares it with [ls-qpack](https://github.com/litespeedtech/ls-qpack)
2.7.1, the C library used by LiteSpeed, lsquic and others. The bench records
one connection per workload (field sections and both streams), checks that
each library decodes the other's output, and then times each library
replaying it. The numbers are nanoseconds per field section, best of 200
runs, on one core with `-C target-cpu=native` and `-march=native`:

| Workload | Table | vqpack bytes | ls-qpack bytes | vqpack encode | ls-qpack encode | vqpack decode | ls-qpack decode |
|---|---|---:|---:|---:|---:|---:|---:|
| Browser requests (622 B) | 4096 B, 100 blocked | 46.1 | 49.6 | 429 | 680 | 245 | 366 |
| Browser requests (622 B) | static only | 442.1 | 442.1 | 871 | 893 | 1152 | 1201 |
| Server responses (323 B) | 4096 B, 100 blocked | 39.5 | 39.9 | 322 | 459 | 215 | 284 |
| Server responses (323 B) | static only | 142.9 | 142.9 | 377 | 448 | 428 | 478 |

With a dynamic table, vqpack's output is as small or smaller, it encodes
1.4 to 1.6 times faster, and it decodes 1.3 to 1.5 times faster. With the
static table only, the work is mostly Huffman coding, and the two are
close.
