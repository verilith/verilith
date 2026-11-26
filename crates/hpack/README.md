# verilith-hpack

A verified HPACK (RFC 7541) header decoder and encoder, written in Rust and
proven correct with [Verus](https://github.com/verus-lang/verus). The
decoder is built to replace the decoder ("inflater") in nghttp2, and so the
one Node.js uses for `node:http2`. The encoder is proven against the
decoder's own specification, for Verilith's HTTP/2 server.

HPACK is the first thing an HTTP/2 server runs on bytes from a peer:
integers with continuation bytes, Huffman codes, a dynamic table with
eviction by size, and size updates with rules about when they may come.
nghttp2's inflater is careful C; verilith-hpack is the same decoder with proofs.

## What is proven

`src/spec.rs` is the specification, as pure functions: integers (§5.1),
Huffman strings (§5.2, Appendix B), string literals, the static and dynamic
tables (§2.3, §4), the field representations (§6) and table size updates
(§4.2, §6.3), with nghttp2's limits where the RFC leaves a choice (at most
five continuation bytes and 32-bit values, strings of at most 65536 bytes,
size updates only at the start of a block and no larger than the announced
limit, and an update required after the limit is lowered). The proofs show:

- **Each representation** (`Decoder::rep`) decodes to exactly the field,
  table and decoder state `spec::rep` gives, or reports "incomplete" or
  "invalid" exactly when the spec does.
- **Huffman decoding** (`huffman::decode`) gives exactly `spec::hdec`: the
  symbols of the codes, followed by fewer than 8 bits of padding that are
  all ones. EOS, longer padding, and padding that is not all ones are
  errors.
- **The dynamic table** (`table.rs`) holds exactly the spec's entries and
  size after each insert, eviction and resize.
- **Input split anywhere gives the same result** (`Decoder::feed`). A
  header block can arrive in any number of pieces (CONTINUATION frames, or
  a caller's own buffering). `feed`'s result is stated against the whole
  undecoded input: the fields it emits, the state it ends in and what it
  reports are what `spec::rep` gives on the concatenation, not on the
  pieces. This rests on an extension lemma (`lemmas.rs`): once a
  representation decodes or fails, more input after it changes nothing.
- **Linear work, however the input is split** (`Decoder::feed_metered`).
  The decoder counts its work in ghost state: a step is a turn of a loop
  whose number of turns is not bounded by a constant (`feed`'s own loop,
  the Huffman decoder's, the table's eviction loop) or a byte copied. The
  theorem is a potential argument:

  ```text
  steps(feed(input)) + pot(after) <= pot(before) + 16 * input.len() + 96 + settings
  ```

  `pot` is 8 per buffered byte, less 4 per byte of a cached name, plus 1
  per dynamic table entry (which pays for evicting it). It is 0 for a new
  decoder and never negative, so over any sequence of calls the work is at
  most 16 steps per input byte plus `96 + settings` per call, wherever the
  input is split. `settings` is SETTINGS_HEADER_TABLE_SIZE (4096 unless the
  local side raises it); it pays for the one copy that is not proportional
  to the input, the name of a table entry copied into a new entry.
  `change_settings_metered` and `end_block` only lower the potential. The
  bound rests on two facts about buffered input: a representation that was
  too short is decoded again only once enough input has arrived to
  possibly complete it, and the name string it had already decoded is
  kept, not decoded again (`Decoder::name_end`). A completed
  representation then ends exactly at the end of the buffer
  (`lemmas::lemma_end_at_need`, from the truncation lemma
  `lemma_rep_trunc`: decoding reads nothing past the representation's
  end).
- No panics, overflows or out-of-bounds accesses, in all of the above.

## The encoder

`Encoder` (`src/encoder.rs`) keeps a copy of the peer decoder's state, a
`spec::DState`: the dynamic table, its size, the peer's
SETTINGS_HEADER_TABLE_SIZE and any size update it is owed. The theorem
(`Encoder::encode`'s `ensures`) is stated against the decoder's
specification above, not a separate encoder spec:

```text
block(state, out) == Some((fields, s2))   and   end_block(s2) == state'
```

`spec::block` decodes a whole header block with `spec::rep`, the function
the decoder is proven to compute; `fields` are the fields given, with
`never` set exactly for the ones marked `sensitive`; `state'` is the
encoder's own state after the call. So the peer's decoder ends each block
with the dynamic table the encoder has, and the next block is encoded
against the right table. What the proofs cover:

- **Huffman** (`hencode.rs`): the bytes written decode by `spec::hdec` to
  the input. The proof is on bit sequences: the codes one after another,
  then fewer than 8 one bits. That such bits decode back needs the code to
  be prefix-free and no run of 1 to 7 one bits to be a code;
  `hencode::check` verifies both against the RFC table at run time, once,
  as the decoder's `huffman::check` verifies its canonical layout.
- **Integers, string literals, every representation** (`emit.rs`):
  indexed, literal with incremental indexing, without indexing and never
  indexed, each with an indexed or a new name; and size updates. Each is a
  spec function (`int_enc`, `str_enc`, `lit_enc`), and a lemma says what
  `spec::rep` decodes it to. A string is Huffman-coded exactly when that is
  shorter.
- **Size updates** (`Encoder::start`): `change_settings(n)` mirrors
  `spec::change_settings` (as nghttp2's decoder does, a lower limit
  shrinks the table at once), and the next block starts with the updates
  §4.2 asks for: the lowest limit announced since the last update when it
  is below the size used, then that size. `set_table_size` chooses the
  size within the peer's limit.
- **The block** (`Encoder::encode`): representations compose
  (`emit::lemma_block_append`, from the decoder's extension lemma), so the
  whole block decodes to the whole list. A name or value longer than
  65536 bytes (the decoder's limit) is refused with nothing written.
- No panics, overflows or out-of-bounds accesses.

Which representation a field gets is a policy, outside the theorem, since
every choice is proven: an exact match in the static or dynamic table is
indexed; otherwise a literal, indexed into the table unless it is one of
nghttp2's never-repeating fields (`:path`, `content-length`, `etag`,
`set-cookie`, `location`, `age`, `if-modified-since`, `if-none-match`,
`authorization`, a cookie shorter than 20 bytes) or would take more than
three quarters of the table. Mark credentials `sensitive`.

Lookups go through two indexes that are not trusted, because every
candidate they give is compared with the table entry before it is used: a
perfect hash of the static table's names (`sindex.rs`, generated by
`tools/gen_sindex.py`), and a 512-slot hash index of the dynamic table
(`Encoder::ix`, two slots per key, entries named by insertion number). A
wrong or stale candidate can only cost compression, never correctness.

```rust
use verilith_hpack::{Encoder, Header};

let mut e = Encoder::new().unwrap();
let mut out = Vec::new();
let fields = [
    Header { name: b":status", value: b"200", sensitive: false },
    Header { name: b"content-type", value: b"text/html", sensitive: false },
];
assert!(e.encode(&fields, &mut out));      // out is the header block
// SETTINGS_HEADER_TABLE_SIZE from the peer, where its decoder applies it
// (after the blocks sent before the SETTINGS ACK):
e.change_settings(1024);
```

## Trusted computing base

What the proofs do not cover, and what is done about each:

- **The spec** (`spec.rs`). Read it against RFC 7541. The RFC's examples
  (Appendix C) are tests (`tests/rfc.rs`).
- **The tables.** `htables.rs` (the Huffman code) and `stable.rs` (the
  static table) are generated by `tools/gen_tables.py` from nghttp2's
  sources, which cross-checks them against a second, independent source
  (Go's `x/net/http2/hpack`) and fails on any difference. The decoder reads
  the code through a canonical layout (`FIRST`, `CNT`, `OFF`, `SYMS`); that
  layout is not trusted: `huffman::check()` checks it against the RFC table
  when a decoder is made, and the proofs assume only what it checks.
  `tests/tables.rs` also checks that the code is prefix-free and complete
  and that every symbol round-trips.
- **`table::static_entry`**: it returns `stable.rs`'s entry `i`, which
  the spec names `static_name(i)` and `static_value(i)`.
- **The encoder's `external_body` function** `hencode::ready` (a
  `OnceLock` returns what `hencode::check` computed), the same pattern as
  the decoder's `huffman::dtab`. `encoder::bytes_eq` is verified: it
  compares 8 bytes at a time with verilith-core's `load_u64_le`, as the
  hash index reads them.
- **The statement `spec::block`**, which strings `spec::rep` together over
  a block. It is what `Decoder::feed` computes, but that is not itself a
  theorem here: `feed` is proven against `rep` one representation at a
  time.
- **The C API** (`src/capi.rs`) and **the nghttp2 shim**
  (`compat/nghttp2/nghttp2_hd_vhpack.inc`), which are unverified glue:
  pointers in and out, and nghttp2's reference-counted buffers.
- **What a step costs.** The work bound counts loop turns and bytes
  copied, not machine instructions. It assumes `Vec` growth is amortized
  constant time per byte and that allocation and freeing take constant
  time. The integer decoder (at most 6 turns), the Huffman decoder's
  refill (at most 8) and code search (at most 30) are bounded by constants
  and not counted.
- **A buffer limit.** `feed` buffers at most 16 MiB of a representation that
  has not fully arrived (one is at most 131085 bytes), and reports
  "invalid" beyond that. The spec allows that outcome explicitly.
- Verus, Z3 and the Rust compiler.

## Using it

### From Rust

```rust
use verilith_hpack::decoder::{Decoder, Feed};

let mut d = Decoder::new().unwrap();
let block: &[u8] = &[0x82, 0x86, 0x84];   // :method GET, :scheme http, :path /
let mut input = block;
loop {
    match d.feed(input, true) {
        Feed::Field(used, never) => {
            println!("{:?}: {:?}", d.name(), d.value());
            input = &input[used..];
        }
        Feed::Final => break,                // the block ended cleanly
        Feed::More => break,                 // (only with fin == false)
        Feed::Bad => panic!("COMPRESSION_ERROR"),
    }
}
d.end_block();
```

`change_settings(n)` is SETTINGS_HEADER_TABLE_SIZE. Pass `fin = false`
while more of the block may come.

### From C, and from nghttp2

`--features nghttp2-abi` exports `vhpack_new`, `vhpack_feed`,
`vhpack_change_settings`, `vhpack_end_block`, `vhpack_free` and table
accessors (`src/capi.rs`).

`compat/nghttp2/patch.py NGHTTP2_LIB_DIR` makes an nghttp2 source tree use
verilith_hpack for its inflater when built with `-DNGHTTP2_VHPACK` and linked with
`libverilith_hpack.a`. It puts the nine `nghttp2_hd_inflate_*` functions under
`#ifndef NGHTTP2_VHPACK` and adds replacements that call verilith-hpack
(`nghttp2_hd_vhpack.inc`). Everything else in nghttp2, including the
deflater and the session code that calls the inflater, is unchanged.
Tested with nghttp2 1.70.0 (the version in Node.js v24.22.1 and v26.13.1).

### Node.js

`compat/node/node.sh NODE_DIR [VHTTP_DIR]` patches a Node.js checkout to
build with verilith-hpack in nghttp2 and, with a
[verilith-http](https://github.com/verilith/verilith/tree/main/crates/http) checkout, verilith-http in
place of llhttp (`node:http`) and of undici's `llhttp.wasm` (`fetch()`).
The Rust side is one static library (`compat/node`), since two Rust static
libraries cannot be linked into one binary. Then build Node as usual:

```sh
compat/node/node.sh ~/node ~/vhttp
cd ~/node && ./configure --ninja && ninja -C out/Release node
```

Node.js v26.13.1 built this way passes 7,245 of the 7,248 tests in its
default suite (`python3 tools/test.py default`), all 319 HTTP/2 tests
among them. The three failures fail the same way on the official v26.13.1
binary: `test-fs-rmSync-special-char-additional-error` fails on any build
run as root, and the two `test-tls-get-ca-certificates-worker-*` tests need
system certificates the sandbox lacks. (v24.22.1 passed 5557 of 5558.) (Run the suite with proxy
environment variables such as `HTTPS_PROXY` unset: `test/client-proxy`
reads them.) Parsers with llhttp's lenient flags set
(`--insecure-http-parser`) stay on llhttp's own generated parser; see
verilith-http's README.

## Testing beyond the proofs

- `tests/rfc.rs`: RFC 7541 Appendix C.2 to C.6, each fed whole, one byte at
  a time, in 3-byte pieces and in mixed pieces, with the dynamic table
  checked after each block.
- `tests/random.rs`: random header lists encoded with every representation,
  random size updates and random splits, decoded and compared with the
  encoder's model of the table; and random garbage, which must get the same
  verdict whole and byte by byte.
- `tests/encoder.rs`: the encoder against the decoder: 400 connections of
  random header lists (names and values from the static table, repeated
  ones, random bytes, sensitive fields), random SETTINGS_HEADER_TABLE_SIZE
  changes and encoder sizes, decoded whole and in random pieces; every
  block must decode to the fields given and leave both tables equal. Also
  every static table entry, which must be one byte.
- `tests/work.rs`: a block that resumes in the buffered path with `fin`
  set, which used to cost time quadratic in its length (each field copied
  the rest of the block; 40,000 one-byte fields took 16 ms instead of
  0.1 ms) and is now linear, as the work bound says.
- `compat/nghttp2/test/run.sh NGHTTP2_LIB_DIR [SEEDS] [CASES]`: a
  differential test of nghttp2 on verilith-hpack against stock nghttp2, both under
  ASan and UBSan. Each case deflates random header lists with nghttp2's own
  encoder, with random settings changes, random corruption and random
  splits, and checks that both inflaters emit the same fields and errors
  and end with the same dynamic table. 200 seeds of 500 cases (100,000
  cases) give identical output.

## Performance

### The decoder

`compat/nghttp2/test/bench.sh NGHTTP2_LIB_DIR [ROUNDS]` decodes
browser-like header blocks with stock nghttp2 and with nghttp2 on verilith-hpack.
On an Apple M3 Pro (macOS, nghttp2 1.70.0, 2000 rounds; five rounds, each
running both on a calm machine, median; not pinned to a core, so
differences under about 2% are noise):

| | nghttp2 1.70.0 | verilith-hpack | verilith-hpack / nghttp2 |
| --- | ---: | ---: | ---: |
| ns per block | 378.1 | 328.8 | 0.87 |
| MB/s decoded | 931 | 1070 | |

This is one synthetic workload (decoding the same blocks over and over),
not HTTP/2 as a whole.

What makes it fast:

- **Huffman:** a 4096-entry table gives the one or two codes each 12-bit
  prefix starts with (`huffman::dtab`), built once and proven
  (`dtab_ok`). The bits are kept at the top of a 64-bit word and an entry
  holds its codes' total length in its low bits, so each step is a load
  and two shifts. Both symbols of an entry are stored unconditionally into
  a buffer sized for the longest possible result (every code is at least 5
  bits), and the count of them taken. Codes longer than 12 bits fall back
  to a search over the canonical layout.
- **No copies of indexed fields:** a field taken from the table refers to
  the entry (`Decoder::name_ref`, `value_ref`) instead of copying it, and
  the nghttp2 shim hands out nghttp2's own static buffers for the static
  table and cached buffers for short dynamic table entries, which it
  names by insertion number (`Table::ins`).
- **No copies into the table:** an inserted field's buffers move into the
  new entry (`Table::insert_move`), taking buffers kept from evicted
  entries in exchange, so a full table allocates nothing.

### The encoder

`bench/run.sh` encodes the header blocks of whole connections with
verilith-hpack's encoder, h2 0.4.21's (hyper's HTTP/2 stack; its HPACK
module is private, so run.sh copies h2 and makes that one module public)
and nghttp2 1.70.0's deflater (curl, Apache, Node.js), each with a fresh
encoder per connection so the dynamic table does what it does in use. All
are built with `-C target-cpu=native` / `-O3 -march=native`. Each encoder's
output is decoded by verilith-hpack's decoder, and verilith-hpack's also by
nghttp2's, and checked against the fields. On a 4-core cloud VM (Intel
Xeon @ 2.1 GHz, Linux), best of five runs, ns per header block (bytes per
block):

| workload | verilith-hpack | nghttp2 1.70.0 | h2 0.4.21 |
| --- | ---: | ---: | ---: |
| static file responses, 100 per connection, 12 fields | **197** (37.2) | 256 (37.2) | 680 (37.2) |
| browser requests, 100 per connection, 16 fields | **356** (125.9) | 542 (125.9) | 1078 (125.9) |
| API responses, 100 per connection, 6 fields | **163** (36.0) | 512 (35.5) | 539 (35.5) |
| first response of a new connection | **751** (187) | 954 (187) | 844 (187) |
| first request of a new connection | **1278** (413) | 1712 (413) | 1319 (413) |

A cloud VM is noisy; instruction counts (callgrind, per block, same
workloads, built without `-march=native`) say the same and do not depend on
the machine: 4,186 / 7,539 / 3,370 / 17,072 / 29,116 for verilith-hpack,
4,751 / 10,137 / 7,624 / 20,142 / 35,842 for nghttp2, and 7,168 / 11,595 /
6,361 / 14,103 / 22,368 for h2. h2 runs fewer instructions on a new
connection because its table entries share the caller's reference-counted
buffers, where verilith-hpack copies a field into its table (two
allocations per entry; reused once the table is full).

What makes it fast:

- **Static table lookups** through a perfect hash of the names: one hash
  of three bytes, one compare.
- **Dynamic table lookups** through a hash index (two slots per key, both
  checked), hashing 8 bytes at a time, and a static name stands in for its
  hash; no scan of the table.
- **Huffman in one pass** for strings under 127 bytes (a placeholder
  length byte, as h2 does), 4 bytes written at a time; the plain string
  when Huffman is not shorter.

## Building and checking

```sh
cargo test --profile release-abort                 # tests
scripts/verify.sh                    # proofs (needs Verus's cargo-verus)
python3 tools/gen_tables.py NGHTTP2_DIR GO_NET_DIR src   # regenerate the tables
```

The proofs check with Verus at the `vstd` version pinned in `Cargo.toml`.
CI (`.github/workflows/ci.yml` at the repository root) verifies the proofs and runs `ci.sh` on every pull request and push to `main` that touches this crate or a crate it depends on.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/hpack/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/hpack/LICENSE-MIT), at your option.
