# verilith-dns

A DNS message (RFC 1035) parser and serializer in Rust, formally verified with
[Verus](https://github.com/verus-lang/verus). It handles name compression,
the source of a long run of CVEs in C resolvers (pointer loops, out-of-bounds
pointers, unbounded name expansion; see RFC 9267). Its compressing
serializer is verified too: whatever it writes is proven to parse back to
the message it was given.

It is a drop-in for c-ares: with a 31-line patch, c-ares uses verilith-dns for
`ares_dns_parse`, `ares_expand_name` and `ares_dns_write`, and so for every
DNS message it reads or writes, and passes its own test suite (see
[cares/README.md](cares/README.md)).

It is also fast: parsing is allocation-free per label and per record, and in
the benchmarks below it is the fastest at every message size, for reading
and for writing, against c-ares, glibc's libresolv, hickory-proto, `domain`,
simple-dns and dns-parser, including the parsers that do less work by
leaving names compressed.

Every place where it reads an RFC strictly or loosely, or behaves
differently from c-ares, is listed in [DEPARTURES.md](DEPARTURES.md).

## Two speeds: drop-in and native

Swap verilith-dns in under c-ares today and get the proofs at no cost in speed;
call verilith-dns directly where message parsing is hot.

| | what you change | against c-ares |
| --- | --- | --- |
| **Drop-in** (c-ares with the patch) | apply the patch, rebuild | 1.25x (1.07x to 1.45x) |
| **Native** (`Message::parse_into`, `records`, `data`) | port the calling code | 14.43x (12.95x to 16.15x) |

The task is: parse a response, read every question and every record (owner
name, type, class, TTL and each RDATA field), free it, on four responses of
45 to 950 bytes.
Measured with [vbench](https://github.com/verilith/verilith/tree/main/bench) on an
Apple M3 Pro (2026-11-20, 31 alternating pairs per case; speedup is c-ares's
time over ours, geometric mean and range over the cases). Both columns run
the same task against the same c-ares driver. The native number is what you
get after porting the calling code; relinking alone gets the drop-in
number.

The gap is the API's shape, not the parser, which is the same code in both
rows. c-ares's API hands back a record tree that it allocates on every
parse and the caller frees, so the drop-in has to build that tree; the
native API parses into a `Message` the caller reuses, with no allocation
once its buffers are warm, and decodes a record's RDATA when it is read.
The two APIs also return names differently: verilith-dns in wire form, c-ares as
text.

## Usage

```rust
use verilith_dns::{parse, Message, Section};

let m = parse(&packet).ok_or("malformed")?;
// Or, to learn why a message was rejected:
// let m = verilith_dns::try_parse(&packet)?;   // Err says what, at which offset, in which record
for q in m.questions() {
    println!("{} type {}", q.name(), q.qtype);
}
for rr in m.answers() {
    println!("{} ttl {} rdata {:?}", rr.name(), rr.ttl, rr.rdata);
}

// Reuse one Message to parse without allocating once its buffers are warm.
let mut msg = Message::new(0, 0);
if msg.parse_into(&packet) { /* ... */ }

// Build and serialize. Invalid names or oversized fields are refused, so
// every Message is well-formed and its bytes always parse back to it.
let mut reply = Message::new(0x1234, 0x8180);
reply.push_question("example.com", 1, 1)?;
reply.push_record(Section::Answer, "example.com", 1, 1, 3600, &[93, 184, 216, 34])?;
let bytes = reply.to_bytes_compressed(); // or to_bytes(), uncompressed
```

### From C

The same API from C or C++, through `include/vdns.h`: build with
`cargo build --release --features capi` and link `target/release/libverilith_dns.a`
(`-lpthread -ldl`). Use it when you can change the calling code; use the
c-ares drop-in (`cares/`) when you cannot.

```c
vdns_message *m = vdns_message_new();          /* reusable; keeps its buffers */
if (vdns_parse(m, packet, len, NULL) == VDNS_OK) {
    vdns_record r;
    char name[1024];
    for (size_t i = 0; vdns_get_record(m, VDNS_ANSWER, i, &r); i++) {
        vdns_name_text(r.name, r.name_len, name, sizeof name);
        /* r.rtype, r.ttl, r.rdata, r.rdata_len */
    }
}
vdns_message_free(m);
```

Reading a question or a record allocates nothing and copies nothing: names
and RDATA are pointers into the message, valid until it is parsed into
again or freed. Names are in uncompressed wire form, and so are the names
inside RDATA, so each RDATA decodes on its own. `vdns_parse` takes an
optional `vdns_error` that says what was wrong, at which offset, in which
record. `vdns_write_query` writes a one-question query.

### Without std

verilith-dns builds as `no_std` with only `alloc`, for embedded resolvers (Zephyr,
lwIP, bare-metal c-ares), where several of the CVEs in [CVES.md](CVES.md)
were found:

```toml
verilith-dns = { version = "0.1", default-features = false }
```

The verified code is the same in both builds; only imports differ (`alloc`
and `core` in place of `std`), and [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core)
picks its checksum kernels from the target's compile-time CPU features
instead of detecting them at run time. `Error` implements
`core::error::Error`.

The static library (the c-ares drop-in) builds for bare metal too:

```sh
cargo build --release --no-default-features --features cares,ares-abi \
    --target thumbv7em-none-eabihf
```

Without std it brings its own panic handler, which calls the C library's
`abort()` (the verified parser and serializer cannot panic; this covers the
adapters), and a global allocator over c-ares's `ares_malloc`,
`ares_realloc` and `ares_free`, so `ares_library_init_mem` hooks apply to
verilith-dns's memory as well. Use `panic = "abort"`. On a hosted target such as
`x86_64-unknown-linux-gnu`, the precompiled `alloc` still refers to
`rust_eh_personality`, which the C program then has to define (an empty
function will do, since nothing unwinds); bare-metal targets don't need it.

One limit: because `Cargo.toml` lists `staticlib` among the crate types,
Cargo also builds the static library when verilith-dns is a dependency, and without
std that needs the `cares` feature for the runtime above. A Rust `no_std`
program that has its own allocator and panic handler can depend on verilith-dns
once the static library moves to `cargo rustc --crate-type staticlib` in
the c-ares build (not done here, since CI builds it).

Checked: `cargo build --no-default-features --features cares,ares-abi`
for `thumbv7em-none-eabihf` (Cortex-M4F), and the same build for x86-64
linked into a C program that calls `ares_expand_name` with every
allocation counted through `ares_malloc`.

## What is proven

Everything below is checked by Verus (`cargo verus verify`: 355 items, 0 errors).

| Property | Where |
| --- | --- |
| **No panics, no out-of-bounds reads, no integer overflow** in the parser, accessors, builder and serializer (Verus checks every index and every arithmetic op) | `src/parse.rs`, `src/message.rs` |
| **Termination on every input**, including pointer loops. Compression pointers must target an offset strictly before the start of the current label run, so the run start strictly decreases on each jump | `spec::parse_labels`, `parse::read_name_into` |
| **Bounded output**: a decoded name never exceeds 255 wire octets, however it is assembled from pointers | `parse::read_name_into` |
| **No pointer is followed twice** (RFC 9267 §2): the locations of the pointers followed are pairwise distinct | loop invariant of `parse::read_name_into` |
| **Bounded work per name**: pointers never outnumber labels, so decoding one name takes at most 256 loop steps and copies at most 255 bytes | loop invariant of `parse::read_name_into` |
| **Up-front count check is sound** (RFC 9267 §6): rejecting counts that cannot fit the message never rejects a message the spec accepts | `lemmas::lemma_counts_fit` |
| **Functional correctness of parsing**: `parse` and `Message::parse_into` compute exactly `spec::parse_message` | `src/parse.rs` |
| **Every `Message` is well-formed** (type invariant): its arena and entry table encode a `SpecMessage` satisfying `valid_message`. Parsing establishes it; every builder call preserves it or is refused and leaves the message unchanged | `Message::inv`, `src/message.rs` |
| **Accessors are exact**: `question(i)`, `record(s, i)` return exactly the spec message's fields | `src/message.rs` |
| **Serialization**: `to_bytes` produces exactly `ser_message`, and its output always parses back to the same message | `Message::to_bytes` |
| **Compressing serialization**: `to_bytes_compressed` always parses back to the same message. Names are compressed against every earlier name and suffix (owner and question names, and names in NS, CNAME, SOA, PTR and MX RDATA, as RFC 3597 §4 allows), pointers only target offsets up to 0x3FFF, and each RDLENGTH is computed before its RDATA is written | `Message::to_bytes_compressed`, `src/compress.rs` |
| **Round trip**: `parse_message(ser_message(m)) == Some(m)` for every well-formed `m` | `lemmas::theorem_roundtrip` |
| **Parsed messages are well-formed** | `lemmas::theorem_parse_valid` |
| **Canonicalization**: parsing, re-serializing (uncompressed) and parsing again gives the same message | `lemmas::theorem_reserialize_stable` |
| **Typed RDATA**: `read_rdata` computes exactly `spec_rdata::parse_rdata` for A, AAAA, NS, CNAME, PTR, MX, TXT, HINFO, SOA, SIG, SRV, NAPTR, OPT, DS, SSHFP, RRSIG, NSEC, DNSKEY, NSEC3, NSEC3PARAM, TLSA, SVCB, HTTPS, URI and CAA, which is every type c-ares decodes (raw bytes for other types), each consuming its RDATA exactly; names inside RDATA are decompressed under the same rules as owner names | `src/rdata.rs` |
| **Canonical RDATA**: a parsed record stores its RDATA with every name inside it decompressed (NS, CNAME, SOA, PTR, MX, SIG, SRV, NAPTR), and **it means what it meant in the message**: decoded on its own, it gives exactly the typed RDATA the original bytes give in the context of the whole message. Canonical RDATA is position-independent, so it keeps that meaning wherever it is written, and a re-serialized message says what the received one said | `lemmas_rdata::theorem_rdata_meaning`, `lemmas_rdata::lemma_canon_rdata_moves` |
| **Typed RDATA is context-free**: `record.data()` decodes `record.rdata` alone | `RecordRef::data` |
| **Encoding round trip for every typed RDATA**: `encode_rdata` lays out the fields of each of the 25 typed RDATA formats, and the bytes it writes decode (`parse_rdata`) to exactly the fields it was given and are already canonical, so the record is stored as written. The c-ares writer goes through it, so a record verilith-dns writes for c-ares means what c-ares's record says. Fields that do not fit their format (a string over 255 octets, an option over 65535, SVCB keys not strictly increasing, a CAA tag that is not 1 to 15 letters and digits, an empty URI target) are refused | `encode::theorem_rdata_encode`, `encode::encode_rdata` |
| **TXT splitting, header and OPT bits**: strings longer than 255 octets are written as 255-octet pieces in order (`txt_split`); the header word puts QR, Opcode, AA, TC, RD, RA, AD, CD and RCODE where RFC 1035 §4.1.1 and RFC 4035 §3.2 say; the OPT TTL holds the extended RCODE, version and flags as RFC 6891 §6.1.3 says | `encode::split_txt`, `encode::header_flags`, `encode::opt_ttl` |
| **Presentation format**: printing computes exactly `spec_text::pres_name` (c-ares's escaping), parsing computes exactly `spec_text::parse_text_name`, and parsing a printed name gives the name back, so no two names print the same | `text::theorem_text_roundtrip`, `text::theorem_text_injective` |

`serialize(parse(b)) == b` does not hold and cannot: compression makes the
format malleable (many byte strings decode to the same message). The
canonicalization theorem is the strongest round trip available.

## Trusted computing base

- The specs in `src/spec.rs`, `src/spec_rdata.rs` and `src/spec_text.rs`:
  read them to check they say what RFC 1035, RFC 9267 and the RDATA RFCs
  say, with `parse_u16`/`parse_u32` and `is_digit` from
  [verilith-core](https://github.com/verilith/verilith/tree/main/crates/core) (`verilith_core::bytes`,
  `verilith_core::num`).
- Verus, Z3 and the Rust compiler.
- vstd's `external_body` specs for `slice_subrange` and `Vec`.
- Unverified, and never handed untrusted bytes except through the verified
  code: `src/name.rs` (the `Name` view and iterators, written with checked
  slicing only; presentation format delegates to the verified `text`
  module), `src/capi.rs` (the `ares_expand_name` adapter: pointer checks
  and allocation) and `src/cares.rs` (the `ares_dns_parse` adapter, which
  copies already-decoded fields into c-ares's records and applies c-ares's
  extra policies, and the `ares_dns_write` adapter, which reads c-ares's
  records with its getters into `Rdata` and hands them to the verified
  encoder, builder and serializer). For writing, what the adapter decides
  is which getter goes into which field, and c-ares's policies (hostname
  characters, non-empty trailing fields, SERVFAIL for an extended RCODE
  without OPT); the byte layout of every field is verified. The sort of
  SVCB parameters by key is `std`'s; the encoder checks the result.
- `src/native.rs` (feature `capi`, 213 lines of code for 11 functions),
  the native C API, is unverified in the same way: pointer checks, a call
  to the `Message` method of the same name, and the copying of the result
  into the caller's struct. It reads no wire bytes itself. `tests/capi.rs`
  checks every result against the Rust API on 18,000 random, truncated and
  corrupted packets, and `tests/c/native.c` runs under ASan and UBSan
  (`scripts/test-c.sh`).

## Design choices

- **Arena layout.** A `Message` holds one byte arena that starts with a
  copy of the input (RDATA without names is a span into it, copied by a
  single `memcpy` for the whole message) followed by every name, and the
  RDATA of every record with names in it, in uncompressed wire form, plus one table of fixed-size entries (questions, then each
  record section) pointing into it. Parsing
  therefore allocates twice per message, never per label or per record, and
  `parse_into` reuses both buffers. Each run of contiguous labels is copied
  with one `memcpy`, and a record whose owner name is just a pointer to the
  first question's name (the usual shape of an answer) shares that name's
  span instead of decoding and copying it again; the proof covers the
  shortcut like any other path. The same goes for the target of the last
  owner name that was a single pointer, so authority records that all point
  at the zone apex decode it once. Names come back as `&[u8]` wire form
  (wrapped by `Name` for labels and display), so comparing and hashing them
  costs nothing extra. (Pointing uncompressed names into the input copy as
  well was tried and measured ~13% slower: finding where a name ends costs
  more than copying it.)

- **Drop-in target: c-ares.** `capi::vdns_expand_name`,
  `cares::vdns_ares_dns_parse` and `cares::dns_write` (feature `cares`)
  implement `ares_expand_name`, `ares_dns_parse` and `ares_dns_write_buf`
  (behind `ares_dns_write` and the TCP writer); the `ares-abi` feature exports
  them under c-ares's names. The adapters build and read c-ares's own
  `ares_dns_record_t` with c-ares's public setters and getters, so
  everything around the wire format (sockets, retries, cache, the query API)
  is unchanged c-ares. verilith-dns does not need its own connection code to be a
  drop-in, and does not replace c-ares's. The Rust API is designed on its
  own terms.
- **Compression on output** uses a dictionary of every name and suffix
  already written, keyed by exact bytes, so the case of every name survives
  (DNS 0x20), and indexed by a small hash of each suffix. The proof never
  relies on the index: it constrains only the match that is chosen, so a
  lookup that misses just costs some compression. Each name is planned before it is written, so a record's
  RDLENGTH is known up front and nothing is patched afterwards. The proof
  works on the bytes written so far: decoding a name, record or section
  only reads bytes before the current end, so appending never changes what
  is already there. On the benchmark messages the output is as small as
  hickory-proto's and as the input; c-ares's writer produces 289 bytes for
  the 278-byte message and 1,226 for the 948-byte one.
- **RFC 9267 compliance.** RFC 9267 ("Common Implementation Anti-Patterns
  Related to DNS RR Processing") lists the parsing rules whose violation
  caused the compression CVEs. Each is enforced, and the checklist is below.
- **Pointer rule** matches c-ares and BIND: a pointer must point strictly
  before the start of the current run of labels (RFC 1035 §4.1.4, "prior
  occurrence"). This is stricter than RFC 9267 §2's "before the pointer".
  In addition, a pointer must land on a label length octet (RFC 9267 §2),
  so a pointer to another pointer is rejected (c-ares accepts up to 128 in
  a chain). A pointer to a root octet is a pointer to a zero-length label
  and is accepted, as c-ares and BIND do.
- **Name length limit**: RFC 1035's 255 wire octets, including names
  assembled from pointers (RFC 9267 §3). c-ares instead caps the
  *presentation* length at 255 (up to 257 wire octets; see PR
  [#1164](https://github.com/c-ares/c-ares/pull/1164)), so it accepts a
  sliver of over-long names we reject.
- **Names inside RDATA are decompressed while parsing.** RDATA that holds
  names (NS, CNAME, SOA, PTR, MX, SIG, SRV, NAPTR) may point into the rest
  of the message, so copying its bytes into another message silently
  changes the names (a pointer to offset 12 means whatever is at offset 12
  there). verilith-dns stores such RDATA in canonical form, with every name
  uncompressed, and rejects the message if the RDATA does not decode
  (RFC 9267 §5). The cost is decoding those names up front (about 25 ns
  each); the benefit is that a record means the same thing however it is
  copied, forwarded, cached or re-serialized, and this is proven, not just
  tested. The builder applies the same rule: `add_record` resolves names
  in the given RDATA against the RDATA alone, stores them uncompressed, and
  refuses RDATA that does not decode (`BuildError::BadRdata`).
- **Typed RDATA** is decoded on demand (`record.data()`), so a caller that
  only needs addresses pays nothing for the rest. Character-strings are
  bytes, as the RFCs define them; c-ares additionally insists that some are
  printable ASCII (see the differential test below), which the c-ares
  adapter applies.
- **Counts must match the data** (RFC 9267 §6): trailing bytes after the
  last record are rejected, and counts that cannot fit the message are
  rejected before any decoding. (The c-ares adapter ignores trailing bytes,
  as c-ares does, by parsing only the message they follow.)
- **No separate jump cap.** c-ares caps pointer jumps at 128 per name
  (PR [#1164](https://github.com/c-ares/c-ares/pull/1164)). Here that bound
  falls out of the rules above and is proven: a pointer never lands on
  another pointer, so pointers never outnumber labels by more than one, and
  a name takes at most 256 steps.
- **No dependency on Vest.** Vest
  ([secure-foundations/vest](https://github.com/secure-foundations/vest)) is
  the closest prior work, but its design notes list "non-linear parsing
  (pointer-chasing)" as unsupported and name DNS compression as an example of
  a malleable format. Compression is the core of this crate, so it is
  hand-written against vstd. Vest combinators could later describe the
  fixed-layout parts (header, RR fixed fields, typed RDATA).

## RFC 9267 checklist

| RFC 9267 rule | How it is met |
| --- | --- |
| §2 pointer target within the message and before the pointer | spec `parse_labels`: target < start of current label run |
| §2 a pointer lands on a label length octet, not another pointer | checked for every pointer (a root octet counts as a zero-length label) |
| §2 nested pointers (to a compressed name) "should be discouraged" | allowed, as every mainstream compressor emits them; they still must land on a label |
| §2 a pointer is not followed more than once | proven (pointer locations distinct) |
| §3 label length 1..=63 and matches the bytes present | spec `parse_labels` |
| §3 name at most 255 octets including decompressed parts; root octet within the limit | spec `parse_name` (limit counts the root octet) |
| §4 do not rely on NUL-terminated input | the parser works on length-delimited slices only |
| §5 RDLENGTH matches the bytes available | spec `parse_record` |
| §5 RDATA conforms to TYPE | spec `parse_rdata`: each type's RDATA must decode and be consumed exactly (raw for unknown types, RFC 3597); for types with names this is checked while parsing, so a message with malformed name-bearing RDATA is dropped |
| §6 counts checked before parsing and must match the data | up-front size check, exact parse, trailing bytes rejected |
| §1, §6 drop malformed replies | every violation makes `parse` return `None` |

## Performance

From the benchmark harness (`bench/`), in ns per message, lower is better.
Each row ran on its own in three separate processes (`dnsbench ROW`), each
taking the best of 30 sustained runs of 20k iterations after a warm-up; the
table gives the best of the three. Every library is built with
optimizations: Rust with `lto = "fat"`, c-ares 4c60465 with CMake's Release
flags (`-O3`), glibc 2.39's libresolv as shipped.

| What is measured | small (45 B, 2 entries) | typical (278 B, 14) | large (948 B, 57) |
| --- | --- | --- | --- |
| **Reading, names decoded** | | | |
| verilith-dns `parse` (every name decoded, including names in RDATA; other RDATA kept as bytes) | **66** | **303** | **971** |
| verilith-dns `parse_into` (buffers reused) | **36** | **269** | **909** |
| `domain` 0.12: walk every record, copy each owner name | 77 | 632 | 2337 |
| glibc `ns_parserr` on every record + `dn_expand` of each owner name | 90 | 1007 | 3452 |
| **Reading, names left compressed** (less work than verilith-dns `parse`) | | | |
| dns-parser 0.8 `Packet::parse` | 78 | 525 | 1901 |
| glibc `ns_initparse` + `ns_parserr` on every record | 87 | 771 | 2768 |
| **Reading, typed RDATA** | | | |
| verilith-dns `parse` + `data()` on every record | **86** | **428** | **1399** |
| simple-dns 0.12 `Packet::parse` | 230 | 1756 | 6964 |
| hickory-proto 0.26 `Message::from_vec` | 247 | 1923 | 6894 |
| **Reading into c-ares's record** | | | |
| vdns-backed `ares_dns_parse` | **469** | **3115** | **11721** |
| c-ares `ares_dns_parse` (builds the same record) | 705 | 6565 | 25005 |
| **Writing, compressed** (the parsed message back to wire form) | | | |
| verilith-dns `to_bytes_compressed` | **66** | **647** | **1983** |
| simple-dns 0.12 `build_bytes_vec_compressed` | 85 | 1278 | 3073 |
| hickory-proto 0.26 `Message::to_vec` | 306 | 3087 | 9907 |
| vdns-backed `ares_dns_write` (from c-ares's record) | **479** | **5732** | **19910** |
| c-ares `ares_dns_write` (from the same record) | 910 | 7240 | 24518 |
| **Writing, uncompressed** | | | |
| verilith-dns `to_bytes` | 36 | 204 | 635 |

verilith-dns is the fastest in every group at every size. Its full parse, which
decodes every name, beats the parsers that leave names compressed by 1.2 to
2.9 times, and those that decode them by 1.2 to 3.6 times; with typed RDATA
it is 2.7 to 5 times faster than simple-dns and hickory-proto. Its
compressing serializer is 1.3 to 2 times faster than simple-dns's and 4.6 to
5 times faster than hickory-proto's, and all three write the same number of
bytes for every message (c-ares writes 1,226 for the large one, against
948). In the c-ares rows, which produce or consume identical c-ares
records, most of the time goes to c-ares's own record allocation and
getters, which the vdns-backed versions also use; even so, reading is 1.5
to 2.1 times faster than c-ares's parser and writing 1.2 to 1.9 times
faster than its writer.

Run it with `CARES_LIB_DIR=/path/to/c-ares/build/lib cargo run --release`
in `bench/`, with c-ares built with `-DCMAKE_BUILD_TYPE=Release` (see
`bench/src/main.rs` for the messages and the exact work per row). The
numbers come from one machine and have not been reproduced independently.

## Recent CVEs

[CVES.md](CVES.md) maps eight DNS parsing CVEs (dnspython, Net::DNS, c-ares,
Zephyr, dnsmasq, BIND) to the proven property that rules out each bug class,
and `tests/cves.rs` reproduces each attack packet's shape.

## Testing

```sh
cargo test --release
```

Unit tests cover a real compressed response, pointer loops, forward pointers,
pointers to the root octet (accepted) or another pointer (rejected), reserved label types, the
255-octet limit across pointers, trailing bytes, impossible counts, and the
slow pointer-chain packet from c-ares PR #1164 (rejected in microseconds),
the builder's refusals, and presentation-format conversion. Randomized tests
build messages with sections added in random order, check the round trip
through both the verified serializer and a separate compressing encoder (and
through `parse_into`), and run ~200k random and mutated packets through both
parsers.

The differential test compares `ares_expand_name` from a real c-ares build
against ours at every offset of random, mutated and label/pointer-soup
buffers:

```sh
cmake -S c-ares -B c-ares/build -DCARES_STATIC=ON -DCARES_SHARED=OFF \
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON && make -C c-ares/build
CARES_LIB_DIR=$PWD/c-ares/build/lib cargo test --release --test differential -- --nocapture
```

Against c-ares 4c60465: 12.8M name decodes. All agree on status, string and
consumed length except two expected kinds, and the test fails on anything
else: 52 names of 256 or 257 wire octets, and 160 names that follow a
pointer to another pointer. Both are names c-ares accepts and RFC 1035 /
RFC 9267 forbid.

The typed RDATA differential test runs 300k random and mutated messages
through `ares_dns_parse` and `record.data()`:

```sh
CARES_LIB_DIR=$PWD/c-ares/build/lib cargo test --release --test differential_rdata -- --nocapture
```

Whenever both accept a message, every typed field matches, except that
c-ares keeps only one EDNS option per option code. Every other disagreement
is classified, and the test fails on any it cannot explain. c-ares is
looser than the RFCs in a few places (it ignores trailing bytes inside
RDATA, does not check CAA tags or SVCB key order, and follows pointers to
pointers), and stricter in others (it rejects classes other than IN, CH,
HS and NONE, non-printable HINFO, NAPTR and URI strings, empty CAA values,
TLSA data and DNSSEC signatures, digests, keys and bit maps).

The c-ares adapter test runs 200k random and mutated messages, with four
`ARES_DNS_PARSE_*_RAW` flag settings each, through the vdns-backed
`ares_dns_parse` and c-ares's own, and writes both resulting records back
with `ares_dns_write`:

```sh
CARES_LIB_DIR=$PWD/c-ares/build/lib cargo test --release --features cares --test cares_abi -- --nocapture
```

Of 800,000 parses, 790,086 (98.8%) give the same status and byte-identical
records. verilith-dns never accepts a message c-ares rejects; the rest are messages
only c-ares accepts, each classified. 8,881 of them are messages with
malformed name-bearing RDATA that c-ares keeps as raw bytes when a caller
sets an `ARES_DNS_PARSE_*_RAW` flag (verilith-dns drops them, RFC 9267 §5; c-ares
itself never sets these flags when it resolves); the other 853 are the RFC
looseness cases above. c-ares's own test suite passes on the patched c-ares except for one
test that expects an RFC violation to be accepted
([cares/README.md](cares/README.md)).

The same test file checks the vdns-backed `ares_dns_write` against
c-ares's own on every record c-ares's parser builds from 100k random and
mutated messages, with and without the raw flags: 141,236 records. Whenever
both writers succeed, c-ares reads the two outputs as the same record,
except for 68 SVCB and HTTPS records whose keys verilith-dns writes in increasing
order (RFC 9460 §2.2). verilith-dns refuses 29,440 records that c-ares writes, all
raw RDATA from a raw-flag parse: 27,860 hold compression pointers into the
message they came from, which c-ares copies into the new message, where
they point at whatever is there, and 1,580 do not decode as their type.
c-ares refuses one record that verilith-dns writes, a name whose escaped text is
over 255 characters, which c-ares's own parser had produced. The test fails
on any other difference.

## Fuzzing

`fuzz/` has four cargo-fuzz targets. They exist for the code the proofs do
not cover: the c-ares adapter (`src/cares.rs`) and the C ABI
(`src/capi.rs`), run against an AddressSanitizer build of c-ares.

| Target | What it checks |
| --- | --- |
| `parse` | Every accessor, typed RDATA, presentation format, re-serialization and `parse_into` on arbitrary input |
| `expand_name` | `ares_expand_name` (verilith-dns's) at every offset, freeing each result with c-ares's allocator |
| `ares_dns_parse` | The vdns-backed `ares_dns_parse` with input-chosen flags; whenever verilith-dns accepts, `ares_dns_write` of its record must equal that of c-ares's own parser |
| `ares_dns_write` | The vdns-backed `ares_dns_write` on records c-ares's parser builds, with input-chosen flags and TTL decrement; its output must parse, and c-ares must read it as the same record as c-ares's own output |

```sh
cmake -S c-ares -B c-ares/build-asan -DCARES_STATIC=ON -DCARES_SHARED=OFF \
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DCMAKE_C_FLAGS=-fsanitize=address
cmake --build c-ares/build-asan
cd fuzz && CARES_LIB_DIR=$PWD/../c-ares/build-asan/lib \
  cargo +nightly fuzz run -s address ares_dns_parse corpus/ares_dns_parse seeds
```

Seeded with c-ares's own fuzz inputs, ten minutes per target ran 19.0M,
0.8M and 9.6M inputs with no crash, leak, sanitizer report or mismatch, and
five minutes of `ares_dns_write` ran 19.5M.

## Continuous integration

CI is the workflow at the repository root, `.github/workflows/ci.yml`. On
every pull request and push to `main` that touches this crate or
verilith-core, it runs:

- **verify**: checks every proof with the Verus build pinned in
  `scripts/verus-version` (built from source and cached), through Buck2;
- **test**: `ci.sh`, which builds c-ares at the pinned commit, runs all
  tests including the c-ares differentials and the native C API's
  (`scripts/test-c.sh`), then applies the patch and runs c-ares's own test
  suite on top of verilith-dns.

A manual run of the workflow with "fuzz" also runs `ci.sh fuzz`: five
minutes per fuzz target under AddressSanitizer.

## Verifying

Install Verus at commit `8bf68ee` (release 0.2026.11.02.8bf68ee; Rust
1.99.1), then:

```sh
cargo verus verify
```

## Next steps

1. Report the c-ares behaviours found here upstream: raw RDATA written with
   stale compression pointers, SVCB keys written out of order, and names
   that c-ares parses but will not write.

## License

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

The fuzz seeds in `fuzz/seeds` and the patch in `cares/` come from
c-ares, under its MIT license in [LICENSE-c-ares](LICENSE-c-ares).
