# verilith-h3

Sans-I/O HTTP/3 framing (RFC 9114), written in Rust and proven correct with
[Verus](https://github.com/verus-lang/verus): QUIC variable-length
integers, frames, unidirectional stream types, and the frame-order rules
of every stream, each with the error code the RFC gives.

This is the part of an HTTP/3 stack that reads bytes from a peer before
anything else does. It does no I/O and owns no connection state beyond
one stream: you give a `Reader` the bytes of one QUIC stream as they
arrive, in pieces of any size, and it hands back one event at a time.
QPACK (field section compression) is a separate layer; this crate hands
HEADERS and PUSH_PROMISE field sections to it as bytes.

## Usage

```rust
use verilith_h3::{Event, Reader, Src};

// A request stream at a server; HEADERS, PUSH_PROMISE and SETTINGS
// payloads over 64 KiB are H3_EXCESSIVE_LOAD.
let mut r = Reader::new_request(true, 1 << 16);
let bytes = [0x01, 0x02, 0xd1, 0xd7, 0x00, 0x03, b'a', b'b', b'c'];
let mut input: &[u8] = &bytes;
loop {
    let (event, used) = r.next(input, true); // `true`: these are the last bytes
    match event {
        Event::Headers(Src::Input(a, b)) => { /* QPACK-decode input[a..b] */ }
        Event::Headers(Src::Buf(off)) => { /* QPACK-decode r.buffered()[off..] */ }
        Event::Data(a, b) => { /* body bytes: input[a..b], not copied */ }
        Event::Need => break,          // used all of `input`; call again with more
        Event::End => break,           // the stream ended, well formed
        Event::Error(code) => { /* close with `code` (an H3_* error) */ break }
        _ => {}
    }
    input = &input[used..];
}
```

- `Reader::new_uni(server, limit)` reads a unidirectional stream: its type
  first (`Event::StreamType`), then for a control stream SETTINGS
  (`Event::Settings`) and the control frames, for a push stream its push
  ID (`Event::PushId`) and then a response. A QPACK encoder or decoder
  stream, or a stream of unknown type, reports its type and then
  `Event::Handoff`: the bytes after the type are not HTTP/3 frames, and
  are the caller's.
- DATA is never copied or buffered: `Event::Data(a, b)` points into the
  input, and a DATA frame split over several calls comes out as several
  `Data` events. HEADERS, PUSH_PROMISE and SETTINGS are delivered whole:
  from the input when the frame is all there (`Src::Input`), otherwise from
  the reader's buffer (`Src::Buf`), which holds at most `limit` bytes.
- `write_var`, `write_header`, `write_settings`, `write_id_frame` and
  `write_push_promise_head` encode frames into a `&mut [u8]` at an offset
  and return the end, or `None` (writing nothing) when a value is out of
  range or the frame does not fit. `header_size`, `settings_frame_size`
  and `var_size` give the sizes in advance.
- `uni_open`, `uni_closed` and `bidi_open` are the connection-level stream
  rules: one control stream and one of each QPACK stream per peer, none of
  them ever closed, and bidirectional streams opened only by clients.

## What is proven

`src/spec.rs` is the specification, as pure functions over byte
sequences. Its module comment lists each rule with its RFC section. In
short:

- varints (RFC 9000 §16);
- frame headers and the payload of each frame type (§7.1, §7.2);
- SETTINGS, including the reserved HTTP/2 identifiers and RFC 9220's and
  RFC 9297's boolean settings (§7.2.4);
- unidirectional stream types (§6.2, RFC 9204 §4.2);
- the frame order of control, request, response and push streams (§4.1,
  §6.2.1, §7.2): SETTINGS first and once, `HEADERS DATA* [HEADERS]`, HTTP/2's
  frame types refused everywhere, unknown types skipped;
- the ID rules: GOAWAY IDs never increase, and a server's are client
  bidirectional stream IDs; MAX_PUSH_ID never decreases and only goes to a
  server; a CANCEL_PUSH a server receives is within the MAX_PUSH_ID it
  received;
- how each kind of stream may end.

`spec::run` is the whole stream read by the spec: the events it yields,
the DATA it carries, and where it stopped (between frames, failed with a
code, or handed off). `spec::end_of` is what the stream's end means there.
The proofs show:

- **Every event is the spec's, however the stream is split**
  (`Reader::next`, `next_ok`). After each call, the events reported so far
  are exactly `run`'s events for the bytes given so far, and the DATA
  reported so far is exactly `run`'s DATA, including a frame that has
  only partly arrived. The reader reports `Error(c)` exactly when `run`
  fails with `c`, or the stream ends where `end_of` says it may not. It
  reports `End` exactly when `end_of` accepts the end. The theorem is
  stated against the concatenation of every piece ever given, not against
  the pieces. It rests on extension lemmas (`lemmas.rs`): once a frame or
  varint is read, more bytes after it change nothing.
- **Linear work, however the stream is split** (`Reader::next_metered`).
  Ghost state counts loop turns and bytes copied. The theorem is a
  potential argument:

  ```text
  steps(next(input)) + pot(after) <= pot(before) + 4 * used + 64
  ```

  `pot` is 2 per buffered byte: it starts at 0 and is never negative, so
  any sequence of calls costs at most 4 steps per byte consumed plus 64 per
  call. A frame buffered over many calls is copied once, not again on each
  call.
- **The encoders write the spec's encoding** (`encode.rs`), and it reads
  back. `frame_dec(frame_enc(f) ++ rest)` is `f` with its length, for
  every frame `f` that can be sent (`lemma_frame_rt`). Through the reader,
  an encoded frame is one unit that yields exactly `f`'s event
  (`lemma_unit_rt`), unless an ID rule refuses it. The varint encoder is
  the shortest encoding (RFC 9000 §16). The varint reader and writer are
  verilith-core's (`verilith_core::varint`, shared with verilith-quic);
  `varint.rs` proves they compute this crate's `var_dec` and `var_enc`
  (`lemma_var_core`, `lemma_enc_core`).
- No panics, overflows or out-of-bounds accesses, in all of the above. The
  public writers check their arguments and room at run time, so plain Rust
  callers cannot reach the unchecked `put_*` writers that verified callers
  use.

`tests/` runs hand-built streams through the reader whole, split at every
pair of points and byte by byte. It also runs 8,000 random streams of
written frames, fed in random pieces, and checks that each comes back as
written.

## Trusted computing base

- **The spec** (`spec.rs`). Read it against RFC 9114. These choices are
  ours, where the RFC leaves one:
  - A response or push stream that ends before its HEADERS is
    H3_MESSAGE_ERROR; the RFC names no code. A request stream that does is
    H3_REQUEST_INCOMPLETE (§4.1.2).
  - A repeated SETTINGS identifier is an error only for the settings
    understood here (§7.2.4 allows any repeat to be one).
  - Any varint length is accepted for any value; only QUIC's own frames
    must be minimal.
  - A CANCEL_PUSH, GOAWAY or MAX_PUSH_ID frame that is empty or longer
    than 8 bytes is refused as soon as its header arrives, since none can
    hold exactly one varint.
- **What is the caller's.** Rules that need more than one stream are not
  checked by a `Reader`. These are the caller's, and the spec's comments
  say so:
  - A client checks CANCEL_PUSH and PUSH_PROMISE push IDs against the
    MAX_PUSH_ID it sent, which is connection state.
  - A QPACK stream must not close: call `uni_closed` when one ends or is
    reset, as for a control stream.
  - The response to an interim (1xx) HEADERS needs QPACK to tell apart, so
    a response stream accepts any number of HEADERS before DATA (§4.1).
- **verilith-core's `prims`**, the unchecked slice accesses whose
  preconditions the proofs discharge, shared with every crate here. See
  the [trust ledger](../../TRUST-LEDGER.md).
- **Verus, Z3 and rustc**, as for every crate here.

The crate has no `assume`, `admit` or `external_body`.

## Performance

`bench/` is a separate Cargo project that compares `Reader` with
[hyperium/h3](https://github.com/hyperium/h3) 0.0.8's `Frame::decode`, the
frame decoder under h3's streams (built with its
`i-implement-a-third-party-backend-and-opt-into-breaking-changes` feature,
which makes it public). Each stream is held whole in memory. h3 reads from
`Bytes`, and its DATA payloads are handed out as `Bytes` slices; ours are
index ranges. `Reader` also checks the frame-order and ID rules, which
h3's decoder leaves to the layers above it, so h3's numbers are a lower
bound on what it spends doing the same job.

`bench/run.sh` runs each implementation in its own process, pinned to one
core, and gives the best of five runs; ns per stream, lower is better:

| stream | verilith-h3 | h3 0.0.8 |
| --- | ---: | ---: |
| request: HEADERS + 64 × 1 KiB DATA | 700 | 1,376 |
| request: HEADERS + 16 × 64 KiB DATA | 197 | 387 |
| request: HEADERS + 4,096 × 8-byte DATA | 44,800 | 62,046 |
| one 300-byte HEADERS frame | 21 | 29 |
| control: SETTINGS + 256 GOAWAY | 3,313 | 3,199 |

These were measured on a shared 4-core 2.1 GHz Xeon cloud VM with
`target-cpu=native`, where run-to-run noise is around 10 to 20%. The
request rows are where an HTTP/3 server spends its framing time.
Control-stream frames come a handful per connection, and there the two are
level.
