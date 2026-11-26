# verilith-h2

The HTTP/2 (RFC 9113) frame layer, written in Rust and proven correct with
[Verus](https://github.com/verus-lang/verus): a parser and a serializer for
the frame header and the ten frame types, sans I/O. It is the bottom of
verilith-server's HTTP/2 engine (see `crates/server/DESIGN.md`, "HTTP/2"),
and has no dependencies besides vstd.

```rust
use verilith_h2::{parse, serialize, Frame, Parsed};

let bytes = [0, 0, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0x10, 0];
match parse(&bytes, 16384) {
    Parsed::Frame(Frame::WindowUpdate { stream: 0, increment }, n) => {
        assert_eq!((increment, n), (4096, 13));
    }
    other => panic!("{other:?}"),
}
let mut out = Vec::new();
serialize(&Frame::WindowUpdate { stream: 0, increment: 4096 }, 16384, &mut out).unwrap();
assert_eq!(out, bytes);
```

`parse(buf, max)` reads the frame at the start of `buf` for a receiver whose
SETTINGS_MAX_FRAME_SIZE is `max`, and returns one of:

- `Frame(frame, len)`: payload fields borrow from `buf`; nothing is copied.
- `Incomplete(need)`: read until `buf` holds at least `need` bytes.
- `StreamError { stream, code, len }`: reset that stream, skip `len` bytes.
- `ConnError(code)`: send GOAWAY with `code` and close.

`serialize(frame, max, out)` appends a frame to a `Vec<u8>`, and fails,
leaving `out` unchanged, when the frame is not one a peer with that `max`
could read back as itself. `encode_head` gives the 9-byte header alone, for
a DATA frame written with `writev` from where its payload already is.

What a frame means for a stream (its state, flow control, whether a stream
may depend on itself, whether a server may receive PUSH_PROMISE) is the
connection layer's to decide, and is not done here.

## What is proven

`src/spec.rs` is the specification: the frame header (§4.1), the size limit
(§4.2), and each type's stream identifier, length, padding and flag rules
(§6.1 to §6.10), with the SETTINGS value rules of §6.5.2, RFC 8441 §3 and
RFC 9218 §2.1. Each rule names the error the RFC gives it and whether it is
a stream or connection error. The proofs show:

- **The parser is the spec** (`frame::parse`): its result is exactly
  `spec::parse` on the same bytes: the same frame with the same fields, the
  same error code and kind, or the same number of bytes needed. A frame
  longer than `max` is a FRAME_SIZE_ERROR as soon as its 9-byte header is
  in the buffer, so no more than `max + 9` bytes are ever buffered for one
  frame.
- **The serializer is the spec** (`frame::serialize`, `serialize_settings`,
  `encode_head`): it appends exactly `spec::serialize(frame)`, and succeeds
  exactly when `spec::wf(frame, max)` holds.
- **Round trip** (`lemmas::lemma_roundtrip`): for every well-formed frame
  `f` and any bytes `rest`,
  `parse(serialize(f) + rest, max) == Frame(f, serialize(f).len())`.
- **Everything parsed is well-formed** (`lemmas::lemma_parse_wf`): a frame
  `parse` returns satisfies `wf`, and took exactly `serialize(f).len()`
  bytes. With the round trip: re-sending what was received is read by the
  next hop as what was received, the property a proxy needs.
- **More input changes nothing once decided** (`lemmas::lemma_parse_prefix`):
  if `parse(b)` is not `Incomplete`, `parse(b + rest) == parse(b)`, so a
  caller may parse as soon as the frame is in, however reads are split.
- No panics, overflows or out-of-bounds accesses, in all of the above.

Where the RFC lets a receiver choose, the spec chooses, and says so in
`spec.rs`: padding bytes are not checked to be zero (§6.1 does not oblige
it); a frame too short for a mandatory field (PADDED with an empty payload,
PRIORITY with fewer than 5 bytes) is a FRAME_SIZE_ERROR, as §4.2 says, where
h2 and nghttp2 send PROTOCOL_ERROR; an oversized frame is always a
connection error (§4.2 allows a stream error for some types, but that would
mean reading past `max` bytes to skip it).

## Trusted computing base

- **The spec** (`spec.rs`), against RFC 9113. `tests/frames.rs` checks
  frames written by hand from the RFC's layouts and every error rule.
- **Verus, Z3 and rustc**, at the versions in `scripts/verus-version`.
- There is no `external_body`, `assume` or axiom in the crate.

## Tests

`cargo test` runs `tests/frames.rs`: each frame type and error rule by
hand; 20,000 generated well-formed frames serialized, then parsed with
trailing bytes and at every short prefix; 200,000 random frames parsed, and
each one accepted serialized and parsed again.

`bench/run.sh agree` is a differential check against h2 0.4.21 (its codec,
and its HEADERS and PUSH_PROMISE functions) and nghttp2 1.70.0 (its frame
decoders with the frame checks of its session): 300,000 mutated frames,
of which 252,400 were judged alike by all three. The differences, all of
them the other library's choice or a rule left to the connection layer:

| Frames | vh2 | h2 | nghttp2 | Why |
|---|---|---|---|---|
| RST_STREAM on stream 0 | PROTOCOL_ERROR | accepted by the codec | error | §6.4 requires the error; h2 checks later, in its stream layer |
| SETTINGS_NO_RFC7540_PRIORITIES above 1 | PROTOCOL_ERROR | accepted | error | RFC 9218 §2.1; h2 does not know the setting |
| PRIORITY or HEADERS depending on its own stream | accepted | stream error | accepted | §5.3.1's rule is about streams: verilith-h2's connection layer applies it |
| PUSH_PROMISE with an empty block fragment | accepted | MalformedMessage | accepted | an empty fragment is allowed (§6.6) |

## Performance

`bench/run.sh` runs verilith-h2 (vh2) against h2 0.4.21, the frame layer
hyper uses, and nghttp2 1.70.0 (curl, Node.js, Apache), on the same frames
in the same process, pinned to one core. Times are ns per frame, best of 31
rounds, on a 4-vCPU cloud VM (Intel Xeon, 2.1 GHz); the number after a time
is how much slower than vh2 it is.

| Case | vh2 | h2 functions | h2 codec | nghttp2 |
|---|---:|---:|---:|---:|
| parse control frames (14 B average) | 15.2 | 23.2 (1.5x) | 75.7 (5.0x) | 22.2 (1.5x) |
| parse HEADERS (52 B) | 7.4 | 52.3 (7.1x) | | 7.8 (1.05x) |
| parse DATA and control mix (1.5 KB) | 13.9 | | 133 (9.6x) | 14.0 (1.0x) |
| parse DATA 16 KB | 6.4 | | 641 (100x) | 5.6 to 6.2 (0.9x to 1.0x) |
| write frame header | 1.3 | 3.5 (2.7x) | | 3.2 (2.5x) |
| write control frames | 10.5 | 12.5 (1.2x) | | |
| write WINDOW_UPDATE | 3.4 | 3.9 (1.2x) | | |

What each column runs:

- **vh2**: `parse` in a loop over the buffer, borrowing the payloads.
- **h2 functions**: h2's own frame code (`Head::parse` and each type's
  `load`, through its `unstable` feature) on the payloads its codec splits
  off its read buffer, without HPACK.
- **h2 codec**: `h2::Codec`, h2's frame reader as a server uses it (length
  delimited framing into a `BytesMut`, then those functions), reading from
  memory. It copies every payload, which is the whole difference on DATA.
- **nghttp2**: `nghttp2_frame.c`'s decoders and encoders, with the frame
  checks of `nghttp2_session.c`'s inbound state machine repeated in
  `bench/ngwrap.c`. nghttp2's session does more per frame than this, so the
  column is a lower bound for nghttp2 itself.

The verified parser is as fast as nghttp2's C: a frame is a few compares
and a borrow, and the proofs added no work at run time (every check in the
code is one the RFC asks for). DATA at 16 KB is within the run-to-run noise
of this machine, where nghttp2 and vh2 trade places. These are cloud
numbers; a quiet machine will move them.
