# verilith-quic

The QUIC version 1 (RFC 9000) wire format and transport state machines,
written in Rust and proven correct with
[Verus](https://github.com/verus-lang/verus): packet headers, packet
numbers, all twenty frame types, transport parameters, flow control,
stream IDs and stream states, the anti-amplification limit, and loss
recovery and congestion control (RFC 9002). It is
sans-I/O and borrows from the caller's buffers: parsing allocates nothing.

It is the part of a QUIC stack that reads bytes from the network and
decides what to send. The TLS 1.3 handshake for QUIC (RFC 9001) is in
`verilith-tls` (`verilith_tls::quic`); packet protection and the
connection itself are not here yet, and in Verilith's HTTP/3 server they
stay in quinn-proto, trusted.

## What is proven

`src/spec.rs` is the specification, written from RFC 9000 as pure
functions: a parser for each structure, from the whole input and a
position, and an encoder that always chooses the shortest integers. The
proofs show, with no panics and no unproven arithmetic anywhere:

- **Variable-length integers** (§16, `varint`): `read` is `spec::varint`,
  `write` is `spec::varint_enc`, and every value below `2^62` reads back.
  The code and these specs are verilith-core's (`verilith_core::varint`),
  shared with verilith-h3.
- **Frames** (§12.4, §19, `frame`): `parse` is `spec::frame` for all
  twenty frame types, and `encode` is `spec::frame_enc`. The round trip
  (`lemmas::lemma_frame_roundtrip`): the encoding of every valid frame,
  at any position and followed by anything that may follow it, parses back
  to the same frame and ends where the encoding ends. The checks the RFC
  makes connection errors are part of the spec: ACK ranges that would make
  a packet number negative, a STREAM or CRYPTO frame past `2^62 - 1`,
  MAX_STREAMS and STREAMS_BLOCKED above `2^60`, an empty NEW_TOKEN, a
  NEW_CONNECTION_ID whose Retire Prior To exceeds its sequence number or
  whose connection ID is not 1 to 20 bytes, and a frame type not in its
  shortest encoding. ACK ranges are checked when the frame is parsed and
  read lazily, as packet numbers, with `Ack::ranges`.
- **Packet headers** (§17, `packet`): `parse_header` is `spec::header`:
  Initial, 0-RTT, Handshake, Retry, Version Negotiation, other versions'
  invariant fields (RFC 8999) and 1-RTT, as they are before header
  protection is removed, with the fixed bit, connection ID lengths and the
  Length field checked against the datagram. `packet_end` finds where each
  of a datagram's coalesced packets ends (§12.2). `encode_header` is
  `spec::header_enc`, and every valid header reads back
  (`lemmas::lemma_header_roundtrip`).
- **Packet numbers** (§17.1, Appendix A): `decode_pn` is Appendix A.3,
  and the theorem `lemmas::lemma_decode_pn` says it recovers every packet
  number within half a window of the one expected. With `pn_len`
  (Appendix A.2), `lemmas::lemma_pn_roundtrip`: a packet number encoded
  with the length the sender chose is recovered by any receiver whose
  largest received packet is at or past the sender's largest acknowledged.
- **Transport parameters** (§18, `params`): `parse` is
  `spec::transport_params` (all of RFC 9000's and RFC 9221's
  max_datagram_frame_size; duplicates and invalid values rejected, unknown
  ones ignored), `encode` is `spec::transport_params_enc`, and valid
  parameters read back (`lemmas::lemma_transport_params_roundtrip`).
  `client_ok` checks a client sent none of the server-only parameters.
- **Flow control** (§4.1, `flow`): a `RecvCredit` never lets the peer's
  usage exceed what was advertised, and reports FLOW_CONTROL_ERROR
  otherwise; a `SendCredit` never spends past the peer's limit and
  ignores limits that would decrease.
- **Streams** (§2.1, §3, §4.5, §4.6, `streams`): the sending and receiving
  states move only along the arrows of RFC 9000's Figures 2 and 3
  (`send_step`, `recv_step`). A stream's final size never changes once
  known, no data is accepted past it (FINAL_SIZE_ERROR), and every byte
  offset is counted against both the stream's and the connection's limit,
  so the connection's count is always the sum of its streams' (each call
  changes both by the same amount). A sender's RESET_STREAM carries exactly
  the bytes it sent. `StreamIds` rejects frames for streams in the wrong
  direction or not yet opened (STREAM_STATE_ERROR) and beyond the limit
  advertised (STREAM_LIMIT_ERROR), and the peer never has more streams
  open than allowed.
- **Anti-amplification** (§8.1, `amplification`): `Budget`'s invariant is
  the RFC's sentence: before the address is validated, the bytes sent are
  at most three times the bytes received, after any sequence of calls.

Loss recovery (RFC 9002), for one packet number space each:

- **Sent packets** (§2, §6, `sent`): `Sent` keeps every packet sent and
  not yet acknowledged or declared lost, and its count of bytes in flight
  is always exactly the sum over in-flight packets still outstanding.
  `on_ack` rejects an ACK of a packet number never sent
  (PROTOCOL_VIOLATION) and otherwise moves exactly the packets in the
  ACK's ranges that were outstanding to acknowledged, each once, reporting
  the largest newly acknowledged for the RTT sample (§5.1).
  `detect_lost` declares lost exactly the outstanding packets sent before
  the largest acknowledged with three or more acknowledged packets after
  them (kPacketThreshold) or sent more than the loss delay ago (§6.1), and
  returns the earliest time another would be (the loss timer, §6.1.2).
  It reports persistent congestion only for two ack-eliciting packets lost
  in that call, sent at least the given duration apart, with no packet
  between them acknowledged (§7.6.2).
- **RTT** (§5, `rtt`): `Rtt::update` computes `spec::rtt_next`, RFC
  9002's smoothed_rtt, rttvar and min_rtt over whole microseconds, with
  the ACK delay capped at max_ack_delay once the handshake is confirmed
  and never subtracted below min_rtt; `loss_delay`, `pto` and
  `persistent` are §6.1.2's, §6.2.1's and §7.6.1's formulas.
- **Congestion control** (§7, Appendix B, `cc`): NewReno, proven to follow
  the appendix's transitions, with the window never below kMinimumWindow
  (two datagrams). A loss or ECN-CE for a packet sent before the current
  recovery period began changes nothing, so the window is reduced at most
  once per period, and acknowledgments of such packets do not grow it.
  `can_send` is exactly `bytes_in_flight + size <= cwnd`.
- **Received packets** (RFC 9000 §12.3, §13.2, `recv`): `Received`
  tracks the packet numbers received in at most 32 ranges. A number
  received before is always reported as a duplicate, and the ranges hold
  only numbers that were received, so the ACK frame `ack_fields` builds
  acknowledges nothing else (§13.1); its (Gap, ACK Range Length) pairs
  decode, through the same `frame::AckRanges` a peer uses, back to
  exactly those ranges. When a 33rd range is needed the oldest is dropped
  and everything below it is treated as a duplicate from then on.
- **Stream reassembly** (§2.2, `reasm`): `Reassembly` puts STREAM and
  CRYPTO data back in order. Against a ghost map of every byte received
  (the first copy of each offset), the application reads exactly those
  bytes, from `read_offset` on, in order and once; `contiguous` is exactly
  where they stop being contiguous; and the buffer stays below twice the
  window plus 16 KiB however the peer splits, repeats or overlaps its
  frames, since data past `read_offset + window` is refused. In-order data
  is appended with one copy.
- **Send bookkeeping** (§2.2, §3.1, §13.3, `sendq`, `ranges`): `SendState`
  tracks one stream's offsets for the sender (the caller keeps the
  bytes). Against a ghost set of the offsets that need nothing more
  (acknowledged, or given up on a reset), `next` returns only offsets
  written and not done, lost ones first and then new data within the flow
  control limit; `base` is exactly the first offset not done, so the
  bytes `on_ack` lets the caller free are all acknowledged and none is
  kept longer; `on_lost` queues again exactly the lost offsets that were
  sent and are not done; and the FIN goes only at the end of what was
  written. Inputs are checked, so offsets never sent change nothing.
  `RangeSet` (sorted, merged ranges) is proven to be set union and
  difference.
- **Per-packet records** (§13.3, `reclog`): `RecLog` holds what each sent
  packet carried, one record per frame, and a packet's token (`pack`)
  names its first record and count. `unpack` gives back exactly that
  packet's records, `take` returns each record once however often its
  packet is reported acknowledged or lost, and only the record pushed at
  that index, and `trim` frees the taken records at the front.
- **Writing packets** (§12.4, §14, RFC 9002 §7, `pktbuf`): `put_frame`
  writes a frame (its type and varint fields) only if it, and the payload
  bytes reserved after it, fit before the packet's end, and otherwise
  writes nothing. `packet_ends` gives those ends: the datagram's room
  less the AEAD tag, and for ack-eliciting frames also the congestion
  window's room, except for probes. `pad` never takes a datagram past its
  allowance (the datagram size and the anti-amplification limit), and
  pads one carrying an ack-eliciting Initial to 1200 bytes when the
  allowance permits.
- **Timers** (RFC 9000 §10.1, RFC 9002 §6.1.2, §6.2.1, A.8, `timers`):
  `idle_timeout` is the smaller nonzero advertised idle timeout, at least
  three PTOs, without overflow for any peer value; `pto_deadline` is the
  earliest backed-off PTO over the spaces with ack-eliciting data in
  flight; `next` is the earliest armed timer, with the PTO armed only
  when no loss timer is and the anti-amplification limit allows sending;
  `due` picks what fires (idle, then the first loss timer due, then the
  PTO), and at the time `next` returns something is due unless only a
  delayed ACK is.
- **Frames per packet type** (§12.4, Table 3, `allowed`): `allowed` is
  Table 3 written column by column, `ack_eliciting` is §13.2's rule, and
  `server_receives` refuses NEW_TOKEN and HANDSHAKE_DONE (§19.7, §19.20).
- **Key updates** (RFC 9001 §6, `keyphase`): `KeyPhase::select` picks
  the previous, current or next generation's keys for a 1-RTT packet,
  only ever one whose phase matches the Key Phase bit; the previous only
  for packets numbered below the first of the current generation, and
  the next only for those at or above it. `on_update` moves on only for a
  packet sent to the next generation, and `phase` (the bit to send with)
  follows the generation.
- **Key installation and discard** (RFC 9001 §4.9, §5.7, `schedule`):
  each space's keys go from absent to installed to discarded and never
  back; Initial keys are discarded on the first Handshake packet
  processed, Handshake keys only once the handshake is complete
  (confirmed, for a server), and 1-RTT packets are opened only after
  that.
- **Routing** (§5.2, §6, §7.2, §14.1, §17.2.1, `route`): a connection ID
  from `make_cid` names its slot (`cid_slot` gives it back); `may_start`
  opens a connection only for an Initial in a datagram of at least 1200
  bytes with a Destination Connection ID of at least 8; and
  `version_negotiation` writes a Version Negotiation packet echoing the
  client's connection IDs swapped and listing version 1, proven to parse
  back as exactly that, only for datagrams of at least 1200 bytes.
- **Frame handling checks** (§19.3, §19.15, §19.16, `handle`):
  `ack_delay` scales an ACK Delay by `2^ack_delay_exponent` and saturates
  rather than losing high bits; a NEW_CONNECTION_ID is refused when we
  send to an empty connection ID, and RETIRE_CONNECTION_ID may only name a
  sequence number we issued.

Every loop in a parser consumes input, so parsing is linear in the input;
the PADDING scan reads eight bytes at a time.

## Trusted base

- `src/spec.rs`: the specification. Reading it against RFC 9000 is what
  the proofs cannot do for you.
- `verilith-core`'s `extend` (a `memcpy` into a `Vec`) and `load_u64_le`
  (both verified there against vstd's specs of `extend_from_slice` and
  `get_unchecked`), and vstd's `slice_subrange`.
- Verus, Z3 and rustc.

There is no `external_body`, `assume` or `unsafe` in this crate.

Not covered: RFC 9221 DATAGRAM frames and other extensions (types
0x30, 0x31, ACK_FREQUENCY) are rejected as unknown frame types; QUIC
version 2 (RFC 9369) headers are reported as another version.

## Tests

`cargo test` runs RFC 9000's Appendix A examples, and round trips of
random frames, headers and transport parameters through the encoders and
parsers. `tests/recovery.rs` runs a sender's `Sent` and a receiver's
`Received` over a lossy, reordering path for 39 seeds, with every ACK
frame encoded and parsed in between, and checks that only received
packets are acknowledged, no packet is acknowledged or lost twice, and
the bytes in flight match a model; and RFC 9002's arithmetic on known
values. `tests/reasm.rs`, `tests/sendq.rs`, `tests/reclog.rs`,
`tests/pktbuf.rs`, `tests/timers.rs` and `tests/route.rs` check
reassembly, `RangeSet`, `SendState`, `RecLog`, `put_frame`, the timers
and routing against simple references.

`bench/` compares verilith-quic with quinn-proto 0.11.19 and quiche
0.24.9 (`bench/setup.sh` copies them from crates.io and makes their frame
parsers public; nothing else in them changes).
`cargo run --release --bin agree` is a differential test:

- 200,000 valid frames of every type, encoded by verilith-quic, are read
  identically by all three.
- Of 200,000 mutated frames (bytes changed, inserted, cut), every
  disagreement is one where verilith-quic rejects a frame RFC 9000 makes
  an error and the others accept it at parse time; the test fails on any
  other. In the last run: 852 extension frame types that were not
  negotiated and 282 frame types in a longer encoding than needed
  (§12.4), 750 stream counts above `2^60` (§19.11, §19.14), 61 Retire
  Prior To values above the Sequence Number (§19.15) and 11 empty
  NEW_TOKEN frames (§19.7).

## Performance

`bench/run.sh`, on a 4-vCPU cloud x86 VM (Xeon, 2.1 GHz), fastest of three
runs, in nanoseconds. The frame rows parse every frame of a decrypted
1-RTT payload and read what a receiver reads (data lengths, ACK ranges).

| | verilith-quic | quinn-proto | quiche |
|---|---:|---:|---:|
| frames: server data (ACK, STREAM of 1100 bytes) | **30** | 89 | 122 |
| frames: client ACK of 8 ranges with ECN, 3 credit frames, PING | **74** | 136 | 333 |
| frames: handshake end (CRYPTO, 3 NEW_CONNECTION_ID, NEW_TOKEN) | **46** | 154 | 183 |
| frames: 20 small STREAM frames | **107** | 551 | 1071 |
| frames: CRYPTO and 900 bytes of PADDING | **71** | 4649 | 700 |
| header: client Initial, 1200 bytes | **6.6** | 118 (36 of it copying into `BytesMut`) | 45 |
| header: 1-RTT | **2.9** | 73 (23 of it copying) | 16 |
| transport parameters (a server's 13) | **54** | 90 | 459 |
| 1000 varints of mixed lengths | **1246** | 1596 | 1562 |
| encode: ACK of 8 ranges | **48** | | 205 |
| encode: STREAM of 1100 bytes | 19 | **14** | 15 |

quinn-proto's header parser takes a `BytesMut` it owns, so its time
includes making one from the datagram; the row also gives the copy alone.
quiche copies STREAM and CRYPTO data out of the packet; verilith-quic and
quinn-proto borrow it. STREAM encoding is the one row verilith-quic does
not lead: it pushes the header's bytes into a `Vec` one at a time, where
the others write into a buffer of known size. An encoder into a fixed
buffer is the fix.
