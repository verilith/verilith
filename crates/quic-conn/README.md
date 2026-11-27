# verilith-quic-conn

A sans-I/O QUIC version 1 server (RFC 9000, RFC 9001, RFC 9002). Datagrams
go in, datagrams come out, and the caller owns the socket and the clock.
It is the QUIC under Verilith's HTTP/3 server, in place of quinn-proto.

## What is verified, and what is not

Every step that has a specification is done by a verified component:

- **`verilith-quic`**:
  - packet headers and packet numbers;
  - all frame types and transport parameters;
  - flow control and stream ID limits, and the stream state machines;
  - the anti-amplification limit;
  - sent-packet tracking, ACK processing and loss detection;
  - the RTT estimator and PTO, and NewReno congestion control;
  - received-packet tracking and the ACK frames built from it;
  - stream and CRYPTO reassembly (`reasm`), with its memory bound;
  - what each send buffer sends, resends and frees (`sendq`);
  - which frames an acknowledged or lost packet carried (`reclog`);
  - every frame written, within the datagram and the congestion window,
    and the padding (`pktbuf`);
  - the timers: idle timeout, loss timers and PTO, and which one fires
    (`timers`).
- **`verilith-tls`**:
  - the TLS 1.3 handshake for QUIC;
  - Initial secrets;
  - packet and header protection;
  - key updates.

This crate is the glue between them, and it is **plain Rust**, not verified
yet. It covers:

- routing datagrams to connections;
- the three packet number spaces and when their keys are installed and
  discarded;
- dispatching frames to the components;
- storing the bytes of send buffers (`buf.rs`);
- choosing what goes into each packet (each frame is written by verified
  `put_frame`, and only payload bytes it reserved are copied after it);
- closing.

It has no `unsafe`. Verifying it is the next step: its decisions are
already made by verified code, so what remains to prove is panic freedom
and the plumbing between those decisions.

## What it does

- **Handshake.** It runs the TLS 1.3 handshake at the Initial and Handshake
  levels, with coalesced packets.
  - Datagrams carrying ack-eliciting Initial packets are padded to 1200
    bytes.
  - Initial keys are discarded on the client's first Handshake packet.
    The client's address is validated at the same point.
  - Handshake keys are discarded once the handshake completes, and
    HANDSHAKE_DONE is sent then.
  - 1-RTT packets that arrive before the handshake completes are kept,
    four at most, and processed once it does.
- **Transport parameters.** It checks the client's transport parameters,
  including initial_source_connection_id (§7.3).
- **Streams.**
  - Bidirectional and unidirectional streams can be opened by either side.
  - Stream and connection flow control raise MAX_STREAM_DATA and MAX_DATA
    as data is read.
  - MAX_STREAMS is raised as the peer's streams close.
  - RESET_STREAM and STOP_SENDING are supported both ways.
- **Loss recovery.**
  - It retransmits the frames of lost packets (data, CRYPTO and control
    frames).
  - On a PTO it sends two probe packets, with outstanding data sent again.
  - It follows the congestion window, and ACK-only packets are exempt.
- **Key updates** started by the peer (RFC 9001 §6).
- **Connection lifetime.**
  - Idle timeout.
  - Closing and draining states.
  - CONNECTION_CLOSE in every space that has keys.
- **Version Negotiation** for unknown versions.
- **Segmentation offload.** `poll_transmit` writes up to `max` datagrams of
  one size for GSO.
- **Path MTU discovery** (§14.3, in the simplest form of RFC 8899):
  - it starts at 1200 bytes;
  - once the handshake is confirmed it sends one probe padded to
    `probe_datagram` (1452 by default), up to three times;
  - if acknowledged, that becomes the datagram size and the congestion
    controller's (verified `raise_mds`);
  - a lost probe is not treated as congestion (§14.4).

Not yet supported:

- Retry and address-validation tokens.
- Starting a key update itself.
- Issuing more than one connection ID, migration, and stateless reset.
- Pacing, ECN, 0-RTT, and noticing a path MTU that shrinks later.

## Tests

`tests/quinn.rs` runs the server against quinn-proto's client. Everything is
in memory with a virtual clock.

- **Handshakes:** one request; 29 seeds with 30% loss in each direction.
- **Volume:** 300 requests on one connection, including 3 MB responses.
- **Lossy path:** 5% loss with reordering, over 5 seeds.
- **Flow control:** stream windows of 4000 bytes and a connection window of
  10,000, with more requests than allowed streams.
- **Key updates:** three updates started by the client.
- **Server-opened streams:** a unidirectional stream opened by the server.
- **Stop and reset:** STOP_SENDING answered with RESET_STREAM; a request
  reset by the client.
- **Closing:** a close by the server; the idle timeout.
- **Path MTU:** probing up to 1452 bytes, and a path that drops
  datagrams over 1300 bytes, where the server stays at 1200.

`src/buf.rs` has unit tests for the send buffers' byte storage.

## Performance

`cargo run --release --example bench` measures server CPU time only:

- each server is driven by quinn-proto's client over an in-memory network
  with no delay and no loss;
- both servers use 1452-byte datagrams and the same flow control windows;
- both use aws-lc for cryptography;
- each figure is the fastest of three runs, on a 4-vCPU cloud x86 VM.

| case | verilith-quic-conn | quinn-proto 0.11.19 |
|---|---:|---:|
| bulk: 1 connection, 4 x 64 MiB | **124 ms** | 149 ms |
| requests: 1 connection, 20000 x 1 KiB, 50 at a time | **14.7 ms** | 20.7 ms |
| requests: 10 connections, 2000 x 16 KiB each, 20 at a time | **122 ms** | 191 ms |
| handshakes: 500 connections, 1 x 1 KiB | **33.4 ms** | 84.5 ms |

This crate is verilith-server's default QUIC. End to end, with h2load over
loopback ([report](../../bench/server/results/2026-11-26-cloud-h3-default/report.md)),
in requests per server CPU-second:

| case | verilith-server on this crate | on quinn-proto | nginx-quic |
|---|---:|---:|---:|
| h3-plaintext | **546k** | 359k | 296k |
| h3-static-64k | 22k | 20k | **27k** |
| h3-static-1m | 1517 | 1251 | **1947** |

nginx still sends large bodies with less CPU.

Interop: besides quinn-proto's client (`tests/quinn.rs`, and the server's
`tests/h3.rs`), ngtcp2 (h2load) and aioquic
(`bench/server/h3/interop/aioquic_client.py`: 32 requests and three key
updates started by the client) work against it.

Neither server issues session tickets or accepts 0-RTT. quinn-proto paces
its sending; this crate does not yet, which a real network may reward
differently from this in-memory one.
