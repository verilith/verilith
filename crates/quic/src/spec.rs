//! The specification: RFC 9000 as pure functions. Everything here is
//! trusted: it is what the proofs prove the code computes.
//!
//! Each parser is a function of the whole input `b` and a position in it,
//! returning what it read and the position after it, or `None` when the
//! input is malformed or ends too soon. Each encoder is a function from a
//! value to the bytes the RFC prescribes for it, always choosing the
//! shortest variable-length integers.
pub use verilith_core::varint::{VARINT_LIMIT, VARINT_MAX};
#[cfg(verus_only)]
pub use verilith_core::varint::{b8, by, varint, varint_enc, varint_size, vlen};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Variable-length integers (§16)
// ---------------------------------------------------------------------------

// The definitions are verilith-core's (`verilith_core::varint`), shared
// with HTTP/3: `VARINT_LIMIT`, `VARINT_MAX`, `vlen`, `by`, `varint`, `b8`,
// `varint_enc` and `varint_size`.


// ---------------------------------------------------------------------------
// Byte strings at a position
// ---------------------------------------------------------------------------

/// `b` holds `s` at position `p`.
pub open spec fn at(b: Seq<u8>, p: int, s: Seq<u8>) -> bool {
    0 <= p && p + s.len() <= b.len() && b.subrange(p, p + s.len()) == s
}

/// The `n` bytes of `b` from `p`, if there are that many.
pub open spec fn take(b: Seq<u8>, p: int, n: int) -> Option<(Seq<u8>, int)> {
    if 0 <= p && 0 <= n && p + n <= b.len() {
        Some((b.subrange(p, p + n), p + n))
    } else {
        None
    }
}

/// A variable-length integer, followed by that many bytes (§19's "Length"
/// fields).
pub open spec fn bytes_len(b: Seq<u8>, p: int) -> Option<(Seq<u8>, int)> {
    match varint(b, p) {
        None => None,
        Some((n, p1)) => take(b, p1, n as int),
    }
}

/// The encoding of `bytes_len`.
pub open spec fn bytes_len_enc(d: Seq<u8>) -> Seq<u8> {
    varint_enc(d.len() as u64) + d
}

// ---------------------------------------------------------------------------
// Frames (§12.4, §19)
// ---------------------------------------------------------------------------

/// A frame (§19). Byte strings are the frame's own bytes.
pub enum Fr {
    /// §19.1: a run of `n >= 1` PADDING frames (zero bytes), the longest
    /// run at that position.
    Padding { n: nat },
    /// §19.2.
    Ping,
    /// §19.3: types 0x02 and 0x03 (`ecn` is `Some` for 0x03). `first` is
    /// the First ACK Range; `ranges` are the (Gap, ACK Range Length) pairs.
    Ack { largest: u64, delay: u64, first: u64, ranges: Seq<(u64, u64)>, ecn: Option<(u64, u64, u64)> },
    /// §19.4.
    ResetStream { id: u64, err: u64, final_size: u64 },
    /// §19.5.
    StopSending { id: u64, err: u64 },
    /// §19.6.
    Crypto { offset: u64, data: Seq<u8> },
    /// §19.7.
    NewToken { token: Seq<u8> },
    /// §19.8: types 0x08 to 0x0f. Without `len`, the data runs to the end
    /// of the packet. Offset 0 is encoded without the OFF bit.
    Stream { id: u64, offset: u64, len: bool, fin: bool, data: Seq<u8> },
    /// §19.9.
    MaxData { max: u64 },
    /// §19.10.
    MaxStreamData { id: u64, max: u64 },
    /// §19.11: types 0x12 (bidirectional) and 0x13.
    MaxStreams { bidi: bool, max: u64 },
    /// §19.12.
    DataBlocked { max: u64 },
    /// §19.13.
    StreamDataBlocked { id: u64, max: u64 },
    /// §19.14: types 0x16 (bidirectional) and 0x17.
    StreamsBlocked { bidi: bool, max: u64 },
    /// §19.15.
    NewConnectionId { seq: u64, retire: u64, cid: Seq<u8>, token: Seq<u8> },
    /// §19.16.
    RetireConnectionId { seq: u64 },
    /// §19.17.
    PathChallenge { data: Seq<u8> },
    /// §19.18.
    PathResponse { data: Seq<u8> },
    /// §19.19: type 0x1c (transport, with the frame type that caused it)
    /// and 0x1d (`app`).
    ConnectionClose { app: bool, err: u64, frame_type: u64, reason: Seq<u8> },
    /// §19.20.
    HandshakeDone,
}

/// `2^60`, the largest stream count (§4.6, §19.11, §19.14).
pub const MAX_STREAMS_LIMIT: u64 = 0x1000_0000_0000_0000;

/// The largest connection ID length in QUIC version 1 (§17.2).
pub const MAX_CID_LEN: u64 = 20;

/// The number of zero bytes from `p`.
pub open spec fn zeros(b: Seq<u8>, p: int) -> nat
    decreases b.len() - p,
{
    if p < 0 || p >= b.len() || b[p] != 0 {
        0
    } else {
        1 + zeros(b, p + 1)
    }
}

/// The (Gap, ACK Range Length) pairs of an ACK frame (§19.3.1): `count`
/// of them from `p`, after a range whose smallest packet number is
/// `smallest`. A gap or length that would make a packet number negative is
/// an error.
pub open spec fn ack_ranges(b: Seq<u8>, p: int, count: nat, smallest: u64) -> Option<(Seq<(u64, u64)>, int)>
    decreases count,
{
    if count == 0 {
        Some((Seq::empty(), p))
    } else {
        match varint(b, p) {
            None => None,
            Some((gap, p1)) => match varint(b, p1) {
                None => None,
                Some((len, p2)) => if gap as int + 2 > smallest || len as int > smallest - gap - 2 {
                    None
                } else {
                    match ack_ranges(b, p2, (count - 1) as nat, (smallest - gap - 2 - len) as u64) {
                        None => None,
                        Some((rs, e)) => Some((seq![(gap, len)] + rs, e)),
                    }
                },
            },
        }
    }
}

/// Two variable-length integers.
pub open spec fn varint2(b: Seq<u8>, p: int) -> Option<(u64, u64, int)> {
    match varint(b, p) {
        None => None,
        Some((x, p1)) => match varint(b, p1) {
            None => None,
            Some((y, p2)) => Some((x, y, p2)),
        },
    }
}

/// Three variable-length integers.
pub open spec fn varint3(b: Seq<u8>, p: int) -> Option<(u64, u64, u64, int)> {
    match varint2(b, p) {
        None => None,
        Some((x, y, p2)) => match varint(b, p2) {
            None => None,
            Some((z, p3)) => Some((x, y, z, p3)),
        },
    }
}

/// The body of an ACK frame of type `t` from `p` (after the type).
pub open spec fn ack_body(b: Seq<u8>, p: int, t: u8) -> Option<(Fr, int)> {
    match varint2(b, p) {
        None => None,
        Some((largest, delay, p2)) => match varint2(b, p2) {
            None => None,
            Some((count, first, p4)) => if first > largest {
                None
            } else {
                match ack_ranges(b, p4, count as nat, (largest - first) as u64) {
                    None => None,
                    Some((ranges, p5)) => if t == 0x02 {
                        Some((Fr::Ack { largest, delay, first, ranges, ecn: None }, p5))
                    } else {
                        match varint3(b, p5) {
                            None => None,
                            Some((e0, e1, ce, p6)) => Some(
                                (Fr::Ack { largest, delay, first, ranges, ecn: Some((e0, e1, ce)) }, p6),
                            ),
                        }
                    },
                }
            },
        },
    }
}

/// The body of a STREAM frame of type `t` (0x08 to 0x0f) from `p`.
pub open spec fn stream_body(b: Seq<u8>, p: int, t: u8) -> Option<(Fr, int)> {
    match varint(b, p) {
        None => None,
        Some((id, p1)) => {
            let off = if t & 0x04 != 0 { varint(b, p1) } else { Some((0u64, p1)) };
            match off {
                None => None,
                Some((offset, p2)) => {
                    let d = if t & 0x02 != 0 { bytes_len(b, p2) } else { take(b, p2, b.len() - p2) };
                    match d {
                        None => None,
                        Some((data, p3)) => if offset as int + data.len() > VARINT_MAX {
                            None
                        } else {
                            Some((Fr::Stream { id, offset, len: t & 0x02 != 0, fin: t & 0x01 != 0, data }, p3))
                        },
                    }
                },
            }
        },
    }
}

/// The body of a NEW_CONNECTION_ID frame from `p`.
pub open spec fn ncid_body(b: Seq<u8>, p: int) -> Option<(Fr, int)> {
    match varint2(b, p) {
        None => None,
        Some((seq, retire, p2)) => if retire > seq || p2 >= b.len() || b[p2] < 1 || b[p2] > 20 {
            None
        } else {
            match take(b, p2 + 1, b[p2] as int) {
                None => None,
                Some((cid, p3)) => match take(b, p3, 16) {
                    None => None,
                    Some((token, p4)) => Some((Fr::NewConnectionId { seq, retire, cid, token }, p4)),
                },
            }
        },
    }
}

/// The body of a CONNECTION_CLOSE frame of type `t` (0x1c or 0x1d) from `p`.
pub open spec fn close_body(b: Seq<u8>, p: int, t: u8) -> Option<(Fr, int)> {
    match varint(b, p) {
        None => None,
        Some((err, p1)) => {
            let ft = if t == 0x1c { varint(b, p1) } else { Some((0u64, p1)) };
            match ft {
                None => None,
                Some((frame_type, p2)) => match bytes_len(b, p2) {
                    None => None,
                    Some((reason, p3)) => Some((Fr::ConnectionClose { app: t == 0x1d, err, frame_type, reason }, p3)),
                },
            }
        },
    }
}

/// The frame at `b[p]` and the position after it (§12.4, §19), or `None`:
/// the frame is malformed, ends too soon, or its type is not one of RFC
/// 9000's (a connection error of type FRAME_ENCODING_ERROR). A frame type
/// is a variable-length integer that must be encoded in one byte (§12.4),
/// which all of RFC 9000's types are.
pub open spec fn frame(b: Seq<u8>, p: int) -> Option<(Fr, int)> {
    if p < 0 || p >= b.len() {
        None
    } else {
        let t = b[p];
        let q = p + 1;
        if t == 0x00 {
            Some((Fr::Padding { n: zeros(b, p) }, p + zeros(b, p)))
        } else if t == 0x01 {
            Some((Fr::Ping, q))
        } else if t == 0x02 || t == 0x03 {
            ack_body(b, q, t)
        } else if t == 0x04 {
            match varint3(b, q) {
                None => None,
                Some((id, err, final_size, e)) => Some((Fr::ResetStream { id, err, final_size }, e)),
            }
        } else if t == 0x05 {
            match varint2(b, q) {
                None => None,
                Some((id, err, e)) => Some((Fr::StopSending { id, err }, e)),
            }
        } else if t == 0x06 {
            match varint(b, q) {
                None => None,
                Some((offset, q1)) => match bytes_len(b, q1) {
                    None => None,
                    Some((data, e)) => if offset as int + data.len() > VARINT_MAX {
                        None
                    } else {
                        Some((Fr::Crypto { offset, data }, e))
                    },
                },
            }
        } else if t == 0x07 {
            match bytes_len(b, q) {
                None => None,
                Some((token, e)) => if token.len() == 0 {
                    None
                } else {
                    Some((Fr::NewToken { token }, e))
                },
            }
        } else if t <= 0x0f {
            stream_body(b, q, t)
        } else if t == 0x10 || t == 0x14 || t == 0x19 {
            match varint(b, q) {
                None => None,
                Some((x, e)) => Some(
                    (
                        if t == 0x10 {
                            Fr::MaxData { max: x }
                        } else if t == 0x14 {
                            Fr::DataBlocked { max: x }
                        } else {
                            Fr::RetireConnectionId { seq: x }
                        },
                        e,
                    ),
                ),
            }
        } else if t == 0x11 || t == 0x15 {
            match varint2(b, q) {
                None => None,
                Some((id, max, e)) => Some(
                    (
                        if t == 0x11 {
                            Fr::MaxStreamData { id, max }
                        } else {
                            Fr::StreamDataBlocked { id, max }
                        },
                        e,
                    ),
                ),
            }
        } else if 0x12 <= t <= 0x13 || 0x16 <= t <= 0x17 {
            match varint(b, q) {
                None => None,
                Some((max, e)) => if max > MAX_STREAMS_LIMIT {
                    None
                } else if t <= 0x13 {
                    Some((Fr::MaxStreams { bidi: t == 0x12, max }, e))
                } else {
                    Some((Fr::StreamsBlocked { bidi: t == 0x16, max }, e))
                },
            }
        } else if t == 0x18 {
            ncid_body(b, q)
        } else if t == 0x1a || t == 0x1b {
            match take(b, q, 8) {
                None => None,
                Some((data, e)) => Some(
                    (if t == 0x1a { Fr::PathChallenge { data } } else { Fr::PathResponse { data } }, e),
                ),
            }
        } else if t == 0x1c || t == 0x1d {
            close_body(b, q, t)
        } else if t == 0x1e {
            Some((Fr::HandshakeDone, q))
        } else {
            None
        }
    }
}

/// The encoding of ACK ranges.
pub open spec fn ack_ranges_enc(rs: Seq<(u64, u64)>) -> Seq<u8>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Seq::empty()
    } else {
        varint_enc(rs[0].0) + varint_enc(rs[0].1) + ack_ranges_enc(rs.drop_first())
    }
}

/// The encoding of a frame (§19), with the shortest integers.
pub open spec fn frame_enc(f: Fr) -> Seq<u8> {
    match f {
        Fr::Padding { n } => Seq::new(n, |i: int| 0u8),
        Fr::Ping => seq![0x01u8],
        Fr::Ack { largest, delay, first, ranges, ecn } => {
            let body = varint_enc(largest) + varint_enc(delay) + varint_enc(ranges.len() as u64)
                + varint_enc(first) + ack_ranges_enc(ranges);
            match ecn {
                None => seq![0x02u8] + body,
                Some((e0, e1, ce)) => seq![0x03u8] + body + varint_enc(e0) + varint_enc(e1) + varint_enc(ce),
            }
        },
        Fr::ResetStream { id, err, final_size } => seq![0x04u8] + varint_enc(id) + varint_enc(err)
            + varint_enc(final_size),
        Fr::StopSending { id, err } => seq![0x05u8] + varint_enc(id) + varint_enc(err),
        Fr::Crypto { offset, data } => seq![0x06u8] + varint_enc(offset) + bytes_len_enc(data),
        Fr::NewToken { token } => seq![0x07u8] + bytes_len_enc(token),
        Fr::Stream { id, offset, len, fin, data } => {
            let t: u8 = (0x08u8 | (if offset != 0 { 0x04u8 } else { 0u8 }) | (if len { 0x02u8 } else { 0u8 })
                | (if fin { 0x01u8 } else { 0u8 })) as u8;
            seq![t] + varint_enc(id) + (if offset != 0 { varint_enc(offset) } else { Seq::empty() }) + (
            if len {
                bytes_len_enc(data)
            } else {
                data
            })
        },
        Fr::MaxData { max } => seq![0x10u8] + varint_enc(max),
        Fr::MaxStreamData { id, max } => seq![0x11u8] + varint_enc(id) + varint_enc(max),
        Fr::MaxStreams { bidi, max } => seq![if bidi { 0x12u8 } else { 0x13u8 }] + varint_enc(max),
        Fr::DataBlocked { max } => seq![0x14u8] + varint_enc(max),
        Fr::StreamDataBlocked { id, max } => seq![0x15u8] + varint_enc(id) + varint_enc(max),
        Fr::StreamsBlocked { bidi, max } => seq![if bidi { 0x16u8 } else { 0x17u8 }] + varint_enc(max),
        Fr::NewConnectionId { seq, retire, cid, token } => seq![0x18u8] + varint_enc(seq) + varint_enc(
            retire,
        ) + seq![cid.len() as u8] + cid + token,
        Fr::RetireConnectionId { seq } => seq![0x19u8] + varint_enc(seq),
        Fr::PathChallenge { data } => seq![0x1au8] + data,
        Fr::PathResponse { data } => seq![0x1bu8] + data,
        Fr::ConnectionClose { app, err, frame_type, reason } => if app {
            seq![0x1du8] + varint_enc(err) + bytes_len_enc(reason)
        } else {
            seq![0x1cu8] + varint_enc(err) + varint_enc(frame_type) + bytes_len_enc(reason)
        },
        Fr::HandshakeDone => seq![0x1eu8],
    }
}

/// `x` is a variable-length integer value.
pub open spec fn vi(x: u64) -> bool {
    x < VARINT_LIMIT
}

/// ACK ranges that are valid after a range whose smallest packet number
/// is `smallest`.
pub open spec fn ack_ranges_wf(rs: Seq<(u64, u64)>, smallest: u64) -> bool
    decreases rs.len(),
{
    if rs.len() == 0 {
        true
    } else {
        let (gap, len) = rs[0];
        &&& vi(gap) && vi(len)
        &&& gap as int + 2 <= smallest
        &&& len as int <= smallest - gap - 2
        &&& ack_ranges_wf(rs.drop_first(), (smallest - gap - 2 - len) as u64)
    }
}

/// The frames that can be encoded, and that `frame` parses back.
pub open spec fn frame_wf(f: Fr) -> bool {
    match f {
        Fr::Padding { n } => n >= 1,
        Fr::Ping => true,
        Fr::Ack { largest, delay, first, ranges, ecn } => vi(largest) && vi(delay) && vi(first)
            && ranges.len() < VARINT_LIMIT && first <= largest && ack_ranges_wf(ranges, (largest - first) as u64)
            && match ecn {
            None => true,
            Some((e0, e1, ce)) => vi(e0) && vi(e1) && vi(ce),
        },
        Fr::ResetStream { id, err, final_size } => vi(id) && vi(err) && vi(final_size),
        Fr::StopSending { id, err } => vi(id) && vi(err),
        Fr::Crypto { offset, data } => vi(offset) && offset + data.len() <= VARINT_MAX,
        Fr::NewToken { token } => 0 < token.len() < VARINT_LIMIT,
        Fr::Stream { id, offset, len, fin, data } => vi(id) && vi(offset) && offset + data.len() <= VARINT_MAX,
        Fr::MaxData { max } => vi(max),
        Fr::MaxStreamData { id, max } => vi(id) && vi(max),
        Fr::MaxStreams { bidi, max } => max <= MAX_STREAMS_LIMIT,
        Fr::DataBlocked { max } => vi(max),
        Fr::StreamDataBlocked { id, max } => vi(id) && vi(max),
        Fr::StreamsBlocked { bidi, max } => max <= MAX_STREAMS_LIMIT,
        Fr::NewConnectionId { seq, retire, cid, token } => vi(seq) && retire <= seq && 1 <= cid.len()
            <= 20 && token.len() == 16,
        Fr::RetireConnectionId { seq } => vi(seq),
        Fr::PathChallenge { data } => data.len() == 8,
        Fr::PathResponse { data } => data.len() == 8,
        Fr::ConnectionClose { app, err, frame_type, reason } => vi(err) && vi(frame_type) && (app
            ==> frame_type == 0) && reason.len() < VARINT_LIMIT,
        Fr::HandshakeDone => true,
    }
}

/// What may follow the encoding of `f` for it to parse back: nothing after
/// a STREAM frame without a length, and no zero byte after PADDING.
pub open spec fn frame_rest_ok(f: Fr, rest: Seq<u8>) -> bool {
    match f {
        Fr::Padding { n } => rest.len() == 0 || rest[0] != 0,
        Fr::Stream { len, .. } => len || rest.len() == 0,
        _ => true,
    }
}


// ---------------------------------------------------------------------------
// Packet headers (§17), before header protection is removed
// ---------------------------------------------------------------------------

/// QUIC version 1 (RFC 9000).
pub const VERSION_1: u32 = 1;

/// The big-endian `u32` at `b[p]`.
pub open spec fn u32be(b: Seq<u8>, p: int) -> u32 {
    ((b[p] as u32) << 24) | ((b[p + 1] as u32) << 16) | ((b[p + 2] as u32) << 8) | (b[p + 3] as u32)
}

/// The big-endian encoding of `v`.
pub open spec fn u32_enc(v: u32) -> Seq<u8> {
    seq![(v >> 24) as u8, (v >> 16) as u8, (v >> 8) as u8, v as u8]
}

/// The concatenated encodings of `vs`.
pub open spec fn u32s_enc(vs: Seq<u32>) -> Seq<u8>
    decreases vs.len(),
{
    if vs.len() == 0 {
        Seq::empty()
    } else {
        u32_enc(vs[0]) + u32s_enc(vs.drop_first())
    }
}

/// `n` big-endian `u32`s from `p`.
pub open spec fn u32s(b: Seq<u8>, p: int, n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![u32be(b, p)] + u32s(b, p + 4, (n - 1) as nat)
    }
}

/// A packet header (§17), as it is before header protection is removed:
/// the low bits of `first` and the packet number are still masked.
pub enum Hdr {
    /// An Initial (type 0), 0-RTT (1) or Handshake (2) packet of version 1
    /// (§17.2.2 to §17.2.4). `token` is empty except for Initial packets.
    /// `len` is the Length field: the packet number and payload that
    /// follow.
    Long { first: u8, dcid: Seq<u8>, scid: Seq<u8>, token: Seq<u8>, len: u64 },
    /// A Retry packet (§17.2.5): the token, and the 16-byte integrity tag
    /// at the end of the datagram.
    Retry { first: u8, dcid: Seq<u8>, scid: Seq<u8>, token: Seq<u8>, tag: Seq<u8> },
    /// A Version Negotiation packet (§17.2.1): version 0, and the versions
    /// that fill the rest of the datagram.
    VersionNegotiation { first: u8, dcid: Seq<u8>, scid: Seq<u8>, versions: Seq<u32> },
    /// A long header of another version: only the version-independent
    /// fields (RFC 8999 §5.1), connection IDs of up to 255 bytes.
    OtherVersion { first: u8, version: u32, dcid: Seq<u8>, scid: Seq<u8> },
    /// A 1-RTT packet (§17.3.1): the destination connection ID, whose
    /// length the receiver chose.
    Short { first: u8, dcid: Seq<u8> },
}

/// The two connection IDs of a long header at `p` (after the first byte
/// and the version), each at most `max` bytes.
pub open spec fn cids(b: Seq<u8>, p: int, max: int) -> Option<(Seq<u8>, Seq<u8>, int)> {
    if p < 0 || p >= b.len() || b[p] > max {
        None
    } else {
        match take(b, p + 1, b[p] as int) {
            None => None,
            Some((dcid, p1)) => if p1 >= b.len() || b[p1] > max {
                None
            } else {
                match take(b, p1 + 1, b[p1] as int) {
                    None => None,
                    Some((scid, p2)) => Some((dcid, scid, p2)),
                }
            },
        }
    }
}

/// The header of the packet at `b[p]` and the position after it, where
/// the datagram `b` ends at `b.len()` and 1-RTT packets carry destination
/// connection IDs of `cid_len` bytes. `None` means the packet is to be
/// discarded (§5.2, §17): too short, a fixed bit of 0, a connection ID too
/// long for version 1, a Length past the end of the datagram, a Retry
/// without a token, or a Version Negotiation packet whose versions are not
/// a whole number of `u32`s.
pub open spec fn header(b: Seq<u8>, p: int, cid_len: nat) -> Option<(Hdr, int)> {
    if p < 0 || p >= b.len() {
        None
    } else if b[p] & 0x80 == 0 {
        if b[p] & 0x40 == 0 {
            None
        } else {
            match take(b, p + 1, cid_len as int) {
                None => None,
                Some((dcid, e)) => Some((Hdr::Short { first: b[p], dcid }, e)),
            }
        }
    } else if p + 5 > b.len() {
        None
    } else {
        let first = b[p];
        let version = u32be(b, p + 1);
        if version == 0 {
            match cids(b, p + 5, 255) {
                None => None,
                Some((dcid, scid, q)) => if (b.len() - q) % 4 != 0 {
                    None
                } else {
                    Some((Hdr::VersionNegotiation { first, dcid, scid, versions: u32s(b, q, ((b.len() - q) / 4) as nat) }, b.len() as int))
                },
            }
        } else if version != VERSION_1 {
            match cids(b, p + 5, 255) {
                None => None,
                Some((dcid, scid, q)) => Some((Hdr::OtherVersion { first, version, dcid, scid }, q)),
            }
        } else if first & 0x40 == 0 {
            None
        } else {
            match cids(b, p + 5, MAX_CID_LEN as int) {
                None => None,
                Some((dcid, scid, q)) => {
                    let ty = (first >> 4) & 3;
                    if ty == 3 {
                        if b.len() - q < 17 {
                            None
                        } else {
                            Some((Hdr::Retry {
                                first,
                                dcid,
                                scid,
                                token: b.subrange(q, b.len() - 16),
                                tag: b.subrange(b.len() - 16, b.len() as int),
                            }, b.len() as int))
                        }
                    } else {
                        let tok = if ty == 0 { bytes_len(b, q) } else { Some((Seq::empty(), q)) };
                        match tok {
                            None => None,
                            Some((token, q1)) => match varint(b, q1) {
                                None => None,
                                Some((len, e)) => if len as int > b.len() - e {
                                    None
                                } else {
                                    Some((Hdr::Long { first, dcid, scid, token, len }, e))
                                },
                            },
                        }
                    }
                },
            }
        }
    }
}

/// Where the packet whose header `h` ends at `e` ends, in a datagram that
/// ends at `n` (§12.2): long headers with a Length field end after it,
/// the others at the end of the datagram.
pub open spec fn packet_end(h: Hdr, e: int, n: int) -> int {
    match h {
        Hdr::Long { len, .. } => e + len,
        _ => n,
    }
}

/// The encoding of a header (§17), with the shortest integers.
pub open spec fn header_enc(h: Hdr) -> Seq<u8> {
    match h {
        Hdr::Long { first, dcid, scid, token, len } => seq![first] + u32_enc(VERSION_1) + seq![dcid.len() as u8] + dcid
            + seq![scid.len() as u8] + scid + (if (first >> 4) & 3 == 0 { bytes_len_enc(token) } else { Seq::empty() })
            + varint_enc(len),
        Hdr::Retry { first, dcid, scid, token, tag } => seq![first] + u32_enc(VERSION_1) + seq![dcid.len() as u8] + dcid
            + seq![scid.len() as u8] + scid + token + tag,
        Hdr::VersionNegotiation { first, dcid, scid, versions } => seq![first] + u32_enc(0) + seq![dcid.len() as u8]
            + dcid + seq![scid.len() as u8] + scid + u32s_enc(versions),
        Hdr::OtherVersion { first, version, dcid, scid } => seq![first] + u32_enc(version) + seq![dcid.len() as u8]
            + dcid + seq![scid.len() as u8] + scid,
        Hdr::Short { first, dcid } => seq![first] + dcid,
    }
}

/// The headers that can be encoded and parse back.
pub open spec fn header_wf(h: Hdr, cid_len: nat) -> bool {
    match h {
        Hdr::Long { first, dcid, scid, token, len } => first & 0xc0 == 0xc0 && (first >> 4) & 3 != 3 && dcid.len()
            <= MAX_CID_LEN && scid.len() <= MAX_CID_LEN && ((first >> 4) & 3 != 0 ==> token.len() == 0)
            && token.len() < VARINT_LIMIT && vi(len),
        Hdr::Retry { first, dcid, scid, token, tag } => first & 0xc0 == 0xc0 && (first >> 4) & 3 == 3 && dcid.len()
            <= MAX_CID_LEN && scid.len() <= MAX_CID_LEN && token.len() > 0 && tag.len() == 16,
        Hdr::VersionNegotiation { first, dcid, scid, versions } => first & 0x80 != 0 && dcid.len() <= 255
            && scid.len() <= 255,
        Hdr::OtherVersion { first, version, dcid, scid } => first & 0x80 != 0 && version != 0 && version
            != VERSION_1 && dcid.len() <= 255 && scid.len() <= 255,
        Hdr::Short { first, dcid } => first & 0xc0 == 0x40 && dcid.len() == cid_len,
    }
}

/// What may follow an encoded header for it to parse back: at least the
/// Length's bytes after a long header, and nothing after a Retry or
/// Version Negotiation packet, which run to the end of the datagram.
pub open spec fn header_rest_ok(h: Hdr, rest: Seq<u8>) -> bool {
    match h {
        Hdr::Long { len, .. } => len <= rest.len(),
        Hdr::Retry { .. } => rest.len() == 0,
        Hdr::VersionNegotiation { .. } => rest.len() == 0,
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Packet numbers (§17.1, Appendix A)
// ---------------------------------------------------------------------------

/// `2^n`.
pub open spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

/// The packet number recovered from its `nbits` least significant bits
/// `truncated`, when the next packet number expected is `expected` (the
/// largest received, plus one; 0 before any): Appendix A.3, the candidate
/// closest to `expected`.
pub open spec fn decode_pn(expected: int, truncated: int, nbits: nat) -> int {
    let win = pow2(nbits) as int;
    let hwin = win / 2;
    let candidate = expected - expected % win + truncated;
    if candidate <= expected - hwin && candidate < VARINT_LIMIT - win {
        candidate + win
    } else if candidate > expected + hwin && candidate >= win {
        candidate - win
    } else {
        candidate
    }
}

/// The number of bytes to encode packet number `pn` with, when the peer
/// has acknowledged packets up to `largest_acked` (-1 before any)
/// (Appendix A.2): enough for twice the packets not yet acknowledged.
pub open spec fn pn_len(pn: int, largest_acked: int) -> int {
    let unacked = pn - largest_acked;
    if unacked <= 0x80 {
        1
    } else if unacked <= 0x8000 {
        2
    } else if unacked <= 0x80_0000 {
        3
    } else {
        4
    }
}


// ---------------------------------------------------------------------------
// Transport parameters (§18)
// ---------------------------------------------------------------------------

/// A preferred_address value (§18.2): the IPv4 address and port (6
/// bytes), the IPv6 address and port (18 bytes), a connection ID of 1 to
/// 20 bytes and a stateless reset token (16 bytes).
pub struct SPref {
    pub v4: Seq<u8>,
    pub v6: Seq<u8>,
    pub cid: Seq<u8>,
    pub token: Seq<u8>,
}

/// The transport parameters of RFC 9000 (and max_datagram_frame_size of
/// RFC 9221), each absent or with its value. Others are ignored (§7.4.2).
pub struct TP {
    /// 0x00: original_destination_connection_id.
    pub original_dcid: Option<Seq<u8>>,
    /// 0x01: max_idle_timeout (milliseconds).
    pub max_idle_timeout: Option<u64>,
    /// 0x02: stateless_reset_token (16 bytes).
    pub stateless_reset_token: Option<Seq<u8>>,
    /// 0x03: max_udp_payload_size, at least 1200.
    pub max_udp_payload_size: Option<u64>,
    /// 0x04: initial_max_data.
    pub initial_max_data: Option<u64>,
    /// 0x05: initial_max_stream_data_bidi_local.
    pub initial_max_stream_data_bidi_local: Option<u64>,
    /// 0x06: initial_max_stream_data_bidi_remote.
    pub initial_max_stream_data_bidi_remote: Option<u64>,
    /// 0x07: initial_max_stream_data_uni.
    pub initial_max_stream_data_uni: Option<u64>,
    /// 0x08: initial_max_streams_bidi, at most 2^60.
    pub initial_max_streams_bidi: Option<u64>,
    /// 0x09: initial_max_streams_uni, at most 2^60.
    pub initial_max_streams_uni: Option<u64>,
    /// 0x0a: ack_delay_exponent, at most 20.
    pub ack_delay_exponent: Option<u64>,
    /// 0x0b: max_ack_delay (milliseconds), below 2^14.
    pub max_ack_delay: Option<u64>,
    /// 0x0c: disable_active_migration.
    pub disable_active_migration: bool,
    /// 0x0d: preferred_address.
    pub preferred_address: Option<SPref>,
    /// 0x0e: active_connection_id_limit, at least 2.
    pub active_connection_id_limit: Option<u64>,
    /// 0x0f: initial_source_connection_id.
    pub initial_scid: Option<Seq<u8>>,
    /// 0x10: retry_source_connection_id.
    pub retry_scid: Option<Seq<u8>>,
    /// 0x20: max_datagram_frame_size (RFC 9221).
    pub max_datagram_frame_size: Option<u64>,
}

/// No parameters.
pub open spec fn tp_empty() -> TP {
    TP {
        original_dcid: None,
        max_idle_timeout: None,
        stateless_reset_token: None,
        max_udp_payload_size: None,
        initial_max_data: None,
        initial_max_stream_data_bidi_local: None,
        initial_max_stream_data_bidi_remote: None,
        initial_max_stream_data_uni: None,
        initial_max_streams_bidi: None,
        initial_max_streams_uni: None,
        ack_delay_exponent: None,
        max_ack_delay: None,
        disable_active_migration: false,
        preferred_address: None,
        active_connection_id_limit: None,
        initial_scid: None,
        retry_scid: None,
        max_datagram_frame_size: None,
    }
}

/// A preferred_address value.
pub open spec fn pref_parse(v: Seq<u8>) -> Option<SPref> {
    if v.len() < 41 || v[24] < 1 || v[24] > 20 || v.len() != 41 + v[24] {
        None
    } else {
        Some(SPref {
            v4: v.subrange(0, 6),
            v6: v.subrange(6, 24),
            cid: v.subrange(25, 25 + v[24]),
            token: v.subrange(25 + v[24], v.len() as int),
        })
    }
}

/// The encoding of a preferred_address value.
pub open spec fn pref_enc(a: SPref) -> Seq<u8> {
    a.v4 + a.v6 + seq![a.cid.len() as u8] + a.cid + a.token
}

/// An integer parameter's value: one variable-length integer, filling it.
pub open spec fn tp_int(v: Seq<u8>) -> Option<u64> {
    match varint(v, 0) {
        Some((x, e)) => if e == v.len() { Some(x) } else { None },
        None => None,
    }
}

/// `acc` with the parameter `id` of value `v` added, or `None` if it is
/// a duplicate (§7.4) or its value is invalid (§18.2): a connection
/// error of type TRANSPORT_PARAMETER_ERROR. Unknown parameters are
/// ignored.
pub open spec fn tp_apply(acc: TP, id: u64, v: Seq<u8>) -> Option<TP> {
    if id == 0x00 {
        if acc.original_dcid is Some || v.len() > MAX_CID_LEN {
            None
        } else {
            Some(TP { original_dcid: Some(v), ..acc })
        }
    } else if id == 0x01 {
        if acc.max_idle_timeout is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { max_idle_timeout: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x02 {
        if acc.stateless_reset_token is Some || v.len() != 16 {
            None
        } else {
            Some(TP { stateless_reset_token: Some(v), ..acc })
        }
    } else if id == 0x03 {
        if acc.max_udp_payload_size is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x >= 1200) {
                    None
                } else {
                    Some(TP { max_udp_payload_size: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x04 {
        if acc.initial_max_data is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { initial_max_data: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x05 {
        if acc.initial_max_stream_data_bidi_local is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { initial_max_stream_data_bidi_local: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x06 {
        if acc.initial_max_stream_data_bidi_remote is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { initial_max_stream_data_bidi_remote: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x07 {
        if acc.initial_max_stream_data_uni is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { initial_max_stream_data_uni: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x08 {
        if acc.initial_max_streams_bidi is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x <= MAX_STREAMS_LIMIT) {
                    None
                } else {
                    Some(TP { initial_max_streams_bidi: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x09 {
        if acc.initial_max_streams_uni is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x <= MAX_STREAMS_LIMIT) {
                    None
                } else {
                    Some(TP { initial_max_streams_uni: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x0a {
        if acc.ack_delay_exponent is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x <= 20) {
                    None
                } else {
                    Some(TP { ack_delay_exponent: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x0b {
        if acc.max_ack_delay is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x < 0x4000) {
                    None
                } else {
                    Some(TP { max_ack_delay: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x0c {
        if acc.disable_active_migration || v.len() != 0 {
            None
        } else {
            Some(TP { disable_active_migration: true, ..acc })
        }
    } else if id == 0x0d {
        if acc.preferred_address is Some {
            None
        } else {
            match pref_parse(v) {
                None => None,
                Some(a) => Some(TP { preferred_address: Some(a), ..acc }),
            }
        }
    } else if id == 0x0e {
        if acc.active_connection_id_limit is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if !(x >= 2) {
                    None
                } else {
                    Some(TP { active_connection_id_limit: Some(x), ..acc })
                },
            }
        }
    } else if id == 0x0f {
        if acc.initial_scid is Some || v.len() > MAX_CID_LEN {
            None
        } else {
            Some(TP { initial_scid: Some(v), ..acc })
        }
    } else if id == 0x10 {
        if acc.retry_scid is Some || v.len() > MAX_CID_LEN {
            None
        } else {
            Some(TP { retry_scid: Some(v), ..acc })
        }
    } else if id == 0x20 {
        if acc.max_datagram_frame_size is Some {
            None
        } else {
            match tp_int(v) {
                None => None,
                Some(x) => if false {
                    None
                } else {
                    Some(TP { max_datagram_frame_size: Some(x), ..acc })
                },
            }
        }
    } else {
        Some(acc)
    }
}

/// One parameter at `p`: its ID, its value and the position after it.
pub open spec fn tp_entry(b: Seq<u8>, p: int) -> Option<(u64, Seq<u8>, int)> {
    match varint(b, p) {
        None => None,
        Some((id, p1)) => match bytes_len(b, p1) {
            None => None,
            Some((v, p2)) => Some((id, v, p2)),
        },
    }
}

/// The parameters from `p` to the end of `b`, added to `acc`.
pub open spec fn tp_parse(b: Seq<u8>, p: int, acc: TP) -> Option<TP>
    decreases b.len() - p,
{
    if p < 0 || p > b.len() {
        None
    } else if p == b.len() {
        Some(acc)
    } else {
        match tp_entry(b, p) {
            None => None,
            Some((id, v, e)) => if e <= p {
                None
            } else {
                match tp_apply(acc, id, v) {
                    None => None,
                    Some(a) => tp_parse(b, e, a),
                }
            },
        }
    }
}

/// The transport parameters encoded in `b` (§18).
pub open spec fn transport_params(b: Seq<u8>) -> Option<TP> {
    tp_parse(b, 0, tp_empty())
}

/// A client sent none of the parameters only a server may send (§18.2):
/// otherwise a connection error of type TRANSPORT_PARAMETER_ERROR.
pub open spec fn tp_client_ok(t: TP) -> bool {
    t.original_dcid is None && t.stateless_reset_token is None && t.preferred_address is None
        && t.retry_scid is None
}

/// The encoding of one parameter.
pub open spec fn tp_entry_enc(id: u64, v: Seq<u8>) -> Seq<u8> {
    varint_enc(id) + bytes_len_enc(v)
}

/// The encoding of parameter `k` of `t`, in ID order (empty if absent).
pub open spec fn tp_field_enc(t: TP, k: int) -> Seq<u8> {
    if k == 0 {
        match t.original_dcid { None => Seq::empty(), Some(v) => tp_entry_enc(0x00, v) }
    } else if k == 1 {
        match t.max_idle_timeout { None => Seq::empty(), Some(x) => tp_entry_enc(0x01, varint_enc(x)) }
    } else if k == 2 {
        match t.stateless_reset_token { None => Seq::empty(), Some(v) => tp_entry_enc(0x02, v) }
    } else if k == 3 {
        match t.max_udp_payload_size { None => Seq::empty(), Some(x) => tp_entry_enc(0x03, varint_enc(x)) }
    } else if k == 4 {
        match t.initial_max_data { None => Seq::empty(), Some(x) => tp_entry_enc(0x04, varint_enc(x)) }
    } else if k == 5 {
        match t.initial_max_stream_data_bidi_local { None => Seq::empty(), Some(x) => tp_entry_enc(0x05, varint_enc(x)) }
    } else if k == 6 {
        match t.initial_max_stream_data_bidi_remote { None => Seq::empty(), Some(x) => tp_entry_enc(0x06, varint_enc(x)) }
    } else if k == 7 {
        match t.initial_max_stream_data_uni { None => Seq::empty(), Some(x) => tp_entry_enc(0x07, varint_enc(x)) }
    } else if k == 8 {
        match t.initial_max_streams_bidi { None => Seq::empty(), Some(x) => tp_entry_enc(0x08, varint_enc(x)) }
    } else if k == 9 {
        match t.initial_max_streams_uni { None => Seq::empty(), Some(x) => tp_entry_enc(0x09, varint_enc(x)) }
    } else if k == 10 {
        match t.ack_delay_exponent { None => Seq::empty(), Some(x) => tp_entry_enc(0x0a, varint_enc(x)) }
    } else if k == 11 {
        match t.max_ack_delay { None => Seq::empty(), Some(x) => tp_entry_enc(0x0b, varint_enc(x)) }
    } else if k == 12 {
        if t.disable_active_migration { tp_entry_enc(0x0c, Seq::empty()) } else { Seq::empty() }
    } else if k == 13 {
        match t.preferred_address { None => Seq::empty(), Some(a) => tp_entry_enc(0x0d, pref_enc(a)) }
    } else if k == 14 {
        match t.active_connection_id_limit { None => Seq::empty(), Some(x) => tp_entry_enc(0x0e, varint_enc(x)) }
    } else if k == 15 {
        match t.initial_scid { None => Seq::empty(), Some(v) => tp_entry_enc(0x0f, v) }
    } else if k == 16 {
        match t.retry_scid { None => Seq::empty(), Some(v) => tp_entry_enc(0x10, v) }
    } else if k == 17 {
        match t.max_datagram_frame_size { None => Seq::empty(), Some(x) => tp_entry_enc(0x20, varint_enc(x)) }
    } else {
        Seq::empty()
    }
}

/// The encodings of parameters `k..18` of `t`.
pub open spec fn tp_enc_from(t: TP, k: nat) -> Seq<u8>
    decreases 18 - k,
{
    if k >= 18 {
        Seq::empty()
    } else {
        tp_field_enc(t, k as int) + tp_enc_from(t, k + 1)
    }
}

/// The encoding of transport parameters, in ID order, with the shortest
/// integers.
pub open spec fn transport_params_enc(t: TP) -> Seq<u8> {
    tp_enc_from(t, 0)
}

/// Transport parameters that can be encoded and parse back.
pub open spec fn tp_wf(t: TP) -> bool {
    &&& (t.original_dcid matches Some(v) ==> v.len() <= MAX_CID_LEN)
    &&& (t.max_idle_timeout matches Some(x) ==> vi(x))
    &&& (t.stateless_reset_token matches Some(v) ==> v.len() == 16)
    &&& (t.max_udp_payload_size matches Some(x) ==> vi(x) && x >= 1200)
    &&& (t.initial_max_data matches Some(x) ==> vi(x))
    &&& (t.initial_max_stream_data_bidi_local matches Some(x) ==> vi(x))
    &&& (t.initial_max_stream_data_bidi_remote matches Some(x) ==> vi(x))
    &&& (t.initial_max_stream_data_uni matches Some(x) ==> vi(x))
    &&& (t.initial_max_streams_bidi matches Some(x) ==> vi(x) && x <= MAX_STREAMS_LIMIT)
    &&& (t.initial_max_streams_uni matches Some(x) ==> vi(x) && x <= MAX_STREAMS_LIMIT)
    &&& (t.ack_delay_exponent matches Some(x) ==> vi(x) && x <= 20)
    &&& (t.max_ack_delay matches Some(x) ==> vi(x) && x < 0x4000)
    &&& (t.preferred_address matches Some(a) ==> a.v4.len() == 6 && a.v6.len() == 18 && 1 <= a.cid.len() <= 20 && a.token.len() == 16)
    &&& (t.active_connection_id_limit matches Some(x) ==> vi(x) && x >= 2)
    &&& (t.initial_scid matches Some(v) ==> v.len() <= MAX_CID_LEN)
    &&& (t.retry_scid matches Some(v) ==> v.len() <= MAX_CID_LEN)
    &&& (t.max_datagram_frame_size matches Some(x) ==> vi(x))
}

/// `t` with parameters `k..` removed.
pub open spec fn tp_upto(t: TP, k: nat) -> TP {
    TP {
        original_dcid: if k > 0 { t.original_dcid } else { None },
        max_idle_timeout: if k > 1 { t.max_idle_timeout } else { None },
        stateless_reset_token: if k > 2 { t.stateless_reset_token } else { None },
        max_udp_payload_size: if k > 3 { t.max_udp_payload_size } else { None },
        initial_max_data: if k > 4 { t.initial_max_data } else { None },
        initial_max_stream_data_bidi_local: if k > 5 { t.initial_max_stream_data_bidi_local } else { None },
        initial_max_stream_data_bidi_remote: if k > 6 { t.initial_max_stream_data_bidi_remote } else { None },
        initial_max_stream_data_uni: if k > 7 { t.initial_max_stream_data_uni } else { None },
        initial_max_streams_bidi: if k > 8 { t.initial_max_streams_bidi } else { None },
        initial_max_streams_uni: if k > 9 { t.initial_max_streams_uni } else { None },
        ack_delay_exponent: if k > 10 { t.ack_delay_exponent } else { None },
        max_ack_delay: if k > 11 { t.max_ack_delay } else { None },
        disable_active_migration: if k > 12 { t.disable_active_migration } else { false },
        preferred_address: if k > 13 { t.preferred_address } else { None },
        active_connection_id_limit: if k > 14 { t.active_connection_id_limit } else { None },
        initial_scid: if k > 15 { t.initial_scid } else { None },
        retry_scid: if k > 16 { t.retry_scid } else { None },
        max_datagram_frame_size: if k > 17 { t.max_datagram_frame_size } else { None },
    }
}

} // verus!
