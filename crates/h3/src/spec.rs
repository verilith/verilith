//! The specification: HTTP/3 framing (RFC 9114) as pure functions. Everything
//! here is trusted: it is what the proofs prove the code computes. Read it
//! against the RFC; the section numbers below are RFC 9114's unless they say
//! otherwise.
//!
//! - Variable-length integers (RFC 9000 §16): the two high bits of the first
//!   byte give the length, 1, 2, 4 or 8 bytes, and the value is the rest in
//!   network byte order. Any length may be used for any value it can hold
//!   (only QUIC's own frame types must be minimal, and those are not HTTP/3
//!   frames); the encoder always uses the shortest.
//! - Frames (§7.1, §7.2): type, length, payload. A payload must hold exactly
//!   the fields its type defines (§7.1): CANCEL_PUSH, GOAWAY and MAX_PUSH_ID
//!   hold one varint, PUSH_PROMISE a varint and a field section, SETTINGS
//!   pairs of varints. DATA, HEADERS and frames of unknown type are opaque.
//! - SETTINGS (§7.2.4): the identifiers HTTP/2 used and HTTP/3 reserved
//!   (0x00, 0x02 to 0x05) are errors, as are values other than 0 and 1 for
//!   the two boolean settings understood here (RFC 9220 and RFC 9297);
//!   other unknown identifiers are ignored. A repeated identifier is an
//!   error for the settings understood here (the RFC allows treating any
//!   repeat as an error); repeats of ignored ones stay ignored.
//! - Unidirectional stream types (§6.2, RFC 9204 §4.2): control, push and
//!   the two QPACK streams. A push stream from a client is an error; QPACK
//!   and unknown stream types are handed back to the caller.
//! - The frame-order rules of each stream (§4.1, §6.2.1, §7.2): SETTINGS
//!   first and only once on the control stream; no message frames there; a
//!   message is HEADERS, DATA*, and optional trailing HEADERS; frames
//!   HTTP/2 used and HTTP/3 reserved are errors anywhere; unknown frame types
//!   are allowed anywhere except first on the control stream. GOAWAY IDs
//!   must not increase, and from a server must be client bidirectional
//!   stream IDs; MAX_PUSH_ID must not decrease, and only a server receives
//!   it; a CANCEL_PUSH a server receives must be within the MAX_PUSH_ID it
//!   was sent.
//! - Implementation limits: a HEADERS, PUSH_PROMISE or SETTINGS payload
//!   longer than the reader's limit is H3_EXCESSIVE_LOAD (these are
//!   buffered whole; DATA and unknown frames are streamed and have no limit),
//!   and a CANCEL_PUSH, GOAWAY or MAX_PUSH_ID payload that is empty or longer
//!   than 8 bytes is H3_FRAME_ERROR as soon as its header is read, since no
//!   such payload can hold exactly one varint.
//! - A stream's end (§4.1, §6.2.1, §7.1): mid-frame is H3_FRAME_ERROR; the
//!   control stream ending at all is H3_CLOSED_CRITICAL_STREAM; a request
//!   stream that ends before its HEADERS is H3_REQUEST_INCOMPLETE, and a
//!   response or push stream that does is H3_MESSAGE_ERROR (our choice: the
//!   RFC names no code for it). A unidirectional stream may end before its
//!   type (§6.2).
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// The largest varint: 2^62 - 1.
pub const MAX_VARINT: u64 = 0x3FFF_FFFF_FFFF_FFFF;

/// Frame types (§7.2, §11.2.1).
pub const DATA: u64 = 0x00;
pub const HEADERS: u64 = 0x01;
pub const CANCEL_PUSH: u64 = 0x03;
pub const SETTINGS: u64 = 0x04;
pub const PUSH_PROMISE: u64 = 0x05;
pub const GOAWAY: u64 = 0x07;
pub const MAX_PUSH_ID: u64 = 0x0d;

/// Unidirectional stream types (§6.2, RFC 9204 §4.2).
pub const STREAM_CONTROL: u64 = 0x00;
pub const STREAM_PUSH: u64 = 0x01;
pub const STREAM_QPACK_ENCODER: u64 = 0x02;
pub const STREAM_QPACK_DECODER: u64 = 0x03;

/// Settings (§7.2.4.1, RFC 9204 §5, RFC 9220 §5, RFC 9297 §2.1.1).
pub const SETTINGS_QPACK_MAX_TABLE_CAPACITY: u64 = 0x01;
pub const SETTINGS_MAX_FIELD_SECTION_SIZE: u64 = 0x06;
pub const SETTINGS_QPACK_BLOCKED_STREAMS: u64 = 0x07;
pub const SETTINGS_ENABLE_CONNECT_PROTOCOL: u64 = 0x08;
pub const SETTINGS_H3_DATAGRAM: u64 = 0x33;

/// Error codes (§8.1).
pub const H3_NO_ERROR: u64 = 0x0100;
pub const H3_GENERAL_PROTOCOL_ERROR: u64 = 0x0101;
pub const H3_INTERNAL_ERROR: u64 = 0x0102;
pub const H3_STREAM_CREATION_ERROR: u64 = 0x0103;
pub const H3_CLOSED_CRITICAL_STREAM: u64 = 0x0104;
pub const H3_FRAME_UNEXPECTED: u64 = 0x0105;
pub const H3_FRAME_ERROR: u64 = 0x0106;
pub const H3_EXCESSIVE_LOAD: u64 = 0x0107;
pub const H3_ID_ERROR: u64 = 0x0108;
pub const H3_SETTINGS_ERROR: u64 = 0x0109;
pub const H3_MISSING_SETTINGS: u64 = 0x010a;
pub const H3_REQUEST_REJECTED: u64 = 0x010b;
pub const H3_REQUEST_CANCELLED: u64 = 0x010c;
pub const H3_REQUEST_INCOMPLETE: u64 = 0x010d;
pub const H3_MESSAGE_ERROR: u64 = 0x010e;
pub const H3_CONNECT_ERROR: u64 = 0x010f;
pub const H3_VERSION_FALLBACK: u64 = 0x0110;

// ---------------------------------------------------------------------------
// Variable-length integers (RFC 9000 §16)
// ---------------------------------------------------------------------------

/// 256^n.
pub open spec fn p256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * p256((n - 1) as nat)
    }
}

/// The big-endian value of `s[0..n]`.
pub open spec fn be(s: Seq<u8>, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        be(s, (n - 1) as nat) * 256 + s[n - 1] as nat
    }
}

/// The length of a varint, from its first byte's two high bits.
pub open spec fn var_len(b: u8) -> nat {
    if b < 0x40 {
        1
    } else if b < 0x80 {
        2
    } else if b < 0xc0 {
        4
    } else {
        8
    }
}

pub enum Var {
    /// `s` ends inside the varint.
    Short,
    /// The value, and the varint's length in bytes.
    Ok(nat, nat),
}

/// The varint at the start of `s`: its bytes with the two length bits of
/// the first cleared, in network byte order.
pub open spec fn var_dec(s: Seq<u8>) -> Var {
    if s.len() == 0 {
        Var::Short
    } else if s.len() < var_len(s[0]) {
        Var::Short
    } else {
        Var::Ok(be(s.update(0, s[0] % 64), var_len(s[0])), var_len(s[0]))
    }
}

/// The shortest varint length that holds `v`.
pub open spec fn var_size(v: nat) -> nat {
    if v < 0x40 {
        1
    } else if v < 0x4000 {
        2
    } else if v < 0x4000_0000 {
        4
    } else {
        8
    }
}

/// `v mod 256^n` in `n` bytes, big-endian.
pub open spec fn be_enc(v: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        be_enc(v / 256, (n - 1) as nat).push((v % 256) as u8)
    }
}

/// The two length bits for an `n`-byte varint, in place in the first byte.
pub open spec fn var_tag(n: nat) -> nat {
    if n == 1 {
        0
    } else if n == 2 {
        0x40
    } else if n == 4 {
        0x80
    } else {
        0xc0
    }
}

/// The shortest encoding of `v` (which must be at most `MAX_VARINT`).
pub open spec fn var_enc(v: nat) -> Seq<u8> {
    let n = var_size(v);
    let b = be_enc(v, n);
    b.update(0, (b[0] + var_tag(n)) as u8)
}

// ---------------------------------------------------------------------------
// Frames (§7)
// ---------------------------------------------------------------------------

pub enum Hdr {
    /// `s` ends inside the type or the length.
    Short,
    /// The type, the payload length and the header's length in bytes.
    Ok(nat, nat, nat),
}

/// The frame header at the start of `s` (§7.1).
pub open spec fn hdr_dec(s: Seq<u8>) -> Hdr {
    match var_dec(s) {
        Var::Short => Hdr::Short,
        Var::Ok(t, n) => match var_dec(s.skip(n as int)) {
            Var::Short => Hdr::Short,
            Var::Ok(len, m) => Hdr::Ok(t, len, n + m),
        },
    }
}

/// What a frame type means to the framing layer.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Kind {
    Data,
    Headers,
    CancelPush,
    Settings,
    PushPromise,
    Goaway,
    MaxPushId,
    /// The types HTTP/2 used and HTTP/3 reserved (0x02, 0x06, 0x08, 0x09:
    /// §7.2.8, §11.2.1): an error wherever they are received.
    H2,
    /// Any other type, including the reserved `0x1f * N + 0x21` ones
    /// (§7.2.8): ignored (§9).
    Other,
}

pub open spec fn kind(t: nat) -> Kind {
    if t == DATA {
        Kind::Data
    } else if t == HEADERS {
        Kind::Headers
    } else if t == CANCEL_PUSH {
        Kind::CancelPush
    } else if t == SETTINGS {
        Kind::Settings
    } else if t == PUSH_PROMISE {
        Kind::PushPromise
    } else if t == GOAWAY {
        Kind::Goaway
    } else if t == MAX_PUSH_ID {
        Kind::MaxPushId
    } else if t == 0x02 || t == 0x06 || t == 0x08 || t == 0x09 {
        Kind::H2
    } else {
        Kind::Other
    }
}

/// The payload of CANCEL_PUSH, GOAWAY and MAX_PUSH_ID: exactly one varint
/// (§7.1: a payload with bytes left over, or one that ends early, is
/// H3_FRAME_ERROR).
pub open spec fn single(p: Seq<u8>) -> Option<nat> {
    match var_dec(p) {
        Var::Ok(v, n) if n == p.len() => Some(v),
        _ => None,
    }
}

/// The settings understood here; the others are ignored (§7.2.4).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Settings {
    pub qpack_max_table_capacity: Option<u64>,
    pub max_field_section_size: Option<u64>,
    pub qpack_blocked_streams: Option<u64>,
    pub enable_connect_protocol: Option<u64>,
    pub h3_datagram: Option<u64>,
}

pub open spec fn no_settings() -> Settings {
    Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: None,
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    }
}

/// HTTP/2's setting identifiers that HTTP/3 reserved (§7.2.4.1, §11.2.2).
pub open spec fn h2_setting(id: nat) -> bool {
    id == 0x00 || id == 0x02 || id == 0x03 || id == 0x04 || id == 0x05
}

/// One setting added to `acc`: `Err` is the error code.
pub open spec fn setting(acc: Settings, id: nat, v: nat) -> Result<Settings, u64> {
    if h2_setting(id) {
        Err(H3_SETTINGS_ERROR)
    } else if id == SETTINGS_QPACK_MAX_TABLE_CAPACITY {
        if acc.qpack_max_table_capacity is Some {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { qpack_max_table_capacity: Some(v as u64), ..acc })
        }
    } else if id == SETTINGS_MAX_FIELD_SECTION_SIZE {
        if acc.max_field_section_size is Some {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { max_field_section_size: Some(v as u64), ..acc })
        }
    } else if id == SETTINGS_QPACK_BLOCKED_STREAMS {
        if acc.qpack_blocked_streams is Some {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { qpack_blocked_streams: Some(v as u64), ..acc })
        }
    } else if id == SETTINGS_ENABLE_CONNECT_PROTOCOL {
        if acc.enable_connect_protocol is Some || v > 1 {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { enable_connect_protocol: Some(v as u64), ..acc })
        }
    } else if id == SETTINGS_H3_DATAGRAM {
        if acc.h3_datagram is Some || v > 1 {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { h3_datagram: Some(v as u64), ..acc })
        }
    } else {
        Ok(acc)
    }
}

/// A SETTINGS payload, read on from `acc`: zero or more (identifier,
/// value) pairs filling it exactly (§7.2.4).
pub open spec fn settings_from(p: Seq<u8>, acc: Settings) -> Result<Settings, u64>
    decreases p.len(),
{
    if p.len() == 0 {
        Ok(acc)
    } else {
        match var_dec(p) {
            Var::Short => Err(H3_FRAME_ERROR),
            Var::Ok(id, n) => match var_dec(p.skip(n as int)) {
                Var::Short => Err(H3_FRAME_ERROR),
                Var::Ok(v, m) => match setting(acc, id, v) {
                    Err(e) => Err(e),
                    Ok(acc2) => settings_from(p.skip((n + m) as int), acc2),
                },
            },
        }
    }
}

pub open spec fn settings_dec(p: Seq<u8>) -> Result<Settings, u64> {
    settings_from(p, no_settings())
}

// ---------------------------------------------------------------------------
// Unidirectional stream types (§6.2)
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum UniKind {
    Control,
    Push,
    QpackEncoder,
    QpackDecoder,
    /// Unknown, including the reserved `0x1f * N + 0x21` types (§6.2.3):
    /// the receiver must discard it or abort reading, and must not treat it
    /// as a connection error.
    Other,
}

pub open spec fn uni_kind(t: nat) -> UniKind {
    if t == STREAM_CONTROL {
        UniKind::Control
    } else if t == STREAM_PUSH {
        UniKind::Push
    } else if t == STREAM_QPACK_ENCODER {
        UniKind::QpackEncoder
    } else if t == STREAM_QPACK_DECODER {
        UniKind::QpackDecoder
    } else {
        UniKind::Other
    }
}

// ---------------------------------------------------------------------------
// The frame-order rules (§4.1, §6.2.1, §7.2)
// ---------------------------------------------------------------------------

/// Where a message is (§4.1): before its HEADERS, after HEADERS and before
/// any DATA, in its DATA, or after its trailing HEADERS.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Phase {
    Start,
    Head,
    Body,
    Done,
}

/// The order state of a framed stream, as its receiver sees it.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Order {
    /// The peer's control stream: whether SETTINGS has been received, the
    /// last GOAWAY ID and the last MAX_PUSH_ID.
    Control { settings: bool, goaway: Option<u64>, max_push: Option<u64> },
    /// A request stream, at the server.
    Request(Phase),
    /// A request stream's response, at the client. Interim (1xx) responses
    /// are HEADERS frames too (§4.1): any number of HEADERS may come
    /// before the first DATA. Telling a final response from an interim one
    /// takes the decoded `:status`, so that is the message layer's check
    /// (§4.1: a second final response is malformed).
    Response(Phase),
    /// A push stream, at the client (§4.6): a response.
    Push(Phase),
}

/// The control stream's state when it starts.
pub open spec fn control0() -> Order {
    Order::Control { settings: false, goaway: None, max_push: None }
}

pub open spec fn with_phase(o: Order, p: Phase) -> Order {
    match o {
        Order::Request(_) => Order::Request(p),
        Order::Response(_) => Order::Response(p),
        Order::Push(_) => Order::Push(p),
        Order::Control { .. } => o,
    }
}

/// A frame of type `t` and payload length `len`, received by a server (or
/// by a client if `!server`) on a stream in state `o`, read only as far as
/// its header: the error code, or the state while its payload is read.
pub open spec fn accept(o: Order, server: bool, limit: nat, t: nat, len: nat) -> Result<Order, u64> {
    let k = kind(t);
    match o {
        Order::Control { settings, goaway, max_push } => {
            if !settings {
                if k != Kind::Settings {
                    Err(H3_MISSING_SETTINGS)
                } else if len > limit {
                    Err(H3_EXCESSIVE_LOAD)
                } else {
                    Ok(Order::Control { settings: true, goaway, max_push })
                }
            } else {
                match k {
                    Kind::CancelPush | Kind::Goaway => {
                        if len == 0 || len > 8 {
                            Err(H3_FRAME_ERROR)
                        } else {
                            Ok(o)
                        }
                    },
                    Kind::MaxPushId => {
                        if !server {
                            Err(H3_FRAME_UNEXPECTED)
                        } else if len == 0 || len > 8 {
                            Err(H3_FRAME_ERROR)
                        } else {
                            Ok(o)
                        }
                    },
                    Kind::Other => Ok(o),
                    _ => Err(H3_FRAME_UNEXPECTED),
                }
            }
        },
        Order::Request(p) | Order::Response(p) | Order::Push(p) => {
            match k {
                Kind::Data => match p {
                    Phase::Head | Phase::Body => Ok(with_phase(o, Phase::Body)),
                    _ => Err(H3_FRAME_UNEXPECTED),
                },
                Kind::Headers => {
                    if p == Phase::Done {
                        Err(H3_FRAME_UNEXPECTED)
                    } else if len > limit {
                        Err(H3_EXCESSIVE_LOAD)
                    } else if p == Phase::Start {
                        Ok(with_phase(o, Phase::Head))
                    } else if p == Phase::Head && !(o is Request) {
                        Ok(o)
                    } else {
                        Ok(with_phase(o, Phase::Done))
                    }
                },
                // Only on request streams, and only from a server (§7.2.5).
                Kind::PushPromise => {
                    if !(o is Response) {
                        Err(H3_FRAME_UNEXPECTED)
                    } else if len > limit {
                        Err(H3_EXCESSIVE_LOAD)
                    } else {
                        Ok(o)
                    }
                },
                Kind::Other => Ok(o),
                _ => Err(H3_FRAME_UNEXPECTED),
            }
        },
    }
}

/// Whether a frame of kind `k` is read whole (and then `complete`d) rather
/// than streamed.
pub open spec fn buffered(k: Kind) -> bool {
    !(k == Kind::Data || k == Kind::Other || k == Kind::H2)
}

/// What a stream reports, besides DATA payloads.
pub enum Ev {
    /// A unidirectional stream's type.
    StreamType(u64),
    /// A push stream's push ID (§4.6).
    PushId(u64),
    /// A HEADERS payload: an encoded field section.
    Headers(Seq<u8>),
    /// A PUSH_PROMISE: the push ID and the encoded field section.
    PushPromise(u64, Seq<u8>),
    Settings(Settings),
    CancelPush(u64),
    Goaway(u64),
    MaxPushId(u64),
}

/// A buffered frame's payload `p`, once it has all arrived, in state `o`
/// (after `accept`): the error code, or the state after it and what it
/// reports.
pub open spec fn complete(o: Order, server: bool, k: Kind, p: Seq<u8>) -> Result<(Order, Ev), u64> {
    match k {
        Kind::Headers => Ok((o, Ev::Headers(p))),
        Kind::PushPromise => match var_dec(p) {
            Var::Short => Err(H3_FRAME_ERROR),
            Var::Ok(id, n) => Ok((o, Ev::PushPromise(id as u64, p.skip(n as int)))),
        },
        Kind::Settings => match settings_dec(p) {
            Err(e) => Err(e),
            Ok(s) => Ok((o, Ev::Settings(s))),
        },
        _ => match (single(p), o) {
            (None, _) => Err(H3_FRAME_ERROR),
            (Some(v), Order::Control { settings, goaway, max_push }) => {
                if k == Kind::CancelPush {
                    // A server checks the push ID against the MAX_PUSH_ID
                    // it received (§7.2.3); a client's check needs the
                    // MAX_PUSH_ID it sent, which is the connection's.
                    if server && (max_push is None || v > max_push->0) {
                        Err(H3_ID_ERROR)
                    } else {
                        Ok((o, Ev::CancelPush(v as u64)))
                    }
                } else if k == Kind::Goaway {
                    // From a server: a client-initiated bidirectional
                    // stream ID; IDs never increase (§5.2, §7.2.6).
                    if (!server && v % 4 != 0) || (goaway is Some && v > goaway->0) {
                        Err(H3_ID_ERROR)
                    } else {
                        Ok((Order::Control { settings, goaway: Some(v as u64), max_push }, Ev::Goaway(v as u64)))
                    }
                } else {
                    // MAX_PUSH_ID never decreases (§7.2.7).
                    if max_push is Some && v < max_push->0 {
                        Err(H3_ID_ERROR)
                    } else {
                        Ok((Order::Control { settings, goaway, max_push: Some(v as u64) }, Ev::MaxPushId(v as u64)))
                    }
                }
            },
            _ => Err(H3_FRAME_UNEXPECTED),
        },
    }
}

// ---------------------------------------------------------------------------
// A stream
// ---------------------------------------------------------------------------

/// Where a stream's reader is between units (a stream header field or a
/// frame).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum RSt {
    /// A unidirectional stream, before its type.
    Type,
    /// A push stream, before its push ID.
    PushId,
    /// Between frames.
    Frames(Order),
}

/// One unit at the start of `s`.
pub enum Unit {
    /// `s` ends inside it.
    Incomplete,
    /// It is an error.
    Fail(u64),
    /// A unidirectional stream type HTTP/3 does not frame (QPACK's, or
    /// unknown), and the length of its varint: the rest of the stream is
    /// not ours.
    Handoff(u64, nat),
    /// It is `n` bytes long; the state after it, what it reports, and the
    /// DATA payload it carries.
    Done(RSt, nat, Seq<Ev>, Seq<u8>),
}

pub open spec fn unit(server: bool, limit: nat, s: Seq<u8>, st: RSt) -> Unit {
    match st {
        RSt::Type => match var_dec(s) {
            Var::Short => Unit::Incomplete,
            Var::Ok(t, n) => match uni_kind(t) {
                UniKind::Control => Unit::Done(RSt::Frames(control0()), n, seq![Ev::StreamType(t as u64)], seq![]),
                UniKind::Push => {
                    if server {
                        Unit::Fail(H3_STREAM_CREATION_ERROR)
                    } else {
                        Unit::Done(RSt::PushId, n, seq![Ev::StreamType(t as u64)], seq![])
                    }
                },
                _ => Unit::Handoff(t as u64, n),
            },
        },
        RSt::PushId => match var_dec(s) {
            Var::Short => Unit::Incomplete,
            Var::Ok(id, n) => Unit::Done(RSt::Frames(Order::Push(Phase::Start)), n, seq![Ev::PushId(id as u64)], seq![]),
        },
        RSt::Frames(o) => match hdr_dec(s) {
            Hdr::Short => Unit::Incomplete,
            Hdr::Ok(t, len, h) => match accept(o, server, limit, t, len) {
                Err(e) => Unit::Fail(e),
                Ok(o2) => {
                    if s.len() < h + len {
                        Unit::Incomplete
                    } else {
                        let p = s.subrange(h as int, (h + len) as int);
                        if !buffered(kind(t)) {
                            Unit::Done(RSt::Frames(o2), h + len, seq![], if kind(t) == Kind::Data { p } else { seq![] })
                        } else {
                            match complete(o2, server, kind(t), p) {
                                Err(e) => Unit::Fail(e),
                                Ok((o3, ev)) => Unit::Done(RSt::Frames(o3), h + len, seq![ev], seq![]),
                            }
                        }
                    }
                },
            },
        },
    }
}

pub enum Tail {
    /// Every unit before offset `q` is complete, and the stream so far ends
    /// inside the unit at `q` (or at it), read in state `st`.
    At(RSt, nat),
    Fail(u64),
    /// From the end of the stream type at offset `q` on, the stream is not
    /// HTTP/3 framed.
    Handoff(u64, nat),
}

pub struct Out {
    /// What the stream reports, in order.
    pub ev: Seq<Ev>,
    /// The payloads of its complete DATA frames.
    pub body: Seq<u8>,
    pub tail: Tail,
}

pub open spec fn shift(t: Tail, n: nat) -> Tail {
    match t {
        Tail::At(st, q) => Tail::At(st, q + n),
        Tail::Fail(e) => Tail::Fail(e),
        Tail::Handoff(k, q) => Tail::Handoff(k, q + n),
    }
}

/// The stream `s` (all that has arrived of it), read from state `st`.
pub open spec fn run(server: bool, limit: nat, s: Seq<u8>, st: RSt) -> Out
    decreases s.len(),
{
    match unit(server, limit, s, st) {
        Unit::Incomplete => Out { ev: seq![], body: seq![], tail: Tail::At(st, 0) },
        Unit::Fail(e) => Out { ev: seq![], body: seq![], tail: Tail::Fail(e) },
        Unit::Handoff(t, n) => Out { ev: seq![Ev::StreamType(t)], body: seq![], tail: Tail::Handoff(t, n) },
        Unit::Done(st2, n, ev, d) => {
            if n == 0 || n > s.len() {
                // Not reached: a unit is at least one byte, and inside s.
                Out { ev: seq![], body: seq![], tail: Tail::Fail(H3_INTERNAL_ERROR) }
            } else {
                let r = run(server, limit, s.skip(n as int), st2);
                Out { ev: ev + r.ev, body: d + r.body, tail: shift(r.tail, n) }
            }
        },
    }
}

/// The DATA payload bytes received so far of an incomplete DATA frame at
/// the start of `s`.
pub open spec fn partial_data(server: bool, limit: nat, s: Seq<u8>, st: RSt) -> Seq<u8> {
    match (st, hdr_dec(s)) {
        (RSt::Frames(o), Hdr::Ok(t, len, h)) => {
            if kind(t) == Kind::Data && accept(o, server, limit, t, len) is Ok && h <= s.len() {
                s.skip(h as int)
            } else {
                seq![]
            }
        },
        _ => seq![],
    }
}

/// How a stream may begin: a unidirectional stream with its type, or a
/// request stream (bidirectional, client-initiated) at the server, or at
/// the client (its response).
pub open spec fn start(uni: bool, server: bool) -> RSt {
    if uni {
        RSt::Type
    } else if server {
        RSt::Frames(Order::Request(Phase::Start))
    } else {
        RSt::Frames(Order::Response(Phase::Start))
    }
}

/// The outcome of the stream `s` ending cleanly (a QUIC FIN) in state `st`
/// with the incomplete unit `rest`.
pub open spec fn at_fin(st: RSt, rest: Seq<u8>) -> Result<(), u64> {
    match st {
        // §6.2: a unidirectional stream may end before its type.
        RSt::Type => Ok(()),
        RSt::PushId => Err(H3_MESSAGE_ERROR),
        RSt::Frames(o) => {
            if rest.len() > 0 {
                // §7.1: the last frame was truncated.
                Err(H3_FRAME_ERROR)
            } else {
                match o {
                    Order::Control { .. } => Err(H3_CLOSED_CRITICAL_STREAM),
                    Order::Request(Phase::Start) => Err(H3_REQUEST_INCOMPLETE),
                    Order::Response(Phase::Start) | Order::Push(Phase::Start) => Err(H3_MESSAGE_ERROR),
                    _ => Ok(()),
                }
            }
        },
    }
}

/// The stream `s`, ended cleanly.
pub open spec fn end_of(server: bool, limit: nat, s: Seq<u8>, st: RSt) -> Result<(), u64> {
    match run(server, limit, s, st).tail {
        Tail::Fail(e) => Err(e),
        Tail::Handoff(..) => Ok(()),
        Tail::At(st2, q) => at_fin(st2, s.skip(q as int)),
    }
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// A frame, as a sender builds it.
pub enum Frame {
    Data(Seq<u8>),
    Headers(Seq<u8>),
    CancelPush(nat),
    Settings(Settings),
    PushPromise(nat, Seq<u8>),
    Goaway(nat),
    MaxPushId(nat),
    /// A frame of a type this layer ignores, such as a reserved one.
    Other(nat, Seq<u8>),
}

/// A setting, if present: its identifier and value, encoded.
pub open spec fn setting_enc(id: nat, v: Option<u64>) -> Seq<u8> {
    match v {
        Some(x) => var_enc(id) + var_enc(x as nat),
        None => seq![],
    }
}

/// SETTINGS' payload: the settings present, in identifier order.
pub open spec fn settings_enc(s: Settings) -> Seq<u8> {
    setting_enc(SETTINGS_QPACK_MAX_TABLE_CAPACITY as nat, s.qpack_max_table_capacity) + setting_enc(
        SETTINGS_MAX_FIELD_SECTION_SIZE as nat,
        s.max_field_section_size,
    ) + setting_enc(SETTINGS_QPACK_BLOCKED_STREAMS as nat, s.qpack_blocked_streams) + setting_enc(
        SETTINGS_ENABLE_CONNECT_PROTOCOL as nat,
        s.enable_connect_protocol,
    ) + setting_enc(SETTINGS_H3_DATAGRAM as nat, s.h3_datagram)
}

pub open spec fn frame_type(f: Frame) -> nat {
    match f {
        Frame::Data(_) => DATA as nat,
        Frame::Headers(_) => HEADERS as nat,
        Frame::CancelPush(_) => CANCEL_PUSH as nat,
        Frame::Settings(_) => SETTINGS as nat,
        Frame::PushPromise(..) => PUSH_PROMISE as nat,
        Frame::Goaway(_) => GOAWAY as nat,
        Frame::MaxPushId(_) => MAX_PUSH_ID as nat,
        Frame::Other(t, _) => t,
    }
}

pub open spec fn payload_enc(f: Frame) -> Seq<u8> {
    match f {
        Frame::Data(p) | Frame::Headers(p) | Frame::Other(_, p) => p,
        Frame::CancelPush(v) | Frame::Goaway(v) | Frame::MaxPushId(v) => var_enc(v),
        Frame::Settings(s) => settings_enc(s),
        Frame::PushPromise(id, p) => var_enc(id) + p,
    }
}

pub open spec fn frame_enc(f: Frame) -> Seq<u8> {
    var_enc(frame_type(f)) + var_enc(payload_enc(f).len()) + payload_enc(f)
}

/// A setting value that can be sent: a varint, and 0 or 1 for the boolean
/// ones.
pub open spec fn settings_ok(s: Settings) -> bool {
    &&& (s.qpack_max_table_capacity matches Some(v) ==> v <= MAX_VARINT)
    &&& (s.max_field_section_size matches Some(v) ==> v <= MAX_VARINT)
    &&& (s.qpack_blocked_streams matches Some(v) ==> v <= MAX_VARINT)
    &&& (s.enable_connect_protocol matches Some(v) ==> v <= 1)
    &&& (s.h3_datagram matches Some(v) ==> v <= 1)
}

/// A frame that can be sent: varints in range, an `Other` type that is not
/// one of the types this layer reads, and a payload length that fits a
/// varint.
pub open spec fn frame_ok(f: Frame) -> bool {
    &&& match f {
        Frame::CancelPush(v) | Frame::Goaway(v) | Frame::MaxPushId(v) => v <= MAX_VARINT,
        Frame::PushPromise(id, _) => id <= MAX_VARINT,
        Frame::Settings(s) => settings_ok(s),
        Frame::Other(t, _) => t <= MAX_VARINT && (kind(t) == Kind::Other || kind(t) == Kind::H2),
        _ => true,
    }
    &&& payload_enc(f).len() <= MAX_VARINT
}

} // verus!
