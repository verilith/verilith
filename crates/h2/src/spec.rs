//! The specification: the HTTP/2 frame layer of RFC 9113 (§4, §6) as pure
//! functions. Everything here is trusted: it is what the proofs prove the
//! code computes, and it is the file to read against the RFC.
//!
//! - **The frame header** (§4.1): a 24-bit length, an 8-bit type, 8 bits of
//!   flags, one reserved bit and a 31-bit stream identifier. The reserved
//!   bit is ignored on receipt and sent as 0. Flags a type does not define
//!   are ignored on receipt and sent as 0.
//! - **The frame size** (§4.2): a frame whose length exceeds the receiver's
//!   SETTINGS_MAX_FRAME_SIZE is a connection error of type
//!   FRAME_SIZE_ERROR, decided from the header alone, so no more than that
//!   is ever buffered for one frame. A frame too short for its mandatory
//!   fields is a FRAME_SIZE_ERROR, a connection error for every type that
//!   can change connection state, and a stream error where §6 says so
//!   (PRIORITY).
//! - **The ten frame types** (§6.1 to §6.10), each with the stream
//!   identifier rule, the length rule, padding (§6.1: padding that is the
//!   whole remaining payload or more is a connection PROTOCOL_ERROR), and
//!   the SETTINGS value rules of §6.5.2 (and of RFC 8441 §3 and RFC 9218
//!   §2.1 for the two settings registered since, which are 0 or 1).
//! - **Unknown frame types** (§4.1, §5.5) are returned, not rejected, so
//!   that the connection can ignore them (or use an extension).
//!
//! What a frame means for a stream (its state, flow control, whether a
//! stream may depend on itself, whether a server may receive PUSH_PROMISE)
//! is the connection layer's to decide, not the frame layer's.
use vstd::prelude::*;

verus! {

/// The length of the frame header (§4.1).
pub const HEAD_LEN: u32 = 9;

/// The initial and smallest value of SETTINGS_MAX_FRAME_SIZE (§6.5.2).
pub const MIN_MAX_FRAME_SIZE: u32 = 16384;

/// The largest value of SETTINGS_MAX_FRAME_SIZE (§6.5.2): `2^24 - 1`.
pub const MAX_MAX_FRAME_SIZE: u32 = 16777215;

/// `2^31 - 1`: the largest stream identifier, window increment and window.
pub const MAX_31: u32 = 0x7fff_ffff;

// Frame types (§6). ------------------------------------------------------

pub const DATA: u8 = 0x0;
pub const HEADERS: u8 = 0x1;
pub const PRIORITY: u8 = 0x2;
pub const RST_STREAM: u8 = 0x3;
pub const SETTINGS: u8 = 0x4;
pub const PUSH_PROMISE: u8 = 0x5;
pub const PING: u8 = 0x6;
pub const GOAWAY: u8 = 0x7;
pub const WINDOW_UPDATE: u8 = 0x8;
pub const CONTINUATION: u8 = 0x9;

// Flags (§6). ------------------------------------------------------------

pub const FLAG_END_STREAM: u8 = 0x1;
pub const FLAG_ACK: u8 = 0x1;
pub const FLAG_END_HEADERS: u8 = 0x4;
pub const FLAG_PADDED: u8 = 0x8;
pub const FLAG_PRIORITY: u8 = 0x20;

// Error codes (§7). ------------------------------------------------------

pub const NO_ERROR: u32 = 0x0;
pub const PROTOCOL_ERROR: u32 = 0x1;
pub const INTERNAL_ERROR: u32 = 0x2;
pub const FLOW_CONTROL_ERROR: u32 = 0x3;
pub const SETTINGS_TIMEOUT: u32 = 0x4;
pub const STREAM_CLOSED: u32 = 0x5;
pub const FRAME_SIZE_ERROR: u32 = 0x6;
pub const REFUSED_STREAM: u32 = 0x7;
pub const CANCEL: u32 = 0x8;
pub const COMPRESSION_ERROR: u32 = 0x9;
pub const CONNECT_ERROR: u32 = 0xa;
pub const ENHANCE_YOUR_CALM: u32 = 0xb;
pub const INADEQUATE_SECURITY: u32 = 0xc;
pub const HTTP_1_1_REQUIRED: u32 = 0xd;

// Settings identifiers (§6.5.2, RFC 8441 §3, RFC 9218 §2.1). --------------

pub const SETTINGS_HEADER_TABLE_SIZE: u16 = 0x1;
pub const SETTINGS_ENABLE_PUSH: u16 = 0x2;
pub const SETTINGS_MAX_CONCURRENT_STREAMS: u16 = 0x3;
pub const SETTINGS_INITIAL_WINDOW_SIZE: u16 = 0x4;
pub const SETTINGS_MAX_FRAME_SIZE: u16 = 0x5;
pub const SETTINGS_MAX_HEADER_LIST_SIZE: u16 = 0x6;
pub const SETTINGS_ENABLE_CONNECT_PROTOCOL: u16 = 0x8;
pub const SETTINGS_NO_RFC7540_PRIORITIES: u16 = 0x9;

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

/// The priority fields of HEADERS and PRIORITY (§5.3.2, §6.3). RFC 9113
/// deprecates the scheme they belong to, but the fields are still on the
/// wire and must still be parsed.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Priority {
    /// The E flag.
    pub exclusive: bool,
    /// The stream this one depends on, below `2^31`.
    pub dependency: u32,
    /// The weight, less one.
    pub weight: u8,
}

/// One SETTINGS parameter (§6.5.1).
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Setting {
    /// The identifier. Unknown identifiers are kept, for the connection to
    /// ignore.
    pub id: u16,
    /// The value.
    pub value: u32,
}

/// A frame, as the spec sees it. `pad` is the Pad Length field when the
/// PADDED flag is set; the padding itself is that many bytes, zero when
/// sent and ignored when received.
pub ghost enum Frame {
    Data { stream: u32, end_stream: bool, pad: Option<u8>, data: Seq<u8> },
    Headers {
        stream: u32,
        end_stream: bool,
        end_headers: bool,
        pad: Option<u8>,
        priority: Option<Priority>,
        fragment: Seq<u8>,
    },
    Priority { stream: u32, prio: Priority },
    RstStream { stream: u32, code: u32 },
    Settings { ack: bool, params: Seq<Setting> },
    PushPromise { stream: u32, end_headers: bool, pad: Option<u8>, promised: u32, fragment: Seq<u8> },
    Ping { ack: bool, opaque: u64 },
    GoAway { last_stream: u32, code: u32, debug: Seq<u8> },
    WindowUpdate { stream: u32, increment: u32 },
    Continuation { stream: u32, end_headers: bool, fragment: Seq<u8> },
    /// A frame of a type this layer does not know (`ty >= 10`), whole.
    Unknown { ty: u8, flags: u8, stream: u32, payload: Seq<u8> },
}

/// The result of parsing the start of a byte stream.
pub ghost enum Res {
    /// The frame is not all there yet: at least `need` bytes from the start
    /// are needed to decide.
    Incomplete(nat),
    /// A frame, taking the first `len` bytes.
    Frame(Frame, nat),
    /// A stream error (§5.4.2) on `stream` with `code`; the frame takes the
    /// first `len` bytes and the connection continues after it.
    StreamError(u32, u32, nat),
    /// A connection error (§5.4.1) with `code`.
    ConnError(u32),
}

// ---------------------------------------------------------------------------
// Integers on the wire (network byte order)
// ---------------------------------------------------------------------------

pub open spec fn be16(b: Seq<u8>, i: int) -> u16 {
    ((b[i] as u16) << 8u16) | (b[i + 1] as u16)
}

pub open spec fn be24(b: Seq<u8>, i: int) -> u32 {
    ((b[i] as u32) << 16u32) | ((b[i + 1] as u32) << 8u32) | (b[i + 2] as u32)
}

pub open spec fn be32(b: Seq<u8>, i: int) -> u32 {
    ((b[i] as u32) << 24u32) | ((b[i + 1] as u32) << 16u32) | ((b[i + 2] as u32) << 8u32) | (
    b[i + 3] as u32)
}

pub open spec fn be64(b: Seq<u8>, i: int) -> u64 {
    ((be32(b, i) as u64) << 32u64) | (be32(b, i + 4) as u64)
}

pub open spec fn enc16(x: u16) -> Seq<u8> {
    seq![(x >> 8u16) as u8, x as u8]
}

pub open spec fn enc24(x: u32) -> Seq<u8> {
    seq![(x >> 16u32) as u8, (x >> 8u32) as u8, x as u8]
}

pub open spec fn enc32(x: u32) -> Seq<u8> {
    seq![(x >> 24u32) as u8, (x >> 16u32) as u8, (x >> 8u32) as u8, x as u8]
}

pub open spec fn enc64(x: u64) -> Seq<u8> {
    enc32((x >> 32u64) as u32) + enc32(x as u32)
}

/// `n` zero bytes.
pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

pub open spec fn flag(flags: u8, f: u8) -> bool {
    flags & f != 0
}

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// The frame header (§4.1), the stream identifier without the reserved bit.
pub struct Head {
    pub len: u32,
    pub ty: u8,
    pub flags: u8,
    pub stream: u32,
}

pub open spec fn head(b: Seq<u8>) -> Head {
    Head { len: be24(b, 0), ty: b[3], flags: b[4], stream: be32(b, 5) & MAX_31 }
}

/// The frame at the start of `b`, for a receiver whose
/// SETTINGS_MAX_FRAME_SIZE is `max`.
pub open spec fn parse(b: Seq<u8>, max: u32) -> Res {
    if b.len() < HEAD_LEN {
        Res::Incomplete(HEAD_LEN as nat)
    } else {
        let h = head(b);
        if h.len > max {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else if b.len() < HEAD_LEN + h.len {
            Res::Incomplete((HEAD_LEN + h.len) as nat)
        } else {
            payload(h, b.subrange(HEAD_LEN as int, HEAD_LEN + h.len))
        }
    }
}

/// Padding (§6.1, §6.2, §6.6): with the PADDED flag the first byte is the
/// Pad Length and that many bytes at the end are padding. `fixed` is the
/// length of the fields that follow the Pad Length and precede the data.
/// Returns the Pad Length and the bounds of what is between, or the error.
pub open spec fn unpad(p: Seq<u8>, padded: bool, fixed: nat) -> Result<(Option<u8>, int, int), u32> {
    if !padded {
        if p.len() < fixed {
            Err(FRAME_SIZE_ERROR)
        } else {
            Ok((None, fixed as int, p.len() as int))
        }
    } else if p.len() < 1 + fixed {
        Err(FRAME_SIZE_ERROR)
    } else if p[0] as int > p.len() - 1 - fixed {
        Err(PROTOCOL_ERROR)
    } else {
        Ok((Some(p[0]), 1 + fixed as int, p.len() - p[0] as int))
    }
}

pub open spec fn priority_at(p: Seq<u8>, i: int) -> Priority {
    let w = be32(p, i);
    Priority { exclusive: w & 0x8000_0000 != 0, dependency: w & MAX_31, weight: p[i + 4] }
}

/// The parameters of a SETTINGS payload whose length is a multiple of 6.
pub open spec fn params(p: Seq<u8>) -> Seq<Setting> {
    Seq::new(p.len() / 6, |i: int| Setting { id: be16(p, 6 * i), value: be32(p, 6 * i + 2) })
}

/// The error a SETTINGS value is (§6.5.2), if any.
pub open spec fn setting_error(s: Setting) -> Option<u32> {
    if s.id == SETTINGS_ENABLE_PUSH && s.value > 1 {
        Some(PROTOCOL_ERROR)
    } else if s.id == SETTINGS_INITIAL_WINDOW_SIZE && s.value > MAX_31 {
        Some(FLOW_CONTROL_ERROR)
    } else if s.id == SETTINGS_MAX_FRAME_SIZE && (s.value < MIN_MAX_FRAME_SIZE || s.value
        > MAX_MAX_FRAME_SIZE) {
        Some(PROTOCOL_ERROR)
    } else if (s.id == SETTINGS_ENABLE_CONNECT_PROTOCOL || s.id == SETTINGS_NO_RFC7540_PRIORITIES)
        && s.value > 1 {
        Some(PROTOCOL_ERROR)
    } else {
        None
    }
}

/// The error of the first invalid parameter among the first `n` of `ps`.
pub open spec fn params_error(ps: Seq<Setting>, n: int) -> Option<u32>
    decreases n,
{
    if n <= 0 {
        None
    } else {
        match params_error(ps, n - 1) {
            Some(e) => Some(e),
            None => setting_error(ps[n - 1]),
        }
    }
}

/// The frame with header `h` and payload `p`, `p.len() == h.len`.
pub open spec fn payload(h: Head, p: Seq<u8>) -> Res {
    let n = (HEAD_LEN + h.len) as nat;
    let s = h.stream;
    if h.ty == DATA {
        // §6.1
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else {
            match unpad(p, flag(h.flags, FLAG_PADDED), 0) {
                Err(e) => Res::ConnError(e),
                Ok((pad, a, z)) => Res::Frame(
                    Frame::Data {
                        stream: s,
                        end_stream: flag(h.flags, FLAG_END_STREAM),
                        pad,
                        data: p.subrange(a, z),
                    },
                    n,
                ),
            }
        }
    } else if h.ty == HEADERS {
        // §6.2
        let prio = flag(h.flags, FLAG_PRIORITY);
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else {
            match unpad(p, flag(h.flags, FLAG_PADDED), if prio { 5 } else { 0 }) {
                Err(e) => Res::ConnError(e),
                Ok((pad, a, z)) => Res::Frame(
                    Frame::Headers {
                        stream: s,
                        end_stream: flag(h.flags, FLAG_END_STREAM),
                        end_headers: flag(h.flags, FLAG_END_HEADERS),
                        pad,
                        priority: if prio {
                            Some(priority_at(p, a - 5))
                        } else {
                            None
                        },
                        fragment: p.subrange(a, z),
                    },
                    n,
                ),
            }
        }
    } else if h.ty == PRIORITY {
        // §6.3
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else if h.len != 5 {
            Res::StreamError(s, FRAME_SIZE_ERROR, n)
        } else {
            Res::Frame(Frame::Priority { stream: s, prio: priority_at(p, 0) }, n)
        }
    } else if h.ty == RST_STREAM {
        // §6.4
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else if h.len != 4 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else {
            Res::Frame(Frame::RstStream { stream: s, code: be32(p, 0) }, n)
        }
    } else if h.ty == SETTINGS {
        // §6.5
        let ack = flag(h.flags, FLAG_ACK);
        if s != 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else if ack && h.len != 0 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else if h.len % 6 != 0 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else {
            let ps = params(p);
            match params_error(ps, ps.len() as int) {
                Some(e) => Res::ConnError(e),
                None => Res::Frame(Frame::Settings { ack, params: ps }, n),
            }
        }
    } else if h.ty == PUSH_PROMISE {
        // §6.6
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else {
            match unpad(p, flag(h.flags, FLAG_PADDED), 4) {
                Err(e) => Res::ConnError(e),
                Ok((pad, a, z)) => Res::Frame(
                    Frame::PushPromise {
                        stream: s,
                        end_headers: flag(h.flags, FLAG_END_HEADERS),
                        pad,
                        promised: be32(p, a - 4) & MAX_31,
                        fragment: p.subrange(a, z),
                    },
                    n,
                ),
            }
        }
    } else if h.ty == PING {
        // §6.7
        if s != 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else if h.len != 8 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else {
            Res::Frame(Frame::Ping { ack: flag(h.flags, FLAG_ACK), opaque: be64(p, 0) }, n)
        }
    } else if h.ty == GOAWAY {
        // §6.8
        if s != 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else if h.len < 8 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else {
            Res::Frame(
                Frame::GoAway {
                    last_stream: be32(p, 0) & MAX_31,
                    code: be32(p, 4),
                    debug: p.subrange(8, p.len() as int),
                },
                n,
            )
        }
    } else if h.ty == WINDOW_UPDATE {
        // §6.9
        if h.len != 4 {
            Res::ConnError(FRAME_SIZE_ERROR)
        } else {
            let inc = be32(p, 0) & MAX_31;
            if inc == 0 {
                if s == 0 {
                    Res::ConnError(PROTOCOL_ERROR)
                } else {
                    Res::StreamError(s, PROTOCOL_ERROR, n)
                }
            } else {
                Res::Frame(Frame::WindowUpdate { stream: s, increment: inc }, n)
            }
        }
    } else if h.ty == CONTINUATION {
        // §6.10
        if s == 0 {
            Res::ConnError(PROTOCOL_ERROR)
        } else {
            Res::Frame(
                Frame::Continuation {
                    stream: s,
                    end_headers: flag(h.flags, FLAG_END_HEADERS),
                    fragment: p,
                },
                n,
            )
        }
    } else {
        // §4.1, §5.5
        Res::Frame(Frame::Unknown { ty: h.ty, flags: h.flags, stream: s, payload: p }, n)
    }
}

// ---------------------------------------------------------------------------
// Serializing
// ---------------------------------------------------------------------------

pub open spec fn pad_flag(pad: Option<u8>) -> u8 {
    if pad is Some {
        FLAG_PADDED
    } else {
        0
    }
}

pub open spec fn bit(b: bool, f: u8) -> u8 {
    if b {
        f
    } else {
        0
    }
}

/// `body` with the Pad Length before it and that many zeros after it.
pub open spec fn padded(pad: Option<u8>, body: Seq<u8>) -> Seq<u8> {
    match pad {
        Some(n) => seq![n] + body + zeros(n as nat),
        None => body,
    }
}

pub open spec fn enc_priority(p: Priority) -> Seq<u8> {
    enc32(if p.exclusive {
        p.dependency | 0x8000_0000
    } else {
        p.dependency
    }) + seq![p.weight]
}

pub open spec fn enc_params(ps: Seq<Setting>) -> Seq<u8>
    decreases ps.len(),
{
    if ps.len() == 0 {
        Seq::empty()
    } else {
        enc_params(ps.drop_last()) + enc16(ps.last().id) + enc32(ps.last().value)
    }
}

/// The type, flags and stream identifier `f` is sent with.
pub open spec fn type_of(f: Frame) -> u8 {
    match f {
        Frame::Data { .. } => DATA,
        Frame::Headers { .. } => HEADERS,
        Frame::Priority { .. } => PRIORITY,
        Frame::RstStream { .. } => RST_STREAM,
        Frame::Settings { .. } => SETTINGS,
        Frame::PushPromise { .. } => PUSH_PROMISE,
        Frame::Ping { .. } => PING,
        Frame::GoAway { .. } => GOAWAY,
        Frame::WindowUpdate { .. } => WINDOW_UPDATE,
        Frame::Continuation { .. } => CONTINUATION,
        Frame::Unknown { ty, .. } => ty,
    }
}

pub open spec fn flags_of(f: Frame) -> u8 {
    match f {
        Frame::Data { end_stream, pad, .. } => bit(end_stream, FLAG_END_STREAM) | pad_flag(pad),
        Frame::Headers { end_stream, end_headers, pad, priority, .. } => bit(
            end_stream,
            FLAG_END_STREAM,
        ) | bit(end_headers, FLAG_END_HEADERS) | pad_flag(pad) | bit(
            priority is Some,
            FLAG_PRIORITY,
        ),
        Frame::Settings { ack, .. } => bit(ack, FLAG_ACK),
        Frame::PushPromise { end_headers, pad, .. } => bit(end_headers, FLAG_END_HEADERS)
            | pad_flag(pad),
        Frame::Ping { ack, .. } => bit(ack, FLAG_ACK),
        Frame::Continuation { end_headers, .. } => bit(end_headers, FLAG_END_HEADERS),
        Frame::Unknown { flags, .. } => flags,
        _ => 0,
    }
}

pub open spec fn stream_of(f: Frame) -> u32 {
    match f {
        Frame::Data { stream, .. } => stream,
        Frame::Headers { stream, .. } => stream,
        Frame::Priority { stream, .. } => stream,
        Frame::RstStream { stream, .. } => stream,
        Frame::PushPromise { stream, .. } => stream,
        Frame::WindowUpdate { stream, .. } => stream,
        Frame::Continuation { stream, .. } => stream,
        Frame::Unknown { stream, .. } => stream,
        _ => 0,
    }
}

/// The payload `f` is sent with.
pub open spec fn payload_of(f: Frame) -> Seq<u8> {
    match f {
        Frame::Data { pad, data, .. } => padded(pad, data),
        Frame::Headers { pad, priority, fragment, .. } => padded(
            pad,
            match priority {
                Some(p) => enc_priority(p) + fragment,
                None => fragment,
            },
        ),
        Frame::Priority { prio, .. } => enc_priority(prio),
        Frame::RstStream { code, .. } => enc32(code),
        Frame::Settings { params, .. } => enc_params(params),
        Frame::PushPromise { pad, promised, fragment, .. } => padded(
            pad,
            enc32(promised) + fragment,
        ),
        Frame::Ping { opaque, .. } => enc64(opaque),
        Frame::GoAway { last_stream, code, debug } => enc32(last_stream) + enc32(code) + debug,
        Frame::WindowUpdate { increment, .. } => enc32(increment),
        Frame::Continuation { fragment, .. } => fragment,
        Frame::Unknown { payload, .. } => payload,
    }
}

/// The frame header (§4.1) with the reserved bit 0.
pub open spec fn enc_head(len: u32, ty: u8, flags: u8, stream: u32) -> Seq<u8> {
    enc24(len) + seq![ty, flags] + enc32(stream)
}

/// The bytes of `f` on the wire.
pub open spec fn serialize(f: Frame) -> Seq<u8> {
    let p = payload_of(f);
    enc_head(p.len() as u32, type_of(f), flags_of(f), stream_of(f)) + p
}

/// `f` can be sent to a peer whose SETTINGS_MAX_FRAME_SIZE is `max`, and
/// a receiver following this spec reads it back as `f`: its payload fits,
/// stream identifiers are 31-bit and nonzero exactly where §6 requires,
/// and its values are ones §6 allows.
pub open spec fn wf(f: Frame, max: u32) -> bool {
    &&& payload_of(f).len() <= max
    &&& max <= MAX_MAX_FRAME_SIZE
    &&& stream_of(f) <= MAX_31
    &&& match f {
        Frame::Data { stream, .. } => stream != 0,
        Frame::Headers { stream, priority, .. } => stream != 0 && (priority matches Some(p)
            ==> p.dependency <= MAX_31),
        Frame::Priority { stream, prio } => stream != 0 && prio.dependency <= MAX_31,
        Frame::RstStream { stream, .. } => stream != 0,
        Frame::Settings { ack, params } => (ack ==> params.len() == 0) && params_error(
            params,
            params.len() as int,
        ) is None,
        Frame::PushPromise { stream, promised, .. } => stream != 0 && promised <= MAX_31,
        Frame::Ping { .. } => true,
        Frame::GoAway { last_stream, .. } => last_stream <= MAX_31,
        Frame::WindowUpdate { increment, .. } => 1 <= increment <= MAX_31,
        Frame::Continuation { stream, .. } => stream != 0,
        Frame::Unknown { ty, .. } => ty > CONTINUATION,
    }
}

} // verus!
