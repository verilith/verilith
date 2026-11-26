//! The verified frame parser and serializer.
//!
//! [`parse`] reads the frame at the start of a buffer without copying:
//! payload fields borrow from the input. [`serialize`] appends a frame to a
//! `Vec<u8>`, and [`encode_head`] gives the 9-byte header alone, for a
//! caller that writes the payload from where it already is (one `writev`).
//! Each is proven to compute exactly its counterpart in `spec.rs`.
use crate::lemmas::*;
use crate::spec;
use crate::spec::{Priority, Setting};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The parameters of a SETTINGS frame, as their bytes on the wire: six per
/// parameter, every value one §6.5.2 allows. Unknown identifiers are kept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params<'a> {
    raw: &'a [u8],
}

impl<'a> View for Params<'a> {
    type V = Seq<Setting>;

    closed spec fn view(&self) -> Seq<Setting> {
        spec::params(self.raw@)
    }
}

impl<'a> Params<'a> {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.raw@.len() % 6 == 0
        &&& spec::params_error(spec::params(self.raw@), spec::params(self.raw@).len() as int) is None
    }

    /// The bytes of the parameters, as sent.
    pub closed spec fn bytes(&self) -> Seq<u8> {
        self.raw@
    }

    /// Nothing at run time: brings the type's invariant into a proof.
    #[inline(always)]
    pub fn lemma_valid(&self)
        ensures
            spec::params_error(self@, self@.len() as int) is None,
            spec::enc_params(self@) == self.bytes(),
            self.bytes().len() == 6 * self@.len(),
    {
        proof {
            use_type_invariant(self);
            lemma_enc_params(self.raw@);
            lemma_enc_params_len(self@);
        }
    }

    /// Checks `raw` as a SETTINGS payload: a multiple of 6 bytes, every
    /// value allowed. Returns the error code otherwise.
    pub fn new(raw: &'a [u8]) -> (r: Result<Params<'a>, u32>)
        ensures
            match r {
                Ok(p) => p.bytes() == raw@ && raw@.len() % 6 == 0 && spec::params_error(
                    p@,
                    p@.len() as int,
                ) is None,
                Err(e) => raw@.len() % 6 != 0 && e == spec::FRAME_SIZE_ERROR || raw@.len() % 6 == 0
                    && spec::params_error(spec::params(raw@), raw@.len() as int / 6) == Some(e),
            },
    {
        if raw.len() % 6 != 0 {
            return Err(spec::FRAME_SIZE_ERROR);
        }
        match check_params(raw) {
            Some(e) => Err(e),
            None => Ok(Params { raw }),
        }
    }

    /// The bytes of the parameters, as sent.
    #[inline(always)]
    pub fn as_bytes(&self) -> (r: &'a [u8])
        ensures
            r@ == self.bytes(),
    {
        self.raw
    }

    /// How many parameters there are.
    #[inline(always)]
    pub fn len(&self) -> (r: usize)
        ensures
            r == self@.len(),
    {
        self.raw.len() / 6
    }

    /// Whether there are none.
    #[inline(always)]
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@.len() == 0),
    {
        self.raw.len() < 6
    }

    /// Parameter `i`.
    #[inline(always)]
    pub fn get(&self, i: usize) -> (r: Setting)
        requires
            i < self@.len(),
        ensures
            r == self@[i as int],
    {
        let _ = self.raw.len();
        proof {
            use_type_invariant(self);
        }
        assert(6 * i + 6 <= self.raw@.len()) by (nonlinear_arith)
            requires
                i < self.raw@.len() / 6,
        ;
        let k = 6 * i;
        Setting { id: rd16(self.raw, k), value: rd32(self.raw, k + 2) }
    }
}

/// A frame. Payload fields borrow from the buffer it was parsed from.
/// `pad` is the Pad Length when the PADDED flag is set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Frame<'a> {
    /// DATA (§6.1).
    Data { stream: u32, end_stream: bool, pad: Option<u8>, data: &'a [u8] },
    /// HEADERS (§6.2).
    Headers {
        stream: u32,
        end_stream: bool,
        end_headers: bool,
        pad: Option<u8>,
        priority: Option<Priority>,
        fragment: &'a [u8],
    },
    /// PRIORITY (§6.3).
    Priority { stream: u32, prio: Priority },
    /// RST_STREAM (§6.4).
    RstStream { stream: u32, code: u32 },
    /// SETTINGS (§6.5). An ACK has no parameters.
    Settings { ack: bool, params: Params<'a> },
    /// PUSH_PROMISE (§6.6).
    PushPromise {
        stream: u32,
        end_headers: bool,
        pad: Option<u8>,
        promised: u32,
        fragment: &'a [u8],
    },
    /// PING (§6.7). The opaque data, read as a big-endian integer.
    Ping { ack: bool, opaque: u64 },
    /// GOAWAY (§6.8).
    GoAway { last_stream: u32, code: u32, debug: &'a [u8] },
    /// WINDOW_UPDATE (§6.9).
    WindowUpdate { stream: u32, increment: u32 },
    /// CONTINUATION (§6.10).
    Continuation { stream: u32, end_headers: bool, fragment: &'a [u8] },
    /// A frame of a type above 9, which the connection ignores (§5.5).
    Unknown { ty: u8, flags: u8, stream: u32, payload: &'a [u8] },
}

impl<'a> View for Frame<'a> {
    type V = spec::Frame;

    open spec fn view(&self) -> spec::Frame {
        match *self {
            Frame::Data { stream, end_stream, pad, data } => spec::Frame::Data {
                stream,
                end_stream,
                pad,
                data: data@,
            },
            Frame::Headers { stream, end_stream, end_headers, pad, priority, fragment } => {
                spec::Frame::Headers {
                    stream,
                    end_stream,
                    end_headers,
                    pad,
                    priority,
                    fragment: fragment@,
                }
            },
            Frame::Priority { stream, prio } => spec::Frame::Priority { stream, prio },
            Frame::RstStream { stream, code } => spec::Frame::RstStream { stream, code },
            Frame::Settings { ack, params } => spec::Frame::Settings { ack, params: params@ },
            Frame::PushPromise { stream, end_headers, pad, promised, fragment } => {
                spec::Frame::PushPromise {
                    stream,
                    end_headers,
                    pad,
                    promised,
                    fragment: fragment@,
                }
            },
            Frame::Ping { ack, opaque } => spec::Frame::Ping { ack, opaque },
            Frame::GoAway { last_stream, code, debug } => spec::Frame::GoAway {
                last_stream,
                code,
                debug: debug@,
            },
            Frame::WindowUpdate { stream, increment } => spec::Frame::WindowUpdate {
                stream,
                increment,
            },
            Frame::Continuation { stream, end_headers, fragment } => spec::Frame::Continuation {
                stream,
                end_headers,
                fragment: fragment@,
            },
            Frame::Unknown { ty, flags, stream, payload } => spec::Frame::Unknown {
                ty,
                flags,
                stream,
                payload: payload@,
            },
        }
    }
}

/// What [`parse`] found at the start of the buffer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Parsed<'a> {
    /// Not enough bytes yet: at least this many are needed from the start.
    Incomplete(usize),
    /// A frame, and the number of bytes it took.
    Frame(Frame<'a>, usize),
    /// A stream error (§5.4.2): reset `stream` with `code`, skip `len`
    /// bytes and carry on.
    StreamError { stream: u32, code: u32, len: usize },
    /// A connection error (§5.4.1): send GOAWAY with this code and close.
    ConnError(u32),
}

impl<'a> View for Parsed<'a> {
    type V = spec::Res;

    open spec fn view(&self) -> spec::Res {
        match *self {
            Parsed::Incomplete(n) => spec::Res::Incomplete(n as nat),
            Parsed::Frame(f, n) => spec::Res::Frame(f@, n as nat),
            Parsed::StreamError { stream, code, len } => spec::Res::StreamError(
                stream,
                code,
                len as nat,
            ),
            Parsed::ConnError(c) => spec::Res::ConnError(c),
        }
    }
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

#[inline(always)]
fn rd16(b: &[u8], i: usize) -> (r: u16)
    requires
        i + 2 <= b@.len(),
    ensures
        r == spec::be16(b@, i as int),
{
    let _ = b.len();
    ((b[i] as u16) << 8u16) | (b[i + 1] as u16)
}

#[inline(always)]
fn rd32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r == spec::be32(b@, i as int),
{
    let _ = b.len();
    ((b[i] as u32) << 24u32) | ((b[i + 1] as u32) << 16u32) | ((b[i + 2] as u32) << 8u32) | (b[i
        + 3] as u32)
}

#[inline(always)]
fn rd64(b: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= b@.len(),
    ensures
        r == spec::be64(b@, i as int),
{
    let _ = b.len();
    ((rd32(b, i) as u64) << 32u64) | (rd32(b, i + 4) as u64)
}

#[inline(always)]
fn rd_priority(b: &[u8], i: usize) -> (r: Priority)
    requires
        i + 5 <= b@.len(),
    ensures
        r == spec::priority_at(b@, i as int),
{
    let _ = b.len();
    let w = rd32(b, i);
    Priority { exclusive: w & 0x8000_0000 != 0, dependency: w & spec::MAX_31, weight: b[i + 4] }
}

/// The error of the first invalid parameter in `raw`, a multiple of 6 bytes.
fn check_params(raw: &[u8]) -> (r: Option<u32>)
    requires
        raw@.len() % 6 == 0,
    ensures
        r == spec::params_error(spec::params(raw@), raw@.len() as int / 6),
{
    let ghost ps = spec::params(raw@);
    let n = raw.len() / 6;
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw@.len() / 6,
            ps == spec::params(raw@),
            i <= n,
            raw@.len() <= usize::MAX,
            spec::params_error(ps, i as int) is None,
        decreases n - i,
    {
        assert(6 * i + 6 <= raw@.len()) by (nonlinear_arith)
            requires
                i < n,
                n == raw@.len() / 6,
        ;
        let id = rd16(raw, 6 * i);
        let value = rd32(raw, 6 * i + 2);
        assert(ps[i as int] == Setting { id, value });
        let e = if id == spec::SETTINGS_ENABLE_PUSH && value > 1 {
            Some(spec::PROTOCOL_ERROR)
        } else if id == spec::SETTINGS_INITIAL_WINDOW_SIZE && value > spec::MAX_31 {
            Some(spec::FLOW_CONTROL_ERROR)
        } else if id == spec::SETTINGS_MAX_FRAME_SIZE && (value < spec::MIN_MAX_FRAME_SIZE || value
            > spec::MAX_MAX_FRAME_SIZE) {
            Some(spec::PROTOCOL_ERROR)
        } else if (id == spec::SETTINGS_ENABLE_CONNECT_PROTOCOL || id
            == spec::SETTINGS_NO_RFC7540_PRIORITIES) && value > 1 {
            Some(spec::PROTOCOL_ERROR)
        } else {
            None
        };
        if e.is_some() {
            proof {
                lemma_params_error_mono(ps, i as int + 1, n as int);
            }
            return e;
        }
        i = i + 1;
    }
    None
}

#[inline(always)]
fn unpad(p: &[u8], padded: bool, fixed: usize) -> (r: Result<(Option<u8>, usize, usize), u32>)
    requires
        fixed <= 5,
    ensures
        match (r, spec::unpad(p@, padded, fixed as nat)) {
            (Ok((pad, a, z)), Ok((sp, sa, sz))) => pad == sp && a == sa && z == sz && a <= z
                <= p@.len(),
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if !padded {
        if p.len() < fixed {
            Err(spec::FRAME_SIZE_ERROR)
        } else {
            Ok((None, fixed, p.len()))
        }
    } else if p.len() < 1 + fixed {
        Err(spec::FRAME_SIZE_ERROR)
    } else if p[0] as usize > p.len() - 1 - fixed {
        Err(spec::PROTOCOL_ERROR)
    } else {
        Ok((Some(p[0]), 1 + fixed, p.len() - p[0] as usize))
    }
}

/// The frame at the start of `b`, for a receiver whose
/// SETTINGS_MAX_FRAME_SIZE is `max`. A frame longer than `max` is an error
/// as soon as its header is in `b`.
#[inline]
pub fn parse<'a>(b: &'a [u8], max: u32) -> (r: Parsed<'a>)
    ensures
        r@ == spec::parse(b@, max),
        r matches Parsed::Frame(_, n) ==> n <= b@.len(),
        r matches Parsed::StreamError { len, .. } ==> len <= b@.len(),
{
    if b.len() < 9 {
        return Parsed::Incomplete(9);
    }
    let (b0, b1, b2) = (b[0], b[1], b[2]);
    let len = ((b0 as u32) << 16u32) | ((b1 as u32) << 8u32) | (b2 as u32);
    let ty = b[3];
    let flags = b[4];
    let stream = rd32(b, 5) & spec::MAX_31;
    let ghost h = spec::head(b@);
    assert(h == spec::Head { len, ty, flags, stream });
    if len > max {
        return Parsed::ConnError(spec::FRAME_SIZE_ERROR);
    }
    assert(len <= 0xff_ffff) by (bit_vector)
        requires
            len == ((b0 as u32) << 16u32) | ((b1 as u32) << 8u32) | (b2 as u32),
    ;
    let n = 9 + len as usize;
    if b.len() < n {
        return Parsed::Incomplete(n);
    }
    let p = slice_subrange(b, 9, n);
    payload(len, ty, flags, stream, p)
}

#[inline(always)]
fn payload<'a>(len: u32, ty: u8, flags: u8, s: u32, p: &'a [u8]) -> (r: Parsed<'a>)
    requires
        p@.len() == len,
        len <= 0xff_ffff,
    ensures
        r@ == spec::payload(spec::Head { len, ty, flags, stream: s }, p@),
        r matches Parsed::Frame(_, n) ==> n == 9 + len,
        r matches Parsed::StreamError { len: l, .. } ==> l == 9 + len,
{
    let n = 9 + len as usize;
    let padded = flags & spec::FLAG_PADDED != 0;
    if ty == spec::DATA {
        if s == 0 {
            return Parsed::ConnError(spec::PROTOCOL_ERROR);
        }
        match unpad(p, padded, 0) {
            Err(e) => Parsed::ConnError(e),
            Ok((pad, a, z)) => Parsed::Frame(
                Frame::Data {
                    stream: s,
                    end_stream: flags & spec::FLAG_END_STREAM != 0,
                    pad,
                    data: slice_subrange(p, a, z),
                },
                n,
            ),
        }
    } else if ty == spec::HEADERS {
        let prio = flags & spec::FLAG_PRIORITY != 0;
        if s == 0 {
            return Parsed::ConnError(spec::PROTOCOL_ERROR);
        }
        match unpad(
            p,
            padded,
            if prio {
                5
            } else {
                0
            },
        ) {
            Err(e) => Parsed::ConnError(e),
            Ok((pad, a, z)) => Parsed::Frame(
                Frame::Headers {
                    stream: s,
                    end_stream: flags & spec::FLAG_END_STREAM != 0,
                    end_headers: flags & spec::FLAG_END_HEADERS != 0,
                    pad,
                    priority: if prio {
                        Some(rd_priority(p, a - 5))
                    } else {
                        None
                    },
                    fragment: slice_subrange(p, a, z),
                },
                n,
            ),
        }
    } else if ty == spec::PRIORITY {
        if s == 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else if len != 5 {
            Parsed::StreamError { stream: s, code: spec::FRAME_SIZE_ERROR, len: n }
        } else {
            Parsed::Frame(Frame::Priority { stream: s, prio: rd_priority(p, 0) }, n)
        }
    } else if ty == spec::RST_STREAM {
        if s == 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else if len != 4 {
            Parsed::ConnError(spec::FRAME_SIZE_ERROR)
        } else {
            Parsed::Frame(Frame::RstStream { stream: s, code: rd32(p, 0) }, n)
        }
    } else if ty == spec::SETTINGS {
        let ack = flags & spec::FLAG_ACK != 0;
        if s != 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else if ack && len != 0 {
            Parsed::ConnError(spec::FRAME_SIZE_ERROR)
        } else if len % 6 != 0 {
            Parsed::ConnError(spec::FRAME_SIZE_ERROR)
        } else {
            match check_params(p) {
                Some(e) => Parsed::ConnError(e),
                None => Parsed::Frame(Frame::Settings { ack, params: Params { raw: p } }, n),
            }
        }
    } else if ty == spec::PUSH_PROMISE {
        if s == 0 {
            return Parsed::ConnError(spec::PROTOCOL_ERROR);
        }
        match unpad(p, padded, 4) {
            Err(e) => Parsed::ConnError(e),
            Ok((pad, a, z)) => Parsed::Frame(
                Frame::PushPromise {
                    stream: s,
                    end_headers: flags & spec::FLAG_END_HEADERS != 0,
                    pad,
                    promised: rd32(p, a - 4) & spec::MAX_31,
                    fragment: slice_subrange(p, a, z),
                },
                n,
            ),
        }
    } else if ty == spec::PING {
        if s != 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else if len != 8 {
            Parsed::ConnError(spec::FRAME_SIZE_ERROR)
        } else {
            Parsed::Frame(Frame::Ping { ack: flags & spec::FLAG_ACK != 0, opaque: rd64(p, 0) }, n)
        }
    } else if ty == spec::GOAWAY {
        if s != 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else if len < 8 {
            Parsed::ConnError(spec::FRAME_SIZE_ERROR)
        } else {
            Parsed::Frame(
                Frame::GoAway {
                    last_stream: rd32(p, 0) & spec::MAX_31,
                    code: rd32(p, 4),
                    debug: slice_subrange(p, 8, p.len()),
                },
                n,
            )
        }
    } else if ty == spec::WINDOW_UPDATE {
        if len != 4 {
            return Parsed::ConnError(spec::FRAME_SIZE_ERROR);
        }
        let inc = rd32(p, 0) & spec::MAX_31;
        if inc == 0 {
            if s == 0 {
                Parsed::ConnError(spec::PROTOCOL_ERROR)
            } else {
                Parsed::StreamError { stream: s, code: spec::PROTOCOL_ERROR, len: n }
            }
        } else {
            Parsed::Frame(Frame::WindowUpdate { stream: s, increment: inc }, n)
        }
    } else if ty == spec::CONTINUATION {
        if s == 0 {
            Parsed::ConnError(spec::PROTOCOL_ERROR)
        } else {
            Parsed::Frame(
                Frame::Continuation {
                    stream: s,
                    end_headers: flags & spec::FLAG_END_HEADERS != 0,
                    fragment: p,
                },
                n,
            )
        }
    } else {
        Parsed::Frame(Frame::Unknown { ty, flags, stream: s, payload: p }, n)
    }
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// The frame header (§4.1) for a payload of `len` bytes, with the reserved
/// bit 0; `None` if `len` does not fit in 24 bits or `stream` in 31.
#[inline(always)]
pub fn encode_head(len: u32, ty: u8, flags: u8, stream: u32) -> (r: Option<[u8; 9]>)
    ensures
        match r {
            Some(h) => len <= spec::MAX_MAX_FRAME_SIZE && stream <= spec::MAX_31 && h@
                == spec::enc_head(len, ty, flags, stream),
            None => len > spec::MAX_MAX_FRAME_SIZE || stream > spec::MAX_31,
        },
{
    if len > spec::MAX_MAX_FRAME_SIZE || stream > spec::MAX_31 {
        return None;
    }
    let h = [
        (len >> 16u32) as u8,
        (len >> 8u32) as u8,
        len as u8,
        ty,
        flags,
        (stream >> 24u32) as u8,
        (stream >> 16u32) as u8,
        (stream >> 8u32) as u8,
        stream as u8,
    ];
    assert(h@ =~= spec::enc_head(len, ty, flags, stream));
    Some(h)
}

#[inline(always)]
fn put_head(out: &mut Vec<u8>, len: u32, ty: u8, flags: u8, stream: u32)
    requires
        len <= spec::MAX_MAX_FRAME_SIZE,
        stream <= spec::MAX_31,
    ensures
        final(out)@ == old(out)@ + spec::enc_head(len, ty, flags, stream),
{
    let h = encode_head(len, ty, flags, stream).unwrap();
    out.extend_from_slice(&h);
    assert(final(out)@ =~= old(out)@ + spec::enc_head(len, ty, flags, stream));
}

#[inline(always)]
fn put32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + spec::enc32(x),
{
    let a = [(x >> 24u32) as u8, (x >> 16u32) as u8, (x >> 8u32) as u8, x as u8];
    out.extend_from_slice(&a);
    assert(final(out)@ =~= old(out)@ + spec::enc32(x));
}

/// A frame header and a 4-byte payload `x`, in one copy.
#[inline(always)]
fn put_head32(out: &mut Vec<u8>, ty: u8, flags: u8, stream: u32, x: u32)
    requires
        stream <= spec::MAX_31,
    ensures
        final(out)@ == old(out)@ + spec::enc_head(4, ty, flags, stream) + spec::enc32(x),
{
    let a = [
        0u8,
        0u8,
        4u8,
        ty,
        flags,
        (stream >> 24u32) as u8,
        (stream >> 16u32) as u8,
        (stream >> 8u32) as u8,
        stream as u8,
        (x >> 24u32) as u8,
        (x >> 16u32) as u8,
        (x >> 8u32) as u8,
        x as u8,
    ];
    assert(((4u32 >> 16u32) as u8) == 0u8 && ((4u32 >> 8u32) as u8) == 0u8 && (4u32 as u8) == 4u8)
        by (bit_vector);
    out.extend_from_slice(&a);
    assert(final(out)@ =~= old(out)@ + spec::enc_head(4, ty, flags, stream) + spec::enc32(x));
}

/// A PING frame, in one copy.
#[inline(always)]
fn put_ping(out: &mut Vec<u8>, flags: u8, hi: u32, lo: u32)
    ensures
        final(out)@ == old(out)@ + spec::enc_head(8, spec::PING, flags, 0) + spec::enc32(hi)
            + spec::enc32(lo),
{
    let a = [
        0u8,
        0u8,
        8u8,
        spec::PING,
        flags,
        0u8,
        0u8,
        0u8,
        0u8,
        (hi >> 24u32) as u8,
        (hi >> 16u32) as u8,
        (hi >> 8u32) as u8,
        hi as u8,
        (lo >> 24u32) as u8,
        (lo >> 16u32) as u8,
        (lo >> 8u32) as u8,
        lo as u8,
    ];
    assert(((8u32 >> 16u32) as u8) == 0u8 && ((8u32 >> 8u32) as u8) == 0u8 && (8u32 as u8) == 8u8
        && ((0u32 >> 24u32) as u8) == 0u8 && ((0u32 >> 16u32) as u8) == 0u8 && ((0u32 >> 8u32) as u8)
        == 0u8 && (0u32 as u8) == 0u8) by (bit_vector);
    out.extend_from_slice(&a);
    assert(final(out)@ =~= old(out)@ + spec::enc_head(8, spec::PING, flags, 0) + spec::enc32(hi)
        + spec::enc32(lo));
}

#[inline(always)]
fn put_bytes(out: &mut Vec<u8>, b: &[u8])
    ensures
        final(out)@ == old(out)@ + b@,
{
    out.extend_from_slice(b);
    assert(final(out)@ =~= old(out)@ + b@);
}

fn put_zeros(out: &mut Vec<u8>, n: u8)
    ensures
        final(out)@ == old(out)@ + spec::zeros(n as nat),
{
    let mut i: u8 = 0;
    while i < n
        invariant
            i <= n,
            out@ == old(out)@ + spec::zeros(i as nat),
        decreases n - i,
    {
        out.push(0u8);
        assert(out@ =~= old(out)@ + spec::zeros((i + 1) as nat));
        i = i + 1;
    }
}

#[inline(always)]
fn put_priority(out: &mut Vec<u8>, p: Priority)
    ensures
        final(out)@ == old(out)@ + spec::enc_priority(p),
{
    put32(
        out,
        if p.exclusive {
            p.dependency | 0x8000_0000
        } else {
            p.dependency
        },
    );
    out.push(p.weight);
    assert(final(out)@ =~= old(out)@ + spec::enc_priority(p));
}

#[inline(always)]
fn bit(b: bool, f: u8) -> (r: u8)
    ensures
        r == spec::bit(b, f),
{
    if b {
        f
    } else {
        0
    }
}

#[inline(always)]
fn pad_flag(pad: Option<u8>) -> (r: u8)
    ensures
        r == spec::pad_flag(pad),
{
    if pad.is_some() {
        spec::FLAG_PADDED
    } else {
        0
    }
}

#[inline(always)]
fn pad_len(pad: Option<u8>) -> (r: usize)
    ensures
        r == match pad {
            Some(n) => 1 + n as int,
            None => 0int,
        },
{
    match pad {
        Some(n) => 1 + n as usize,
        None => 0,
    }
}

/// Appends `f`, for a peer whose SETTINGS_MAX_FRAME_SIZE is `max`. Fails,
/// leaving `out` as it was, exactly when `f` is not well-formed
/// (`spec::wf`): then a receiver could not read it back as `f`.
#[inline]
pub fn serialize(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    if max > spec::MAX_MAX_FRAME_SIZE {
        return Err(());
    }
    match *f {
        Frame::Data { .. } => ser_data(f, max, out),
        Frame::Headers { .. } => ser_headers(f, max, out),
        Frame::Priority { .. } => ser_priority(f, max, out),
        Frame::RstStream { .. } => ser_rst_stream(f, max, out),
        Frame::Settings { .. } => ser_settings(f, max, out),
        Frame::PushPromise { .. } => ser_push_promise(f, max, out),
        Frame::Ping { .. } => ser_ping(f, max, out),
        Frame::GoAway { .. } => ser_go_away(f, max, out),
        Frame::WindowUpdate { .. } => ser_window_update(f, max, out),
        Frame::Continuation { .. } => ser_continuation(f, max, out),
        Frame::Unknown { .. } => ser_unknown(f, max, out),
    }
}

#[inline(always)]
fn ser_data(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Data,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Data { stream, end_stream, pad, data } => {
            if stream == 0 || stream > spec::MAX_31 || data.len() > m {
                return Err(());
            }
            let len = data.len() + pad_len(pad);
            if len > m {
                return Err(());
            }
            put_head(out, len as u32, spec::DATA, bit(end_stream, spec::FLAG_END_STREAM) | pad_flag(pad), stream);
            if let Some(k) = pad {
                out.push(k);
            }
            put_bytes(out, data);
            if let Some(k) = pad {
                put_zeros(out, k);
            }
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_headers(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Headers,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Headers { stream, end_stream, end_headers, pad, priority, fragment } => {
            if stream == 0 || stream > spec::MAX_31 || fragment.len() > m {
                return Err(());
            }
            if let Some(pr) = priority {
                if pr.dependency > spec::MAX_31 {
                    return Err(());
                }
            }
            let len = fragment.len() + pad_len(pad) + if priority.is_some() {
                5
            } else {
                0
            };
            if len > m {
                return Err(());
            }
            let flags = bit(end_stream, spec::FLAG_END_STREAM) | bit(
                end_headers,
                spec::FLAG_END_HEADERS,
            ) | pad_flag(pad) | bit(priority.is_some(), spec::FLAG_PRIORITY);
            put_head(out, len as u32, spec::HEADERS, flags, stream);
            if let Some(k) = pad {
                out.push(k);
            }
            if let Some(pr) = priority {
                put_priority(out, pr);
            }
            put_bytes(out, fragment);
            if let Some(k) = pad {
                put_zeros(out, k);
            }
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_priority(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Priority,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Priority { stream, prio } => {
            if stream == 0 || stream > spec::MAX_31 || prio.dependency > spec::MAX_31 || m < 5 {
                return Err(());
            }
            put_head(out, 5, spec::PRIORITY, 0, stream);
            put_priority(out, prio);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_rst_stream(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is RstStream,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::RstStream { stream, code } => {
            if stream == 0 || stream > spec::MAX_31 || m < 4 {
                return Err(());
            }
            put_head32(out, spec::RST_STREAM, 0, stream, code);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_settings(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Settings,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Settings { ack, params } => {
            params.lemma_valid();
            let raw = params.as_bytes();
            if raw.len() > m || (ack && raw.len() != 0) {
                return Err(());
            }
            put_head(out, raw.len() as u32, spec::SETTINGS, bit(ack, spec::FLAG_ACK), 0);
            put_bytes(out, raw);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_push_promise(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is PushPromise,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::PushPromise { stream, end_headers, pad, promised, fragment } => {
            if stream == 0 || stream > spec::MAX_31 || promised > spec::MAX_31 || fragment.len()
                > m {
                return Err(());
            }
            let len = fragment.len() + pad_len(pad) + 4;
            if len > m {
                return Err(());
            }
            let flags = bit(end_headers, spec::FLAG_END_HEADERS) | pad_flag(pad);
            put_head(out, len as u32, spec::PUSH_PROMISE, flags, stream);
            if let Some(k) = pad {
                out.push(k);
            }
            put32(out, promised);
            put_bytes(out, fragment);
            if let Some(k) = pad {
                put_zeros(out, k);
            }
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_ping(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Ping,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Ping { ack, opaque } => {
            if m < 8 {
                return Err(());
            }
            put_ping(out, bit(ack, spec::FLAG_ACK), (opaque >> 32u64) as u32, opaque as u32);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_go_away(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is GoAway,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::GoAway { last_stream, code, debug } => {
            if last_stream > spec::MAX_31 || debug.len() > m || debug.len() + 8 > m {
                return Err(());
            }
            put_head(out, (debug.len() + 8) as u32, spec::GOAWAY, 0, 0);
            put32(out, last_stream);
            put32(out, code);
            put_bytes(out, debug);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_window_update(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is WindowUpdate,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::WindowUpdate { stream, increment } => {
            assert((stream | increment) > 0x7fff_ffff <==> (stream > 0x7fff_ffff || increment
                > 0x7fff_ffff)) by (bit_vector);
            if (stream | increment) > spec::MAX_31 || increment == 0 || m < 4 {
                return Err(());
            }
            put_head32(out, spec::WINDOW_UPDATE, 0, stream, increment);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_continuation(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Continuation,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Continuation { stream, end_headers, fragment } => {
            if stream == 0 || stream > spec::MAX_31 || fragment.len() > m {
                return Err(());
            }
            put_head(
                out,
                fragment.len() as u32,
                spec::CONTINUATION,
                bit(end_headers, spec::FLAG_END_HEADERS),
                stream,
            );
            put_bytes(out, fragment);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

#[inline(always)]
fn ser_unknown(f: &Frame, max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    requires
        f@ is Unknown,
        max <= spec::MAX_MAX_FRAME_SIZE,
    ensures
        r is Ok <==> spec::wf(f@, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(f@),
        r is Err ==> final(out)@ == old(out)@,
{
    let m = max as usize;
    let ghost sf = f@;
    match *f {
        Frame::Unknown { ty, flags, stream, payload } => {
            if ty <= spec::CONTINUATION || stream > spec::MAX_31 || payload.len() > m {
                return Err(());
            }
            put_head(out, payload.len() as u32, ty, flags, stream);
            put_bytes(out, payload);
            assert(final(out)@ =~= old(out)@ + spec::serialize(sf));
            Ok(())
        },
        _ => Err(()),
    }
}

/// Appends a SETTINGS frame (not an ACK) with `params`, for a peer whose
/// SETTINGS_MAX_FRAME_SIZE is `max`. Fails, leaving `out` as it was,
/// exactly when the frame is not well-formed.
pub fn serialize_settings(params: &[Setting], max: u32, out: &mut Vec<u8>) -> (r: Result<(), ()>)
    ensures
        r is Ok <==> spec::wf(spec::Frame::Settings { ack: false, params: params@ }, max),
        r is Ok ==> final(out)@ == old(out)@ + spec::serialize(
            spec::Frame::Settings { ack: false, params: params@ },
        ),
        r is Err ==> final(out)@ == old(out)@,
{
    let ghost f = spec::Frame::Settings { ack: false, params: params@ };
    proof {
        lemma_enc_params_len(params@);
    }
    if max > spec::MAX_MAX_FRAME_SIZE || params.len() > max as usize / 6 {
        return Err(());
    }
    let len = 6 * params.len();
    let mut i: usize = 0;
    while i < params.len()
        invariant
            i <= params@.len(),
            spec::params_error(params@, i as int) is None,
        decreases params@.len() - i,
    {
        let s = params[i];
        let id = s.id;
        let value = s.value;
        let bad = if id == spec::SETTINGS_ENABLE_PUSH && value > 1 {
            true
        } else if id == spec::SETTINGS_INITIAL_WINDOW_SIZE && value > spec::MAX_31 {
            true
        } else if id == spec::SETTINGS_MAX_FRAME_SIZE && (value < spec::MIN_MAX_FRAME_SIZE || value
            > spec::MAX_MAX_FRAME_SIZE) {
            true
        } else if (id == spec::SETTINGS_ENABLE_CONNECT_PROTOCOL || id
            == spec::SETTINGS_NO_RFC7540_PRIORITIES) && value > 1 {
            true
        } else {
            false
        };
        if bad {
            proof {
                lemma_params_error_mono(params@, i as int + 1, params@.len() as int);
                assert(spec::params_error(params@, params@.len() as int) is Some);
            }
            return Err(());
        }
        i = i + 1;
    }
    put_head(out, len as u32, spec::SETTINGS, 0, 0);
    let ghost start = out@;
    let mut j: usize = 0;
    while j < params.len()
        invariant
            j <= params@.len(),
            out@ == start + spec::enc_params(params@.subrange(0, j as int)),
        decreases params@.len() - j,
    {
        let s = params[j];
        out.push((s.id >> 8u16) as u8);
        out.push(s.id as u8);
        put32(out, s.value);
        proof {
            let q = params@.subrange(0, j as int + 1);
            assert(q.drop_last() =~= params@.subrange(0, j as int));
            assert(q.last() == s);
        }
        assert(out@ =~= start + spec::enc_params(params@.subrange(0, j as int + 1)));
        j = j + 1;
    }
    assert(params@.subrange(0, params@.len() as int) =~= params@);
    assert(final(out)@ =~= old(out)@ + spec::serialize(f));
    Ok(())
}

} // verus!
