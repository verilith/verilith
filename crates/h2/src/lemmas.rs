//! The round-trip theorems, on the spec alone:
//!
//! - `lemma_roundtrip`: a well-formed frame, serialized and followed by
//!   anything, parses back to itself and takes exactly its own bytes.
//! - `lemma_parse_wf`: every frame the parser returns is well-formed, and
//!   took exactly as many bytes as it serializes to. With the first, this
//!   is `parse(serialize(parse(b))) == parse(b)`: what a proxy re-sends is
//!   read by the next hop as what it received.
//! - `lemma_parse_prefix`: once the parser has decided (anything but
//!   Incomplete), more bytes after the frame change nothing.
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Integers
// ---------------------------------------------------------------------------

pub proof fn lemma_be16(b: Seq<u8>, i: int, x: u16)
    requires
        0 <= i,
        i + 2 <= b.len(),
        b.subrange(i, i + 2) == enc16(x),
    ensures
        be16(b, i) == x,
{
    assert(b[i] == b.subrange(i, i + 2)[0]);
    assert(b[i + 1] == b.subrange(i, i + 2)[1]);
    let (b0, b1) = (b[i], b[i + 1]);
    assert(b0 == (x >> 8u16) as u8 && b1 == x as u8 ==> ((b0 as u16) << 8u16) | (b1 as u16) == x)
        by (bit_vector);
}

pub proof fn lemma_be24(b: Seq<u8>, i: int, x: u32)
    requires
        0 <= i,
        i + 3 <= b.len(),
        b.subrange(i, i + 3) == enc24(x),
        x <= MAX_MAX_FRAME_SIZE,
    ensures
        be24(b, i) == x,
{
    assert(b[i] == b.subrange(i, i + 3)[0]);
    assert(b[i + 1] == b.subrange(i, i + 3)[1]);
    assert(b[i + 2] == b.subrange(i, i + 3)[2]);
    let (b0, b1, b2) = (b[i], b[i + 1], b[i + 2]);
    assert(x <= 16777215 && b0 == (x >> 16u32) as u8 && b1 == (x >> 8u32) as u8 && b2 == x as u8
        ==> ((b0 as u32) << 16u32) | ((b1 as u32) << 8u32) | (b2 as u32) == x) by (bit_vector);
}

pub proof fn lemma_be32(b: Seq<u8>, i: int, x: u32)
    requires
        0 <= i,
        i + 4 <= b.len(),
        b.subrange(i, i + 4) == enc32(x),
    ensures
        be32(b, i) == x,
{
    assert(b[i] == b.subrange(i, i + 4)[0]);
    assert(b[i + 1] == b.subrange(i, i + 4)[1]);
    assert(b[i + 2] == b.subrange(i, i + 4)[2]);
    assert(b[i + 3] == b.subrange(i, i + 4)[3]);
    let (b0, b1, b2, b3) = (b[i], b[i + 1], b[i + 2], b[i + 3]);
    assert(b0 == (x >> 24u32) as u8 && b1 == (x >> 16u32) as u8 && b2 == (x >> 8u32) as u8 && b3
        == x as u8 ==> ((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (
    b3 as u32) == x) by (bit_vector);
}

pub proof fn lemma_be64(b: Seq<u8>, i: int, x: u64)
    requires
        0 <= i,
        i + 8 <= b.len(),
        b.subrange(i, i + 8) == enc64(x),
    ensures
        be64(b, i) == x,
{
    let hi = (x >> 32u64) as u32;
    let lo = x as u32;
    assert(b.subrange(i, i + 4) =~= b.subrange(i, i + 8).subrange(0, 4));
    assert(b.subrange(i + 4, i + 8) =~= b.subrange(i, i + 8).subrange(4, 8));
    assert(enc64(x).subrange(0, 4) =~= enc32(hi));
    assert(enc64(x).subrange(4, 8) =~= enc32(lo));
    lemma_be32(b, i, hi);
    lemma_be32(b, i + 4, lo);
    assert((((x >> 32u64) as u32) as u64) << 32u64 | ((x as u32) as u64) == x) by (bit_vector);
}

/// The stream identifier read back, without the reserved bit.
pub proof fn lemma_31(x: u32)
    requires
        x <= MAX_31,
    ensures
        x & MAX_31 == x,
{
    assert(x <= 0x7fff_ffff ==> x & 0x7fff_ffff == x) by (bit_vector);
}

// ---------------------------------------------------------------------------
// The frame header
// ---------------------------------------------------------------------------

pub proof fn lemma_head(b: Seq<u8>, len: u32, ty: u8, flags: u8, stream: u32)
    requires
        b.len() >= HEAD_LEN,
        b.subrange(0, 9) == enc_head(len, ty, flags, stream),
        len <= MAX_MAX_FRAME_SIZE,
        stream <= MAX_31,
    ensures
        head(b) == (Head { len, ty, flags, stream }),
{
    let e = enc_head(len, ty, flags, stream);
    assert(b.subrange(0, 3) =~= e.subrange(0, 3));
    assert(e.subrange(0, 3) =~= enc24(len));
    assert(b.subrange(5, 9) =~= e.subrange(5, 9));
    assert(e.subrange(5, 9) =~= enc32(stream));
    assert(b[3] == e[3] && b[4] == e[4]);
    lemma_be24(b, 0, len);
    lemma_be32(b, 5, stream);
    lemma_31(stream);
}

// ---------------------------------------------------------------------------
// Flags
// ---------------------------------------------------------------------------

proof fn lemma_flags_data(e: bool, p: bool)
    ensures
        flag(bit(e, FLAG_END_STREAM) | bit(p, FLAG_PADDED), FLAG_END_STREAM) == e,
        flag(bit(e, FLAG_END_STREAM) | bit(p, FLAG_PADDED), FLAG_PADDED) == p,
{
    let (x, y) = (bit(e, 1), bit(p, 8));
    assert((x == 0 || x == 1) && (y == 0 || y == 8) ==> ((x | y) & 1 != 0) == (x == 1) && ((x | y)
        & 8 != 0) == (y == 8)) by (bit_vector);
}

proof fn lemma_flags_headers(e: bool, h: bool, p: bool, r: bool)
    ensures
        ({
            let f = bit(e, FLAG_END_STREAM) | bit(h, FLAG_END_HEADERS) | bit(p, FLAG_PADDED) | bit(
                r,
                FLAG_PRIORITY,
            );
            &&& flag(f, FLAG_END_STREAM) == e
            &&& flag(f, FLAG_END_HEADERS) == h
            &&& flag(f, FLAG_PADDED) == p
            &&& flag(f, FLAG_PRIORITY) == r
        }),
{
    let (a, b, c, d) = (bit(e, 1), bit(h, 4), bit(p, 8), bit(r, 0x20));
    assert((a == 0 || a == 1) && (b == 0 || b == 4) && (c == 0 || c == 8) && (d == 0 || d == 0x20)
        ==> ((a | b | c | d) & 1 != 0) == (a == 1) && ((a | b | c | d) & 4 != 0) == (b == 4) && ((a
        | b | c | d) & 8 != 0) == (c == 8) && ((a | b | c | d) & 0x20 != 0) == (d == 0x20))
        by (bit_vector);
}

proof fn lemma_flags_pp(h: bool, p: bool)
    ensures
        flag(bit(h, FLAG_END_HEADERS) | bit(p, FLAG_PADDED), FLAG_END_HEADERS) == h,
        flag(bit(h, FLAG_END_HEADERS) | bit(p, FLAG_PADDED), FLAG_PADDED) == p,
{
    let (x, y) = (bit(h, 4), bit(p, 8));
    assert((x == 0 || x == 4) && (y == 0 || y == 8) ==> ((x | y) & 4 != 0) == (x == 4) && ((x | y)
        & 8 != 0) == (y == 8)) by (bit_vector);
}

proof fn lemma_flag1(b: bool, f: u8)
    requires
        f == 1 || f == 4,
    ensures
        flag(bit(b, f), f) == b,
{
    let x = bit(b, f);
    assert((f == 1 || f == 4) && (x == 0 || x == f) ==> (x & f != 0) == (x == f)) by (bit_vector);
}

// ---------------------------------------------------------------------------
// Payload pieces
// ---------------------------------------------------------------------------

pub proof fn lemma_unpad(pad: Option<u8>, body: Seq<u8>, fixed: nat)
    requires
        body.len() >= fixed,
    ensures
        ({
            let p = padded(pad, body);
            let off: int = if pad is Some {
                1
            } else {
                0
            };
            &&& unpad(p, pad is Some, fixed) == Ok::<_, u32>(
                (pad, off + fixed, off + body.len()),
            )
            &&& p.subrange(off, off + body.len()) == body
            &&& p.len() == off + body.len() + match pad {
                Some(n) => n as int,
                None => 0,
            }
        }),
{
    let p = padded(pad, body);
    match pad {
        Some(n) => {
            assert(p[0] == n);
            assert(p.subrange(1, 1 + body.len() as int) =~= body);
        },
        None => {
            assert(p.subrange(0, body.len() as int) =~= body);
        },
    }
}

pub proof fn lemma_priority(b: Seq<u8>, i: int, p: Priority)
    requires
        0 <= i,
        i + 5 <= b.len(),
        b.subrange(i, i + 5) == enc_priority(p),
        p.dependency <= MAX_31,
    ensures
        priority_at(b, i) == p,
{
    let w = if p.exclusive {
        p.dependency | 0x8000_0000
    } else {
        p.dependency
    };
    assert(b.subrange(i, i + 4) =~= b.subrange(i, i + 5).subrange(0, 4));
    assert(enc_priority(p).subrange(0, 4) =~= enc32(w));
    lemma_be32(b, i, w);
    assert(b[i + 4] == b.subrange(i, i + 5)[4]);
    let d = p.dependency;
    assert(d <= 0x7fff_ffff ==> (d | 0x8000_0000) & 0x8000_0000 != 0 && (d | 0x8000_0000)
        & 0x7fff_ffff == d && d & 0x8000_0000 == 0 && d & 0x7fff_ffff == d) by (bit_vector);
}

pub proof fn lemma_enc_params_len(ps: Seq<Setting>)
    ensures
        enc_params(ps).len() == 6 * ps.len(),
    decreases ps.len(),
{
    if ps.len() > 0 {
        lemma_enc_params_len(ps.drop_last());
    }
}

pub proof fn lemma_params(ps: Seq<Setting>)
    ensures
        params(enc_params(ps)) == ps,
    decreases ps.len(),
{
    lemma_enc_params_len(ps);
    let e = enc_params(ps);
    if ps.len() > 0 {
        let q = ps.drop_last();
        lemma_params(q);
        lemma_enc_params_len(q);
        let eq = enc_params(q);
        let k = (6 * q.len()) as int;
        assert forall|i: int| 0 <= i < ps.len() implies #[trigger] params(e)[i] == ps[i] by {
            if i < q.len() {
                assert(e.subrange(6 * i, 6 * i + 2) =~= eq.subrange(6 * i, 6 * i + 2));
                assert(e.subrange(6 * i + 2, 6 * i + 6) =~= eq.subrange(6 * i + 2, 6 * i + 6));
                assert(params(eq)[i] == q[i]);
                assert(be16(e, 6 * i) == be16(eq, 6 * i));
                assert(be32(e, 6 * i + 2) == be32(eq, 6 * i + 2));
            } else {
                assert(i == q.len());
                assert(e.subrange(k, k + 2) =~= enc16(ps.last().id));
                assert(e.subrange(k + 2, k + 6) =~= enc32(ps.last().value));
                lemma_be16(e, k, ps.last().id);
                lemma_be32(e, k + 2, ps.last().value);
            }
        }
        assert(params(e) =~= ps);
    } else {
        assert(params(e) =~= ps);
    }
}

/// `params` of a payload whose length is a multiple of 6 encodes back to it.
pub proof fn lemma_enc_params(p: Seq<u8>)
    requires
        p.len() % 6 == 0,
    ensures
        enc_params(params(p)) == p,
    decreases p.len(),
{
    let ps = params(p);
    lemma_enc_params_len(ps);
    if p.len() > 0 {
        let k = p.len() - 6;
        let q = p.subrange(0, k);
        lemma_enc_params(q);
        assert(params(q) =~= ps.drop_last());
        let s = ps.last();
        let (b0, b1) = (p[k], p[k + 1]);
        assert(enc16(((b0 as u16) << 8u16) | (b1 as u16)) =~= seq![b0, b1]) by {
            assert((((((b0 as u16) << 8u16) | (b1 as u16)) >> 8u16) as u8) == b0 && ((((b0 as u16)
                << 8u16) | (b1 as u16)) as u8) == b1) by (bit_vector);
        }
        let (c0, c1, c2, c3) = (p[k + 2], p[k + 3], p[k + 4], p[k + 5]);
        let v = ((c0 as u32) << 24u32) | ((c1 as u32) << 16u32) | ((c2 as u32) << 8u32) | (
        c3 as u32);
        assert(enc32(v) =~= seq![c0, c1, c2, c3]) by {
            assert(((v >> 24u32) as u8) == c0 && ((v >> 16u32) as u8) == c1 && ((v >> 8u32) as u8)
                == c2 && (v as u8) == c3) by (bit_vector)
                requires
                    v == ((c0 as u32) << 24u32) | ((c1 as u32) << 16u32) | ((c2 as u32) << 8u32) | (
                    c3 as u32),
            ;
        }
        assert(enc_params(ps) =~= p);
    } else {
        assert(enc_params(ps) =~= p);
    }
}

/// Once a parameter is invalid, every longer prefix has the same error.
pub proof fn lemma_params_error_mono(ps: Seq<Setting>, i: int, n: int)
    requires
        0 <= i <= n,
    ensures
        params_error(ps, i) is Some ==> params_error(ps, n) == params_error(ps, i),
    decreases n - i,
{
    if i < n {
        lemma_params_error_mono(ps, i, n - 1);
    }
}

// ---------------------------------------------------------------------------
// The theorems
// ---------------------------------------------------------------------------

/// A well-formed frame followed by anything parses back to itself.
pub proof fn lemma_roundtrip(f: Frame, max: u32, rest: Seq<u8>)
    requires
        wf(f, max),
    ensures
        parse(serialize(f) + rest, max) == Res::Frame(f, serialize(f).len()),
{
    let p = payload_of(f);
    let len = p.len() as u32;
    let e = enc_head(len, type_of(f), flags_of(f), stream_of(f));
    let b = serialize(f) + rest;
    assert(b.subrange(0, 9) =~= e);
    lemma_head(b, len, type_of(f), flags_of(f), stream_of(f));
    assert(b.subrange(9, 9 + len) =~= p);
    let h = head(b);
    assert(serialize(f).len() == 9 + len);
    lemma_payload(f, h);
}

proof fn lemma_payload(f: Frame, h: Head)
    requires
        wf(f, MAX_MAX_FRAME_SIZE),
        h == (Head {
            len: payload_of(f).len() as u32,
            ty: type_of(f),
            flags: flags_of(f),
            stream: stream_of(f),
        }),
    ensures
        payload(h, payload_of(f)) == Res::Frame(f, (HEAD_LEN + h.len) as nat),
{
    let p = payload_of(f);
    match f {
        Frame::Data { stream, end_stream, pad, data } => {
            lemma_flags_data(end_stream, pad is Some);
            lemma_unpad(pad, data, 0);
        },
        Frame::Headers { .. } => lemma_payload_headers(f, h),
        Frame::Priority { stream, prio } => {
            assert(p.subrange(0, 5) =~= p);
            lemma_priority(p, 0, prio);
        },
        Frame::RstStream { stream, code } => {
            assert(p.subrange(0, 4) =~= p);
            lemma_be32(p, 0, code);
        },
        Frame::Settings { ack, params: ps } => {
            lemma_flag1(ack, FLAG_ACK);
            lemma_enc_params_len(ps);
            lemma_params(ps);
            assert(p.len() % 6 == 0) by (nonlinear_arith)
                requires
                    p.len() == 6 * ps.len(),
            ;
        },
        Frame::PushPromise { .. } => lemma_payload_pushpromise(f, h),
        Frame::Ping { ack, opaque } => {
            lemma_flag1(ack, FLAG_ACK);
            assert(p.subrange(0, 8) =~= p);
            lemma_be64(p, 0, opaque);
        },
        Frame::GoAway { last_stream, code, debug } => {
            assert(p.subrange(0, 4) =~= enc32(last_stream));
            assert(p.subrange(4, 8) =~= enc32(code));
            assert(p.subrange(8, p.len() as int) =~= debug);
            lemma_be32(p, 0, last_stream);
            lemma_be32(p, 4, code);
            lemma_31(last_stream);
        },
        Frame::WindowUpdate { stream, increment } => {
            assert(p.subrange(0, 4) =~= p);
            lemma_be32(p, 0, increment);
            lemma_31(increment);
        },
        Frame::Continuation { stream, end_headers, fragment } => {
            lemma_flag1(end_headers, FLAG_END_HEADERS);
        },
        Frame::Unknown { .. } => {},
    }
}

proof fn lemma_payload_headers(f: Frame, h: Head)
    requires
        f is Headers,
        wf(f, MAX_MAX_FRAME_SIZE),
        h == (Head {
            len: payload_of(f).len() as u32,
            ty: type_of(f),
            flags: flags_of(f),
            stream: stream_of(f),
        }),
    ensures
        payload(h, payload_of(f)) == Res::Frame(f, (HEAD_LEN + h.len) as nat),
{
    let p = payload_of(f);
    if let Frame::Headers { stream, end_stream, end_headers, pad, priority, fragment } = f {
        lemma_flags_headers(end_stream, end_headers, pad is Some, priority is Some);
        let body = match priority {
            Some(pr) => enc_priority(pr) + fragment,
            None => fragment,
        };
        let fixed: nat = if priority is Some {
            5
        } else {
            0
        };
        lemma_unpad(pad, body, fixed);
        let off: int = if pad is Some {
            1
        } else {
            0
        };
        assert(p.subrange(off + fixed, off + body.len()) =~= body.subrange(
            fixed as int,
            body.len() as int,
        )) by {
            assert(p.subrange(off, off + body.len()) == body);
            assert(p.subrange(off + fixed, off + body.len()) =~= p.subrange(
                off,
                off + body.len(),
            ).subrange(fixed as int, body.len() as int));
        }
        if let Some(pr) = priority {
            assert(body.subrange(5, body.len() as int) =~= fragment);
            assert(p.subrange(off, off + 5) =~= body.subrange(0, 5)) by {
                assert(p.subrange(off, off + 5) =~= p.subrange(off, off + body.len()).subrange(
                    0,
                    5,
                ));
            }
            assert(body.subrange(0, 5) =~= enc_priority(pr));
            lemma_priority(p, off, pr);
        } else {
            assert(body.subrange(0, body.len() as int) =~= fragment);
        }
    }
}

proof fn lemma_payload_pushpromise(f: Frame, h: Head)
    requires
        f is PushPromise,
        wf(f, MAX_MAX_FRAME_SIZE),
        h == (Head {
            len: payload_of(f).len() as u32,
            ty: type_of(f),
            flags: flags_of(f),
            stream: stream_of(f),
        }),
    ensures
        payload(h, payload_of(f)) == Res::Frame(f, (HEAD_LEN + h.len) as nat),
{
    let p = payload_of(f);
    if let Frame::PushPromise { stream, end_headers, pad, promised, fragment } = f {
        lemma_flags_pp(end_headers, pad is Some);
        let body = enc32(promised) + fragment;
        lemma_unpad(pad, body, 4);
        let off: int = if pad is Some {
            1
        } else {
            0
        };
        assert(p.subrange(off, off + body.len()) == body);
        assert(p.subrange(off + 4, off + body.len()) =~= fragment) by {
            assert(p.subrange(off + 4, off + body.len()) =~= p.subrange(
                off,
                off + body.len(),
            ).subrange(4, body.len() as int));
        }
        assert(p.subrange(off, off + 4) =~= enc32(promised)) by {
            assert(p.subrange(off, off + 4) =~= p.subrange(off, off + body.len()).subrange(0, 4));
        }
        lemma_be32(p, off, promised);
        lemma_31(promised);
    }
}

/// What the parser returns is well-formed, and is as long as its own
/// serialization.
pub proof fn lemma_parse_wf(b: Seq<u8>, max: u32)
    requires
        max <= MAX_MAX_FRAME_SIZE,
    ensures
        parse(b, max) matches Res::Frame(f, n) ==> wf(f, max) && n == serialize(f).len(),
{
    if b.len() >= HEAD_LEN {
        let h = head(b);
        if h.len <= max && b.len() >= HEAD_LEN + h.len {
            let p = b.subrange(HEAD_LEN as int, HEAD_LEN + h.len);
            assert(h.stream <= MAX_31) by {
                let x = be32(b, 5);
                assert(x & 0x7fff_ffff <= 0x7fff_ffff) by (bit_vector);
            }
            lemma_payload_wf(h, p, max);
        }
    }
}

proof fn lemma_payload_wf(h: Head, p: Seq<u8>, max: u32)
    requires
        p.len() == h.len,
        h.len <= max <= MAX_MAX_FRAME_SIZE,
        h.stream <= MAX_31,
    ensures
        payload(h, p) matches Res::Frame(f, n) ==> wf(f, max) && n == HEAD_LEN + payload_of(f).len(),
{
    if let Res::Frame(f, n) = payload(h, p) {
        lemma_payload_len(h, p);
    }
}

/// The payload of a parsed frame serializes to as many bytes as it took,
/// and its values are in range.
proof fn lemma_payload_len(h: Head, p: Seq<u8>)
    requires
        p.len() == h.len,
        h.len <= MAX_MAX_FRAME_SIZE,
        h.stream <= MAX_31,
        payload(h, p) is Frame,
    ensures
        ({
            let f = payload(h, p)->Frame_0;
            &&& payload_of(f).len() == p.len()
            &&& stream_of(f) <= MAX_31
            &&& wf(f, h.len)
        }),
{
    let f = payload(h, p)->Frame_0;
    assert(forall|x: u32| #[trigger] (x & 0x7fff_ffff) <= 0x7fff_ffff) by {
        assert(forall|x: u32| #[trigger] (x & 0x7fff_ffff) <= 0x7fff_ffff) by (bit_vector);
    }
    match f {
        Frame::Settings { ack, params: ps } => {
            lemma_enc_params(p);
        },
        _ => {},
    }
}

/// Bytes after a decided frame change nothing.
pub proof fn lemma_parse_prefix(b: Seq<u8>, rest: Seq<u8>, max: u32)
    requires
        !(parse(b, max) is Incomplete),
    ensures
        parse(b + rest, max) == parse(b, max),
{
    let c = b + rest;
    assert(c.subrange(0, b.len() as int) =~= b);
    let h = head(b);
    assert(head(c) == h);
    if h.len <= max {
        assert(c.subrange(HEAD_LEN as int, HEAD_LEN + h.len) =~= b.subrange(
            HEAD_LEN as int,
            HEAD_LEN + h.len,
        ));
    }
}

} // verus!
