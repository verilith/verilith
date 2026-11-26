//! Lemmas about the specification: framing (a parse depends only on the
//! bytes it reads) and the round trips.
use crate::spec::*;
use crate::varint::*;
use vstd::prelude::*;

verus! {

/// Equal windows of two sequences have equal sub-windows.
pub proof fn lemma_sub_sub(b: Seq<u8>, p: int, c: Seq<u8>, q: int, n: int, i: int, j: int)
    requires
        0 <= p,
        0 <= q,
        p + n <= b.len(),
        q + n <= c.len(),
        c.subrange(q, q + n) == b.subrange(p, p + n),
        0 <= i <= j <= n,
    ensures
        c.subrange(q + i, q + j) == b.subrange(p + i, p + j),
{
    assert forall|k: int| 0 <= k < j - i implies #[trigger] c.subrange(q + i, q + j)[k] == b.subrange(
        p + i,
        p + j,
    )[k] by {
        assert(c.subrange(q, q + n)[i + k] == b.subrange(p, p + n)[i + k]);
        assert(c.subrange(q, q + n)[i + k] == c[q + i + k]);
        assert(b.subrange(p, p + n)[i + k] == b[p + i + k]);
    }
    assert(c.subrange(q + i, q + j) =~= b.subrange(p + i, p + j));
}

/// ACK ranges parse the same from any copy of their bytes.
pub proof fn lemma_ack_ranges_frame(b: Seq<u8>, p: int, count: nat, s: u64, c: Seq<u8>, q: int)
    requires
        ack_ranges(b, p, count, s) is Some,
        0 <= p,
        0 <= q,
        q + (ack_ranges(b, p, count, s).unwrap().1 - p) <= c.len(),
        ack_ranges(b, p, count, s).unwrap().1 <= b.len(),
        c.subrange(q, q + (ack_ranges(b, p, count, s).unwrap().1 - p)) == b.subrange(
            p,
            ack_ranges(b, p, count, s).unwrap().1,
        ),
    ensures
        ack_ranges(c, q, count, s) == Some(
            (ack_ranges(b, p, count, s).unwrap().0, q + (ack_ranges(b, p, count, s).unwrap().1 - p)),
        ),
    decreases count,
{
    let e = ack_ranges(b, p, count, s).unwrap().1;
    lemma_ack_ranges_end(b, p, count, s);
    if count > 0 {
        let (gap, p1) = varint(b, p).unwrap();
        let (len, p2) = varint(b, p1).unwrap();
        lemma_varint_bound(b, p);
        lemma_varint_bound(b, p1);
        lemma_ack_ranges_end(b, p2, (count - 1) as nat, (s - gap - 2 - len) as u64);
        lemma_sub_sub(b, p, c, q, e - p, 0, p1 - p);
        lemma_varint_frame(b, p, c, q);
        lemma_sub_sub(b, p, c, q, e - p, p1 - p, p2 - p);
        lemma_varint_frame(b, p1, c, q + (p1 - p));
        lemma_sub_sub(b, p, c, q, e - p, p2 - p, e - p);
        lemma_ack_ranges_frame(b, p2, (count - 1) as nat, (s - gap - 2 - len) as u64, c, q + (p2 - p));
    }
}

/// ACK ranges end at or after where they start.
pub proof fn lemma_ack_ranges_end(b: Seq<u8>, p: int, count: nat, s: u64)
    ensures
        ack_ranges(b, p, count, s) matches Some((rs, e)) ==> p <= e && rs.len() == count && (count
            > 0 ==> e <= b.len()),
    decreases count,
{
    if count > 0 {
        lemma_varint_bound(b, p);
        if let Some((gap, p1)) = varint(b, p) {
            lemma_varint_bound(b, p1);
            if let Some((len, p2)) = varint(b, p1) {
                if gap as int + 2 <= s && len as int <= s - gap - 2 {
                    lemma_ack_ranges_end(b, p2, (count - 1) as nat, (s - gap - 2 - len) as u64);
                }
            }
        }
    }
}


// ---------------------------------------------------------------------------
// Reading back what was written
// ---------------------------------------------------------------------------

/// `pre + s + rest` holds `s` after `pre`.
pub proof fn lemma_at_whole(pre: Seq<u8>, s: Seq<u8>, rest: Seq<u8>)
    ensures
        at(pre + s + rest, pre.len() as int, s),
{
    assert((pre + s + rest).subrange(pre.len() as int, (pre.len() + s.len()) as int) =~= s);
}

pub broadcast proof fn lemma_at_split(b: Seq<u8>, p: int, s1: Seq<u8>, s2: Seq<u8>)
    requires
        #[trigger] at(b, p, s1 + s2),
    ensures
        at(b, p, s1),
        at(b, p + s1.len(), s2),
{
    assert((s1 + s2).subrange(0, (s1 + s2).len() as int) =~= s1 + s2);
    lemma_sub_sub(s1 + s2, 0, b, p, (s1.len() + s2.len()) as int, 0, s1.len() as int);
    lemma_sub_sub(s1 + s2, 0, b, p, (s1.len() + s2.len()) as int, s1.len() as int, (s1.len() + s2.len()) as int);
    assert((s1 + s2).subrange(0, (s1 + s2).len() as int) =~= s1 + s2);
    assert((s1 + s2).subrange(0, s1.len() as int) =~= s1);
    assert((s1 + s2).subrange(s1.len() as int, (s1.len() + s2.len()) as int) =~= s2);
}

pub broadcast proof fn lemma_at_varint(b: Seq<u8>, p: int, v: u64)
    requires
        #[trigger] at(b, p, varint_enc(v)),
        v < VARINT_LIMIT,
    ensures
        varint(b, p) == Some((v, p + varint_size(v))),
{
    lemma_varint_roundtrip(v, Seq::empty(), Seq::empty());
    let e = varint_enc(v);
    assert(Seq::<u8>::empty() + e + Seq::<u8>::empty() =~= e);
    assert(e.subrange(0, e.len() as int) =~= e);
    lemma_varint_frame(e, 0, b, p);
}

pub broadcast proof fn lemma_varint_size(v: u64)
    ensures
        #[trigger] varint_enc(v).len() == varint_size(v),
{
}

pub broadcast proof fn lemma_at_byte(b: Seq<u8>, p: int, x: u8)
    requires
        #[trigger] at(b, p, seq![x]),
    ensures
        0 <= p < b.len(),
        b[p] == x,
{
    assert(b.subrange(p, p + 1)[0] == b[p]);
}

pub broadcast proof fn lemma_at_take(b: Seq<u8>, p: int, d: Seq<u8>)
    requires
        #[trigger] at(b, p, d),
    ensures
        take(b, p, d.len() as int) == Some((d, p + d.len())),
{
}

pub broadcast proof fn lemma_at_bytes_len(b: Seq<u8>, p: int, d: Seq<u8>)
    requires
        #[trigger] at(b, p, bytes_len_enc(d)),
        d.len() < VARINT_LIMIT,
    ensures
        bytes_len(b, p) == Some((d, p + varint_size(d.len() as u64) + d.len())),
{
    lemma_at_split(b, p, varint_enc(d.len() as u64), d);
    lemma_at_varint(b, p, d.len() as u64);
    lemma_at_take(b, p + varint_size(d.len() as u64), d);
}

/// The encoding of valid ACK ranges parses back.
pub proof fn lemma_ack_ranges_roundtrip(b: Seq<u8>, p: int, rs: Seq<(u64, u64)>, s: u64)
    requires
        ack_ranges_wf(rs, s),
        at(b, p, ack_ranges_enc(rs)),
    ensures
        ack_ranges(b, p, rs.len(), s) == Some((rs, p + ack_ranges_enc(rs).len())),
    decreases rs.len(),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size;

    if rs.len() == 0 {
        assert(rs =~= Seq::<(u64, u64)>::empty());
    } else {
        let (gap, len) = rs[0];
        let e1 = varint_enc(gap);
        let e2 = varint_enc(len);
        let tl = ack_ranges_enc(rs.drop_first());
        assert(ack_ranges_enc(rs) == e1 + e2 + tl);
        lemma_at_split(b, p, e1 + e2, tl);
        lemma_at_split(b, p, e1, e2);
        lemma_ack_ranges_roundtrip(b, p + e1.len() + e2.len(), rs.drop_first(), (s - gap - 2 - len) as u64);
        assert(seq![(gap, len)] + rs.drop_first() =~= rs);
    }
}

/// The number of zero bytes after a run of `n` and a nonzero byte (or the
/// end).
pub proof fn lemma_zeros_run(b: Seq<u8>, p: int, n: nat)
    requires
        at(b, p, Seq::new(n, |i: int| 0u8)),
        p + n == b.len() || b[p + n] != 0,
    ensures
        zeros(b, p) == n,
    decreases n,
{
    if n > 0 {
        assert(b[p] == 0) by {
            assert(b.subrange(p, p + n)[0] == b[p]);
        }
        let z = Seq::new((n - 1) as nat, |i: int| 0u8);
        assert(b.subrange(p + 1, p + n) =~= z) by {
            let zn = Seq::new(n, |i: int| 0u8);
            assert(zn.subrange(0, n as int) =~= zn);
            lemma_sub_sub(zn, 0, b, p, n as int, 1, n as int);
            assert(zn.subrange(1, n as int) =~= z);
        }
        lemma_zeros_run(b, p + 1, (n - 1) as nat);
    } else {
    }
}

/// The STREAM frame type with the OFF, LEN and FIN bits.
pub proof fn lemma_stream_type(o: bool, l: bool, f: bool)
    ensures
        ({
            let t: u8 = (0x08u8 | (if o { 0x04u8 } else { 0u8 }) | (if l { 0x02u8 } else { 0u8 }) | (if f {
                0x01u8
            } else {
                0u8
            })) as u8;
            &&& 0x08 <= t <= 0x0f
            &&& (t & 0x04 != 0) == o
            &&& (t & 0x02 != 0) == l
            &&& (t & 0x01 != 0) == f
        }),
{
    let a: u8 = if o { 0x04u8 } else { 0u8 };
    let c: u8 = if l { 0x02u8 } else { 0u8 };
    let d: u8 = if f { 0x01u8 } else { 0u8 };
    assert(((a == 0 || a == 4) && (c == 0 || c == 2) && (d == 0 || d == 1)) ==> ({
        let t: u8 = (0x08u8 | a | c | d) as u8;
        &&& 0x08 <= t <= 0x0f
        &&& (t & 0x04 != 0) == (a != 0)
        &&& (t & 0x02 != 0) == (c != 0)
        &&& (t & 0x01 != 0) == (d != 0)
    })) by (bit_vector);
}

proof fn rt_padding(b: Seq<u8>, p: int, n: nat, rest: Seq<u8>)
    requires
        n >= 1,
        at(b, p, Seq::new(n, |i: int| 0u8)),
        b.len() == p + n + rest.len(),
        rest.len() == 0 || rest[0] != 0,
        rest.len() > 0 ==> b[p + n] == rest[0],
    ensures
        frame(b, p) == Some((Fr::Padding { n }, p + n)),
{
    assert(b[p] == 0) by {
        assert(b.subrange(p, p + n)[0] == b[p]);
    }
    lemma_zeros_run(b, p, n);
}

#[verifier::rlimit(40)]
proof fn rt_ack(b: Seq<u8>, p: int, f: Fr)
    requires
        f is Ack,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte;

    if let Fr::Ack { largest, delay, first, ranges, ecn } = f {
        let pr = p + 1 + varint_size(largest) + varint_size(delay) + varint_size(ranges.len() as u64) + varint_size(first);
        let body = varint_enc(largest) + varint_enc(delay) + varint_enc(ranges.len() as u64)
            + varint_enc(first) + ack_ranges_enc(ranges);
        match ecn {
            None => {
                assert(at(b, p, seq![0x02u8] + body));
            },
            Some((e0, e1, ce)) => {
                assert(at(b, p, seq![0x03u8] + body + varint_enc(e0) + varint_enc(e1) + varint_enc(ce)));
            },
        }
        assert(at(b, pr, ack_ranges_enc(ranges)));
        lemma_ack_ranges_roundtrip(b, pr, ranges, (largest - first) as u64);
    }
}

proof fn rt_stream(b: Seq<u8>, p: int, f: Fr)
    requires
        f is Stream,
        frame_wf(f),
        at(b, p, frame_enc(f)),
        !f->Stream_len ==> b.len() == p + frame_enc(f).len(),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::Stream { id, offset, len, fin, data } = f {
        lemma_stream_type(offset != 0, len, fin);
        let t: u8 = (0x08u8 | (if offset != 0 { 0x04u8 } else { 0u8 }) | (if len { 0x02u8 } else { 0u8 }) | (if fin {
            0x01u8
        } else {
            0u8
        })) as u8;
        let oe: Seq<u8> = if offset != 0 { varint_enc(offset) } else { Seq::empty() };
        let de: Seq<u8> = if len { bytes_len_enc(data) } else { data };
        assert(frame_enc(f) == seq![t] + varint_enc(id) + oe + de);
        assert(at(b, p, seq![t] + varint_enc(id) + oe + de));
        assert(at(b, p + 1 + varint_size(id), oe));
    }
}

proof fn rt_ping(b: Seq<u8>, p: int, f: Fr)
    requires
        f is Ping,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::Ping = f {
        assert(at(b, p, seq![0x01u8]));
    }
}

proof fn rt_reset_stream(b: Seq<u8>, p: int, f: Fr)
    requires
        f is ResetStream,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::ResetStream { id, err, final_size } = f {
        assert(at(b, p, seq![0x04u8] + varint_enc(id) + varint_enc(err) + varint_enc(final_size)));
    }
}

proof fn rt_stop_sending(b: Seq<u8>, p: int, f: Fr)
    requires
        f is StopSending,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::StopSending { id, err } = f {
        assert(at(b, p, seq![0x05u8] + varint_enc(id) + varint_enc(err)));
    }
}

proof fn rt_crypto(b: Seq<u8>, p: int, f: Fr)
    requires
        f is Crypto,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::Crypto { offset, data } = f {
        assert(at(b, p, seq![0x06u8] + varint_enc(offset) + bytes_len_enc(data)));
    }
}

proof fn rt_new_token(b: Seq<u8>, p: int, f: Fr)
    requires
        f is NewToken,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::NewToken { token } = f {
        assert(at(b, p, seq![0x07u8] + bytes_len_enc(token)));
    }
}

proof fn rt_max_data(b: Seq<u8>, p: int, f: Fr)
    requires
        f is MaxData,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::MaxData { max } = f {
        assert(at(b, p, seq![0x10u8] + varint_enc(max)));
    }
}

proof fn rt_max_stream_data(b: Seq<u8>, p: int, f: Fr)
    requires
        f is MaxStreamData,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::MaxStreamData { id, max } = f {
        assert(at(b, p, seq![0x11u8] + varint_enc(id) + varint_enc(max)));
    }
}

proof fn rt_max_streams(b: Seq<u8>, p: int, f: Fr)
    requires
        f is MaxStreams,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::MaxStreams { bidi, max } = f {
        assert(at(b, p, seq![if bidi { 0x12u8 } else { 0x13u8 }] + varint_enc(max)));
    }
}

proof fn rt_data_blocked(b: Seq<u8>, p: int, f: Fr)
    requires
        f is DataBlocked,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::DataBlocked { max } = f {
        assert(at(b, p, seq![0x14u8] + varint_enc(max)));
    }
}

proof fn rt_stream_data_blocked(b: Seq<u8>, p: int, f: Fr)
    requires
        f is StreamDataBlocked,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::StreamDataBlocked { id, max } = f {
        assert(at(b, p, seq![0x15u8] + varint_enc(id) + varint_enc(max)));
    }
}

proof fn rt_streams_blocked(b: Seq<u8>, p: int, f: Fr)
    requires
        f is StreamsBlocked,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::StreamsBlocked { bidi, max } = f {
        assert(at(b, p, seq![if bidi { 0x16u8 } else { 0x17u8 }] + varint_enc(max)));
    }
}

proof fn rt_new_connection_id(b: Seq<u8>, p: int, f: Fr)
    requires
        f is NewConnectionId,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::NewConnectionId { seq, retire, cid, token } = f {
        assert(at(b, p, seq![0x18u8] + varint_enc(seq) + varint_enc(retire) + seq![cid.len() as u8] + cid + token));
    }
}

proof fn rt_retire_connection_id(b: Seq<u8>, p: int, f: Fr)
    requires
        f is RetireConnectionId,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::RetireConnectionId { seq } = f {
        assert(at(b, p, seq![0x19u8] + varint_enc(seq)));
    }
}

proof fn rt_path_challenge(b: Seq<u8>, p: int, f: Fr)
    requires
        f is PathChallenge,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::PathChallenge { data } = f {
        assert(at(b, p, seq![0x1au8] + data));
    }
}

proof fn rt_path_response(b: Seq<u8>, p: int, f: Fr)
    requires
        f is PathResponse,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::PathResponse { data } = f {
        assert(at(b, p, seq![0x1bu8] + data));
    }
}

proof fn rt_handshake_done(b: Seq<u8>, p: int, f: Fr)
    requires
        f is HandshakeDone,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::HandshakeDone = f {
        assert(at(b, p, seq![0x1eu8]));
    }
}

proof fn rt_close(b: Seq<u8>, p: int, f: Fr)
    requires
        f is ConnectionClose,
        frame_wf(f),
        at(b, p, frame_enc(f)),
    ensures
        frame(b, p) == Some((f, p + frame_enc(f).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len;

    if let Fr::ConnectionClose { app, err, frame_type, reason } = f {
        if app {
            assert(at(b, p, seq![0x1du8] + varint_enc(err) + bytes_len_enc(reason)));
        } else {
            assert(at(b, p, seq![0x1cu8] + varint_enc(err) + varint_enc(frame_type) + bytes_len_enc(reason)));
        }
    }
}

/// Round trip: the encoding of a valid frame, after anything and followed
/// by anything that may follow it, parses back to the same frame, ending
/// where the encoding ends.
pub proof fn lemma_frame_roundtrip(f: Fr, pre: Seq<u8>, rest: Seq<u8>)
    requires
        frame_wf(f),
        frame_rest_ok(f, rest),
    ensures
        frame(pre + frame_enc(f) + rest, pre.len() as int) == Some((f, (pre.len() + frame_enc(f).len()) as int)),
{
    let enc = frame_enc(f);
    let b = pre + enc + rest;
    let p = pre.len() as int;
    lemma_at_whole(pre, enc, rest);
    match f {
        Fr::Padding { n } => {
            if rest.len() > 0 {
                assert(b[p + n] == rest[0]);
            }
            rt_padding(b, p, n, rest);
        },
        Fr::Ack { .. } => rt_ack(b, p, f),
        Fr::Stream { .. } => rt_stream(b, p, f),
        Fr::Ping => rt_ping(b, p, f),
        Fr::ResetStream { .. } => rt_reset_stream(b, p, f),
        Fr::StopSending { .. } => rt_stop_sending(b, p, f),
        Fr::Crypto { .. } => rt_crypto(b, p, f),
        Fr::NewToken { .. } => rt_new_token(b, p, f),
        Fr::MaxData { .. } => rt_max_data(b, p, f),
        Fr::MaxStreamData { .. } => rt_max_stream_data(b, p, f),
        Fr::MaxStreams { .. } => rt_max_streams(b, p, f),
        Fr::DataBlocked { .. } => rt_data_blocked(b, p, f),
        Fr::StreamDataBlocked { .. } => rt_stream_data_blocked(b, p, f),
        Fr::StreamsBlocked { .. } => rt_streams_blocked(b, p, f),
        Fr::NewConnectionId { .. } => rt_new_connection_id(b, p, f),
        Fr::RetireConnectionId { .. } => rt_retire_connection_id(b, p, f),
        Fr::PathChallenge { .. } => rt_path_challenge(b, p, f),
        Fr::PathResponse { .. } => rt_path_response(b, p, f),
        Fr::HandshakeDone => rt_handshake_done(b, p, f),
        Fr::ConnectionClose { .. } => rt_close(b, p, f),
    }
}


/// The ranges from `i` on are valid after the smallest packet number the
/// ranges before them reach.
pub proof fn lemma_ack_wf_tail(rs: Seq<(u64, u64)>, i: int, s: u64)
    requires
        ack_ranges_wf(rs, s),
        0 <= i < rs.len(),
    ensures
        vi(rs[i].0) && vi(rs[i].1),
    decreases i,
{
    if i > 0 {
        let (gap, len) = rs[0];
        lemma_ack_wf_tail(rs.drop_first(), i - 1, (s - gap - 2 - len) as u64);
    }
}

// ---------------------------------------------------------------------------
// Headers
// ---------------------------------------------------------------------------

pub proof fn lemma_pow2_bytes()
    ensures
        pow2(8) == 0x100,
        pow2(16) == 0x1_0000,
        pow2(24) == 0x100_0000,
        pow2(32) == 0x1_0000_0000,
{
    reveal_with_fuel(pow2, 33);
}

/// `n` `u32`s parse the same from a copy of their bytes.
pub proof fn lemma_u32s_frame(b: Seq<u8>, q: int, n: nat)
    requires
        0 <= q,
        q + 4 * n == b.len(),
    ensures
        u32s(b, q, n) == u32s(b.subrange(q, b.len() as int), 0, n),
    decreases n,
{
    if n > 0 {
        let c = b.subrange(q, b.len() as int);
        assert(c[0] == b[q] && c[1] == b[q + 1] && c[2] == b[q + 2] && c[3] == b[q + 3]);
        lemma_u32s_frame(b, q + 4, (n - 1) as nat);
        lemma_u32s_frame(c, 4, (n - 1) as nat);
        assert(c.subrange(4, c.len() as int) =~= b.subrange(q + 4, b.len() as int));
    }
}

/// Dropping the bytes before the `u32`s.
pub proof fn lemma_u32s_shift(c: Seq<u8>, k: int, n: nat)
    requires
        0 <= k,
        k + 4 * n == c.len(),
    ensures
        u32s(c, k, n) == u32s(c.subrange(k, c.len() as int), 0, n),
{
    lemma_u32s_frame(c, k, n);
}

/// A `u32` reads back.
pub proof fn lemma_u32_roundtrip(v: u32)
    ensures
        u32be(u32_enc(v), 0) == v,
        u32_enc(v).len() == 4,
{
    let e = u32_enc(v);
    assert(e[0] == (v >> 24) as u8 && e[1] == (v >> 16) as u8 && e[2] == (v >> 8) as u8 && e[3] == v as u8);
    assert(((((v >> 24) as u8) as u32) << 24) | ((((v >> 16) as u8) as u32) << 16) | ((((v >> 8) as u8) as u32)
        << 8) | ((v as u8) as u32) == v) by (bit_vector);
}

pub broadcast proof fn lemma_at_u32(b: Seq<u8>, p: int, v: u32)
    requires
        #[trigger] at(b, p, u32_enc(v)),
    ensures
        p + 4 <= b.len(),
        u32be(b, p) == v,
{
    lemma_u32_roundtrip(v);
    let e = u32_enc(v);
    assert(b.subrange(p, p + 4)[0] == b[p] && b.subrange(p, p + 4)[1] == b[p + 1]);
    assert(b.subrange(p, p + 4)[2] == b[p + 2] && b.subrange(p, p + 4)[3] == b[p + 3]);
}

/// Bytes that are whole `u32`s are the encoding of the `u32`s they hold.
pub proof fn lemma_u32s_raw(raw: Seq<u8>)
    requires
        raw.len() % 4 == 0,
    ensures
        u32s_enc(u32s(raw, 0, (raw.len() / 4) as nat)) == raw,
    decreases raw.len(),
{
    if raw.len() > 0 {
        let tl = raw.subrange(4, raw.len() as int);
        lemma_u32s_raw(tl);
        lemma_u32s_shift(raw, 4, ((raw.len() / 4) - 1) as nat);
        let vs = u32s(raw, 0, (raw.len() / 4) as nat);
        assert(vs.drop_first() =~= u32s(raw, 4, ((raw.len() / 4) - 1) as nat));
        let v = u32be(raw, 0);
        assert(u32_enc(v) =~= raw.subrange(0, 4)) by {
            let (a, b1, c, d) = (raw[0], raw[1], raw[2], raw[3]);
            assert((((((a as u32) << 24) | ((b1 as u32) << 16) | ((c as u32) << 8) | (d as u32)) >> 24) as u8 == a
                && ((((a as u32) << 24) | ((b1 as u32) << 16) | ((c as u32) << 8) | (d as u32)) >> 16) as u8 == b1
                && ((((a as u32) << 24) | ((b1 as u32) << 16) | ((c as u32) << 8) | (d as u32)) >> 8) as u8 == c
                && (((a as u32) << 24) | ((b1 as u32) << 16) | ((c as u32) << 8) | (d as u32)) as u8 == d)) by (bit_vector);
        }
        assert(raw =~= raw.subrange(0, 4) + tl);
    }
}

/// `u32`s read back.
pub proof fn lemma_u32s_roundtrip(b: Seq<u8>, p: int, vs: Seq<u32>)
    requires
        at(b, p, u32s_enc(vs)),
    ensures
        u32s(b, p, vs.len()) == vs,
        u32s_enc(vs).len() == 4 * vs.len(),
    decreases vs.len(),
{
    broadcast use lemma_at_split, lemma_at_u32;

    if vs.len() == 0 {
        assert(vs =~= Seq::<u32>::empty());
    } else {
        lemma_u32_roundtrip(vs[0]);
        assert(u32s_enc(vs) == u32_enc(vs[0]) + u32s_enc(vs.drop_first()));
        lemma_u32s_roundtrip(b, p + 4, vs.drop_first());
        assert(seq![vs[0]] + vs.drop_first() =~= vs);
    }
}

#[verifier::rlimit(40)]
proof fn hrt_long(h: Hdr, cid_len: nat, b: Seq<u8>, p: int, rest: Seq<u8>)
    requires
        h is Long,
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
        at(b, p, header_enc(h)),
        b.len() == p + header_enc(h).len() + rest.len(),
    ensures
        header(b, p, cid_len) == Some((h, p + header_enc(h).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len, lemma_at_u32;

    let enc = header_enc(h);
    match h {
        Hdr::Long { first, dcid, scid, token, len } => {
            assert(first & 0xc0 == 0xc0 ==> first & 0x80 != 0 && first & 0x40 != 0) by (bit_vector);
            let te: Seq<u8> = if (first >> 4) & 3 == 0 { bytes_len_enc(token) } else { Seq::empty() };
            assert(at(b, p, seq![first] + u32_enc(VERSION_1) + seq![dcid.len() as u8] + dcid + seq![scid.len() as u8]
                + scid + te + varint_enc(len)));
            let q = p + 5 + 1 + dcid.len() + 1 + scid.len();
            assert(at(b, q, te));
            assert(at(b, q + te.len(), varint_enc(len)));
            lemma_u32_roundtrip(VERSION_1);
            assert(at(b, p + 5, seq![dcid.len() as u8]));
            assert(at(b, p + 6, dcid));
            assert(at(b, p + 6 + dcid.len(), seq![scid.len() as u8]));
            assert(at(b, p + 7 + dcid.len(), scid));
            assert(cids(b, p + 5, MAX_CID_LEN as int) == Some((dcid, scid, q)));
            assert(u32be(b, p + 1) == VERSION_1);
            let ty = (first >> 4) & 3;
            if ty == 0 {
                assert(bytes_len(b, q) == Some((token, q + te.len())));
            } else {
                assert(token =~= Seq::<u8>::empty());
                assert(te.len() == 0);
            }
            assert(varint(b, q + te.len()) == Some((len, q + te.len() + varint_size(len))));
            assert(enc.len() == q + te.len() + varint_size(len) - p);
            assert(b.len() == p + enc.len() + rest.len());
        },
        _ => {},
    }
}

#[verifier::rlimit(40)]
proof fn hrt_retry(h: Hdr, cid_len: nat, b: Seq<u8>, p: int, rest: Seq<u8>)
    requires
        h is Retry,
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
        at(b, p, header_enc(h)),
        b.len() == p + header_enc(h).len() + rest.len(),
    ensures
        header(b, p, cid_len) == Some((h, p + header_enc(h).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len, lemma_at_u32;

    let enc = header_enc(h);
    match h {
        Hdr::Retry { first, dcid, scid, token, tag } => {
            assert(first & 0xc0 == 0xc0 ==> first & 0x80 != 0 && first & 0x40 != 0) by (bit_vector);
            assert(at(b, p, seq![first] + u32_enc(VERSION_1) + seq![dcid.len() as u8] + dcid + seq![scid.len() as u8]
                + scid + token + tag));
            lemma_u32_roundtrip(VERSION_1);
            assert(b.len() == p + enc.len());
        },
        _ => {},
    }
}

#[verifier::rlimit(40)]
proof fn hrt_version_negotiation(h: Hdr, cid_len: nat, b: Seq<u8>, p: int, rest: Seq<u8>)
    requires
        h is VersionNegotiation,
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
        at(b, p, header_enc(h)),
        b.len() == p + header_enc(h).len() + rest.len(),
    ensures
        header(b, p, cid_len) == Some((h, p + header_enc(h).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len, lemma_at_u32;

    let enc = header_enc(h);
    match h {
        Hdr::VersionNegotiation { first, dcid, scid, versions } => {
            assert(at(b, p, seq![first] + u32_enc(0) + seq![dcid.len() as u8] + dcid + seq![scid.len() as u8] + scid
                + u32s_enc(versions)));
            let q = p + 5 + 1 + dcid.len() + 1 + scid.len();
            lemma_u32s_roundtrip(b, q, versions);
            assert(b.len() == q + 4 * versions.len());
            assert((4 * versions.len()) % 4 == 0 && (4 * versions.len()) / 4 == versions.len()) by (nonlinear_arith);
        },
        _ => {},
    }
}

#[verifier::rlimit(40)]
proof fn hrt_other_version(h: Hdr, cid_len: nat, b: Seq<u8>, p: int, rest: Seq<u8>)
    requires
        h is OtherVersion,
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
        at(b, p, header_enc(h)),
        b.len() == p + header_enc(h).len() + rest.len(),
    ensures
        header(b, p, cid_len) == Some((h, p + header_enc(h).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len, lemma_at_u32;

    let enc = header_enc(h);
    match h {
        Hdr::OtherVersion { first, version, dcid, scid } => {
            assert(at(b, p, seq![first] + u32_enc(version) + seq![dcid.len() as u8] + dcid + seq![scid.len() as u8]
                + scid));
        },
        _ => {},
    }
}

#[verifier::rlimit(40)]
proof fn hrt_short(h: Hdr, cid_len: nat, b: Seq<u8>, p: int, rest: Seq<u8>)
    requires
        h is Short,
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
        at(b, p, header_enc(h)),
        b.len() == p + header_enc(h).len() + rest.len(),
    ensures
        header(b, p, cid_len) == Some((h, p + header_enc(h).len())),
{
    broadcast use lemma_at_split, lemma_at_varint, lemma_varint_size, lemma_at_byte, lemma_at_take, lemma_at_bytes_len, lemma_at_u32;

    let enc = header_enc(h);
    match h {
        Hdr::Short { first, dcid } => {
            assert(first & 0xc0 == 0x40 ==> first & 0x80 == 0 && first & 0x40 != 0) by (bit_vector);
            assert(at(b, p, seq![first] + dcid));
        },
        _ => {},
    }
}

/// Round trip: a valid header, followed by what may follow it, parses
/// back, ending where its encoding ends.
pub proof fn lemma_header_roundtrip(h: Hdr, cid_len: nat, pre: Seq<u8>, rest: Seq<u8>)
    requires
        header_wf(h, cid_len),
        header_rest_ok(h, rest),
    ensures
        header(pre + header_enc(h) + rest, pre.len() as int, cid_len) == Some(
            (h, (pre.len() + header_enc(h).len()) as int),
        ),
{
    let enc = header_enc(h);
    let b = pre + enc + rest;
    let p = pre.len() as int;
    lemma_at_whole(pre, enc, rest);
    match h {
        Hdr::Long { .. } => hrt_long(h, cid_len, b, p, rest),
        Hdr::Retry { .. } => hrt_retry(h, cid_len, b, p, rest),
        Hdr::VersionNegotiation { .. } => hrt_version_negotiation(h, cid_len, b, p, rest),
        Hdr::OtherVersion { .. } => hrt_other_version(h, cid_len, b, p, rest),
        Hdr::Short { .. } => hrt_short(h, cid_len, b, p, rest),
    }
}

// ---------------------------------------------------------------------------
// Packet numbers
// ---------------------------------------------------------------------------

/// Appendix A.3 recovers every packet number within half a window of the
/// one expected.
pub proof fn lemma_decode_pn(expected: int, pn: int, nbits: nat)
    requires
        nbits == 8 || nbits == 16 || nbits == 24 || nbits == 32,
        0 <= expected,
        0 <= pn < VARINT_LIMIT,
        expected - pow2(nbits) / 2 < pn <= expected + pow2(nbits) / 2,
    ensures
        decode_pn(expected, pn % (pow2(nbits) as int), nbits) == pn,
{
    lemma_pow2_bytes();
    let win = pow2(nbits) as int;
    let hwin = win / 2;
    let t = pn % win;
    let base = expected - expected % win;
    let candidate = base + t;
    assert(0 <= expected % win < win);
    assert(0 <= t < win);
    // pn and candidate differ by a multiple of win.
    assert(pn == (pn / win) * win + t) by (nonlinear_arith)
        requires win > 0, t == pn % win;
    assert(base == (expected / win) * win) by (nonlinear_arith)
        requires win > 0, base == expected - expected % win;
    let k = pn / win - expected / win;
    assert(pn - candidate == k * win) by (nonlinear_arith)
        requires pn == (pn / win) * win + t, base == (expected / win) * win, candidate == base + t, k == pn / win
            - expected / win;
    // |pn - expected| <= hwin, |candidate - expected| < win, so k is -1, 0 or 1.
    assert(-2 * win < k * win < 2 * win);
    assert(-2 < k < 2) by (nonlinear_arith)
        requires -2 * win < k * win < 2 * win, win > 0;
    if k == 0 {
        assert(candidate == pn);
    } else if k == 1 {
        assert(candidate == pn - win);
    } else {
        assert(candidate == pn + win);
    }
}

/// Appendix A.2 and A.3 together: a packet number encoded with
/// `pn_len(pn, largest_acked)` bytes is recovered by a receiver whose
/// largest received packet number `largest` is at least `largest_acked`
/// (both -1 before any) and below `pn`, with at most `2^31` packets not
/// yet acknowledged.
pub proof fn lemma_pn_roundtrip(pn: int, largest_acked: int, largest: int)
    requires
        0 <= pn < VARINT_LIMIT,
        -1 <= largest_acked <= largest < pn,
        pn - largest_acked <= 0x8000_0000,
    ensures
        ({
            let nbits = (8 * pn_len(pn, largest_acked)) as nat;
            decode_pn(largest + 1, pn % (pow2(nbits) as int), nbits) == pn
        }),
{
    lemma_pow2_bytes();
    let n = pn_len(pn, largest_acked);
    lemma_decode_pn(largest + 1, pn, (8 * n) as nat);
}
} // verus!
