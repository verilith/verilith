//! Frames (§12.4, §19): the verified parser and encoder.
//!
//! [`parse`] reads one frame at a position in a decrypted packet payload,
//! borrowing its byte strings from the payload; [`Frames`] reads them all.
//! [`encode`] appends a frame's encoding to a buffer. The proofs: `parse`
//! is `spec::frame`, `encode` is `spec::frame_enc`, and the encoding of
//! every valid frame parses back to the same frame
//! (`lemmas::lemma_frame_roundtrip`).
use crate::spec::*;
use crate::varint;
use vstd::prelude::*;
use verilith_core::prims::extend;
use vstd::slice::slice_subrange;

verus! {

/// The ACK ranges after the first (§19.3.1), still encoded. Iterate them
/// with [`Ack::ranges`].
#[derive(Clone, Copy)]
pub struct Ack<'a> {
    /// Largest Acknowledged.
    pub largest: u64,
    /// ACK Delay, in units of `2^ack_delay_exponent` microseconds.
    pub delay: u64,
    /// First ACK Range: packets `largest - first ..= largest` are
    /// acknowledged.
    pub first: u64,
    /// ACK Range Count.
    pub count: u64,
    /// The encoded (Gap, ACK Range Length) pairs, already checked.
    pub raw: &'a [u8],
    /// The ECN counts (ECT0, ECT1, ECN-CE) of an ACK frame of type 0x03.
    pub ecn: Option<(u64, u64, u64)>,
}

/// A frame (§19), borrowing its byte strings from the packet.
#[derive(Clone, Copy)]
pub enum Frame<'a> {
    /// A run of PADDING frames (§19.1) of this many bytes.
    Padding(usize),
    /// PING (§19.2).
    Ping,
    /// ACK (§19.3).
    Ack(Ack<'a>),
    /// RESET_STREAM (§19.4).
    ResetStream {
        /// Stream ID.
        id: u64,
        /// Application Protocol Error Code.
        err: u64,
        /// Final Size.
        final_size: u64,
    },
    /// STOP_SENDING (§19.5).
    StopSending {
        /// Stream ID.
        id: u64,
        /// Application Protocol Error Code.
        err: u64,
    },
    /// CRYPTO (§19.6).
    Crypto {
        /// Offset.
        offset: u64,
        /// Crypto Data.
        data: &'a [u8],
    },
    /// NEW_TOKEN (§19.7).
    NewToken(&'a [u8]),
    /// STREAM (§19.8).
    Stream {
        /// Stream ID.
        id: u64,
        /// Offset (0 without the OFF bit).
        offset: u64,
        /// Whether the frame has a Length field (the LEN bit); without one
        /// the data runs to the end of the packet.
        len: bool,
        /// The FIN bit.
        fin: bool,
        /// Stream Data.
        data: &'a [u8],
    },
    /// MAX_DATA (§19.9).
    MaxData(u64),
    /// MAX_STREAM_DATA (§19.10).
    MaxStreamData {
        /// Stream ID.
        id: u64,
        /// Maximum Stream Data.
        max: u64,
    },
    /// MAX_STREAMS (§19.11), bidirectional or unidirectional.
    MaxStreams {
        /// Type 0x12.
        bidi: bool,
        /// Maximum Streams, at most `2^60`.
        max: u64,
    },
    /// DATA_BLOCKED (§19.12).
    DataBlocked(u64),
    /// STREAM_DATA_BLOCKED (§19.13).
    StreamDataBlocked {
        /// Stream ID.
        id: u64,
        /// Maximum Stream Data.
        max: u64,
    },
    /// STREAMS_BLOCKED (§19.14).
    StreamsBlocked {
        /// Type 0x16.
        bidi: bool,
        /// Maximum Streams, at most `2^60`.
        max: u64,
    },
    /// NEW_CONNECTION_ID (§19.15).
    NewConnectionId {
        /// Sequence Number.
        seq: u64,
        /// Retire Prior To, at most `seq`.
        retire: u64,
        /// Connection ID, 1 to 20 bytes.
        cid: &'a [u8],
        /// Stateless Reset Token, 16 bytes.
        token: &'a [u8],
    },
    /// RETIRE_CONNECTION_ID (§19.16).
    RetireConnectionId(u64),
    /// PATH_CHALLENGE (§19.17), 8 bytes.
    PathChallenge(&'a [u8]),
    /// PATH_RESPONSE (§19.18), 8 bytes.
    PathResponse(&'a [u8]),
    /// CONNECTION_CLOSE (§19.19).
    ConnectionClose {
        /// Type 0x1d: an application error.
        app: bool,
        /// Error Code.
        err: u64,
        /// Frame Type (0 for type 0x1d).
        frame_type: u64,
        /// Reason Phrase.
        reason: &'a [u8],
    },
    /// HANDSHAKE_DONE (§19.20).
    HandshakeDone,
}

impl<'a> Ack<'a> {
    /// The smallest packet number of the first range.
    pub open spec fn smallest(self) -> u64 {
        (self.largest - self.first) as u64
    }

    /// The decoded ranges.
    pub open spec fn ranges_view(self) -> Seq<(u64, u64)> {
        ack_ranges(self.raw@, 0, self.count as nat, self.smallest()).unwrap().0
    }

    /// What `parse` guarantees of an ACK frame: the raw ranges are exactly
    /// `count` valid ones.
    pub open spec fn wf(self) -> bool {
        &&& self.first <= self.largest
        &&& ack_ranges(self.raw@, 0, self.count as nat, self.smallest()) matches Some((_, e))
        &&& e == self.raw@.len()
    }
}

impl<'a> Frame<'a> {
    /// The frame as `spec::Fr`.
    pub open spec fn view(self) -> Fr {
        match self {
            Frame::Padding(n) => Fr::Padding { n: n as nat },
            Frame::Ping => Fr::Ping,
            Frame::Ack(a) => Fr::Ack {
                largest: a.largest,
                delay: a.delay,
                first: a.first,
                ranges: a.ranges_view(),
                ecn: a.ecn,
            },
            Frame::ResetStream { id, err, final_size } => Fr::ResetStream { id, err, final_size },
            Frame::StopSending { id, err } => Fr::StopSending { id, err },
            Frame::Crypto { offset, data } => Fr::Crypto { offset, data: data@ },
            Frame::NewToken(t) => Fr::NewToken { token: t@ },
            Frame::Stream { id, offset, len, fin, data } => Fr::Stream { id, offset, len, fin, data: data@ },
            Frame::MaxData(m) => Fr::MaxData { max: m },
            Frame::MaxStreamData { id, max } => Fr::MaxStreamData { id, max },
            Frame::MaxStreams { bidi, max } => Fr::MaxStreams { bidi, max },
            Frame::DataBlocked(m) => Fr::DataBlocked { max: m },
            Frame::StreamDataBlocked { id, max } => Fr::StreamDataBlocked { id, max },
            Frame::StreamsBlocked { bidi, max } => Fr::StreamsBlocked { bidi, max },
            Frame::NewConnectionId { seq, retire, cid, token } => Fr::NewConnectionId {
                seq,
                retire,
                cid: cid@,
                token: token@,
            },
            Frame::RetireConnectionId(s) => Fr::RetireConnectionId { seq: s },
            Frame::PathChallenge(d) => Fr::PathChallenge { data: d@ },
            Frame::PathResponse(d) => Fr::PathResponse { data: d@ },
            Frame::ConnectionClose { app, err, frame_type, reason } => Fr::ConnectionClose {
                app,
                err,
                frame_type,
                reason: reason@,
            },
            Frame::HandshakeDone => Fr::HandshakeDone,
        }
    }

    /// An ACK frame's ranges are well formed.
    pub open spec fn wf(self) -> bool {
        self matches Frame::Ack(a) ==> a.wf()
    }
}

/// `r` is the exec form of the spec result `s`.
pub open spec fn res_matches<'a>(r: Option<(Frame<'a>, usize)>, s: Option<(Fr, int)>) -> bool {
    match (r, s) {
        (None, None) => true,
        (Some((f, e)), Some((sf, se))) => f.wf() && f@ == sf && e == se,
        _ => false,
    }
}

/// Two varints.
#[inline(always)]
fn read2(b: &[u8], p: usize) -> (r: Option<(u64, u64, usize)>)
    ensures
        match (r, varint2(b@, p as int)) {
            (None, None) => true,
            (Some((x, y, e)), Some((sx, sy, se))) => x == sx && y == sy && e == se,
            _ => false,
        },
        r matches Some((x, y, e)) ==> p < e <= b@.len(),
{
    let (x, p1) = match varint::read(b, p) {
        None => return None,
        Some(v) => v,
    };
    let (y, p2) = match varint::read(b, p1) {
        None => return None,
        Some(v) => v,
    };
    Some((x, y, p2))
}

/// Three varints.
#[inline(always)]
fn read3(b: &[u8], p: usize) -> (r: Option<(u64, u64, u64, usize)>)
    ensures
        match (r, varint3(b@, p as int)) {
            (None, None) => true,
            (Some((x, y, z, e)), Some((sx, sy, sz, se))) => x == sx && y == sy && z == sz && e == se,
            _ => false,
        },
        r matches Some((x, y, z, e)) ==> p < e <= b@.len(),
{
    let (x, y, p2) = match read2(b, p) {
        None => return None,
        Some(v) => v,
    };
    let (z, p3) = match varint::read(b, p2) {
        None => return None,
        Some(v) => v,
    };
    Some((x, y, z, p3))
}

/// `n` bytes from `p`.
#[inline(always)]
fn take_exec<'a>(b: &'a [u8], p: usize, n: u64) -> (r: Option<(&'a [u8], usize)>)
    requires
        p <= b@.len(),
    ensures
        match (r, take(b@, p as int, n as int)) {
            (None, None) => true,
            (Some((d, e)), Some((sd, se))) => d@ == sd && e == se,
            _ => false,
        },
{
    if n > (b.len() - p) as u64 {
        return None;
    }
    let e = p + n as usize;
    Some((slice_subrange(b, p, e), e))
}

/// A varint length and that many bytes.
#[inline(always)]
fn read_bytes<'a>(b: &'a [u8], p: usize) -> (r: Option<(&'a [u8], usize)>)
    ensures
        match (r, bytes_len(b@, p as int)) {
            (None, None) => true,
            (Some((d, e)), Some((sd, se))) => d@ == sd && e == se,
            _ => false,
        },
        r matches Some((d, e)) ==> p < e <= b@.len(),
{
    let (n, p1) = match varint::read(b, p) {
        None => return None,
        Some(v) => v,
    };
    take_exec(b, p1, n)
}

/// The number of zero bytes from `p`.
#[inline(always)]
fn count_zeros(b: &[u8], p: usize) -> (r: usize)
    requires
        p <= b@.len(),
    ensures
        r == zeros(b@, p as int),
        p + r <= b@.len(),
{
    let mut i = p;
    while i < b.len() && b[i] == 0
        invariant
            p <= i <= b@.len(),
            zeros(b@, p as int) == (i - p) + zeros(b@, i as int),
        decreases b@.len() - i,
    {
        i = i + 1;
    }
    proof {
        lemma_zeros_bound(b@, i as int);
    }
    i - p
}

proof fn lemma_zeros_bound(b: Seq<u8>, p: int)
    requires
        0 <= p <= b.len(),
    ensures
        p + zeros(b, p) <= b.len(),
    decreases b.len() - p,
{
    if p < b.len() && b[p] == 0 {
        lemma_zeros_bound(b, p + 1);
    }
}

/// Where ACK ranges end.
pub open spec fn ack_end(r: Option<(Seq<(u64, u64)>, int)>) -> Option<int> {
    match r {
        None => None,
        Some((_, e)) => Some(e),
    }
}

/// Checks `count` ACK ranges from `p`.
fn check_ranges(b: &[u8], p: usize, count: u64, smallest: u64) -> (r: Option<usize>)
    requires
        p <= b@.len(),
    ensures
        match (r, ack_ranges(b@, p as int, count as nat, smallest)) {
            (None, None) => true,
            (Some(e), Some((_, se))) => e == se,
            _ => false,
        },
        r matches Some(e) ==> p <= e <= b@.len(),
{
    let mut i: u64 = 0;
    let mut q = p;
    let mut s = smallest;
    while i < count
        invariant
            i <= count,
            p <= q <= b@.len(),
            ack_end(ack_ranges(b@, p as int, count as nat, smallest)) == ack_end(
                ack_ranges(b@, q as int, (count - i) as nat, s),
            ),
        decreases count - i,
    {
        let (gap, len, q2) = match read2(b, q) {
            None => return None,
            Some(v) => v,
        };
        if gap > s || s - gap < 2 || len > s - gap - 2 {
            return None;
        }
        s = s - gap - 2 - len;
        q = q2;
        i = i + 1;
    }
    Some(q)
}

/// Parses the frame at `b[pos]` (§19): `spec::frame`. `None` is a
/// connection error of type FRAME_ENCODING_ERROR.
pub fn parse<'a>(b: &'a [u8], pos: usize) -> (r: Option<(Frame<'a>, usize)>)
    ensures
        res_matches(r, frame(b@, pos as int)),
        r matches Some((_, e)) ==> pos < e <= b@.len(),
{
    if pos >= b.len() {
        return None;
    }
    let t = b[pos];
    let q = pos + 1;
    if t == 0x00 {
        let n = count_zeros(b, pos);
        Some((Frame::Padding(n), pos + n))
    } else if t == 0x01 {
        Some((Frame::Ping, q))
    } else if t == 0x02 || t == 0x03 {
        parse_ack(b, q, t)
    } else if t == 0x04 {
        let (id, err, final_size, e) = match read3(b, q) {
            None => return None,
            Some(v) => v,
        };
        Some((Frame::ResetStream { id, err, final_size }, e))
    } else if t == 0x05 {
        let (id, err, e) = match read2(b, q) {
            None => return None,
            Some(v) => v,
        };
        Some((Frame::StopSending { id, err }, e))
    } else if t == 0x06 {
        let (offset, q1) = match varint::read(b, q) {
            None => return None,
            Some(v) => v,
        };
        let (data, e) = match read_bytes(b, q1) {
            None => return None,
            Some(v) => v,
        };
        if data.len() as u64 > VARINT_MAX - offset {
            return None;
        }
        Some((Frame::Crypto { offset, data }, e))
    } else if t == 0x07 {
        let (token, e) = match read_bytes(b, q) {
            None => return None,
            Some(v) => v,
        };
        if token.len() == 0 {
            return None;
        }
        Some((Frame::NewToken(token), e))
    } else if t <= 0x0f {
        parse_stream(b, q, t)
    } else if t == 0x10 || t == 0x14 || t == 0x19 {
        let (x, e) = match varint::read(b, q) {
            None => return None,
            Some(v) => v,
        };
        Some(
            (
                if t == 0x10 {
                    Frame::MaxData(x)
                } else if t == 0x14 {
                    Frame::DataBlocked(x)
                } else {
                    Frame::RetireConnectionId(x)
                },
                e,
            ),
        )
    } else if t == 0x11 || t == 0x15 {
        let (id, max, e) = match read2(b, q) {
            None => return None,
            Some(v) => v,
        };
        Some(
            (
                if t == 0x11 {
                    Frame::MaxStreamData { id, max }
                } else {
                    Frame::StreamDataBlocked { id, max }
                },
                e,
            ),
        )
    } else if (0x12 <= t && t <= 0x13) || (0x16 <= t && t <= 0x17) {
        let (max, e) = match varint::read(b, q) {
            None => return None,
            Some(v) => v,
        };
        if max > MAX_STREAMS_LIMIT {
            None
        } else if t <= 0x13 {
            Some((Frame::MaxStreams { bidi: t == 0x12, max }, e))
        } else {
            Some((Frame::StreamsBlocked { bidi: t == 0x16, max }, e))
        }
    } else if t == 0x18 {
        parse_ncid(b, q)
    } else if t == 0x1a || t == 0x1b {
        let (data, e) = match take_exec(b, q, 8) {
            None => return None,
            Some(v) => v,
        };
        Some(
            (
                if t == 0x1a {
                    Frame::PathChallenge(data)
                } else {
                    Frame::PathResponse(data)
                },
                e,
            ),
        )
    } else if t == 0x1c || t == 0x1d {
        parse_close(b, q, t)
    } else if t == 0x1e {
        Some((Frame::HandshakeDone, q))
    } else {
        None
    }
}

fn parse_ack<'a>(b: &'a [u8], p: usize, t: u8) -> (r: Option<(Frame<'a>, usize)>)
    requires
        t == 0x02 || t == 0x03,
        0 < p <= b@.len(),
    ensures
        res_matches(r, ack_body(b@, p as int, t)),
        r matches Some((_, e)) ==> p < e <= b@.len(),
{
    let (largest, delay, p2) = match read2(b, p) {
        None => return None,
        Some(v) => v,
    };
    let (count, first, p4) = match read2(b, p2) {
        None => return None,
        Some(v) => v,
    };
    if first > largest {
        return None;
    }
    let p5 = match check_ranges(b, p4, count, largest - first) {
        None => return None,
        Some(e) => e,
    };
    let raw = slice_subrange(b, p4, p5);
    proof {
        assert(raw@.subrange(0, raw@.len() as int) =~= raw@);
        crate::lemmas::lemma_ack_ranges_end(b@, p4 as int, count as nat, (largest - first) as u64);
        crate::lemmas::lemma_ack_ranges_frame(b@, p4 as int, count as nat, (largest - first) as u64, raw@, 0);
    }
    if t == 0x02 {
        Some((Frame::Ack(Ack { largest, delay, first, count, raw, ecn: None }), p5))
    } else {
        let (e0, e1, ce, p6) = match read3(b, p5) {
            None => return None,
            Some(v) => v,
        };
        Some((Frame::Ack(Ack { largest, delay, first, count, raw, ecn: Some((e0, e1, ce)) }), p6))
    }
}

fn parse_stream<'a>(b: &'a [u8], p: usize, t: u8) -> (r: Option<(Frame<'a>, usize)>)
    requires
        0x08 <= t <= 0x0f,
        0 < p <= b@.len(),
    ensures
        res_matches(r, stream_body(b@, p as int, t)),
        r matches Some((_, e)) ==> p < e <= b@.len(),
{
    let (id, p1) = match varint::read(b, p) {
        None => return None,
        Some(v) => v,
    };
    let (offset, p2) = if t & 0x04 != 0 {
        match varint::read(b, p1) {
            None => return None,
            Some(v) => v,
        }
    } else {
        (0, p1)
    };
    let (data, p3) = if t & 0x02 != 0 {
        match read_bytes(b, p2) {
            None => return None,
            Some(v) => v,
        }
    } else {
        (slice_subrange(b, p2, b.len()), b.len())
    };
    proof {
        if t & 0x02 == 0 {
            assert(take(b@, p2 as int, b@.len() - p2) == Some((b@.subrange(p2 as int, b@.len() as int), b@.len() as int)));
        }
    }
    if data.len() as u64 > VARINT_MAX - offset {
        return None;
    }
    Some((Frame::Stream { id, offset, len: t & 0x02 != 0, fin: t & 0x01 != 0, data }, p3))
}

fn parse_ncid<'a>(b: &'a [u8], p: usize) -> (r: Option<(Frame<'a>, usize)>)
    requires
        0 < p <= b@.len(),
    ensures
        res_matches(r, ncid_body(b@, p as int)),
        r matches Some((_, e)) ==> p < e <= b@.len(),
{
    let (seq, retire, p2) = match read2(b, p) {
        None => return None,
        Some(v) => v,
    };
    if retire > seq || p2 >= b.len() || b[p2] < 1 || b[p2] > 20 {
        return None;
    }
    let (cid, p3) = match take_exec(b, p2 + 1, b[p2] as u64) {
        None => return None,
        Some(v) => v,
    };
    let (token, p4) = match take_exec(b, p3, 16) {
        None => return None,
        Some(v) => v,
    };
    Some((Frame::NewConnectionId { seq, retire, cid, token }, p4))
}

fn parse_close<'a>(b: &'a [u8], p: usize, t: u8) -> (r: Option<(Frame<'a>, usize)>)
    requires
        t == 0x1c || t == 0x1d,
        0 < p <= b@.len(),
    ensures
        res_matches(r, close_body(b@, p as int, t)),
        r matches Some((_, e)) ==> p < e <= b@.len(),
{
    let (err, p1) = match varint::read(b, p) {
        None => return None,
        Some(v) => v,
    };
    let (frame_type, p2) = if t == 0x1c {
        match varint::read(b, p1) {
            None => return None,
            Some(v) => v,
        }
    } else {
        (0, p1)
    };
    let (reason, p3) = match read_bytes(b, p2) {
        None => return None,
        Some(v) => v,
    };
    Some((Frame::ConnectionClose { app: t == 0x1d, err, frame_type, reason }, p3))
}

} // verus!

verus! {

/// The ACK ranges after the first, as packet numbers.
pub struct AckRanges<'a> {
    raw: &'a [u8],
    pos: usize,
    left: u64,
    smallest: u64,
}

impl<'a> AckRanges<'a> {
    /// The ranges not yet returned, as (Gap, ACK Range Length) pairs.
    pub closed spec fn rest(&self) -> Seq<(u64, u64)> {
        ack_ranges(self.raw@, self.pos as int, self.left as nat, self.smallest).unwrap().0
    }

    /// The smallest packet number acknowledged so far.
    pub closed spec fn smallest(&self) -> u64 {
        self.smallest
    }

    /// The ranges are well formed and end where the encoding ends.
    pub closed spec fn wf(&self) -> bool {
        &&& self.pos <= self.raw@.len()
        &&& ack_ranges(self.raw@, self.pos as int, self.left as nat, self.smallest) matches Some((_, e))
        &&& e == self.raw@.len()
    }

    /// The next range, `(smallest, largest)` inclusive, in descending
    /// order (§19.3.1).
    pub fn next(&mut self) -> (r: Option<(u64, u64)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self).rest().len() == 0 ==> r is None && final(self).rest() == old(self).rest(),
            old(self).rest().len() > 0 ==> {
                let (gap, len) = old(self).rest()[0];
                &&& r == Some((
                    (old(self).smallest() - gap - 2 - len) as u64,
                    (old(self).smallest() - gap - 2) as u64,
                ))
                &&& final(self).smallest() == old(self).smallest() - gap - 2 - len
                &&& final(self).rest() == old(self).rest().drop_first()
            },
    {
        proof {
            crate::lemmas::lemma_ack_ranges_end(self.raw@, self.pos as int, self.left as nat, self.smallest);
        }
        if self.left == 0 {
            return None;
        }
        let (gap, len, q) = match read2(self.raw, self.pos) {
            None => return None,
            Some(v) => v,
        };
        let hi = self.smallest - gap - 2;
        let lo = hi - len;
        proof {
            let rs = ack_ranges(self.raw@, q as int, (self.left - 1) as nat, lo).unwrap().0;
            assert((seq![(gap, len)] + rs).drop_first() =~= rs);
        }
        self.pos = q;
        self.left = self.left - 1;
        self.smallest = lo;
        Some((lo, hi))
    }
}

impl<'a> Ack<'a> {
    /// The ranges after the first one.
    pub fn ranges(&self) -> (r: AckRanges<'a>)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.rest() == self.ranges_view(),
            r.smallest() == self.smallest(),
    {
        AckRanges { raw: self.raw, pos: 0, left: self.count, smallest: self.largest - self.first }
    }
}

/// `out` is `old` followed by the encoding of `rs[..i]`, which is the start
/// of the encoding of `rs`.
proof fn lemma_ranges_enc_step(rs: Seq<(u64, u64)>, i: int)
    requires
        0 <= i < rs.len(),
    ensures
        ack_ranges_enc(rs.subrange(i, rs.len() as int)) == varint_enc(rs[i].0) + varint_enc(rs[i].1)
            + ack_ranges_enc(rs.subrange(i + 1, rs.len() as int)),
{
    assert(rs.subrange(i, rs.len() as int).drop_first() =~= rs.subrange(i + 1, rs.len() as int));
}

/// Appends the encoding of an ACK frame.
#[verifier::rlimit(60)]
fn encode_ack(a: &Ack, out: &mut Vec<u8>)
    requires
        a.wf(),
        frame_wf(Frame::Ack(*a)@),
    ensures
        final(out)@ == old(out)@ + frame_enc(Frame::Ack(*a)@),
{
    let ghost o = old(out)@;
        out.push(if a.ecn.is_some() { 0x03 } else { 0x02 });
        varint::write(out, a.largest);
        varint::write(out, a.delay);
        proof {
            crate::lemmas::lemma_ack_ranges_end(a.raw@, 0, a.count as nat, a.smallest());
        }
        varint::write(out, a.count);
        varint::write(out, a.first);
        let ghost rs = a.ranges_view();
        let ghost hdr = out@;
        let mut it = a.ranges();
        let mut i: u64 = 0;
        let mut prev = a.largest - a.first;
        proof {
            assert(rs.subrange(0, rs.len() as int) =~= rs);
            assert(ack_ranges_wf(rs, a.smallest()));
        }
        while i < a.count
            invariant
                it.wf(),
                prev == it.smallest(),
                rs.len() == a.count,
                i <= rs.len(),
                it.rest() == rs.subrange(i as int, rs.len() as int),
                out@ + ack_ranges_enc(it.rest()) == hdr + ack_ranges_enc(rs),
                ack_ranges_wf(rs, a.smallest()),
            decreases a.count - i,
        {
            let ghost before = out@;
            let ghost r0 = it.rest()[0];
            proof {
                lemma_ranges_enc_step(rs, i as int);
                assert(rs.subrange(i as int, rs.len() as int)[0] == rs[i as int]);
                crate::lemmas::lemma_ack_wf_tail(rs, i as int, a.smallest());
            }
            let (lo, hi) = match it.next() {
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
                Some(v) => v,
            };
            let gap = prev - hi - 2;
            let len = hi - lo;
            prev = lo;
            varint::write(out, gap);
            varint::write(out, len);
            i = i + 1;
            proof {
                assert(it.rest() =~= rs.subrange(i as int, rs.len() as int));
                assert(out@ + ack_ranges_enc(it.rest()) =~= hdr + ack_ranges_enc(rs));
            }
        }
        proof {
            assert(rs.subrange(i as int, rs.len() as int).len() == 0);
            assert(out@ =~= hdr + ack_ranges_enc(rs));
        }
        if let Some((e0, e1, ce)) = a.ecn {
            varint::write(out, e0);
            varint::write(out, e1);
            varint::write(out, ce);
        }
    proof {
        assert(out@ =~= o + frame_enc(Frame::Ack(*a)@));
    }
}

#[inline(always)]
fn enc_padding(f: &Frame, out: &mut Vec<u8>)
    requires
        f is Padding,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::Padding(n) => {
            let mut i: usize = 0;
            while i < *n
                invariant
                    i <= *n,
                    out@ == o + Seq::new(i as nat, |j: int| 0u8),
                decreases *n - i,
            {
                out.push(0);
                i = i + 1;
                proof {
                    assert(out@ =~= o + Seq::new(i as nat, |j: int| 0u8));
                }
            }
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_ping(f: &Frame, out: &mut Vec<u8>)
    requires
        f is Ping,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::Ping => {
            out.push(0x01);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_ack(f: &Frame, out: &mut Vec<u8>)
    requires
        f is Ack,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::Ack(a) => {
            encode_ack(a, out);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_reset_stream(f: &Frame, out: &mut Vec<u8>)
    requires
        f is ResetStream,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::ResetStream { id, err, final_size } => {
            out.push(0x04);
            varint::write(out, *id);
            varint::write(out, *err);
            varint::write(out, *final_size);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_stop_sending(f: &Frame, out: &mut Vec<u8>)
    requires
        f is StopSending,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::StopSending { id, err } => {
            out.push(0x05);
            varint::write(out, *id);
            varint::write(out, *err);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_crypto(f: &Frame, out: &mut Vec<u8>)
    requires
        f is Crypto,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::Crypto { offset, data } => {
            out.push(0x06);
            varint::write(out, *offset);
            varint::write(out, data.len() as u64);
            extend(out, data);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_new_token(f: &Frame, out: &mut Vec<u8>)
    requires
        f is NewToken,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::NewToken(t) => {
            out.push(0x07);
            varint::write(out, t.len() as u64);
            extend(out, t);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_stream(f: &Frame, out: &mut Vec<u8>)
    requires
        f is Stream,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::Stream { id, offset, len, fin, data } => {
            let t: u8 = 0x08u8 | (if *offset != 0 { 0x04u8 } else { 0u8 }) | (if *len { 0x02u8 } else { 0u8 }) | (
            if *fin {
                0x01u8
            } else {
                0u8
            });
            out.push(t);
            varint::write(out, *id);
            if *offset != 0 {
                varint::write(out, *offset);
            }
            if *len {
                varint::write(out, data.len() as u64);
            }
            extend(out, data);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_max_data(f: &Frame, out: &mut Vec<u8>)
    requires
        f is MaxData,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::MaxData(m) => {
            out.push(0x10);
            varint::write(out, *m);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_max_stream_data(f: &Frame, out: &mut Vec<u8>)
    requires
        f is MaxStreamData,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::MaxStreamData { id, max } => {
            out.push(0x11);
            varint::write(out, *id);
            varint::write(out, *max);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_max_streams(f: &Frame, out: &mut Vec<u8>)
    requires
        f is MaxStreams,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::MaxStreams { bidi, max } => {
            out.push(if *bidi { 0x12 } else { 0x13 });
            varint::write(out, *max);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_data_blocked(f: &Frame, out: &mut Vec<u8>)
    requires
        f is DataBlocked,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::DataBlocked(m) => {
            out.push(0x14);
            varint::write(out, *m);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_stream_data_blocked(f: &Frame, out: &mut Vec<u8>)
    requires
        f is StreamDataBlocked,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::StreamDataBlocked { id, max } => {
            out.push(0x15);
            varint::write(out, *id);
            varint::write(out, *max);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_streams_blocked(f: &Frame, out: &mut Vec<u8>)
    requires
        f is StreamsBlocked,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::StreamsBlocked { bidi, max } => {
            out.push(if *bidi { 0x16 } else { 0x17 });
            varint::write(out, *max);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_new_connection_id(f: &Frame, out: &mut Vec<u8>)
    requires
        f is NewConnectionId,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::NewConnectionId { seq, retire, cid, token } => {
            out.push(0x18);
            varint::write(out, *seq);
            varint::write(out, *retire);
            out.push(cid.len() as u8);
            extend(out, cid);
            extend(out, token);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_retire_connection_id(f: &Frame, out: &mut Vec<u8>)
    requires
        f is RetireConnectionId,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::RetireConnectionId(s) => {
            out.push(0x19);
            varint::write(out, *s);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_path_challenge(f: &Frame, out: &mut Vec<u8>)
    requires
        f is PathChallenge,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::PathChallenge(d) => {
            out.push(0x1a);
            extend(out, d);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_path_response(f: &Frame, out: &mut Vec<u8>)
    requires
        f is PathResponse,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::PathResponse(d) => {
            out.push(0x1b);
            extend(out, d);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_connection_close(f: &Frame, out: &mut Vec<u8>)
    requires
        f is ConnectionClose,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::ConnectionClose { app, err, frame_type, reason } => {
            out.push(if *app { 0x1d } else { 0x1c });
            varint::write(out, *err);
            if !*app {
                varint::write(out, *frame_type);
            }
            varint::write(out, reason.len() as u64);
            extend(out, reason);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

#[inline(always)]
fn enc_handshake_done(f: &Frame, out: &mut Vec<u8>)
    requires
        f is HandshakeDone,
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    let ghost o = old(out)@;
    match f {
        Frame::HandshakeDone => {
            out.push(0x1e);
            proof { assert(out@ =~= o + frame_enc(f@)); }
        },
        _ => {},
    }
}

/// Appends the encoding of `f` (`spec::frame_enc`) to `out`.
pub fn encode(f: &Frame, out: &mut Vec<u8>)
    requires
        f.wf(),
        frame_wf(f@),
    ensures
        final(out)@ == old(out)@ + frame_enc(f@),
{
    match f {
        Frame::Padding(..) => enc_padding(f, out),
        Frame::Ping => enc_ping(f, out),
        Frame::Ack(..) => enc_ack(f, out),
        Frame::ResetStream { .. } => enc_reset_stream(f, out),
        Frame::StopSending { .. } => enc_stop_sending(f, out),
        Frame::Crypto { .. } => enc_crypto(f, out),
        Frame::NewToken(..) => enc_new_token(f, out),
        Frame::Stream { .. } => enc_stream(f, out),
        Frame::MaxData(..) => enc_max_data(f, out),
        Frame::MaxStreamData { .. } => enc_max_stream_data(f, out),
        Frame::MaxStreams { .. } => enc_max_streams(f, out),
        Frame::DataBlocked(..) => enc_data_blocked(f, out),
        Frame::StreamDataBlocked { .. } => enc_stream_data_blocked(f, out),
        Frame::StreamsBlocked { .. } => enc_streams_blocked(f, out),
        Frame::NewConnectionId { .. } => enc_new_connection_id(f, out),
        Frame::RetireConnectionId(..) => enc_retire_connection_id(f, out),
        Frame::PathChallenge(..) => enc_path_challenge(f, out),
        Frame::PathResponse(..) => enc_path_response(f, out),
        Frame::ConnectionClose { .. } => enc_connection_close(f, out),
        Frame::HandshakeDone => enc_handshake_done(f, out),
    }
}

} // verus!
