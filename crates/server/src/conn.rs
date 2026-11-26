//! The HTTP/1.1 connection core, verified: where each request in a byte
//! stream starts and ends (DESIGN.md milestone 2, "the connection engine").
//!
//! `msgs`-style specification: [`first`] is the request at the front of a
//! byte stream, by verilith-http's specification (`spec::parse_request`
//! for the head, `spec::request_body` for the framing, `chunked::run` for
//! a chunked body). [`prefix_ok`] says a list of requests is the stream's
//! first requests, back to back. The theorem of this module is the
//! invariant of [`Core`]: the requests it has handed out are, at every
//! moment, `prefix_ok` of every byte the connection has received. So the
//! server never acts on a request the specification does not see at that
//! place in the stream, never skips one, and never disagrees with it about
//! where a body ends: no request smuggling or desynchronization within a
//! connection, whatever the bytes and however they are split into reads.
//!
//! The core is sans I/O and calls no handler: `h1.rs` (plain Rust) asks it
//! for the next request, runs the handler, and tells it to move on.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verilith_http::chunked::{lemma_run_consumed, run, stops, theorem_split};
use verilith_http::chunked::{decode, CState, Decoded};
#[cfg(verus_keep_ghost)]
use verilith_http::framing::fx_agrees;
use verilith_http::framing::{request_body_exec, request_body_fx, FieldsExec};
#[cfg(verus_keep_ghost)]
use verilith_http::lemmas::theorem_request_ext;
#[cfg(verus_keep_ghost)]
use verilith_http::parse::{hdr_ok, hdrs_ok, headers_view};
use verilith_http::parse::{request_fx, request_resume, Header, Out, RequestLine, Span};
use verilith_http::spec::*;
use vstd::slice::slice_subrange;
use crate::persist::persists_exec;
#[cfg(verus_keep_ghost)]
use crate::persist::{lemma_conn_frame, persists};

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// A request, as the specification reads it from the front of a stream:
/// its head (spans relative to the request's first byte), the head's
/// length, the decoded body, and how many stream bytes the whole request
/// occupies.
pub ghost struct SMsg {
    pub req: SpecRequest,
    pub head: int,
    pub body: Seq<u8>,
    pub len: int,
}

/// The body that starts at `e` in `b` under framing `f`, if it is all
/// there: the body bytes (decoded, for chunked) and how many bytes of `b`
/// it occupies.
pub open spec fn body_at(b: Seq<u8>, e: int, f: Body) -> Option<(Seq<u8>, int)> {
    match f {
        Body::Empty => Some((Seq::empty(), 0)),
        Body::Length(n) => if e + n <= b.len() {
            Some((b.subrange(e, e + n), n as int))
        } else {
            None
        },
        Body::Chunked => match run(CState::SizeStart, b.subrange(e, b.len() as int), false) {
            Some((s, o, k)) => if s is Done {
                Some((o, k as int))
            } else {
                None
            },
            None => None,
        },
        Body::Close => None,
    }
}

/// The complete request at the front of `b`, if there is one. The framing
/// is decided from the head's bytes alone (`b[..e]`).
pub open spec fn first(b: Seq<u8>, max: nat) -> Option<SMsg> {
    match parse_request(b, max) {
        Parsed::Done(q, e) => match request_body(b.subrange(0, e), q) {
            Some(f) => match body_at(b, e, f) {
                Some((body, k)) => Some(SMsg { req: q, head: e, body, len: e + k }),
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}

/// `log` is the first `log.len()` requests of `b`, back to back.
pub open spec fn prefix_ok(b: Seq<u8>, log: Seq<SMsg>, max: nat) -> bool
    decreases log.len(),
{
    if log.len() == 0 {
        true
    } else {
        &&& first(b, max) == Some(log[0])
        &&& prefix_ok(b.subrange(log[0].len, b.len() as int), log.drop_first(), max)
    }
}

/// The stream bytes the requests in `log` occupy.
pub open spec fn total(log: Seq<SMsg>) -> int
    decreases log.len(),
{
    if log.len() == 0 {
        0
    } else {
        log[0].len + total(log.drop_first())
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

proof fn lemma_run_end_ge(b: Seq<u8>, i: int, k: Cls)
    ensures
        run_end(b, i, k) >= i,
    decreases b.len() - i,
{
    if !(i < 0 || i >= b.len() || !in_cls(k, b[i])) {
        lemma_run_end_ge(b, i + 1, k);
    }
}

proof fn lemma_trim_end_in(b: Seq<u8>, s: int, e: int)
    requires
        s <= e,
    ensures
        s <= trim_end(b, s, e) <= e,
    decreases e - s,
{
    if !(e <= s || !is_ows(b[e - 1])) {
        lemma_trim_end_in(b, s, e - 1);
    }
}

/// Both spans of `h` lie within `lo..hi`.
pub open spec fn span_in(h: SpecHeader, lo: int, hi: int) -> bool {
    &&& lo <= h.name.start <= h.name.end <= hi
    &&& lo <= h.value.start <= h.value.end <= hi
}

proof fn lemma_header_spans(b: Seq<u8>, i: int)
    requires
        0 <= i,
        parse_header(b, i) is Done,
    ensures
        parse_header(b, i) matches Parsed::Done(h, n) && span_in(h, i, n) && i < n,
{
    let ne = run_end(b, i, Cls::Token);
    lemma_run_end_ge(b, i, Cls::Token);
    let v0 = ne + 1;
    let vs = run_end(b, v0, Cls::Ows);
    lemma_run_end_ge(b, v0, Cls::Ows);
    let e = run_end(b, vs, Cls::Value);
    lemma_run_end_ge(b, vs, Cls::Value);
    lemma_trim_end_in(b, vs, e);
}

proof fn lemma_headers_spans(b: Seq<u8>, i: int, max: nat)
    requires
        0 <= i,
        parse_headers(b, i, max) is Done,
    ensures
        parse_headers(b, i, max) matches Parsed::Done(hs, m) && i < m && forall|j: int|
            0 <= j < hs.len() ==> span_in(#[trigger] hs[j], i, m),
    decreases b.len() - i,
{
    if i < 0 || i >= b.len() {
    } else if b[i] == CR {
    } else if max == 0 {
    } else {
        lemma_header_spans(b, i);
        let (h, n) = match parse_header(b, i) {
            Parsed::Done(h, n) => (h, n),
            _ => arbitrary(),
        };
        lemma_headers_spans(b, n, (max - 1) as nat);
        let (hs, m) = match parse_headers(b, n, (max - 1) as nat) {
            Parsed::Done(hs, m) => (hs, m),
            _ => arbitrary(),
        };
        let all = seq![h] + hs;
        assert forall|j: int| 0 <= j < all.len() implies span_in(#[trigger] all[j], i, m) by {
            if j > 0 {
                assert(all[j] == hs[j - 1]);
            }
        }
    }
}

/// A request head's field lines lie within the head.
pub proof fn lemma_request_spans(b: Seq<u8>, max: nat)
    requires
        parse_request(b, max) is Done,
    ensures
        parse_request(b, max) matches Parsed::Done(q, e) && forall|j: int|
            0 <= j < q.headers.len() ==> span_in(#[trigger] q.headers[j], 0, e),
{
    let s = match skip_empty_lines(b, 0) {
        Parsed::Done(_, s) => s,
        _ => arbitrary(),
    };
    verilith_http::unique::lemma_skip_bounds(b, 0);
    let t = run_then(b, s, Cls::Token, SP)->Done_1;
    lemma_run_end_ge(b, s, Cls::Token);
    let v = run_then(b, t, Cls::Target, SP)->Done_1;
    lemma_run_end_ge(b, t, Cls::Target);
    let h = parse_version(b, v)->Done_1;
    let h2 = lit(b, h, crlf())->Done_1;
    lemma_headers_spans(b, h2, max);
}

/// `fields_of` reads only the bytes its spans cover.
proof fn lemma_fields_take(b: Seq<u8>, hs: Seq<SpecHeader>, l: int)
    requires
        0 <= l <= b.len(),
        forall|j: int| 0 <= j < hs.len() ==> span_in(#[trigger] hs[j], 0, l),
    ensures
        fields_of(b, hs) == fields_of(b.subrange(0, l), hs),
    decreases hs.len(),
{
    if hs.len() > 0 {
        let p = hs.drop_last();
        assert forall|j: int| 0 <= j < p.len() implies span_in(#[trigger] p[j], 0, l) by {
            assert(p[j] == hs[j]);
        }
        lemma_fields_take(b, p, l);
        let h = hs.last();
        assert(span_in(hs[hs.len() - 1], 0, l));
        let t = b.subrange(0, l);
        assert(span_bytes(b, h.name) =~= span_bytes(t, h.name));
        assert(span_bytes(b, h.value) =~= span_bytes(t, h.value));
    }
}

/// The framing decided on the whole of `b` is the one decided on its head.
pub proof fn lemma_body_take(b: Seq<u8>, max: nat)
    requires
        parse_request(b, max) is Done,
    ensures
        parse_request(b, max) matches Parsed::Done(q, e) && 0 <= e <= b.len() && request_body(b, q)
            == request_body(b.subrange(0, e), q),
{
    theorem_request_ext(b, Seq::empty(), max);
    lemma_request_spans(b, max);
    let (q, e) = match parse_request(b, max) {
        Parsed::Done(q, e) => (q, e),
        _ => arbitrary(),
    };
    lemma_skip_nonneg(b, max);
    lemma_fields_take(b, q.headers, e);
}

proof fn lemma_skip_nonneg(b: Seq<u8>, max: nat)
    requires
        parse_request(b, max) is Done,
    ensures
        parse_request(b, max)->Done_1 >= 0,
{
    let s = skip_empty_lines(b, 0)->Done_1;
    verilith_http::unique::lemma_skip_bounds(b, 0);
    lemma_run_end_ge(b, s, Cls::Token);
    let t = run_then(b, s, Cls::Token, SP)->Done_1;
    lemma_run_end_ge(b, t, Cls::Target);
    let v = run_then(b, t, Cls::Target, SP)->Done_1;
    let h = parse_version(b, v)->Done_1;
    let h2 = lit(b, h, crlf())->Done_1;
    lemma_headers_spans(b, h2, max);
}

/// A complete request occupies at most the stream it was read from.
pub proof fn lemma_first_len(b: Seq<u8>, max: nat)
    requires
        first(b, max) is Some,
    ensures
        first(b, max) matches Some(m) && 0 < m.len <= b.len() && 0 <= m.head <= m.len,
{
    theorem_request_ext(b, Seq::empty(), max);
    lemma_skip_nonneg(b, max);
    lemma_request_spans(b, max);
    let (q, e) = match parse_request(b, max) {
        Parsed::Done(q, e) => (q, e),
        _ => arbitrary(),
    };
    lemma_head_nonempty(b, max);
    let f = request_body(b.subrange(0, e), q).unwrap();
    if f is Chunked {
        lemma_run_consumed(CState::SizeStart, b.subrange(e, b.len() as int), false);
    }
}

proof fn lemma_head_nonempty(b: Seq<u8>, max: nat)
    requires
        parse_request(b, max) is Done,
    ensures
        parse_request(b, max)->Done_1 > 0,
{
    let s = skip_empty_lines(b, 0)->Done_1;
    verilith_http::unique::lemma_skip_bounds(b, 0);
    lemma_run_end_ge(b, s, Cls::Token);
    let t = run_then(b, s, Cls::Token, SP)->Done_1;
    lemma_run_end_ge(b, t, Cls::Target);
    let v = run_then(b, t, Cls::Target, SP)->Done_1;
    let h = parse_version(b, v)->Done_1;
    let h2 = lit(b, h, crlf())->Done_1;
    lemma_headers_spans(b, h2, max);
}

/// More bytes do not change a complete request.
pub proof fn lemma_first_ext(b: Seq<u8>, c: Seq<u8>, max: nat)
    requires
        first(b, max) is Some,
    ensures
        first(b + c, max) == first(b, max),
{
    theorem_request_ext(b, c, max);
    lemma_first_len(b, max);
    let (q, e) = match parse_request(b, max) {
        Parsed::Done(q, e) => (q, e),
        _ => arbitrary(),
    };
    let bc = b + c;
    assert(bc.subrange(0, e) =~= b.subrange(0, e));
    let f = request_body(b.subrange(0, e), q).unwrap();
    match f {
        Body::Length(n) => {
            assert(bc.subrange(e, e + n) =~= b.subrange(e, e + n));
        },
        Body::Chunked => {
            let a = b.subrange(e, b.len() as int);
            assert(bc.subrange(e, bc.len() as int) =~= a + c);
            theorem_split(CState::SizeStart, a, c, false);
        },
        _ => {},
    }
}

/// More bytes do not change the requests already read.
pub proof fn lemma_prefix_ext(b: Seq<u8>, c: Seq<u8>, log: Seq<SMsg>, max: nat)
    requires
        prefix_ok(b, log, max),
    ensures
        prefix_ok(b + c, log, max),
    decreases log.len(),
{
    if log.len() > 0 {
        lemma_first_ext(b, c, max);
        lemma_first_len(b, max);
        let n = log[0].len;
        let r = b.subrange(n, b.len() as int);
        assert((b + c).subrange(n, (b + c).len() as int) =~= r + c);
        lemma_prefix_ext(r, c, log.drop_first(), max);
    }
}

/// The requests in `log` fit in `b`, back to back.
pub proof fn lemma_prefix_total(b: Seq<u8>, log: Seq<SMsg>, max: nat)
    requires
        prefix_ok(b, log, max),
    ensures
        0 <= total(log) <= b.len(),
    decreases log.len(),
{
    if log.len() > 0 {
        lemma_first_len(b, max);
        lemma_prefix_total(b.subrange(log[0].len, b.len() as int), log.drop_first(), max);
    }
}

/// The next request, at the end of the ones already read, extends them.
pub proof fn lemma_prefix_push(b: Seq<u8>, log: Seq<SMsg>, m: SMsg, max: nat)
    requires
        prefix_ok(b, log, max),
        first(b.subrange(total(log), b.len() as int), max) == Some(m),
    ensures
        prefix_ok(b, log.push(m), max),
    decreases log.len(),
{
    lemma_prefix_total(b, log, max);
    if log.len() == 0 {
        assert(total(log) == 0);
        assert(b.subrange(0, b.len() as int) =~= b);
        assert(log.push(m)[0] == m);
        assert(log.push(m).len() == 1);
        assert(log.push(m).drop_first() =~= Seq::<SMsg>::empty());
        assert(first(b, max) == Some(log.push(m)[0]));
        assert(prefix_ok(b.subrange(m.len, b.len() as int), log.push(m).drop_first(), max));
    } else {
        let r = b.subrange(log[0].len, b.len() as int);
        lemma_first_len(b, max);
        lemma_prefix_total(r, log.drop_first(), max);
        assert(total(log) == log[0].len + total(log.drop_first()));
        assert(r.subrange(total(log.drop_first()), r.len() as int) =~= b.subrange(
            total(log),
            b.len() as int,
        ));
        lemma_prefix_push(r, log.drop_first(), m, max);
        assert(log.push(m)[0] == log[0]);
        assert(log.push(m).drop_first() =~= log.drop_first().push(m));
        assert(first(b, max) == Some(log.push(m)[0]));
        assert(prefix_ok(r, log.push(m).drop_first(), max));
    }
}

// ---------------------------------------------------------------------------
// The core
// ---------------------------------------------------------------------------

/// A request head, as spans into the request's bytes (`rbuf[start..]`).
#[derive(Clone, Copy, Debug)]
pub struct HeadInfo {
    pub method: Span,
    pub target: Span,
    pub minor: u8,
    pub head_len: usize,
}

#[derive(Clone, Copy, Debug)]
pub enum Phase {
    /// Waiting for a request head.
    Head,
    /// Head read; waiting for `need` body bytes.
    Length { hd: HeadInfo, need: usize },
    /// Head read; decoding a chunked body. `out` decoded bytes follow the
    /// head in place.
    Chunked { hd: HeadInfo, out: usize, dec: CState },
    /// A complete request: head, then `body` body bytes, at `rbuf[start..]`.
    Ready { hd: HeadInfo, body: usize },
    /// No more requests on this connection.
    Closed,
}

/// What [`Core::step`] found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ev {
    /// More bytes are needed.
    Need,
    /// A request is ready (`Phase::Ready`).
    Ready,
    /// The bytes are not a valid request (or exceed a limit): answer with
    /// this status and close. Nothing after it is read.
    Bad(u16),
    /// The connection takes no more requests.
    Closed,
}

pub struct Core {
    pub rbuf: Vec<u8>,
    /// The current request starts at `rbuf[start]`; bytes received end at
    /// `rbuf[end]`.
    pub start: usize,
    pub end: usize,
    /// `end - start` at the last Partial parse (for linear-time resumes).
    pub last_len: usize,
    /// The current request's field lines, as spans into `rbuf[start..]`.
    pub headers: Vec<Header>,
    pub phase: Phase,
    pub max_headers: usize,
    pub max_body: usize,
    /// Every byte received on the connection.
    pub stream: Ghost<Seq<u8>>,
    /// The requests handed out so far.
    pub log: Ghost<Seq<SMsg>>,
    /// The current request's head, once read.
    pub q: Ghost<SpecRequest>,
    /// Stream bytes of the current chunked body consumed so far.
    pub raw: Ghost<int>,
}

/// `a[i..i + n] == b[j..j + n]`.
pub open spec fn same(a: Seq<u8>, i: int, b: Seq<u8>, j: int, n: int) -> bool {
    &&& 0 <= i && i + n <= a.len()
    &&& 0 <= j && j + n <= b.len()
    &&& 0 <= n
    &&& a.subrange(i, i + n) == b.subrange(j, j + n)
}

/// The current head is `q`, ending at `hd.head_len`, its framing is `f`,
/// and `w` (the current request's bytes in `rbuf`) still starts with it.
pub open spec fn head_is(w: Seq<u8>, b: Seq<u8>, hd: HeadInfo, f: Body, q: SpecRequest, hs: Seq<Header>, max: nat) -> bool {
    let e = hd.head_len as int;
    &&& parse_request(b, max) == Parsed::Done(q, e)
    &&& request_body(b.subrange(0, e), q) == Some(f)
    &&& hd.method@ == q.method
    &&& hd.target@ == q.target
    &&& hd.minor == q.minor
    &&& headers_view(hs) == q.headers
    &&& hdrs_ok(hs, e)
    &&& 0 < e <= b.len()
    &&& e <= w.len()
    &&& w.subrange(0, e) == b.subrange(0, e)
}

/// What each phase knows: `w` is `rbuf[start..end]`, `b` the stream from
/// the current request on.
pub open spec fn ph_ok(w: Seq<u8>, b: Seq<u8>, phase: Phase, q: SpecRequest, raw: int, hs: Seq<Header>, last_len: usize, max: nat) -> bool {
    match phase {
        Phase::Head => {
            &&& w == b
            &&& last_len == 0 || (last_len <= w.len() && !(parse_request(b.subrange(0, last_len as int), max) is Done))
        },
        Phase::Length { hd, need } => {
            &&& head_is(w, b, hd, Body::Length(need as u64), q, hs, max)
            &&& w == b
        },
        Phase::Chunked { hd, out, dec } => {
            let e = hd.head_len as int;
            &&& head_is(w, b, hd, Body::Chunked, q, hs, max)
            &&& 0 <= raw && e + raw <= b.len()
            &&& e + out <= w.len()
            &&& run(CState::SizeStart, b.subrange(e, e + raw), false) == Some((dec, w.subrange(e, e + out), raw as nat))
            &&& !stops(dec, false)
            &&& w.subrange(e + out, w.len() as int) == b.subrange(e + raw, b.len() as int)
        },
        Phase::Ready { hd, body } => {
            let e = hd.head_len as int;
            &&& 0 < e && e + body <= w.len()
            &&& first(b, max) == Some(SMsg { req: q, head: e, body: w.subrange(e, e + body), len: e + raw })
            &&& hd.method@ == q.method
            &&& hd.target@ == q.target
            &&& hd.minor == q.minor
            &&& headers_view(hs) == q.headers
            &&& hdrs_ok(hs, e)
            &&& w.subrange(0, e) == b.subrange(0, e)
            &&& 0 <= raw && e + raw <= b.len()
            &&& w.subrange(e + body, w.len() as int) == b.subrange(e + raw, b.len() as int)
        },
        Phase::Closed => true,
    }
}

/// Bytes added to both the window and the stream keep every phase's facts.
#[verifier::rlimit(40)]
proof fn lemma_ph_ext(w: Seq<u8>, b: Seq<u8>, c: Seq<u8>, phase: Phase, q: SpecRequest, raw: int, hs: Seq<Header>, last_len: usize, max: nat)
    requires
        ph_ok(w, b, phase, q, raw, hs, last_len, max),
    ensures
        ph_ok(w + c, b + c, phase, q, raw, hs, last_len, max),
{
    let w2 = w + c;
    let b2 = b + c;
    match phase {
        Phase::Head => {
            assert(b2.subrange(0, last_len as int) =~= b.subrange(0, last_len as int));
        },
        Phase::Length { hd, need } => {
            let e = hd.head_len as int;
            lemma_head_ext(b, c, max, e);
            assert(w2.subrange(0, e) =~= w.subrange(0, e));
        },
        Phase::Chunked { hd, out, dec } => {
            let e = hd.head_len as int;
            lemma_head_ext(b, c, max, e);
            assert(w2.subrange(0, e) =~= w.subrange(0, e));
            assert(b2.subrange(e, e + raw) =~= b.subrange(e, e + raw));
            assert(w2.subrange(e, e + out) =~= w.subrange(e, e + out));
            assert(w2.subrange(e + out, w2.len() as int) =~= w.subrange(e + out, w.len() as int) + c);
            assert(b2.subrange(e + raw, b2.len() as int) =~= b.subrange(e + raw, b.len() as int) + c);
        },
        Phase::Ready { hd, body } => {
            let e = hd.head_len as int;
            lemma_first_ext(b, c, max);
            assert(w2.subrange(0, e) =~= w.subrange(0, e));
            assert(b2.subrange(0, e) =~= b.subrange(0, e));
            assert(w2.subrange(e, e + body) =~= w.subrange(e, e + body));
            assert(w2.subrange(e + body, w2.len() as int) =~= w.subrange(e + body, w.len() as int) + c);
            assert(b2.subrange(e + raw, b2.len() as int) =~= b.subrange(e + raw, b.len() as int) + c);
        },
        Phase::Closed => {},
    }
}

impl Core {
    /// Where the current request starts in the stream.
    pub open spec fn pos(&self) -> int {
        total(self.log@)
    }

    /// The stream from the current request on.
    pub open spec fn rest(&self) -> Seq<u8> {
        self.stream@.subrange(self.pos(), self.stream@.len() as int)
    }

    pub open spec fn max(&self) -> nat {
        self.max_headers as nat
    }

    /// The bytes of the current request received so far.
    pub open spec fn win(&self) -> Seq<u8> {
        self.rbuf@.subrange(self.start as int, self.end as int)
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.start <= self.end <= self.rbuf@.len()
        &&& prefix_ok(self.stream@, self.log@, self.max())
        &&& 0 <= self.pos() <= self.stream@.len()
        &&& ph_ok(self.win(), self.rest(), self.phase, self.q@, self.raw@, self.headers@, self.last_len, self.max())
    }

    pub fn new(cap: usize, max_headers: usize, max_body: usize) -> (r: Core)
        ensures
            r.inv(),
            r.log@.len() == 0,
            r.stream@.len() == 0,
            r.rbuf@.len() == cap,
            r.phase is Head,
    {
        let c = Core {
            rbuf: vec_zeros(cap),
            start: 0,
            end: 0,
            last_len: 0,
            headers: Vec::new(),
            phase: Phase::Head,
            max_headers,
            max_body,
            stream: Ghost(Seq::empty()),
            log: Ghost(Seq::empty()),
            q: Ghost(arbitrary()),
            raw: Ghost(0),
        };
        proof {
            assert(c.rest() =~= Seq::<u8>::empty());
            assert(c.rbuf@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        c
    }

    /// `n` bytes were read into `rbuf[end..end + n]`: they join the stream.
    #[verifier::rlimit(40)]
    pub fn filled(&mut self, n: usize)
        requires
            old(self).inv(),
            old(self).end + n <= old(self).rbuf@.len(),
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@ + old(self).rbuf@.subrange(
                old(self).end as int,
                old(self).end + n,
            ),
            final(self).rbuf@ == old(self).rbuf@,
            final(self).start == old(self).start,
            final(self).end == old(self).end + n,
            final(self).phase == old(self).phase,
    {
        let ghost c = self.rbuf@.subrange(self.end as int, self.end + n);
        let ghost b0 = self.rest();
        let ghost w0 = self.win();
        let ghost st0 = self.stream@;
        let ghost p = self.pos();
        proof {
            lemma_prefix_ext(st0, c, self.log@, self.max());
            assert((st0 + c).subrange(p, (st0 + c).len() as int) =~= b0 + c);
            lemma_ph_ext(w0, b0, c, self.phase, self.q@, self.raw@, self.headers@, self.last_len, self.max());
        }
        self.stream = Ghost(st0 + c);
        let _len = self.rbuf.len();
        self.end = self.end + n;
        proof {
            assert(self.rest() =~= b0 + c);
            assert(self.win() =~= w0 + c);
        }
    }

    /// Moves the current request's bytes to the front of `rbuf`.
    pub fn compact(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).start == 0,
            final(self).end == old(self).end - old(self).start,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            final(self).phase == old(self).phase,
            final(self).win() == old(self).win(),
    {
        if self.start == 0 {
            return;
        }
        let ghost w0 = self.win();
        shift_down(&mut self.rbuf, self.start, self.end);
        self.end = self.end - self.start;
        self.start = 0;
        proof {
            assert(self.win() =~= w0);
        }
    }

    /// Makes `rbuf` at least `n` bytes long.
    pub fn grow(&mut self, n: usize)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).start == old(self).start,
            final(self).end == old(self).end,
            final(self).rbuf@.len() >= n,
            final(self).rbuf@.len() >= old(self).rbuf@.len(),
            final(self).phase == old(self).phase,
            final(self).win() == old(self).win(),
    {
        let ghost w0 = self.win();
        if self.rbuf.len() < n {
            grow_zeros(&mut self.rbuf, n);
        }
        proof {
            assert(self.win() =~= w0);
        }
    }

    /// No more requests on this connection.
    pub fn close(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).phase is Closed,
    {
        self.phase = Phase::Closed;
    }

    /// A new connection, keeping the buffers (at most `cap` bytes of read
    /// buffer).
    pub fn reset(&mut self, cap: usize)
        ensures
            final(self).inv(),
            final(self).log@.len() == 0,
            final(self).stream@.len() == 0,
            final(self).phase is Head,
            final(self).max_headers == old(self).max_headers,
            final(self).max_body == old(self).max_body,
    {
        if self.rbuf.len() > cap {
            // A new buffer, which frees the larger one: its bytes are dead.
            self.rbuf = vec_zeros(cap);
        }
        self.start = 0;
        self.end = 0;
        self.last_len = 0;
        self.headers.clear();
        self.phase = Phase::Head;
        self.stream = Ghost(Seq::empty());
        self.log = Ghost(Seq::empty());
        self.raw = Ghost(0);
        proof {
            assert(self.rest() =~= Seq::<u8>::empty());
            assert(self.win() =~= Seq::<u8>::empty());
        }
    }

    /// Parses as far as the bytes allow. On `Ready` the request is
    /// `phase`'s, and is the specification's next request in the stream.
    pub fn step(&mut self) -> (r: Ev)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            r == Ev::Ready <==> final(self).phase is Ready,
            r is Bad || r == Ev::Closed ==> final(self).phase is Closed,
            r == Ev::Need ==> !(final(self).phase is Closed) && !(final(self).phase is Ready),
    {
        if matches!(self.phase, Phase::Head) {
            match self.step_head() {
                Go::Stop(ev) => return ev,
                Go::Again => {},
            }
        }
        if matches!(self.phase, Phase::Length { .. }) {
            match self.step_length() {
                Go::Stop(ev) => return ev,
                Go::Again => {},
            }
        }
        if matches!(self.phase, Phase::Chunked { .. }) {
            match self.step_chunked() {
                Go::Stop(ev) => return ev,
                Go::Again => {},
            }
        }
        match self.phase {
            Phase::Ready { .. } => Ev::Ready,
            Phase::Closed => Ev::Closed,
            _ => Ev::Need,
        }
    }

    #[verifier::rlimit(60)]
    fn step_head(&mut self) -> (r: Go)
        requires
            old(self).inv(),
            old(self).phase is Head,
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            r matches Go::Stop(ev) ==> (ev == Ev::Need && final(self).phase is Head) || (ev is Bad
                && final(self).phase is Closed),
    {
        if self.start == self.end {
            proof {
                assert(self.win().len() == 0);
                assert(self.rest().len() == 0);
            }
            self.start = 0;
            self.end = 0;
            self.last_len = 0;
            proof {
                assert(self.win() =~= Seq::<u8>::empty());
                assert(self.win() =~= self.rest());
            }
            return Go::Stop(Ev::Need);
        }
        let ghost b = self.rest();
        let n = self.end - self.start;
        let last = self.last_len;
        let mut fx: Option<FieldsExec> = None;
        let buf = slice_subrange(self.rbuf.as_slice(), self.start, self.end);
        assert(buf@ == b);
        let (r, _) = if last == 0 {
            request_fx(buf, self.max_headers, &mut self.headers, true, &mut fx)
        } else {
            request_resume(buf, last, self.max_headers, &mut self.headers)
        };
        match r {
            Out::Done(line, e) => {
                let body = if last == 0 {
                    request_body_fx(buf, line, self.headers.as_slice(), fx)
                } else {
                    request_body_exec(buf, line, self.headers.as_slice())
                };
                let ghost q = SpecRequest {
                    method: line.method@,
                    target: line.target@,
                    minor: line.minor,
                    headers: headers_view(self.headers@),
                };
                proof {
                    lemma_body_take(b, self.max());
                    lemma_request_spans(b, self.max());
                    lemma_head_nonempty(b, self.max());
                    assert(parse_request(b, self.max()) == Parsed::Done(q, e as int));
                    assert forall|j: int| 0 <= j < self.headers@.len() implies hdr_ok(
                        #[trigger] self.headers@[j],
                        e as int,
                    ) by {
                        assert(headers_view(self.headers@)[j] == self.headers@[j]@);
                        assert(span_in(q.headers[j], 0, e as int));
                    }
                }
                self.q = Ghost(q);
                let hd = HeadInfo { method: line.method, target: line.target, minor: line.minor, head_len: e };
                match body {
                    None => {
                        self.phase = Phase::Closed;
                        Go::Stop(Ev::Bad(400))
                    },
                    Some(Body::Empty) => {
                        self.phase = Phase::Ready { hd, body: 0 };
                        self.raw = Ghost(0);
                        proof {
                            let w = self.win();
                            assert(w.subrange(e as int, e as int) =~= Seq::<u8>::empty());
                            assert(b.subrange(0, e as int) =~= w.subrange(0, e as int));
                        }
                        Go::Again
                    },
                    Some(Body::Length(len)) => {
                        if len > self.max_body as u64 {
                            self.phase = Phase::Closed;
                            return Go::Stop(Ev::Bad(413));
                        }
                        self.phase = Phase::Length { hd, need: len as usize };
                        proof {
                            assert(b.subrange(0, e as int) =~= self.win().subrange(0, e as int));
                        }
                        Go::Again
                    },
                    Some(Body::Chunked) => {
                        self.phase = Phase::Chunked { hd, out: 0, dec: CState::SizeStart };
                        self.raw = Ghost(0);
                        proof {
                            let w = self.win();
                            assert(b.subrange(0, e as int) =~= w.subrange(0, e as int));
                            assert(b.subrange(e as int, e as int) =~= Seq::<u8>::empty());
                            assert(w.subrange(e as int, e as int) =~= Seq::<u8>::empty());
                        }
                        Go::Again
                    },
                    Some(Body::Close) => {
                        self.phase = Phase::Closed;
                        Go::Stop(Ev::Bad(400))
                    },
                }
            },
            Out::Partial => {
                self.last_len = n;
                proof {
                    assert(b.subrange(0, n as int) =~= b);
                }
                if self.start == 0 && self.end == self.rbuf.len() {
                    self.phase = Phase::Closed;
                    return Go::Stop(Ev::Bad(431));
                }
                Go::Stop(Ev::Need)
            },
            Out::Invalid => {
                self.phase = Phase::Closed;
                Go::Stop(Ev::Bad(400))
            },
        }
    }

    fn step_length(&mut self) -> (r: Go)
        requires
            old(self).inv(),
            old(self).phase is Length,
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            r matches Go::Stop(ev) ==> ev == Ev::Need && final(self).phase is Length,
    {
        let (hd, need) = match self.phase {
            Phase::Length { hd, need } => (hd, need),
            _ => { return Go::Stop(Ev::Need); },
        };
        let have = self.end - self.start - hd.head_len;
        if have < need {
            return Go::Stop(Ev::Need);
        }
        self.phase = Phase::Ready { hd, body: need };
        self.raw = Ghost(need as int);
        proof {
            let w = self.win();
            let e = hd.head_len as int;
            assert(w.subrange(e, e + need) == self.rest().subrange(e, e + need));
        }
        Go::Again
    }

    #[verifier::rlimit(60)]
    fn step_chunked(&mut self) -> (r: Go)
        requires
            old(self).inv(),
            old(self).phase is Chunked,
        ensures
            final(self).inv(),
            final(self).log@ == old(self).log@,
            final(self).stream@ == old(self).stream@,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            r matches Go::Stop(ev) ==> (ev == Ev::Need && final(self).phase is Chunked) || (ev is Bad
                && final(self).phase is Closed),
    {
        let (hd, out, dec) = match self.phase {
            Phase::Chunked { hd, out, dec } => (hd, out, dec),
            _ => { return Go::Stop(Ev::Need); },
        };
        let from = self.start + hd.head_len + out;
        if from == self.end {
            return Go::Stop(Ev::Need);
        }
        let ghost b = self.rest();
        let ghost w0 = self.win();
        let ghost v0 = self.rbuf@;
        let ghost e = hd.head_len as int;
        let ghost raw = self.raw@;
        let ghost s0 = self.start as int;
        let ghost x = v0.subrange(from as int, self.end as int);
        let ghost o0 = w0.subrange(e, e + out);
        let len = self.end - from;
        let mut st = dec;
        proof {
            lemma_win_split(v0, s0, self.end as int, e, out as int);
        }
        let (d, _) = decode_in(&mut st, &mut self.rbuf, from, self.end);
        let ghost v = self.rbuf@;
        proof {
            lemma_prefix_keep(v0, v, s0, from as int);
            lemma_run_consumed(dec, x, false);
        }
        match d {
            Decoded::Invalid => {
                self.phase = Phase::Closed;
                Go::Stop(Ev::Bad(400))
            },
            Decoded::More { out: o } => {
                self.end = from + o;
                self.raw = Ghost(raw + len);
                if out > self.max_body || o > self.max_body - out {
                    self.phase = Phase::Closed;
                    return Go::Stop(Ev::Bad(413));
                }
                self.phase = Phase::Chunked { hd, out: out + o, dec: st };
                proof {
                    lemma_chunk_more(b, e, raw, dec, o0, x);
                    lemma_win_join(v0, v, s0, e, out as int, o as int, 0);
                    let w = self.win();
                    assert(w.len() == e + out + o);
                    assert(w.subrange(0, e) == b.subrange(0, e));
                    assert(w.subrange(e, e + out + o) == o0 + v.subrange(from as int, from + o));
                    assert(head_is(w, b, hd, Body::Chunked, self.q@, self.headers@, self.max()));
                    assert(w.subrange(e + out + o, w.len() as int) =~= b.subrange(e + raw + len, b.len() as int));
                }
                Go::Stop(Ev::Need)
            },
            Decoded::Done { out: o, consumed: k } => {
                self.end = from + o + (len - k);
                self.raw = Ghost(raw + k);
                self.phase = Phase::Ready { hd, body: out + o };
                proof {
                    lemma_chunk_done(b, e, raw, dec, o0, x);
                    lemma_win_join(v0, v, s0, e, out as int, o as int, (len - k) as int);
                    assert(v.subrange(from + o, from + o + len - k) == x.subrange(k as int, len as int));
                    lemma_first_parts(b, self.max(), self.q@, e, w0, o0 + v.subrange(from as int, from + o), raw + k);
                    let w = self.win();
                    assert(w.subrange(0, e) == b.subrange(0, e));
                    assert(w.subrange(e, e + out + o) == o0 + v.subrange(from as int, from + o));
                    assert(w.subrange(e + out + o, w.len() as int) == b.subrange(e + raw + k, b.len() as int));
                }
                Go::Again
            },
        }
    }

    /// Whether the ready request lets the connection carry another
    /// (RFC 9112 §9.3): exactly `persist::persists` of it.
    pub fn ready_persists(&self) -> (r: bool)
        requires
            self.inv(),
            self.phase is Ready,
        ensures
            r == persists(self.rest(), first(self.rest(), self.max()).unwrap().req),
    {
        let hd = match self.phase {
            Phase::Ready { hd, body: _ } => hd,
            _ => { return false; },
        };
        let w = slice_subrange(self.rbuf.as_slice(), self.start, self.end);
        let r = persists_exec(w, self.headers.as_slice(), hd.minor);
        proof {
            let e = hd.head_len as int;
            let hs = headers_view(self.headers@);
            assert(w@ == self.win());
            assert forall|j: int| 0 <= j < hs.len() implies {
                &&& 0 <= #[trigger] hs[j].name.start <= hs[j].name.end <= e
                &&& 0 <= hs[j].value.start <= hs[j].value.end <= e
            } by {
                assert(hdr_ok(self.headers@[j], e));
            }
            assert(hdrs_ok(self.headers@, w@.len() as int)) by {
                assert forall|j: int| 0 <= j < self.headers@.len() implies hdr_ok(#[trigger] self.headers@[j], w@.len() as int) by {
                    assert(hdr_ok(self.headers@[j], e));
                }
            }
            lemma_conn_frame(self.win(), self.rest(), hs, e);
        }
        r
    }

    /// The handler has answered the ready request: move past it, to the
    /// next request if `keep` and the request persists (RFC 9112 §9.3),
    /// else to `Closed`. The check is here, not in the caller: whatever
    /// `h1.rs` passes, a request that does not persist ends the connection.
    pub fn done(&mut self, keep: bool)
        requires
            old(self).inv(),
            old(self).phase is Ready,
        ensures
            final(self).inv(),
            final(self).stream@ == old(self).stream@,
            final(self).rbuf@.len() == old(self).rbuf@.len(),
            final(self).log@ == old(self).log@.push(first(old(self).rest(), old(self).max()).unwrap()),
            final(self).phase is Head <==> (keep && persists(old(self).rest(), first(old(self).rest(), old(self).max()).unwrap().req)),
            !(final(self).phase is Head) ==> final(self).phase is Closed,
    {
        let keep = keep && self.ready_persists();
        let (hd, body) = match self.phase {
            Phase::Ready { hd, body } => (hd, body),
            _ => { return; },
        };
        let ghost b = self.rest();
        let ghost m = first(b, self.max()).unwrap();
        let ghost w0 = self.win();
        proof {
            lemma_first_len(b, self.max());
            lemma_prefix_total(self.stream@, self.log@, self.max());
            lemma_prefix_push(self.stream@, self.log@, m, self.max());
            lemma_total_push(self.log@, m);
        }
        self.start = self.start + hd.head_len + body;
        self.last_len = 0;
        self.log = Ghost(self.log@.push(m));
        self.phase = if keep { Phase::Head } else { Phase::Closed };
        proof {
            let e = hd.head_len as int;
            assert(self.pos() == total(old(self).log@) + m.len);
            assert(self.rest() =~= b.subrange(m.len, b.len() as int));
            assert(self.win() =~= w0.subrange(e + body, w0.len() as int));
        }
    }
}

/// The chunked decoder has consumed all of `x` without finishing.
proof fn lemma_chunk_more(b: Seq<u8>, e: int, raw: int, dec: CState, o0: Seq<u8>, x: Seq<u8>)
    requires
        0 <= e && 0 <= raw && e + raw <= b.len(),
        run(CState::SizeStart, b.subrange(e, e + raw), false) == Some((dec, o0, raw as nat)),
        !stops(dec, false),
        x == b.subrange(e + raw, b.len() as int),
        run(dec, x, false) matches Some((s, o, k)) && !(k < x.len() || stops(s, false)),
    ensures
        run(dec, x, false) matches Some((s, o, k)) && k == x.len() && e + raw + x.len() == b.len()
            && run(CState::SizeStart, b.subrange(e, e + raw + x.len()), false) == Some((s, o0 + o, (raw + x.len()) as nat))
            && !stops(s, false),
{
    let a = b.subrange(e, e + raw);
    lemma_run_consumed(dec, x, false);
    assert(b.subrange(e, e + raw + x.len()) =~= a + x);
    theorem_split(CState::SizeStart, a, x, false);
}

/// The chunked decoder finished within `x`.
proof fn lemma_chunk_done(b: Seq<u8>, e: int, raw: int, dec: CState, o0: Seq<u8>, x: Seq<u8>)
    requires
        0 <= e && 0 <= raw && e + raw <= b.len(),
        run(CState::SizeStart, b.subrange(e, e + raw), false) == Some((dec, o0, raw as nat)),
        !stops(dec, false),
        x == b.subrange(e + raw, b.len() as int),
        run(dec, x, false) matches Some((s, o, k)) && (k < x.len() || stops(s, false)),
    ensures
        run(dec, x, false) matches Some((s, o, k)) && k <= x.len() && body_at(b, e, Body::Chunked) == Some(
            (o0 + o, raw + k),
        ) && b.subrange(e + raw + k, b.len() as int) == x.subrange(k as int, x.len() as int),
{
    let a = b.subrange(e, e + raw);
    lemma_run_consumed(dec, x, false);
    assert(b.subrange(e, b.len() as int) =~= a + x);
    theorem_split(CState::SizeStart, a, x, false);
    let k = run(dec, x, false).unwrap().2;
    assert(b.subrange(e + raw + k, b.len() as int) =~= x.subrange(k as int, x.len() as int));
}

/// A request whose head parsed with chunked framing, and whose body is all
/// there, is the stream's first.
proof fn lemma_first_parts(b: Seq<u8>, max: nat, q: SpecRequest, e: int, w: Seq<u8>, body: Seq<u8>, k: int)
    requires
        parse_request(b, max) == Parsed::Done(q, e),
        request_body(b.subrange(0, e), q) == Some(Body::Chunked),
        body_at(b, e, Body::Chunked) == Some((body, k)),
    ensures
        first(b, max) == Some(SMsg { req: q, head: e, body, len: e + k }),
{
}

/// The window `v[s..end]` in three parts: head, decoded body, the rest.
proof fn lemma_win_split(v: Seq<u8>, s: int, end: int, e: int, out: int)
    requires
        0 <= s && 0 <= e && 0 <= out && s + e + out <= end <= v.len(),
    ensures
        v.subrange(s, end).subrange(0, e) == v.subrange(s, s + e),
        v.subrange(s, end).subrange(e, e + out) == v.subrange(s + e, s + e + out),
        v.subrange(s, end).subrange(e + out, end - s) == v.subrange(s + e + out, end),
{
    assert(v.subrange(s, end).subrange(0, e) =~= v.subrange(s, s + e));
    assert(v.subrange(s, end).subrange(e, e + out) =~= v.subrange(s + e, s + e + out));
    assert(v.subrange(s, end).subrange(e + out, end - s) =~= v.subrange(s + e + out, end));
}

/// What `v[..f]` keeps from `v0[..f]`, from `s` on.
proof fn lemma_prefix_keep(v0: Seq<u8>, v: Seq<u8>, s: int, f: int)
    requires
        0 <= s <= f <= v0.len(),
        f <= v.len(),
        v.subrange(0, f) == v0.subrange(0, f),
    ensures
        v.subrange(s, f) == v0.subrange(s, f),
{
    assert(v.subrange(s, f) =~= v.subrange(0, f).subrange(s, f));
    assert(v0.subrange(s, f) =~= v0.subrange(0, f).subrange(s, f));
}

/// The new window after decoding: head and old output kept, `o` new output
/// bytes, then `r` unconsumed bytes.
proof fn lemma_win_join(v0: Seq<u8>, v: Seq<u8>, s: int, e: int, out: int, o: int, r: int)
    requires
        0 <= s && 0 <= e && 0 <= out && 0 <= o && 0 <= r,
        s + e + out + o + r <= v.len(),
        s + e + out <= v0.len(),
        v.subrange(s, s + e + out) == v0.subrange(s, s + e + out),
    ensures
        ({
            let w = v.subrange(s, s + e + out + o + r);
            let f = s + e + out;
            &&& w.subrange(0, e) == v0.subrange(s, s + e)
            &&& w.subrange(e, e + out + o) == v0.subrange(s + e, f) + v.subrange(f, f + o)
            &&& w.subrange(e + out + o, w.len() as int) == v.subrange(f + o, f + o + r)
        }),
{
    let w = v.subrange(s, s + e + out + o + r);
    let f = s + e + out;
    assert(w.subrange(0, e) =~= v.subrange(s, f).subrange(0, e));
    assert(v0.subrange(s, s + e) =~= v0.subrange(s, f).subrange(0, e));
    assert(w.subrange(e, e + out + o) =~= v.subrange(s, f).subrange(e, e + out) + v.subrange(f, f + o));
    assert(v0.subrange(s + e, f) =~= v0.subrange(s, f).subrange(e, e + out));
    assert(w.subrange(e + out + o, w.len() as int) =~= v.subrange(f + o, f + o + r));
}

enum Go {
    Stop(Ev),
    Again,
}

proof fn lemma_total_push(log: Seq<SMsg>, m: SMsg)
    ensures
        total(log.push(m)) == total(log) + m.len,
    decreases log.len(),
{
    let p = log.push(m);
    assert(p[0] == if log.len() == 0 { m } else { log[0] });
    if log.len() == 0 {
        assert(p.drop_first() =~= Seq::<SMsg>::empty());
        assert(total(p.drop_first()) == 0);
    } else {
        assert(p.drop_first() =~= log.drop_first().push(m));
        lemma_total_push(log.drop_first(), m);
    }
}

/// `decode` on `v[from..end]`. Trusted: only the slicing (`&mut
/// v[from..end]` is a view of those bytes, and the rest of `v` is not
/// touched); the decoding is verilith-http's verified `chunked::decode`.
#[verifier::external_body]
fn decode_in(st: &mut CState, v: &mut Vec<u8>, from: usize, end: usize) -> (r: (Decoded, Ghost<nat>))
    requires
        from <= end <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@.subrange(0, from as int) == old(v)@.subrange(0, from as int),
        match run(*old(st), old(v)@.subrange(from as int, end as int), false) {
            None => r.0 is Invalid,
            Some((s, o, k)) => {
                let len = end - from;
                &&& *final(st) == s
                &&& (k < len || stops(s, false)) ==> (r.0 matches Decoded::Done { out, consumed }
                    && out == o.len() && consumed == k && final(v)@.subrange(from as int, from + out) == o
                    && final(v)@.subrange(from + out, from + out + len - k) == old(v)@.subrange(
                    from + k,
                    end as int,
                ))
                &&& !(k < len || stops(s, false)) ==> (r.0 matches Decoded::More { out } && out == o.len()
                    && final(v)@.subrange(from as int, from + out) == o)
            },
        },
{
    let r = decode(st, &mut v[from..end], end - from, false);
    (r.0, Ghost::assume_new())
}

/// Appends zeros up to length `n`.
fn grow_zeros(v: &mut Vec<u8>, n: usize)
    requires
        old(v)@.len() < n,
    ensures
        final(v)@.len() == n,
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
{
    v.resize(n, 0u8);
    proof {
        assert(v@.subrange(0, old(v)@.len() as int) =~= old(v)@);
    }
}

/// `v[..end - from] = v[from..end]`, the rest unchanged.
fn shift_down(v: &mut Vec<u8>, from: usize, end: usize)
    requires
        from <= end <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@.subrange(0, end - from) == old(v)@.subrange(from as int, end as int),
{
    v.as_mut_slice().copy_within(from..end, 0);
    proof {
        assert(v@.subrange(0, end - from) =~= old(v)@.subrange(from as int, end as int));
    }
}

/// `n` zero bytes.
fn vec_zeros(n: usize) -> (r: Vec<u8>)
    ensures
        r@.len() == n,
{
    vec![0u8; n]
}

/// A read head stays read, with its framing, when bytes are added.
proof fn lemma_head_ext(b: Seq<u8>, c: Seq<u8>, max: nat, e: int)
    requires
        parse_request(b, max) matches Parsed::Done(_, f) && f == e,
    ensures
        parse_request(b + c, max) == parse_request(b, max),
        (b + c).subrange(0, e) == b.subrange(0, e),
{
    theorem_request_ext(b, c, max);
    lemma_skip_nonneg(b, max);
    assert((b + c).subrange(0, e) =~= b.subrange(0, e));
}

} // verus!
