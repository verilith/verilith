//! Persistence (RFC 9112 §9.3), verified: whether a connection may carry
//! another request after this one.
//!
//! [`persists`] is the specification: a request persists unless a
//! `Connection` field lists the option `close`; an HTTP/1.0 request
//! persists only if one lists `keep-alive`. Options are the elements of the
//! comma-separated values (RFC 9110 §7.6.1, §5.6.1), compared ignoring
//! ASCII case after OWS is trimmed. [`persists_exec`] computes it exactly,
//! and `conn::Core::done` moves on to a next request only if the one
//! answered persists (its precondition).
use vstd::prelude::*;

use verilith_http::framing::ci_eq_exec;
#[cfg(verus_keep_ghost)]
use verilith_http::parse::{hdr_ok, hdrs_ok, headers_view};
use verilith_http::parse::Header;
use verilith_http::spec::*;
use vstd::slice::slice_subrange;

verus! {

/// "connection"
pub open spec fn name_connection() -> Seq<u8> {
    seq![0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e]
}

/// "close"
pub open spec fn opt_close() -> Seq<u8> {
    seq![0x63u8, 0x6c, 0x6f, 0x73, 0x65]
}

/// "keep-alive"
pub open spec fn opt_keep_alive() -> Seq<u8> {
    seq![0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65]
}

/// The next `,` from `i`, or the end.
pub open spec fn comma_end(v: Seq<u8>, i: int) -> int
    decreases v.len() - i,
{
    if i < 0 || i >= v.len() || v[i] == 0x2c { i } else { comma_end(v, i + 1) }
}

/// `i` moved past leading OWS, up to `e`.
pub open spec fn lead(v: Seq<u8>, i: int, e: int) -> int
    decreases e - i,
{
    if i < e && 0 <= i < v.len() && is_ows(v[i]) { lead(v, i + 1, e) } else { i }
}

/// `v[i..e]` with OWS trimmed from both ends.
pub open spec fn element(v: Seq<u8>, i: int, e: int) -> Seq<u8> {
    let a = lead(v, i, e);
    v.subrange(a, trim_end(v, a, e))
}

/// The options of the list `v[i..]`, added to `acc`: (close, keep-alive).
pub open spec fn opts(v: Seq<u8>, i: int, acc: (bool, bool)) -> (bool, bool)
    decreases v.len() - i,
{
    if i < 0 || i > v.len() {
        acc
    } else {
        let c = comma_end(v, i);
        let el = element(v, i, c);
        let acc2 = (acc.0 || ci_eq(el, opt_close()), acc.1 || ci_eq(el, opt_keep_alive()));
        if c >= v.len() || c < i { acc2 } else { opts(v, c + 1, acc2) }
    }
}

pub open spec fn span_bytes(b: Seq<u8>, s: SpecSpan) -> Seq<u8> {
    b.subrange(s.start, s.end)
}

/// The Connection options of the field lines `hs` over `b`.
pub open spec fn conn_of(b: Seq<u8>, hs: Seq<SpecHeader>) -> (bool, bool)
    decreases hs.len(),
{
    if hs.len() == 0 {
        (false, false)
    } else {
        let r = conn_of(b, hs.drop_last());
        let h = hs.last();
        if ci_eq(span_bytes(b, h.name), name_connection()) { opts(span_bytes(b, h.value), 0, r) } else { r }
    }
}

/// RFC 9112 §9.3.
pub open spec fn persists_hm(b: Seq<u8>, hs: Seq<SpecHeader>, minor: u8) -> bool {
    let (close, keep) = conn_of(b, hs);
    !close && (minor >= 1 || keep)
}

pub open spec fn persists(b: Seq<u8>, q: SpecRequest) -> bool {
    persists_hm(b, q.headers, q.minor)
}

pub open spec fn spans_in(hs: Seq<SpecHeader>, n: int) -> bool {
    forall|j: int| 0 <= j < hs.len() ==> {
        &&& 0 <= #[trigger] hs[j].name.start <= hs[j].name.end <= n
        &&& 0 <= hs[j].value.start <= hs[j].value.end <= n
    }
}

/// Persistence reads only the field lines' bytes: two buffers that agree
/// on `0..e` agree on it.
pub proof fn lemma_conn_frame(x: Seq<u8>, y: Seq<u8>, hs: Seq<SpecHeader>, e: int)
    requires
        spans_in(hs, e),
        e <= x.len(),
        e <= y.len(),
        x.subrange(0, e) == y.subrange(0, e),
    ensures
        conn_of(x, hs) == conn_of(y, hs),
    decreases hs.len(),
{
    if hs.len() > 0 {
        let t = hs.drop_last();
        assert forall|j: int| 0 <= j < t.len() implies {
            &&& 0 <= #[trigger] t[j].name.start <= t[j].name.end <= e
            &&& 0 <= t[j].value.start <= t[j].value.end <= e
        } by {
            assert(t[j] == hs[j]);
        }
        lemma_conn_frame(x, y, t, e);
        let h = hs.last();
        assert(hs[hs.len() - 1] == h);
        assert(span_bytes(x, h.name) =~= x.subrange(0, e).subrange(h.name.start, h.name.end));
        assert(span_bytes(y, h.name) =~= y.subrange(0, e).subrange(h.name.start, h.name.end));
        assert(span_bytes(x, h.value) =~= x.subrange(0, e).subrange(h.value.start, h.value.end));
        assert(span_bytes(y, h.value) =~= y.subrange(0, e).subrange(h.value.start, h.value.end));
    }
}

proof fn lemma_comma_end(v: Seq<u8>, i: int)
    requires 0 <= i <= v.len(),
    ensures
        i <= comma_end(v, i) <= v.len(),
        comma_end(v, i) < v.len() ==> v[comma_end(v, i)] == 0x2c,
    decreases v.len() - i,
{
    if i < v.len() && v[i] != 0x2c {
        lemma_comma_end(v, i + 1);
    }
}

proof fn lemma_lead(v: Seq<u8>, i: int, e: int)
    requires 0 <= i <= e <= v.len(),
    ensures i <= lead(v, i, e) <= e,
    decreases e - i,
{
    if i < e && is_ows(v[i]) {
        lemma_lead(v, i + 1, e);
    }
}

proof fn lemma_trim(v: Seq<u8>, s: int, e: int)
    requires s <= e,
    ensures s <= trim_end(v, s, e) <= e,
    decreases e - s,
{
    if !(e <= s || !is_ows(v[e - 1])) {
        lemma_trim(v, s, e - 1);
    }
}

/// The options of `v`, added to `acc`: exactly [`opts`] from 0.
pub fn opts_exec(v: &[u8], acc: (bool, bool)) -> (r: (bool, bool))
    ensures r == opts(v@, 0, acc),
{
    let n = v.len();
    let mut i: usize = 0;
    let mut a = acc;
    loop
        invariant
            n == v@.len(),
            i <= n,
            opts(v@, 0, acc) == opts(v@, i as int, a),
        decreases n - i,
    {
        proof {
            lemma_comma_end(v@, i as int);
        }
        let mut c = i;
        while c < n && v[c] != 0x2c
            invariant
                n == v@.len(),
                i <= c <= n,
                comma_end(v@, i as int) == comma_end(v@, c as int),
            decreases n - c,
        {
            c += 1;
        }
        let mut s = i;
        proof {
            lemma_lead(v@, i as int, c as int);
        }
        while s < c && (v[s] == 0x20 || v[s] == 0x09)
            invariant
                n == v@.len(),
                i <= s <= c <= n,
                lead(v@, i as int, c as int) == lead(v@, s as int, c as int),
            decreases c - s,
        {
            s += 1;
        }
        let mut t = c;
        proof {
            lemma_trim(v@, s as int, c as int);
        }
        while t > s && (v[t - 1] == 0x20 || v[t - 1] == 0x09)
            invariant
                n == v@.len(),
                s <= t <= c <= n,
                trim_end(v@, s as int, c as int) == trim_end(v@, s as int, t as int),
            decreases t - s,
        {
            t -= 1;
        }
        let el = slice_subrange(v, s, t);
        assert(el@ =~= element(v@, i as int, c as int));
        let close: [u8; 5] = [0x63u8, 0x6c, 0x6f, 0x73, 0x65];
        let keep: [u8; 10] = [0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65];
        proof {
            assert(close@ =~= opt_close());
            assert(keep@ =~= opt_keep_alive());
        }
        let is_close = ci_eq_exec(el, close.as_slice());
        let is_keep = ci_eq_exec(el, keep.as_slice());
        a = (a.0 || is_close, a.1 || is_keep);
        if c >= n {
            return a;
        }
        i = c + 1;
    }
}

/// [`persists_hm`] for exec field lines over `b`.
pub fn persists_exec(b: &[u8], hs: &[Header], minor: u8) -> (r: bool)
    requires hdrs_ok(hs@, b@.len() as int),
    ensures r == persists_hm(b@, headers_view(hs@), minor),
{
    let mut acc = (false, false);
    let mut k: usize = 0;
    proof {
        assert(headers_view(hs@).subrange(0, 0) =~= Seq::<SpecHeader>::empty());
    }
    while k < hs.len()
        invariant
            k <= hs@.len(),
            hdrs_ok(hs@, b@.len() as int),
            acc == conn_of(b@, headers_view(hs@).subrange(0, k as int)),
        decreases hs@.len() - k,
    {
        let h = hs[k];
        proof {
            assert(hdr_ok(hs@[k as int], b@.len() as int));
            let t = headers_view(hs@).subrange(0, k as int + 1);
            assert(t.drop_last() =~= headers_view(hs@).subrange(0, k as int));
            assert(t.last() == h@);
        }
        let name = slice_subrange(b, h.name.start, h.name.end);
        assert(name@ =~= span_bytes(b@, h@.name));
        let conn: [u8; 10] = [0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
        assert(conn@ =~= name_connection());
        if ci_eq_exec(name, conn.as_slice()) {
            let v = slice_subrange(b, h.value.start, h.value.end);
            assert(v@ =~= span_bytes(b@, h@.value));
            acc = opts_exec(v, acc);
        }
        k += 1;
    }
    assert(headers_view(hs@).subrange(0, hs@.len() as int) =~= headers_view(hs@));
    !acc.0 && (minor >= 1 || acc.1)
}

/// Whether response field lines `fs` list the connection option `close`
/// (RFC 9112 §9.6): a server that sends it must close after the response.
pub open spec fn fields_close(fs: Seq<(Seq<u8>, Seq<u8>)>) -> bool
    decreases fs.len(),
{
    if fs.len() == 0 {
        false
    } else {
        fields_close(fs.drop_last()) || (ci_eq(fs.last().0, name_connection()) && opts(fs.last().1, 0, (false, false)).0)
    }
}

pub proof fn lemma_fields_close_concat(a: Seq<(Seq<u8>, Seq<u8>)>, b: Seq<(Seq<u8>, Seq<u8>)>)
    ensures
        fields_close(a + b) == (fields_close(a) || fields_close(b)),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_fields_close_concat(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// [`fields_close`] of response field lines.
pub fn fields_close_exec(fs: &[crate::respond::Field]) -> (r: bool)
    ensures
        r == fields_close(crate::respond::fields_view(fs@)),
{
    let mut k: usize = 0;
    let mut acc = false;
    proof {
        assert(crate::respond::fields_view(fs@).take(0) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
    }
    while k < fs.len()
        invariant
            k <= fs@.len(),
            acc == fields_close(crate::respond::fields_view(fs@).take(k as int)),
        decreases fs@.len() - k,
    {
        let f = &fs[k];
        let conn: [u8; 10] = [0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
        assert(conn@ =~= name_connection());
        let this = ci_eq_exec(f.name, conn.as_slice()) && opts_exec(f.value, (false, false)).0;
        proof {
            let fv = crate::respond::fields_view(fs@);
            assert(fv.take(k + 1).drop_last() =~= fv.take(k as int));
            assert(fv.take(k + 1).last() == fv[k as int]);
            assert(fv[k as int] == crate::respond::field_view(fs@[k as int]));
        }
        acc = acc || this;
        k += 1;
    }
    assert(crate::respond::fields_view(fs@).take(fs@.len() as int) =~= crate::respond::fields_view(fs@));
    acc
}

} // verus!
