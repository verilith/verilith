//! Verified hop-by-hop filtering (RFC 9110 §7.6.1).
//!
//! A proxy must not forward the fields that describe one connection:
//! `Connection` and every field it names, and the fields RFC 9110 and 9112
//! define as connection-specific (`Keep-Alive`, `Proxy-Connection`, `TE`,
//! `Transfer-Encoding`, `Upgrade`, `Trailer`, and the proxy's own
//! `Proxy-Authorization` and `Proxy-Authenticate`). It also drops `Host`
//! and `Content-Length`, which it writes itself for the next hop.
//! [`forwarded`] is the specification, a filter that keeps the order of
//! what it keeps; [`forward`] computes it exactly, in both directions
//! (requests to the backend, responses to the client). Every name is
//! compared ignoring ASCII case, and a Connection field's options are the
//! elements of its comma-separated list with OWS trimmed, the same reading
//! verilith-server's persistence proof uses (`persist.rs`).
use vstd::prelude::*;
use verilith_http::framing::ci_eq_exec;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::{ci_eq, lower, trim_end};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{comma_end, element, lead, name_connection};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{lemma_comma_end, lemma_lead, lemma_trim};
use verilith_server::respond::{Field, SField};
#[cfg(verus_keep_ghost)]
use verilith_server::respond::{field_view, fields_view};
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// Equal ignoring ASCII case.
pub open spec fn same_ci(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> lower(#[trigger] a[i]) == lower(b[i])
}

/// Whether the list `v[i..]` has an element equal to `n` ignoring case.
pub open spec fn listed(v: Seq<u8>, i: int, n: Seq<u8>) -> bool
    decreases v.len() - i,
{
    if i < 0 || i > v.len() {
        false
    } else {
        let c = comma_end(v, i);
        same_ci(element(v, i, c), n) || (i <= c < v.len() && listed(v, c + 1, n))
    }
}

/// Whether a Connection field among `fs` names `n`.
pub open spec fn conn_listed(fs: Seq<SField>, n: Seq<u8>) -> bool
    decreases fs.len(),
{
    if fs.len() == 0 {
        false
    } else {
        conn_listed(fs.drop_last(), n) || (ci_eq(fs.last().0, name_connection()) && listed(
            fs.last().1,
            0,
            n,
        ))
    }
}

pub open spec fn s_keep_alive() -> Seq<u8> { seq![0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65] }
pub open spec fn s_proxy_connection() -> Seq<u8> { seq![0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e] }
pub open spec fn s_te() -> Seq<u8> { seq![0x74u8, 0x65] }
pub open spec fn s_transfer_encoding() -> Seq<u8> { seq![0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67] }
pub open spec fn s_upgrade() -> Seq<u8> { seq![0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65] }
pub open spec fn s_trailer() -> Seq<u8> { seq![0x74u8, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72] }
pub open spec fn s_proxy_authorization() -> Seq<u8> { seq![0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x7a, 0x61, 0x74, 0x69, 0x6f, 0x6e] }
pub open spec fn s_proxy_authenticate() -> Seq<u8> { seq![0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x61, 0x75, 0x74, 0x68, 0x65, 0x6e, 0x74, 0x69, 0x63, 0x61, 0x74, 0x65] }
pub open spec fn s_host() -> Seq<u8> { seq![0x68u8, 0x6f, 0x73, 0x74] }
pub open spec fn s_content_length() -> Seq<u8> { seq![0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68] }

/// A field the proxy never forwards, whatever the Connection fields say.
pub open spec fn hop_name(n: Seq<u8>) -> bool {
    ci_eq(n, name_connection()) || ci_eq(n, s_keep_alive()) || ci_eq(n, s_proxy_connection())
        || ci_eq(n, s_te()) || ci_eq(n, s_transfer_encoding()) || ci_eq(n, s_upgrade())
        || ci_eq(n, s_trailer()) || ci_eq(n, s_proxy_authorization()) || ci_eq(
        n,
        s_proxy_authenticate(),
    ) || ci_eq(n, s_host()) || ci_eq(n, s_content_length())
}

/// Whether a field named `n`, in a message with the fields `all`, is
/// forwarded.
pub open spec fn keeps(all: Seq<SField>, n: Seq<u8>) -> bool {
    !hop_name(n) && !conn_listed(all, n)
}

/// The fields of `fs` that are forwarded, in order, in a message whose
/// fields are `all`.
pub open spec fn forwarded(fs: Seq<SField>, all: Seq<SField>) -> Seq<SField>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        let r = forwarded(fs.drop_last(), all);
        if keeps(all, fs.last().0) { r.push(fs.last()) } else { r }
    }
}

/// What the filter guarantees: nothing it keeps is connection-specific,
/// and it keeps everything else.
pub proof fn theorem_forwarded(fs: Seq<SField>, all: Seq<SField>)
    ensures
        forall|i: int| 0 <= i < forwarded(fs, all).len() ==> keeps(all, #[trigger] forwarded(fs, all)[i].0),
        forwarded(fs, all).len() <= fs.len(),
        (forall|i: int| 0 <= i < fs.len() ==> keeps(all, #[trigger] fs[i].0)) ==> forwarded(fs, all) == fs,
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_last();
        theorem_forwarded(t, all);
        if forall|i: int| 0 <= i < fs.len() ==> keeps(all, #[trigger] fs[i].0) {
            assert forall|i: int| 0 <= i < t.len() implies keeps(all, #[trigger] t[i].0) by {
                assert(t[i] == fs[i]);
            }
            assert(keeps(all, fs[fs.len() - 1].0));
            assert(fs == t.push(fs.last()));
        }
        let r = forwarded(t, all);
        if keeps(all, fs.last().0) {
            assert forall|i: int| 0 <= i < r.push(fs.last()).len() implies keeps(all, #[trigger] r.push(fs.last())[i].0) by {
                if i < r.len() {
                    assert(r.push(fs.last())[i] == r[i]);
                }
            }
        }
    } else {
        assert(fs =~= Seq::<SField>::empty());
    }
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

#[inline]
fn lower_exec(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if c >= 0x41 && c <= 0x5A { c + 0x20 } else { c }
}

/// [`same_ci`].
pub fn same_ci_exec(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == same_ci(a@, b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> lower(#[trigger] a@[j]) == lower(b@[j]),
        decreases a.len() - i,
    {
        if lower_exec(a[i]) != lower_exec(b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// [`listed`] from 0.
pub fn listed_exec(v: &[u8], n: &[u8]) -> (r: bool)
    ensures
        r == listed(v@, 0, n@),
{
    let len = v.len();
    let mut i: usize = 0;
    loop
        invariant
            len == v@.len(),
            i <= len,
            listed(v@, 0, n@) == listed(v@, i as int, n@),
        decreases len - i,
    {
        proof {
            lemma_comma_end(v@, i as int);
        }
        let mut c = i;
        while c < len && v[c] != 0x2c
            invariant
                len == v@.len(),
                i <= c <= len,
                comma_end(v@, i as int) == comma_end(v@, c as int),
            decreases len - c,
        {
            c += 1;
        }
        let mut s = i;
        proof {
            lemma_lead(v@, i as int, c as int);
        }
        while s < c && (v[s] == 0x20 || v[s] == 0x09)
            invariant
                len == v@.len(),
                i <= s <= c <= len,
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
                len == v@.len(),
                s <= t <= c <= len,
                trim_end(v@, s as int, c as int) == trim_end(v@, s as int, t as int),
            decreases t - s,
        {
            t -= 1;
        }
        let el = slice_subrange(v, s, t);
        assert(el@ =~= element(v@, i as int, c as int));
        if same_ci_exec(el, n) {
            return true;
        }
        if c >= len {
            return false;
        }
        i = c + 1;
    }
}

/// [`conn_listed`].
pub fn conn_listed_exec(fs: &[Field], n: &[u8]) -> (r: bool)
    ensures
        r == conn_listed(fields_view(fs@), n@),
{
    let ghost fv = fields_view(fs@);
    let mut k: usize = 0;
    let mut acc = false;
    assert(fv.take(0) =~= Seq::<SField>::empty());
    while k < fs.len()
        invariant
            k <= fs@.len(),
            fv == fields_view(fs@),
            acc == conn_listed(fv.take(k as int), n@),
        decreases fs@.len() - k,
    {
        let f = &fs[k];
        let conn: [u8; 10] = [0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
        assert(conn@ =~= name_connection());
        let this = ci_eq_exec(f.name, &conn) && listed_exec(f.value, n);
        proof {
            assert(fv.take(k + 1).drop_last() =~= fv.take(k as int));
            assert(fv.take(k + 1).last() == fv[k as int]);
            assert(fv[k as int] == field_view(fs@[k as int]));
        }
        acc = acc || this;
        k += 1;
    }
    assert(fv.take(fs@.len() as int) =~= fv);
    acc
}

/// [`hop_name`].
pub fn hop_name_exec(n: &[u8]) -> (r: bool)
    ensures
        r == hop_name(n@),
{
    let a: [u8; 10] = [0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let b: [u8; 10] = [0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65];
    let c: [u8; 16] = [0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let d: [u8; 2] = [0x74u8, 0x65];
    let e: [u8; 17] = [0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67];
    let f: [u8; 7] = [0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65];
    let g: [u8; 7] = [0x74u8, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72];
    let h: [u8; 19] = [0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x7a, 0x61, 0x74, 0x69, 0x6f, 0x6e];
    let i: [u8; 18] = [0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x61, 0x75, 0x74, 0x68, 0x65, 0x6e, 0x74, 0x69, 0x63, 0x61, 0x74, 0x65];
    let j: [u8; 4] = [0x68u8, 0x6f, 0x73, 0x74];
    let k: [u8; 14] = [0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68];
    assert(a@ =~= name_connection());
    assert(b@ =~= s_keep_alive());
    assert(c@ =~= s_proxy_connection());
    assert(d@ =~= s_te());
    assert(e@ =~= s_transfer_encoding());
    assert(f@ =~= s_upgrade());
    assert(g@ =~= s_trailer());
    assert(h@ =~= s_proxy_authorization());
    assert(i@ =~= s_proxy_authenticate());
    assert(j@ =~= s_host());
    assert(k@ =~= s_content_length());
    ci_eq_exec(n, &a) || ci_eq_exec(n, &b) || ci_eq_exec(n, &c) || ci_eq_exec(n, &d) || ci_eq_exec(n, &e)
        || ci_eq_exec(n, &f) || ci_eq_exec(n, &g) || ci_eq_exec(n, &h) || ci_eq_exec(n, &i)
        || ci_eq_exec(n, &j) || ci_eq_exec(n, &k)
}

/// Appends to `out` the fields of `fs` that are forwarded: exactly
/// [`forwarded`] of them.
pub fn forward<'a>(fs: &[Field<'a>], out: &mut Vec<Field<'a>>)
    ensures
        fields_view(final(out)@) == fields_view(old(out)@) + forwarded(fields_view(fs@), fields_view(fs@)),
{
    let ghost fv = fields_view(fs@);
    let ghost o = fields_view(out@);
    let mut k: usize = 0;
    assert(fv.take(0) =~= Seq::<SField>::empty());
    assert(fields_view(out@) =~= o + forwarded(fv.take(0), fv));
    while k < fs.len()
        invariant
            k <= fs@.len(),
            fv == fields_view(fs@),
            fields_view(out@) == o + forwarded(fv.take(k as int), fv),
        decreases fs@.len() - k,
    {
        let f = fs[k];
        let keep = !hop_name_exec(f.name) && !conn_listed_exec(fs, f.name);
        proof {
            assert(fv.take(k + 1).drop_last() =~= fv.take(k as int));
            assert(fv.take(k + 1).last() == fv[k as int]);
            assert(fv[k as int] == field_view(fs@[k as int]));
        }
        let ghost before = out@;
        if keep {
            out.push(f);
            proof {
                assert(out@ == before.push(f));
                assert(fields_view(out@) =~= fields_view(before).push(field_view(f)));
            }
        }
        k += 1;
    }
    assert(fv.take(fs@.len() as int) =~= fv);
}

} // verus!
