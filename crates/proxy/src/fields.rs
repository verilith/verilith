//! Which fields the proxy forwards (verified): the client's request
//! fields to the upstream, and the upstream's response fields to the
//! client.
//!
//! Both go through the verified hop-by-hop filter ([`crate::hop::forward`]).
//! A request then loses every field the proxy sets itself
//! ([`proxy_sets`]: X-Forwarded-For, X-Forwarded-Proto, X-Forwarded-Host,
//! Forwarded, Via, Expect, Cookie and Accept-Encoding, by name ignoring
//! ASCII case), and the proxy's own fields are appended
//! ([`request_fields`]). So a client cannot make the upstream see an
//! X-Forwarded-For, X-Forwarded-Proto or Via of its choosing: each field
//! of the result with such a name is one the proxy passed in `own`
//! ([`theorem_request_fields`]). A response loses Date and Server, which
//! the server writes, and Age, which the cache sets ([`response_fields`]).
use vstd::prelude::*;
use verilith_http::framing::ci_eq_exec;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::ci_eq;
use verilith_server::respond::Field;
#[cfg(verus_keep_ghost)]
use verilith_server::respond::{field_view, fields_view, SField};
#[cfg(verus_keep_ghost)]
use crate::hop::{forwarded, keeps, theorem_forwarded};

verus! {

pub open spec fn s_x_forwarded_for() -> Seq<u8> { seq![0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x66, 0x6f, 0x72] }
pub open spec fn s_x_forwarded_proto() -> Seq<u8> { seq![0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x70, 0x72, 0x6f, 0x74, 0x6f] }
pub open spec fn s_x_forwarded_host() -> Seq<u8> { seq![0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x68, 0x6f, 0x73, 0x74] }
pub open spec fn s_forwarded() -> Seq<u8> { seq![0x66u8, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64] }
pub open spec fn s_via() -> Seq<u8> { seq![0x76u8, 0x69, 0x61] }
pub open spec fn s_expect() -> Seq<u8> { seq![0x65u8, 0x78, 0x70, 0x65, 0x63, 0x74] }
pub open spec fn s_cookie() -> Seq<u8> { seq![0x63u8, 0x6f, 0x6f, 0x6b, 0x69, 0x65] }
pub open spec fn s_accept_encoding() -> Seq<u8> { seq![0x61u8, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67] }
pub open spec fn s_date() -> Seq<u8> { seq![0x64u8, 0x61, 0x74, 0x65] }
pub open spec fn s_server() -> Seq<u8> { seq![0x73u8, 0x65, 0x72, 0x76, 0x65, 0x72] }
pub open spec fn s_age() -> Seq<u8> { seq![0x61u8, 0x67, 0x65] }

/// A request field the proxy writes itself, so never forwards a client's.
pub open spec fn proxy_sets(n: Seq<u8>) -> bool {
    ci_eq(n, s_x_forwarded_for())
        || ci_eq(n, s_x_forwarded_proto())
        || ci_eq(n, s_x_forwarded_host())
        || ci_eq(n, s_forwarded())
        || ci_eq(n, s_via())
        || ci_eq(n, s_expect())
        || ci_eq(n, s_cookie())
        || ci_eq(n, s_accept_encoding())
}

/// A response field the server or the cache writes itself.
pub open spec fn server_sets(n: Seq<u8>) -> bool {
    ci_eq(n, s_date()) || ci_eq(n, s_server()) || ci_eq(n, s_age())
}

/// `fs` without the fields named as `proxy_sets` (`req`) or `server_sets`
/// (not `req`) says, in order.
pub open spec fn without(fs: Seq<SField>, req: bool) -> Seq<SField>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        let r = without(fs.drop_last(), req);
        let n = fs.last().0;
        if (if req { proxy_sets(n) } else { server_sets(n) }) { r } else { r.push(fs.last()) }
    }
}

/// What the request filter guarantees: what it keeps of the forwarded
/// fields is not hop-by-hop and not a field the proxy sets.
pub proof fn theorem_without(fs: Seq<SField>, req: bool)
    ensures
        forall|i: int| 0 <= i < without(fs, req).len() ==> #[trigger] fs.contains(without(fs, req)[i])
            && (if req { !proxy_sets(without(fs, req)[i].0) } else { !server_sets(without(fs, req)[i].0) }),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_last();
        theorem_without(t, req);
        let r = without(t, req);
        assert forall|i: int| 0 <= i < without(fs, req).len() implies #[trigger] fs.contains(without(fs, req)[i])
            && (if req { !proxy_sets(without(fs, req)[i].0) } else { !server_sets(without(fs, req)[i].0) }) by {
            let w = without(fs, req);
            if i < r.len() {
                assert(w[i] == r[i]);
                assert(t.contains(r[i]));
                let j = choose|j: int| 0 <= j < t.len() && t[j] == r[i];
                assert(fs[j] == t[j]);
            } else {
                assert(w[i] == fs.last());
                assert(fs[fs.len() - 1] == fs.last());
            }
        }
    }
}

/// The request's forwarded fields: the client's `fs`, without hop-by-hop
/// fields and the fields the proxy sets, then the proxy's `own`.
pub open spec fn request_spec(fs: Seq<SField>, own: Seq<SField>) -> Seq<SField> {
    without(forwarded(fs, fs), true) + own
}

/// Each field of the forwarded request either is one of `own` or is a
/// client field that is neither hop-by-hop nor one the proxy sets.
pub proof fn theorem_request_fields(fs: Seq<SField>, own: Seq<SField>)
    ensures
        forall|i: int| 0 <= i < request_spec(fs, own).len() ==> {
            let f = #[trigger] request_spec(fs, own)[i];
            own.contains(f) || (fs.contains(f) && keeps(fs, f.0) && !proxy_sets(f.0))
        },
{
    let fw = forwarded(fs, fs);
    theorem_forwarded(fs, fs);
    theorem_without(fw, true);
    lemma_forwarded_in(fs, fs);
    let w = without(fw, true);
    assert forall|i: int| 0 <= i < request_spec(fs, own).len() implies {
        let f = #[trigger] request_spec(fs, own)[i];
        own.contains(f) || (fs.contains(f) && keeps(fs, f.0) && !proxy_sets(f.0))
    } by {
        let f = request_spec(fs, own)[i];
        if i < w.len() {
            assert(f == w[i]);
            assert(fw.contains(f));
            let j = choose|j: int| 0 <= j < fw.len() && fw[j] == f;
            assert(keeps(fs, fw[j].0));
        } else {
            assert(f == own[i - w.len()]);
        }
    }
}

/// Everything `forwarded` keeps is a field of the input.
pub proof fn lemma_forwarded_in(fs: Seq<SField>, all: Seq<SField>)
    ensures forall|i: int| 0 <= i < forwarded(fs, all).len() ==> #[trigger] fs.contains(forwarded(fs, all)[i]),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_last();
        lemma_forwarded_in(t, all);
        let r = forwarded(t, all);
        let w = forwarded(fs, all);
        assert(w == if keeps(all, fs.last().0) { r.push(fs.last()) } else { r });
        assert forall|i: int| 0 <= i < w.len() implies #[trigger] fs.contains(w[i]) by {
            if i < r.len() {
                assert(w[i] == r[i]);
                assert(t.contains(forwarded(t, all)[i]));
                let j = choose|j: int| 0 <= j < t.len() && t[j] == r[i];
                assert(fs[j] == t[j]);
            } else {
                assert(w[i] == fs.last());
                assert(fs[fs.len() - 1] == fs.last());
            }
        }
    }
}

/// [`proxy_sets`].
pub fn proxy_sets_exec(n: &[u8]) -> (r: bool)
    ensures r == proxy_sets(n@),
{
    let a0: [u8; 15] = [0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x66, 0x6f, 0x72];
    let a1: [u8; 17] = [0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x70, 0x72, 0x6f, 0x74, 0x6f];
    let a2: [u8; 16] = [0x78u8, 0x2d, 0x66, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64, 0x2d, 0x68, 0x6f, 0x73, 0x74];
    let a3: [u8; 9] = [0x66u8, 0x6f, 0x72, 0x77, 0x61, 0x72, 0x64, 0x65, 0x64];
    let a4: [u8; 3] = [0x76u8, 0x69, 0x61];
    let a5: [u8; 6] = [0x65u8, 0x78, 0x70, 0x65, 0x63, 0x74];
    let a6: [u8; 6] = [0x63u8, 0x6f, 0x6f, 0x6b, 0x69, 0x65];
    let a7: [u8; 15] = [0x61u8, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67];
    assert(a0@ =~= s_x_forwarded_for());
    assert(a1@ =~= s_x_forwarded_proto());
    assert(a2@ =~= s_x_forwarded_host());
    assert(a3@ =~= s_forwarded());
    assert(a4@ =~= s_via());
    assert(a5@ =~= s_expect());
    assert(a6@ =~= s_cookie());
    assert(a7@ =~= s_accept_encoding());
    ci_eq_exec(n, &a0)
        || ci_eq_exec(n, &a1)
        || ci_eq_exec(n, &a2)
        || ci_eq_exec(n, &a3)
        || ci_eq_exec(n, &a4)
        || ci_eq_exec(n, &a5)
        || ci_eq_exec(n, &a6)
        || ci_eq_exec(n, &a7)
}

/// [`server_sets`].
pub fn server_sets_exec(n: &[u8]) -> (r: bool)
    ensures r == server_sets(n@),
{
    let a0: [u8; 4] = [0x64u8, 0x61, 0x74, 0x65];
    let a1: [u8; 6] = [0x73u8, 0x65, 0x72, 0x76, 0x65, 0x72];
    let a2: [u8; 3] = [0x61u8, 0x67, 0x65];
    assert(a0@ =~= s_date());
    assert(a1@ =~= s_server());
    assert(a2@ =~= s_age());
    ci_eq_exec(n, &a0) || ci_eq_exec(n, &a1) || ci_eq_exec(n, &a2)
}

/// Appends to `out` the fields of `fs` that [`without`] keeps.
fn drop_set<'a>(fs: &Vec<Field<'a>>, req: bool, out: &mut Vec<Field<'a>>)
    ensures fields_view(final(out)@) == fields_view(old(out)@) + without(fields_view(fs@), req),
{
    let ghost fv = fields_view(fs@);
    let ghost o = fields_view(out@);
    let mut k: usize = 0;
    assert(fv.take(0) =~= Seq::<SField>::empty());
    assert(fields_view(out@) =~= o + without(fv.take(0), req));
    while k < fs.len()
        invariant
            k <= fs@.len(),
            fv == fields_view(fs@),
            fields_view(out@) == o + without(fv.take(k as int), req),
        decreases fs@.len() - k,
    {
        let f = fs[k];
        let set = if req { proxy_sets_exec(f.name) } else { server_sets_exec(f.name) };
        proof {
            assert(fv.take(k + 1).drop_last() =~= fv.take(k as int));
            assert(fv.take(k + 1).last() == fv[k as int]);
            assert(fv[k as int] == field_view(fs@[k as int]));
        }
        let ghost before = out@;
        if !set {
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

/// The fields of the request to the upstream: exactly [`request_spec`] of
/// the client's `fs` and the proxy's `own`.
pub fn request_fields<'a>(fs: &[Field<'a>], own: &[Field<'a>]) -> (r: Vec<Field<'a>>)
    ensures fields_view(r@) == request_spec(fields_view(fs@), fields_view(own@)),
{
    let mut fw: Vec<Field<'a>> = Vec::with_capacity(fs.len());
    crate::hop::forward(fs, &mut fw);
    assert(fields_view(fw@) =~= forwarded(fields_view(fs@), fields_view(fs@)));
    let cap = if own.len() <= usize::MAX - fw.len() { fw.len() + own.len() } else { fw.len() };
    let mut out: Vec<Field<'a>> = Vec::with_capacity(cap);
    assert(fields_view(out@) =~= Seq::<SField>::empty());
    drop_set(&fw, true, &mut out);
    let ghost mid = out@;
    let mut k: usize = 0;
    while k < own.len()
        invariant
            k <= own@.len(),
            out@ == mid + own@.take(k as int),
        decreases own@.len() - k,
    {
        out.push(own[k]);
        proof { assert(own@.take(k + 1) =~= own@.take(k as int).push(own@[k as int])); }
        k += 1;
    }
    proof {
        assert(own@.take(own@.len() as int) =~= own@);
        assert(fields_view(out@) =~= fields_view(mid) + fields_view(own@)) by {
            lemma_fields_view_add(mid, own@);
        }
    }
    out
}

/// The upstream's response fields as the client gets them: through the
/// hop-by-hop filter, without Date, Server and Age.
pub fn response_fields<'a>(fs: &[Field<'a>]) -> (r: Vec<Field<'a>>)
    ensures fields_view(r@) == without(forwarded(fields_view(fs@), fields_view(fs@)), false),
{
    let mut fw: Vec<Field<'a>> = Vec::with_capacity(fs.len());
    crate::hop::forward(fs, &mut fw);
    assert(fields_view(fw@) =~= forwarded(fields_view(fs@), fields_view(fs@)));
    let mut out: Vec<Field<'a>> = Vec::with_capacity(fw.len());
    assert(fields_view(out@) =~= Seq::<SField>::empty());
    drop_set(&fw, false, &mut out);
    assert(fields_view(out@) =~= without(fields_view(fw@), false));
    out
}

proof fn lemma_fields_view_add(a: Seq<Field>, b: Seq<Field>)
    ensures fields_view(a + b) =~= fields_view(a) + fields_view(b),
{
    assert(fields_view(a + b).len() == fields_view(a).len() + fields_view(b).len());
    assert forall|i: int| 0 <= i < fields_view(a + b).len() implies fields_view(a + b)[i] == (fields_view(a) + fields_view(b))[i] by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

} // verus!
