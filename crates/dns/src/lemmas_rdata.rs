//! Proofs about canonical RDATA: it means the same wherever it is placed.
#[cfg(verus_only)]
use crate::lemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::spec_rdata::*;
use vstd::prelude::*;

verus! {

/// `b[lo + d..hi + d]` holds the bytes `b0[lo..hi]`.
pub open spec fn same(b0: Seq<u8>, lo: int, hi: int, b: Seq<u8>, d: int) -> bool {
    &&& 0 <= lo <= hi <= b0.len()
    &&& 0 <= lo + d
    &&& hi + d <= b.len()
    &&& forall|i: int| lo <= i < hi ==> #[trigger] b[i + d] == b0[i]
}

proof fn lemma_same_at(b0: Seq<u8>, lo: int, hi: int, b: Seq<u8>, d: int)
    requires
        0 <= lo <= hi <= b0.len(),
        at(b, lo + d, b0.subrange(lo, hi)),
    ensures
        same(b0, lo, hi, b, d),
{
    assert forall|i: int| lo <= i < hi implies #[trigger] b[i + d] == b0[i] by {
        assert(b.subrange(lo + d, hi + d)[i - lo] == b[i + d]);
    }
}

proof fn lemma_same_sub(b0: Seq<u8>, lo: int, hi: int, b: Seq<u8>, d: int, x: int, y: int)
    requires
        same(b0, lo, hi, b, d),
        lo <= x <= y <= hi,
    ensures
        b.subrange(x + d, y + d) == b0.subrange(x, y),
{
    assert(b.subrange(x + d, y + d) =~= b0.subrange(x, y)) by {
        assert forall|i: int| 0 <= i < y - x implies b.subrange(x + d, y + d)[i] == b0.subrange(
            x,
            y,
        )[i] by {
            assert(b[(x + i) + d] == b0[x + i]);
        }
    }
}

proof fn lemma_u16_same(b0: Seq<u8>, lo: int, hi: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, lo, hi, b, d),
        lo <= p,
        p + 2 <= hi,
    ensures
        parse_u16(b, p + d) == (match parse_u16(b0, p) {
            Some((x, q)) => Some((x, q + d)),
            None => None,
        }),
{
    assert(b[p + d] == b0[p]);
    assert(b[(p + 1) + d] == b0[p + 1]);
}

proof fn lemma_u32_same(b0: Seq<u8>, lo: int, hi: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, lo, hi, b, d),
        lo <= p,
        p + 4 <= hi,
    ensures
        parse_u32(b, p + d) == (match parse_u32(b0, p) {
            Some((x, q)) => Some((x, q + d)),
            None => None,
        }),
{
    assert(b[p + d] == b0[p]);
    assert(b[(p + 1) + d] == b0[p + 1]);
    assert(b[(p + 2) + d] == b0[p + 2]);
    assert(b[(p + 3) + d] == b0[p + 3]);
}

/// A character-string inside bytes that are the same reads the same.
proof fn lemma_cstring_shift(b0: Seq<u8>, p: int, e0: int, b: Seq<u8>, d: int, lim: int, e: int)
    requires
        parse_cstring(b0, p, e0) matches Some((_, q)) && q <= lim,
        same(b0, p, lim, b, d),
        lim + d <= e <= b.len(),
    ensures
        parse_cstring(b, p + d, e) == (match parse_cstring(b0, p, e0) {
            Some((x, q)) => Some((x, q + d)),
            None => None,
        }),
{
    let q = p + 1 + b0[p] as int;
    assert(b[p + d] == b0[p]);
    lemma_same_sub(b0, p, lim, b, d, p + 1, q);
}

/// A name from `parse_name`, written out uncompressed anywhere, parses back
/// to itself.
proof fn lemma_name_moves(b0: Seq<u8>, p: int, b: Seq<u8>, q: int)
    requires
        parse_name(b0, p) is Some,
        at(b, q, ser_name(parse_name(b0, p).unwrap().0)),
    ensures
        parse_name(b, q) == Some(
            (parse_name(b0, p).unwrap().0, q + ser_name(parse_name(b0, p).unwrap().0).len()),
        ),
{
    lemma_parse_name_valid(b0, p);
    lemma_name_roundtrip(b, q, parse_name(b0, p).unwrap().0);
}

proof fn lemma_shift_one_name(b0: Seq<u8>, t: u16, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        t == TYPE_NS || t == TYPE_CNAME || t == TYPE_PTR,
        canon_names(b0, t, s0, e0) is Some,
        at(b, s, canon_names(b0, t, s0, e0).unwrap()),
    ensures
        canon_names(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len()) == canon_names(
            b0,
            t,
            s0,
            e0,
        ),
        parse_rdata(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len()) == parse_rdata(
            b0,
            t,
            s0,
            e0,
        ),
{
    lemma_name_moves(b0, s0, b, s);
}

proof fn lemma_shift_mx_srv(b0: Seq<u8>, t: u16, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        t == TYPE_MX || t == TYPE_SRV,
        canon_names(b0, t, s0, e0) is Some,
        at(b, s, canon_names(b0, t, s0, e0).unwrap()),
    ensures
        canon_names(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len()) == canon_names(
            b0,
            t,
            s0,
            e0,
        ),
        parse_rdata(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len()) == parse_rdata(
            b0,
            t,
            s0,
            e0,
        ),
{
    let c = canon_names(b0, t, s0, e0).unwrap();
    let k: int = if t == TYPE_MX { 2 } else { 6 };
    let n = parse_name_exact(b0, s0 + k, e0).unwrap();
    let pre = b0.subrange(s0, s0 + k);
    assert(c == pre + ser_name(n));
    lemma_at_split(b, s, pre, ser_name(n));
    lemma_name_moves(b0, s0 + k, b, s + k);
    lemma_same_at(b0, s0, s0 + k, b, s - s0);
    assert(b[s0 + (s - s0)] == b0[s0]);
    assert(b[(s0 + 1) + (s - s0)] == b0[s0 + 1]);
    if t == TYPE_SRV {
        assert(b[(s0 + 2) + (s - s0)] == b0[s0 + 2]);
        assert(b[(s0 + 3) + (s - s0)] == b0[s0 + 3]);
        assert(b[(s0 + 4) + (s - s0)] == b0[s0 + 4]);
        assert(b[(s0 + 5) + (s - s0)] == b0[s0 + 5]);
    }
    let e = s + c.len();
    assert(b.subrange(s, s + k) == pre);
    assert(parse_name_exact(b, s + k, e) == Some(n));
}

proof fn lemma_shift_soa(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        canon_names(b0, TYPE_SOA, s0, e0) is Some,
        at(b, s, canon_names(b0, TYPE_SOA, s0, e0).unwrap()),
    ensures
        canon_names(b, TYPE_SOA, s, s + canon_names(b0, TYPE_SOA, s0, e0).unwrap().len())
            == canon_names(b0, TYPE_SOA, s0, e0),
        parse_rdata(b, TYPE_SOA, s, s + canon_names(b0, TYPE_SOA, s0, e0).unwrap().len())
            == parse_rdata(b0, TYPE_SOA, s0, e0),
{
    let c = canon_names(b0, TYPE_SOA, s0, e0).unwrap();
    let (n1, p1) = parse_name_in(b0, s0, e0).unwrap();
    let (n2, p2) = parse_name_in(b0, p1, e0).unwrap();
    let sn1 = ser_name(n1);
    let sn2 = ser_name(n2);
    let tail = b0.subrange(p2, e0);
    assert(c == sn1 + sn2 + tail);
    lemma_at_split(b, s, sn1 + sn2, tail);
    lemma_at_split(b, s, sn1, sn2);
    lemma_name_moves(b0, s0, b, s);
    lemma_name_moves(b0, p1, b, s + sn1.len());
    let q = s + sn1.len() + sn2.len();
    let d = q - p2;
    lemma_parse_name_valid(b0, s0);
    lemma_parse_name_valid(b0, p1);
    lemma_same_at(b0, p2, e0, b, d);
    lemma_u32_same(b0, p2, e0, b, d, p2);
    lemma_u32_same(b0, p2, e0, b, d, p2 + 4);
    lemma_u32_same(b0, p2, e0, b, d, p2 + 8);
    lemma_u32_same(b0, p2, e0, b, d, p2 + 12);
    lemma_u32_same(b0, p2, e0, b, d, p2 + 16);
    lemma_same_sub(b0, p2, e0, b, d, p2, e0);
    let e = s + c.len();
    assert(parse_name_in(b, s, e) == Some((n1, s + sn1.len())));
    assert(parse_name_in(b, s + sn1.len(), e) == Some((n2, q)));
    assert(parse_soa(b, s, e) == parse_soa(b0, s0, e0));
}

proof fn lemma_shift_sig(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        canon_names(b0, TYPE_SIG, s0, e0) is Some,
        at(b, s, canon_names(b0, TYPE_SIG, s0, e0).unwrap()),
    ensures
        canon_names(b, TYPE_SIG, s, s + canon_names(b0, TYPE_SIG, s0, e0).unwrap().len())
            == canon_names(b0, TYPE_SIG, s0, e0),
        parse_rdata(b, TYPE_SIG, s, s + canon_names(b0, TYPE_SIG, s0, e0).unwrap().len())
            == parse_rdata(b0, TYPE_SIG, s0, e0),
{
    let c = canon_names(b0, TYPE_SIG, s0, e0).unwrap();
    let pre = b0.subrange(s0, s0 + 18);
    let (n, p) = parse_name_in(b0, s0 + 18, e0).unwrap();
    let sn = ser_name(n);
    let tail = b0.subrange(p, e0);
    assert(c == pre + sn + tail);
    lemma_at_split(b, s, pre + sn, tail);
    lemma_at_split(b, s, pre, sn);
    lemma_name_moves(b0, s0 + 18, b, s + 18);
    lemma_parse_name_valid(b0, s0 + 18);
    let d = s - s0;
    let e = s + c.len();
    lemma_same_at(b0, s0, s0 + 18, b, d);
    lemma_u16_same(b0, s0, s0 + 18, b, d, s0);
    lemma_u32_same(b0, s0, s0 + 18, b, d, s0 + 4);
    lemma_u32_same(b0, s0, s0 + 18, b, d, s0 + 8);
    lemma_u32_same(b0, s0, s0 + 18, b, d, s0 + 12);
    lemma_u16_same(b0, s0, s0 + 18, b, d, s0 + 16);
    assert(b[(s0 + 2) + d] == b0[s0 + 2]);
    assert(b[(s0 + 3) + d] == b0[s0 + 3]);
    lemma_same_sub(b0, s0, s0 + 18, b, d, s0, s0 + 18);
    let q = s + 18 + sn.len();
    lemma_same_at(b0, p, e0, b, q - p);
    lemma_same_sub(b0, p, e0, b, q - p, p, e0);
    assert(parse_name_in(b, s + 18, e) == Some((n, q)));
    assert(parse_sig(b, s, e) == parse_sig(b0, s0, e0));
}

proof fn lemma_shift_naptr(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        canon_names(b0, TYPE_NAPTR, s0, e0) is Some,
        at(b, s, canon_names(b0, TYPE_NAPTR, s0, e0).unwrap()),
    ensures
        canon_names(b, TYPE_NAPTR, s, s + canon_names(b0, TYPE_NAPTR, s0, e0).unwrap().len())
            == canon_names(b0, TYPE_NAPTR, s0, e0),
        parse_rdata(b, TYPE_NAPTR, s, s + canon_names(b0, TYPE_NAPTR, s0, e0).unwrap().len())
            == parse_rdata(b0, TYPE_NAPTR, s0, e0),
{
    let c = canon_names(b0, TYPE_NAPTR, s0, e0).unwrap();
    let (_, p1) = parse_cstring(b0, s0 + 4, e0).unwrap();
    let (_, p2) = parse_cstring(b0, p1, e0).unwrap();
    let (_, p3) = parse_cstring(b0, p2, e0).unwrap();
    let n = parse_name_exact(b0, p3, e0).unwrap();
    let pre = b0.subrange(s0, p3);
    let sn = ser_name(n);
    assert(c == pre + sn);
    lemma_at_split(b, s, pre, sn);
    let d = s - s0;
    let e = s + c.len();
    lemma_same_at(b0, s0, p3, b, d);
    lemma_name_moves(b0, p3, b, s + pre.len());
    assert(p3 + d == s + pre.len());
    lemma_cstring_shift(b0, s0 + 4, e0, b, d, p3, e);
    lemma_cstring_shift(b0, p1, e0, b, d, p3, e);
    lemma_cstring_shift(b0, p2, e0, b, d, p3, e);
    assert(b[s0 + d] == b0[s0]);
    assert(b[(s0 + 1) + d] == b0[s0 + 1]);
    assert(b[(s0 + 2) + d] == b0[s0 + 2]);
    assert(b[(s0 + 3) + d] == b0[s0 + 3]);
    lemma_same_sub(b0, s0, p3, b, d, s0, p3);
    assert(parse_name_exact(b, p3 + d, e) == Some(n));
}

/// **Canonical RDATA is position-independent.** Canonical RDATA placed
/// anywhere in any buffer is canonical there too, and for the types with
/// names it decodes to the same typed RDATA as the bytes it came from.
pub proof fn lemma_canon_moves(b0: Seq<u8>, t: u16, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        canon_names(b0, t, s0, e0) is Some,
        at(b, s, canon_names(b0, t, s0, e0).unwrap()),
    ensures
        canon_names(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len()) == canon_names(
            b0,
            t,
            s0,
            e0,
        ),
        compressible(t) ==> parse_rdata(b, t, s, s + canon_names(b0, t, s0, e0).unwrap().len())
            == parse_rdata(b0, t, s0, e0),
{
    if t == TYPE_NS || t == TYPE_CNAME || t == TYPE_PTR {
        lemma_shift_one_name(b0, t, s0, e0, b, s);
    } else if t == TYPE_MX || t == TYPE_SRV {
        lemma_shift_mx_srv(b0, t, s0, e0, b, s);
    } else if t == TYPE_SOA {
        lemma_shift_soa(b0, s0, e0, b, s);
    } else if t == TYPE_SIG {
        lemma_shift_sig(b0, s0, e0, b, s);
    } else if t == TYPE_NAPTR {
        lemma_shift_naptr(b0, s0, e0, b, s);
    }
}

/// Canonical RDATA is canonical in a buffer of its own, and placed
/// anywhere it stays canonical (the form `valid_record` requires and
/// `parse_record` checks).
pub proof fn lemma_canon_rdata_moves(b0: Seq<u8>, t: u16, s0: int, e0: int, b: Seq<u8>, s: int)
    requires
        canon_rdata(b0, t, s0, e0) is Some,
        at(b, s, canon_rdata(b0, t, s0, e0).unwrap()),
    ensures
        canon_rdata(b, t, s, s + canon_rdata(b0, t, s0, e0).unwrap().len()) == canon_rdata(
            b0,
            t,
            s0,
            e0,
        ),
        compressible(t) ==> parse_rdata(b, t, s, s + canon_rdata(b0, t, s0, e0).unwrap().len())
            == parse_rdata(b0, t, s0, e0),
{
    lemma_canon_moves(b0, t, s0, e0, b, s);
}

/// The canonical RDATA of a record is canonical on its own.
pub proof fn lemma_canon_rdata_idem(b0: Seq<u8>, t: u16, s0: int, e0: int)
    requires
        canon_rdata(b0, t, s0, e0) is Some,
    ensures
        ({
            let c = canon_rdata(b0, t, s0, e0).unwrap();
            &&& canon_rdata(c, t, 0, c.len() as int) == Some(c)
            &&& compressible(t) ==> parse_rdata(c, t, 0, c.len() as int) == parse_rdata(
                b0,
                t,
                s0,
                e0,
            )
        }),
{
    let c = canon_rdata(b0, t, s0, e0).unwrap();
    lemma_at_whole(c);
    lemma_canon_rdata_moves(b0, t, s0, e0, c, 0);
}

// ---------------------------------------------------------------------------
// The other types read only the RDATA's own bytes
// ---------------------------------------------------------------------------

pub open spec fn shifted<A>(r: Option<(A, int)>, d: int) -> Option<(A, int)> {
    match r {
        Some((x, q)) => Some((x, q + d)),
        None => None,
    }
}

proof fn lemma_u16_in_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p,
    ensures
        parse_u16_in(b, p + d, e0 + d) == shifted(parse_u16_in(b0, p, e0), d),
{
    if p + 2 <= e0 {
        lemma_u16_same(b0, s0, e0, b, d, p);
    }
}

proof fn lemma_cstring_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p,
    ensures
        parse_cstring(b, p + d, e0 + d) == shifted(parse_cstring(b0, p, e0), d),
        parse_cstring(b0, p, e0) matches Some((_, q)) ==> p < q <= e0,
{
    if p < e0 {
        assert(b[p + d] == b0[p]);
        let q = p + 1 + b0[p] as int;
        if q <= e0 {
            lemma_same_sub(b0, s0, e0, b, d, p + 1, q);
        }
    }
}

proof fn lemma_cstrings_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p <= e0,
    ensures
        parse_cstrings(b, p + d, e0 + d) == parse_cstrings(b0, p, e0),
    decreases e0 - p,
{
    lemma_cstring_local(b0, s0, e0, b, d, p);
    if p != e0 {
        if let Some((x, q)) = parse_cstring(b0, p, e0) {
            lemma_cstrings_local(b0, s0, e0, b, d, q);
        }
    }
}

proof fn lemma_kv_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p,
    ensures
        parse_kv(b, p + d, e0 + d) == shifted(parse_kv(b0, p, e0), d),
        parse_kv(b0, p, e0) matches Some((_, q)) ==> p < q <= e0,
{
    lemma_u16_in_local(b0, s0, e0, b, d, p);
    lemma_u16_in_local(b0, s0, e0, b, d, p + 2);
    if p + 4 <= e0 {
        let len = parse_u16(b0, p + 2).unwrap().0 as int;
        if p + 4 + len <= e0 {
            lemma_same_sub(b0, s0, e0, b, d, p + 4, p + 4 + len);
        }
    }
}

proof fn lemma_kvs_local(
    b0: Seq<u8>,
    s0: int,
    e0: int,
    b: Seq<u8>,
    d: int,
    p: int,
    inc: bool,
    prev: int,
)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p <= e0,
    ensures
        parse_kvs(b, p + d, e0 + d, inc, prev) == parse_kvs(b0, p, e0, inc, prev),
    decreases e0 - p,
{
    lemma_kv_local(b0, s0, e0, b, d, p);
    if p != e0 {
        if let Some((kv, q)) = parse_kv(b0, p, e0) {
            lemma_kvs_local(b0, s0, e0, b, d, q, inc, kv.0 as int);
        }
    }
}

proof fn lemma_plain_labels_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p,
    ensures
        parse_plain_labels(b, p + d, e0 + d) == shifted(parse_plain_labels(b0, p, e0), d),
        parse_plain_labels(b0, p, e0) matches Some((_, q)) ==> p < q <= e0,
    decreases e0 - p,
{
    if p < e0 {
        assert(b[p + d] == b0[p]);
        let c = b0[p];
        if c != 0 && c < 64 && p + 1 + c as int <= e0 {
            lemma_same_sub(b0, s0, e0, b, d, p + 1, p + 1 + c as int);
            lemma_plain_labels_local(b0, s0, e0, b, d, p + 1 + c as int);
        }
    }
}

proof fn lemma_plain_name_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, p: int)
    requires
        same(b0, s0, e0, b, d),
        s0 <= p,
    ensures
        parse_plain_name(b, p + d, e0 + d) == shifted(parse_plain_name(b0, p, e0), d),
        parse_plain_name(b0, p, e0) matches Some((_, q)) ==> p < q <= e0,
{
    lemma_plain_labels_local(b0, s0, e0, b, d, p);
}

proof fn lemma_svcb_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int)
    requires
        same(b0, s0, e0, b, d),
    ensures
        parse_svcb(b, s0 + d, e0 + d) == parse_svcb(b0, s0, e0),
{
    lemma_u16_in_local(b0, s0, e0, b, d, s0);
    if s0 + 2 <= e0 {
        lemma_plain_name_local(b0, s0, e0, b, d, s0 + 2);
        if let Some((_, q)) = parse_plain_name(b0, s0 + 2, e0) {
            lemma_kvs_local(b0, s0, e0, b, d, q, true, -1);
        }
    }
}

proof fn lemma_fixed_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, t: u16)
    requires
        same(b0, s0, e0, b, d),
        t == TYPE_A || t == TYPE_AAAA || t == TYPE_DS || t == TYPE_SSHFP || t == TYPE_DNSKEY || t
            == TYPE_TLSA || t == TYPE_URI || t == TYPE_HINFO || t == TYPE_TXT || t == TYPE_OPT,
    ensures
        parse_rdata(b, t, s0 + d, e0 + d) == parse_rdata(b0, t, s0, e0),
{
    lemma_same_sub(b0, s0, e0, b, d, s0, e0);
    if e0 - s0 >= 2 {
        assert(b[s0 + d] == b0[s0]);
        assert(b[(s0 + 1) + d] == b0[s0 + 1]);
        lemma_same_sub(b0, s0, e0, b, d, s0 + 2, e0);
    }
    if e0 - s0 >= 3 {
        assert(b[(s0 + 2) + d] == b0[s0 + 2]);
        lemma_same_sub(b0, s0, e0, b, d, s0 + 3, e0);
    }
    if e0 - s0 >= 4 {
        assert(b[(s0 + 3) + d] == b0[s0 + 3]);
        lemma_u16_same(b0, s0, e0, b, d, s0);
        lemma_u16_same(b0, s0, e0, b, d, s0 + 2);
        lemma_same_sub(b0, s0, e0, b, d, s0 + 4, e0);
    }
    let (s, e) = (s0 + d, e0 + d);
    if t == TYPE_A || t == TYPE_AAAA {
    } else if t == TYPE_DS {
        assert(parse_ds(b, s, e) == parse_ds(b0, s0, e0));
    } else if t == TYPE_SSHFP {
        assert(parse_sshfp(b, s, e) == parse_sshfp(b0, s0, e0));
    } else if t == TYPE_DNSKEY {
        assert(parse_dnskey(b, s, e) == parse_dnskey(b0, s0, e0));
    } else if t == TYPE_TLSA {
        assert(parse_tlsa(b, s, e) == parse_tlsa(b0, s0, e0));
    } else if t == TYPE_URI {
        assert(parse_uri(b, s, e) == parse_uri(b0, s0, e0));
    } else if t == TYPE_HINFO {
        lemma_cstring_local(b0, s0, e0, b, d, s0);
        if let Some((_, q)) = parse_cstring(b0, s0, e0) {
            lemma_cstring_local(b0, s0, e0, b, d, q);
        }
        assert(parse_hinfo(b, s, e) == parse_hinfo(b0, s0, e0));
    } else if t == TYPE_TXT {
        lemma_cstrings_local(b0, s0, e0, b, d, s0);
        assert(parse_txt(b, s, e) == parse_txt(b0, s0, e0));
    } else {
        lemma_kvs_local(b0, s0, e0, b, d, s0, false, -1);
    }
}

proof fn lemma_dnssec_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int, t: u16)
    requires
        same(b0, s0, e0, b, d),
        t == TYPE_RRSIG || t == TYPE_NSEC || t == TYPE_NSEC3 || t == TYPE_NSEC3PARAM,
    ensures
        parse_rdata(b, t, s0 + d, e0 + d) == parse_rdata(b0, t, s0, e0),
{
    if t == TYPE_NSEC {
        lemma_plain_name_local(b0, s0, e0, b, d, s0);
        if let Some((_, q)) = parse_plain_name(b0, s0, e0) {
            lemma_same_sub(b0, s0, e0, b, d, q, e0);
        }
    } else if e0 - s0 >= 4 {
        assert(b[s0 + d] == b0[s0]);
        assert(b[(s0 + 1) + d] == b0[s0 + 1]);
        assert(b[(s0 + 2) + d] == b0[s0 + 2]);
        assert(b[(s0 + 3) + d] == b0[s0 + 3]);
        lemma_u16_same(b0, s0, e0, b, d, s0);
        lemma_u16_same(b0, s0, e0, b, d, s0 + 2);
        if t == TYPE_RRSIG {
            if e0 - s0 >= 18 {
                lemma_u32_same(b0, s0, e0, b, d, s0 + 4);
                lemma_u32_same(b0, s0, e0, b, d, s0 + 8);
                lemma_u32_same(b0, s0, e0, b, d, s0 + 12);
                lemma_u16_same(b0, s0, e0, b, d, s0 + 16);
                lemma_plain_name_local(b0, s0, e0, b, d, s0 + 18);
                if let Some((_, q)) = parse_plain_name(b0, s0 + 18, e0) {
                    lemma_same_sub(b0, s0, e0, b, d, q, e0);
                }
            }
        } else {
            lemma_cstring_local(b0, s0, e0, b, d, s0 + 4);
            if let Some((_, q)) = parse_cstring(b0, s0 + 4, e0) {
                lemma_cstring_local(b0, s0, e0, b, d, q);
                if let Some((_, r)) = parse_cstring(b0, q, e0) {
                    lemma_same_sub(b0, s0, e0, b, d, r, e0);
                }
            }
        }
    }
}

proof fn lemma_caa_local(b0: Seq<u8>, s0: int, e0: int, b: Seq<u8>, d: int)
    requires
        same(b0, s0, e0, b, d),
    ensures
        parse_caa(b, s0 + d, e0 + d) == parse_caa(b0, s0, e0),
{
    if e0 - s0 >= 2 {
        assert(b[s0 + d] == b0[s0]);
        assert(b[(s0 + 1) + d] == b0[s0 + 1]);
        let len = b0[s0 + 1] as int;
        if 1 <= len <= 15 && s0 + 2 + len <= e0 {
            let s = s0 + d;
            assert((forall|i: int| s + 2 <= i < s + 2 + len ==> is_alnum(#[trigger] b[i])) == (
            forall|i: int| s0 + 2 <= i < s0 + 2 + len ==> is_alnum(#[trigger] b0[i]))) by {
                assert forall|i: int| s + 2 <= i < s + 2 + len implies b[i] == b0[i - d] by {
                    assert(b[(i - d) + d] == b0[i - d]);
                }
                assert forall|i: int| s0 + 2 <= i < s0 + 2 + len implies b0[i] == b[i + d] by {}
            }
            lemma_same_sub(b0, s0, e0, b, d, s0 + 2, s0 + 2 + len);
            lemma_same_sub(b0, s0, e0, b, d, s0 + 2 + len, e0);
        }
    }
}

/// RDATA of a type without compressed names decodes the same from its own
/// bytes wherever they are.
pub proof fn lemma_rdata_local(b0: Seq<u8>, t: u16, s0: int, e0: int, b: Seq<u8>, d: int)
    requires
        !compressible(t),
        same(b0, s0, e0, b, d),
    ensures
        parse_rdata(b, t, s0 + d, e0 + d) == parse_rdata(b0, t, s0, e0),
{
    if t == TYPE_A || t == TYPE_AAAA || t == TYPE_DS || t == TYPE_SSHFP || t == TYPE_DNSKEY || t
        == TYPE_TLSA || t == TYPE_URI || t == TYPE_HINFO || t == TYPE_TXT || t == TYPE_OPT {
        lemma_fixed_local(b0, s0, e0, b, d, t);
    } else if t == TYPE_RRSIG || t == TYPE_NSEC || t == TYPE_NSEC3 || t == TYPE_NSEC3PARAM {
        lemma_dnssec_local(b0, s0, e0, b, d, t);
    } else if t == TYPE_SVCB || t == TYPE_HTTPS {
        lemma_svcb_local(b0, s0, e0, b, d);
    } else if t == TYPE_CAA {
        lemma_caa_local(b0, s0, e0, b, d);
    } else {
        lemma_same_sub(b0, s0, e0, b, d, s0, e0);
    }
}

/// Where the RDATA of the record at `pos` lies in `b`.
pub open spec fn rdata_range(b: Seq<u8>, pos: int) -> (int, int) {
    let p1 = parse_name(b, pos).unwrap().1;
    (p1 + 10, p1 + 10 + parse_u16(b, p1 + 8).unwrap().0 as int)
}

/// **RDATA meaning theorem.** The canonical RDATA a parsed record stores
/// decodes, on its own, to exactly what the record's RDATA decodes to in
/// the original message (names inside it resolved against that message).
/// So decompressing names at parse time, and re-serializing, never changes
/// what a record says.
pub proof fn theorem_rdata_meaning(b: Seq<u8>, pos: int)
    ensures
        parse_record(b, pos) matches Some((r, _)) ==> parse_rdata(
            r.rdata,
            r.rtype,
            0,
            r.rdata.len() as int,
        ) == parse_rdata(b, r.rtype, rdata_range(b, pos).0, rdata_range(b, pos).1),
{
    if let Some((r, _)) = parse_record(b, pos) {
        let (s0, e0) = rdata_range(b, pos);
        if compressible(r.rtype) {
            lemma_canon_rdata_idem(b, r.rtype, s0, e0);
        } else {
            assert(r.rdata == b.subrange(s0, e0));
            lemma_at_whole(r.rdata);
            lemma_same_at(b, s0, e0, r.rdata, -s0);
            lemma_rdata_local(b, r.rtype, s0, e0, r.rdata, -s0);
        }
    }
}

} // verus!
