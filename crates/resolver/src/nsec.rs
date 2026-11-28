//! Authenticated denial of existence: NSEC (RFC 4034 §4, RFC 4035 §5.4)
//! and NSEC3 (RFC 5155 §8). Every check here is proven to establish the
//! `dspec` predicate it is named after; the searches at the end, the
//! proofs `dspec::proves_*` ask for.
use crate::canon::*;
use crate::dspec::*;
use crate::name::*;
use crate::rr::*;
use crate::sha1::sha1_x;
use crate::sigcheck::u16_at_x;
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Canonical name order
// ---------------------------------------------------------------------------

/// `labels_of(n, 0)`.
pub fn labels_x(n: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures
        views(r@) == labels_of(n@, 0),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut p: usize = 0;
    proof {
        assert(views(out@) =~= Seq::<Seq<u8>>::empty());
        assert(labels_of(n@, 0) =~= views(out@) + labels_of(n@, 0));
    }
    while p < n.len()
        invariant
            labels_of(n@, 0) == views(out@) + labels_of(n@, p as int),
        decreases n@.len() - p,
    {
        let l = n[p] as usize;
        if l == 0 || l + 1 >= n.len() - p {
            proof {
                assert(labels_of(n@, p as int) =~= Seq::<Seq<u8>>::empty());
                assert(views(out@) + labels_of(n@, p as int) =~= views(out@));
            }
            return out;
        }
        let mut lab: Vec<u8> = Vec::new();
        push_lower(&mut lab, slice_subrange(n, p + 1, p + 1 + l));
        let ghost o = views(out@);
        out.push(lab);
        proof {
            assert(lab@ =~= lower_seq(n@.subrange(p + 1, p + 1 + l)));
            assert(views(out@) =~= o.push(lab@));
            assert(labels_of(n@, p as int) == seq![lab@] + labels_of(n@, p + 1 + l));
            assert(o + labels_of(n@, p as int) =~= views(out@) + labels_of(n@, p + 1 + l));
        }
        p = p + 1 + l;
    }
    proof {
        assert(labels_of(n@, p as int) =~= Seq::<Seq<u8>>::empty());
        assert(views(out@) + labels_of(n@, p as int) =~= views(out@));
    }
    out
}

pub fn reversed(v: Vec<Vec<u8>>) -> (r: Vec<Vec<u8>>)
    ensures
        views(r@) == views(v@).reverse(),
{
    let mut out: Vec<Vec<u8>> = Vec::with_capacity(v.len());
    let mut v = v;
    let ghost orig = views(v@);
    let ghost n = v@.len();
    while v.len() > 0
        invariant
            v@.len() + out@.len() == n,
            orig.len() == n,
            views(v@) == orig.subrange(0, v@.len() as int),
            views(out@) == orig.reverse().subrange(0, out@.len() as int),
        decreases v@.len(),
    {
        let ghost k = out@.len();
        proof {
            assert(views(v@)[v@.len() - 1] == v@[v@.len() - 1]@);
        }
        let x = v.pop().unwrap();
        proof {
            assert(x@ == orig[(n - k - 1) as int]);
        }
        out.push(x);
        proof {
            assert(views(v@) =~= orig.subrange(0, v@.len() as int));
            assert(views(out@) =~= orig.reverse().subrange(0, out@.len() as int));
        }
    }
    proof {
        assert(orig.reverse().subrange(0, n as int) =~= orig.reverse());
    }
    out
}

pub proof fn lemma_lab_unique(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>, k: int)
    requires
        0 <= k <= x.len(),
        k <= y.len(),
        x.subrange(0, k) == y.subrange(0, k),
        k == x.len() || k == y.len() || x[k] != y[k],
    ensures
        lab_lt(x, y) <==> ((k == x.len() && k < y.len()) || (k < x.len() && k < y.len() && bytes_lt(x[k], y[k]))),
{
    let rhs = (k == x.len() && k < y.len()) || (k < x.len() && k < y.len() && bytes_lt(x[k], y[k]));
    if lab_lt(x, y) {
        let j = choose|j: int|
            0 <= j <= x.len() && j <= y.len() && x.subrange(0, j) == y.subrange(0, j) && ((j == x.len() && j
                < y.len()) || (j < x.len() && j < y.len() && bytes_lt(x[j], y[j])));
        if j < k {
            assert(x.subrange(0, k)[j] == y.subrange(0, k)[j]);
            assert(x.subrange(0, k)[j] == x[j]);
            assert(y.subrange(0, k)[j] == y[j]);
            lemma_lt_irrefl(x[j]);
            assert(false);
        } else if j > k {
            assert(x.subrange(0, j)[k] == y.subrange(0, j)[k]);
            assert(x.subrange(0, j)[k] == x[k]);
            assert(y.subrange(0, j)[k] == y[k]);
            assert(false);
        }
        assert(rhs);
    }
    if rhs {
        assert(0 <= k <= x.len() && k <= y.len() && x.subrange(0, k) == y.subrange(0, k) && ((k == x.len() && k
            < y.len()) || (k < x.len() && k < y.len() && bytes_lt(x[k], y[k]))));
    }
}

/// `lab_lt(x, y)`.
pub fn lab_lt_x(x: &Vec<Vec<u8>>, y: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == lab_lt(views(x@), views(y@)),
{
    let ghost (a, b) = (views(x@), views(y@));
    let n = if x.len() < y.len() { x.len() } else { y.len() };
    let mut i: usize = 0;
    while i < n
        invariant
            a == views(x@),
            b == views(y@),
            n <= x@.len(),
            n <= y@.len(),
            n == x@.len() || n == y@.len(),
            i <= n,
            a.subrange(0, i as int) == b.subrange(0, i as int),
        decreases n - i,
    {
        let c = bytes_cmp(&x[i], &y[i]);
        if c != 0 {
            proof {
                assert(a[i as int] == x@[i as int]@);
                assert(b[i as int] == y@[i as int]@);
                lemma_lab_unique(a, b, i as int);
            }
            return c == -1;
        }
        proof {
            assert(a[i as int] == b[i as int]);
            let ghost k1 = i + 1;
            let ghost (sa, sb) = (a.subrange(0, k1), b.subrange(0, k1));
            assert forall|j: int| 0 <= j < k1 implies #[trigger] sa[j] == sb[j] by {
                if j < i {
                    assert(a.subrange(0, i as int)[j] == b.subrange(0, i as int)[j]);
                }
            }
            assert(sa =~= sb);
        }
        i = i + 1;
    }
    proof {
        if n == x@.len() && n == y@.len() {
        } else if n == x@.len() {
        } else {
        }
        lemma_lab_unique(a, b, n as int);
    }
    x.len() < y.len()
}

/// `name_lt(a, b)`.
pub fn name_lt_x(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == name_lt(a@, b@),
{
    let x = reversed(labels_x(a));
    let y = reversed(labels_x(b));
    lab_lt_x(&x, &y)
}

/// `common(a, b)`.
pub fn common_x(a: &[u8], b: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == common(a@, b@),
{
    let x = reversed(labels_x(a));
    let y = reversed(labels_x(b));
    let ghost (xv, yv) = (views(x@), views(y@));
    let mut k: usize = 0;
    while k < x.len() && k < y.len() && bytes_eq(&x[k], &y[k])
        invariant
            xv == views(x@),
            yv == views(y@),
            k <= x@.len(),
            common_k(xv, yv, 0) == common_k(xv, yv, k as nat),
        decreases x@.len() - k,
    {
        proof {
            assert(xv[k as int] == x@[k as int]@);
            assert(yv[k as int] == y@[k as int]@);
        }
        k = k + 1;
    }
    proof {
        if k < x@.len() && k < y@.len() {
            assert(xv[k as int] == x@[k as int]@);
            assert(yv[k as int] == y@[k as int]@);
        }
    }
    let s = suffix_x(a, k);
    to_vec(slice_subrange(a, s, a.len()))
}

// ---------------------------------------------------------------------------
// Type bit maps
// ---------------------------------------------------------------------------

fn pow2_8_x(k: u16) -> (r: u8)
    requires
        k < 8,
    ensures
        r as int == pow2_8(k as int),
        r > 0,
{
    if k == 0 { 1 } else if k == 1 { 2 } else if k == 2 { 4 } else if k == 3 { 8 } else if k == 4 { 16 } else if k == 5 { 32 } else if k == 6 { 64 } else { 128 }
}

/// `has_type_from(bm, off, t)`.
pub fn has_type_x(bm: &[u8], off: usize, t: u16) -> (r: bool)
    ensures
        r == has_type_from(bm@, off as int, t),
{
    let mut p = off;
    while p <= bm.len() && bm.len() - p >= 2
        invariant
            off <= p,
            has_type_from(bm@, off as int, t) == has_type_from(bm@, p as int, t),
        decreases bm@.len() - p,
    {
        let win = bm[p];
        let l = bm[p + 1] as usize;
        if l == 0 || l > 32 || l > bm.len() - p - 2 {
            return false;
        }
        if win as u16 == t / 256 {
            let byte = ((t % 256) / 8) as usize;
            if byte >= l {
                return false;
            }
            let d = pow2_8_x(7 - t % 8);
            return (bm[p + 2 + byte] / d) % 2 == 1;
        }
        p = p + 2 + l;
    }
    false
}

// ---------------------------------------------------------------------------
// NSEC
// ---------------------------------------------------------------------------

/// The length of an NSEC's next name, if it is an NSEC.
pub fn nsec_next_len(r: &Rr) -> (l: Option<usize>)
    ensures
        l matches Some(x) ==> nsec_wf(r@) && name_len(r@.rdata, 0) == Some(x as int) && x <= r@.rdata.len(),
{
    if r.rtype != TYPE_NSEC {
        return None;
    }
    name_len_x(&r.rdata, 0)
}

pub fn nsec_has_x(r: &Rr, l: usize, t: u16) -> (b: bool)
    requires
        name_len(r@.rdata, 0) == Some(l as int),
    ensures
        b == nsec_has(r@, t),
{
    has_type_x(&r.rdata, l, t)
}

/// `nsec_covers(r, n, zone)`, or false.
pub fn nsec_covers_x(r: &Rr, n: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> nsec_covers(r@, n@, zone@),
{
    let l = match nsec_next_len(r) {
        Some(l) => l,
        None => {
            return false;
        },
    };
    let next = slice_subrange(r.rdata.as_slice(), 0, l);
    if !is_sub_exec(n, zone) || !name_lt_x(&r.name, n) {
        return false;
    }
    if !(name_lt_x(n, next) || !name_lt_x(&r.name, next)) {
        return false;
    }
    if is_sub_exec(n, &r.name) {
        if nsec_has_x(r, l, TYPE_DNAME) || (nsec_has_x(r, l, TYPE_NS) && !nsec_has_x(r, l, TYPE_SOA_)) {
            return false;
        }
    }
    true
}

/// `nsec_nodata(r, n, t)`, or false.
pub fn nsec_nodata_x(r: &Rr, n: &[u8], t: u16) -> (b: bool)
    ensures
        b ==> nsec_nodata(r@, n@, t),
{
    let l = match nsec_next_len(r) {
        Some(l) => l,
        None => {
            return false;
        },
    };
    if !eq_ci_exec(&r.name, n) || nsec_has_x(r, l, t) || nsec_has_x(r, l, TYPE_CNAME) {
        return false;
    }
    let soa = nsec_has_x(r, l, TYPE_SOA_);
    if t == TYPE_DS {
        !soa
    } else {
        !(nsec_has_x(r, l, TYPE_NS) && !soa)
    }
}

/// `nsec_ce(r, n)`.
pub fn nsec_ce_x(r: &Rr, n: &[u8]) -> (c: Vec<u8>)
    requires
        nsec_wf(r@),
    ensures
        c@ == nsec_ce(r@, n@),
{
    let l = name_len_x(&r.rdata, 0).unwrap();
    let a = common_x(n, &r.name);
    let b = common_x(n, slice_subrange(r.rdata.as_slice(), 0, l));
    if label_count_x(&a) >= label_count_x(&b) {
        a
    } else {
        b
    }
}

pub fn wild_of_x(n: &[u8]) -> (w: Vec<u8>)
    ensures
        w@ == wild_of(n@),
{
    let mut w: Vec<u8> = Vec::new();
    w.push(1);
    w.push(42);
    push_bytes(&mut w, n);
    proof {
        assert(w@ =~= wild_of(n@));
    }
    w
}

// ---------------------------------------------------------------------------
// NSEC3
// ---------------------------------------------------------------------------

pub fn n3_wf_x(r: &Rr) -> (b: bool)
    ensures
        b == n3_wf(r@),
{
    let d = &r.rdata;
    if r.rtype != TYPE_NSEC3 || d.len() < 5 || d[0] != 1 || u16_at_x(d, 2) > MAX_NSEC3_ITERATIONS {
        return false;
    }
    let s = d[4] as usize;
    if 5 + s + 1 > d.len() {
        return false;
    }
    d[5 + s] == 20 && 5 + s + 21 <= d.len()
}

fn pow32_x(k: usize) -> (r: u64)
    requires
        k < 8,
    ensures
        r as int == pow32(k as int),
        r > 0,
{
    proof {
        reveal_with_fuel(pow32, 8);
    }
    if k == 0 { 1 } else if k == 1 { 32 } else if k == 2 { 1024 } else if k == 3 { 32768 } else if k == 4 { 1048576 } else if k == 5 { 33554432 } else if k == 6 { 1073741824 } else { 34359738368 }
}

/// `b32hex(h)`.
pub fn b32hex_x(h: &[u8]) -> (r: Vec<u8>)
    requires
        h@.len() == 20,
    ensures
        r@ == b32hex(h@),
{
    let mut out: Vec<u8> = Vec::with_capacity(32);
    let mut i: usize = 0;
    while i < 32
        invariant
            h@.len() == 20,
            i <= 32,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == b32hex(h@)[j],
        decreases 32 - i,
    {
        let c = i / 8;
        let v: u64 = (h[5 * c] as u64) * 0x1_0000_0000 + (h[5 * c + 1] as u64) * 0x100_0000 + (h[5 * c + 2] as u64)
            * 0x1_0000 + (h[5 * c + 3] as u64) * 0x100 + h[5 * c + 4] as u64;
        let d = (v / pow32_x(7 - i % 8)) % 32;
        let ch: u8 = if d < 10 { 48 + d as u8 } else { 87 + d as u8 };
        proof {
            assert(v as int == chunk40(h@, c as int));
        }
        out.push(ch);
        i = i + 1;
    }
    proof {
        assert(out@ =~= b32hex(h@));
    }
    out
}

/// `ih(salt, x, k)`.
pub fn ih_x(salt: &[u8], x: &[u8], k: u16) -> (r: Vec<u8>)
    requires
        salt@.len() < 256,
        x@.len() < 0x0100_0000,
    ensures
        r@ == ih(salt@, x@, k as nat),
        r@.len() == 20,
{
    let mut d: Vec<u8> = Vec::new();
    push_bytes(&mut d, x);
    push_bytes(&mut d, salt);
    let h0 = sha1_x(&d);
    let mut h: Vec<u8> = to_vec(h0.as_slice());
    let mut i: u16 = 0;
    proof {
        assert(d@ == x@ + salt@);
    }
    while i < k
        invariant
            salt@.len() < 256,
            i <= k,
            h@ == ih(salt@, x@, i as nat),
            h@.len() == 20,
        decreases k - i,
    {
        let mut e: Vec<u8> = Vec::new();
        push_bytes(&mut e, &h);
        push_bytes(&mut e, salt);
        let hn = sha1_x(&e);
        h = to_vec(hn.as_slice());
        i = i + 1;
        proof {
            assert(e@ == ih(salt@, x@, (i - 1) as nat) + salt@);
        }
    }
    h
}

/// `n3_hash(r, n)`, for a well-formed NSEC3.
pub fn n3_hash_x(r: &Rr, n: &[u8]) -> (h: Option<Vec<u8>>)
    requires
        n3_wf(r@),
    ensures
        h matches Some(v) ==> v@ == n3_hash(r@, n@) && v@.len() == 20,
{
    if n.len() >= 0x0100_0000 {
        return None;
    }
    let d = &r.rdata;
    let s = d[4] as usize;
    let salt = slice_subrange(d.as_slice(), 5, 5 + s);
    let mut low: Vec<u8> = Vec::new();
    push_lower(&mut low, n);
    proof {
        assert(low@ =~= lower_seq(n@));
    }
    Some(ih_x(salt, &low, u16_at_x(d, 2)))
}

/// `n3_label(r, zone)`.
pub fn n3_label_x(r: &Rr, zone: &[u8]) -> (l: Option<Vec<u8>>)
    ensures
        l matches Some(v) ==> n3_label(r@, zone@) == Some(v@),
        l is None ==> n3_label(r@, zone@) is None,
{
    let nm = &r.name;
    if nm.len() >= 33 && nm[0] == 32 && eq_ci_exec(slice_subrange(nm.as_slice(), 33, nm.len()), zone) {
        let mut v: Vec<u8> = Vec::new();
        push_lower(&mut v, slice_subrange(nm.as_slice(), 1, 33));
        proof {
            assert(v@ =~= lower_seq(nm@.subrange(1, 33)));
        }
        Some(v)
    } else {
        None
    }
}

/// `n3_matches(r, n, zone)`, or false.
pub fn n3_matches_x(r: &Rr, n: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> n3_matches(r@, n@, zone@),
{
    if !n3_wf_x(r) || !is_sub_exec(n, zone) {
        return false;
    }
    let own = match n3_label_x(r, zone) {
        Some(l) => l,
        None => {
            return false;
        },
    };
    let h = match n3_hash_x(r, n) {
        Some(h) => h,
        None => {
            return false;
        },
    };
    let e = b32hex_x(&h);
    bytes_eq(&own, &e)
}

/// `n3_covers(r, n, zone)`, or false.
pub fn n3_covers_x(r: &Rr, n: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> n3_covers(r@, n@, zone@),
{
    if !n3_wf_x(r) || !is_sub_exec(n, zone) {
        return false;
    }
    let own = match n3_label_x(r, zone) {
        Some(l) => l,
        None => {
            return false;
        },
    };
    let h = match n3_hash_x(r, n) {
        Some(h) => h,
        None => {
            return false;
        },
    };
    let e = b32hex_x(&h);
    let d = &r.rdata;
    let s = 5 + d[4] as usize + 1;
    let nx = b32hex_x(slice_subrange(d.as_slice(), s, s + 20));
    let a = bytes_cmp(&own, &e) == -1;
    let b = bytes_cmp(&e, &nx) == -1;
    if bytes_cmp(&own, &nx) == -1 {
        a && b
    } else {
        a || b
    }
}

pub fn n3_has_x(r: &Rr, t: u16) -> (b: bool)
    requires
        n3_wf(r@),
    ensures
        b == n3_has(r@, t),
{
    has_type_x(&r.rdata, 5 + r.rdata[4] as usize + 21, t)
}

/// `n3_nodata(r, n, t, zone)`, or false.
pub fn n3_nodata_x(r: &Rr, n: &[u8], t: u16, zone: &[u8]) -> (b: bool)
    ensures
        b ==> n3_nodata(r@, n@, t, zone@),
{
    if !n3_matches_x(r, n, zone) || n3_has_x(r, t) || n3_has_x(r, TYPE_CNAME) {
        return false;
    }
    let soa = n3_has_x(r, TYPE_SOA_);
    if t == TYPE_DS {
        !soa
    } else {
        !(n3_has_x(r, TYPE_NS) && !soa)
    }
}

/// The next closer name of `n` for an ancestor with `k` labels, as an
/// offset into `n`: `next_closer(n, ce)` when `ce` has `k` labels.
pub fn next_closer_x(n: &[u8], k: usize) -> (o: usize)
    requires
        k < 0xffff,
    ensures
        o <= n@.len(),
        n@.subrange(o as int, n@.len() as int) == suffix(n@, (k + 1) as nat),
{
    suffix_x(n, k + 1)
}

/// The NSEC3 closest encloser proof for `n` with ancestor `ce`, or false.
pub fn n3_ce_x(ns: &Vec<Rr>, n: &[u8], ce: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> n3_ce(rrs(ns@), n@, ce@, zone@),
{
    if !is_sub_exec(n, ce) || !is_sub_exec(ce, zone) {
        return false;
    }
    let k = label_count_x(ce);
    if k >= label_count_x(n) || k >= 0xffff {
        return false;
    }
    let s = suffix_x(n, k);
    if !bytes_eq(slice_subrange(n, s, n.len()), ce) {
        return false;
    }
    let o = next_closer_x(n, k);
    let nc = slice_subrange(n, o, n.len());
    let ghost v = rrs(ns@);
    let mut found_m = false;
    let mut found_c = false;
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            v == rrs(ns@),
            nc@ == next_closer(n@, ce@),
            found_m ==> exists|i: int| 0 <= i < v.len() && n3_matches(#[trigger] v[i], ce@, zone@) && !(n3_has(v[i], TYPE_DNAME))
                && !(n3_has(v[i], TYPE_NS) && !n3_has(v[i], TYPE_SOA_)),
            found_c ==> exists|i: int| 0 <= i < v.len() && n3_covers(#[trigger] v[i], next_closer(n@, ce@), zone@),
        decreases ns@.len() - i,
    {
        let r = &ns[i];
        proof {
            assert(v[i as int] == r@);
        }
        if !found_m && n3_matches_x(r, ce, zone) && !n3_has_x(r, TYPE_DNAME) && !(n3_has_x(r, TYPE_NS) && !n3_has_x(r, TYPE_SOA_)) {
            found_m = true;
        }
        if !found_c && n3_covers_x(r, nc, zone) {
            found_c = true;
        }
        i = i + 1;
    }
    found_m && found_c
}

// ---------------------------------------------------------------------------
// The proofs
// ---------------------------------------------------------------------------

/// Some record of `ns` covers `n` (NSEC).
fn find_nsec_cover(ns: &Vec<Rr>, n: &[u8], zone: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < ns@.len() && nsec_covers(rrs(ns@)[i as int], n@, zone@),
{
    let mut i: usize = 0;
    while i < ns.len()
        decreases ns@.len() - i,
    {
        if nsec_covers_x(&ns[i], n, zone) {
            proof {
                assert(rrs(ns@)[i as int] == ns@[i as int]@);
            }
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// Some record of `ns` covers `n` (NSEC3).
fn find_n3_cover(ns: &Vec<Rr>, n: &[u8], zone: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < ns@.len() && n3_covers(rrs(ns@)[i as int], n@, zone@),
{
    let mut i: usize = 0;
    while i < ns.len()
        decreases ns@.len() - i,
    {
        if n3_covers_x(&ns[i], n, zone) {
            proof {
                assert(rrs(ns@)[i as int] == ns@[i as int]@);
            }
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// The NSEC3 closest encloser of `n` in `zone`, if `ns` proves one: the
/// deepest ancestor of `n` for which `n3_ce` holds.
fn find_n3_ce(ns: &Vec<Rr>, n: &[u8], zone: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(ce) ==> n3_ce(rrs(ns@), n@, ce@, zone@),
{
    let lc = label_count_x(n);
    let mut k = lc;
    while k > 0
        decreases k,
    {
        k = k - 1;
        let s = suffix_x(n, k);
        let ce = slice_subrange(n, s, n.len());
        if !is_sub_exec(ce, zone) {
            return None;
        }
        if n3_ce_x(ns, n, ce, zone) {
            return Some(to_vec(ce));
        }
    }
    None
}

/// `ns` proves that `n` does not exist in `zone`.
pub fn find_nxdomain(ns: &Vec<Rr>, n: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> proves_nxdomain(rrs(ns@), n@, zone@),
{
    let ghost v = rrs(ns@);
    if let Some(i) = find_nsec_cover(ns, n, zone) {
        let ce = nsec_ce_x(&ns[i], n);
        proof {
            assert(v[i as int] == ns@[i as int]@);
        }
        let w = wild_of_x(&ce);
        if let Some(j) = find_nsec_cover(ns, &w, zone) {
            proof {
                assert(nsec_covers(v[i as int], n@, zone@) && nsec_covers(v[j as int], wild_of(nsec_ce(v[i as int], n@)), zone@));
            }
            return true;
        }
    }
    if let Some(ce) = find_n3_ce(ns, n, zone) {
        let w = wild_of_x(&ce);
        if let Some(j) = find_n3_cover(ns, &w, zone) {
            proof {
                assert(n3_ce(v, n@, ce@, zone@));
                assert(n3_covers(v[j as int], wild_of(ce@), zone@));
            }
            return true;
        }
    }
    false
}

/// An NSEC3 with opt-out covers the next closer name of `n` from `ce`.
fn find_optout(ns: &Vec<Rr>, n: &[u8], ce: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> optout_covered(rrs(ns@), n@, ce@, zone@),
{
    let ghost v = rrs(ns@);
    let k = label_count_x(ce);
    if k >= 0xffff {
        return false;
    }
    let o = next_closer_x(n, k);
    let nc = slice_subrange(n, o, n.len());
    let mut j: usize = 0;
    while j < ns.len()
        invariant
            v == rrs(ns@),
            k == label_count(ce@),
            nc@ == next_closer(n@, ce@),
        decreases ns@.len() - j,
    {
        proof {
            assert(v[j as int] == ns@[j as int]@);
        }
        if n3_covers_x(&ns[j], nc, zone) && ns[j].rdata[1] % 2 == 1 {
            return true;
        }
        j = j + 1;
    }
    false
}

/// An NSEC at `n` or NSEC3 for `n` says it has no type `t`.
fn find_nodata_at(ns: &Vec<Rr>, n: &[u8], t: u16, zone: &[u8]) -> (b: u8)
    ensures
        b <= 2,
        b == 1 ==> exists|i: int| 0 <= i < ns@.len() && nsec_nodata(#[trigger] rrs(ns@)[i], n@, t),
        b == 2 ==> exists|i: int| 0 <= i < ns@.len() && n3_nodata(#[trigger] rrs(ns@)[i], n@, t, zone@),
{
    let ghost v = rrs(ns@);
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            v == rrs(ns@),
        decreases ns@.len() - i,
    {
        proof {
            assert(v[i as int] == ns@[i as int]@);
        }
        if nsec_nodata_x(&ns[i], n, t) {
            return 1;
        }
        if n3_nodata_x(&ns[i], n, t, zone) {
            return 2;
        }
        i = i + 1;
    }
    0
}

/// `ns` proves that `n` has no records of type `t` in `zone`.
pub fn find_nodata(ns: &Vec<Rr>, n: &[u8], t: u16, zone: &[u8]) -> (b: bool)
    ensures
        b ==> proves_nodata(rrs(ns@), n@, t, zone@),
{
    let ghost v = rrs(ns@);
    if find_nodata_at(ns, n, t, zone) != 0 {
        return true;
    }
    // An empty non-terminal; or a wildcard that exists without the type.
    if let Some(i) = find_nsec_cover(ns, n, zone) {
        let ce = nsec_ce_x(&ns[i], n);
        proof {
            assert(v[i as int] == ns@[i as int]@);
        }
        if let Some(l) = nsec_next_len(&ns[i]) {
            let next = slice_subrange(ns[i].rdata.as_slice(), 0, l);
            if is_sub_exec(next, n) && !eq_ci_exec(next, n) {
                proof {
                    assert(nsec_ent(v[i as int], n@, zone@));
                }
                return true;
            }
        }
        let w = wild_of_x(&ce);
        if find_nodata_at(ns, &w, t, zone) == 1 {
            proof {
                let j = choose|j: int| 0 <= j < ns@.len() && nsec_nodata(#[trigger] v[j], w@, t);
                assert(nsec_covers(v[i as int], n@, zone@) && nsec_nodata(v[j], wild_of(nsec_ce(v[i as int], n@)), t));
            }
            return true;
        }
    }
    if let Some(ce) = find_n3_ce(ns, n, zone) {
        if t == TYPE_DS && find_optout(ns, n, &ce, zone) {
            return true;
        }
        let w = wild_of_x(&ce);
        if find_nodata_at(ns, &w, t, zone) == 2 {
            proof {
                assert(n3_ce(v, n@, ce@, zone@));
            }
            return true;
        }
    }
    false
}

/// `ns` proves the wildcard expansion of `n` from closest encloser `ce`.
pub fn find_expansion(ns: &Vec<Rr>, n: &[u8], ce: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> proves_expansion(rrs(ns@), n@, ce@, zone@),
{
    let ghost v = rrs(ns@);
    if let Some(i) = find_nsec_cover(ns, n, zone) {
        return true;
    }
    let k = label_count_x(ce);
    if k >= label_count_x(n) || k >= 0xffff {
        return false;
    }
    let o = next_closer_x(n, k);
    match find_n3_cover(ns, slice_subrange(n, o, n.len()), zone) {
        Some(i) => true,
        None => false,
    }
}

/// `ns` proves that `c` is a delegation of `zone` without DS.
pub fn find_unsigned(ns: &Vec<Rr>, c: &[u8], zone: &[u8]) -> (b: bool)
    ensures
        b ==> proves_unsigned(rrs(ns@), c@, zone@),
{
    let ghost v = rrs(ns@);
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            v == rrs(ns@),
        decreases ns@.len() - i,
    {
        proof {
            assert(v[i as int] == ns@[i as int]@);
        }
        let r = &ns[i];
        if nsec_nodata_x(r, c, TYPE_DS) {
            match nsec_next_len(r) {
                Some(l) => {
                    if nsec_has_x(r, l, TYPE_NS) {
                        return true;
                    }
                },
                None => {},
            }
        }
        if n3_nodata_x(r, c, TYPE_DS, zone) && n3_has_x(r, TYPE_NS) {
            return true;
        }
        i = i + 1;
    }
    if let Some(ce) = find_n3_ce(ns, c, zone) {
        if find_optout(ns, c, &ce, zone) {
            return true;
        }
    }
    false
}

} // verus!
