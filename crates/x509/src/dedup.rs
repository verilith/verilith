//! Pass 2 of the duplicate-extension check, with `alloc`: the OIDs are
//! collected into a vector, merge-sorted, and checked for two equal
//! neighbours. `check_extensions` runs it only when a list has more than
//! `MAX_OTHER_EXTENSIONS` OIDs outside the low id-ce arcs, which no issued
//! certificate has; a crafted one would otherwise cost time quadratic in
//! its number of extensions.
use crate::der::*;
#[cfg(verus_only)]
use crate::ext::*;
use crate::spec::*;
#[cfg(verus_only)]
use crate::x509::*;
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The order: lexicographic, a proper prefix first
// ---------------------------------------------------------------------------

/// `a` and `b` agree on their first `k` octets.
pub open spec fn agree(a: Seq<u8>, b: Seq<u8>, k: int) -> bool {
    &&& 0 <= k <= a.len()
    &&& k <= b.len()
    &&& forall|j: int| 0 <= j < k ==> a[j] == b[j]
}

/// `a` comes before `b`, and they first differ at `k`.
pub open spec fn lt_at(a: Seq<u8>, b: Seq<u8>, k: int) -> bool {
    &&& agree(a, b, k)
    &&& k < b.len()
    &&& (k == a.len() || a[k] < b[k])
}

pub open spec fn lex_lt(a: Seq<u8>, b: Seq<u8>) -> bool {
    exists|k: int| lt_at(a, b, k)
}

pub open spec fn lex_le(a: Seq<u8>, b: Seq<u8>) -> bool {
    lex_lt(a, b) || a == b
}

pub proof fn lemma_lt_irrefl(a: Seq<u8>)
    ensures
        !lex_lt(a, a),
{
    if lex_lt(a, a) {
        let k = choose|k: int| lt_at(a, a, k);
        assert(k < a.len());
    }
}

pub proof fn lemma_lt_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        lex_lt(a, b),
        lex_lt(b, c),
    ensures
        lex_lt(a, c),
{
    let k1 = choose|k: int| lt_at(a, b, k);
    let k2 = choose|k: int| lt_at(b, c, k);
    let k = if k1 <= k2 { k1 } else { k2 };
    assert forall|j: int| 0 <= j < k implies a[j] == c[j] by {
        assert(a[j] == b[j]);
        assert(b[j] == c[j]);
    }
    if k1 < k2 {
        assert(b[k1] == c[k1]);
    } else if k2 < k1 {
        assert(a[k2] == b[k2]);
    }
    assert(lt_at(a, c, k));
}

/// Compares `a` with `b`: -1 if it comes first, 0 if equal, 1 if after.
/// Its steps are the octets the two have in common.
pub fn cmp_m(a: &[u8], b: &[u8]) -> (r: (i8, Ghost<nat>))
    ensures
        -1 <= r.0 <= 1,
        r.0 == -1 ==> lex_lt(a@, b@),
        r.0 == 0 ==> a@ == b@,
        r.0 == 1 ==> lex_lt(b@, a@),
        r.1@ <= a@.len(),
        r.1@ <= b@.len(),
{
    let n = if a.len() < b.len() {
        a.len()
    } else {
        b.len()
    };
    let mut i: usize = 0;
    while i < n
        invariant
            n <= a@.len(),
            n <= b@.len(),
            n == a@.len() || n == b@.len(),
            i <= n,
            agree(a@, b@, i as int),
        decreases n - i,
    {
        let x = at(a, i);
        let y = at(b, i);
        if x != y {
            if x < y {
                proof {
                    assert(lt_at(a@, b@, i as int));
                }
                return (-1, Ghost(i as nat));
            } else {
                proof {
                    assert(lt_at(b@, a@, i as int));
                }
                return (1, Ghost(i as nat));
            }
        }
        i = i + 1;
    }
    if a.len() < b.len() {
        proof {
            assert(lt_at(a@, b@, i as int));
        }
        (-1, Ghost(i as nat))
    } else if b.len() < a.len() {
        proof {
            assert(lt_at(b@, a@, i as int));
        }
        (1, Ghost(i as nat))
    } else {
        proof {
            assert(a@ =~= b@);
        }
        (0, Ghost(i as nat))
    }
}

// ---------------------------------------------------------------------------
// Sequences of OIDs
// ---------------------------------------------------------------------------

pub open spec fn views(s: Seq<&[u8]>) -> Seq<Seq<u8>> {
    s.map_values(|x: &[u8]| x@)
}

/// The octets of `s`, plus one for each: what sorting it costs per level.
pub open spec fn wt(s: Seq<Seq<u8>>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        wt(s.drop_last()) + s.last().len() + 1
    }
}

pub proof fn lemma_wt_push(s: Seq<Seq<u8>>, x: Seq<u8>)
    ensures
        wt(s.push(x)) == wt(s) + x.len() + 1,
{
    assert(s.push(x).drop_last() =~= s);
}

pub proof fn lemma_wt_concat(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures
        wt(a + b) == wt(a) + wt(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_wt_concat(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

pub proof fn lemma_wt_prefix(s: Seq<Seq<u8>>, m: int)
    requires
        0 <= m <= s.len(),
    ensures
        wt(s.take(m)) <= wt(s),
{
    assert(s =~= s.take(m) + s.skip(m));
    lemma_wt_concat(s.take(m), s.skip(m));
}

pub proof fn lemma_wt_len(s: Seq<Seq<u8>>)
    ensures
        s.len() <= wt(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_wt_len(s.drop_last());
    }
}

pub open spec fn sorted(s: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < s.len() - 1 ==> lex_le(#[trigger] s[k], s[k + 1])
}

proof fn lemma_sorted_push(s: Seq<Seq<u8>>, x: Seq<u8>)
    requires
        sorted(s),
        s.len() > 0 ==> lex_le(s.last(), x),
    ensures
        sorted(s.push(x)),
{
    let t = s.push(x);
    assert forall|k: int| 0 <= k < t.len() - 1 implies lex_le(#[trigger] t[k], t[k + 1]) by {
        assert(t[k] == s[k]);
        if k + 1 < s.len() {
            assert(t[k + 1] == s[k + 1]);
        }
    }
}

/// Each neighbour after the one before: then every element after every
/// earlier one.
proof fn lemma_strict_pq(s: Seq<Seq<u8>>, p: int, q: int)
    requires
        forall|k: int| 0 <= k < s.len() - 1 ==> lex_lt(#[trigger] s[k], s[k + 1]),
        0 <= p < q < s.len(),
    ensures
        lex_lt(s[p], s[q]),
    decreases q - p,
{
    if q > p + 1 {
        lemma_strict_pq(s, p, q - 1);
        assert(lex_lt(s[q - 1], s[q]));
        lemma_lt_trans(s[p], s[q - 1], s[q]);
    }
}

proof fn lemma_strict_no_dup(s: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < s.len() - 1 ==> lex_lt(#[trigger] s[k], s[k + 1]),
    ensures
        s.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j implies s[i] != s[j] by {
        if i < j {
            lemma_strict_pq(s, i, j);
            lemma_lt_irrefl(s[i]);
        } else {
            lemma_strict_pq(s, j, i);
            lemma_lt_irrefl(s[j]);
        }
    }
}

// ---------------------------------------------------------------------------
// Merge sort
// ---------------------------------------------------------------------------

/// Halvings until one element is left: the merge sort's depth.
pub open spec fn depth(n: nat) -> nat
    decreases n,
{
    if n <= 1 {
        0
    } else {
        1 + depth(((n + 1) / 2) as nat)
    }
}

pub proof fn lemma_depth_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        depth(a) <= depth(b),
    decreases b,
{
    if a > 1 {
        lemma_depth_mono(((a + 1) / 2) as nat, ((b + 1) / 2) as nat);
    }
}

/// Merges two sorted vectors; each step takes at most the octets of the OID
/// it moves, plus one.
fn merge<'a>(a: &Vec<&'a [u8]>, b: &Vec<&'a [u8]>) -> (r: (Vec<&'a [u8]>, Ghost<nat>))
    requires
        sorted(views(a@)),
        sorted(views(b@)),
    ensures
        views(r.0@).to_multiset() == views(a@).to_multiset().add(views(b@).to_multiset()),
        sorted(views(r.0@)),
        wt(views(r.0@)) == wt(views(a@)) + wt(views(b@)),
        r.1@ <= wt(views(a@)) + wt(views(b@)),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms;

    let ghost va = views(a@);
    let ghost vb = views(b@);
    let mut out: Vec<&'a [u8]> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    let ghost mut st: nat = 0;
    proof {
        assert(views(out@) =~= Seq::<Seq<u8>>::empty());
        assert(va.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(vb.take(0) =~= Seq::<Seq<u8>>::empty());
        assert(views(out@).to_multiset() =~= va.take(0).to_multiset().add(vb.take(0).to_multiset()));
    }
    while i < a.len() || j < b.len()
        invariant
            va == views(a@),
            vb == views(b@),
            sorted(va),
            sorted(vb),
            i <= a@.len(),
            j <= b@.len(),
            views(out@).to_multiset() == va.take(i as int).to_multiset().add(
                vb.take(j as int).to_multiset(),
            ),
            wt(views(out@)) == wt(va.take(i as int)) + wt(vb.take(j as int)),
            st <= wt(views(out@)),
            sorted(views(out@)),
            out@.len() > 0 && i < a@.len() ==> lex_le(views(out@).last(), va[i as int]),
            out@.len() > 0 && j < b@.len() ==> lex_le(views(out@).last(), vb[j as int]),
        decreases a@.len() + b@.len() - i - j,
    {
        let ghost vo = views(out@);
        let mut take_a = i < a.len();
        let ghost mut s1: nat = 0;
        if i < a.len() && j < b.len() {
            let (c, sc) = cmp_m(a[i], b[j]);
            take_a = c <= 0;
            proof {
                s1 = sc@;
                if c == 0 {
                    assert(lex_le(va[i as int], vb[j as int]));
                }
                if c == 1 {
                    assert(lex_le(vb[j as int], va[i as int]));
                }
            }
        }
        if take_a {
            let x = a[i];
            out.push(x);
            proof {
                assert(views(out@) =~= vo.push(va[i as int]));
                assert(va.take(i + 1) =~= va.take(i as int).push(va[i as int]));
                vo.to_multiset_ensures();
                va.take(i as int).to_multiset_ensures();
                assert(vo.push(va[i as int]).to_multiset() =~= vo.to_multiset().insert(va[i as int]));
                assert(va.take(i as int).push(va[i as int]).to_multiset() =~= va.take(i as int).to_multiset().insert(va[i as int]));
                lemma_wt_push(vo, va[i as int]);
                lemma_wt_push(va.take(i as int), va[i as int]);
                lemma_sorted_push(vo, va[i as int]);
                assert(views(out@).to_multiset() =~= va.take(i + 1).to_multiset().add(
                    vb.take(j as int).to_multiset(),
                ));
                if i + 1 < a@.len() {
                    assert(lex_le(va[i as int], va[i + 1]));
                }
                st = st + s1 + 1;
            }
            i = i + 1;
        } else {
            let x = b[j];
            out.push(x);
            proof {
                assert(views(out@) =~= vo.push(vb[j as int]));
                assert(vb.take(j + 1) =~= vb.take(j as int).push(vb[j as int]));
                vo.to_multiset_ensures();
                vb.take(j as int).to_multiset_ensures();
                assert(vo.push(vb[j as int]).to_multiset() =~= vo.to_multiset().insert(vb[j as int]));
                assert(vb.take(j as int).push(vb[j as int]).to_multiset() =~= vb.take(j as int).to_multiset().insert(vb[j as int]));
                lemma_wt_push(vo, vb[j as int]);
                lemma_wt_push(vb.take(j as int), vb[j as int]);
                lemma_sorted_push(vo, vb[j as int]);
                assert(views(out@).to_multiset() =~= va.take(i as int).to_multiset().add(
                    vb.take(j + 1).to_multiset(),
                ));
                if j + 1 < b@.len() {
                    assert(lex_le(vb[j as int], vb[j + 1]));
                }
                st = st + s1 + 1;
            }
            j = j + 1;
        }
    }
    proof {
        assert(va.take(i as int) =~= va);
        assert(vb.take(j as int) =~= vb);
    }
    (out, Ghost(st))
}

/// Sorts `v[lo..hi]`.
fn msort<'a>(v: &Vec<&'a [u8]>, lo: usize, hi: usize) -> (r: (Vec<&'a [u8]>, Ghost<nat>))
    requires
        lo <= hi <= v@.len(),
    ensures
        views(r.0@).to_multiset() == views(v@).subrange(lo as int, hi as int).to_multiset(),
        sorted(views(r.0@)),
        wt(views(r.0@)) == wt(views(v@).subrange(lo as int, hi as int)),
        r.1@ <= wt(views(v@).subrange(lo as int, hi as int)) * depth((hi - lo) as nat),
    decreases hi - lo,
{
    let ghost vv = views(v@);
    if hi - lo <= 1 {
        let mut out: Vec<&'a [u8]> = Vec::new();
        if hi > lo {
            out.push(v[lo]);
        }
        proof {
            assert(views(out@) =~= vv.subrange(lo as int, hi as int));
        }
        return (out, Ghost(0));
    }
    let mid = lo + (hi - lo) / 2;
    let (a, sa) = msort(v, lo, mid);
    let (b, sb) = msort(v, mid, hi);
    let (out, sm) = merge(&a, &b);
    proof {
        broadcast use vstd::seq_lib::lemma_multiset_commutative;

        let l = vv.subrange(lo as int, mid as int);
        let r = vv.subrange(mid as int, hi as int);
        assert(vv.subrange(lo as int, hi as int) =~= l + r);
        vstd::seq_lib::lemma_multiset_commutative(l, r);
        lemma_wt_concat(l, r);
        let n = (hi - lo) as nat;
        let h = ((n + 1) / 2) as nat;
        lemma_depth_mono((mid - lo) as nat, h);
        lemma_depth_mono((hi - mid) as nat, h);
        assert(depth(n) == 1 + depth(h));
        let wl = wt(l);
        let wr = wt(r);
        let dl = depth((mid - lo) as nat);
        let dr = depth((hi - mid) as nat);
        let dh = depth(h);
        assert(sa@ + sb@ + sm@ <= (wl + wr) * (dh + 1)) by (nonlinear_arith)
            requires
                sa@ <= wl * dl,
                sb@ <= wr * dr,
                sm@ <= wl + wr,
                dl <= dh,
                dr <= dh,
        ;
    }
    (out, Ghost(sa@ + sb@ + sm@))
}

// ---------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------

/// Whether the OIDs of `all`, which `l` parses to, are distinct.
pub fn distinct_sorted(l: &[u8], Ghost(all): Ghost<Seq<SpecExtension>>) -> (r: (bool, Ghost<nat>))
    requires
        parse_extensions(l@) == Some(all),
    ensures
        r.0 == distinct_oids(all),
        r.1@ <= dup_cost(l@.len() as nat),
{
    let ghost oids = all.map_values(|e: SpecExtension| e.oid);
    let ghost n = l@.len();
    let mut v: Vec<&[u8]> = Vec::new();
    let mut a = l;
    let ghost mut i: int = 0;
    let ghost mut st: nat = 0;
    proof {
        assert(all.skip(0) =~= all);
        assert(views(v@) =~= oids.take(0));
    }
    while a.len() > 0
        invariant
            parse_extensions(l@) == Some(all),
            oids == all.map_values(|e: SpecExtension| e.oid),
            n == l@.len(),
            0 <= i <= all.len(),
            parse_extensions(a@) == Some(all.skip(i)),
            views(v@) == oids.take(i),
            a@.len() <= n,
            st + wt(views(v@)) <= n - a@.len(),
        decreases a@.len(),
    {
        let (c, r) = match read_expect(a, 0x30) {
            Some(x) => x,
            None => {
                proof {
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        let (oid, x) = match read_expect(c, 0x06) {
            Some(x) => x,
            None => {
                proof {
                    lemma_ext_list_unfold(a@, c@, r@);
                    assert(false);
                }
                return (false, Ghost(st));
            },
        };
        proof {
            lemma_ext_list_step(a@, c@, r@, oid@, x@);
            let e = parse_extension(c@).unwrap();
            lemma_skip_step(all, i, e, parse_extensions(r@).unwrap());
        }
        let ghost v0 = views(v@);
        v.push(oid);
        proof {
            assert(views(v@) =~= v0.push(oid@));
            assert(oids.take(i + 1) =~= oids.take(i).push(oids[i]));
            lemma_wt_push(v0, oid@);
            st = st + 1;
            i = i + 1;
        }
        a = r;
    }
    proof {
        assert(all.skip(i).len() == 0);
        assert(i == all.len());
        assert(views(v@) =~= oids);
        assert(views(v@).subrange(0, v@.len() as int) =~= views(v@));
        lemma_wt_len(views(v@));
    }
    let k = v.len();
    let (sv, s1) = msort(&v, 0, k);
    let ghost w = wt(oids);
    let ghost ss = views(sv@);
    proof {
        assert(oids.len() == all.len());
        assert(ss.to_multiset() == oids.to_multiset());
        assert(wt(ss) == w);
        assert(st + w <= n);
        assert(sv@.len() == ss.len());
        assert(ss.to_multiset().len() == oids.to_multiset().len()) by {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
        }
        assert(ss.len() == oids.len()) by {
            broadcast use vstd::seq_lib::group_to_multiset_ensures;
        }
    }
    // Neighbours in order, each strictly before the next until two are equal.
    let mut j: usize = 1;
    let ghost mut s2: nat = 0;
    proof {
        if ss.len() > 0 {
            assert(ss.take(1).drop_last() =~= Seq::<Seq<u8>>::empty());
        }
    }
    while j < sv.len()
        invariant
            ss == views(sv@),
            sorted(ss),
            oids == all.map_values(|e: SpecExtension| e.oid),
            oids.len() == all.len(),
            ss.to_multiset() == oids.to_multiset(),
            wt(ss) == w,
            st + w <= n,
            n == l@.len(),
            k <= w,
            s1@ <= w * depth(k as nat),
            1 <= j,
            j <= ss.len() || ss.len() == 0,
            forall|p: int| 0 <= p < j - 1 && p < ss.len() - 1 ==> lex_lt(#[trigger] ss[p], ss[p + 1]),
            ss.len() > 0 ==> s2 <= wt(ss.take(j as int)),
            ss.len() == 0 ==> s2 == 0,
        decreases sv@.len() - j,
    {
        let (c, sc) = cmp_m(sv[j - 1], sv[j]);
        proof {
            assert(ss.take(j + 1) =~= ss.take(j as int).push(ss[j as int]));
            lemma_wt_push(ss.take(j as int), ss[j as int]);
            s2 = s2 + sc@;
        }
        if c == 0 {
            proof {
                lemma_wt_prefix(ss, j + 1);
                assert(ss[j - 1] == ss[j as int]);
                if distinct_oids(all) {
                    assert forall|p: int, q: int|
                        0 <= p < oids.len() && 0 <= q < oids.len() && p != q implies oids[p] != oids[q] by {
                        if p < q {
                            assert(all[p].oid != all[q].oid);
                        } else {
                            assert(all[q].oid != all[p].oid);
                        }
                    }
                    assert(oids.no_duplicates());
                    oids.lemma_multiset_has_no_duplicates();
                    ss.lemma_multiset_has_no_duplicates_conv();
                    assert(false);
                }
                lemma_total(l@.len() as nat, st, s1@, s2, w, k as nat);
            }
            return (false, Ghost(st + s1@ + s2));
        }
        if c == 1 {
            proof {
                assert(lex_le(ss[j - 1], ss[j as int]));
                if lex_lt(ss[j - 1], ss[j as int]) {
                    lemma_lt_trans(ss[j as int], ss[j - 1], ss[j as int]);
                }
                lemma_lt_irrefl(ss[j as int]);
                assert(false);
            }
            return (false, Ghost(st + s1@ + s2));
        }
        j = j + 1;
    }
    proof {
        assert(forall|p: int| 0 <= p < ss.len() - 1 ==> lex_lt(#[trigger] ss[p], ss[p + 1]));
        lemma_strict_no_dup(ss);
        ss.lemma_multiset_has_no_duplicates();
        oids.lemma_multiset_has_no_duplicates_conv();
        assert forall|p: int, q: int| 0 <= p < q < all.len() implies #[trigger] all[p].oid != #[trigger] all[q].oid by {
            assert(oids[p] != oids[q]);
        }
        if ss.len() > 0 {
            assert(ss.take(j as int) =~= ss);
        }
        lemma_total(l@.len() as nat, st, s1@, s2, w, k as nat);
    }
    (true, Ghost(st + s1@ + s2))
}

/// The three phases' steps add up to at most `dup_cost(n)`.
proof fn lemma_total(n: nat, st: nat, s1: nat, s2: nat, w: nat, k: nat)
    requires
        st + w <= n,
        k <= w,
        s1 <= w * depth(k),
        s2 <= w,
    ensures
        st + s1 + s2 <= dup_cost(n),
{
    lemma_depth_mono(k, n);
    let dk = depth(k);
    let dn = depth(n);
    assert(w * dk <= n * dn) by (nonlinear_arith)
        requires
            w <= n,
            dk <= dn,
    ;
    assert(n + n * dn <= n * (dn + 2)) by (nonlinear_arith);
}

} // verus!
