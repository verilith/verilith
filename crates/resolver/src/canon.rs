//! Canonical form (RFC 4034 §6) and the data an RRSIG signs (RFC 4034
//! §3.1.8.1), proven to compute `dspec`'s definitions exactly: names and
//! their lengths, the canonical RDATA, the owner as signed (wildcards
//! included), the RRset sorted and without duplicates.
use crate::dspec::*;
use crate::name::*;
use crate::rr::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// `name_len(b, off)`.
pub fn name_len_x(b: &[u8], off: usize) -> (r: Option<usize>)
    ensures
        r matches Some(x) ==> name_len(b@, off as int) == Some(x as int) && off + x <= b@.len() && x >= 1,
        r is None ==> name_len(b@, off as int) is None,
{
    let mut p = off;
    proof {
        lemma_name_len_bound(b@, off as int);
    }
    while p < b.len()
        invariant
            off <= p,
            name_len(b@, off as int) == match name_len(b@, p as int) {
                Some(l) => Some(l + p - off),
                None => None,
            },
        decreases b@.len() - p,
    {
        let c = b[p] as usize;
        if c == 0 {
            proof {
                lemma_name_len_bound(b@, off as int);
            }
            return Some(p + 1 - off);
        }
        if c > 63 || c + 1 >= b.len() - p {
            return None;
        }
        p = p + 1 + c;
    }
    None
}

pub proof fn lemma_name_len_bound(b: Seq<u8>, off: int)
    ensures
        name_len(b, off) matches Some(l) ==> l >= 1 && off >= 0 && off + l <= b.len(),
    decreases b.len() - off,
{
    if off >= 0 && off < b.len() && b[off] != 0 && b[off] <= 63 && off + 1 + b[off] < b.len() {
        lemma_name_len_bound(b, off + 1 + b[off]);
    }
}

/// `skip_strings(b, off, s)`.
fn skip_strings_x(b: &[u8], off: usize, s: usize) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> skip_strings(b@, off as int, s as nat) == Some(e as int),
        r is None ==> skip_strings(b@, off as int, s as nat) is None,
{
    let mut p = off;
    let mut k = s;
    while k > 0
        invariant
            off <= p,
            k <= s,
            k < s ==> p <= b@.len(),
            skip_strings(b@, off as int, s as nat) == skip_strings(b@, p as int, k as nat),
        decreases k,
    {
        if p >= b.len() {
            return None;
        }
        let l = b[p] as usize;
        if l + 1 > b.len() - p {
            return None;
        }
        p = p + 1 + l;
        k = k - 1;
    }
    Some(p)
}

/// `skip_names(b, off, k)`.
fn skip_names_x(b: &[u8], off: usize, k: usize) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> skip_names(b@, off as int, k as nat) == Some(e as int),
        r is None ==> skip_names(b@, off as int, k as nat) is None,
{
    let blen = b.len();
    let mut p = off;
    let mut j = k;
    while j > 0
        invariant
            j <= k,
            blen == b@.len(),
            p <= b@.len() || j == k,
            skip_names(b@, off as int, k as nat) == skip_names(b@, p as int, j as nat),
        decreases j,
    {
        match name_len_x(b, p) {
            Some(l) => {
                proof {
                    assert(skip_names(b@, p as int, j as nat) == skip_names(b@, p + l, (j - 1) as nat));
                }
                p = p + l;
            },
            None => {
                return None;
            },
        }
        j = j - 1;
    }
    Some(p)
}

/// `layout(t)`.
fn layout_x(t: u16) -> (r: Option<(usize, usize, usize)>)
    ensures
        match layout(t) {
            Some((f, s, k)) => r == Some((f as usize, s as usize, k as usize)),
            None => r is None,
        },
{
    if t == 2 || t == 3 || t == 4 || t == 5 || t == 7 || t == 8 || t == 9 || t == 12 || t == 30 || t == 39 {
        Some((0, 0, 1))
    } else if t == 6 || t == 14 || t == 17 {
        Some((0, 0, 2))
    } else if t == 15 || t == 18 || t == 21 || t == 36 {
        Some((2, 0, 1))
    } else if t == 26 {
        Some((2, 0, 2))
    } else if t == 33 {
        Some((6, 0, 1))
    } else if t == 35 {
        Some((4, 3, 1))
    } else if t == 24 || t == 46 {
        Some((18, 0, 1))
    } else {
        None
    }
}

/// `name_region(t, rd)`.
fn name_region_x(t: u16, rd: &[u8]) -> (r: Option<(usize, usize)>)
    ensures
        r matches Some((a, b)) ==> name_region(t, rd@) == Some((a as int, b as int)),
        r is None ==> name_region(t, rd@) is None,
{
    match layout_x(t) {
        Some((f, s, k)) => {
            if f > rd.len() {
                return None;
            }
            match skip_strings_x(rd, f, s) {
                Some(a) => match skip_names_x(rd, a, k) {
                    Some(b) => Some((a, b)),
                    None => None,
                },
                None => None,
            }
        },
        None => None,
    }
}

/// `canon_rdata(t, rd)`, appended to `out`.
pub fn push_canon_rdata(out: &mut Vec<u8>, t: u16, rd: &[u8])
    ensures
        final(out)@ == old(out)@ + canon_rdata(t, rd@),
{
    let ghost o = out@;
    let ghost want = canon_rdata(t, rd@);
    let (a, b) = match name_region_x(t, rd) {
        Some((a, b)) => (a, b),
        None => (0, 0),
    };
    proof {
        match name_region(t, rd@) {
            Some((x, y)) => {
                assert(x == a && y == b);
            },
            None => {
                assert(a == 0 && b == 0);
                assert(want == rd@);
            },
        }
        assert(forall|i: int| 0 <= i < rd@.len() ==> #[trigger] want[i] == if a <= i < b { lower(rd@[i]) } else { rd@[i] });
        assert(want.len() == rd@.len());
    }
    let mut i: usize = 0;
    while i < rd.len()
        invariant
            i <= rd@.len(),
            want.len() == rd@.len(),
            forall|j: int| 0 <= j < rd@.len() ==> #[trigger] want[j] == if a <= j < b { lower(rd@[j]) } else { rd@[j] },
            out@ == o + want.subrange(0, i as int),
        decreases rd@.len() - i,
    {
        let c = rd[i];
        if a <= i && i < b {
            out.push(lower_byte(c));
        } else {
            out.push(c);
        }
        i = i + 1;
        proof {
            assert(out@ =~= o + want.subrange(0, i as int));
        }
    }
    proof {
        assert(want.subrange(0, rd@.len() as int) =~= want);
    }
}

pub fn canon_rdata_x(t: u16, rd: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == canon_rdata(t, rd@),
{
    let mut v: Vec<u8> = Vec::new();
    push_canon_rdata(&mut v, t, rd);
    proof {
        assert(v@ =~= canon_rdata(t, rd@));
    }
    v
}

/// Appends `s` lowercased.
pub fn push_lower(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + lower_seq(s@),
{
    let ghost o = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            out@ == o + lower_seq(s@).subrange(0, i as int),
        decreases s@.len() - i,
    {
        out.push(lower_byte(s[i]));
        i = i + 1;
        proof {
            assert(out@ =~= o + lower_seq(s@).subrange(0, i as int));
        }
    }
    proof {
        assert(lower_seq(s@).subrange(0, s@.len() as int) =~= lower_seq(s@));
    }
}

pub fn push_bytes(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost o = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            out@ == o + s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        out.push(s[i]);
        i = i + 1;
        proof {
            assert(out@ =~= o + s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
}

pub fn push_u16(out: &mut Vec<u8>, x: u16)
    ensures
        final(out)@ == old(out)@ + be16(x),
{
    out.push((x / 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + be16(x));
    }
}

pub fn push_u32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ == old(out)@ + be32(x),
{
    out.push((x / 0x100_0000) as u8);
    out.push(((x / 0x1_0000) % 256) as u8);
    out.push(((x / 0x100) % 256) as u8);
    out.push((x % 256) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + be32(x));
    }
}

/// `labels_from(n, off)`.
pub fn label_count_x(n: &[u8]) -> (r: usize)
    ensures
        r == label_count(n@),
{
    let mut p: usize = 0;
    let mut c: usize = 0;
    proof {
        lemma_labels_bound(n@, 0);
    }
    while p < n.len()
        invariant
            c + labels_from(n@, p as int) == label_count(n@),
            c <= p,
        decreases n@.len() - p,
    {
        let l = n[p] as usize;
        if l == 0 || l + 1 >= n.len() - p {
            return c;
        }
        p = p + 1 + l;
        c = c + 1;
    }
    c
}

pub proof fn lemma_labels_bound(n: Seq<u8>, off: int)
    ensures
        labels_from(n, off) <= n.len(),
        off >= 0 ==> labels_from(n, off) + off <= n.len() || labels_from(n, off) == 0,
    decreases n.len() - off,
{
    if !(off < 0 || off >= n.len() || n[off] == 0 || off + 1 + n[off] >= n.len()) {
        lemma_labels_bound(n, off + 1 + n[off]);
    }
}

pub fn is_wild_x(n: &[u8]) -> (r: bool)
    ensures
        r == is_wild(n@),
{
    n.len() >= 2 && n[0] == 1 && n[1] == 42
}

pub fn sig_label_count_x(n: &[u8]) -> (r: usize)
    ensures
        r == sig_label_count(n@),
{
    let c = label_count_x(n);
    if is_wild_x(n) && c > 0 {
        c - 1
    } else {
        c
    }
}

/// `skip_labels(n, 0, k)`.
pub fn skip_labels_x(n: &[u8], k: usize) -> (r: usize)
    ensures
        r == skip_labels(n@, 0, k as nat),
        r <= n@.len(),
{
    let mut p: usize = 0;
    let mut j = k;
    while j > 0
        invariant
            p <= n@.len(),
            j <= k,
            skip_labels(n@, 0, k as nat) == skip_labels(n@, p as int, j as nat),
        decreases j,
    {
        if p >= n.len() {
            return p;
        }
        let l = n[p] as usize;
        if l == 0 || l + 1 >= n.len() - p {
            return p;
        }
        p = p + 1 + l;
        j = j - 1;
    }
    p
}

/// `suffix(n, k)`: as an offset into `n`.
pub fn suffix_x(n: &[u8], k: usize) -> (r: usize)
    ensures
        r <= n@.len(),
        n@.subrange(r as int, n@.len() as int) == suffix(n@, k as nat),
{
    let c = label_count_x(n);
    if c <= k {
        proof {
            assert(n@.subrange(0, n@.len() as int) =~= n@);
        }
        0
    } else {
        skip_labels_x(n, c - k)
    }
}

/// `signed_owner(owner, labels)`, appended to `out`.
pub fn push_signed_owner(out: &mut Vec<u8>, owner: &[u8], labels: u8)
    ensures
        final(out)@ == old(out)@ + signed_owner(owner@, labels),
{
    let ghost o = out@;
    if (labels as usize) < sig_label_count_x(owner) {
        let s = suffix_x(owner, labels as usize);
        out.push(1);
        out.push(42);
        push_lower(out, vstd::slice::slice_subrange(owner, s, owner.len()));
        proof {
            assert(out@ =~= o + wild_of(lower_seq(suffix(owner@, labels as nat))));
        }
    } else {
        push_lower(out, owner);
    }
}

// ---------------------------------------------------------------------------
// RDATA order
// ---------------------------------------------------------------------------

/// Compares `a` and `b` in RDATA order: -1, 0 or 1.
pub fn bytes_cmp(a: &[u8], b: &[u8]) -> (r: i8)
    ensures
        r == -1 <==> bytes_lt(a@, b@),
        r == 0 <==> a@ == b@,
        r == 1 <==> bytes_lt(b@, a@),
        r == -1 || r == 0 || r == 1,
{
    let n = if a.len() < b.len() { a.len() } else { b.len() };
    let mut i: usize = 0;
    while i < n
        invariant
            n <= a@.len(),
            n <= b@.len(),
            n == a@.len() || n == b@.len(),
            i <= n,
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
        decreases n - i,
    {
        if a[i] != b[i] {
            proof {
                lemma_lt_unique(a@, b@, i as int);
                lemma_lt_unique(b@, a@, i as int);
                if a@[i as int] < b@[i as int] {
                    assert(bytes_lt(a@, b@));
                    assert(a@ != b@);
                } else {
                    assert(bytes_lt(b@, a@));
                    assert(a@[i as int] != b@[i as int]);
                }
            }
            return if a[i] < b[i] { -1 } else { 1 };
        }
        i = i + 1;
        proof {
            assert forall|j: int| 0 <= j < i implies a@.subrange(0, i as int)[j] == b@.subrange(0, i as int)[j] by {
                if j < i - 1 {
                    assert(a@.subrange(0, i - 1)[j] == b@.subrange(0, i - 1)[j]);
                }
            }
            assert(a@.subrange(0, i as int) =~= b@.subrange(0, i as int));
        }
    }
    proof {
        lemma_lt_unique(a@, b@, n as int);
        lemma_lt_unique(b@, a@, n as int);
        if a@.len() == b@.len() {
            assert(a@.subrange(0, n as int) =~= a@);
            assert(b@.subrange(0, n as int) =~= b@);
        } else {
            assert(a@ != b@);
        }
    }
    if a.len() < b.len() {
        -1
    } else if a.len() > b.len() {
        1
    } else {
        0
    }
}

/// When `a` and `b` agree up to `k` and then differ (or one ends), whether
/// `a` is first depends only on what happens at `k`.
pub proof fn lemma_lt_unique(a: Seq<u8>, b: Seq<u8>, k: int)
    requires
        0 <= k <= a.len(),
        k <= b.len(),
        a.subrange(0, k) == b.subrange(0, k),
        k == a.len() || k == b.len() || a[k] != b[k],
    ensures
        bytes_lt(a, b) <==> ((k == a.len() && k < b.len()) || (k < a.len() && k < b.len() && a[k] < b[k])),
{
    let rhs = (k == a.len() && k < b.len()) || (k < a.len() && k < b.len() && a[k] < b[k]);
    if bytes_lt(a, b) {
        let j = choose|j: int|
            0 <= j <= a.len() && j <= b.len() && a.subrange(0, j) == b.subrange(0, j) && ((j == a.len() && j
                < b.len()) || (j < a.len() && j < b.len() && a[j] < b[j]));
        if j < k {
            assert(a.subrange(0, k)[j] == b.subrange(0, k)[j]);
            assert(a.subrange(0, k)[j] == a[j]);
            assert(b.subrange(0, k)[j] == b[j]);
            assert(false);
        } else if j > k {
            assert(a.subrange(0, j)[k] == b.subrange(0, j)[k]);
            assert(a[k] == b[k]);
            assert(false);
        }
        assert(rhs);
    }
    if rhs {
        assert(0 <= k <= a.len() && k <= b.len() && a.subrange(0, k) == b.subrange(0, k) && ((k == a.len() && k
            < b.len()) || (k < a.len() && k < b.len() && a[k] < b[k])));
        assert(bytes_lt(a, b));
    }
}

pub proof fn lemma_lt_irrefl(a: Seq<u8>)
    ensures
        !bytes_lt(a, a),
{
}

pub proof fn lemma_lt_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        bytes_lt(a, b),
        bytes_lt(b, c),
    ensures
        bytes_lt(a, c),
{
    let i = choose|j: int|
        0 <= j <= a.len() && j <= b.len() && a.subrange(0, j) == b.subrange(0, j) && ((j == a.len() && j < b.len())
            || (j < a.len() && j < b.len() && a[j] < b[j]));
    let k = choose|j: int|
        0 <= j <= b.len() && j <= c.len() && b.subrange(0, j) == c.subrange(0, j) && ((j == b.len() && j < c.len())
            || (j < b.len() && j < c.len() && b[j] < c[j]));
    let m = if i < k { i } else { k };
    assert forall|j: int| 0 <= j < m implies a.subrange(0, m)[j] == c.subrange(0, m)[j] by {
        assert(a.subrange(0, i)[j] == b.subrange(0, i)[j]);
        assert(b.subrange(0, k)[j] == c.subrange(0, k)[j]);
    }
    assert(a.subrange(0, m) =~= c.subrange(0, m));
    if i < k {
        assert(b.subrange(0, k)[i] == c.subrange(0, k)[i]);
    } else if k < i {
        assert(a.subrange(0, i)[k] == b.subrange(0, i)[k]);
    }
    assert(0 <= m <= a.len() && m <= c.len() && a.subrange(0, m) == c.subrange(0, m) && ((m == a.len() && m
        < c.len()) || (m < a.len() && m < c.len() && a[m] < c[m])));
}

// ---------------------------------------------------------------------------
// The RRset in canonical order
// ---------------------------------------------------------------------------

/// Where `c` goes in the sorted `out`: the first position not before it,
/// and whether `c` is there already.
fn find_pos(out: &Vec<Vec<u8>>, c: &Vec<u8>) -> (r: (usize, bool))
    ensures
        r.0 <= out@.len(),
        forall|x: int| 0 <= x < r.0 ==> bytes_lt(#[trigger] out@[x]@, c@),
        r.1 ==> r.0 < out@.len() && out@[r.0 as int]@ == c@,
        !r.1 ==> r.0 == out@.len() || bytes_lt(c@, out@[r.0 as int]@),
{
    let mut p: usize = 0;
    while p < out.len()
        invariant
            p <= out@.len(),
            forall|x: int| 0 <= x < p ==> bytes_lt(#[trigger] out@[x]@, c@),
        decreases out@.len() - p,
    {
        let o = bytes_cmp(&out[p], c);
        if o == 0 {
            return (p, true);
        }
        if o == 1 {
            return (p, false);
        }
        p = p + 1;
    }
    (p, false)
}

/// Inserts `c` into the strictly sorted `out`, unless it is there.
fn insert_sorted(out: &mut Vec<Vec<u8>>, c: Vec<u8>)
    requires
        sorted_strict(views(old(out)@)),
    ensures
        sorted_strict(views(final(out)@)),
        views(final(out)@).to_set() == views(old(out)@).to_set().insert(c@),
{
    let (p, same) = find_pos(out, &c);
    let ghost before = out@;
    let ghost vb = views(before);
    let ghost cv = c@;
    if same {
        proof {
            assert(vb[p as int] == cv);
            assert(vb.to_set().contains(cv));
            assert(vb.to_set().insert(cv) =~= vb.to_set());
        }
        return;
    }
    out.insert(p, c);
    proof {
        let v = views(out@);
        assert(forall|x: int| 0 <= x < p ==> #[trigger] v[x] == vb[x]);
        assert(forall|x: int| p < x < v.len() ==> #[trigger] v[x] == vb[x - 1]);
        assert(v[p as int] == cv);
        assert forall|x: int, y: int| 0 <= x < y < v.len() implies bytes_lt(#[trigger] v[x], #[trigger] v[y]) by {
            if y < p {
                assert(bytes_lt(vb[x], vb[y]));
            } else if y == p {
                assert(bytes_lt(before[x]@, cv));
            } else if x == p {
                assert(bytes_lt(cv, vb[p as int]));
                if y - 1 > p {
                    assert(bytes_lt(vb[p as int], vb[y - 1]));
                    lemma_lt_trans(cv, vb[p as int], vb[y - 1]);
                }
            } else if x < p {
                assert(bytes_lt(before[x]@, cv));
                assert(bytes_lt(cv, vb[p as int]));
                lemma_lt_trans(vb[x], cv, vb[p as int]);
                if y - 1 > p {
                    assert(bytes_lt(vb[p as int], vb[y - 1]));
                    lemma_lt_trans(vb[x], vb[p as int], vb[y - 1]);
                }
            } else {
                assert(bytes_lt(vb[x - 1], vb[y - 1]));
            }
        }
        assert forall|z: Seq<u8>| v.to_set().contains(z) <==> vb.to_set().insert(cv).contains(z) by {
            if v.to_set().contains(z) {
                let x = choose|x: int| 0 <= x < v.len() && v[x] == z;
                if x < p {
                    assert(vb[x] == z);
                } else if x > p {
                    assert(vb[x - 1] == z);
                }
            }
            if vb.to_set().contains(z) {
                let y = choose|y: int| 0 <= y < vb.len() && vb[y] == z;
                if y < p {
                    assert(v[y] == z);
                } else {
                    assert(v[y + 1] == z);
                }
            }
            if z == cv {
                assert(v[p as int] == z);
            }
        }
        assert(v.to_set() =~= vb.to_set().insert(cv));
    }
}

/// The canonical RDATA of `rs` (all of type `t`), sorted, duplicates
/// removed (RFC 4034 §6.3).
pub fn sorted_rdata(rs: &Vec<Rr>, t: u16) -> (r: Vec<Vec<u8>>)
    ensures
        sorted_strict(views(r@)),
        rdata_set(views(r@), rrs(rs@), t),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    let ghost all = canons(rrs(rs@), t);
    proof {
        assert(views(out@) =~= Seq::<Seq<u8>>::empty());
        assert(all.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
    }
    while i < rs.len()
        invariant
            i <= rs@.len(),
            all == canons(rrs(rs@), t),
            all.len() == rs@.len(),
            sorted_strict(views(out@)),
            views(out@).to_set() == all.subrange(0, i as int).to_set(),
        decreases rs@.len() - i,
    {
        let c = canon_rdata_x(t, &rs[i].rdata);
        proof {
            assert(rrs(rs@)[i as int] == rs@[i as int]@);
            assert(all[i as int] == c@);
            assert(all.subrange(0, i + 1) =~= all.subrange(0, i as int).push(c@));
            all.subrange(0, i as int).lemma_push_to_set_commute(c@);
        }
        insert_sorted(&mut out, c);
        i = i + 1;
    }
    proof {
        assert(all.subrange(0, rs@.len() as int) =~= all);
    }
    out
}

pub open spec fn views(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

/// The data RRSIG `sig_rd` signs for an RRset of type `t` owned by
/// `owner`, from its sorted canonical RDATA `ords`; `None` if an RDATA is
/// too long to be one.
pub fn signed_data_x(sig_rd: &[u8], owner: &[u8], t: u16, ords: &Vec<Vec<u8>>) -> (r: Option<Vec<u8>>)
    requires
        sig_wf(sig_rd@),
    ensures
        r matches Some(d) ==> d@ == signed_data(sig_rd@, signed_owner(owner@, sig_labels(sig_rd@)), t, views(ords@)),
{
    let slen = sig_rd.len();
    let end = match name_len_x(sig_rd, 18) {
        Some(l) => 18 + l,
        None => {
            return None;
        },
    };
    let ghost so = signed_owner(owner@, sig_labels(sig_rd@));
    let ttl = ((sig_rd[4] as u32) * 0x100_0000) + ((sig_rd[5] as u32) * 0x1_0000) + ((sig_rd[6] as u32) * 0x100)
        + sig_rd[7] as u32;
    let mut out: Vec<u8> = Vec::new();
    let mut pre: Vec<u8> = canon_rdata_x(TYPE_RRSIG, sig_rd);
    proof {
        assert(pre@.len() == sig_rd@.len());
    }
    pre.truncate(end);
    push_bytes(&mut out, &pre);
    let mut own: Vec<u8> = Vec::new();
    push_signed_owner(&mut own, owner, sig_rd[3]);
    let ghost p0 = out@;
    proof {
        assert(pre@ =~= canon_rdata(TYPE_RRSIG, sig_rd@).subrange(0, sig_end(sig_rd@)));
        assert(views(ords@).subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
        assert(p0 =~= p0 + rrs_wire(so, t, ttl, views(ords@).subrange(0, 0)));
    }
    let mut i: usize = 0;
    while i < ords.len()
        invariant
            i <= ords@.len(),
            own@ == so,
            out@ == p0 + rrs_wire(so, t, ttl, views(ords@).subrange(0, i as int)),
        decreases ords@.len() - i,
    {
        let rd = &ords[i];
        if rd.len() > 65535 {
            return None;
        }
        push_bytes(&mut out, &own);
        push_u16(&mut out, t);
        push_u16(&mut out, 1);
        push_u32(&mut out, ttl);
        push_u16(&mut out, rd.len() as u16);
        push_bytes(&mut out, rd);
        proof {
            let s = views(ords@).subrange(0, i + 1);
            assert(s.drop_last() =~= views(ords@).subrange(0, i as int));
            assert(s.last() == rd@);
            assert(out@ =~= p0 + rrs_wire(so, t, ttl, s));
        }
        i = i + 1;
    }
    proof {
        assert(views(ords@).subrange(0, ords@.len() as int) =~= views(ords@));
        assert(ttl == sig_ttl(sig_rd@));
    }
    Some(out)
}

} // verus!
