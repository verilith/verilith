//! Static dictionary references (§8): a dictionary word and its transform.
use crate::dict::*;
#[cfg(verus_only)]
use crate::spec;
use crate::spec::{DOFFSET, NDBITS};
use crate::tables::{PREFIX_SUFFIX, PS_MAP, TRANSFORMS};
use vstd::prelude::*;

verus! {

/// The longest prefix or suffix string is 8 bytes; every one lies in
/// `PREFIX_SUFFIX`.
#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub proof fn lemma_ps()
    ensures
        forall|i: int| 0 <= i < 50 ==> #[trigger] PS_MAP[i] + 1 + PREFIX_SUFFIX[PS_MAP[i] as int] <= 217
            && PREFIX_SUFFIX[PS_MAP[i] as int] <= 8,
        forall|i: int| 0 <= i < 363 ==> #[trigger] TRANSFORMS[i] < 50,
        forall|t: int| 0 <= t < 121 ==> #[trigger] TRANSFORMS[3 * t + 1] <= 20,
{
    assert(forall|i: int| 0 <= i < 50 ==> #[trigger] PS_MAP[i] + 1 + PREFIX_SUFFIX[PS_MAP[i] as int] <= 217
        && PREFIX_SUFFIX[PS_MAP[i] as int] <= 8) by (compute);
    assert(forall|i: int| 0 <= i < 363 ==> #[trigger] TRANSFORMS[i] < 50) by (compute);
    assert(forall|t: int| 0 <= t < 121 ==> #[trigger] TRANSFORMS[3 * t + 1] <= 20) by (compute);
}

/// Appends prefix or suffix string `id`.
#[verifier::spinoff_prover]
pub fn push_ps(out: &mut Vec<u8>, id: usize)
    requires
        id < 50,
    ensures
        final(out)@ == old(out)@ + spec::ps_string(id as int),
        spec::ps_string(id as int).len() <= 8,
{
    proof {
        lemma_ps();
    }
    let off = PS_MAP[id] as usize;
    let n = PREFIX_SUFFIX[off] as usize;
    let ghost o = out@;
    let ghost ps = spec::ps_string(id as int);
    if n != 0 {
        out.extend_from_slice(slice_sub(PREFIX_SUFFIX.as_slice(), off + 1, off + 1 + n));
    }
    proof {
        if n != 0 {
            assert(PREFIX_SUFFIX@.subrange(off + 1, off + 1 + n) =~= ps);
        } else {
            assert(ps =~= Seq::<u8>::empty());
        }
        assert(out@ =~= o + ps);
    }
}

/// `spec::uc_step` at `i`, in place; returns the step.
#[verifier::spinoff_prover]
fn uc_step(v: &mut Vec<u8>, i: usize) -> (k: usize)
    requires
        i < old(v)@.len() <= 64,
    ensures
        final(v)@ == spec::uc_step(old(v)@, i as int).0,
        k == spec::uc_step(old(v)@, i as int).1,
        k == (if old(v)@[i as int] < 0xc0 { 1usize } else if old(v)@[i as int] < 0xe0 { 2 } else { 3 }),
        final(v)@.len() == old(v)@.len(),
{
    let n = v.len();
    let c = v[i];
    if c < 0xc0 {
        if 97 <= c && c <= 122 {
            v.set(i, c ^ 32);
        }
        1
    } else if c < 0xe0 {
        if i + 1 < n {
            let x = v[i + 1];
            v.set(i + 1, x ^ 32);
        }
        2
    } else {
        if i + 2 < n {
            let x = v[i + 2];
            v.set(i + 2, x ^ 5);
        }
        3
    }
}

/// Uppercasing at an offset: what is in front is left alone.
pub proof fn lemma_uc_step_off(p: Seq<u8>, w: Seq<u8>, i: int)
    requires
        0 <= i < w.len(),
    ensures
        spec::uc_step(p + w, p.len() + i).0 == p + spec::uc_step(w, i).0,
        spec::uc_step(p + w, p.len() + i).1 == spec::uc_step(w, i).1,
        spec::uc_step(w, i).0.len() == w.len(),
{
    let x = p + w;
    let j = p.len() + i;
    assert(x[j] == w[i]);
    if i + 1 < w.len() {
        assert(x[j + 1] == w[i + 1]);
    }
    if i + 2 < w.len() {
        assert(x[j + 2] == w[i + 2]);
    }
    assert(spec::uc_step(x, j).0 =~= p + spec::uc_step(w, i).0);
}

pub proof fn lemma_uc_all_off(p: Seq<u8>, w: Seq<u8>, i: int, n: int)
    requires
        0 <= i,
        n == w.len(),
    ensures
        spec::uc_all(p + w, p.len() + i, p.len() + n) == p + spec::uc_all(w, i, n),
        spec::uc_all(w, i, n).len() == w.len(),
    decreases
            (if i < n {
                n - i
            } else {
                0
            }),
{
    if i < n {
        let x = p + w;
        assert(x[p.len() + i] == w[i]);
        lemma_uc_step_off(p, w, i);
        let k: int = if w[i] < 0xc0 {
            1
        } else if w[i] < 0xe0 {
            2
        } else {
            3
        };
        lemma_uc_all_off(p, spec::uc_step(w, i).0, i + k, n);
    }
}

/// `spec::uc_all` from `s` to the end, in place.
#[verifier::spinoff_prover]
fn uc_from(v: &mut Vec<u8>, s: usize)
    requires
        s <= old(v)@.len() <= 64,
    ensures
        final(v)@ == spec::uc_all(old(v)@, s as int, old(v)@.len() as int),
        final(v)@.len() == old(v)@.len(),
{
    let ghost w = v@;
    let n = v.len();
    let mut i: usize = s;
    while i < n
        invariant
            n == w.len() == v@.len(),
            n <= 64,
            i <= n + 2,
            spec::uc_all(v@, i as int, n as int) == spec::uc_all(w, s as int, n as int),
        decreases n + 3 - i,
    {
        let ghost v0 = v@;
        let k = uc_step(v, i);
        proof {
            assert(spec::uc_all(v0, i as int, n as int) == spec::uc_all(v@, i + k, n as int));
        }
        i = i + k;
    }
}

/// `spec::transform_word(w, t)`, appended to `v`.
#[verifier::spinoff_prover]
#[inline(always)]
fn transform_word_app(v: &mut Vec<u8>, w: &[u8], t: usize)
    requires
        t <= 20,
        w@.len() <= 24,
        old(v)@.len() <= 8,
    ensures
        final(v)@ == old(v)@ + spec::transform_word(w@, t as int),
        spec::transform_word(w@, t as int).len() <= w@.len(),
{
    let n = w.len();
    let ghost p = v@;
    let o = v.len();
    if t <= 9 {
        if n > t {
            v.extend_from_slice(slice_sub(w, 0, n - t));
        }
        proof {
            if n > t {
                assert(v@ =~= p + w@.subrange(0, n - t));
            } else {
                assert(v@ =~= p + Seq::<u8>::empty());
            }
        }
    } else if t >= 12 {
        let k = t - 11;
        if n > k {
            v.extend_from_slice(slice_sub(w, k, n));
        }
        proof {
            if n > k {
                assert(v@ =~= p + w@.subrange(k as int, n as int));
            } else {
                assert(v@ =~= p + Seq::<u8>::empty());
            }
        }
    } else {
        v.extend_from_slice(w);
        proof {
            assert(v@ =~= p + w@);
        }
        if t == 10 {
            if n > 0 {
                proof {
                    lemma_uc_step_off(p, w@, 0);
                }
                uc_step(v, o);
            }
        } else {
            proof {
                lemma_uc_all_off(p, w@, 0, n as int);
            }
            uc_from(v, o);
        }
    }
}

/// `spec::transform(w, id)`, into the empty `out`. `mid` is no longer used.
#[verifier::spinoff_prover]
pub fn transform_into(out: &mut Vec<u8>, mid: &mut Vec<u8>, w: &[u8], id: usize)
    requires
        id < 121,
        w@.len() <= 24,
        old(out)@.len() == 0,
    ensures
        final(out)@ == old(out)@ + spec::transform(w@, id as int),
        spec::transform(w@, id as int).len() <= 40,
{
    proof {
        lemma_ps();
        assert(TRANSFORMS[3 * id as int] < 50 && TRANSFORMS[3 * id + 2] < 50);
        assert(TRANSFORMS[3 * id + 1] <= 20);
    }
    let ghost o = out@;
    push_ps(out, TRANSFORMS[3 * id] as usize);
    transform_word_app(out, w, TRANSFORMS[3 * id + 1] as usize);
    push_ps(out, TRANSFORMS[3 * id + 2] as usize);
    proof {
        assert(out@ =~= o + spec::transform(w@, id as int));
    }
}

/// Transform 0 is the identity.
pub proof fn lemma_transform0(w: Seq<u8>)
    ensures
        spec::transform(w, 0) == w,
{
    assert(TRANSFORMS[0] == 49 && TRANSFORMS[1] == 0 && TRANSFORMS[2] == 49) by (compute);
    assert(PREFIX_SUFFIX[PS_MAP[49] as int] == 0) by (compute);
    assert(spec::ps_string(49) =~= Seq::<u8>::empty());
    assert(spec::transform_word(w, 0) =~= w);
    assert(spec::transform(w, 0) =~= w);
}

/// `r` holds `a`, `b` and `c` in a row from `ti`.
proof fn lemma_join3(r: Seq<u8>, ti: int, a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        0 <= ti,
        ti + a.len() + b.len() + c.len() <= r.len(),
        forall|k: int| ti <= k < ti + a.len() ==> #[trigger] r[k] == a[k - ti],
        forall|k: int| ti + a.len() <= k < ti + a.len() + b.len() ==> #[trigger] r[k] == b[k - (ti + a.len())],
        forall|k: int|
            ti + a.len() + b.len() <= k < ti + a.len() + b.len() + c.len() ==> #[trigger] r[k] == c[k - (ti + a.len()) - b.len()],
    ensures
        r.subrange(ti, ti + a.len() + b.len() + c.len()) == a + b + c,
{
    let got = r.subrange(ti, ti + a.len() + b.len() + c.len());
    let want = a + b + c;
    assert forall|i: int| 0 <= i < got.len() implies got[i] == want[i] by {
        let k = ti + i;
        assert(got[i] == r[k]);
    }
    assert(got =~= want);
}

/// Copies `src[so..so + 8]` to `v[at..at + 8]`.
#[inline(always)]
fn put8(v: &mut Vec<u8>, at: usize, src: &[u8], so: usize)
    requires
        at + 8 <= old(v)@.len(),
        so + 8 <= src@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|k: int|
            0 <= k < old(v)@.len() ==> #[trigger] final(v)@[k] == if at <= k < at + 8 {
                src@[k - at + so]
            } else {
                old(v)@[k]
            },
{
    verilith_core::prims::copy_in(v.as_mut_slice(), at, src, so, 8);
}

/// Writes the `n` dictionary bytes at `o` to `v[q..]`: 16 bytes whatever
/// `n` is, and 8 more when it is over 16.
#[inline(always)]
pub fn put_word(v: &mut Vec<u8>, q: usize, o: usize, n: usize)
    requires
        n <= 24,
        q + 24 <= old(v)@.len(),
        o + 24 <= 122784,
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|k: int| q <= k < q + n ==> #[trigger] final(v)@[k] == spec::dict(o + (k - q)),
        forall|k: int|
            0 <= k < old(v)@.len() && !(q <= k < q + 16) && !(n > 16 && q <= k < q + 24) ==> #[trigger] final(v)@[k]
                == old(v)@[k],
{
    let vl = v.len();
    assert(q + 24 <= vl);
    let c = dict_bytes(o, 24);
    put8(v, q, c, 0);
    put8(v, q + 8, c, 8);
    if n > 16 {
        put8(v, q + 16, c, 16);
    }
    proof {
        assert forall|k: int| q <= k < q + n implies #[trigger] v@[k] == spec::dict(o + (k - q)) by {
            assert(v@[k] == c@[k - q]);
        }
    }
}

/// `spec::uc_step` at the start of the `m` bytes at `v[q..]`, for `m` of 3
/// or more, so that no change falls past their end.
#[inline(always)]
fn uc_first(v: &mut Vec<u8>, q: usize, Ghost(m): Ghost<int>)
    requires
        3 <= m,
        q + m <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        final(v)@.subrange(q as int, q + m) == spec::uc_step(old(v)@.subrange(q as int, q + m), 0).0,
        forall|k: int| 0 <= k < old(v)@.len() && !(q <= k < q + 3) ==> #[trigger] final(v)@[k] == old(v)@[k],
{
    let ghost w = v@.subrange(q as int, q + m);
    let vl = v.len();
    assert(q + 3 <= vl);
    let c = v[q];
    assert(c == w[0]);
    if c < 0xc0 {
        if 97 <= c && c <= 122 {
            v.set(q, c ^ 32);
        }
    } else if c < 0xe0 {
        let x = v[q + 1];
        assert(x == w[1]);
        v.set(q + 1, x ^ 32);
    } else {
        let x = v[q + 2];
        assert(x == w[2]);
        v.set(q + 2, x ^ 5);
    }
    assert(v@.subrange(q as int, q + m) =~= spec::uc_step(w, 0).0);
}

/// What `transform_ring` needs of each transform, packed: bits 0..8 where
/// to read 8 bytes of the prefix in `PREFIX_SUFFIX`, 8..12 its length,
/// 12..20 and 20..24 the same for the suffix, 24..28 how many bytes of the
/// word are cut, and 28.. the kind: 0 cut at the end, 1 cut at the front,
/// 2 upper-case first, 3 not handled. `lemma_tr` checks every entry against
/// `TRANSFORMS`, `PS_MAP` and `PREFIX_SUFFIX`.
pub const TR: [u32; 121] = [
    0x000d10d1, 0x001010d1, 0x00101101, 0x110d10d1, 0x201010d1, 0x005d00d1, 0x000d1101, 0x00101214,
    0x0040f0d1, 0x200d10d1, 0x005190d1, 0x120d10d1, 0x010d10d1, 0x00101203, 0x002030d1, 0x20101101,
    0x0041f0d1, 0x004260d1, 0x301012d1, 0x001240d1, 0x001170d1, 0x0022b0d1, 0x0012e0d1, 0x030d10d1,
    0x001330d1, 0x005350d1, 0x130d10d1, 0x020d10d1, 0x0033b0d1, 0x0063f0d1, 0x200d1101, 0x002300d1,
    0x000d1117, 0x00203101, 0x140d10d1, 0x006480d1, 0x001460d1, 0x0064f0d1, 0x004560d1, 0x150d10d1,
    0x160d10d1, 0x000d15d0, 0x040d10d1, 0x0065d0d1, 0x300d10d1, 0x004640d1, 0x004690d1, 0x0046e0d1,
    0x070d10d1, 0x014730d1, 0x002780d1, 0x0017b0d1, 0x00230101, 0x0037d0d1, 0x190d10d1, 0x170d10d1,
    0x060d10d1, 0x0015b0d1, 0x202030d1, 0x080d10d1, 0x004840d1, 0x003890d1, 0x0040f5d0, 0x050d10d1,
    0x090d10d1, 0x20203101, 0x201240d1, 0x0015b117, 0x301010d1, 0x2022b0d1, 0x002810d1, 0x00117101,
    0x000d1592, 0x008065d0, 0x201460d1, 0x007980d1, 0x0018d0d1, 0x00101117, 0x2015b0d1, 0x201170d1,
    0x005a00d1, 0x00281101, 0x003a60d1, 0x30101101, 0x003aa0d1, 0x300d1101, 0x0028f0d1, 0x301240d1,
    0x202300d1, 0x0015b101, 0x004ae0d1, 0x20230101, 0x004b30d1, 0x005b80d1, 0x301460d1, 0x004be0d1,
    0x20117101, 0x3022b0d1, 0x0028f101, 0x2018d0d1, 0x004c30d1, 0x301170d1, 0x000d12c8, 0x0018d101,
    0x202810d1, 0x302810d1, 0x004cb0d1, 0x302030d1, 0x2028f0d1, 0x2018d101, 0x30281101, 0x30203101,
    0x3018d0d1, 0x3015b0d1, 0x302300d1, 0x30117101, 0x3028f0d1, 0x30230101, 0x20281101, 0x3028f101,
    0x2028f101,
];

/// Entry `id` of `TR` is what the transform tables say.
pub open spec fn tr_ok(id: int) -> bool {
    let e = TR[id];
    let t = TRANSFORMS[3 * id + 1];
    let po = PS_MAP[TRANSFORMS[3 * id] as int];
    let so = PS_MAP[TRANSFORMS[3 * id + 2] as int];
    let pl = PREFIX_SUFFIX[po as int];
    let sl = PREFIX_SUFFIX[so as int];
    &&& (e & 0xff) as int == (if po + 9 <= 217 { po + 1 } else { 209 })
    &&& ((e >> 8) & 15) as int == pl
    &&& ((e >> 12) & 0xff) as int == (if so + 9 <= 217 { so + 1 } else { 209 })
    &&& ((e >> 20) & 15) as int == sl
    &&& ((e >> 24) & 15) as int == (if t <= 9 { t as int } else if t <= 11 { 0 } else { t - 11 })
    &&& (e >> 28) as int == (if t == 11 || (pl != 0 && po + 9 > 217) || (sl != 0 && so + 9 > 217) {
        3int
    } else if t <= 9 {
        0
    } else if t == 10 {
        2
    } else {
        1
    })
}

/// `tr_ok` for the entries below `n`.
pub open spec fn tr_all(n: int) -> bool
    decreases n,
{
    n <= 0 || (tr_ok(n - 1) && tr_all(n - 1))
}

proof fn lemma_tr_all(n: int, id: int)
    requires
        tr_all(n),
        0 <= id < n,
    ensures
        tr_ok(id),
    decreases n,
{
    if id < n - 1 {
        lemma_tr_all(n - 1, id);
    }
}

pub proof fn lemma_tr(id: int)
    requires
        0 <= id < 121,
    ensures
        tr_ok(id),
{
    assert(tr_all(121)) by (compute_only);
    lemma_tr_all(121, id);
}

/// Writes `spec::transform` of dictionary word `(len, idx)` under transform
/// `id` straight to `ring[ti..]`, in 8-byte pieces, and returns its length.
/// Up to 16 bytes after the word are overwritten too. Returns 0, with the
/// ring as it was, for what it does not handle: the upper-casing
/// transforms, an empty result, one longer than `lim`, and reads that would
/// run past the end of a table.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
#[inline(always)]
pub fn transform_ring(ring: &mut Vec<u8>, ti: usize, len: usize, idx: usize, id: usize, lim: u64) -> (wl: usize)
    requires
        id < 121,
        4 <= len <= 24,
        DOFFSET[len as int] + (idx + 1) * len <= 122784,
        ti + 64 <= old(ring)@.len(),
    ensures
        final(ring)@.len() == old(ring)@.len(),
        wl == 0 ==> *final(ring) == *old(ring),
        wl != 0 ==> {
            let w = spec::transform(spec::dict_word(len as int, idx as int), id as int);
            &&& wl == w.len()
            &&& wl <= lim
            &&& wl <= 40
            &&& final(ring)@.subrange(ti as int, ti + wl) == w
            &&& forall|k: int|
                0 <= k < old(ring)@.len() && !(ti <= k < ti + wl + 16) ==> #[trigger] final(ring)@[k] == old(ring)@[k]
        },
{
    proof {
        lemma_ps();
        assert(TRANSFORMS[3 * id as int] < 50 && TRANSFORMS[3 * id + 2] < 50);
        assert(TRANSFORMS[3 * id + 1] <= 20);
        assert(idx * len + len == (idx + 1) * len) by (nonlinear_arith);
    }
    let ghost pid = TRANSFORMS[3 * id as int] as usize;
    let ghost t = TRANSFORMS[3 * id + 1] as usize;
    let ghost sid = TRANSFORMS[3 * id + 2] as usize;
    let ghost po = PS_MAP[pid as int] as usize;
    let ghost so = PS_MAP[sid as int] as usize;
    let e = TR[id];
    let mode = e >> 28;
    let pr = (e & 0xff) as usize;
    let pl = ((e >> 8) & 15) as usize;
    let sr = ((e >> 12) & 0xff) as usize;
    let sl = ((e >> 20) & 15) as usize;
    let k0 = ((e >> 24) & 15) as usize;
    proof {
        lemma_tr(id as int);
        assert(PS_MAP[pid as int] + 1 + PREFIX_SUFFIX[PS_MAP[pid as int] as int] <= 217 && pl <= 8);
        assert(PS_MAP[sid as int] + 1 + PREFIX_SUFFIX[PS_MAP[sid as int] as int] <= 217 && sl <= 8);
    }
    if mode == 3 || len <= k0 {
        return 0;
    }
    let ws = if mode == 1 { k0 } else { 0 };
    let wn = len - k0;
    let wl = pl + wn + sl;
    let off = DOFFSET[len] as usize + idx * len;
    if wl as u64 > lim || off + 33 > 122784 {
        return 0;
    }
    let rl = ring.len();
    let ghost r0 = ring@;
    let ghost word = spec::dict_word(len as int, idx as int);
    let ghost pre = spec::ps_string(pid as int);
    let ghost suf = spec::ps_string(sid as int);
    let ghost cut = word.subrange(ws as int, ws + wn);
    let ghost mid = if t == 10 { spec::uc_step(word, 0).0 } else { cut };
    proof {
        assert(spec::transform_word(word, t as int) =~= mid);
    }
    put8(ring, ti, PREFIX_SUFFIX.as_slice(), pr);
    let ghost ra = ring@;
    assert(ti + 64 <= rl);
    let q = ti + pl;
    put_word(ring, q, off + ws, wn);
    let ghost rw = ring@;
    proof {
        assert forall|k: int| q <= k < q + wn implies #[trigger] rw[k] == cut[k - q] by {
            assert(rw[k] == spec::dict(off + ws + (k - q)));
            assert(cut[k - q] == word[ws + (k - q)]);
        }
        assert(rw.subrange(q as int, q + wn) =~= cut);
    }
    if mode == 2 {
        // Upper-case first: the word is whole, and at least 4 bytes.
        uc_first(ring, q, Ghost(wn as int));
        proof {
            assert(cut =~= word);
        }
    }
    proof {
        let rb = ring@;
        assert forall|k: int| ti <= k < ti + pl implies #[trigger] rb[k] == PREFIX_SUFFIX[k - ti + po + 1] by {
            assert(rw[k] == ra[k]);
        }
        assert(rb.subrange(q as int, q + wn) == mid);
        assert forall|k: int| q <= k < q + wn implies #[trigger] rb[k] == mid[k - q] by {
            assert(rb[k] == rb.subrange(q as int, q + wn)[k - q]);
        }
        assert forall|k: int| 0 <= k < r0.len() && !(ti <= k < ti + wl + 16) implies #[trigger] rb[k] == r0[k] by {
            assert(rw[k] == ra[k]);
        }
    }
    let ghost r2 = ring@;
    put8(ring, q + wn, PREFIX_SUFFIX.as_slice(), sr);
    proof {
        let r3 = ring@;
        assert forall|k: int| ti <= k < ti + pl implies #[trigger] r3[k] == pre[k - ti] by {
            assert(r3[k] == r2[k]);
        }
        assert forall|k: int| q <= k < q + wn implies #[trigger] r3[k] == mid[k - q] by {
            assert(r3[k] == r2[k]);
        }
        assert forall|k: int| q + wn <= k < q + wn + sl implies #[trigger] r3[k] == suf[k - q - wn] by {
            assert(r3[k] == PREFIX_SUFFIX@[k - (q + wn) + so + 1]);
        }
        lemma_join3(r3, ti as int, pre, mid, suf);
        assert forall|k: int| 0 <= k < r0.len() && !(ti <= k < ti + wl + 16) implies #[trigger] r3[k] == r0[k] by {
            assert(r3[k] == r2[k]);
        }
    }
    wl
}

/// The dictionary word of length `len` and index `idx`.
#[verifier::spinoff_prover]
pub fn dict_word(len: usize, idx: usize) -> (r: &'static [u8])
    requires
        4 <= len <= 24,
        DOFFSET[len as int] + (idx + 1) * len <= 122784,
    ensures
        r@ == spec::dict_word(len as int, idx as int),
{
    proof {
        assert(idx * len + len == (idx + 1) * len) by (nonlinear_arith);
    }
    let off = DOFFSET[len] as usize + idx * len;
    let r = dict_bytes(off, len);
    proof {
        assert(r@ =~= spec::dict_word(len as int, idx as int));
    }
    r
}

/// `&s[a..b]`.
fn slice_sub<'a>(s: &'a [u8], a: usize, b: usize) -> (r: &'a [u8])
    requires
        a <= b <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    &s[a..b]
}

} // verus!
