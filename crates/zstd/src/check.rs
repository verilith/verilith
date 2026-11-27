//! The check of a compressed block against the input it should decode to.
//! `compress` keeps a block only if the spec decodes it to its input; this
//! decides that without decoding a copy of the output: the literals and
//! sequences are decoded by the spec's rules as the decoder does
//! (`seq::seq_dec`, `seq::seq_next_exec`), and each sequence's literals
//! and match are compared with the input where they would be written. The
//! frame's output so far is the input's start, so a match is a comparison
//! of the input with itself `off` bytes back (`lemma_match_src`).
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
use crate::huf::*;
use crate::prims::row;
use crate::seq::*;
use crate::work::Meter;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use verilith_core::bits::*;
use crate::fse::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The decoder's state `st` when its output is `src[0..q]`: `d` holds
/// everything but the output.
pub open spec fn chk_is(d: &FrameDec, st: FrameState, src: Seq<u8>, q: int) -> bool {
    &&& 0 <= q <= src.len()
    &&& st.out == src.subrange(0, q)
    &&& st.reps == (Reps { r1: d.r1 as nat, r2: d.r2 as nat, r3: d.r3 as nat })
    &&& huf_opt_is(d.huf, st.huf)
    &&& seqt_opt_is(d.seqt, st.seqt)
}

/// A match of `ml` bytes from `off` back after `src[0..x]` is
/// `src[0..x + ml]` when the input repeats itself there.
pub proof fn lemma_match_src(src: Seq<u8>, x: int, off: nat, ml: nat)
    requires
        1 <= off <= x,
        x + ml <= src.len(),
        forall|j: int| 0 <= j < ml ==> #[trigger] src[x + j] == src[x - off + j],
    ensures
        copy_match(src.subrange(0, x), off, ml) == src.subrange(0, x + ml),
    decreases ml,
{
    let o = src.subrange(0, x);
    if ml == 0 {
        assert(copy_match(o, off, 0) == o);
    } else {
        assert(src[x + 0] == src[x - off + 0]);
        assert(o.push(o[o.len() - off]) =~= src.subrange(0, x + 1));
        assert forall|j: int| 0 <= j < ml - 1 implies #[trigger] src[(x + 1) + j] == src[(x + 1) - off + j] by {
            assert(src[x + (j + 1)] == src[x - off + (j + 1)]);
        }
        lemma_match_src(src, x + 1, off, (ml - 1) as nat);
    }
}

/// The low `n` bytes of two words agree when their difference shifted up
/// by the other `8 - n` bytes is zero.
proof fn lemma_low_bytes(u: u64, v: u64, n: u64, k: u64)
    requires
        1 <= n <= 7,
        k < n,
        ((u ^ v) << ((64 - 8 * n) as u64)) == 0,
    ensures
        ((u >> ((8 * k) as u64)) & 0xff) == ((v >> ((8 * k) as u64)) & 0xff),
{
    assert(((u >> ((8 * k) as u64)) & 0xff) == ((v >> ((8 * k) as u64)) & 0xff)) by (bit_vector)
        requires
            1 <= n <= 7,
            k < n,
            ((u ^ v) << ((64 - 8 * n) as u64)) == 0,
    ;
}

/// Bytes below `k` of two words whose difference vanishes under the mask
/// of the low `8 * k` bits are equal.
proof fn lemma_mask_bytes(u: u64, v: u64, k: u64, j: u64)
    requires
        k <= 8,
        j < k,
        ((u ^ v) & (if k >= 8 { 0xffff_ffff_ffff_ffffu64 } else { ((1u64 << ((8 * k) as u64)) - 1) as u64 })) == 0,
    ensures
        ((u >> ((8 * j) as u64)) & 0xff) == ((v >> ((8 * j) as u64)) & 0xff),
{
    if k >= 8 {
        assert(((u >> ((8 * j) as u64)) & 0xff) == ((v >> ((8 * j) as u64)) & 0xff)) by (bit_vector)
            requires
                j < 8,
                (u ^ v) & 0xffff_ffff_ffff_ffffu64 == 0,
        ;
    } else {
        assert(((u >> ((8 * j) as u64)) & 0xff) == ((v >> ((8 * j) as u64)) & 0xff)) by (bit_vector)
            requires
                k < 8,
                j < k,
                ((u ^ v) & (((1u64 << ((8 * k) as u64)) - 1) as u64)) == 0,
        ;
    }
}

/// The mask of the low `8 * k` bits.
#[inline(always)]
fn low_mask(k: u64) -> (m: u64)
    requires
        k <= 8,
    ensures
        m == (if k >= 8 { 0xffff_ffff_ffff_ffffu64 } else { ((1u64 << ((8 * k) as u64)) - 1) as u64 }),
{
    if k >= 8 {
        0xffff_ffff_ffff_ffffu64
    } else {
        assert(1u64 << ((8 * k) as u64) >= 1) by (bit_vector)
            requires
                k < 8,
        ;
        (1u64 << (8 * k)) - 1
    }
}

/// `same` for at most 16 bytes with 16 readable on both sides: two masked
/// word comparisons and no branch on the length.
#[inline(always)]
fn same16(x: &[u8], a: usize, y: &[u8], b: usize, n: usize) -> (r: bool)
    requires
        n <= 16,
        a + 16 <= x@.len(),
        b + 16 <= y@.len(),
    ensures
        r ==> forall|k: int| 0 <= k < n ==> #[trigger] x@[a + k] == y@[b + k],
{
    let k0: u64 = if n >= 8 { 8 } else { n as u64 };
    let k1: u64 = n as u64 - k0;
    let xl = x.len();
    let yl = y.len();
    assert(a + 8 <= xl && b + 8 <= yl);
    let u0 = verilith_core::prims::load_u64_le(x, a);
    let v0 = verilith_core::prims::load_u64_le(y, b);
    let u1 = verilith_core::prims::load_u64_le(x, a + 8);
    let v1 = verilith_core::prims::load_u64_le(y, b + 8);
    let m0 = low_mask(k0);
    let m1 = low_mask(k1);
    let d0 = (u0 ^ v0) & m0;
    let d1 = (u1 ^ v1) & m1;
    let r = (d0 | d1) == 0;
    proof {
        if r {
            assert(d0 == 0 && d1 == 0) by (bit_vector)
                requires
                    (d0 | d1) == 0,
            ;
            assert forall|k: int| 0 <= k < n implies #[trigger] x@[a + k] == y@[b + k] by {
                if k < 8 {
                    let j = k as u64;
                    lemma_mask_bytes(u0, v0, k0, j);
                    verilith_core::lz::lemma_word_byte(x@, a as int, u0, j);
                    verilith_core::lz::lemma_word_byte(y@, b as int, v0, j);
                } else {
                    let j = (k - 8) as u64;
                    lemma_mask_bytes(u1, v1, k1, j);
                    verilith_core::lz::lemma_word_byte(x@, a + 8, u1, j);
                    verilith_core::lz::lemma_word_byte(y@, b + 8, v1, j);
                    assert(x@[a + 8 + j] == x@[a + k]);
                    assert(y@[b + 8 + j] == y@[b + k]);
                }
            }
        }
    }
    r
}

/// Is `x[a..a + n]` equal to `y[b..b + n]`? Eight bytes at a time, the
/// last eight overlapping the ones before; fewer than eight in one masked
/// comparison when there are eight bytes to read.
#[inline(always)]
pub fn same(x: &[u8], a: usize, y: &[u8], b: usize, n: usize) -> (r: bool)
    requires
        a + n <= x@.len(),
        b + n <= y@.len(),
    ensures
        r ==> x@.subrange(a as int, a + n) == y@.subrange(b as int, b + n),
{
    let xl = x.len();
    let yl = y.len();
    if n <= 16 && 16 <= xl - a && 16 <= yl - b {
        if !same16(x, a, y, b, n) {
            return false;
        }
    } else if n >= 8 {
        let mut i: usize = 0;
        while n - i > 8
            invariant
                i <= n,
                n >= 8,
                xl == x@.len(),
                yl == y@.len(),
                a + n <= x@.len(),
                b + n <= y@.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] x@[a + k] == y@[b + k],
            decreases n - i,
        {
            let u = verilith_core::prims::load_u64_le(x, a + i);
            let v = verilith_core::prims::load_u64_le(y, b + i);
            if u != v {
                return false;
            }
            proof {
                assert forall|k: int| 0 <= k < i + 8 implies #[trigger] x@[a + k] == y@[b + k] by {
                    if k >= i {
                        let q = (k - i) as u64;
                        verilith_core::lz::lemma_word_byte(x@, (a + i) as int, u, q);
                        verilith_core::lz::lemma_word_byte(y@, (b + i) as int, v, q);
                    }
                }
            }
            i = i + 8;
        }
        let e = n - 8;
        let u = verilith_core::prims::load_u64_le(x, a + e);
        let v = verilith_core::prims::load_u64_le(y, b + e);
        if u != v {
            return false;
        }
        proof {
            assert forall|k: int| 0 <= k < n implies #[trigger] x@[a + k] == y@[b + k] by {
                if k >= e {
                    let q = (k - e) as u64;
                    verilith_core::lz::lemma_word_byte(x@, (a + e) as int, u, q);
                    verilith_core::lz::lemma_word_byte(y@, (b + e) as int, v, q);
                }
            }
        }
    } else if n > 0 && 8 <= xl - a && 8 <= yl - b {
        let u = verilith_core::prims::load_u64_le(x, a);
        let v = verilith_core::prims::load_u64_le(y, b);
        assert(n < 8);
        let n64 = n as u64;
        assert(n64 < 8);
        let sh: u64 = 64 - 8 * n64;
        if ((u ^ v) << sh) != 0 {
            return false;
        }
        proof {
            assert forall|k: int| 0 <= k < n implies #[trigger] x@[a + k] == y@[b + k] by {
                let q = k as u64;
                lemma_low_bytes(u, v, n as u64, q);
                verilith_core::lz::lemma_word_byte(x@, a as int, u, q);
                verilith_core::lz::lemma_word_byte(y@, b as int, v, q);
            }
        }
    } else {
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                xl == x@.len(),
                yl == y@.len(),
                a + n <= x@.len(),
                b + n <= y@.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] x@[a + k] == y@[b + k],
            decreases n - i,
        {
            if x[a + i] != y[b + i] {
                return false;
            }
            i = i + 1;
        }
    }
    proof {
        assert forall|k: int| 0 <= k < n implies #[trigger] x@.subrange(a as int, a + n)[k] == y@.subrange(b as int, b + n)[k] by {
            assert(x@[a + k] == y@[b + k]);
        }
        assert(x@.subrange(a as int, a + n) =~= y@.subrange(b as int, b + n));
    }
    true
}

/// The fields of one sequence the slow way (as `seq_step_exec` reads
/// them): offset value, match length, literals length and the position
/// after them.
#[verifier::rlimit(40)]
#[inline(always)]
fn seq_fields(t: &SeqTabs, s: &[u8], p: usize, sll: u32, sof: u32, sml: u32, Ghost(ts): Ghost<SeqTables>) -> (r: Option<(u64, u64, u64, usize)>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        p <= 8 * s@.len(),
        (sll as int) < t.ll.rows@.len(),
        (sof as int) < t.of.rows@.len(),
        (sml as int) < t.ml.rows@.len(),
    ensures
        ({
            let ell = ts.ll.rows[sll as int];
            let eof = ts.of.rows[sof as int];
            let eml = ts.ml.rows[sml as int];
            let oc = eof.sym;
            let mlb = ml_bits(eml.sym);
            let llb = ll_bits(ell.sym);
            if oc + mlb + llb > p {
                r is None
            } else {
                &&& r is Some
                &&& r.unwrap().0 as nat == pow2(oc) + bits(s@, p - oc, oc)
                &&& r.unwrap().1 as nat == ml_base(eml.sym) + bits(s@, p - oc - mlb, mlb)
                &&& r.unwrap().2 as nat == ll_base(ell.sym) + bits(s@, p - oc - mlb - llb, llb)
                &&& r.unwrap().3 as int == p - oc - mlb - llb
                &&& r.unwrap().0 < 0x1_0000_0000
                &&& r.unwrap().1 <= 131074
                &&& r.unwrap().2 <= 131071
                &&& r.unwrap().1 >= 3
            }
        }),
{
    let ell = row(t.ll.rows.as_slice(), sll as usize);
    let eof = row(t.of.rows.as_slice(), sof as usize);
    let eml = row(t.ml.rows.as_slice(), sml as usize);
    proof {
        assert(t.ll.rows@[sll as int] == ell);
        assert(t.of.rows@[sof as int] == eof);
        assert(t.ml.rows@[sml as int] == eml);
    }
    let oc = eof.sym as u32;
    proof {
        assert((eml.sym as int) < 53);
    }
    let (mlbase, mlb) = ml_code(eml.sym);
    proof {
        lemma_ml_base_min(eml.sym as nat);
    }
    let (llbase, llb) = ll_code(ell.sym);
    if (oc + mlb + llb) as usize > p {
        return None;
    }
    proof {
        lemma_u64_pow2_no_overflow(oc as nat);
        lemma_u64_shl_is_mul(1, oc as u64);
        lemma_pow2_le(oc as nat, 31);
        lemma_pow2_le(mlb as nat, 16);
        lemma_pow2_le(llb as nat, 16);
        assert(pow2(31) == 0x8000_0000 && pow2(16) == 65536) by {
            lemma2_to64();
        }
    }
    let p1 = p - oc as usize;
    let p2 = p1 - mlb as usize;
    let p3 = p2 - llb as usize;
    let xo = rd(s, p, oc);
    let xm = rd(s, p1, mlb);
    let xl = rd(s, p2, llb);
    let ov: u64 = (1u64 << oc as u64) + xo;
    let ml: u64 = mlbase as u64 + xm;
    let ll: u64 = llbase as u64 + xl;
    Some((ov, ml, ll, p3))
}

/// One sequence's fields and, unless it is the last, the next position
/// and states (for the last, `np` is the position after its fields).
pub struct Fld {
    pub ov: u64,
    pub ml: u64,
    pub ll: u64,
    pub np: usize,
    pub na: u32,
    pub nb: u32,
    pub nc: u32,
}

/// The `seq_step` fields of one sequence at `p` in the given states, and
/// the `seq_next` update after them unless `last`.
pub open spec fn fld_is(f: Fld, ts: SeqTables, s: Seq<u8>, p: int, sll: nat, sof: nat, sml: nat, last: bool) -> bool {
    let ell = ts.ll.rows[sll as int];
    let eof = ts.of.rows[sof as int];
    let eml = ts.ml.rows[sml as int];
    let oc = eof.sym;
    let mlb = ml_bits(eml.sym);
    let llb = ll_bits(ell.sym);
    let p3 = p - oc - mlb - llb;
    &&& oc + mlb + llb <= p
    &&& f.ov as nat == pow2(oc) + bits(s, p - oc, oc)
    &&& f.ml as nat == ml_base(eml.sym) + bits(s, p - oc - mlb, mlb)
    &&& f.ll as nat == ll_base(ell.sym) + bits(s, p3, llb)
    &&& f.ov < 0x1_0000_0000
    &&& f.ml <= 131074
    &&& f.ll <= 131071
    &&& (last ==> f.np as int == p3)
    &&& (!last ==> seq_next(ts, s, p3, sll, sof, sml) == Some((f.np as int, f.na as nat, f.nb as nat, f.nc as nat)))
}

/// Decodes one sequence: from one 56-bit read when it fits, else the slow
/// way.
#[verifier::rlimit(40)]
#[inline(always)]
fn chk_dec(t: &SeqTabs, s: &[u8], p: usize, sll: u32, sof: u32, sml: u32, last: bool, Ghost(ts): Ghost<SeqTables>) -> (r: Option<Fld>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        p <= 8 * s@.len(),
        (sll as int) < t.ll.rows@.len(),
        (sof as int) < t.of.rows@.len(),
        (sml as int) < t.ml.rows@.len(),
    ensures
        r matches Some(f) ==> {
            &&& fld_is(f, ts, s@, p as int, sll as nat, sof as nat, sml as nat, last)
            &&& f.np <= p
            &&& (f.na as int) < t.ll.rows@.len()
            &&& (f.nb as int) < t.of.rows@.len()
            &&& (f.nc as int) < t.ml.rows@.len()
        },
{
    if !last && p >= 64 && p < 8 * s.len() {
        if let Some(d) = seq_dec(t, s, p, sll, sof, sml, Ghost(ts)) {
            return Some(Fld { ov: d.ov, ml: d.ml, ll: d.ll, np: p - d.tot as usize, na: d.a, nb: d.b, nc: d.c });
        }
    }
    let (ov, ml, ll, p3) = match seq_fields(t, s, p, sll, sof, sml, Ghost(ts)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    if last {
        return Some(Fld { ov, ml, ll, np: p3, na: sll, nb: sof, nc: sml });
    }
    match seq_next_exec(t, s, p3, sll, sof, sml, Ghost(ts)) {
        None => None,
        Some((np, na, nb, nc)) => Some(Fld { ov, ml, ll, np, na, nb, nc }),
    }
}

/// The new output of one sequence: `out1` is `src[0..q]` and the literals,
/// then the match is copied; `None` unless that output is `src[0..q2]`
/// with `q2 <= qlim`.
pub open spec fn exec_is(
    src: Seq<u8>,
    lits: Seq<u8>,
    li: int,
    q: int,
    window: nat,
    ov: nat,
    ml: nat,
    ll: nat,
    reps: Reps,
    n1: nat,
    n2: nat,
    n3: nat,
    q2: int,
) -> bool {
    match resolve_offset(ov, ll == 0, reps) {
        None => false,
        Some((off, reps2)) => {
            let out1 = src.subrange(0, q) + lits.subrange(li, li + ll);
            &&& li + ll <= lits.len()
            &&& reps2 == (Reps { r1: n1, r2: n2, r3: n3 })
            &&& !(off > out1.len() || off > window || off == 0)
            &&& copy_match(out1, off, ml) == src.subrange(0, q2)
        },
    }
}

/// Checks that one sequence's literals and match are the input's next
/// bytes.
#[inline(always)]
fn chk_exec(
    lits: &[u8],
    li: usize,
    src: &[u8],
    q: usize,
    qlim: usize,
    window: u64,
    ov: u64,
    ml: u64,
    ll: u64,
    r1: u64,
    r2: u64,
    r3: u64,
) -> (r: Option<(u64, u64, u64, usize)>)
    requires
        ov < 0x1_0000_0000,
        ml <= 131074,
        ll <= 131071,
        li <= lits@.len(),
        lits@.len() <= 131072,
        q <= qlim <= src@.len(),
    ensures
        r matches Some((n1, n2, n3, q2)) ==> {
            &&& exec_is(src@, lits@, li as int, q as int, window as nat, ov as nat, ml as nat, ll as nat,
                Reps { r1: r1 as nat, r2: r2 as nat, r3: r3 as nat }, n1 as nat, n2 as nat, n3 as nat, q2 as int)
            &&& q2 == q + ll + ml
            &&& q2 <= qlim
        },
{
    let (off, n1, n2, n3) = match resolve_offset_exec(ov, ll == 0, r1, r2, r3) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    if ll > (lits.len() - li) as u64 {
        return None;
    }
    if ll > (qlim - q) as u64 || ml > (qlim - q - ll as usize) as u64 {
        return None;
    }
    let lend = li + ll as usize;
    let x = q + ll as usize;
    if !same(lits, li, src, q, ll as usize) {
        return None;
    }
    if off == 0 || off > x as u64 || off > window {
        return None;
    }
    let y = x - off as usize;
    if !same(src, x, src, y, ml as usize) {
        return None;
    }
    proof {
        let out1 = src@.subrange(0, q as int) + lits@.subrange(li as int, lend as int);
        assert(out1 =~= src@.subrange(0, x as int));
        assert forall|j: int| 0 <= j < ml implies #[trigger] src@[x + j] == src@[x - off + j] by {
            assert(src@.subrange(x as int, x + ml)[j] == src@.subrange(y as int, y + ml)[j]);
        }
        lemma_match_src(src@, x as int, off as nat, ml as nat);
    }
    Some((n1, n2, n3, x + ml as usize))
}

/// The result of checking a block's sequences: stream position, repeat
/// offsets, literals used and how far into the input the output reached.
pub struct ChkOut {
    pub p: usize,
    pub r1: u64,
    pub r2: u64,
    pub r3: u64,
    pub li: usize,
    pub q: usize,
}

/// `n` sequences from `st0` decode (`seq_run`) to the state `o` describes,
/// with the output `src[0..o.q]` and `q0 <= o.q <= qlim`.
pub open spec fn run_ok(ts: SeqTables, s: Seq<u8>, lits: Seq<u8>, window: nat, n: nat, st0: SeqState, o: ChkOut, src: Seq<u8>, q0: int, qlim: int) -> bool {
    &&& seq_run(ts, s, lits, window, n, st0) matches Some(fin)
    &&& fin.p == o.p as int
    &&& fin.reps == (Reps { r1: o.r1 as nat, r2: o.r2 as nat, r3: o.r3 as nat })
    &&& fin.li == o.li as int
    &&& fin.out == src.subrange(0, o.q as int)
    &&& o.li <= lits.len()
    &&& q0 <= o.q <= qlim
}

/// Decodes `n` sequences after the output `src[0..q0]` (`seq_run`) and
/// checks that they write `src[q0..q]` without passing `qlim`.
#[verifier::rlimit(40)]
#[inline(always)]
pub fn check_run(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    n: usize,
    p0: usize,
    sll0: u32,
    sof0: u32,
    sml0: u32,
    r10: u64,
    r20: u64,
    r30: u64,
    src: &[u8],
    q0: usize,
    qlim: usize,
    Ghost(ts): Ghost<SeqTables>,
) -> (r: Option<ChkOut>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p0 <= 8 * s@.len(),
        (sll0 as int) < t.ll.rows@.len(),
        (sof0 as int) < t.of.rows@.len(),
        (sml0 as int) < t.ml.rows@.len(),
        q0 <= qlim <= src@.len(),
    ensures
        r matches Some(o) ==> run_ok(ts, s@, lits@, window as nat, n as nat, SeqState {
            p: p0 as int,
            sll: sll0 as nat,
            sof: sof0 as nat,
            sml: sml0 as nat,
            reps: Reps { r1: r10 as nat, r2: r20 as nat, r3: r30 as nat },
            li: 0,
            out: src@.subrange(0, q0 as int),
        }, o, src@, q0 as int, qlim as int),
{
    let ghost st0 = SeqState {
        p: p0 as int,
        sll: sll0 as nat,
        sof: sof0 as nat,
        sml: sml0 as nat,
        reps: Reps { r1: r10 as nat, r2: r20 as nat, r3: r30 as nat },
        li: 0,
        out: src@.subrange(0, q0 as int),
    };
    let ghost full = seq_run(ts, s@, lits@, window as nat, n as nat, st0);
    let mut p = p0;
    let mut sll = sll0;
    let mut sof = sof0;
    let mut sml = sml0;
    let mut r1 = r10;
    let mut r2 = r20;
    let mut r3 = r30;
    let mut li: usize = 0;
    let mut q = q0;
    let mut i: usize = 0;
    let slen = s.len();
    loop
        invariant
            i <= n,
            slen == s@.len(),
            seqtabs_is(t, ts),
            s@.len() < BITS_MAX,
            lits@.len() <= 131072,
            p <= 8 * s@.len(),
            li <= lits@.len(),
            (sll as int) < t.ll.rows@.len(),
            (sof as int) < t.of.rows@.len(),
            (sml as int) < t.ml.rows@.len(),
            q0 <= q <= qlim <= src@.len(),
            st0 == (SeqState {
                p: p0 as int,
                sll: sll0 as nat,
                sof: sof0 as nat,
                sml: sml0 as nat,
                reps: Reps { r1: r10 as nat, r2: r20 as nat, r3: r30 as nat },
                li: 0,
                out: src@.subrange(0, q0 as int),
            }),
            full == seq_run(ts, s@, lits@, window as nat, n as nat, st0),
            seq_run(
                ts,
                s@,
                lits@,
                window as nat,
                (n - i) as nat,
                SeqState {
                    p: p as int,
                    sll: sll as nat,
                    sof: sof as nat,
                    sml: sml as nat,
                    reps: Reps { r1: r1 as nat, r2: r2 as nat, r3: r3 as nat },
                    li: li as int,
                    out: src@.subrange(0, q as int),
                },
            ) == full,
        decreases n - i,
    {
        let ghost cur = SeqState {
            p: p as int,
            sll: sll as nat,
            sof: sof as nat,
            sml: sml as nat,
            reps: Reps { r1: r1 as nat, r2: r2 as nat, r3: r3 as nat },
            li: li as int,
            out: src@.subrange(0, q as int),
        };
        if i == n {
            proof {
                reveal(seq_run);
                assert(seq_run(ts, s@, lits@, window as nat, 0, cur) == Some(cur));
                assert(full == Some(cur));
                assert(seq_run(ts, s@, lits@, window as nat, n as nat, st0) == Some(cur));
                assert(cur.p == p as int);
                assert(cur.li == li as int);
                assert(li <= lits@.len());
                assert(q0 <= q <= qlim);
                assert(run_ok(ts, s@, lits@, window as nat, n as nat, st0, ChkOut { p, r1, r2, r3, li, q }, src@, q0 as int, qlim as int));
            }
            return Some(ChkOut { p, r1, r2, r3, li, q });
        }
        proof {
            lemma_seq_run_unfold(ts, s@, lits@, window as nat, (n - i) as nat, cur);
        }
        let last = i + 1 == n;
        let f = match chk_dec(t, s, p, sll, sof, sml, last, Ghost(ts)) {
            None => {
                return None;
            },
            Some(f) => f,
        };
        let (n1, n2, n3, q2) = match chk_exec(lits, li, src, q, qlim, window, f.ov, f.ml, f.ll, r1, r2, r3) {
            None => {
                return None;
            },
            Some(x) => x,
        };
        let lend = li + f.ll as usize;
        proof {
            let ell = ts.ll.rows[sll as int];
            let eof = ts.of.rows[sof as int];
            let eml = ts.ml.rows[sml as int];
            let p3 = p - eof.sym - ml_bits(eml.sym) - ll_bits(ell.sym);
            assert(seq_step(ts, s@, lits@, window as nat, cur) == Some(SeqState {
                p: p3,
                sll: sll as nat,
                sof: sof as nat,
                sml: sml as nat,
                reps: Reps { r1: n1 as nat, r2: n2 as nat, r3: n3 as nat },
                li: lend as int,
                out: src@.subrange(0, q2 as int),
            }));
            if last {
                assert(f.np as int == p3);
                assert(full == seq_run(ts, s@, lits@, window as nat, 1, cur));
            }
        }
        if last {
            return Some(ChkOut { p: f.np, r1: n1, r2: n2, r3: n3, li: lend, q: q2 });
        }
        let np = f.np;
        let na = f.na;
        let nb = f.nb;
        let nc = f.nc;
        p = np;
        sll = na;
        sof = nb;
        sml = nc;
        r1 = n1;
        r2 = n2;
        r3 = n3;
        li = lend;
        q = q2;
        i = i + 1;
    }
}


/// The bitstream of a sequences section after its tables (`seq_body`),
/// checked against `src[q0..qlim]` as `check_run` does, the literals left
/// after the last sequence included. Returns where the output ends.
pub fn check_body(
    b: &[u8],
    window: u64,
    d: &mut FrameDec,
    tabs: SeqTabs,
    a3: usize,
    n: usize,
    src: &[u8],
    q0: usize,
    qlim: usize,
    Ghost(st): Ghost<FrameState>,
    Ghost(ts): Ghost<SeqTables>,
) -> (r: Option<usize>)
    requires
        b@.len() < BITS_MAX,
        a3 <= b@.len(),
        seqtabs_is(&tabs, ts),
        chk_is(old(d), st, src@, q0 as int),
        old(d).lits@.len() <= 131072,
        q0 <= qlim <= src@.len(),
    ensures
        final(d).lits@ == old(d).lits@,
        r matches Some(q) ==> {
            &&& seq_body(b@, old(d).lits@, window as nat, st, ts, a3 as int, n as nat) matches Some(st2)
            &&& chk_is(final(d), st2, src@, q as int)
            &&& q0 <= q <= qlim
        },
{
    let s = slice_subrange(b, a3, b.len());
    let p = match bstart_exec(s) {
        None => {
            return None;
        },
        Some(p) => p,
    };
    let l1 = tabs.ll.log as usize;
    let l2 = tabs.of.log as usize;
    let l3 = tabs.ml.log as usize;
    if l1 + l2 + l3 > p {
        return None;
    }
    proof {
        lemma_pow2_le(l1 as nat, 9);
        lemma_pow2_le(l2 as nat, 9);
        lemma_pow2_le(l3 as nat, 9);
        assert(pow2(9) == 512) by {
            lemma2_to64();
        }
    }
    let sll = rd(s, p, l1 as u32) as u32;
    let sof = rd(s, p - l1, l2 as u32) as u32;
    let sml = rd(s, p - l1 - l2, l3 as u32) as u32;
    proof {
        assert(s@ == b@.subrange(a3 as int, b@.len() as int));
    }
    let o = match crate::cpu::run_check(&tabs, s, d.lits.as_slice(), window, n, p - l1 - l2 - l3, sll, sof, sml, d.r1, d.r2, d.r3, src, q0, qlim, Ghost(ts)) {
        None => {
            return None;
        },
        Some(o) => o,
    };
    if o.p != 0 {
        return None;
    }
    let rest = d.lits.len() - o.li;
    if rest > qlim - o.q {
        return None;
    }
    if !same(d.lits.as_slice(), o.li, src, o.q, rest) {
        return None;
    }
    let q = o.q + rest;
    proof {
        let lits = d.lits@;
        assert(lits.subrange(o.li as int, lits.len() as int) == lits.subrange(o.li as int, o.li + rest));
        assert(src@.subrange(0, o.q as int) + src@.subrange(o.q as int, q as int) =~= src@.subrange(0, q as int));
    }
    d.r1 = o.r1;
    d.r2 = o.r2;
    d.r3 = o.r3;
    d.seqt = Some(tabs);
    Some(q)
}

/// The sequences section `b` of a block whose literals are in `d.lits`
/// (`seq_section`), checked against `src[q0..qlim]`.
pub fn check_section(
    b: &[u8],
    window: u64,
    d: &mut FrameDec,
    src: &[u8],
    q0: usize,
    qlim: usize,
    Ghost(st): Ghost<FrameState>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Option<usize>)
    requires
        b@.len() < BITS_MAX,
        chk_is(old(d), st, src@, q0 as int),
        old(d).lits@.len() <= 131072,
        q0 <= qlim <= src@.len(),
    ensures
        final(d).lits@ == old(d).lits@,
        r matches Some(q) ==> {
            &&& seq_section(b@, old(d).lits@, window as nat, st) matches Some(st2)
            &&& chk_is(final(d), st2, src@, q as int)
            &&& q0 <= q <= qlim
        },
{
    proof {
        lemma_seq_section(b@, d.lits@, window as nat, st);
    }
    let (n, h) = match nb_seq_exec(b) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    if n == 0 {
        if h != b.len() {
            return None;
        }
        let k = d.lits.len();
        if k > qlim - q0 || !same(d.lits.as_slice(), 0, src, q0, k) {
            return None;
        }
        proof {
            assert(d.lits@.subrange(0, k as int) =~= d.lits@);
            assert(src@.subrange(0, q0 as int) + src@.subrange(q0 as int, q0 + k) =~= src@.subrange(0, q0 + k));
        }
        return Some(q0 + k);
    }
    if h + 1 > b.len() || b[h] % 4 != 0 {
        return None;
    }
    let (tabs, a3) = match seq_hdr_exec(b, h, &d.seqt, Ghost(st), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let ghost ts = seq_hdr(b@, h as int, st).unwrap().0;
    check_body(b, window, d, tabs, a3, n, src, q0, qlim, Ghost(st), Ghost(ts))
}

/// A compressed block's content `b` (`compressed_block`), checked to
/// decode, after the output `src[0..pos]`, to exactly `src[pos..end]`.
/// On `Some(st2)` the spec accepts the block with the state `st2`, whose
/// output is `src[0..end]`, and `d` is in `st2`.
pub fn check_cblock(
    b: &[u8],
    window: u64,
    bmax: usize,
    d: &mut FrameDec,
    src: &[u8],
    pos: usize,
    end: usize,
    Ghost(st): Ghost<FrameState>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Option<Ghost<FrameState>>)
    requires
        b@.len() < BITS_MAX,
        bmax <= 131072,
        pos <= end <= src@.len(),
        end - pos <= bmax,
        chk_is(old(d), st, src@, pos as int),
    ensures
        r matches Some(g) ==> {
            &&& compressed_block(b@, window as nat, bmax as nat, st) == Some(g@)
            &&& chk_is(final(d), g@, src@, end as int)
        },
{
    let ghost hc = old_huf_code(&d.huf);
    proof {
        assert(hc == st.huf);
    }
    let used = match lit_section_exec(b, bmax, &mut d.huf, &mut d.lits, Tracked(m)) {
        None => {
            return None;
        },
        Some(u) => u,
    };
    let ghost l = lit_section(b@, bmax as nat, hc).unwrap();
    let ghost st1 = FrameState { huf: l.huf, ..st };
    let q = match check_section(slice_subrange(b, used, b.len()), window, d, src, pos, end, Ghost(st1), Tracked(m)) {
        None => {
            return None;
        },
        Some(q) => q,
    };
    if q != end {
        return None;
    }
    let ghost st2 = seq_section(b@.subrange(used as int, b@.len() as int), l.lits, window as nat, st1).unwrap();
    Some(Ghost(st2))
}

} // verus!
