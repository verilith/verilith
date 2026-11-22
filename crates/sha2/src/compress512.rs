//! The SHA-512 compression function (FIPS 180-4 §6.4.2), proven to compute
//! `spec512::compress` block by block: the shape of [`crate::compress`]
//! with 64-bit words, 128-byte blocks and 80 rounds. The round calls are
//! the same text, written by the same `tools/gen_rounds.py`.
// Rotations are written as FIPS 180-4 defines ROTR, (x >> n) | (x << 64 - n),
// since vstd has no specification of `rotate_right`. LLVM emits `ror` for both.
#![allow(clippy::manual_rotate)]
use crate::spec512::{self as spec, Vars, K};
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

#[inline(always)]
fn add(x: u64, y: u64) -> (r: u64)
    ensures
        r == spec::add(x, y),
{
    x.wrapping_add(y)
}

#[inline(always)]
fn big_sigma0(x: u64) -> (r: u64)
    ensures
        r == spec::big_sigma0(x),
{
    (x >> 28 | x << 36) ^ (x >> 34 | x << 30) ^ (x >> 39 | x << 25)
}

#[inline(always)]
fn big_sigma1(x: u64) -> (r: u64)
    ensures
        r == spec::big_sigma1(x),
{
    (x >> 14 | x << 50) ^ (x >> 18 | x << 46) ^ (x >> 41 | x << 23)
}

#[inline(always)]
fn small_sigma0(x: u64) -> (r: u64)
    ensures
        r == spec::small_sigma0(x),
{
    (x >> 1 | x << 63) ^ (x >> 8 | x << 56) ^ (x >> 7)
}

#[inline(always)]
fn small_sigma1(x: u64) -> (r: u64)
    ensures
        r == spec::small_sigma1(x),
{
    (x >> 19 | x << 45) ^ (x >> 61 | x << 3) ^ (x >> 6)
}

/// Ch with one operation fewer than its definition.
#[inline(always)]
fn ch(x: u64, y: u64, z: u64) -> (r: u64)
    ensures
        r == spec::ch(x, y, z),
{
    proof {
        assert(z ^ (x & (y ^ z)) == (x & y) ^ (!x & z)) by (bit_vector);
    }
    z ^ (x & (y ^ z))
}

/// Maj with one operation fewer than its definition.
#[inline(always)]
fn maj(x: u64, y: u64, z: u64) -> (r: u64)
    ensures
        r == spec::maj(x, y, z),
{
    proof {
        assert(((x ^ y) & (y ^ z)) ^ y == (x & y) ^ (x & z) ^ (y & z)) by (bit_vector);
    }
    ((x ^ y) & (y ^ z)) ^ y
}

/// One round: the working variables `a..h` become `h, a, b, c, d, e, f, g`
/// with the new values in `h` and `d`.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn round(a: u64, b: u64, c: u64, d: &mut u64, e: u64, f: u64, g: u64, h: &mut u64, k: u64, w: u64)
    ensures
        spec::round(Vars { a, b, c, d: *old(d), e, f, g, h: *old(h) }, k, w) == (Vars {
            a: *final(h),
            b: a,
            c: b,
            d: c,
            e: *final(d),
            f: e,
            g: f,
            h: g,
        }),
{
    let t1 = add(add(add(add(*h, big_sigma1(e)), ch(e, f, g)), k), w);
    let t2 = add(big_sigma0(a), maj(a, b, c));
    *d = add(*d, t1);
    *h = add(t1, t2);
}

/// The window holds W_{i-16}..W_{i-1} at their indices modulo 16.
pub open spec fn window(w: Seq<u64>, m: Seq<u64>, lo: int, hi: int) -> bool {
    forall|k: int| lo <= k < hi ==> w[k % 16] == #[trigger] spec::schedule(m, k)
}

/// W_i from the window: the schedule's definition, unfolded once.
proof fn lemma_sched_value(w: Seq<u64>, m: Seq<u64>, i: int)
    requires
        16 <= i,
        window(w, m, i - 16, i),
    ensures
        spec::add(
            spec::add(spec::add(spec::small_sigma1(w[(i - 2) % 16]), w[(i - 7) % 16]), spec::small_sigma0(w[(i - 15) % 16])),
            w[i % 16],
        ) == spec::schedule(m, i),
{
    // Equal arguments, equal results: nothing inside these is needed.
    hide(spec::add);
    hide(spec::small_sigma0);
    hide(spec::small_sigma1);
    assert(w[(i - 2) % 16] == spec::schedule(m, i - 2));
    assert(w[(i - 7) % 16] == spec::schedule(m, i - 7));
    assert(w[(i - 15) % 16] == spec::schedule(m, i - 15));
    assert(w[(i - 16) % 16] == spec::schedule(m, i - 16));
    assert((i - 16) % 16 == i % 16);
}

/// Writing W_i over W_{i-16} moves the window on by one.
proof fn lemma_sched_window(w: Seq<u64>, v: Seq<u64>, m: Seq<u64>, i: int)
    requires
        16 <= i,
        w.len() == 16,
        window(w, m, i - 16, i),
        v == w.update(i % 16, spec::schedule(m, i)),
    ensures
        window(v, m, i - 15, i + 1),
{
    assert forall|k: int| i - 15 <= k < i + 1 implies v[k % 16] == #[trigger] spec::schedule(m, k) by {
        if k < i {
            lemma_mod16(k, i);
        }
    }
}

/// This writes W_i over W_{i-16}.
#[verifier::spinoff_prover]
#[inline(always)]
fn sched(w: &mut [u64; 16], i: usize, Ghost(m): Ghost<Seq<u64>>)
    requires
        16 <= i < 80,
        window(old(w)@, m, i - 16, i as int),
    ensures
        window(final(w)@, m, i - 15, i + 1),
{
    let x = add(
        add(add(small_sigma1(w[(i - 2) % 16]), w[(i - 7) % 16]), small_sigma0(w[(i - 15) % 16])),
        w[i % 16],
    );
    proof {
        lemma_sched_value(w@, m, i as int);
    }
    let ghost w0 = w@;
    w[i % 16] = x;
    proof {
        lemma_sched_window(w0, w@, m, i as int);
    }
}

/// Two indices less than 16 apart are different modulo 16.
proof fn lemma_mod16(k: int, i: int)
    requires
        0 <= k < i < k + 16,
    ensures
        k % 16 != i % 16,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, 16);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 16);
}

/// `rounds` one step further: its definition, unfolded once.
proof fn lemma_round(v: Vars, m: Seq<u64>, t: nat)
    ensures
        spec::rounds(v, m, t + 1) == spec::round(spec::rounds(v, m, t), K[t as int], spec::schedule(m, t as int)),
{
}

/// The working variables, in locals once inlined.
#[derive(Clone, Copy)]
struct Regs {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
}

impl Regs {
    spec fn vars(&self) -> Vars {
        Vars { a: self.a, b: self.b, c: self.c, d: self.d, e: self.e, f: self.f, g: self.g, h: self.h }
    }
}

/// Rounds t to t + 7, for t < 16: W_t is M_t.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds8(r: &mut Regs, w: &[u64; 16], t: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u64>>)
    requires
        t % 8 == 0,
        t + 8 <= 16,
        forall|i: int| 0 <= i < 16 ==> w@[i] == #[trigger] spec::schedule(m, i),
        old(r).vars() == spec::rounds(v0, m, t as nat),
    ensures
        final(r).vars() == spec::rounds(v0, m, (t + 8) as nat),
{
    let (mut a, mut b, mut c, mut d) = (r.a, r.b, r.c, r.d);
    let (mut e, mut f, mut g, mut h) = (r.e, r.f, r.g, r.h);
    assert(Vars { a, b, c, d, e, f, g, h } == spec::rounds(v0, m, t as nat));
    // GENERATED ROUNDS (tools/gen_rounds.py)
    round(a, b, c, &mut d, e, f, g, &mut h, K[t], w[t]);
    proof { lemma_round(v0, m, (t) as nat); }
    assert(Vars { a: h, b: a, c: b, d: c, e: d, f: e, g: f, h: g } == spec::rounds(v0, m, (t + 1) as nat));
    round(h, a, b, &mut c, d, e, f, &mut g, K[t + 1], w[t + 1]);
    proof { lemma_round(v0, m, (t + 1) as nat); }
    assert(Vars { a: g, b: h, c: a, d: b, e: c, f: d, g: e, h: f } == spec::rounds(v0, m, (t + 2) as nat));
    round(g, h, a, &mut b, c, d, e, &mut f, K[t + 2], w[t + 2]);
    proof { lemma_round(v0, m, (t + 2) as nat); }
    assert(Vars { a: f, b: g, c: h, d: a, e: b, f: c, g: d, h: e } == spec::rounds(v0, m, (t + 3) as nat));
    round(f, g, h, &mut a, b, c, d, &mut e, K[t + 3], w[t + 3]);
    proof { lemma_round(v0, m, (t + 3) as nat); }
    assert(Vars { a: e, b: f, c: g, d: h, e: a, f: b, g: c, h: d } == spec::rounds(v0, m, (t + 4) as nat));
    round(e, f, g, &mut h, a, b, c, &mut d, K[t + 4], w[t + 4]);
    proof { lemma_round(v0, m, (t + 4) as nat); }
    assert(Vars { a: d, b: e, c: f, d: g, e: h, f: a, g: b, h: c } == spec::rounds(v0, m, (t + 5) as nat));
    round(d, e, f, &mut g, h, a, b, &mut c, K[t + 5], w[t + 5]);
    proof { lemma_round(v0, m, (t + 5) as nat); }
    assert(Vars { a: c, b: d, c: e, d: f, e: g, f: h, g: a, h: b } == spec::rounds(v0, m, (t + 6) as nat));
    round(c, d, e, &mut f, g, h, a, &mut b, K[t + 6], w[t + 6]);
    proof { lemma_round(v0, m, (t + 6) as nat); }
    assert(Vars { a: b, b: c, c: d, d: e, e: f, f: g, g: h, h: a } == spec::rounds(v0, m, (t + 7) as nat));
    round(b, c, d, &mut e, f, g, h, &mut a, K[t + 7], w[t + 7]);
    proof { lemma_round(v0, m, (t + 7) as nat); }
    assert(Vars { a: a, b: b, c: c, d: d, e: e, f: f, g: g, h: h } == spec::rounds(v0, m, (t + 8) as nat));
    // END GENERATED ROUNDS
    *r = Regs { a, b, c, d, e, f, g, h };
}

/// Rounds t to t + 7, for 16 <= t < 80, computing each W_t first.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds8_sched(r: &mut Regs, w: &mut [u64; 16], t: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u64>>)
    requires
        t % 8 == 0,
        16 <= t,
        t + 8 <= 80,
        window(old(w)@, m, t - 16, t as int),
        old(r).vars() == spec::rounds(v0, m, t as nat),
    ensures
        window(final(w)@, m, t - 8, t + 8),
        final(r).vars() == spec::rounds(v0, m, (t + 8) as nat),
{
    let (mut a, mut b, mut c, mut d) = (r.a, r.b, r.c, r.d);
    let (mut e, mut f, mut g, mut h) = (r.e, r.f, r.g, r.h);
    assert(Vars { a, b, c, d, e, f, g, h } == spec::rounds(v0, m, t as nat));
    // GENERATED SCHEDULED (tools/gen_rounds.py)
    sched(w, t, Ghost(m));
    round(a, b, c, &mut d, e, f, g, &mut h, K[t], w[(t) % 16]);
    proof { lemma_round(v0, m, (t) as nat); }
    assert(Vars { a: h, b: a, c: b, d: c, e: d, f: e, g: f, h: g } == spec::rounds(v0, m, (t + 1) as nat));
    sched(w, t + 1, Ghost(m));
    round(h, a, b, &mut c, d, e, f, &mut g, K[t + 1], w[(t + 1) % 16]);
    proof { lemma_round(v0, m, (t + 1) as nat); }
    assert(Vars { a: g, b: h, c: a, d: b, e: c, f: d, g: e, h: f } == spec::rounds(v0, m, (t + 2) as nat));
    sched(w, t + 2, Ghost(m));
    round(g, h, a, &mut b, c, d, e, &mut f, K[t + 2], w[(t + 2) % 16]);
    proof { lemma_round(v0, m, (t + 2) as nat); }
    assert(Vars { a: f, b: g, c: h, d: a, e: b, f: c, g: d, h: e } == spec::rounds(v0, m, (t + 3) as nat));
    sched(w, t + 3, Ghost(m));
    round(f, g, h, &mut a, b, c, d, &mut e, K[t + 3], w[(t + 3) % 16]);
    proof { lemma_round(v0, m, (t + 3) as nat); }
    assert(Vars { a: e, b: f, c: g, d: h, e: a, f: b, g: c, h: d } == spec::rounds(v0, m, (t + 4) as nat));
    sched(w, t + 4, Ghost(m));
    round(e, f, g, &mut h, a, b, c, &mut d, K[t + 4], w[(t + 4) % 16]);
    proof { lemma_round(v0, m, (t + 4) as nat); }
    assert(Vars { a: d, b: e, c: f, d: g, e: h, f: a, g: b, h: c } == spec::rounds(v0, m, (t + 5) as nat));
    sched(w, t + 5, Ghost(m));
    round(d, e, f, &mut g, h, a, b, &mut c, K[t + 5], w[(t + 5) % 16]);
    proof { lemma_round(v0, m, (t + 5) as nat); }
    assert(Vars { a: c, b: d, c: e, d: f, e: g, f: h, g: a, h: b } == spec::rounds(v0, m, (t + 6) as nat));
    sched(w, t + 6, Ghost(m));
    round(c, d, e, &mut f, g, h, a, &mut b, K[t + 6], w[(t + 6) % 16]);
    proof { lemma_round(v0, m, (t + 6) as nat); }
    assert(Vars { a: b, b: c, c: d, d: e, e: f, f: g, g: h, h: a } == spec::rounds(v0, m, (t + 7) as nat));
    sched(w, t + 7, Ghost(m));
    round(b, c, d, &mut e, f, g, h, &mut a, K[t + 7], w[(t + 7) % 16]);
    proof { lemma_round(v0, m, (t + 7) as nat); }
    assert(Vars { a: a, b: b, c: c, d: d, e: e, f: f, g: g, h: h } == spec::rounds(v0, m, (t + 8) as nat));
    // END GENERATED SCHEDULED
    *r = Regs { a, b, c, d, e, f, g, h };
}

/// The 80 rounds over block words `m`, of which the schedule knows only
/// that `w` starts as M0..M15.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds80(r: &mut Regs, w: &mut [u64; 16], Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u64>>)
    requires
        forall|i: int| 0 <= i < 16 ==> old(w)@[i] == #[trigger] spec::schedule(m, i),
        old(r).vars() == v0,
    ensures
        final(r).vars() == spec::rounds(v0, m, 80),
{
    assert(r.vars() == spec::rounds(v0, m, 0));
    // Unrolled with constant t, so that every index into the window and
    // into K is a constant once inlined.
    rounds8(r, w, 0, Ghost(v0), Ghost(m));
    rounds8(r, w, 8, Ghost(v0), Ghost(m));
    assert(window(w@, m, 0, 16)) by {
        assert forall|k: int| 0 <= k < 16 implies w@[k % 16] == #[trigger] spec::schedule(m, k) by {
            assert(k % 16 == k);
        }
    }
    rounds8_sched(r, w, 16, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 24, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 32, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 40, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 48, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 56, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 64, Ghost(v0), Ghost(m));
    rounds8_sched(r, w, 72, Ghost(v0), Ghost(m));
}

/// The word at byte `i`, most significant byte first. LLVM turns the eight
/// loads into one load and a byte swap.
#[inline(always)]
fn load_be64(p: &[u8], i: usize) -> (r: u64)
    requires
        i + 8 <= p@.len(),
    ensures
        r == spec::be64_at(p@, i as int),
{
    let _n = p.len();
    (get(p, i) as u64) << 56 | (get(p, i + 1) as u64) << 48 | (get(p, i + 2) as u64) << 40
        | (get(p, i + 3) as u64) << 32 | (get(p, i + 4) as u64) << 24 | (get(p, i + 5) as u64) << 16
        | (get(p, i + 6) as u64) << 8 | (get(p, i + 7) as u64)
}

/// The block's sixteen words M0..M15.
#[inline(always)]
fn load_block(p: &[u8], off: usize) -> (w: [u64; 16])
    requires
        off + 128 <= p@.len(),
    ensures
        forall|i: int| 0 <= i < 16 ==> w@[i] == #[trigger] spec::words(p@.subrange(off as int, off + 128))[i],
{
    let _n = p.len();
    let ghost blk = p@.subrange(off as int, off + 128);
    let mut w = [0u64; 16];
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            off + 128 <= p@.len(),
            p@.len() <= usize::MAX,
            blk == p@.subrange(off as int, off + 128),
            forall|i: int| 0 <= i < j ==> w@[i] == #[trigger] spec::words(blk)[i],
        decreases 16 - j,
    {
        let x = load_be64(p, off + 8 * j);
        proof {
            assert(spec::be64_at(p@, off + 8 * j) == spec::be64_at(blk, 8 * j as int));
        }
        w[j] = x;
        j = j + 1;
    }
    w
}

/// H(i) from H(i-1) = `st` and the 128-byte block at `off`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress_block(st: &mut [u64; 8], p: &[u8], off: usize)
    requires
        off + 128 <= p@.len(),
    ensures
        final(st)@ == spec::compress(old(st)@, p@.subrange(off as int, off + 128)),
{
    let ghost blk = p@.subrange(off as int, off + 128);
    let ghost m = spec::words(blk);
    let mut w = load_block(p, off);
    proof {
        assert forall|i: int| 0 <= i < 16 implies w@[i] == #[trigger] spec::schedule(m, i) by {
            assert(w@[i] == m[i]);
        }
    }

    let ghost h0 = st@;
    let ghost v0 = spec::init(h0);
    let mut r = Regs { a: st[0], b: st[1], c: st[2], d: st[3], e: st[4], f: st[5], g: st[6], h: st[7] };

    rounds80(&mut r, &mut w, Ghost(v0), Ghost(m));

    st[0] = add(r.a, st[0]);
    st[1] = add(r.b, st[1]);
    st[2] = add(r.c, st[2]);
    st[3] = add(r.d, st[3]);
    st[4] = add(r.e, st[4]);
    st[5] = add(r.f, st[5]);
    st[6] = add(r.g, st[6]);
    st[7] = add(r.h, st[7]);
    proof {
        reveal(spec::compress);
        assert(st@ =~= spec::compress(h0, blk));
    }
}

/// H(n) from H(0) = `st` over the `n = p.len() / 128` whole blocks of `p`;
/// bytes after the last whole block are not read.
#[inline(always)]
pub fn compress_blocks(st: &mut [u64; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    let ghost h0 = st@;
    let n = p.len() / 128;
    let mut i: usize = 0;
    while i < n
        invariant
            n == p@.len() / 128,
            p@.len() <= usize::MAX,
            i <= n,
            st@ == spec::hash_blocks(h0, p@, i as nat),
        decreases n - i,
    {
        compress_block(st, p, 128 * i);
        i = i + 1;
    }
}

// ---------------------------------------------------------------------------
// Rounds over a precomputed schedule
// ---------------------------------------------------------------------------

/// Addition modulo 2^64 is associative.
proof fn lemma_add_assoc(x: u64, y: u64, z: u64)
    ensures
        spec::add(spec::add(x, y), z) == spec::add(x, spec::add(y, z)),
{
    let m = 0x1_0000_0000_0000_0000int;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x as int + y as int, z as int, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x as int, y as int + z as int, m);
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, m as nat);
    vstd::arithmetic::div_mod::lemma_small_mod(z as nat, m as nat);
}

/// [`round`] with K_t + W_t given as one word `kw`.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn round_kw(
    a: u64,
    b: u64,
    c: u64,
    d: &mut u64,
    e: u64,
    f: u64,
    g: u64,
    h: &mut u64,
    Ghost(k): Ghost<u64>,
    Ghost(w): Ghost<u64>,
    kw: u64,
)
    requires
        kw == spec::add(k, w),
    ensures
        spec::round(Vars { a, b, c, d: *old(d), e, f, g, h: *old(h) }, k, w) == (Vars {
            a: *final(h),
            b: a,
            c: b,
            d: c,
            e: *final(d),
            f: e,
            g: f,
            h: g,
        }),
{
    let x = add(add(*h, big_sigma1(e)), ch(e, f, g));
    proof {
        lemma_add_assoc(x, k, w);
    }
    let t1 = add(x, kw);
    let t2 = add(big_sigma0(a), maj(a, b, c));
    *d = add(*d, t1);
    *h = add(t1, t2);
}

/// `wk` is K_t + W_t for the block words `m`, for every t.
pub open spec fn kw_schedule(wk: Seq<u64>, m: Seq<u64>) -> bool {
    forall|i: int| 0 <= i < 80 ==> wk[i] == #[trigger] spec::add(K[i], spec::schedule(m, i))
}

/// Rounds t to t + 7 from a precomputed schedule.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds8_kw(r: &mut Regs, wk: &[u64; 80], t: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u64>>)
    requires
        t % 8 == 0,
        t + 8 <= 80,
        kw_schedule(wk@, m),
        old(r).vars() == spec::rounds(v0, m, t as nat),
    ensures
        final(r).vars() == spec::rounds(v0, m, (t + 8) as nat),
{
    let (mut a, mut b, mut c, mut d) = (r.a, r.b, r.c, r.d);
    let (mut e, mut f, mut g, mut h) = (r.e, r.f, r.g, r.h);
    assert(Vars { a, b, c, d, e, f, g, h } == spec::rounds(v0, m, t as nat));
    // GENERATED KW (tools/gen_rounds.py)
    round_kw(a, b, c, &mut d, e, f, g, &mut h, Ghost(K[(t) as int]), Ghost(spec::schedule(m, (t) as int)), wk[t]);
    proof { lemma_round(v0, m, (t) as nat); }
    assert(Vars { a: h, b: a, c: b, d: c, e: d, f: e, g: f, h: g } == spec::rounds(v0, m, (t + 1) as nat));
    round_kw(h, a, b, &mut c, d, e, f, &mut g, Ghost(K[(t + 1) as int]), Ghost(spec::schedule(m, (t + 1) as int)), wk[t + 1]);
    proof { lemma_round(v0, m, (t + 1) as nat); }
    assert(Vars { a: g, b: h, c: a, d: b, e: c, f: d, g: e, h: f } == spec::rounds(v0, m, (t + 2) as nat));
    round_kw(g, h, a, &mut b, c, d, e, &mut f, Ghost(K[(t + 2) as int]), Ghost(spec::schedule(m, (t + 2) as int)), wk[t + 2]);
    proof { lemma_round(v0, m, (t + 2) as nat); }
    assert(Vars { a: f, b: g, c: h, d: a, e: b, f: c, g: d, h: e } == spec::rounds(v0, m, (t + 3) as nat));
    round_kw(f, g, h, &mut a, b, c, d, &mut e, Ghost(K[(t + 3) as int]), Ghost(spec::schedule(m, (t + 3) as int)), wk[t + 3]);
    proof { lemma_round(v0, m, (t + 3) as nat); }
    assert(Vars { a: e, b: f, c: g, d: h, e: a, f: b, g: c, h: d } == spec::rounds(v0, m, (t + 4) as nat));
    round_kw(e, f, g, &mut h, a, b, c, &mut d, Ghost(K[(t + 4) as int]), Ghost(spec::schedule(m, (t + 4) as int)), wk[t + 4]);
    proof { lemma_round(v0, m, (t + 4) as nat); }
    assert(Vars { a: d, b: e, c: f, d: g, e: h, f: a, g: b, h: c } == spec::rounds(v0, m, (t + 5) as nat));
    round_kw(d, e, f, &mut g, h, a, b, &mut c, Ghost(K[(t + 5) as int]), Ghost(spec::schedule(m, (t + 5) as int)), wk[t + 5]);
    proof { lemma_round(v0, m, (t + 5) as nat); }
    assert(Vars { a: c, b: d, c: e, d: f, e: g, f: h, g: a, h: b } == spec::rounds(v0, m, (t + 6) as nat));
    round_kw(c, d, e, &mut f, g, h, a, &mut b, Ghost(K[(t + 6) as int]), Ghost(spec::schedule(m, (t + 6) as int)), wk[t + 6]);
    proof { lemma_round(v0, m, (t + 6) as nat); }
    assert(Vars { a: b, b: c, c: d, d: e, e: f, f: g, g: h, h: a } == spec::rounds(v0, m, (t + 7) as nat));
    round_kw(b, c, d, &mut e, f, g, h, &mut a, Ghost(K[(t + 7) as int]), Ghost(spec::schedule(m, (t + 7) as int)), wk[t + 7]);
    proof { lemma_round(v0, m, (t + 7) as nat); }
    assert(Vars { a: a, b: b, c: c, d: d, e: e, f: f, g: g, h: h } == spec::rounds(v0, m, (t + 8) as nat));
    // END GENERATED KW
    *r = Regs { a, b, c, d, e, f, g, h };
}

/// The 80 rounds over a precomputed schedule for block words `m`.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds80_kw(r: &mut Regs, wk: &[u64; 80], Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u64>>)
    requires
        kw_schedule(wk@, m),
        old(r).vars() == v0,
    ensures
        final(r).vars() == spec::rounds(v0, m, 80),
{
    assert(r.vars() == spec::rounds(v0, m, 0));
    rounds8_kw(r, wk, 0, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 8, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 16, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 24, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 32, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 40, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 48, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 56, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 64, Ghost(v0), Ghost(m));
    rounds8_kw(r, wk, 72, Ghost(v0), Ghost(m));
}

/// H(i) from H(i-1) = `st` and a block whose K_t + W_t are `wk`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress_block_kw(st: &mut [u64; 8], wk: &[u64; 80], Ghost(blk): Ghost<Seq<u8>>)
    requires
        kw_schedule(wk@, spec::words(blk)),
    ensures
        final(st)@ == spec::compress(old(st)@, blk),
{
    let ghost m = spec::words(blk);
    let ghost h0 = st@;
    let ghost v0 = spec::init(h0);
    let mut r = Regs { a: st[0], b: st[1], c: st[2], d: st[3], e: st[4], f: st[5], g: st[6], h: st[7] };
    rounds80_kw(&mut r, wk, Ghost(v0), Ghost(m));
    st[0] = add(r.a, st[0]);
    st[1] = add(r.b, st[1]);
    st[2] = add(r.c, st[2]);
    st[3] = add(r.d, st[3]);
    st[4] = add(r.e, st[4]);
    st[5] = add(r.f, st[5]);
    st[6] = add(r.g, st[6]);
    st[7] = add(r.h, st[7]);
    proof {
        reveal(spec::compress);
        assert(st@ =~= spec::compress(h0, blk));
    }
}

/// H(n) from H(0) = `st` over the whole blocks of `p`, two blocks' schedules
/// at a time from the AVX2 kernel (`crate::avx2::schedule512x2`), and a last
/// odd block by the scalar rounds. To be called only where the CPU has AVX2.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn compress_blocks_x2(st: &mut [u64; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    let ghost h0 = st@;
    let n = p.len() / 128;
    let mut i: usize = 0;
    if n >= 2 {
        let mut w0 = [0u64; 80];
        let mut w1 = [0u64; 80];
        while i + 2 <= n
            invariant
                n == p@.len() / 128,
                p@.len() <= usize::MAX,
                i <= n,
                st@ == spec::hash_blocks(h0, p@, i as nat),
            decreases n - i,
        {
            crate::avx2::schedule512x2(p, 128 * i, 128 * (i + 1), &mut w0, &mut w1);
            compress_block_kw(st, &w0, Ghost(spec::block(p@, i as int)));
            assert(st@ == spec::hash_blocks(h0, p@, (i + 1) as nat));
            compress_block_kw(st, &w1, Ghost(spec::block(p@, (i + 1) as int)));
            assert(st@ == spec::hash_blocks(h0, p@, (i + 2) as nat));
            i = i + 2;
        }
    } else {
        assert(st@ == spec::hash_blocks(h0, p@, 0));
    }
    if i < n {
        compress_block(st, p, 128 * i);
        assert(st@ == spec::hash_blocks(h0, p@, (i + 1) as nat));
    }
}

// ---------------------------------------------------------------------------
// Pipelined: the next pair's schedule between this pair's rounds
// ---------------------------------------------------------------------------

/// Rounds t to t + 7 from the precomputed schedule `wk`, and, if `step`,
/// steps `s` and `s + 1` of another schedule.
#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn group_kw_step(
    r: &mut Regs,
    wk: &[u64; 80],
    t: usize,
    Ghost(v0): Ghost<Vars>,
    Ghost(m): Ghost<Seq<u64>>,
    sc: &mut crate::avx2::Sched512,
    s: usize,
    step: bool,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        t % 8 == 0,
        t + 8 <= 80,
        kw_schedule(wk@, m),
        old(r).vars() == spec::rounds(v0, m, t as nat),
        step ==> 8 <= s && s + 2 <= 40,
        crate::avx2::sched_at(*old(sc), m0, m1, s as int),
        crate::avx2::kw_upto(old(w0)@, m0, 2 * s),
        crate::avx2::kw_upto(old(w1)@, m1, 2 * s),
    ensures
        final(r).vars() == spec::rounds(v0, m, (t + 8) as nat),
        step ==> crate::avx2::sched_at(*final(sc), m0, m1, s + 2),
        step ==> crate::avx2::kw_upto(final(w0)@, m0, 2 * s + 4),
        step ==> crate::avx2::kw_upto(final(w1)@, m1, 2 * s + 4),
        !step ==> *final(sc) == *old(sc) && final(w0)@ == old(w0)@ && final(w1)@ == old(w1)@,
{
    rounds8_kw(r, wk, t, Ghost(v0), Ghost(m));
    if step {
        crate::avx2::sched_steps2(sc, s, w0, w1, Ghost(m0), Ghost(m1));
    }
}

/// The 80 rounds from the precomputed schedule `wk`, with `k` pairs of
/// steps of another schedule (from step `s0`) between the round groups.
#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn rounds80_kw_steps(
    r: &mut Regs,
    wk: &[u64; 80],
    Ghost(v0): Ghost<Vars>,
    Ghost(m): Ghost<Seq<u64>>,
    sc: &mut crate::avx2::Sched512,
    s0: usize,
    k: usize,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        kw_schedule(wk@, m),
        old(r).vars() == v0,
        k <= 10,
        8 <= s0,
        s0 + 2 * k <= 40,
        crate::avx2::sched_at(*old(sc), m0, m1, s0 as int),
        crate::avx2::kw_upto(old(w0)@, m0, 2 * s0),
        crate::avx2::kw_upto(old(w1)@, m1, 2 * s0),
    ensures
        final(r).vars() == spec::rounds(v0, m, 80),
        crate::avx2::sched_at(*final(sc), m0, m1, s0 + 2 * k),
        crate::avx2::kw_upto(final(w0)@, m0, 2 * (s0 + 2 * k)),
        crate::avx2::kw_upto(final(w1)@, m1, 2 * (s0 + 2 * k)),
{
    assert(r.vars() == spec::rounds(v0, m, 0));
    let sg = if 0 < k { s0 + 0 } else { s0 + 2 * k };
    group_kw_step(r, wk, 0, Ghost(v0), Ghost(m), sc, sg, 0 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 1 < k { s0 + 2 } else { s0 + 2 * k };
    group_kw_step(r, wk, 8, Ghost(v0), Ghost(m), sc, sg, 1 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 2 < k { s0 + 4 } else { s0 + 2 * k };
    group_kw_step(r, wk, 16, Ghost(v0), Ghost(m), sc, sg, 2 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 3 < k { s0 + 6 } else { s0 + 2 * k };
    group_kw_step(r, wk, 24, Ghost(v0), Ghost(m), sc, sg, 3 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 4 < k { s0 + 8 } else { s0 + 2 * k };
    group_kw_step(r, wk, 32, Ghost(v0), Ghost(m), sc, sg, 4 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 5 < k { s0 + 10 } else { s0 + 2 * k };
    group_kw_step(r, wk, 40, Ghost(v0), Ghost(m), sc, sg, 5 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 6 < k { s0 + 12 } else { s0 + 2 * k };
    group_kw_step(r, wk, 48, Ghost(v0), Ghost(m), sc, sg, 6 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 7 < k { s0 + 14 } else { s0 + 2 * k };
    group_kw_step(r, wk, 56, Ghost(v0), Ghost(m), sc, sg, 7 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 8 < k { s0 + 16 } else { s0 + 2 * k };
    group_kw_step(r, wk, 64, Ghost(v0), Ghost(m), sc, sg, 8 < k, w0, w1, Ghost(m0), Ghost(m1));
    let sg = if 9 < k { s0 + 18 } else { s0 + 2 * k };
    group_kw_step(r, wk, 72, Ghost(v0), Ghost(m), sc, sg, 9 < k, w0, w1, Ghost(m0), Ghost(m1));
}

/// One block's rounds from its precomputed schedule `wk`, with `k` pairs of
/// steps of another schedule (from step `s0`) between the round groups.
#[cfg(target_arch = "x86_64")]
#[verifier::spinoff_prover]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn block_with_steps(
    st: &mut [u64; 8],
    wk: &[u64; 80],
    Ghost(blk): Ghost<Seq<u8>>,
    sc: &mut crate::avx2::Sched512,
    s0: usize,
    k: usize,
    w0: &mut [u64; 80],
    w1: &mut [u64; 80],
    Ghost(m0): Ghost<Seq<u64>>,
    Ghost(m1): Ghost<Seq<u64>>,
)
    requires
        kw_schedule(wk@, spec::words(blk)),
        k <= 10,
        8 <= s0,
        s0 + 2 * k <= 40,
        crate::avx2::sched_at(*old(sc), m0, m1, s0 as int),
        crate::avx2::kw_upto(old(w0)@, m0, 2 * s0),
        crate::avx2::kw_upto(old(w1)@, m1, 2 * s0),
    ensures
        final(st)@ == spec::compress(old(st)@, blk),
        crate::avx2::sched_at(*final(sc), m0, m1, s0 + 2 * k),
        crate::avx2::kw_upto(final(w0)@, m0, 2 * (s0 + 2 * k)),
        crate::avx2::kw_upto(final(w1)@, m1, 2 * (s0 + 2 * k)),
{
    let ghost m = spec::words(blk);
    let ghost h0 = st@;
    let ghost v0 = spec::init(h0);
    let mut r = Regs { a: st[0], b: st[1], c: st[2], d: st[3], e: st[4], f: st[5], g: st[6], h: st[7] };
    rounds80_kw_steps(&mut r, wk, Ghost(v0), Ghost(m), sc, s0, k, w0, w1, Ghost(m0), Ghost(m1));
    st[0] = add(r.a, st[0]);
    st[1] = add(r.b, st[1]);
    st[2] = add(r.c, st[2]);
    st[3] = add(r.d, st[3]);
    st[4] = add(r.e, st[4]);
    st[5] = add(r.f, st[5]);
    st[6] = add(r.g, st[6]);
    st[7] = add(r.h, st[7]);
    proof {
        reveal(spec::compress);
        assert(st@ =~= spec::compress(h0, blk));
    }
}

/// `kw_upto` over all 80 words is `kw_schedule`.
proof fn lemma_kw_all(wk: Seq<u64>, m: Seq<u64>)
    requires
        crate::avx2::kw_upto(wk, m, 80),
    ensures
        kw_schedule(wk, m),
{
}

/// The rounds of blocks `b0` and `b1` from their schedules, and the whole
/// schedule of the blocks at `o0` and `o1` of `p`, interleaved with them:
/// 10 pairs of steps during the first block, 6 during the second.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub fn pair_kw(
    st: &mut [u64; 8],
    cur0: &[u64; 80],
    cur1: &[u64; 80],
    Ghost(b0): Ghost<Seq<u8>>,
    Ghost(b1): Ghost<Seq<u8>>,
    p: &[u8],
    o0: usize,
    o1: usize,
    nxt0: &mut [u64; 80],
    nxt1: &mut [u64; 80],
)
    requires
        kw_schedule(cur0@, spec::words(b0)),
        kw_schedule(cur1@, spec::words(b1)),
        o0 + 128 <= p@.len(),
        o1 + 128 <= p@.len(),
    ensures
        final(st)@ == spec::compress(spec::compress(old(st)@, b0), b1),
        kw_schedule(final(nxt0)@, spec::words(p@.subrange(o0 as int, o0 + 128))),
        kw_schedule(final(nxt1)@, spec::words(p@.subrange(o1 as int, o1 + 128))),
{
    let ghost m0 = spec::words(p@.subrange(o0 as int, o0 + 128));
    let ghost m1 = spec::words(p@.subrange(o1 as int, o1 + 128));
    let mut sc = crate::avx2::sched_start(p, o0, o1, nxt0, nxt1);
    block_with_steps(st, cur0, Ghost(b0), &mut sc, 8, 10, nxt0, nxt1, Ghost(m0), Ghost(m1));
    block_with_steps(st, cur1, Ghost(b1), &mut sc, 28, 6, nxt0, nxt1, Ghost(m0), Ghost(m1));
    proof {
        lemma_kw_all(nxt0@, m0);
        lemma_kw_all(nxt1@, m1);
    }
}

/// H(n) from H(0) = `st` over the whole blocks of `p`, pipelined: each pair
/// of blocks is compressed (by `cpu::pair_avx2`, which is [`pair_kw`]
/// compiled with AVX2) while the next pair's schedule is computed. To be
/// called only where the CPU has AVX2.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub fn compress_blocks_pipe(st: &mut [u64; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 128) as nat),
{
    let n = p.len() / 128;
    if n < 4 {
        compress_blocks_x2(st, p);
        return;
    }
    let ghost h0 = st@;
    let mut a0 = [0u64; 80];
    let mut a1 = [0u64; 80];
    let mut c0 = [0u64; 80];
    let mut c1 = [0u64; 80];
    crate::avx2::schedule512x2(p, 0, 128, &mut a0, &mut a1);
    let mut i: usize = 0;
    let mut in_a = true;
    // Blocks i and i + 1 are scheduled, in a0/a1 or c0/c1.
    while i + 4 <= n
        invariant
            n == p@.len() / 128,
            p@.len() <= usize::MAX,
            i + 2 <= n,
            st@ == spec::hash_blocks(h0, p@, i as nat),
            in_a ==> kw_schedule(a0@, spec::words(spec::block(p@, i as int))),
            in_a ==> kw_schedule(a1@, spec::words(spec::block(p@, i + 1))),
            !in_a ==> kw_schedule(c0@, spec::words(spec::block(p@, i as int))),
            !in_a ==> kw_schedule(c1@, spec::words(spec::block(p@, i + 1))),
        decreases n - i,
    {
        let ghost b0 = spec::block(p@, i as int);
        let ghost b1 = spec::block(p@, i + 1);
        if in_a {
            crate::cpu::pair_avx2(st, &a0, &a1, Ghost(b0), Ghost(b1), p, 128 * (i + 2), 128 * (i + 3), &mut c0, &mut c1);
        } else {
            crate::cpu::pair_avx2(st, &c0, &c1, Ghost(b0), Ghost(b1), p, 128 * (i + 2), 128 * (i + 3), &mut a0, &mut a1);
        }
        assert(spec::hash_blocks(h0, p@, (i + 1) as nat) == spec::compress(spec::hash_blocks(h0, p@, i as nat), b0));
        assert(st@ == spec::hash_blocks(h0, p@, (i + 2) as nat));
        in_a = !in_a;
        i = i + 2;
    }
    // The last scheduled pair.
    let ghost b0 = spec::block(p@, i as int);
    let ghost b1 = spec::block(p@, i + 1);
    if in_a {
        compress_block_kw(st, &a0, Ghost(b0));
        compress_block_kw(st, &a1, Ghost(b1));
    } else {
        compress_block_kw(st, &c0, Ghost(b0));
        compress_block_kw(st, &c1, Ghost(b1));
    }
    assert(spec::hash_blocks(h0, p@, (i + 1) as nat) == spec::compress(spec::hash_blocks(h0, p@, i as nat), b0));
    assert(st@ == spec::hash_blocks(h0, p@, (i + 2) as nat));
    i = i + 2;
    if i < n {
        compress_block(st, p, 128 * i);
        assert(st@ == spec::hash_blocks(h0, p@, (i + 1) as nat));
    }
}

} // verus!
