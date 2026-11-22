//! The SHA-256 compression function (FIPS 180-4 §6.2.2), proven to compute
//! `spec::compress` block by block.
//!
//! The rounds keep the eight working variables in eight locals and never
//! move them: round t updates d and h in place, and the next round passes
//! the same locals rotated by one name (`tools/gen_rounds.py` writes the
//! calls). The message schedule is a 16-word window, W_t overwriting
//! W_{t-16}. This is the shape of the fastest portable implementations;
//! [`crate::cpu`] uses the CPU's SHA instructions where it has them.
// Rotations are written as FIPS 180-4 defines ROTR, (x >> n) | (x << 32 - n),
// since vstd has no specification of `rotate_right`. LLVM emits `ror` for both.
#![allow(clippy::manual_rotate)]
use crate::spec::{self, Vars, K};
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

#[inline(always)]
fn add(x: u32, y: u32) -> (r: u32)
    ensures
        r == spec::add(x, y),
{
    x.wrapping_add(y)
}

#[inline(always)]
fn big_sigma0(x: u32) -> (r: u32)
    ensures
        r == spec::big_sigma0(x),
{
    (x >> 2 | x << 30) ^ (x >> 13 | x << 19) ^ (x >> 22 | x << 10)
}

#[inline(always)]
fn big_sigma1(x: u32) -> (r: u32)
    ensures
        r == spec::big_sigma1(x),
{
    (x >> 6 | x << 26) ^ (x >> 11 | x << 21) ^ (x >> 25 | x << 7)
}

#[inline(always)]
fn small_sigma0(x: u32) -> (r: u32)
    ensures
        r == spec::small_sigma0(x),
{
    (x >> 7 | x << 25) ^ (x >> 18 | x << 14) ^ (x >> 3)
}

#[inline(always)]
fn small_sigma1(x: u32) -> (r: u32)
    ensures
        r == spec::small_sigma1(x),
{
    (x >> 17 | x << 15) ^ (x >> 19 | x << 13) ^ (x >> 10)
}

/// Ch with one operation fewer than its definition.
#[inline(always)]
fn ch(x: u32, y: u32, z: u32) -> (r: u32)
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
fn maj(x: u32, y: u32, z: u32) -> (r: u32)
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
fn round(a: u32, b: u32, c: u32, d: &mut u32, e: u32, f: u32, g: u32, h: &mut u32, k: u32, w: u32)
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
pub open spec fn window(w: Seq<u32>, m: Seq<u32>, lo: int, hi: int) -> bool {
    forall|k: int| lo <= k < hi ==> w[k % 16] == #[trigger] spec::schedule(m, k)
}

/// W_i from the window: the schedule's definition, unfolded once.
proof fn lemma_sched_value(w: Seq<u32>, m: Seq<u32>, i: int)
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
proof fn lemma_sched_window(w: Seq<u32>, v: Seq<u32>, m: Seq<u32>, i: int)
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
fn sched(w: &mut [u32; 16], i: usize, Ghost(m): Ghost<Seq<u32>>)
    requires
        16 <= i < 64,
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
proof fn lemma_round(v: Vars, m: Seq<u32>, t: nat)
    ensures
        spec::rounds(v, m, t + 1) == spec::round(spec::rounds(v, m, t), K[t as int], spec::schedule(m, t as int)),
{
}

/// The working variables, in locals once inlined.
#[derive(Clone, Copy)]
struct Regs {
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    e: u32,
    f: u32,
    g: u32,
    h: u32,
}

impl Regs {
    spec fn vars(&self) -> Vars {
        Vars { a: self.a, b: self.b, c: self.c, d: self.d, e: self.e, f: self.f, g: self.g, h: self.h }
    }
}

/// Rounds t to t + 7, for t < 16: W_t is M_t.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds8(r: &mut Regs, w: &[u32; 16], t: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u32>>)
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

/// Rounds t to t + 7, for 16 <= t < 64, computing each W_t first.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds8_sched(r: &mut Regs, w: &mut [u32; 16], t: usize, Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u32>>)
    requires
        t % 8 == 0,
        16 <= t,
        t + 8 <= 64,
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

/// The 64 rounds over block words `m`, of which the schedule knows only
/// that `w` starts as M0..M15.
#[verifier::spinoff_prover]
#[inline(always)]
fn rounds64(r: &mut Regs, w: &mut [u32; 16], Ghost(v0): Ghost<Vars>, Ghost(m): Ghost<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < 16 ==> old(w)@[i] == #[trigger] spec::schedule(m, i),
        old(r).vars() == v0,
    ensures
        final(r).vars() == spec::rounds(v0, m, 64),
{
    assert(r.vars() == spec::rounds(v0, m, 0));
    // Rounds 0 to 15: W_t is M_t.
    let mut t: usize = 0;
    while t < 16
        invariant
            t % 8 == 0,
            t <= 16,
            forall|i: int| 0 <= i < 16 ==> w@[i] == #[trigger] spec::schedule(m, i),
            r.vars() == spec::rounds(v0, m, t as nat),
        decreases 16 - t,
    {
        rounds8(r, w, t, Ghost(v0), Ghost(m));
        t = t + 8;
    }

    // Rounds 16 to 63, each computing W_t first.
    while t < 64
        invariant
            t % 8 == 0,
            16 <= t <= 64,
            window(w@, m, t - 16, t as int),
            r.vars() == spec::rounds(v0, m, t as nat),
        decreases 64 - t,
    {
        rounds8_sched(r, w, t, Ghost(v0), Ghost(m));
        t = t + 8;
    }
}

/// The word at byte `i`, most significant byte first. LLVM turns the four
/// loads into one load and a byte swap.
#[inline(always)]
fn load_be32(p: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= p@.len(),
    ensures
        r == spec::be32(p@, i as int),
{
    let _n = p.len();
    (get(p, i) as u32) << 24 | (get(p, i + 1) as u32) << 16 | (get(p, i + 2) as u32) << 8 | (get(p, i + 3) as u32)
}

/// The block's sixteen words M0..M15.
#[inline(always)]
fn load_block(p: &[u8], off: usize) -> (w: [u32; 16])
    requires
        off + 64 <= p@.len(),
    ensures
        forall|i: int| 0 <= i < 16 ==> w@[i] == #[trigger] spec::words(p@.subrange(off as int, off + 64))[i],
{
    let _n = p.len();
    let ghost blk = p@.subrange(off as int, off + 64);
    let mut w = [0u32; 16];
    let mut j: usize = 0;
    while j < 16
        invariant
            j <= 16,
            off + 64 <= p@.len(),
            p@.len() <= usize::MAX,
            blk == p@.subrange(off as int, off + 64),
            forall|i: int| 0 <= i < j ==> w@[i] == #[trigger] spec::words(blk)[i],
        decreases 16 - j,
    {
        let x = load_be32(p, off + 4 * j);
        proof {
            assert(spec::be32(p@, off + 4 * j) == spec::be32(blk, 4 * j as int));
        }
        w[j] = x;
        j = j + 1;
    }
    w
}

/// H(i) from H(i-1) = `st` and the 64-byte block at `off`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn compress_block(st: &mut [u32; 8], p: &[u8], off: usize)
    requires
        off + 64 <= p@.len(),
    ensures
        final(st)@ == spec::compress(old(st)@, p@.subrange(off as int, off + 64)),
{
    let ghost blk = p@.subrange(off as int, off + 64);
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

    rounds64(&mut r, &mut w, Ghost(v0), Ghost(m));

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

/// H(n) from H(0) = `st` over the `n = p.len() / 64` whole blocks of `p`;
/// bytes after the last whole block are not read.
#[inline(always)]
pub fn compress_blocks(st: &mut [u32; 8], p: &[u8])
    ensures
        final(st)@ == spec::hash_blocks(old(st)@, p@, (p@.len() / 64) as nat),
{
    let ghost h0 = st@;
    let n = p.len() / 64;
    let mut i: usize = 0;
    while i < n
        invariant
            n == p@.len() / 64,
            p@.len() <= usize::MAX,
            i <= n,
            st@ == spec::hash_blocks(h0, p@, i as nat),
        decreases n - i,
    {
        compress_block(st, p, 64 * i);
        i = i + 1;
    }
}

} // verus!
