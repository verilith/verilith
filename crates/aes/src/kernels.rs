//! The 128-bit kernels, proven once over [`Isa`]'s operations: GHASH
//! multiplication and reduction, one block, eight blocks and one block of
//! CTR, and GHASH of up to sixteen blocks with one reduction.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::arch::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

pub open spec fn rev_const() -> u128 {
    0x000102030405060708090a0b0c0d0e0fu128
}

pub open spec fn ctr_const() -> u128 {
    0x0c0d0e0f0b0a09080706050403020100u128
}

pub proof fn lemma_masks()
    ensures
        bytes16(rev_const()) == rev_mask(),
        bytes16(ctr_const()) == ctr_mask(),
{
    {
        let v = rev_const();
        assert((v >> 0u128) as u8 == 15u8 && (v >> 8u128) as u8 == 14u8 && (v >> 16u128) as u8 == 13u8 && (v >> 24u128) as u8 == 12u8 && (v >> 32u128) as u8 == 11u8 && (v >> 40u128) as u8 == 10u8 && (v >> 48u128) as u8 == 9u8 && (v >> 56u128) as u8 == 8u8 && (v >> 64u128) as u8 == 7u8 && (v >> 72u128) as u8 == 6u8 && (v >> 80u128) as u8 == 5u8 && (v >> 88u128) as u8 == 4u8 && (v >> 96u128) as u8 == 3u8 && (v >> 104u128) as u8 == 2u8 && (v >> 112u128) as u8 == 1u8 && (v >> 120u128) as u8 == 0u8) by (bit_vector)
            requires
                v == 0x000102030405060708090a0b0c0d0e0fu128,
        ;
        assert(bytes16(v) =~= rev_mask());
    }
    {
        let v = ctr_const();
        assert((v >> 0u128) as u8 == 0u8 && (v >> 8u128) as u8 == 1u8 && (v >> 16u128) as u8 == 2u8 && (v >> 24u128) as u8 == 3u8 && (v >> 32u128) as u8 == 4u8 && (v >> 40u128) as u8 == 5u8 && (v >> 48u128) as u8 == 6u8 && (v >> 56u128) as u8 == 7u8 && (v >> 64u128) as u8 == 8u8 && (v >> 72u128) as u8 == 9u8 && (v >> 80u128) as u8 == 10u8 && (v >> 88u128) as u8 == 11u8 && (v >> 96u128) as u8 == 15u8 && (v >> 104u128) as u8 == 14u8 && (v >> 112u128) as u8 == 13u8 && (v >> 120u128) as u8 == 12u8) by (bit_vector)
            requires
                v == 0x0c0d0e0f0b0a09080706050403020100u128,
        ;
        assert(bytes16(v) =~= ctr_mask());
    }
}

#[inline(always)]
pub fn rev_x<A: Isa>() -> (r: A::R)
    requires
        A::ok(),
    ensures
        xb::<A>(r) == rev_mask(),
{
    proof {
        lemma_masks();
    }
    A::set(0x000102030405060708090a0b0c0d0e0f)
}

#[inline(always)]
pub fn ctr_x<A: Isa>() -> (r: A::R)
    requires
        A::ok(),
    ensures
        xb::<A>(r) == ctr_mask(),
{
    proof {
        lemma_masks();
    }
    A::set(0x0c0d0e0f0b0a09080706050403020100)
}

/// The block at `d[i..i + 16]`, as GHASH reads it.
#[inline(always)]
pub fn load_be<A: Isa>(d: &[u8], i: usize, rev: A::R) -> (r: A::R)
    requires
        A::ok(),
        i + 16 <= d@.len(),
        xb::<A>(rev) == rev_mask(),
    ensures
        A::v(r) == be128(d@.subrange(i as int, i + 16)),
{
    let x = A::load(d, i);
    let r = A::pshufb(x, rev);
    proof {
        lemma_rev(A::v(x), A::v(r));
    }
    r
}

// ---------------------------------------------------------------------------
// GF(2^128)
// ---------------------------------------------------------------------------

proof fn lemma_shl1(a: u128)
    ensures
        sll64x2(a, 1) ^ (srl64x2(a, 63) << 64u128) == a << 1u128,
{
    assert(sll64x2(a, 1) == ((((a >> 64u128) as u64) << 1u64) as u128) << 64u128 | ((((a as u64) << 1u64)) as u128));
    assert(srl64x2(a, 63) == ((((a >> 64u128) as u64) >> 63u64) as u128) << 64u128 | (((a as u64) >> 63u64) as u128));
    assert((((((a >> 64u128) as u64) << 1u64) as u128) << 64u128 | ((((a as u64) << 1u64)) as u128)) ^ ((((((a >> 64u128)
        as u64) >> 63u64) as u128) << 64u128 | (((a as u64) >> 63u64) as u128)) << 64u128) == a << 1u128) by (bit_vector);
}

/// [`red`] with the 64-bit lane shifts SSE has.
#[inline(always)]
pub fn red_x<A: Isa>(lo: A::R, hi: A::R) -> (r: A::R)
    requires
        A::ok(),
    ensures
        A::v(r) == red((A::v(lo), A::v(hi))),
{
    let cl = A::srl64::<63>(lo);
    let ch = A::srl64::<63>(hi);
    let h = A::xor(A::sll64::<1>(lo), A::bsll8(cl));
    let hh = A::xor(A::xor(A::sll64::<1>(hi), A::bsll8(ch)), A::bsrl8(cl));
    let e = A::bsll8(A::xor(A::xor(A::sll64::<63>(h), A::sll64::<62>(h)), A::sll64::<57>(h)));
    let f = A::xor(h, e);
    let g1 = A::xor(A::xor(A::srl64::<1>(f), A::srl64::<2>(f)), A::srl64::<7>(f));
    let g2 = A::bsrl8(A::xor(A::xor(A::sll64::<63>(f), A::sll64::<62>(f)), A::sll64::<57>(f)));
    let r = A::xor(A::xor(hh, f), A::xor(g1, g2));
    proof {
        let (l, u) = (A::v(lo), A::v(hi));
        lemma_shl1(l);
        assert(A::v(h) == l << 1u128);
        assert(A::v(hh) == (u << 1u128) | (l >> 127u128)) by {
            lemma_shl1(u);
            let a = srl64x2(l, 63);
            assert(a == ((((l >> 64u128) as u64) >> 63u64) as u128) << 64u128 | (((l as u64) >> 63u64) as u128));
            assert((u << 1u128) ^ (a >> 64u128) == (u << 1u128) | (l >> 127u128)) by (bit_vector)
                requires
                    a == ((((l >> 64u128) as u64) >> 63u64) as u128) << 64u128 | (((l as u64) >> 63u64) as u128),
            ;
        };
        let hv = A::v(h);
        assert(A::v(e) == (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128)) by {
            assert(((sll64x2(hv, 63) ^ sll64x2(hv, 62)) ^ sll64x2(hv, 57)) << 64u128 == (hv << 127u128) ^ (hv << 126u128)
                ^ (hv << 121u128)) by (bit_vector)
                requires
                    sll64x2(hv, 63) == ((((hv >> 64u128) as u64) << 63u64) as u128) << 64u128 | ((((hv as u64)
                        << 63u64)) as u128),
                    sll64x2(hv, 62) == ((((hv >> 64u128) as u64) << 62u64) as u128) << 64u128 | ((((hv as u64)
                        << 62u64)) as u128),
                    sll64x2(hv, 57) == ((((hv >> 64u128) as u64) << 57u64) as u128) << 64u128 | ((((hv as u64)
                        << 57u64)) as u128),
            ;
        };
        let fv = A::v(f);
        let ev = A::v(e);
        assert(fv == hv ^ (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128)) by (bit_vector)
            requires
                fv == hv ^ ev,
                ev == (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128),
        ;
        assert(A::v(g1) ^ A::v(g2) == (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128)) by {
            assert(((srl64x2(fv, 1) ^ srl64x2(fv, 2)) ^ srl64x2(fv, 7)) ^ (((sll64x2(fv, 63) ^ sll64x2(fv, 62)) ^ sll64x2(
                fv,
                57,
            )) >> 64u128) == (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128)) by (bit_vector)
                requires
                    sll64x2(fv, 63) == ((((fv >> 64u128) as u64) << 63u64) as u128) << 64u128 | ((((fv as u64)
                        << 63u64)) as u128),
                    sll64x2(fv, 62) == ((((fv >> 64u128) as u64) << 62u64) as u128) << 64u128 | ((((fv as u64)
                        << 62u64)) as u128),
                    sll64x2(fv, 57) == ((((fv >> 64u128) as u64) << 57u64) as u128) << 64u128 | ((((fv as u64)
                        << 57u64)) as u128),
                    srl64x2(fv, 1) == ((((fv >> 64u128) as u64) >> 1u64) as u128) << 64u128 | ((((fv as u64) >> 1u64))
                        as u128),
                    srl64x2(fv, 2) == ((((fv >> 64u128) as u64) >> 2u64) as u128) << 64u128 | ((((fv as u64) >> 2u64))
                        as u128),
                    srl64x2(fv, 7) == ((((fv >> 64u128) as u64) >> 7u64) as u128) << 64u128 | ((((fv as u64) >> 7u64))
                        as u128),
            ;
        };
        let hhv = A::v(hh);
        let g = A::v(g1) ^ A::v(g2);
        assert((hhv ^ fv) ^ g == hhv ^ fv ^ (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128)) by (bit_vector)
            requires
                g == (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128),
        ;
        assert(A::v(r) == (hhv ^ fv) ^ (A::v(g1) ^ A::v(g2)));
    }
    r
}

/// The three parts of the carry-less product: low, middle, high.
#[inline(always)]
pub fn prod_x<A: Isa>(a: A::R, b: A::R) -> (r: (A::R, A::R, A::R))
    requires
        A::ok(),
    ensures
        A::v(r.0) == clmul(lo64(A::v(a)), lo64(A::v(b))),
        A::v(r.1) == mid(A::v(a), A::v(b)),
        A::v(r.2) == clmul(hi64(A::v(a)), hi64(A::v(b))),
{
    let l = A::clmul::<0x00>(a, b);
    let h = A::clmul::<0x11>(a, b);
    let m1 = A::clmul::<0x10>(a, b);
    let m2 = A::clmul::<0x01>(a, b);
    let m = A::xor(m1, m2);
    proof {
        assert(0x00i32 & 1 == 0 && 0x00i32 & 0x10 == 0) by (bit_vector);
        assert(0x11i32 & 1 != 0 && 0x11i32 & 0x10 != 0) by (bit_vector);
        assert(0x10i32 & 1 == 0 && 0x10i32 & 0x10 != 0) by (bit_vector);
        assert(0x01i32 & 1 != 0 && 0x01i32 & 0x10 == 0) by (bit_vector);
    }
    (l, m, h)
}

/// The halves of a product from its parts.
#[inline(always)]
pub fn join_x<A: Isa>(l: A::R, m: A::R, h: A::R) -> (r: (A::R, A::R))
    requires
        A::ok(),
    ensures
        (A::v(r.0), A::v(r.1)) == join(A::v(l), A::v(m), A::v(h)),
{
    (A::xor(l, A::bsll8(m)), A::xor(h, A::bsrl8(m)))
}

/// X • Y.
#[inline(always)]
pub fn mul_x<A: Isa>(a: A::R, b: A::R) -> (r: A::R)
    requires
        A::ok(),
    ensures
        A::v(r) == gf_mul(A::v(a), A::v(b)),
{
    let (l, m, h) = prod_x::<A>(a, b);
    let (lo, hi) = join_x::<A>(l, m, h);
    proof {
        lemma_gf_mul_prod(A::v(a), A::v(b));
    }
    red_x::<A>(lo, hi)
}

// ---------------------------------------------------------------------------
// AES
// ---------------------------------------------------------------------------

/// One block: CIPHER(x) with the round keys `rk`.
#[inline(always)]
pub fn enc_x<A: Isa>(rk: &[u128; 15], nr: usize, x: A::R, Ghost(key): Ghost<Seq<u8>>) -> (r: A::R)
    requires
        A::ok(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
    ensures
        xb::<A>(r) == cipher(key, xb::<A>(x)),
{
    let ghost input = xb::<A>(x);
    let mut s = A::first(x, rk, Ghost(key));
    let mut r: usize = 1;
    while r < nr
        invariant
            A::ok(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            input.len() == 16,
            A::st(s, key, input, r as int),
        decreases nr - r,
    {
        s = A::round(s, rk, r, Ghost(key), Ghost(input));
        r = r + 1;
    }
    A::last(s, rk, nr, Ghost(key), Ghost(input))
}

/// The word in every column.
pub open spec fn bcast(w: u32) -> u128 {
    (w as u128) | (w as u128) << 32u128 | (w as u128) << 64u128 | (w as u128) << 96u128
}

pub proof fn lemma_bcast(w: u32)
    ensures
        forall|i: int| 0 <= i < 16 ==> #[trigger] bytes16(bcast(w))[i] == wbyte(w, i % 4),
        shift_rows(bytes16(bcast(w))) == bytes16(bcast(w)),
{
    let v = bcast(w);
    assert((v >> 0u128) as u8 == (w >> 0u32) as u8 && (v >> 8u128) as u8 == (w >> 8u32) as u8 && (v >> 16u128) as u8 == (w >> 16u32) as u8 && (v >> 24u128) as u8 == (w >> 24u32) as u8 && (v >> 32u128) as u8 == (w >> 0u32) as u8 && (v >> 40u128) as u8 == (w >> 8u32) as u8 && (v >> 48u128) as u8 == (w >> 16u32) as u8 && (v >> 56u128) as u8 == (w >> 24u32) as u8 && (v >> 64u128) as u8 == (w >> 0u32) as u8 && (v >> 72u128) as u8 == (w >> 8u32) as u8 && (v >> 80u128) as u8 == (w >> 16u32) as u8 && (v >> 88u128) as u8 == (w >> 24u32) as u8 && (v >> 96u128) as u8 == (w >> 0u32) as u8 && (v >> 104u128) as u8 == (w >> 8u32) as u8 && (v >> 112u128) as u8 == (w >> 16u32) as u8 && (v >> 120u128) as u8 == (w >> 24u32) as u8) by (bit_vector)
        requires
            v == (w as u128) | (w as u128) << 32u128 | (w as u128) << 64u128 | (w as u128) << 96u128,
    ;
    let b = bytes16(v);
    assert forall|i: int| 0 <= i < 16 implies #[trigger] b[i] == wbyte(w, i % 4) by {
        assert(b[i] == (v >> (8 * i) as u128) as u8);
    };
    assert forall|i: int| 0 <= i < 16 implies #[trigger] shift_rows(b)[i] == b[i] by {
        let j = i % 4 + 4 * ((i / 4 + i % 4) % 4);
        assert(j % 4 == i % 4);
    };
    assert(shift_rows(b) =~= b);
}

pub proof fn lemma_zero_bytes()
    ensures
        bytes16(0) == Seq::new(16, |i: int| 0u8),
{
    assert forall|i: int| 0 <= i < 16 implies #[trigger] bytes16(0)[i] == 0u8 by {
        let s = (8 * i) as u128;
        assert((0u128 >> s) as u8 == 0) by (bit_vector);
    };
    assert(bytes16(0) =~= Seq::new(16, |i: int| 0u8));
}

pub proof fn lemma_low_word(sv: u128)
    ensures
        sv as u32 == word(bytes16(sv)[0], bytes16(sv)[1], bytes16(sv)[2], bytes16(sv)[3]),
{
    assert(bytes16(sv)[0] == (sv >> 0u128) as u8);
    assert(bytes16(sv)[1] == (sv >> 8u128) as u8);
    assert(bytes16(sv)[2] == (sv >> 16u128) as u8);
    assert(bytes16(sv)[3] == (sv >> 24u128) as u8);
    assert(sv as u32 == word((sv >> 0u128) as u8, (sv >> 8u128) as u8, (sv >> 16u128) as u8, (sv >> 24u128) as u8))
        by (bit_vector);
}

/// Keystream byte k from counter c: byte k % 16 of CIPHER of the
/// counter block for c + k / 16.
pub open spec fn ks(key: Seq<u8>, iv: Seq<u8>, c: int, k: int) -> u8 {
    cipher(key, counter_block(iv, c + k / 16))[k % 16]
}

/// The blocks at `d[i..i + 16 n]`, as GHASH reads them.
pub open spec fn blocks_at(d: Seq<u8>, i: int, n: int) -> Seq<u128> {
    Seq::new(n as nat, |j: int| be128(d.subrange(i + 16 * j, i + 16 * j + 16)))
}

/// `hr[m]` is H^(16 - m): the powers in the order the 16-block GHASH
/// multiplies the blocks by.
pub open spec fn rpowers_ok(h: u128, hr: Seq<u128>) -> bool {
    hr.len() == 16 && forall|m: int| 0 <= m < 16 ==> #[trigger] hr[m] == pow(h, (16 - m) as nat)
}

/// `hp[m]` is H^(m + 1).
pub open spec fn powers_ok(h: u128, hp: Seq<u128>) -> bool {
    hp.len() == 16 && forall|m: int| 0 <= m < 16 ==> #[trigger] hp[m] == pow(h, (m + 1) as nat)
}

/// Adds the product of `x` and `k` to the unreduced sum (l, m, h).
#[verifier::spinoff_prover]
#[inline(always)]
pub fn acc_x<A: Isa>(l: A::R, m: A::R, h: A::R, x: A::R, k: A::R) -> (r: (A::R, A::R, A::R))
    requires
        A::ok(),
    ensures
        red(join(A::v(r.0), A::v(r.1), A::v(r.2))) == red(join(A::v(l), A::v(m), A::v(h))) ^ gf_mul(A::v(x), A::v(k)),
{
    let (pl, pm, ph) = prod_x::<A>(x, k);
    proof {
        lemma_join_xor(A::v(l), A::v(m), A::v(h), A::v(pl), A::v(pm), A::v(ph));
        lemma_red_xor(join(A::v(l), A::v(m), A::v(h)), join(A::v(pl), A::v(pm), A::v(ph)));
        lemma_gf_mul_prod(A::v(x), A::v(k));
    }
    (A::xor(l, pl), A::xor(m, pm), A::xor(h, ph))
}

/// GHASH of n <= 8 blocks at `d[i..]`, from `acc`, with one reduction:
/// the sum of the blocks times H^n .. H^1 (the first with `acc` added).
#[inline(always)]
pub fn ghash_x<A: Isa>(accr: A::R, d: &[u8], i: usize, n: usize, hp: &[u128; 16], Ghost(h): Ghost<u128>) -> (r: A::R)
    requires
        A::ok(),
        1 <= n <= 16,
        i + 16 * n <= d@.len(),
        powers_ok(h, hp@),
    ensures
        A::v(r) == ghash_from(h, A::v(accr), blocks_at(d@, i as int, n as int)),
{
    let ghost acc = A::v(accr);
    let ghost xs = blocks_at(d@, i as int, n as int);
    let ghost ys = xs.update(0, acc ^ xs[0]);
    let _len = d.len();
    let rev = rev_x::<A>();
    let z = A::set(0);
    let mut l = z;
    let mut m = z;
    let mut hh = z;
    proof {
        assert(0u128 ^ (0u128 << 64u128) == 0 && 0u128 ^ (0u128 >> 64u128) == 0) by (bit_vector);
        lemma_red_zero();
        assert(ys.take(0) =~= Seq::<u128>::empty());
    }
    let mut j: usize = 0;
    let mut o: usize = i;
    while j < n
        invariant
            A::ok(),
            1 <= n <= 16,
            i + 16 * n <= d@.len(),
            powers_ok(h, hp@),
            xb::<A>(rev) == rev_mask(),
            xs == blocks_at(d@, i as int, n as int),
            ys == xs.update(0, acc ^ xs[0]),
            acc == A::v(accr),
            j <= n,
            d@.len() <= usize::MAX,
            o == i + 16 * j,
            red(join(A::v(l), A::v(m), A::v(hh))) == dsum(h, ys.take(j as int), n as nat),
        decreases n - j,
    {
        assert(o + 16 <= d@.len()) by (nonlinear_arith)
            requires
                o == i + 16 * j,
                i + 16 * n <= d@.len(),
                j < n,
        ;
        let mut x = load_be::<A>(d, o, rev);
        if j == 0 {
            x = A::xor(x, accr);
            proof {
                let a = xs[0];
                assert(a ^ acc == acc ^ a) by (bit_vector);
            }
        }
        assert(A::v(x) == ys[j as int]);
        let k = A::load_u128(hp, n - 1 - j);
        assert(A::v(k) == pow(h, (n - j) as nat));
        let ghost old_sum = red(join(A::v(l), A::v(m), A::v(hh)));
        let (l1, m1, h1) = acc_x::<A>(l, m, hh, x, k);
        l = l1;
        m = m1;
        hh = h1;
        proof {
            assert(ys.take(j + 1).drop_last() =~= ys.take(j as int));
            assert(ys.take(j + 1).last() == ys[j as int]);
        }
        j = j + 1;
        o = o + 16;
    }
    proof {
        assert(ys.take(n as int) =~= ys);
        lemma_ghash_dsum(h, ys);
        lemma_ghash_from_first(h, acc, xs);
    }
    let (lo, hi) = join_x::<A>(l, m, hh);
    red_x::<A>(lo, hi)
}

/// `buf` is `b0` with `buf[i..i + 16 m]` encrypted from counter c.
#[verifier::opaque]
pub open spec fn ctr_done(buf: Seq<u8>, b0: Seq<u8>, i: int, m: int, key: Seq<u8>, iv: Seq<u8>, c: int) -> bool {
    &&& buf.len() == b0.len()
    &&& forall|k: int|
        0 <= k < buf.len() ==> #[trigger] buf[k] == if i <= k < i + 16 * m {
            b0[k] ^ ks(key, iv, c, k - i)
        } else {
            b0[k]
        }
}

/// The counter block for c + j, ready for round 1.
#[inline(always)]
pub fn start_x<A: Isa>(ctr: A::R, cmask: A::R, rk: &[u128; 15], j: u32, Ghost(key): Ghost<Seq<u8>>, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>) -> (r: A::R)
    requires
        A::ok(),
        rk_ok(key, rk@),
        xb::<A>(cmask) == ctr_mask(),
        ctr_reg_ok(A::v(ctr), iv, c),
        c >= 0,
    ensures
        A::st(r, key, counter_block(iv, c + j), 1),
{
    let cj = A::add32(ctr, A::set((j as u128) << 96));
    let b = A::pshufb(cj, cmask);
    proof {
        lemma_ctr_add(A::v(ctr), iv, c, j);
        lemma_ctr_block(A::v(cj), iv, c + j);
    }
    A::first(b, rk, Ghost(key))
}

/// Block j of a CTR run: XOR the keystream block `s` into `buf`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn xor_block<A: Isa>(
    buf: &mut [u8],
    i: usize,
    j: usize,
    o: usize,
    s: A::R,
    Ghost(b0): Ghost<Seq<u8>>,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        A::ok(),
        ctr_done(old(buf)@, b0, i as int, j as int, key, iv, c),
        old(buf)@.len() == b0.len(),
        i + 16 * (j + 1) <= b0.len(),
        o == i + 16 * j,
        xb::<A>(s) == cipher(key, counter_block(iv, c + j)),
    ensures
        ctr_done(final(buf)@, b0, i as int, j + 1, key, iv, c),
        final(buf)@.len() == b0.len(),
{
    let p = A::load(buf, o);
    let x = A::xor(p, s);
    proof {
        lemma_xor_bytes16(A::v(p), A::v(s));
    }
    A::store(buf, o, x);
    proof {
        reveal(ctr_done);
        assert forall|k: int| 0 <= k < buf@.len() implies #[trigger] buf@[k] == if i <= k < i + 16 * (j + 1) {
            b0[k] ^ ks(key, iv, c, k - i)
        } else {
            b0[k]
        } by {
            if o <= k < o + 16 {
                assert((k - i) / 16 == j && (k - i) % 16 == k - o) by (nonlinear_arith)
                    requires
                        o == i + 16 * j,
                        o <= k < o + 16,
                ;
                assert(xb::<A>(p)[k - o] == b0[k]);
            }
        };
    }
}

/// The keystream of 8 blocks: CIPHER of the counter blocks for c, c + 1, ...
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ks8_x<A: Isa>(
    rk: &[u128; 15],
    nr: usize,
    ctr: A::R,
    cmask: A::R,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
) -> (r: (A::R, A::R, A::R, A::R, A::R, A::R, A::R, A::R,))
    requires
        A::ok(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb::<A>(cmask) == ctr_mask(),
        ctr_reg_ok(A::v(ctr), iv, c),
        c >= 0,
    ensures
        xb::<A>(r.0) == cipher(key, counter_block(iv, c + 0)),
        xb::<A>(r.1) == cipher(key, counter_block(iv, c + 1)),
        xb::<A>(r.2) == cipher(key, counter_block(iv, c + 2)),
        xb::<A>(r.3) == cipher(key, counter_block(iv, c + 3)),
        xb::<A>(r.4) == cipher(key, counter_block(iv, c + 4)),
        xb::<A>(r.5) == cipher(key, counter_block(iv, c + 5)),
        xb::<A>(r.6) == cipher(key, counter_block(iv, c + 6)),
        xb::<A>(r.7) == cipher(key, counter_block(iv, c + 7)),
{
    let ghost in0 = counter_block(iv, c + 0);
    proof { lemma_counter_block_len(iv, c + 0); }
    let mut s0 = start_x::<A>(ctr, cmask, rk, 0, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in1 = counter_block(iv, c + 1);
    proof { lemma_counter_block_len(iv, c + 1); }
    let mut s1 = start_x::<A>(ctr, cmask, rk, 1, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in2 = counter_block(iv, c + 2);
    proof { lemma_counter_block_len(iv, c + 2); }
    let mut s2 = start_x::<A>(ctr, cmask, rk, 2, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in3 = counter_block(iv, c + 3);
    proof { lemma_counter_block_len(iv, c + 3); }
    let mut s3 = start_x::<A>(ctr, cmask, rk, 3, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in4 = counter_block(iv, c + 4);
    proof { lemma_counter_block_len(iv, c + 4); }
    let mut s4 = start_x::<A>(ctr, cmask, rk, 4, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in5 = counter_block(iv, c + 5);
    proof { lemma_counter_block_len(iv, c + 5); }
    let mut s5 = start_x::<A>(ctr, cmask, rk, 5, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in6 = counter_block(iv, c + 6);
    proof { lemma_counter_block_len(iv, c + 6); }
    let mut s6 = start_x::<A>(ctr, cmask, rk, 6, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in7 = counter_block(iv, c + 7);
    proof { lemma_counter_block_len(iv, c + 7); }
    let mut s7 = start_x::<A>(ctr, cmask, rk, 7, Ghost(key), Ghost(iv), Ghost(c));
    let mut r: usize = 1;
    while r < nr
        invariant
            A::ok(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            in0.len() == 16,
            A::st(s0, key, in0, r as int),
            in1.len() == 16,
            A::st(s1, key, in1, r as int),
            in2.len() == 16,
            A::st(s2, key, in2, r as int),
            in3.len() == 16,
            A::st(s3, key, in3, r as int),
            in4.len() == 16,
            A::st(s4, key, in4, r as int),
            in5.len() == 16,
            A::st(s5, key, in5, r as int),
            in6.len() == 16,
            A::st(s6, key, in6, r as int),
            in7.len() == 16,
            A::st(s7, key, in7, r as int),
        decreases nr - r,
    {
        s0 = A::round(s0, rk, r, Ghost(key), Ghost(in0));
        s1 = A::round(s1, rk, r, Ghost(key), Ghost(in1));
        s2 = A::round(s2, rk, r, Ghost(key), Ghost(in2));
        s3 = A::round(s3, rk, r, Ghost(key), Ghost(in3));
        s4 = A::round(s4, rk, r, Ghost(key), Ghost(in4));
        s5 = A::round(s5, rk, r, Ghost(key), Ghost(in5));
        s6 = A::round(s6, rk, r, Ghost(key), Ghost(in6));
        s7 = A::round(s7, rk, r, Ghost(key), Ghost(in7));
        r = r + 1;
    }
    s0 = A::last(s0, rk, nr, Ghost(key), Ghost(in0));
    s1 = A::last(s1, rk, nr, Ghost(key), Ghost(in1));
    s2 = A::last(s2, rk, nr, Ghost(key), Ghost(in2));
    s3 = A::last(s3, rk, nr, Ghost(key), Ghost(in3));
    s4 = A::last(s4, rk, nr, Ghost(key), Ghost(in4));
    s5 = A::last(s5, rk, nr, Ghost(key), Ghost(in5));
    s6 = A::last(s6, rk, nr, Ghost(key), Ghost(in6));
    s7 = A::last(s7, rk, nr, Ghost(key), Ghost(in7));
    (s0, s1, s2, s3, s4, s5, s6, s7,)
}

/// 8 blocks of CTR: `buf[i..i + 128]` XOR the keystream from counter c.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ctr8_x<A: Isa>(
    rk: &[u128; 15],
    nr: usize,
    ctr: A::R,
    cmask: A::R,
    buf: &mut [u8],
    i: usize,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        A::ok(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb::<A>(cmask) == ctr_mask(),
        ctr_reg_ok(A::v(ctr), iv, c),
        c >= 0,
        i + 128 <= old(buf)@.len(),
    ensures
        ctr_done(final(buf)@, old(buf)@, i as int, 8, key, iv, c),
        final(buf)@.len() == old(buf)@.len(),
{
    let ks = ks8_x::<A>(rk, nr, ctr, cmask, Ghost(key), Ghost(iv), Ghost(c));
    let _len = buf.len();
    let ghost b0 = buf@;
    proof {
        reveal(ctr_done);
        assert(ctr_done(buf@, b0, i as int, 0, key, iv, c));
    }
    xor_block::<A>(buf, i, 0, i + 0, ks.0, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 1, i + 16, ks.1, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 2, i + 32, ks.2, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 3, i + 48, ks.3, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 4, i + 64, ks.4, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 5, i + 80, ks.5, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 6, i + 96, ks.6, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block::<A>(buf, i, 7, i + 112, ks.7, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
}

/// The keystream of 1 blocks: CIPHER of the counter blocks for c, c + 1, ...
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ks1_x<A: Isa>(
    rk: &[u128; 15],
    nr: usize,
    ctr: A::R,
    cmask: A::R,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
) -> (r: (A::R,))
    requires
        A::ok(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb::<A>(cmask) == ctr_mask(),
        ctr_reg_ok(A::v(ctr), iv, c),
        c >= 0,
    ensures
        xb::<A>(r.0) == cipher(key, counter_block(iv, c + 0)),
{
    let ghost in0 = counter_block(iv, c + 0);
    proof { lemma_counter_block_len(iv, c + 0); }
    let mut s0 = start_x::<A>(ctr, cmask, rk, 0, Ghost(key), Ghost(iv), Ghost(c));
    let mut r: usize = 1;
    while r < nr
        invariant
            A::ok(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            in0.len() == 16,
            A::st(s0, key, in0, r as int),
        decreases nr - r,
    {
        s0 = A::round(s0, rk, r, Ghost(key), Ghost(in0));
        r = r + 1;
    }
    s0 = A::last(s0, rk, nr, Ghost(key), Ghost(in0));
    (s0,)
}

/// 1 blocks of CTR: `buf[i..i + 16]` XOR the keystream from counter c.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ctr1_x<A: Isa>(
    rk: &[u128; 15],
    nr: usize,
    ctr: A::R,
    cmask: A::R,
    buf: &mut [u8],
    i: usize,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        A::ok(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb::<A>(cmask) == ctr_mask(),
        ctr_reg_ok(A::v(ctr), iv, c),
        c >= 0,
        i + 16 <= old(buf)@.len(),
    ensures
        ctr_done(final(buf)@, old(buf)@, i as int, 1, key, iv, c),
        final(buf)@.len() == old(buf)@.len(),
{
    let ks = ks1_x::<A>(rk, nr, ctr, cmask, Ghost(key), Ghost(iv), Ghost(c));
    let _len = buf.len();
    let ghost b0 = buf@;
    proof {
        reveal(ctr_done);
        assert(ctr_done(buf@, b0, i as int, 0, key, iv, c));
    }
    xor_block::<A>(buf, i, 0, i + 0, ks.0, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
}

} // verus!
