//! The 128-bit x86-64 kernels (AES-NI, PCLMULQDQ), proven over the
//! instruction wrappers of [`crate::x86`]: the key expansion, one block,
//! eight blocks of CTR, and GHASH of up to eight blocks with one
//! reduction.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::x86::*;
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
pub fn rev_x() -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == rev_mask(),
{
    proof {
        lemma_masks();
    }
    x_set(0x000102030405060708090a0b0c0d0e0f)
}

#[inline(always)]
pub fn ctr_x() -> (r: X128)
    requires
        ni(),
    ensures
        xb(r) == ctr_mask(),
{
    proof {
        lemma_masks();
    }
    x_set(0x0c0d0e0f0b0a09080706050403020100)
}

/// The block at `d[i..i + 16]`, as GHASH reads it.
#[inline(always)]
pub fn load_be(d: &[u8], i: usize, rev: X128) -> (r: X128)
    requires
        ni(),
        i + 16 <= d@.len(),
        xb(rev) == rev_mask(),
    ensures
        xv(r) == be128(d@.subrange(i as int, i + 16)),
{
    let x = x_load(d, i);
    let r = x_pshufb(x, rev);
    proof {
        lemma_rev(xv(x), xv(r));
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
pub fn red_x(lo: X128, hi: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == red((xv(lo), xv(hi))),
{
    let cl = x_srl64::<63>(lo);
    let ch = x_srl64::<63>(hi);
    let h = x_xor(x_sll64::<1>(lo), x_bsll8(cl));
    let hh = x_xor(x_xor(x_sll64::<1>(hi), x_bsll8(ch)), x_bsrl8(cl));
    let e = x_bsll8(x_xor(x_xor(x_sll64::<63>(h), x_sll64::<62>(h)), x_sll64::<57>(h)));
    let f = x_xor(h, e);
    let g1 = x_xor(x_xor(x_srl64::<1>(f), x_srl64::<2>(f)), x_srl64::<7>(f));
    let g2 = x_bsrl8(x_xor(x_xor(x_sll64::<63>(f), x_sll64::<62>(f)), x_sll64::<57>(f)));
    let r = x_xor(x_xor(hh, f), x_xor(g1, g2));
    proof {
        let (l, u) = (xv(lo), xv(hi));
        lemma_shl1(l);
        assert(xv(h) == l << 1u128);
        assert(xv(hh) == (u << 1u128) | (l >> 127u128)) by {
            lemma_shl1(u);
            let a = srl64x2(l, 63);
            assert(a == ((((l >> 64u128) as u64) >> 63u64) as u128) << 64u128 | (((l as u64) >> 63u64) as u128));
            assert((u << 1u128) ^ (a >> 64u128) == (u << 1u128) | (l >> 127u128)) by (bit_vector)
                requires
                    a == ((((l >> 64u128) as u64) >> 63u64) as u128) << 64u128 | (((l as u64) >> 63u64) as u128),
            ;
        };
        let hv = xv(h);
        assert(xv(e) == (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128)) by {
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
        let fv = xv(f);
        let ev = xv(e);
        assert(fv == hv ^ (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128)) by (bit_vector)
            requires
                fv == hv ^ ev,
                ev == (hv << 127u128) ^ (hv << 126u128) ^ (hv << 121u128),
        ;
        assert(xv(g1) ^ xv(g2) == (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128)) by {
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
        let hhv = xv(hh);
        let g = xv(g1) ^ xv(g2);
        assert((hhv ^ fv) ^ g == hhv ^ fv ^ (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128)) by (bit_vector)
            requires
                g == (fv >> 1u128) ^ (fv >> 2u128) ^ (fv >> 7u128),
        ;
        assert(xv(r) == (hhv ^ fv) ^ (xv(g1) ^ xv(g2)));
    }
    r
}

/// The three parts of the carry-less product: low, middle, high.
#[inline(always)]
pub fn prod_x(a: X128, b: X128) -> (r: (X128, X128, X128))
    requires
        ni(),
    ensures
        xv(r.0) == clmul(lo64(xv(a)), lo64(xv(b))),
        xv(r.1) == mid(xv(a), xv(b)),
        xv(r.2) == clmul(hi64(xv(a)), hi64(xv(b))),
{
    let l = x_clmul::<0x00>(a, b);
    let h = x_clmul::<0x11>(a, b);
    let m1 = x_clmul::<0x10>(a, b);
    let m2 = x_clmul::<0x01>(a, b);
    let m = x_xor(m1, m2);
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
pub fn join_x(l: X128, m: X128, h: X128) -> (r: (X128, X128))
    requires
        ni(),
    ensures
        (xv(r.0), xv(r.1)) == join(xv(l), xv(m), xv(h)),
{
    (x_xor(l, x_bsll8(m)), x_xor(h, x_bsrl8(m)))
}

/// X • Y.
#[inline(always)]
pub fn mul_x(a: X128, b: X128) -> (r: X128)
    requires
        ni(),
    ensures
        xv(r) == gf_mul(xv(a), xv(b)),
{
    let (l, m, h) = prod_x(a, b);
    let (lo, hi) = join_x(l, m, h);
    proof {
        lemma_gf_mul_prod(xv(a), xv(b));
    }
    red_x(lo, hi)
}

// ---------------------------------------------------------------------------
// AES
// ---------------------------------------------------------------------------

/// One block: CIPHER(x) with the round keys `rk`.
#[inline(always)]
pub fn enc_x(rk: &[u128; 15], nr: usize, x: X128, Ghost(key): Ghost<Seq<u8>>) -> (r: X128)
    requires
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
    ensures
        xb(r) == cipher(key, xb(x)),
{
    let ghost input = xb(x);
    let mut s = x_xor(x, x_load_u128(rk, 0));
    proof {
        lemma_xor_bytes16(xv(x), rk@[0]);
        lemma_rounds_step(key, input, 1);
    }
    let mut r: usize = 1;
    while r < nr
        invariant
            ni(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            input.len() == 16,
            xb(s) == rounds(key, input, r as int),
        decreases nr - r,
    {
        let k = x_load_u128(rk, r);
        proof {
            lemma_rounds_len(key, input, r as int);
            lemma_aesenc(xb(s), xb(k));
            lemma_rounds_step(key, input, r as int);
        }
        s = x_aesenc(s, k);
        r = r + 1;
    }
    let k = x_load_u128(rk, nr);
    proof {
        lemma_rounds_len(key, input, nr as int);
        lemma_aesenc(xb(s), xb(k));
        lemma_cipher(key, input);
    }
    x_aesenclast(s, k)
}

/// The word in every column.
pub open spec fn bcast(w: u32) -> u128 {
    (w as u128) | (w as u128) << 32u128 | (w as u128) << 64u128 | (w as u128) << 96u128
}

proof fn lemma_bcast(w: u32)
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

proof fn lemma_zero_bytes()
    ensures
        bytes16(0) == Seq::new(16, |i: int| 0u8),
{
    assert forall|i: int| 0 <= i < 16 implies #[trigger] bytes16(0)[i] == 0u8 by {
        let s = (8 * i) as u128;
        assert((0u128 >> s) as u8 == 0) by (bit_vector);
    };
    assert(bytes16(0) =~= Seq::new(16, |i: int| 0u8));
}

proof fn lemma_low_word(sv: u128)
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

/// SUBWORD(w), with `AESENCLAST` on `w` in every column and a zero round
/// key (ShiftRows does nothing when the columns are the same).
#[inline(always)]
pub fn sub_word_x(w: u32) -> (r: u32)
    requires
        ni(),
    ensures
        r == sub_word(w),
{
    let v: u128 = (w as u128) | (w as u128) << 32 | (w as u128) << 64 | (w as u128) << 96;
    let x = x_set(v);
    let z = x_set(0);
    let s = x_aesenclast(x, z);
    let r = x_get(s) as u32;
    proof {
        assert(v == bcast(w));
        lemma_bcast(w);
        lemma_zero_bytes();
        let o = xb(s);
        let b = bytes16(v);
        reveal(aesenclast);
        assert forall|i: int| 0 <= i < 4 implies #[trigger] o[i] == sbox(wbyte(w, i)) by {
            let y = sbox(wbyte(w, i));
            assert(o[i] == sub_bytes(b)[i] ^ 0u8);
            assert(y ^ 0u8 == y) by (bit_vector);
        };
        lemma_low_word(xv(s));
    }
    r
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

/// `hp[m]` is H^(m + 1).
pub open spec fn powers_ok(h: u128, hp: Seq<u128>) -> bool {
    hp.len() == 16 && forall|m: int| 0 <= m < 16 ==> #[trigger] hp[m] == pow(h, (m + 1) as nat)
}

/// Adds the product of `x` and `k` to the unreduced sum (l, m, h).
#[verifier::spinoff_prover]
#[inline(always)]
pub fn acc_x(l: X128, m: X128, h: X128, x: X128, k: X128) -> (r: (X128, X128, X128))
    requires
        ni(),
    ensures
        red(join(xv(r.0), xv(r.1), xv(r.2))) == red(join(xv(l), xv(m), xv(h))) ^ gf_mul(xv(x), xv(k)),
{
    let (pl, pm, ph) = prod_x(x, k);
    proof {
        lemma_join_xor(xv(l), xv(m), xv(h), xv(pl), xv(pm), xv(ph));
        lemma_red_xor(join(xv(l), xv(m), xv(h)), join(xv(pl), xv(pm), xv(ph)));
        lemma_gf_mul_prod(xv(x), xv(k));
    }
    (x_xor(l, pl), x_xor(m, pm), x_xor(h, ph))
}

/// GHASH of n <= 8 blocks at `d[i..]`, from `acc`, with one reduction:
/// the sum of the blocks times H^n .. H^1 (the first with `acc` added).
#[inline(always)]
pub fn ghash_x(acc: u128, d: &[u8], i: usize, n: usize, hp: &[u128; 16], Ghost(h): Ghost<u128>) -> (r: u128)
    requires
        ni(),
        1 <= n <= 16,
        i + 16 * n <= d@.len(),
        powers_ok(h, hp@),
    ensures
        r == ghash_from(h, acc, blocks_at(d@, i as int, n as int)),
{
    let ghost xs = blocks_at(d@, i as int, n as int);
    let ghost ys = xs.update(0, acc ^ xs[0]);
    let _len = d.len();
    let rev = rev_x();
    let z = x_set(0);
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
            ni(),
            1 <= n <= 16,
            i + 16 * n <= d@.len(),
            powers_ok(h, hp@),
            xb(rev) == rev_mask(),
            xs == blocks_at(d@, i as int, n as int),
            ys == xs.update(0, acc ^ xs[0]),
            j <= n,
            d@.len() <= usize::MAX,
            o == i + 16 * j,
            red(join(xv(l), xv(m), xv(hh))) == dsum(h, ys.take(j as int), n as nat),
        decreases n - j,
    {
        assert(o + 16 <= d@.len()) by (nonlinear_arith)
            requires
                o == i + 16 * j,
                i + 16 * n <= d@.len(),
                j < n,
        ;
        let mut x = load_be(d, o, rev);
        if j == 0 {
            x = x_xor(x, x_set(acc));
            proof {
                let a = xs[0];
                assert(a ^ acc == acc ^ a) by (bit_vector);
            }
        }
        assert(xv(x) == ys[j as int]);
        let k = x_load_u128(hp, n - 1 - j);
        assert(xv(k) == pow(h, (n - j) as nat));
        let ghost old_sum = red(join(xv(l), xv(m), xv(hh)));
        let (l1, m1, h1) = acc_x(l, m, hh, x, k);
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
    let (lo, hi) = join_x(l, m, hh);
    x_get(red_x(lo, hi))
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

/// The counter block for c + j, after round 0.
#[inline(always)]
pub fn start_x(ctr: X128, cmask: X128, k0: X128, j: u32, Ghost(key): Ghost<Seq<u8>>, Ghost(iv): Ghost<Seq<u8>>, Ghost(c): Ghost<int>) -> (r: X128)
    requires
        ni(),
        key_ok(key),
        xb(k0) == round_key(key, 0),
        xb(cmask) == ctr_mask(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
    ensures
        xb(r) == rounds(key, counter_block(iv, c + j), 1),
{
    let cj = x_add32(ctr, x_set((j as u128) << 96));
    let b = x_pshufb(cj, cmask);
    proof {
        lemma_ctr_add(xv(ctr), iv, c, j);
        lemma_ctr_block(xv(cj), iv, c + j);
        lemma_xor_bytes16(xv(b), xv(k0));
        lemma_rounds_step(key, counter_block(iv, c + j), 1);
    }
    x_xor(b, k0)
}

/// Round r (1 <= r < Nr).
#[inline(always)]
pub fn round_x(s: X128, k: X128, Ghost(key): Ghost<Seq<u8>>, Ghost(input): Ghost<Seq<u8>>, Ghost(r): Ghost<int>) -> (o: X128)
    requires
        ni(),
        input.len() == 16,
        r >= 1,
        xb(s) == rounds(key, input, r),
        xb(k) == round_key(key, r),
    ensures
        xb(o) == rounds(key, input, r + 1),
{
    proof {
        lemma_rounds_len(key, input, r);
        lemma_aesenc(xb(s), xb(k));
        lemma_rounds_step(key, input, r);
    }
    x_aesenc(s, k)
}

/// The last round.
#[inline(always)]
pub fn last_x(s: X128, k: X128, Ghost(key): Ghost<Seq<u8>>, Ghost(input): Ghost<Seq<u8>>) -> (o: X128)
    requires
        ni(),
        input.len() == 16,
        xb(s) == rounds(key, input, crate::spec::nr(key)),
        xb(k) == round_key(key, crate::spec::nr(key)),
    ensures
        xb(o) == cipher(key, input),
{
    proof {
        lemma_rounds_len(key, input, crate::spec::nr(key));
        lemma_aesenc(xb(s), xb(k));
        lemma_cipher(key, input);
    }
    x_aesenclast(s, k)
}

/// Block j of a CTR run: XOR the keystream block `s` into `buf`.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn xor_block(
    buf: &mut [u8],
    i: usize,
    j: usize,
    o: usize,
    s: X128,
    Ghost(b0): Ghost<Seq<u8>>,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        ni(),
        ctr_done(old(buf)@, b0, i as int, j as int, key, iv, c),
        old(buf)@.len() == b0.len(),
        i + 16 * (j + 1) <= b0.len(),
        o == i + 16 * j,
        xb(s) == cipher(key, counter_block(iv, c + j)),
    ensures
        ctr_done(final(buf)@, b0, i as int, j + 1, key, iv, c),
        final(buf)@.len() == b0.len(),
{
    let p = x_load(buf, o);
    let x = x_xor(p, s);
    proof {
        lemma_xor_bytes16(xv(p), xv(s));
    }
    x_store(buf, o, x);
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
                assert(xb(p)[k - o] == b0[k]);
            }
        };
    }
}

/// The keystream of 8 blocks: CIPHER of the counter blocks for c, c + 1, ...
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ks8_x(
    rk: &[u128; 15],
    nr: usize,
    ctr: X128,
    cmask: X128,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
) -> (r: (X128, X128, X128, X128, X128, X128, X128, X128,))
    requires
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb(cmask) == ctr_mask(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
    ensures
        xb(r.0) == cipher(key, counter_block(iv, c + 0)),
        xb(r.1) == cipher(key, counter_block(iv, c + 1)),
        xb(r.2) == cipher(key, counter_block(iv, c + 2)),
        xb(r.3) == cipher(key, counter_block(iv, c + 3)),
        xb(r.4) == cipher(key, counter_block(iv, c + 4)),
        xb(r.5) == cipher(key, counter_block(iv, c + 5)),
        xb(r.6) == cipher(key, counter_block(iv, c + 6)),
        xb(r.7) == cipher(key, counter_block(iv, c + 7)),
{
    let k0 = x_load_u128(rk, 0);
    let ghost in0 = counter_block(iv, c + 0);
    proof { lemma_counter_block_len(iv, c + 0); }
    let mut s0 = start_x(ctr, cmask, k0, 0, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in1 = counter_block(iv, c + 1);
    proof { lemma_counter_block_len(iv, c + 1); }
    let mut s1 = start_x(ctr, cmask, k0, 1, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in2 = counter_block(iv, c + 2);
    proof { lemma_counter_block_len(iv, c + 2); }
    let mut s2 = start_x(ctr, cmask, k0, 2, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in3 = counter_block(iv, c + 3);
    proof { lemma_counter_block_len(iv, c + 3); }
    let mut s3 = start_x(ctr, cmask, k0, 3, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in4 = counter_block(iv, c + 4);
    proof { lemma_counter_block_len(iv, c + 4); }
    let mut s4 = start_x(ctr, cmask, k0, 4, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in5 = counter_block(iv, c + 5);
    proof { lemma_counter_block_len(iv, c + 5); }
    let mut s5 = start_x(ctr, cmask, k0, 5, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in6 = counter_block(iv, c + 6);
    proof { lemma_counter_block_len(iv, c + 6); }
    let mut s6 = start_x(ctr, cmask, k0, 6, Ghost(key), Ghost(iv), Ghost(c));
    let ghost in7 = counter_block(iv, c + 7);
    proof { lemma_counter_block_len(iv, c + 7); }
    let mut s7 = start_x(ctr, cmask, k0, 7, Ghost(key), Ghost(iv), Ghost(c));
    let mut r: usize = 1;
    while r < nr
        invariant
            ni(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            in0.len() == 16,
            xb(s0) == rounds(key, in0, r as int),
            in1.len() == 16,
            xb(s1) == rounds(key, in1, r as int),
            in2.len() == 16,
            xb(s2) == rounds(key, in2, r as int),
            in3.len() == 16,
            xb(s3) == rounds(key, in3, r as int),
            in4.len() == 16,
            xb(s4) == rounds(key, in4, r as int),
            in5.len() == 16,
            xb(s5) == rounds(key, in5, r as int),
            in6.len() == 16,
            xb(s6) == rounds(key, in6, r as int),
            in7.len() == 16,
            xb(s7) == rounds(key, in7, r as int),
        decreases nr - r,
    {
        let k = x_load_u128(rk, r);
        s0 = round_x(s0, k, Ghost(key), Ghost(in0), Ghost(r as int));
        s1 = round_x(s1, k, Ghost(key), Ghost(in1), Ghost(r as int));
        s2 = round_x(s2, k, Ghost(key), Ghost(in2), Ghost(r as int));
        s3 = round_x(s3, k, Ghost(key), Ghost(in3), Ghost(r as int));
        s4 = round_x(s4, k, Ghost(key), Ghost(in4), Ghost(r as int));
        s5 = round_x(s5, k, Ghost(key), Ghost(in5), Ghost(r as int));
        s6 = round_x(s6, k, Ghost(key), Ghost(in6), Ghost(r as int));
        s7 = round_x(s7, k, Ghost(key), Ghost(in7), Ghost(r as int));
        r = r + 1;
    }
    let k = x_load_u128(rk, nr);
    s0 = last_x(s0, k, Ghost(key), Ghost(in0));
    s1 = last_x(s1, k, Ghost(key), Ghost(in1));
    s2 = last_x(s2, k, Ghost(key), Ghost(in2));
    s3 = last_x(s3, k, Ghost(key), Ghost(in3));
    s4 = last_x(s4, k, Ghost(key), Ghost(in4));
    s5 = last_x(s5, k, Ghost(key), Ghost(in5));
    s6 = last_x(s6, k, Ghost(key), Ghost(in6));
    s7 = last_x(s7, k, Ghost(key), Ghost(in7));
    (s0, s1, s2, s3, s4, s5, s6, s7,)
}

/// 8 blocks of CTR: `buf[i..i + 128]` XOR the keystream from counter c.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ctr8_x(
    rk: &[u128; 15],
    nr: usize,
    ctr: X128,
    cmask: X128,
    buf: &mut [u8],
    i: usize,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb(cmask) == ctr_mask(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
        i + 128 <= old(buf)@.len(),
    ensures
        ctr_done(final(buf)@, old(buf)@, i as int, 8, key, iv, c),
        final(buf)@.len() == old(buf)@.len(),
{
    let ks = ks8_x(rk, nr, ctr, cmask, Ghost(key), Ghost(iv), Ghost(c));
    let _len = buf.len();
    let ghost b0 = buf@;
    proof {
        reveal(ctr_done);
        assert(ctr_done(buf@, b0, i as int, 0, key, iv, c));
    }
    xor_block(buf, i, 0, i + 0, ks.0, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 1, i + 16, ks.1, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 2, i + 32, ks.2, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 3, i + 48, ks.3, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 4, i + 64, ks.4, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 5, i + 80, ks.5, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 6, i + 96, ks.6, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
    xor_block(buf, i, 7, i + 112, ks.7, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
}

/// The keystream of 1 blocks: CIPHER of the counter blocks for c, c + 1, ...
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ks1_x(
    rk: &[u128; 15],
    nr: usize,
    ctr: X128,
    cmask: X128,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
) -> (r: (X128,))
    requires
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb(cmask) == ctr_mask(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
    ensures
        xb(r.0) == cipher(key, counter_block(iv, c + 0)),
{
    let k0 = x_load_u128(rk, 0);
    let ghost in0 = counter_block(iv, c + 0);
    proof { lemma_counter_block_len(iv, c + 0); }
    let mut s0 = start_x(ctr, cmask, k0, 0, Ghost(key), Ghost(iv), Ghost(c));
    let mut r: usize = 1;
    while r < nr
        invariant
            ni(),
            rk_ok(key, rk@),
            nr == crate::spec::nr(key),
            1 <= r <= nr,
            in0.len() == 16,
            xb(s0) == rounds(key, in0, r as int),
        decreases nr - r,
    {
        let k = x_load_u128(rk, r);
        s0 = round_x(s0, k, Ghost(key), Ghost(in0), Ghost(r as int));
        r = r + 1;
    }
    let k = x_load_u128(rk, nr);
    s0 = last_x(s0, k, Ghost(key), Ghost(in0));
    (s0,)
}

/// 1 blocks of CTR: `buf[i..i + 16]` XOR the keystream from counter c.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn ctr1_x(
    rk: &[u128; 15],
    nr: usize,
    ctr: X128,
    cmask: X128,
    buf: &mut [u8],
    i: usize,
    Ghost(key): Ghost<Seq<u8>>,
    Ghost(iv): Ghost<Seq<u8>>,
    Ghost(c): Ghost<int>,
)
    requires
        ni(),
        rk_ok(key, rk@),
        nr == crate::spec::nr(key),
        xb(cmask) == ctr_mask(),
        ctr_reg_ok(xv(ctr), iv, c),
        c >= 0,
        i + 16 <= old(buf)@.len(),
    ensures
        ctr_done(final(buf)@, old(buf)@, i as int, 1, key, iv, c),
        final(buf)@.len() == old(buf)@.len(),
{
    let ks = ks1_x(rk, nr, ctr, cmask, Ghost(key), Ghost(iv), Ghost(c));
    let _len = buf.len();
    let ghost b0 = buf@;
    proof {
        reveal(ctr_done);
        assert(ctr_done(buf@, b0, i as int, 0, key, iv, c));
    }
    xor_block(buf, i, 0, i + 0, ks.0, Ghost(b0), Ghost(key), Ghost(iv), Ghost(c));
}

} // verus!
