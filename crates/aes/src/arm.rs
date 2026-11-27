//! [`Isa`] on AArch64: FEAT_AES and FEAT_PMULL, proven from the wrappers
//! of [`crate::neon`]. `AESE` starts a round with its round key, so the
//! state kept before round r is FIPS 197's state after round r - 1 without
//! round key r - 1 added: round r is `AESMC(AESE(s, rk[r - 1]))`, and the
//! last is `AESE(s, rk[Nr - 1]) XOR rk[Nr]`. There is no 16-block path.
#![allow(unused_imports)]
use crate::arch::{Isa, Wide};
use crate::gf::*;
use crate::isa::*;
use crate::kernels::*;
use crate::lemmas::*;
use crate::neon::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub struct Arm;

impl Isa for Arm {
    type R = N128;

    open spec fn ok() -> bool {
        arm_aes()
    }

    open spec fn v(r: N128) -> u128 {
        nv(r)
    }

    open spec fn st(s: N128, key: Seq<u8>, input: Seq<u8>, r: int) -> bool {
        add_round_key(nb(s), round_key(key, r - 1)) == rounds(key, input, r)
    }

    #[inline(always)]
    fn load(d: &[u8], i: usize) -> (r: N128) {
        n_load(d, i)
    }

    #[inline(always)]
    fn store(d: &mut [u8], i: usize, x: N128) {
        n_store(d, i, x)
    }

    #[inline(always)]
    fn load16(a: &[u8; 16]) -> (r: N128) {
        n_load16(a)
    }

    #[inline(always)]
    fn store16(a: &mut [u8; 16], x: N128) {
        n_store16(a, x)
    }

    #[inline(always)]
    fn load_u128(a: &[u128], i: usize) -> (r: N128) {
        n_load_u128(a, i)
    }

    #[inline(always)]
    fn set(v: u128) -> (r: N128) {
        n_set(v)
    }

    #[inline(always)]
    fn store_u128(a: &mut [u128; 16], i: usize, x: N128) {
        a[i] = n_get(x);
    }

    #[inline(always)]
    fn is_zero(x: N128) -> (r: bool) {
        n_get(x) == 0
    }

    #[inline(always)]
    fn xor(a: N128, b: N128) -> (r: N128) {
        n_xor(a, b)
    }

    #[inline(always)]
    fn clmul<const IMM: i32>(a: N128, b: N128) -> (r: N128) {
        n_clmul::<IMM>(a, b)
    }

    #[inline(always)]
    fn pshufb(a: N128, m: N128) -> (r: N128) {
        n_tbl(a, m)
    }

    #[inline(always)]
    fn add32(a: N128, b: N128) -> (r: N128) {
        n_add32(a, b)
    }

    #[inline(always)]
    fn sll64<const N: i32>(a: N128) -> (r: N128) {
        n_sll64::<N>(a)
    }

    #[inline(always)]
    fn srl64<const N: i32>(a: N128) -> (r: N128) {
        n_srl64::<N>(a)
    }

    #[inline(always)]
    fn bsll8(a: N128) -> (r: N128) {
        n_bsll8(a)
    }

    #[inline(always)]
    fn bsrl8(a: N128) -> (r: N128) {
        n_bsrl8(a)
    }

    /// Nothing: round 1's `AESE` adds round key 0.
    #[inline(always)]
    fn first(x: N128, rk: &[u128; 15], key: Ghost<Seq<u8>>) -> (o: N128) {
        proof {
            lemma_rounds_step(key@, nb(x), 1);
        }
        x
    }

    /// `AESMC(AESE(s, rk[r - 1]))`.
    #[inline(always)]
    fn round(s: N128, rk: &[u128; 15], r: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: N128) {
        let k = n_load_u128(rk, r - 1);
        let t = n_aese(s, k);
        let o = n_aesmc(t);
        proof {
            lemma_aese(nb(s), nb(k));
            lemma_rounds_step(key@, input@, r as int);
            reveal(round);
            assert(nb(k) == round_key(key@, r - 1));
        }
        o
    }

    /// `AESE(s, rk[Nr - 1]) XOR rk[Nr]`.
    #[inline(always)]
    fn last(s: N128, rk: &[u128; 15], nr: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: N128) {
        let k = n_load_u128(rk, nr - 1);
        let kl = n_load_u128(rk, nr);
        let t = n_aese(s, k);
        let o = n_xor(t, kl);
        proof {
            assert(nb(k) == round_key(key@, nr - 1));
            lemma_aese(nb(s), nb(k));
            lemma_xor_bytes16(nv(t), nv(kl));
            reveal(final_round);
            lemma_cipher(key@, input@);
        }
        o
    }

    /// `AESE` on `w` in every column with a zero round key (ShiftRows does
    /// nothing when the columns are the same).
    #[inline(always)]
    fn sub_word(w: u32) -> (r: u32) {
        let v: u128 = (w as u128) | (w as u128) << 32 | (w as u128) << 64 | (w as u128) << 96;
        let x = n_set(v);
        let z = n_set(0);
        let s = n_aese(x, z);
        let r = n_get(s) as u32;
        proof {
            lemma_sub_word_aese(w, v, x, z, s);
        }
        r
    }
}

/// The proof of [`Arm::sub_word`], apart from the trait implementation so
/// that its context is only what it needs.
proof fn lemma_sub_word_aese(w: u32, v: u128, x: N128, z: N128, s: N128)
    requires
    v == (w as u128) | (w as u128) << 32 | (w as u128) << 64 | (w as u128) << 96,
    nv(x) == v,
    nv(z) == 0,
    nb(s) == aese(nb(x), nb(z)),
    ensures
    nv(s) as u32 == sub_word(w),
{
    assert(v == bcast(w));
    lemma_bcast(w);
    lemma_zero_bytes();
    let b = bytes16(v);
    assert forall|i: int| 0 <= i < 16 implies #[trigger] add_round_key(b, bytes16(0))[i] == b[i] by {
        let y = b[i];
        assert(y ^ 0u8 == y) by (bit_vector);
    };
    assert(add_round_key(b, bytes16(0)) =~= b);
    reveal(aese);
    let o = nb(s);
    assert forall|i: int| 0 <= i < 4 implies #[trigger] o[i] == sbox(wbyte(w, i)) by {
        assert(o[i] == sbox(shift_rows(b)[i]));
    };
    lemma_low_word(nv(s));
}

impl Wide for Arm {
    open spec fn wide() -> bool {
        false
    }

    #[inline(always)]
    fn ghash16(acc: N128, d: &[u8], i: usize, hr: &[u128; 16], h: Ghost<u128>) -> (r: N128) {
        acc
    }

    #[inline(always)]
    fn ctr16(
        rk: &[u128; 15],
        nr: usize,
        ctr: N128,
        buf: &mut [u8],
        i: usize,
        key: Ghost<Seq<u8>>,
        iv: Ghost<Seq<u8>>,
        c: Ghost<int>,
    ) {
    }
}

} // verus!
