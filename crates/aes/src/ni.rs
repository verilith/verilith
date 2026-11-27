//! [`Isa`] on x86-64: AES-NI and PCLMULQDQ, and VAES and VPCLMULQDQ for
//! the 16-block path, proven from the wrappers of [`crate::x86`]. The AES
//! state between rounds is FIPS 197's state itself: `AESENC` ends a round
//! with its round key.
#![allow(unused_imports)]
use crate::arch::{Isa, Wide};
use crate::gf::*;
use crate::isa::*;
use crate::kernels::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::x86::*;
use vstd::prelude::*;

verus! {

pub struct Ni;

impl Isa for Ni {
    type R = X128;

    open spec fn ok() -> bool {
        ni()
    }

    open spec fn v(r: X128) -> u128 {
        xv(r)
    }

    open spec fn st(s: X128, key: Seq<u8>, input: Seq<u8>, r: int) -> bool {
        xb(s) == rounds(key, input, r)
    }

    #[inline(always)]
    fn load(d: &[u8], i: usize) -> (r: X128) {
        x_load(d, i)
    }

    #[inline(always)]
    fn store(d: &mut [u8], i: usize, x: X128) {
        x_store(d, i, x)
    }

    #[inline(always)]
    fn load16(a: &[u8; 16]) -> (r: X128) {
        x_load16(a)
    }

    #[inline(always)]
    fn store16(a: &mut [u8; 16], x: X128) {
        x_store16(a, x)
    }

    #[inline(always)]
    fn load_u128(a: &[u128], i: usize) -> (r: X128) {
        x_load_u128(a, i)
    }

    #[inline(always)]
    fn set(v: u128) -> (r: X128) {
        x_set(v)
    }

    #[inline(always)]
    fn get(x: X128) -> (r: u128) {
        x_get(x)
    }

    #[inline(always)]
    fn xor(a: X128, b: X128) -> (r: X128) {
        x_xor(a, b)
    }

    #[inline(always)]
    fn clmul<const IMM: i32>(a: X128, b: X128) -> (r: X128) {
        x_clmul::<IMM>(a, b)
    }

    #[inline(always)]
    fn pshufb(a: X128, m: X128) -> (r: X128) {
        x_pshufb(a, m)
    }

    #[inline(always)]
    fn add32(a: X128, b: X128) -> (r: X128) {
        x_add32(a, b)
    }

    #[inline(always)]
    fn sll64<const N: i32>(a: X128) -> (r: X128) {
        x_sll64::<N>(a)
    }

    #[inline(always)]
    fn srl64<const N: i32>(a: X128) -> (r: X128) {
        x_srl64::<N>(a)
    }

    #[inline(always)]
    fn bsll8(a: X128) -> (r: X128) {
        x_bsll8(a)
    }

    #[inline(always)]
    fn bsrl8(a: X128) -> (r: X128) {
        x_bsrl8(a)
    }

    /// Round 0: XOR with round key 0.
    #[inline(always)]
    fn first(x: X128, rk: &[u128; 15], key: Ghost<Seq<u8>>) -> (o: X128) {
        let k0 = x_load_u128(rk, 0);
        proof {
            lemma_xor_bytes16(xv(x), rk@[0]);
            lemma_rounds_step(key@, xb(x), 1);
        }
        x_xor(x, k0)
    }

    /// `AESENC` with round key r.
    #[inline(always)]
    fn round(s: X128, rk: &[u128; 15], r: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: X128) {
        let k = x_load_u128(rk, r);
        proof {
            lemma_rounds_len(key@, input@, r as int);
            lemma_aesenc(xb(s), xb(k));
            lemma_rounds_step(key@, input@, r as int);
        }
        x_aesenc(s, k)
    }

    /// `AESENCLAST` with round key Nr.
    #[inline(always)]
    fn last(s: X128, rk: &[u128; 15], nr: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: X128) {
        let k = x_load_u128(rk, nr);
        proof {
            lemma_rounds_len(key@, input@, nr as int);
            lemma_aesenc(xb(s), xb(k));
            lemma_cipher(key@, input@);
        }
        x_aesenclast(s, k)
    }

    /// `AESENCLAST` on `w` in every column with a zero round key
    /// (ShiftRows does nothing when the columns are the same).
    #[inline(always)]
    fn sub_word(w: u32) -> (r: u32) {
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

}

impl Wide for Ni {
    open spec fn wide() -> bool {
        vaes()
    }

    #[inline(always)]
    fn ghash16(acc: u128, d: &[u8], i: usize, hr: &[u128; 16], h: Ghost<u128>) -> (r: u128) {
        crate::vaes::ghash16_z(acc, d, i, hr, h)
    }

    #[inline(always)]
    fn ctr16(
        rk: &[u128; 15],
        nr: usize,
        ctr: X128,
        buf: &mut [u8],
        i: usize,
        key: Ghost<Seq<u8>>,
        iv: Ghost<Seq<u8>>,
        c: Ghost<int>,
    ) {
        crate::vaes::ctr16_z(rk, nr, ctr, buf, i, key, iv, c)
    }
}

} // verus!
