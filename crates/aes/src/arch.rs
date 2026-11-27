//! The operations the kernels are written with, as a trait over the
//! instruction set: [`crate::ni::Ni`] (x86-64 AES-NI, PCLMULQDQ and, for
//! the wide path, VAES and VPCLMULQDQ) and [`crate::arm::Arm`] (AArch64
//! FEAT_AES and FEAT_PMULL). The kernels and GCM are proven once, against
//! these `ensures`; each implementation is proven to meet them from its
//! instruction wrappers.
//!
//! A register is a 128-bit integer ([`Isa::v`]), byte 0 in bits 7:0.
//!
//! The trait is also how the generic code keeps secrets secret. In
//! `kernels.rs` and `gcm.rs` every secret (the round keys, H and its
//! powers, the counter blocks, the keystream, the GHASH state, the tag) is
//! an `A::R` from the moment it is loaded, and `A::R` is an associated
//! type with no operations but the trait's: the compiler rejects an `if`,
//! a `match`, a comparison or an index on it. No method returns anything
//! computed from a register's value except [`Isa::is_zero`], called once,
//! through [`crate::ct::declassify`]. The type check is the proof that the
//! generic code cannot branch on or index memory with a secret held in a
//! register. (It does not cover the bytes copied for a partial block,
//! the key schedule's words, or the instruction sets' implementations of
//! the trait; `scripts/ctcheck.py` checks all of it on the machine code.) The
//! one place the two instruction sets differ in shape is the AES round:
//! x86's `AESENC` ends a round with the round key, Arm's `AESE` starts one
//! with it. So the state between rounds is left to each implementation
//! ([`Isa::st`]), and the kernels only step it.
#![allow(unused_imports)]
use crate::gf::*;
use crate::isa::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::kernels::*;
use vstd::prelude::*;

verus! {

/// The bytes of a register.
pub open spec fn xb<A: Isa>(r: A::R) -> Seq<u8> {
    bytes16(A::v(r))
}

pub trait Isa {
    type R: Copy;

    /// The CPU has the instructions.
    spec fn ok() -> bool;

    /// The register as a 128-bit integer.
    spec fn v(r: Self::R) -> u128;

    /// The AES state of `input` before round r (1 <= r <= Nr): whatever
    /// form of FIPS 197's state after rounds 0..r-1 the implementation
    /// keeps.
    spec fn st(s: Self::R, key: Seq<u8>, input: Seq<u8>, r: int) -> bool;

    fn load(d: &[u8], i: usize) -> (r: Self::R)
        requires
            Self::ok(),
            i + 16 <= d@.len(),
        ensures
            bytes16(Self::v(r)) == d@.subrange(i as int, i + 16),
    ;

    fn store(d: &mut [u8], i: usize, x: Self::R)
        requires
            Self::ok(),
            i + 16 <= old(d)@.len(),
        ensures
            final(d)@.len() == old(d)@.len(),
            forall|k: int|
                0 <= k < final(d)@.len() ==> #[trigger] final(d)@[k] == if i <= k < i + 16 {
                    bytes16(Self::v(x))[k - i]
                } else {
                    old(d)@[k]
                },
    ;

    fn load16(a: &[u8; 16]) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            bytes16(Self::v(r)) == a@,
    ;

    fn store16(a: &mut [u8; 16], x: Self::R)
        requires
            Self::ok(),
        ensures
            final(a)@ == bytes16(Self::v(x)),
    ;

    fn load_u128(a: &[u128], i: usize) -> (r: Self::R)
        requires
            Self::ok(),
            i < a@.len(),
        ensures
            Self::v(r) == a@[i as int],
    ;

    fn set(v: u128) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            Self::v(r) == v,
    ;

    /// `a[i] := x`: a register stored in an expanded key's table.
    fn store_u128(a: &mut [u128; 16], i: usize, x: Self::R)
        requires
            Self::ok(),
            i < 16,
        ensures
            final(a)@ == old(a)@.update(i as int, Self::v(x)),
    ;

    /// Whether the register is zero: the one method that turns a register
    /// into something code can branch on. Its one caller (`Gcm::open`,
    /// on whether the tag matched) passes the result straight to
    /// [`crate::ct::declassify`].
    fn is_zero(x: Self::R) -> (r: bool)
        requires
            Self::ok(),
        ensures
            r == (Self::v(x) == 0),
    ;

    fn xor(a: Self::R, b: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            Self::v(r) == Self::v(a) ^ Self::v(b),
    ;

    fn clmul<const IMM: i32>(a: Self::R, b: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
            IMM == 0x00 || IMM == 0x01 || IMM == 0x10 || IMM == 0x11,
        ensures
            Self::v(r) == pclmul(Self::v(a), Self::v(b), IMM),
    ;

    fn pshufb(a: Self::R, m: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            bytes16(Self::v(r)) == pshufb(bytes16(Self::v(a)), bytes16(Self::v(m))),
    ;

    fn add32(a: Self::R, b: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            Self::v(r) == add32x4(Self::v(a), Self::v(b)),
    ;

    fn sll64<const N: i32>(a: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
            0 < N < 64,
        ensures
            Self::v(r) == sll64x2(Self::v(a), N as u64),
    ;

    fn srl64<const N: i32>(a: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
            0 < N < 64,
        ensures
            Self::v(r) == srl64x2(Self::v(a), N as u64),
    ;

    fn bsll8(a: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            Self::v(r) == Self::v(a) << 64u128,
    ;

    fn bsrl8(a: Self::R) -> (r: Self::R)
        requires
            Self::ok(),
        ensures
            Self::v(r) == Self::v(a) >> 64u128,
    ;

    /// The state before round 1 of the block `x`.
    fn first(x: Self::R, rk: &[u128; 15], key: Ghost<Seq<u8>>) -> (o: Self::R)
        requires
            Self::ok(),
            rk_ok(key@, rk@),
        ensures
            Self::st(o, key@, bytes16(Self::v(x)), 1),
    ;

    /// Round r (1 <= r < Nr).
    fn round(s: Self::R, rk: &[u128; 15], r: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: Self::R)
        requires
            Self::ok(),
            rk_ok(key@, rk@),
            1 <= r < nr(key@),
            input@.len() == 16,
            Self::st(s, key@, input@, r as int),
        ensures
            Self::st(o, key@, input@, r + 1),
    ;

    /// The last round: CIPHER(input).
    fn last(s: Self::R, rk: &[u128; 15], nr: usize, key: Ghost<Seq<u8>>, input: Ghost<Seq<u8>>) -> (o: Self::R)
        requires
            Self::ok(),
            rk_ok(key@, rk@),
            nr == crate::spec::nr(key@),
            input@.len() == 16,
            Self::st(s, key@, input@, nr as int),
        ensures
            bytes16(Self::v(o)) == cipher(key@, input@),
    ;

    /// SUBWORD(w), for the key expansion.
    fn sub_word(w: u32) -> (r: u32)
        requires
            Self::ok(),
        ensures
            r == sub_word(w),
    ;

}

/// The 16-block path, where there is one (a separate trait, so that its
/// implementation can use the kernels proven over [`Isa`]).
pub trait Wide: Isa {
    /// The CPU has the 16-block path.
    spec fn wide() -> bool;

    /// GHASH of the 16 blocks at `d[i..i + 256]`, from `acc`.
    fn ghash16(acc: Self::R, d: &[u8], i: usize, hr: &[u128; 16], h: Ghost<u128>) -> (r: Self::R)
        requires
            Self::ok(),
            Self::wide(),
            i + 256 <= d@.len(),
            rpowers_ok(h@, hr@),
        ensures
            Self::v(r) == ghash_from(h@, Self::v(acc), blocks_at(d@, i as int, 16)),
    ;

    /// 16 blocks of CTR: `buf[i..i + 256]` XOR the keystream from counter c.
    fn ctr16(
        rk: &[u128; 15],
        nr: usize,
        ctr: Self::R,
        buf: &mut [u8],
        i: usize,
        key: Ghost<Seq<u8>>,
        iv: Ghost<Seq<u8>>,
        c: Ghost<int>,
    )
        requires
            Self::ok(),
            Self::wide(),
            rk_ok(key@, rk@),
            nr == crate::spec::nr(key@),
            ctr_reg_ok(Self::v(ctr), iv@, c@),
            c@ >= 0,
            i + 256 <= old(buf)@.len(),
        ensures
            ctr_done(final(buf)@, old(buf)@, i as int, 16, key@, iv@, c@),
            final(buf)@.len() == old(buf)@.len(),
    ;
}

} // verus!
