//! Portable implementations of [`crate::aes`]'s instruction
//! specifications, proven to compute them. `tests/isa.rs` runs every
//! instruction wrapper against these on random operands, so that a wrapper
//! whose intrinsic does not do what its `ensures` says is caught on the
//! CPU, not only by review.
#![allow(unused_imports, missing_docs)]
use crate::aes::*;
use vstd::prelude::*;

verus! {

/// The bytes of `v`, byte 0 least significant.
pub fn bytes_of(v: u128) -> (r: [u8; 16])
    ensures
        r@ == bytes16(v),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == bytes16(v)[j],
        decreases 16 - k,
    {
        r[k] = (v >> (8 * k as u128)) as u8;
        k = k + 1;
    }
    assert(r@ =~= bytes16(v));
    r
}

pub fn sub_bytes_ref(s: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == sub_bytes(s@),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == sub_bytes(s@)[j],
        decreases 16 - k,
    {
        r[k] = SBOX[s[k] as usize];
        k = k + 1;
    }
    assert(r@ =~= sub_bytes(s@));
    r
}

pub fn shift_rows_ref(s: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == shift_rows(s@),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == shift_rows(s@)[j],
        decreases 16 - k,
    {
        r[k] = s[k % 4 + 4 * ((k / 4 + k % 4) % 4)];
        k = k + 1;
    }
    assert(r@ =~= shift_rows(s@));
    r
}

fn xtimes_ref(b: u8) -> (r: u8)
    ensures
        r == xtimes(b),
{
    if b & 0x80 == 0 {
        ((b as u16) << 1) as u8
    } else {
        (((b as u16) << 1) as u8) ^ 0x1b
    }
}

pub fn mix_columns_ref(s: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == mix_columns(s@),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == mix_columns(s@)[j],
        decreases 16 - k,
    {
        let c = 4 * (k / 4);
        let q = k % 4;
        let s0 = s[c + q];
        let s1 = s[c + (q + 1) % 4];
        let s2 = s[c + (q + 2) % 4];
        let s3 = s[c + (q + 3) % 4];
        r[k] = xtimes_ref(s0) ^ (xtimes_ref(s1) ^ s1) ^ s2 ^ s3;
        k = k + 1;
    }
    assert(r@ =~= mix_columns(s@));
    r
}

pub fn xor_ref(a: [u8; 16], b: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == add_round_key(a@, b@),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == add_round_key(a@, b@)[j],
        decreases 16 - k,
    {
        r[k] = a[k] ^ b[k];
        k = k + 1;
    }
    assert(r@ =~= add_round_key(a@, b@));
    r
}

pub fn aesenc_ref(s: [u8; 16], k: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == aesenc(s@, k@),
{
    reveal(aesenc);
    xor_ref(mix_columns_ref(sub_bytes_ref(shift_rows_ref(s))), k)
}

pub fn aesenclast_ref(s: [u8; 16], k: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == aesenclast(s@, k@),
{
    reveal(aesenclast);
    xor_ref(sub_bytes_ref(shift_rows_ref(s)), k)
}

pub fn aese_ref(d: [u8; 16], k: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == aese(d@, k@),
{
    reveal(aese);
    sub_bytes_ref(shift_rows_ref(xor_ref(d, k)))
}

pub fn aesmc_ref(d: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == aesmc(d@),
{
    mix_columns_ref(d)
}

pub fn pshufb_ref(a: [u8; 16], m: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == pshufb(a@, m@),
{
    let mut r = [0u8; 16];
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            forall|j: int| 0 <= j < k ==> #[trigger] r@[j] == pshufb(a@, m@)[j],
        decreases 16 - k,
    {
        let mk = m[k];
        assert(mk & 15 < 16) by (bit_vector);
        r[k] = if mk & 0x80 != 0 { 0 } else { a[(mk & 15) as usize] };
        k = k + 1;
    }
    assert(r@ =~= pshufb(a@, m@));
    r
}

pub fn clmul_ref(a: u64, b: u64) -> (r: u128)
    ensures
        r == clmul(a, b),
{
    let mut r: u128 = 0;
    let mut n: u32 = 0;
    while n < 64
        invariant
            n <= 64,
            r == clmul_n(a, b, n as nat),
        decreases 64 - n,
    {
        let ghost r0 = r;
        if (a >> n) & 1 == 1 {
            r = r ^ ((b as u128) << n);
        } else {
            assert(r0 ^ 0u128 == r0) by (bit_vector);
        }
        assert(clmul_n(a, b, (n + 1) as nat) == clmul_n(a, b, n as nat) ^ (if (a >> n as u64) & 1 == 1 {
            (b as u128) << n as u128
        } else {
            0
        }));
        n = n + 1;
    }
    r
}

pub fn pclmul_ref(a: u128, b: u128, imm: i32) -> (r: u128)
    ensures
        r == pclmul(a, b, imm),
{
    let x = if imm & 1 != 0 { (a >> 64) as u64 } else { a as u64 };
    let y = if imm & 0x10 != 0 { (b >> 64) as u64 } else { b as u64 };
    assert(x == half(a, imm & 1 != 0));
    assert(y == half(b, imm & 0x10 != 0));
    clmul_ref(x, y)
}

pub fn add32x4_ref(a: u128, b: u128) -> (r: u128)
    ensures
        r == add32x4(a, b),
{
    let r0 = ((a >> 0) as u32).wrapping_add((b >> 0) as u32);
    let r1 = ((a >> 32) as u32).wrapping_add((b >> 32) as u32);
    let r2 = ((a >> 64) as u32).wrapping_add((b >> 64) as u32);
    let r3 = ((a >> 96) as u32).wrapping_add((b >> 96) as u32);
    assert(r0 == lane32(a, 0).wrapping_add(lane32(b, 0)));
    assert(r1 == lane32(a, 1).wrapping_add(lane32(b, 1)));
    assert(r2 == lane32(a, 2).wrapping_add(lane32(b, 2)));
    assert(r3 == lane32(a, 3).wrapping_add(lane32(b, 3)));
    (r0 as u128) | (r1 as u128) << 32 | (r2 as u128) << 64 | (r3 as u128) << 96
}

pub fn sll64x2_ref(a: u128, n: u64) -> (r: u128)
    requires
        n < 64,
    ensures
        r == sll64x2(a, n),
{
    ((((a >> 64) as u64) << n) as u128) << 64 | (((a as u64) << n) as u128)
}

pub fn srl64x2_ref(a: u128, n: u64) -> (r: u128)
    requires
        n < 64,
    ensures
        r == srl64x2(a, n),
{
    ((((a >> 64) as u64) >> n) as u128) << 64 | (((a as u64) >> n) as u128)
}

} // verus!
