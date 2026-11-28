//! Verified scalar implementations of the instruction specifications in
//! [`crate::sha`]: what verilith-sha2's `tests/isa.rs` compares the CPU with, and the body
//! of the AArch64 instruction wrappers on other targets (so the AArch64
//! kernels build, verify and run everywhere).
#![allow(missing_docs)]
#![allow(clippy::manual_rotate)]
use crate::sha as isa;
use vstd::prelude::*;

verus! {

#[inline(always)]
fn a32(x: u32, y: u32) -> (r: u32)
    ensures
        r == isa::add32(x, y),
{
    x.wrapping_add(y)
}

#[inline(always)]
fn a64(x: u64, y: u64) -> (r: u64)
    ensures
        r == isa::add64(x, y),
{
    x.wrapping_add(y)
}

#[inline(always)]
fn ror32(x: u32, n: u32) -> (r: u32)
    requires
        0 < n < 32,
    ensures
        r == isa::ror32(x, n),
{
    (x >> n) | (x << (32 - n))
}

#[inline(always)]
fn ror64(x: u64, n: u64) -> (r: u64)
    requires
        0 < n < 64,
    ensures
        r == isa::ror64(x, n),
{
    (x >> n) | (x << (64 - n))
}

fn x_ch(e: u32, f: u32, g: u32) -> (r: u32)
    ensures
        r == isa::x_ch(e, f, g),
{
    (e & f) ^ (!e & g)
}

fn x_maj(a: u32, b: u32, c: u32) -> (r: u32)
    ensures
        r == isa::x_maj(a, b, c),
{
    (a & b) ^ (a & c) ^ (b & c)
}

fn x_big_s0(a: u32) -> (r: u32)
    ensures
        r == isa::x_big_s0(a),
{
    ror32(a, 2) ^ ror32(a, 13) ^ ror32(a, 22)
}

fn x_big_s1(e: u32) -> (r: u32)
    ensures
        r == isa::x_big_s1(e),
{
    ror32(e, 6) ^ ror32(e, 11) ^ ror32(e, 25)
}

fn x_small_s0(w: u32) -> (r: u32)
    ensures
        r == isa::x_small_s0(w),
{
    ror32(w, 7) ^ ror32(w, 18) ^ (w >> 3)
}

fn x_small_s1(w: u32) -> (r: u32)
    ensures
        r == isa::x_small_s1(w),
{
    ror32(w, 17) ^ ror32(w, 19) ^ (w >> 10)
}

fn rnds2_step(s: [u32; 8], wk: u32) -> (r: [u32; 8])
    ensures
        r@ == seq![
            isa::rnds2_step(isa::Rnds2 { a: s[0], b: s[1], c: s[2], d: s[3], e: s[4], f: s[5], g: s[6], h: s[7] }, wk).a,
            s[0], s[1], s[2],
            isa::rnds2_step(isa::Rnds2 { a: s[0], b: s[1], c: s[2], d: s[3], e: s[4], f: s[5], g: s[6], h: s[7] }, wk).e,
            s[4], s[5], s[6],
        ],
{
    let t = a32(a32(a32(x_ch(s[4], s[5], s[6]), x_big_s1(s[4])), wk), s[7]);
    let a = a32(a32(t, x_maj(s[0], s[1], s[2])), x_big_s0(s[0]));
    let e = a32(t, s[3]);
    let r = [a, s[0], s[1], s[2], e, s[4], s[5], s[6]];
    assert(r@ =~= seq![a, s[0], s[1], s[2], e, s[4], s[5], s[6]]);
    r
}

/// `SHA256RNDS2`.
pub fn sha256rnds2(src1: [u32; 4], src2: [u32; 4], k: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256rnds2(src1@, src2@, k@),
{
    let s0 = [src2[3], src2[2], src1[3], src1[2], src2[1], src2[0], src1[1], src1[0]];
    let s1 = rnds2_step(s0, k[0]);
    let s2 = rnds2_step(s1, k[1]);
    let r = [s2[5], s2[4], s2[1], s2[0]];
    assert(r@ =~= isa::sha256rnds2(src1@, src2@, k@));
    r
}

/// `SHA256MSG1`.
pub fn sha256msg1(src1: [u32; 4], src2: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256msg1(src1@, src2@),
{
    let r = [
        a32(src1[0], x_small_s0(src1[1])),
        a32(src1[1], x_small_s0(src1[2])),
        a32(src1[2], x_small_s0(src1[3])),
        a32(src1[3], x_small_s0(src2[0])),
    ];
    assert(r@ =~= isa::sha256msg1(src1@, src2@));
    r
}

/// `SHA256MSG2`.
pub fn sha256msg2(src1: [u32; 4], src2: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256msg2(src1@, src2@),
{
    let w16 = a32(src1[0], x_small_s1(src2[2]));
    let w17 = a32(src1[1], x_small_s1(src2[3]));
    let w18 = a32(src1[2], x_small_s1(w16));
    let w19 = a32(src1[3], x_small_s1(w17));
    let r = [w16, w17, w18, w19];
    assert(r@ =~= isa::sha256msg2(src1@, src2@));
    r
}

fn sha256hash_step(x: [u32; 4], y: [u32; 4], w: u32) -> (r: ([u32; 4], [u32; 4]))
    ensures
        (r.0@, r.1@) == isa::sha256hash_step(x@, y@, w),
{
    let chs = ((y[1] ^ y[2]) & y[0]) ^ y[2];
    let maj = (x[0] & x[1]) | ((x[0] | x[1]) & x[2]);
    let s1 = ror32(y[0], 6) ^ ror32(y[0], 11) ^ ror32(y[0], 25);
    let s0 = ror32(x[0], 2) ^ ror32(x[0], 13) ^ ror32(x[0], 22);
    let t = a32(a32(a32(y[3], s1), chs), w);
    let x3 = a32(t, x[3]);
    let y3 = a32(a32(t, s0), maj);
    let rx = [y3, x[0], x[1], x[2]];
    let ry = [x3, y[0], y[1], y[2]];
    let ghost s = isa::sha256hash_step(x@, y@, w);
    assert(rx@ =~= s.0);
    assert(ry@ =~= s.1);
    (rx, ry)
}

fn sha256hash(x: [u32; 4], y: [u32; 4], w: [u32; 4]) -> (r: ([u32; 4], [u32; 4]))
    ensures
        (r.0@, r.1@) == isa::sha256hash(x@, y@, w@),
{
    let (x1, y1) = sha256hash_step(x, y, w[0]);
    let (x2, y2) = sha256hash_step(x1, y1, w[1]);
    let (x3, y3) = sha256hash_step(x2, y2, w[2]);
    sha256hash_step(x3, y3, w[3])
}

/// `SHA256H`.
pub fn sha256h(hash_abcd: [u32; 4], hash_efgh: [u32; 4], wk: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256h(hash_abcd@, hash_efgh@, wk@),
{
    sha256hash(hash_abcd, hash_efgh, wk).0
}

/// `SHA256H2`.
pub fn sha256h2(hash_efgh: [u32; 4], hash_abcd: [u32; 4], wk: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256h2(hash_efgh@, hash_abcd@, wk@),
{
    sha256hash(hash_abcd, hash_efgh, wk).1
}

fn su0_sig(x: u32) -> (r: u32)
    ensures
        r == isa::ror32(x, 7) ^ isa::ror32(x, 18) ^ (x >> 3u32),
{
    ror32(x, 7) ^ ror32(x, 18) ^ (x >> 3)
}

/// `SHA256SU0`.
pub fn sha256su0(w0_3: [u32; 4], w4_7: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256su0(w0_3@, w4_7@),
{
    let r = [
        a32(su0_sig(w0_3[1]), w0_3[0]),
        a32(su0_sig(w0_3[2]), w0_3[1]),
        a32(su0_sig(w0_3[3]), w0_3[2]),
        a32(su0_sig(w4_7[0]), w0_3[3]),
    ];
    assert(r@ =~= isa::sha256su0(w0_3@, w4_7@));
    r
}

fn su1_sig(x: u32) -> (r: u32)
    ensures
        r == isa::su1_sig(x),
{
    ror32(x, 17) ^ ror32(x, 19) ^ (x >> 10)
}

/// `SHA256SU1`.
pub fn sha256su1(tw0_3: [u32; 4], w8_11: [u32; 4], w12_15: [u32; 4]) -> (r: [u32; 4])
    ensures
        r@ == isa::sha256su1(tw0_3@, w8_11@, w12_15@),
{
    let r0 = a32(a32(su1_sig(w12_15[2]), tw0_3[0]), w8_11[1]);
    let r1 = a32(a32(su1_sig(w12_15[3]), tw0_3[1]), w8_11[2]);
    let r2 = a32(a32(su1_sig(r0), tw0_3[2]), w8_11[3]);
    let r3 = a32(a32(su1_sig(r1), tw0_3[3]), w12_15[0]);
    let r = [r0, r1, r2, r3];
    assert(r@ =~= isa::sha256su1(tw0_3@, w8_11@, w12_15@));
    r
}

fn big64(x: u64, a: u64, b: u64, c: u64) -> (r: u64)
    requires
        0 < a < 64,
        0 < b < 64,
        0 < c < 64,
    ensures
        r == isa::ror64(x, a) ^ isa::ror64(x, b) ^ isa::ror64(x, c),
{
    ror64(x, a) ^ ror64(x, b) ^ ror64(x, c)
}

/// `SHA512H`.
pub fn sha512h(w: [u64; 2], x: [u64; 2], y: [u64; 2]) -> (r: [u64; 2])
    ensures
        r@ == isa::sha512h(w@, x@, y@),
{
    let ms1 = big64(y[1], 14, 18, 41);
    let hi0 = (y[1] & x[0]) ^ (!y[1] & x[1]);
    let hi = a64(a64(hi0, ms1), w[1]);
    let tmp = a64(hi, y[0]);
    let ms1b = big64(tmp, 14, 18, 41);
    let lo0 = (tmp & y[1]) ^ (!tmp & x[0]);
    let lo = a64(a64(lo0, ms1b), w[0]);
    let r = [lo, hi];
    assert(r@ =~= isa::sha512h(w@, x@, y@));
    r
}

/// `SHA512H2`.
pub fn sha512h2(w: [u64; 2], x: [u64; 2], y: [u64; 2]) -> (r: [u64; 2])
    ensures
        r@ == isa::sha512h2(w@, x@, y@),
{
    let ns0 = big64(y[0], 28, 34, 39);
    let hi0 = (x[0] & y[1]) ^ (x[0] & y[0]) ^ (y[1] & y[0]);
    let hi = a64(a64(hi0, ns0), w[1]);
    let ns0b = big64(hi, 28, 34, 39);
    let lo0 = (hi & y[0]) ^ (hi & y[1]) ^ (y[1] & y[0]);
    let lo = a64(a64(lo0, ns0b), w[0]);
    let r = [lo, hi];
    assert(r@ =~= isa::sha512h2(w@, x@, y@));
    r
}

/// `SHA512SU0`.
pub fn sha512su0(w: [u64; 2], x: [u64; 2]) -> (r: [u64; 2])
    ensures
        r@ == isa::sha512su0(w@, x@),
{
    let s0 = ror64(w[1], 1) ^ ror64(w[1], 8) ^ (w[1] >> 7);
    let s1 = ror64(x[0], 1) ^ ror64(x[0], 8) ^ (x[0] >> 7);
    let r = [a64(w[0], s0), a64(w[1], s1)];
    assert(r@ =~= isa::sha512su0(w@, x@));
    r
}

/// `SHA512SU1`.
pub fn sha512su1(w: [u64; 2], x: [u64; 2], y: [u64; 2]) -> (r: [u64; 2])
    ensures
        r@ == isa::sha512su1(w@, x@, y@),
{
    let s1 = ror64(x[1], 19) ^ ror64(x[1], 61) ^ (x[1] >> 6);
    let s0 = ror64(x[0], 19) ^ ror64(x[0], 61) ^ (x[0] >> 6);
    let r = [a64(a64(w[0], s0), y[0]), a64(a64(w[1], s1), y[1])];
    assert(r@ =~= isa::sha512su1(w@, x@, y@));
    r
}

/// `PBLENDW`.
pub fn blend16(a: [u8; 16], b: [u8; 16], imm: u8) -> (r: [u8; 16])
    ensures
        r@ == isa::blend16(a@, b@, imm as int),
{
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] isa::blend16(a@, b@, imm as int)[j],
        decreases 16 - i,
    {
        let bit = (imm >> ((i / 2) as u8)) & 1;
        proof {
            let k = (i / 2) as u8;
            assert(k < 8);
            lemma_bit(imm, k);
        }
        r[i] = if bit == 1 { b[i] } else { a[i] };
        i = i + 1;
    }
    assert(r@ =~= isa::blend16(a@, b@, imm as int));
    r
}

/// Bit `k` of `x` as the spec reads it.
proof fn lemma_bit(x: u8, k: u8)
    requires
        k < 8,
    ensures
        ((x >> k) & 1u8 == 1u8) == ((x as int / vstd::arithmetic::power2::pow2(k as nat) as int) % 2 == 1),
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::bits::lemma_u8_shr_is_div(x, k);
    let s = x >> k;
    assert(s & 1u8 == s % 2) by (bit_vector);
}

/// `REV32` on bytes.
pub fn rev32(a: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == isa::rev32(a@),
{
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] isa::rev32(a@)[j],
        decreases 16 - i,
    {
        r[i] = a[4 * (i / 4) + 3 - i % 4];
        i = i + 1;
    }
    assert(r@ =~= isa::rev32(a@));
    r
}

/// `REV64` on bytes.
pub fn rev64(a: [u8; 16]) -> (r: [u8; 16])
    ensures
        r@ == isa::rev64(a@),
{
    let mut r = [0u8; 16];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] isa::rev64(a@)[j],
        decreases 16 - i,
    {
        r[i] = a[8 * (i / 8) + 7 - i % 8];
        i = i + 1;
    }
    assert(r@ =~= isa::rev64(a@));
    r
}

/// 64-bit lane `add`.
pub fn add64x2(a: [u64; 2], b: [u64; 2]) -> (r: [u64; 2])
    ensures
        r@ == isa::add64x2(a@, b@),
{
    let r = [a64(a[0], b[0]), a64(a[1], b[1])];
    assert(r@ =~= isa::add64x2(a@, b@));
    r
}

} // verus!
