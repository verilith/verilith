//! CRC-32 by folding with carry-less multiplication (`pclmulqdq`, and
//! `vpclmulqdq` on 512-bit vectors), proven to compute `crc_from`.
//!
//! The method is Intel's ("Fast CRC Computation for Generic Polynomials
//! Using PCLMULQDQ"): keep the input as 128-bit blocks, and move each block
//! forward over the data with two carry-less products, by constants that
//! are powers of x modulo the polynomial, XORing it onto the block that far
//! ahead. At the end one block is left, with the CRC effect of everything
//! before it, and its sixteen bytes go through the table code.
//!
//! The proof has three layers, all here and all verified:
//!
//! - **The register as a 128-bit shift register** (`wsteps`): the CRC
//!   register after sixteen bytes `v` is `v` stepped 128 times with the
//!   data above the register bits (`lemma_crc16_wide`). So `crc16`, the
//!   register after a block, is linear and shifting a block left one bit
//!   steps its register once less (`lemma_crc16_shl`).
//! - **One fold** (`lemma_fold`): with `fold_k(n) = crc_steps(POLY, n) << 1`,
//!   the carry-less product of a quadword with `fold_k` has the register of
//!   that quadword stepped `n` bits further. This is shown for the top bit
//!   by evaluating both sides, then for each lower bit by `lemma_crc16_shl`,
//!   then for any quadword by linearity. The constants are not trusted
//!   numbers: they are computed by the verified `lanes::steps_exec`.
//! - **Runs of blocks** (`eff`): the register after a run of blocks is the
//!   XOR of each block's register stepped past the blocks after it, so a
//!   run can be folded onto the next run (`lemma_eff_step`) and four
//!   blocks folded into one (`lemma_eff4`).
//!
//! The kernels at the end (x86-64 only) are verified against these; what
//! they trust is `vclmul.rs`: that the instructions compute `clmul` and
//! that loads read bytes in order.
#[cfg(verus_only)]
use super::lanes::lemma_steps_zero;
#[cfg(verus_only)]
use super::spec::{crc_step, crc_steps, CRC_POLY};
#[cfg(verus_only)]
use super::{crc_from, lemma_crc_append, lemma_steps_add, lemma_steps_xor};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The register as a 128-bit shift register.
// ---------------------------------------------------------------------------

/// One bit step of a 128-bit register: `crc_step` with the data still to
/// come held above the 32 register bits.
pub open spec fn wstep(v: u128) -> u128 {
    if v & 1 == 1 { (v >> 1u128) ^ (CRC_POLY as u128) } else { v >> 1u128 }
}

pub open spec fn wsteps(v: u128, n: nat) -> u128 decreases n {
    if n == 0 { v } else { wsteps(wstep(v), (n - 1) as nat) }
}

/// The sixteen bytes of `v`, least significant first.
pub open spec fn bytes16(v: u128) -> Seq<u8> {
    Seq::new(16, |k: int| (v >> (8 * k) as u128) as u8)
}

/// The register after the sixteen bytes of `v`, from zero.
pub open spec fn crc16(v: u128) -> u32 {
    crc_from(0, bytes16(v))
}

pub proof fn lemma_wstep_xor(a: u128, b: u128)
    ensures wstep(a ^ b) == wstep(a) ^ wstep(b),
{
    assert((if (a ^ b) & 1 == 1 { ((a ^ b) >> 1) ^ 0xedb88320u128 } else { (a ^ b) >> 1 })
        == (if a & 1 == 1 { (a >> 1) ^ 0xedb88320u128 } else { a >> 1 }) ^ (if b & 1 == 1 {
        (b >> 1) ^ 0xedb88320u128 } else { b >> 1 })) by (bit_vector);
}

pub proof fn lemma_wsteps_xor(a: u128, b: u128, n: nat)
    ensures wsteps(a ^ b, n) == wsteps(a, n) ^ wsteps(b, n), decreases n,
{
    if n > 0 {
        lemma_wstep_xor(a, b);
        lemma_wsteps_xor(wstep(a), wstep(b), (n - 1) as nat);
    }
}

pub proof fn lemma_wsteps_add(a: u128, m: nat, n: nat)
    ensures wsteps(wsteps(a, m), n) == wsteps(a, m + n), decreases m,
{
    if m > 0 {
        lemma_wsteps_add(wstep(a), (m - 1) as nat, n);
        assert((m - 1) as nat + n == (m + n - 1) as nat);
    }
}

/// Steps of a value whose low `n` bits are zero only shift it.
pub proof fn lemma_wsteps_shift(y: u128, n: nat)
    requires
        n < 128,
        y & ((1u128 << n as u128) - 1) as u128 == 0,
    ensures
        wsteps(y, n) == y >> n as u128,
    decreases n,
{
    if n == 0 {
        assert(y >> 0u128 == y) by (bit_vector);
    } else {
        let nu = n as u128;
        assert(y & 1 == 0 && (y >> 1u128) & ((1u128 << (nu - 1) as u128) - 1) as u128 == 0
            && (y >> 1u128) >> (nu - 1) as u128 == y >> nu) by (bit_vector)
            requires 0 < nu < 128, y & ((1u128 << nu) - 1) as u128 == 0;
        lemma_wsteps_shift(y >> 1u128, (n - 1) as nat);
    }
}

/// Below 2^32 the 128-bit register is the CRC register.
pub proof fn lemma_wsteps_narrow(v: u128, n: nat)
    requires v < 0x1_0000_0000,
    ensures wsteps(v, n) == crc_steps(v as u32, n) as u128, wsteps(v, n) < 0x1_0000_0000,
    decreases n,
{
    if n > 0 {
        let c = v as u32;
        assert(wstep(v) == crc_step(c) as u128 && wstep(v) < 0x1_0000_0000) by (bit_vector)
            requires v < 0x1_0000_0000, c == v as u32;
        lemma_wsteps_narrow(wstep(v), (n - 1) as nat);
    }
}

/// What remains of `v` above its first `k` bytes.
pub open spec fn rest(v: u128, k: nat) -> u128 {
    if k < 16 { v >> (8 * k) as u128 } else { 0 }
}

/// The 128-bit register over the first `k` bytes of `v`, from `c`: the CRC
/// register, with the bytes still to come above it.
proof fn lemma_wide_prefix(c: u32, v: u128, k: nat)
    requires k <= 16,
    ensures wsteps((c as u128) ^ v, 8 * k) == (crc_from(c, bytes16(v).take(k as int)) as u128) ^ rest(v, k),
    decreases k,
{
    let d = bytes16(v);
    if k == 0 {
        assert(d.take(0) =~= Seq::<u8>::empty());
        assert(v >> 0u128 == v) by (bit_vector);
    } else {
        let j = (k - 1) as nat;
        lemma_wide_prefix(c, v, j);
        let r = crc_from(c, d.take(j as int));
        let h = rest(v, j);
        let b = d[j as int];
        let s = j as u128;
        assert(h == v >> (8 * s)) by { assert(j < 16); }
        assert(b == (v >> (8 * s)) as u8);
        // h is the byte b, then the rest above it.
        let hi = h & !0xffu128;
        assert(h == (b as u128) ^ hi && hi & ((1u128 << 8u128) - 1) as u128 == 0) by (bit_vector)
            requires b == h as u8, hi == h & !0xffu128;
        lemma_wsteps_shift(hi, 8);
        assert(hi >> 8u128 == rest(v, k)) by {
            if k < 16 {
                assert((((v >> (8 * s)) & !0xffu128) >> 8u128) == v >> (8 * (s + 1))) by (bit_vector)
                    requires s < 15;
            } else {
                assert(s == 15);
                assert((((v >> (8 * s)) & !0xffu128) >> 8u128) == 0) by (bit_vector)
                    requires s == 15;
            }
        }
        let x = (r as u128) ^ (b as u128);
        assert((r as u128) ^ h == x ^ hi) by (bit_vector)
            requires h == (b as u128) ^ hi, x == (r as u128) ^ (b as u128);
        assert(x < 0x1_0000_0000 && x as u32 == r ^ (b as u32)) by (bit_vector)
            requires x == (r as u128) ^ (b as u128);
        lemma_wsteps_add((c as u128) ^ v, 8 * j, 8);
        assert(8 * j + 8 == 8 * k);
        lemma_wsteps_xor(x, hi, 8);
        lemma_wsteps_narrow(x, 8);
        assert(d.take(k as int).drop_last() =~= d.take(j as int));
        assert(d.take(k as int).last() == b);
    }
}

/// The register after the sixteen bytes of `v`, from `c`.
pub proof fn lemma_crc16_wide(c: u32, v: u128)
    ensures
        crc_from(c, bytes16(v)) as u128 == wsteps((c as u128) ^ v, 128),
        wsteps((c as u128) ^ v, 128) < 0x1_0000_0000,
{
    lemma_wide_prefix(c, v, 16);
    assert(bytes16(v).take(16) =~= bytes16(v));
    let r = crc_from(c, bytes16(v));
    assert((r as u128) ^ 0u128 == r as u128) by (bit_vector);
}

pub proof fn lemma_crc16_xor(u: u128, v: u128)
    ensures crc16(u ^ v) == crc16(u) ^ crc16(v),
{
    lemma_crc16_wide(0, u);
    lemma_crc16_wide(0, v);
    lemma_crc16_wide(0, u ^ v);
    assert(0u128 ^ u == u && 0u128 ^ v == v && 0u128 ^ (u ^ v) == u ^ v) by (bit_vector);
    lemma_wsteps_xor(u, v, 128);
    let a = crc16(u);
    let b = crc16(v);
    assert(((a as u128) ^ (b as u128)) as u32 == a ^ b) by (bit_vector);
}

/// Starting from `c` is the same as XORing `c` into the first four bytes.
pub proof fn lemma_crc16_from(c: u32, v: u128)
    ensures crc_from(c, bytes16(v)) == crc16((c as u128) ^ v),
{
    lemma_crc16_wide(c, v);
    lemma_crc16_wide(0, (c as u128) ^ v);
    assert(0u128 ^ ((c as u128) ^ v) == (c as u128) ^ v) by (bit_vector);
}

/// A register value as sixteen bytes: steps past them.
pub proof fn lemma_crc16_reg(c: u32)
    ensures crc16(c as u128) == crc_steps(c, 128),
{
    lemma_crc16_wide(0, c as u128);
    assert(0u128 ^ (c as u128) == c as u128) by (bit_vector);
    lemma_wsteps_narrow(c as u128, 128);
    assert((c as u128) as u32 == c) by (bit_vector);
}

/// Shifting the data one bit later steps the register once less.
pub proof fn lemma_crc16_shl(v: u128)
    requires v < 0x8000_0000_0000_0000_0000_0000_0000_0000u128,
    ensures crc16(v) == crc_step(crc16(v << 1u128)),
{
    let w = v << 1u128;
    lemma_crc16_wide(0, v);
    lemma_crc16_wide(0, w);
    assert(0u128 ^ v == v && 0u128 ^ w == w) by (bit_vector);
    assert(w & 1 == 0 && w >> 1u128 == v) by (bit_vector)
        requires w == v << 1u128, v < 0x8000_0000_0000_0000_0000_0000_0000_0000u128;
    assert(wstep(w) == v);
    lemma_wsteps_add(w, 1, 127);
    lemma_wsteps_add(v, 127, 1);
    let t = wsteps(w, 128);
    assert(wsteps(wstep(w), 0) == wstep(w));
    assert(wsteps(w, 1) == wstep(w));
    assert(wsteps(v, 127 + 1) == wsteps(wsteps(v, 127), 1));
    assert(t == wsteps(v, 127));
    lemma_wsteps_narrow(t, 1);
    let c = crc16(w);
    assert(t == c as u128);
    assert((c as u128) as u32 == c) by (bit_vector);
    lemma_steps_one(c);
    let a = crc16(v);
    let b = crc_step(c);
    assert(a as u128 == b as u128 ==> a == b) by (bit_vector);
}

pub proof fn lemma_steps_one(c: u32)
    ensures crc_steps(c, 1) == crc_step(c),
{
    assert(crc_steps(crc_step(c), 0) == crc_step(c));
}

pub proof fn lemma_crc16_zero()
    ensures crc16(0) == 0,
{
    lemma_crc16_wide(0, 0);
    assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    lemma_wsteps_narrow(0, 128);
    lemma_steps_zero(128);
    let a = crc16(0);
    assert(a as u128 == 0 ==> a == 0) by (bit_vector);
}

// ---------------------------------------------------------------------------
// Carry-less multiplication
// ---------------------------------------------------------------------------

/// The carry-less product of `a`'s bits `i < n` with `b` (`pclmulqdq`).
pub open spec fn clmul_n(a: u64, b: u64, n: nat) -> u128 decreases n {
    if n == 0 {
        0
    } else {
        clmul_n(a, b, (n - 1) as nat) ^ (if (a >> (n - 1) as u64) & 1 == 1 {
            (b as u128) << (n - 1) as u128
        } else {
            0
        })
    }
}

/// The 128-bit carry-less product of `a` and `b`.
pub open spec fn clmul(a: u64, b: u64) -> u128 {
    clmul_n(a, b, 64)
}

/// The low `n` bits of `a`.
pub open spec fn low_bits(a: u64, n: nat) -> u64 {
    if n >= 64 { a } else { a & ((1u64 << n as u64) - 1) as u64 }
}

/// A fold constant: `x^n mod P` in the reflected form `pclmulqdq` takes.
/// `crc_steps(POLY, n)` is the register of a 1 bit `n + 1` bits back; the
/// shift makes room for the product's bit 0 lining up with data bit 0.
pub open spec fn fold_k(n: nat) -> u64 {
    (crc_steps(CRC_POLY, n) as u64) << 1u64
}

/// For `k = fold_k(n)`: the product of `1 << j` with `k` has the CRC effect
/// of the bit `j` advanced by `n + 64` steps, where `(1 << j)` is
/// at bit `j + o` of the block (o = 0 for the low quadword, 64 for the high).
proof fn lemma_fold_pow(n: nat, o: nat, j: nat)
    requires
        o == 0 || o == 64,
        o == 0 || n >= 64,
        j < 64,
    ensures
        crc16((fold_k((n - o) as nat) as u128) << j as u128) == crc_steps(crc16(1u128 << (j + o) as u128), n),
    decreases 64 - j,
{
    let n2 = (n - o) as nat;
    let r = crc_steps(CRC_POLY, n2);
    let k = fold_k(n2);
    assert(k == (r as u64) << 1u64);
    let ju = j as u128;
    let ou = o as u128;
    if j == 63 {
        // k << 63: 63 shifts bring k down; one step makes it r; 64 more
        // steps are what the data block has left.
        let w = (k as u128) << 63u128;
        assert(w & ((1u128 << 63u128) - 1) as u128 == 0 && w >> 63u128 == k as u128) by (bit_vector)
            requires w == (k as u128) << 63u128, k == (r as u64) << 1u64;
        lemma_wsteps_shift(w, 63);
        assert(wstep(k as u128) == r as u128) by (bit_vector)
            requires k == (r as u64) << 1u64;
        lemma_wsteps_add(w, 63, 65);
        lemma_wsteps_add(k as u128, 1, 64);
        lemma_wsteps_narrow(r as u128, 64);
        assert((r as u128) as u32 == r) by (bit_vector);
        lemma_crc16_wide(0, w);
        assert(0u128 ^ w == w) by (bit_vector);
        assert(crc16(w) as u128 == crc_steps(r, 64) as u128);
        assert(crc16(w) == crc_steps(r, 64)) by {
            let a = crc16(w);
            let b = crc_steps(r, 64);
            assert(a as u128 == b as u128 ==> a == b) by (bit_vector);
        }
        // The bit itself: 63 + o shifts, then one step makes it POLY, then
        // 64 - o more.
        let e = 1u128 << (63 + ou);
        assert(e & ((1u128 << (63 + ou)) - 1) as u128 == 0 && e >> (63 + ou) == 1u128) by (bit_vector)
            requires e == 1u128 << (63 + ou), ou == 0 || ou == 64;
        assert((63 + o) as u128 == 63 + ou);
        lemma_wsteps_shift(e, (63 + o) as nat);
        assert(1u128 & 1 == 1 && (1u128 >> 1u128) ^ 0xedb88320u128 == 0xedb88320u128) by (bit_vector);
        assert(wstep(1u128) == CRC_POLY as u128);
        lemma_wsteps_add(e, (63 + o) as nat, (65 - o) as nat);
        lemma_wsteps_add(1u128, 1, (64 - o) as nat);
        lemma_wsteps_narrow(CRC_POLY as u128, (64 - o) as nat);
        lemma_crc16_wide(0, e);
        assert(0u128 ^ e == e) by (bit_vector);
        assert((CRC_POLY as u128) as u32 == CRC_POLY);
        let pe = crc_steps(CRC_POLY, (64 - o) as nat);
        assert(crc16(e) == pe) by {
            let a = crc16(e);
            assert(a as u128 == pe as u128 ==> a == pe) by (bit_vector);
        }
        assert((j + o) as u128 == 63 + ou);
        // r stepped 64 == POLY stepped (64 - o) then n.
        lemma_steps_add(CRC_POLY, n2, 64);
        lemma_steps_add(CRC_POLY, (64 - o) as nat, n);
        assert(n2 + 64 == (64 - o) as nat + n);
    } else {
        lemma_fold_pow(n, o, j + 1);
        // Both sides one bit lower: one more step each.
        let w = (k as u128) << (ju + 1);
        let v = (k as u128) << ju;
        assert(v < 0x8000_0000_0000_0000_0000_0000_0000_0000u128 && v << 1u128 == w) by (bit_vector)
            requires v == (k as u128) << ju, w == (k as u128) << (ju + 1), ju < 63, k == (r as u64) << 1u64;
        assert((j + 1) as u128 == ju + 1);
        lemma_crc16_shl(v);
        let e1 = 1u128 << (ju + 1 + ou);
        let e = 1u128 << (ju + ou);
        assert(e < 0x8000_0000_0000_0000_0000_0000_0000_0000u128 && e << 1u128 == e1) by (bit_vector)
            requires e1 == 1u128 << (ju + 1 + ou), e == 1u128 << (ju + ou), ju < 63, ou == 0 || ou == 64;
        assert((j + 1 + o) as u128 == ju + 1 + ou);
        assert((j + o) as u128 == ju + ou);
        lemma_crc16_shl(e);
        let x = crc16(e1);
        lemma_steps_add(x, 1, n);
        lemma_steps_add(x, n, 1);
        lemma_steps_one(x);
        lemma_steps_one(crc_steps(x, n));
        let y = crc16(w);
        lemma_steps_one(y);
        assert(1 + n == n + 1);
    }
}

proof fn lemma_clmul_n_xor(a: u64, c: u64, b: u64, n: nat)
    ensures clmul_n(a ^ c, b, n) == clmul_n(a, b, n) ^ clmul_n(c, b, n),
    decreases n,
{
    if n == 0 {
        assert(0u128 ^ 0u128 == 0u128) by (bit_vector);
    }
    if n > 0 {
        lemma_clmul_n_xor(a, c, b, (n - 1) as nat);
        let i = (n - 1) as u64;
        let p = clmul_n(a, b, (n - 1) as nat);
        let q = clmul_n(c, b, (n - 1) as nat);
        let t = (b as u128) << (n - 1) as u128;
        let ba = (a >> i) & 1 == 1;
        let bc = (c >> i) & 1 == 1;
        assert(((a ^ c) >> i) & 1 == 1 <==> (ba != bc)) by (bit_vector)
            requires ba == ((a >> i) & 1 == 1), bc == ((c >> i) & 1 == 1);
        assert(clmul_n(a ^ c, b, n) == clmul_n(a ^ c, b, (n - 1) as nat) ^ (if ((a ^ c) >> i) & 1 == 1 { t } else { 0 }));
        assert(clmul_n(a, b, n) == p ^ (if ba { t } else { 0 }));
        assert(clmul_n(c, b, n) == q ^ (if bc { t } else { 0 }));
        assert((p ^ q) ^ (if ba != bc { t } else { 0 }) == (p ^ (if ba { t } else { 0 })) ^ (q ^ (if bc { t } else { 0 }))) by (bit_vector);
    }
}

/// The fold: the carry-less product of the low quadword with
/// `fold_k(n)` has the CRC effect of that quadword advanced `n + 64` bits.
proof fn lemma_fold_lane(a: u64, n: nat, o: nat, m: nat)
    requires
        o == 0 || o == 64,
        o == 0 || n >= 64,
        m <= 64,
    ensures
        crc16(clmul_n(a, fold_k((n - o) as nat), m)) == crc_steps(crc16((low_bits(a, m) as u128) << o as u128), n),
    decreases m,
{
    let ou = o as u128;
    let k = fold_k((n - o) as nat);
    if m == 0 {
        assert(low_bits(a, 0) == 0) by { assert(a & ((1u64 << 0u64) - 1) as u64 == 0) by (bit_vector); }
        assert((0u64 as u128) << ou == 0) by (bit_vector);
        lemma_crc16_zero();
        lemma_steps_zero(n);
    } else {
        let j = (m - 1) as nat;
        let ju = j as u64;
        lemma_fold_lane(a, n, o, j);
        let lo = low_bits(a, j);
        let hi = low_bits(a, m);
        let bit = (a >> ju) & 1 == 1;
        assert(hi == lo ^ (if bit { 1u64 << ju } else { 0 })) by {
            if m < 64 {
                assert(a & ((1u64 << (ju + 1)) - 1) as u64 == (a & ((1u64 << ju) - 1) as u64) ^ (if (a >> ju) & 1 == 1 { 1u64 << ju } else { 0 })) by (bit_vector)
                    requires ju < 63;
                assert((j + 1) as u64 == ju + 1);
            } else {
                assert(a == (a & ((1u64 << ju) - 1) as u64) ^ (if (a >> ju) & 1 == 1 { 1u64 << ju } else { 0 })) by (bit_vector)
                    requires ju == 63;
            }
        }
        let lw = (lo as u128) << ou;
        let bw = (if bit { 1u128 << (ju as u128 + ou) } else { 0 });
        assert((hi as u128) << ou == lw ^ bw) by (bit_vector)
            requires hi == lo ^ (if bit { 1u64 << ju } else { 0 }), lw == (lo as u128) << ou,
                bw == (if bit { 1u128 << (ju as u128 + ou) } else { 0 }), ju < 64, ou == 0 || ou == 64;
        lemma_crc16_xor(lw, bw);
        lemma_steps_xor(crc16(lw), crc16(bw), n);
        let t = (k as u128) << j as u128;
        let p = clmul_n(a, k, j);
        lemma_crc16_xor(p, if bit { t } else { 0 });
        if bit {
            lemma_fold_pow(n, o, j);
            assert((j + o) as u128 == ju as u128 + ou);
        } else {
            lemma_crc16_zero();
            lemma_steps_zero(n);
            let z = crc16(lw);
            assert(z ^ 0u32 == z) by (bit_vector);
            let pp = crc16(p);
            assert(pp ^ 0u32 == pp) by (bit_vector);
        }
    }
}




/// The low and high quadwords of a block.
pub open spec fn lo64(v: u128) -> u64 { v as u64 }
pub open spec fn hi64(v: u128) -> u64 { (v >> 64u128) as u64 }

/// A pair of fold constants as `pclmulqdq` reads them: the low quadword
/// multiplies a block's low quadword, the high one its high quadword.
pub open spec fn fold_pair(n: nat) -> u128 {
    ((fold_k((n - 64) as nat) as u128) << 64u128) | (fold_k(n) as u128)
}

/// `lo64(a) * lo64(k) ^ hi64(a) * hi64(k)`, carry-less: `pclmulqdq` with
/// immediates 0x00 and 0x11, XORed.
pub open spec fn fold_with(a: u128, k: u128) -> u128 {
    clmul(lo64(a), lo64(k)) ^ clmul(hi64(a), hi64(k))
}

/// A block's CRC effect `n` bits later, as a block.
pub open spec fn fold(v: u128, n: nat) -> u128 {
    fold_with(v, fold_pair(n))
}

pub proof fn lemma_fold(v: u128, n: nat)
    requires n >= 64,
    ensures crc16(fold(v, n)) == crc_steps(crc16(v), n),
{
    let p = fold_pair(n);
    let kl = fold_k(n);
    let kh = fold_k((n - 64) as nat);
    assert(lo64(p) == kl && hi64(p) == kh) by (bit_vector)
        requires p == ((kh as u128) << 64u128) | (kl as u128);
    let a = lo64(v);
    let b = hi64(v);
    lemma_fold_lane(a, n, 0, 64);
    lemma_fold_lane(b, n, 64, 64);
    assert(low_bits(a, 64) == a && low_bits(b, 64) == b);
    assert((a as u128) << 0u128 == a as u128) by (bit_vector);
    assert(v == (a as u128) ^ ((b as u128) << 64u128)) by (bit_vector)
        requires a == v as u64, b == (v >> 64u128) as u64;
    assert((n - 0) as nat == n);
    lemma_crc16_xor(a as u128, (b as u128) << 64u128);
    lemma_steps_xor(crc16(a as u128), crc16((b as u128) << 64u128), n);
    lemma_crc16_xor(clmul(a, kl), clmul(b, kh));
}

// ---------------------------------------------------------------------------
// Runs of blocks
// ---------------------------------------------------------------------------

/// The bytes of blocks `xs`, in order.
pub open spec fn flat(xs: Seq<u128>) -> Seq<u8> decreases xs.len() {
    if xs.len() == 0 { Seq::empty() } else { flat(xs.drop_last()) + bytes16(xs.last()) }
}

/// The CRC effect of blocks `xs` from register zero: each block's own
/// register, stepped past the blocks after it.
pub open spec fn eff(xs: Seq<u128>) -> u32 decreases xs.len() {
    if xs.len() == 0 { 0 } else { crc_steps(eff(xs.drop_last()), 128) ^ crc16(xs.last()) }
}

pub proof fn lemma_flat_len(xs: Seq<u128>)
    ensures flat(xs).len() == 16 * xs.len(), decreases xs.len(),
{
    if xs.len() > 0 { lemma_flat_len(xs.drop_last()); }
}

/// The register after blocks `xs` from `c`.
pub proof fn lemma_eff(c: u32, xs: Seq<u128>)
    ensures crc_from(c, flat(xs)) == crc_steps(c, 128 * xs.len()) ^ eff(xs),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(c ^ 0u32 == c) by (bit_vector);
    } else {
        let ys = xs.drop_last();
        let x = xs.last();
        lemma_eff(c, ys);
        lemma_crc_append(c, flat(ys), bytes16(x));
        let r = crc_from(c, flat(ys));
        lemma_crc16_from(r, x);
        lemma_crc16_xor(r as u128, x);
        lemma_crc16_reg(r);
        let s = crc_steps(c, 128 * ys.len());
        let e = eff(ys);
        lemma_steps_xor(s, e, 128);
        lemma_steps_add(c, 128 * ys.len(), 128);
        assert(128 * ys.len() + 128 == 128 * xs.len());
        let p = crc_steps(s, 128);
        let q = crc_steps(e, 128);
        let t = crc16(x);
        assert((p ^ q) ^ t == p ^ (q ^ t)) by (bit_vector);
    }
}

pub proof fn lemma_eff_zero(xs: Seq<u128>)
    ensures crc_from(0, flat(xs)) == eff(xs),
{
    lemma_eff(0, xs);
    lemma_steps_zero(128 * xs.len());
    let e = eff(xs);
    assert(0u32 ^ e == e) by (bit_vector);
}

/// Blocks combined lane by lane with XOR.
pub open spec fn xors(xs: Seq<u128>, ys: Seq<u128>) -> Seq<u128> {
    Seq::new(xs.len(), |j: int| xs[j] ^ ys[j])
}

/// Each block folded `n` bits.
pub open spec fn folds(xs: Seq<u128>, n: nat) -> Seq<u128> {
    Seq::new(xs.len(), |j: int| fold(xs[j], n))
}

pub proof fn lemma_eff_xor(xs: Seq<u128>, ys: Seq<u128>)
    requires xs.len() == ys.len(),
    ensures eff(xors(xs, ys)) == eff(xs) ^ eff(ys),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(0u32 ^ 0u32 == 0u32) by (bit_vector);
    } else {
        let a = xs.drop_last();
        let b = ys.drop_last();
        lemma_eff_xor(a, b);
        assert(xors(xs, ys).drop_last() =~= xors(a, b));
        lemma_steps_xor(eff(a), eff(b), 128);
        lemma_crc16_xor(xs.last(), ys.last());
        let p = crc_steps(eff(a), 128);
        let q = crc_steps(eff(b), 128);
        let u = crc16(xs.last());
        let v = crc16(ys.last());
        assert((p ^ q) ^ (u ^ v) == (p ^ u) ^ (q ^ v)) by (bit_vector);
    }
}

pub proof fn lemma_eff_folds(xs: Seq<u128>, n: nat)
    requires n >= 64,
    ensures eff(folds(xs, n)) == crc_steps(eff(xs), n),
    decreases xs.len(),
{
    if xs.len() == 0 {
        lemma_steps_zero(n);
    } else {
        let a = xs.drop_last();
        lemma_eff_folds(a, n);
        assert(folds(xs, n).drop_last() =~= folds(a, n));
        lemma_fold(xs.last(), n);
        let e = eff(a);
        lemma_steps_add(e, n, 128);
        lemma_steps_add(e, 128, n);
        assert(n + 128 == 128 + n);
        lemma_steps_xor(crc_steps(e, 128), crc16(xs.last()), n);
    }
}

pub proof fn lemma_eff_append(xs: Seq<u128>, ys: Seq<u128>)
    ensures eff(xs + ys) == crc_steps(eff(xs), 128 * ys.len()) ^ eff(ys),
    decreases ys.len(),
{
    if ys.len() == 0 {
        assert(xs + ys =~= xs);
        assert(crc_steps(eff(xs), 0) == eff(xs));
        let e = eff(xs);
        assert(e ^ 0u32 == e) by (bit_vector);
    } else {
        let b = ys.drop_last();
        lemma_eff_append(xs, b);
        assert((xs + ys).drop_last() =~= xs + b);
        assert((xs + ys).last() == ys.last());
        let s = crc_steps(eff(xs), 128 * b.len());
        lemma_steps_xor(s, eff(b), 128);
        lemma_steps_add(eff(xs), 128 * b.len(), 128);
        assert(128 * b.len() + 128 == 128 * ys.len());
        let p = crc_steps(s, 128);
        let q = crc_steps(eff(b), 128);
        let t = crc16(ys.last());
        assert((p ^ q) ^ t == p ^ (q ^ t)) by (bit_vector);
    }
}

/// The main loop's step: the next run of blocks after `xs`, with `xs`
/// folded onto it, has the same effect as both.
pub proof fn lemma_eff_step(xs: Seq<u128>, ys: Seq<u128>)
    requires xs.len() == ys.len(), xs.len() >= 1,
    ensures eff(xs + ys) == eff(xors(folds(xs, 128 * xs.len()), ys)),
{
    lemma_eff_append(xs, ys);
    lemma_eff_xor(folds(xs, 128 * xs.len()), ys);
    lemma_eff_folds(xs, 128 * xs.len());
}

/// Starting from `c`: `c` XORed into the first block.
pub proof fn lemma_eff_reg(c: u32, xs: Seq<u128>)
    requires xs.len() >= 1,
    ensures crc_from(c, flat(xs)) == eff(xs.update(0, xs[0] ^ (c as u128))),
    decreases xs.len(),
{
    let ys = xs.update(0, xs[0] ^ (c as u128));
    lemma_eff(c, xs);
    let zs = Seq::new(xs.len(), |j: int| if j == 0 { c as u128 } else { 0u128 });
    assert(ys =~= xors(xs, zs)) by {
        assert forall|j: int| 0 <= j < xs.len() implies ys[j] == #[trigger] xors(xs, zs)[j] by {
            if j != 0 { let x = xs[j]; assert(x ^ 0u128 == x) by (bit_vector); }
        }
    }
    lemma_eff_xor(xs, zs);
    lemma_eff_unit(c, xs.len());
    assert(zs =~= Seq::new(xs.len(), |j: int| if j == 0 { c as u128 } else { 0u128 }));
    let s = crc_steps(c, 128 * xs.len());
    let e = eff(xs);
    assert(s ^ e == e ^ s) by (bit_vector);
}

proof fn lemma_eff_unit(c: u32, n: nat)
    requires n >= 1,
    ensures eff(Seq::new(n, |j: int| if j == 0 { c as u128 } else { 0u128 })) == crc_steps(c, 128 * n),
    decreases n,
{
    let zs = Seq::new(n, |j: int| if j == 0 { c as u128 } else { 0u128 });
    lemma_crc16_zero();
    if n == 1 {
        assert(zs.drop_last() =~= Seq::<u128>::empty());
        assert(eff(Seq::<u128>::empty()) == 0);
        assert(zs.last() == c as u128);
        lemma_steps_zero(128);
        lemma_crc16_reg(c);
        let t = crc16(c as u128);
        assert(0u32 ^ t == t) by (bit_vector);
        assert(eff(zs) == crc_steps(eff(zs.drop_last()), 128) ^ crc16(zs.last()));
    } else {
        let m = (n - 1) as nat;
        lemma_eff_unit(c, m);
        assert(zs.drop_last() =~= Seq::new(m, |j: int| if j == 0 { c as u128 } else { 0u128 }));
        assert(zs.last() == 0u128);
        lemma_steps_add(c, 128 * m, 128);
        assert(128 * m + 128 == 128 * n);
        let t = crc_steps(c, 128 * n);
        assert(t ^ 0u32 == t) by (bit_vector);
        assert(eff(zs) == crc_steps(eff(zs.drop_last()), 128) ^ crc16(zs.last()));
    }
}

/// Four blocks to one: each folded to the end, XORed.
pub proof fn lemma_eff4(xs: Seq<u128>)
    requires xs.len() == 4,
    ensures eff(xs) == crc16(fold(xs[0], 384) ^ fold(xs[1], 256) ^ fold(xs[2], 128) ^ xs[3]),
{
    let s0 = seq![xs[0]];
    let s1 = seq![xs[0], xs[1]];
    let s2 = seq![xs[0], xs[1], xs[2]];
    assert(xs.drop_last() =~= s2);
    assert(s2.drop_last() =~= s1);
    assert(s1.drop_last() =~= s0);
    assert(s0.drop_last() =~= Seq::<u128>::empty());
    assert(eff(Seq::<u128>::empty()) == 0);
    let (a, b, c, d) = (crc16(xs[0]), crc16(xs[1]), crc16(xs[2]), crc16(xs[3]));
    lemma_steps_zero(128);
    assert(0u32 ^ a == a) by (bit_vector);
    assert(eff(s0) == crc_steps(eff(s0.drop_last()), 128) ^ crc16(s0.last()));
    assert(eff(s0) == a);
    assert(eff(s1) == crc_steps(a, 128) ^ b);
    let a1 = crc_steps(a, 128);
    let a2 = crc_steps(a, 256);
    let a3 = crc_steps(a, 384);
    let b1 = crc_steps(b, 128);
    let b2 = crc_steps(b, 256);
    let c1 = crc_steps(c, 128);
    lemma_steps_add(a, 128, 128);
    lemma_steps_add(a, 256, 128);
    lemma_steps_add(b, 128, 128);
    lemma_steps_xor(a1, b, 128);
    assert(eff(s2) == crc_steps(a1 ^ b, 128) ^ c);
    assert(eff(s2) == (a2 ^ b1) ^ c);
    lemma_steps_xor(a2 ^ b1, c, 128);
    lemma_steps_xor(a2, b1, 128);
    assert(eff(xs) == crc_steps((a2 ^ b1) ^ c, 128) ^ d);
    assert(eff(xs) == ((a3 ^ b2) ^ c1) ^ d);
    lemma_fold(xs[0], 384);
    lemma_fold(xs[1], 256);
    lemma_fold(xs[2], 128);
    let (f0, f1, f2) = (fold(xs[0], 384), fold(xs[1], 256), fold(xs[2], 128));
    lemma_crc16_xor(f0, f1);
    lemma_crc16_xor(f0 ^ f1, f2);
    lemma_crc16_xor(f0 ^ f1 ^ f2, xs[3]);
}


// ---------------------------------------------------------------------------
// The last block to the register
// ---------------------------------------------------------------------------

/// Steps are a bijection on registers (the polynomial's top bit tells
/// whether the step XORed it), so equal results after `n` steps mean
/// equal registers before.
pub proof fn lemma_steps_inj(a: u32, b: u32, n: nat)
    requires
        crc_steps(a, n) == crc_steps(b, n),
    ensures
        a == b,
    decreases n,
{
    if n > 0 {
        lemma_steps_inj(crc_step(a), crc_step(b), (n - 1) as nat);
        assert(crc_step(a) == crc_step(b) ==> a == b) by (bit_vector);
    }
}

/// A value below `2^(m + 32)` is a register after `m` steps.
pub proof fn lemma_wsteps_bound(x: u128, m: nat)
    requires
        m <= 96,
        x >> (m + 32) as u128 == 0,
    ensures
        wsteps(x, m) >> 32u128 == 0,
    decreases m,
{
    if m > 0 {
        let mu = m as u128;
        assert(wstep(x) >> (mu + 31) == 0) by (bit_vector)
            requires
                1 <= mu <= 96,
                x >> (mu + 32) == 0,
                wstep(x) == (if x & 1 == 1 { (x >> 1u128) ^ 0xedb88320u128 } else { x >> 1u128 }),
        ;
        assert((m - 1 + 32) as u128 == mu + 31);
        lemma_wsteps_bound(wstep(x), (m - 1) as nat);
    }
}

/// `m` more steps of a value below `2^(m + 32)` (so a register after
/// them), then `k`.
proof fn lemma_wsteps_then(x: u128, m: nat, k: nat)
    requires
        m <= 96,
        x >> (m + 32) as u128 == 0,
    ensures
        wsteps(x, m + k) == crc_steps(wsteps(x, m) as u32, k) as u128,
        wsteps(x, m) == (wsteps(x, m) as u32) as u128,
{
    lemma_wsteps_bound(x, m);
    lemma_wsteps_add(x, m, k);
    let y = wsteps(x, m);
    assert(y >> 32u128 == 0 ==> y < 0x1_0000_0000 && (y as u32) as u128 == y) by (bit_vector);
    lemma_wsteps_narrow(y, k);
}

/// The register after the block `v` from its two halves: the low quadword
/// folded 64 bits onto the high one, then the low 32 bits of that folded
/// 32 bits onto the rest. What is left needs only 32 more steps.
pub proof fn lemma_reduce(v: u128)
    ensures
        ({
            let y = clmul(lo64(v), fold_k(64)) ^ (v >> 64u128);
            let z = clmul((y & 0xffff_ffffu128) as u64, fold_k(32)) ^ (y >> 32u128);
            crc16(v) == crc_steps(z as u32, 32) ^ ((z as u64) >> 32u64) as u32
        }),
{
    let lo = lo64(v);
    let hi = hi64(v);
    let k64 = fold_k(64);
    let k32 = fold_k(32);
    let p = clmul(lo, k64);
    let y = p ^ (v >> 64u128);
    let ylo = #[verifier::truncate] ((y & 0xffff_ffffu128) as u64);
    let q = clmul(ylo, k32);
    let z = q ^ (y >> 32u128);
    // Products of a quadword with a 33-bit constant have at most 96 bits.
    assert(k64 >> 33u64 == 0 && k32 >> 33u64 == 0) by {
        let r64 = crc_steps(CRC_POLY, 64);
        let r32 = crc_steps(CRC_POLY, 32);
        assert(((r64 as u64) << 1u64) >> 33u64 == 0 && ((r32 as u64) << 1u64) >> 33u64 == 0) by (bit_vector);
    }
    lemma_clmul_bound(lo, k64, 64, 33);
    assert(y >> 96u128 == 0) by {
        assert(p >> 96u128 == 0);
        assert(p >> 96u128 == 0 ==> (p ^ (v >> 64u128)) >> 96u128 == 0) by (bit_vector);
    }
    assert(ylo >> 32u64 == 0) by (bit_vector) requires ylo == (y & 0xffff_ffffu128) as u64;
    lemma_clmul_bound(ylo, k32, 32, 33);
    // The register after v: the halves' registers.
    lemma_crc16_wide(0, v);
    assert(0u128 ^ v == v) by (bit_vector);
    assert(v == (lo as u128) ^ ((hi as u128) << 64u128)) by (bit_vector)
        requires lo == v as u64, hi == (v >> 64u128) as u64;
    lemma_wsteps_xor(lo as u128, (hi as u128) << 64u128, 128);
    let hw = (hi as u128) << 64u128;
    assert(hw & ((1u128 << 64u128) - 1) as u128 == 0 && hw >> 64u128 == hi as u128) by (bit_vector)
        requires hw == (hi as u128) << 64u128;
    lemma_wsteps_shift(hw, 64);
    lemma_wsteps_add(hw, 64, 64);
    // wsteps(p, 64) is the low half's register.
    lemma_fold_lane(lo, 64, 0, 64);
    assert(low_bits(lo, 64) == lo);
    assert((lo as u128) << 0u128 == lo as u128) by (bit_vector);
    lemma_crc16_wide(0, p);
    lemma_crc16_wide(0, lo as u128);
    assert(0u128 ^ p == p && 0u128 ^ (lo as u128) == lo as u128) by (bit_vector);
    lemma_wsteps_then(p, 64, 64);
    let x = wsteps(p, 64) as u32;
    let cl = crc16(lo as u128);
    assert(crc16(p) == crc_steps(x, 64)) by {
        let a = crc16(p);
        let b = crc_steps(x, 64);
        assert(a as u128 == b as u128 ==> a == b) by (bit_vector);
    }
    lemma_steps_inj(x, cl, 64);
    // So y needs 64 more steps.
    assert(v >> 64u128 == hi as u128) by (bit_vector) requires hi == (v >> 64u128) as u64;
    lemma_wsteps_xor(p, hi as u128, 64);
    assert(wsteps(y, 64) == wsteps(v, 128)) by {
        assert(wsteps(lo as u128, 128) == cl as u128);
        assert(wsteps(p, 64) == cl as u128);
    }
    // y's low 32 bits folded 32 bits onto the rest.
    let yl = ylo as u128;
    let yh = y >> 32u128;
    assert(y == yl ^ (yh << 32u128) && yl >> 32u128 == 0 && yl < 0x1_0000_0000 && (yh << 32u128) & ((1u128 << 32u128) - 1) as u128 == 0
        && (yh << 32u128) >> 32u128 == yh) by (bit_vector)
        requires ylo == (y & 0xffff_ffffu128) as u64, yl == ylo as u128, yh == y >> 32u128, y >> 96u128 == 0;
    lemma_wsteps_xor(yl, yh << 32u128, 64);
    lemma_wsteps_shift(yh << 32u128, 32);
    lemma_wsteps_add(yh << 32u128, 32, 32);
    lemma_wsteps_narrow(yl, 64);
    // wsteps(q, 32) is y's low 32 bits stepped 64.
    lemma_fold_lane(ylo, 32, 0, 64);
    assert(low_bits(ylo, 64) == ylo);
    assert((ylo as u128) << 0u128 == ylo as u128) by (bit_vector);
    lemma_crc16_wide(0, q);
    lemma_crc16_wide(0, yl);
    assert(0u128 ^ q == q && 0u128 ^ yl == yl) by (bit_vector);
    lemma_wsteps_then(q, 32, 96);
    lemma_wsteps_narrow(yl, 128);
    let xq = wsteps(q, 32) as u32;
    let c0 = ylo as u32;
    assert((c0 as u128) == yl) by (bit_vector) requires c0 == ylo as u32, yl == ylo as u128, ylo >> 32u64 == 0;
    assert(crc16(q) == crc_steps(xq, 96)) by {
        let a = crc16(q);
        let b = crc_steps(xq, 96);
        assert(a as u128 == b as u128 ==> a == b) by (bit_vector);
    }
    assert(crc16(yl) == crc_steps(c0, 128)) by {
        let a = crc16(yl);
        let b = crc_steps(c0, 128);
        assert(a as u128 == b as u128 ==> a == b) by (bit_vector);
    }
    lemma_steps_add(c0, 128, 32);
    lemma_steps_add(c0, 64, 96);
    assert(128 + 32 == 64 + 96);
    lemma_steps_inj(xq, crc_steps(c0, 64), 96);
    lemma_wsteps_xor(q, yh, 32);
    // z: 32 more steps.
    let zl = (#[verifier::truncate] (z as u32)) as u128;
    let zh = #[verifier::truncate] (((#[verifier::truncate] (z as u64)) >> 32u64) as u32);
    assert(z >> 64u128 == 0) by {
        assert((32 + 33 - 1) as u128 == 64u128);
        assert(q >> 64u128 == 0);
        assert(yh >> 64u128 == 0) by (bit_vector) requires yh == y >> 32u128, y >> 96u128 == 0;
        assert(q >> 64u128 == 0 && yh >> 64u128 == 0 ==> (q ^ yh) >> 64u128 == 0) by (bit_vector);
    }
    assert(z == zl ^ (((zh as u128)) << 32u128) && ((zh as u128) << 32u128) & ((1u128 << 32u128) - 1) as u128 == 0
        && ((zh as u128) << 32u128) >> 32u128 == zh as u128) by (bit_vector)
        requires zl == (z as u32) as u128, zh == ((z as u64) >> 32u64) as u32, z >> 64u128 == 0;
    lemma_wsteps_xor(zl, (zh as u128) << 32u128, 32);
    lemma_wsteps_shift((zh as u128) << 32u128, 32);
    assert(zl < 0x1_0000_0000) by (bit_vector) requires zl == (z as u32) as u128;
    lemma_wsteps_narrow(zl, 32);
    assert(zl as u32 == z as u32) by (bit_vector) requires zl == (z as u32) as u128;
    // Tie the 128-bit values back to the 32-bit register.
    let w = wsteps(v, 128);
    assert(crc16(v) as u128 == w);
    let s = crc_steps(z as u32, 32);
    assert(w == (s as u128) ^ (zh as u128));
    assert((s as u128) ^ (zh as u128) == ((s ^ zh) as u128)) by (bit_vector);
    let cv = crc16(v);
    let t = s ^ zh;
    assert(cv as u128 == t as u128 ==> cv == t) by (bit_vector);
}

/// A product of `a < 2^m` and `b < 2^k` is below `2^(m + k - 1)`.
proof fn lemma_clmul_bound(a: u64, b: u64, m: nat, k: nat)
    requires
        m <= 64,
        k <= 64,
        m >= 1,
        k >= 1,
        m == 64 || a >> m as u64 == 0,
        b >> k as u64 == 0,
    ensures
        clmul(a, b) >> (m + k - 1) as u128 == 0,
{
    lemma_clmul_n_bound(a, b, 64, m, k);
}

proof fn lemma_clmul_n_bound(a: u64, b: u64, n: nat, m: nat, k: nat)
    requires
        n <= 64,
        m <= 64,
        k <= 64,
        m >= 1,
        k >= 1,
        m == 64 || a >> m as u64 == 0,
        b >> k as u64 == 0,
    ensures
        clmul_n(a, b, n) >> (m + k - 1) as u128 == 0,
    decreases n,
{
    let s = (m + k - 1) as u128;
    if n == 0 {
        assert(0u128 >> s == 0) by (bit_vector);
    } else {
        lemma_clmul_n_bound(a, b, (n - 1) as nat, m, k);
        let i = (n - 1) as u64;
        let p = clmul_n(a, b, (n - 1) as nat);
        let t = (b as u128) << (n - 1) as u128;
        let bit = (a >> i) & 1 == 1;
        let mu = m as u64;
        let ku = k as u128;
        assert(bit ==> (i as u128) < m as u128) by {
            if m < 64 {
                assert(((a >> i) & 1 == 1 && a >> mu == 0 && i < 64 && mu < 64) ==> i < mu) by (bit_vector);
            }
        }
        assert((p >> s == 0 && (bit ==> (b as u128) >> ku == 0 && (i as u128) + ku <= s)) ==> (p ^ (if bit { t } else { 0 })) >> s == 0) by (bit_vector)
            requires t == (b as u128) << (i as u128), i < 64, s <= 127;
        assert((b as u128) >> ku == 0) by (bit_vector) requires b >> (ku as u64) == 0, ku <= 64;
        assert((n - 1) as u128 == i as u128);
    }
}

// ---------------------------------------------------------------------------
// Constants and a reference
// ---------------------------------------------------------------------------

/// `fold_pair(n)`, computed by the verified `lanes::steps_exec`.
pub const fn fold_pair_exec(n: u32) -> (r: u128)
    requires
        64 <= n,
    ensures
        r == fold_pair(n as nat),
{
    assert(CRC_POLY == 0xedb8_8320u32);
    let lo = (super::lanes::steps_exec(0xedb8_8320, n) as u64) << 1u64;
    let hi = (super::lanes::steps_exec(0xedb8_8320, n - 64) as u64) << 1u64;
    assert(((n - 64) as u32) as nat == (n as nat - 64) as nat);
    ((hi as u128) << 64u128) | (lo as u128)
}

/// Fold over 256 bytes (the main loop of the 512-bit kernel).
/// The final reduction's constants: `fold_k(64)` and `fold_k(32)`, in the
/// low quadwords.
pub exec const R64: u128
    ensures
        R64 == fold_k(64) as u128,
{
    let p = fold_pair_exec(128);
    let ghost a = fold_k(64);
    let ghost b = fold_k(128);
    assert(p == ((a as u128) << 64u128) | (b as u128));
    assert((((a as u128) << 64u128) | (b as u128)) >> 64u128 == a as u128) by (bit_vector);
    p >> 64u128
}

pub exec const R32: u128
    ensures
        R32 == fold_k(32) as u128,
{
    assert(CRC_POLY == 0xedb8_8320u32);
    let x = super::lanes::steps_exec(0xedb8_8320, 32);
    assert(((x as u64) as u128) << 1u128 == (((x as u64) << 1u64) as u128)) by (bit_vector);
    ((x as u64) as u128) << 1u128
}

pub exec const K2048: u128
    ensures
        K2048 == fold_pair(2048),
{
    fold_pair_exec(2048)
}

pub exec const K1536: u128
    ensures
        K1536 == fold_pair(1536),
{
    fold_pair_exec(1536)
}

pub exec const K1024: u128
    ensures
        K1024 == fold_pair(1024),
{
    fold_pair_exec(1024)
}

pub exec const K768: u128
    ensures
        K768 == fold_pair(768),
{
    fold_pair_exec(768)
}

pub exec const K512: u128
    ensures
        K512 == fold_pair(512),
{
    fold_pair_exec(512)
}

pub exec const K384: u128
    ensures
        K384 == fold_pair(384),
{
    fold_pair_exec(384)
}

pub exec const K256: u128
    ensures
        K256 == fold_pair(256),
{
    fold_pair_exec(256)
}

pub exec const K128: u128
    ensures
        K128 == fold_pair(128),
{
    fold_pair_exec(128)
}

/// The carry-less product, bit by bit: what `tests/vclmul.rs` checks the
/// instructions against.
pub fn clmul_ref(a: u64, b: u64) -> (r: u128)
    ensures
        r == clmul(a, b),
{
    let mut r: u128 = 0;
    let mut i: u64 = 0;
    while i < 64
        invariant
            i <= 64,
            r == clmul_n(a, b, i as nat),
        decreases 64 - i,
    {
        let ghost r0 = r;
        if (a >> i) & 1 == 1 {
            r = r ^ ((b as u128) << (i as u128));
        } else {
            assert(r ^ 0u128 == r) by (bit_vector);
        }
        assert(clmul_n(a, b, (i + 1) as nat) == clmul_n(a, b, i as nat) ^ (if (a >> i) & 1 == 1 {
            (b as u128) << (i as u128)
        } else {
            0
        }));
        i = i + 1;
    }
    r
}

/// The sixteen bytes of `v`.
pub fn bytes16_exec(v: u128) -> (r: [u8; 16])
    ensures
        r@ == bytes16(v),
{
    let r = [
        v as u8, (v >> 8u128) as u8, (v >> 16u128) as u8, (v >> 24u128) as u8,
        (v >> 32u128) as u8, (v >> 40u128) as u8, (v >> 48u128) as u8, (v >> 56u128) as u8,
        (v >> 64u128) as u8, (v >> 72u128) as u8, (v >> 80u128) as u8, (v >> 88u128) as u8,
        (v >> 96u128) as u8, (v >> 104u128) as u8, (v >> 112u128) as u8, (v >> 120u128) as u8,
    ];
    assert(v >> 0u128 == v) by (bit_vector);
    assert(r@ =~= bytes16(v));
    r
}

// ---------------------------------------------------------------------------
// Lemmas the kernels use
// ---------------------------------------------------------------------------

pub proof fn lemma_flat_append(xs: Seq<u128>, ys: Seq<u128>)
    ensures
        flat(xs + ys) == flat(xs) + flat(ys),
    decreases ys.len(),
{
    if ys.len() == 0 {
        assert(xs + ys =~= xs);
        assert(flat(xs) + flat(ys) =~= flat(xs));
    } else {
        lemma_flat_append(xs, ys.drop_last());
        assert((xs + ys).drop_last() =~= xs + ys.drop_last());
        assert((xs + ys).last() == ys.last());
        assert(flat(xs) + flat(ys.drop_last()) + bytes16(ys.last()) =~= flat(xs) + (flat(ys.drop_last())
            + bytes16(ys.last())));
    }
}

pub proof fn lemma_flat_one(v: u128)
    ensures
        flat(seq![v]) == bytes16(v),
{
    assert(seq![v].drop_last() =~= Seq::<u128>::empty());
    assert(seq![v].last() == v);
    assert(flat(Seq::<u128>::empty()) == Seq::<u8>::empty());
    assert(Seq::<u8>::empty() + bytes16(v) =~= bytes16(v));
}

/// After the blocks `xs` (whose effect is `c`), the blocks `ys`: the same
/// effect as `ys` with `xs` folded onto them.
pub proof fn lemma_run(c: u32, xs: Seq<u128>, ys: Seq<u128>)
    requires
        xs.len() == ys.len(),
        xs.len() >= 1,
        c == eff(xs),
    ensures
        crc_from(c, flat(ys)) == eff(xors(folds(xs, 128 * xs.len()), ys)),
{
    lemma_eff(c, ys);
    lemma_eff_append(xs, ys);
    lemma_eff_step(xs, ys);
}

/// The prefix `d[..i + m]` from the prefix `d[..i]` and the next `m` bytes.
pub proof fn lemma_prefix(reg: u32, d: Seq<u8>, i: int, m: int)
    requires
        0 <= i,
        0 <= m,
        i + m <= d.len(),
    ensures
        crc_from(reg, d.subrange(0, i + m)) == crc_from(crc_from(reg, d.subrange(0, i)), d.subrange(i, i
            + m)),
{
    lemma_crc_append(reg, d.subrange(0, i), d.subrange(i, i + m));
    assert(d.subrange(0, i) + d.subrange(i, i + m) =~= d.subrange(0, i + m));
}

} // verus!

#[cfg(target_arch = "x86_64")]
verus! {

use super::vclmul::*;

broadcast use group_vclmul;

/// Folds `xs` (four blocks) `n` bits onto `ys`.
#[inline(always)]
fn zstep(x: &Z512, k: &Z512, y: &Z512, Ghost(n): Ghost<nat>) -> (r: Z512)
    requires
        vpclmul(),
        zl(*k) == seq![fold_pair(n), fold_pair(n), fold_pair(n), fold_pair(n)],
    ensures
        zl(r) == xors(folds(zl(*x), n), zl(*y)),
{
    let f = z_fold(x, k);
    let r = z_xor(&f, y);
    assert(zl(r) =~= xors(folds(zl(*x), n), zl(*y)));
    r
}

/// Folds one block `n` bits onto `y`.
#[inline(always)]
fn xstep(x: &X128, k: &X128, y: &X128, Ghost(n): Ghost<nat>) -> (r: X128)
    requires
        pclmul(),
        xv(*k) == fold_pair(n),
    ensures
        xv(r) == fold(xv(*x), n) ^ xv(*y),
{
    let f = x_fold(x, k);
    x_xor(&f, y)
}

/// The register after the one block `x`, and then the rest of `d` from
/// `i`: two carry-less products (`lemma_reduce`), four table lookups, and
/// the table code over the tail.
#[inline(always)]
fn finish(reg: u32, d: &[u8], i: usize, x: &X128) -> (r: u32)
    requires
        pclmul(),
        i <= d@.len(),
        crc_from(reg, d@.subrange(0, i as int)) == crc16(xv(*x)),
    ensures
        r == crc_from(reg, d@),
{
    let r64 = x_set(R64);
    let r32 = x_set(R32);
    let m32 = x_set(0xffff_ffff);
    let p = x_clmul_lo(x, &r64);
    let h = x_shr64(x);
    let y = x_xor(&p, &h);
    let yl = x_and(&y, &m32);
    let q = x_clmul_lo(&yl, &r32);
    let yh = x_shr32(&y);
    let z = x_xor(&q, &yh);
    let w = x_low64(&z);
    proof {
        lemma_reduce(xv(*x));
        let v = xv(*x);
        assert(lo64(xv(r64)) == fold_k(64)) by {
            let k = fold_k(64);
            assert(((k as u128) as u64) == k) by (bit_vector);
        }
        assert(lo64(xv(r32)) == fold_k(32)) by {
            let k = fold_k(32);
            assert(((k as u128) as u64) == k) by (bit_vector);
        }
        let yv = xv(y);
        let ylv = xv(yl);
        assert((ylv as u64) == (yv & 0xffff_ffffu128) as u64) by (bit_vector)
            requires ylv == yv & 0xffff_ffffu128;
        let zv = xv(z);
        assert((w as u32) == (zv as u32) && ((w >> 32u64) as u32) == (((zv as u64) >> 32u64) as u32)) by (bit_vector)
            requires w == zv as u64;
    }
    let c = super::crc_shift32(w as u32) ^ ((w >> 32) as u32);
    let n = d.len();
    if i == n {
        assert(d@.subrange(0, i as int) =~= d@);
        return c;
    }
    let tail = vstd::slice::slice_subrange(d, i, n);
    proof {
        lemma_crc_append(reg, d@.subrange(0, i as int), tail@);
        assert(d@.subrange(0, i as int) + tail@ =~= d@);
    }
    super::crc32_update(c, tail)
}

/// **CRC-32 with PCLMULQDQ**: four blocks folded 64 bytes at a time,
/// then one block 16 bytes at a time.
#[inline(always)]
pub fn crc32_pclmul(reg: u32, d: &[u8]) -> (r: u32)
    requires
        pclmul(),
        d@.len() >= 64,
    ensures
        r == crc_from(reg, d@),
{
    let n = d.len();
    let x0 = x_load(d, 0);
    let rv = x_set(reg as u128);
    let mut a = x_xor(&x0, &rv);
    let mut b = x_load(d, 16);
    let mut c = x_load(d, 32);
    let mut e = x_load(d, 48);
    proof {
        let xs = seq![xv(x0), xv(b), xv(c), xv(e)];
        lemma_flat_one(xv(x0));
        lemma_flat_append(seq![xv(x0)], seq![xv(b)]);
        lemma_flat_one(xv(b));
        assert(seq![xv(x0)] + seq![xv(b)] =~= seq![xv(x0), xv(b)]);
        lemma_flat_append(seq![xv(x0), xv(b)], seq![xv(c)]);
        lemma_flat_one(xv(c));
        assert(seq![xv(x0), xv(b)] + seq![xv(c)] =~= seq![xv(x0), xv(b), xv(c)]);
        lemma_flat_append(seq![xv(x0), xv(b), xv(c)], seq![xv(e)]);
        lemma_flat_one(xv(e));
        assert(seq![xv(x0), xv(b), xv(c)] + seq![xv(e)] =~= xs);
        assert(flat(xs) =~= d@.subrange(0, 64));
        lemma_eff_reg(reg, xs);
        assert(xs.update(0, xs[0] ^ (reg as u128)) =~= seq![xv(a), xv(b), xv(c), xv(e)]);
    }
    let k512 = x_set(K512);
    let mut i: usize = 64;
    while n - i >= 64
        invariant
            pclmul(),
            n == d@.len(),
            64 <= i <= n,
            xv(k512) == fold_pair(512),
            crc_from(reg, d@.subrange(0, i as int)) == eff(seq![xv(a), xv(b), xv(c), xv(e)]),
        decreases n - i,
    {
        let ya = x_load(d, i);
        let yb = x_load(d, i + 16);
        let yc = x_load(d, i + 32);
        let ye = x_load(d, i + 48);
        let ghost xs = seq![xv(a), xv(b), xv(c), xv(e)];
        let ghost ys = seq![xv(ya), xv(yb), xv(yc), xv(ye)];
        proof {
            lemma_prefix(reg, d@, i as int, 64);
            lemma_flat_one(ys[0]);
            lemma_flat_append(seq![ys[0]], seq![ys[1]]);
            lemma_flat_one(ys[1]);
            assert(seq![ys[0]] + seq![ys[1]] =~= seq![ys[0], ys[1]]);
            lemma_flat_append(seq![ys[0], ys[1]], seq![ys[2]]);
            lemma_flat_one(ys[2]);
            assert(seq![ys[0], ys[1]] + seq![ys[2]] =~= seq![ys[0], ys[1], ys[2]]);
            lemma_flat_append(seq![ys[0], ys[1], ys[2]], seq![ys[3]]);
            lemma_flat_one(ys[3]);
            assert(seq![ys[0], ys[1], ys[2]] + seq![ys[3]] =~= ys);
            assert(flat(ys) =~= d@.subrange(i as int, i + 64));
            lemma_run(eff(xs), xs, ys);
        }
        a = xstep(&a, &k512, &ya, Ghost(512));
        b = xstep(&b, &k512, &yb, Ghost(512));
        c = xstep(&c, &k512, &yc, Ghost(512));
        e = xstep(&e, &k512, &ye, Ghost(512));
        proof {
            assert(xors(folds(xs, 128 * xs.len()), ys) =~= seq![xv(a), xv(b), xv(c), xv(e)]);
        }
        i = i + 64;
    }
    // Four blocks to one.
    let k384 = x_set(K384);
    let k256 = x_set(K256);
    let k128 = x_set(K128);
    let fa = x_fold(&a, &k384);
    let fb = x_fold(&b, &k256);
    let fc = x_fold(&c, &k128);
    let t1 = x_xor(&fa, &fb);
    let t2 = x_xor(&t1, &fc);
    let mut x = x_xor(&t2, &e);
    proof {
        lemma_eff4(seq![xv(a), xv(b), xv(c), xv(e)]);
    }
    while n - i >= 16
        invariant
            pclmul(),
            n == d@.len(),
            i <= n,
            xv(k128) == fold_pair(128),
            crc_from(reg, d@.subrange(0, i as int)) == crc16(xv(x)),
        decreases n - i,
    {
        let y = x_load(d, i);
        proof {
            lemma_prefix(reg, d@, i as int, 16);
            lemma_block_step(xv(x), xv(y));
        }
        x = xstep(&x, &k128, &y, Ghost(128));
        i = i + 16;
    }
    finish(reg, d, i, &x)
}

/// Folds `xs` (two blocks) `n` bits onto `ys`.
#[inline(always)]
fn ystep(x: &Y256, k: &Y256, y: &Y256, Ghost(n): Ghost<nat>) -> (r: Y256)
    requires
        vpclmul256(),
        yl(*k) == seq![fold_pair(n), fold_pair(n)],
    ensures
        yl(r) == xors(folds(yl(*x), n), yl(*y)),
{
    let f = y_fold(x, k);
    let r = y_xor(&f, y);
    assert(yl(r) =~= xors(folds(yl(*x), n), yl(*y)));
    r
}

/// Two blocks to one.
pub proof fn lemma_eff2(xs: Seq<u128>)
    requires
        xs.len() == 2,
    ensures
        eff(xs) == crc16(fold(xs[0], 128) ^ xs[1]),
{
    let s0 = seq![xs[0]];
    assert(xs.drop_last() =~= s0);
    assert(s0.drop_last() =~= Seq::<u128>::empty());
    assert(eff(Seq::<u128>::empty()) == 0);
    let a = crc16(xs[0]);
    lemma_steps_zero(128);
    assert(0u32 ^ a == a) by (bit_vector);
    assert(eff(s0) == crc_steps(eff(s0.drop_last()), 128) ^ crc16(s0.last()));
    lemma_fold(xs[0], 128);
    lemma_crc16_xor(fold(xs[0], 128), xs[1]);
}

/// **CRC-32 with VPCLMULQDQ on 256-bit vectors**: eight blocks (four
/// vectors) folded 128 bytes at a time, then two 32 bytes at a time, then
/// one 16 bytes at a time.
#[inline(always)]
pub fn crc32_vpclmul256(reg: u32, d: &[u8]) -> (r: u32)
    requires
        vpclmul256(),
        d@.len() >= 128,
    ensures
        r == crc_from(reg, d@),
{
    let n = d.len();
    let l0 = y_load(d, 0);
    let rv = y_reg(reg);
    let mut z0 = y_xor(&l0, &rv);
    let mut z1 = y_load(d, 32);
    let mut z2 = y_load(d, 64);
    let mut z3 = y_load(d, 96);
    proof {
        let xs = yl(l0) + yl(z1) + yl(z2) + yl(z3);
        lemma_flat_append(yl(l0), yl(z1));
        lemma_flat_append(yl(l0) + yl(z1), yl(z2));
        lemma_flat_append(yl(l0) + yl(z1) + yl(z2), yl(z3));
        assert(flat(xs) =~= d@.subrange(0, 128));
        lemma_eff_reg(reg, xs);
        assert(yl(z0) =~= yl(l0).update(0, yl(l0)[0] ^ (reg as u128))) by {
            let w = yl(l0)[1];
            assert(yl(rv)[1] == 0u128);
            assert(w ^ 0u128 == w) by (bit_vector);
        }
        assert(xs.update(0, xs[0] ^ (reg as u128)) =~= yl(z0) + yl(z1) + yl(z2) + yl(z3));
    }
    let k1024 = y_splat(K1024);
    let mut i: usize = 128;
    while n - i >= 128
        invariant
            vpclmul256(),
            n == d@.len(),
            128 <= i <= n,
            yl(k1024) == seq![fold_pair(1024), fold_pair(1024)],
            crc_from(reg, d@.subrange(0, i as int)) == eff(yl(z0) + yl(z1) + yl(z2) + yl(z3)),
        decreases n - i,
    {
        let y0 = y_load(d, i);
        let y1 = y_load(d, i + 32);
        let y2 = y_load(d, i + 64);
        let y3 = y_load(d, i + 96);
        let ghost xs = yl(z0) + yl(z1) + yl(z2) + yl(z3);
        let ghost ys = yl(y0) + yl(y1) + yl(y2) + yl(y3);
        proof {
            lemma_prefix(reg, d@, i as int, 128);
            lemma_flat_append(yl(y0), yl(y1));
            lemma_flat_append(yl(y0) + yl(y1), yl(y2));
            lemma_flat_append(yl(y0) + yl(y1) + yl(y2), yl(y3));
            assert(flat(ys) =~= d@.subrange(i as int, i + 128));
            lemma_run(eff(xs), xs, ys);
        }
        z0 = ystep(&z0, &k1024, &y0, Ghost(1024));
        z1 = ystep(&z1, &k1024, &y1, Ghost(1024));
        z2 = ystep(&z2, &k1024, &y2, Ghost(1024));
        z3 = ystep(&z3, &k1024, &y3, Ghost(1024));
        proof {
            assert(xors(folds(xs, 128 * xs.len()), ys) =~= yl(z0) + yl(z1) + yl(z2) + yl(z3));
        }
        i = i + 128;
    }
    // Four vectors to one: each folded to the last.
    let k768 = y_splat(K768);
    let k512 = y_splat(K512);
    let k256 = y_splat(K256);
    let f0 = y_fold(&z0, &k768);
    let f1 = y_fold(&z1, &k512);
    let t1 = y_xor(&f0, &f1);
    let t2 = ystep(&z2, &k256, &t1, Ghost(256));
    let mut z = y_xor(&t2, &z3);
    proof {
        let (a, b, c, e) = (yl(z0), yl(z1), yl(z2), yl(z3));
        lemma_eff_append(a + b + c, e);
        lemma_eff_append(a + b, c);
        lemma_eff_append(a, b);
        lemma_eff_folds(a, 768);
        lemma_eff_folds(b, 512);
        lemma_eff_folds(c, 256);
        lemma_steps_add(eff(a), 256, 256);
        lemma_steps_add(eff(a), 512, 256);
        lemma_steps_add(eff(b), 256, 256);
        let (ea, eb, ec, ee) = (eff(a), eff(b), eff(c), eff(e));
        lemma_steps_xor(crc_steps(ea, 256), eb, 256);
        lemma_steps_xor(crc_steps(crc_steps(ea, 256) ^ eb, 256), ec, 256);
        lemma_steps_xor(crc_steps(ea, 512), crc_steps(eb, 256), 256);
        let fa = folds(a, 768);
        let fb = folds(b, 512);
        let fc = folds(c, 256);
        lemma_eff_xor(fa, fb);
        assert(yl(t1) =~= xors(fa, fb));
        assert(yl(t2) =~= xors(fc, xors(fa, fb)));
        lemma_eff_xor(fc, xors(fa, fb));
        assert(yl(z) =~= xors(xors(fc, xors(fa, fb)), e));
        lemma_eff_xor(xors(fc, xors(fa, fb)), e);
        let (p, q, s) = (crc_steps(ea, 768), crc_steps(eb, 512), crc_steps(ec, 256));
        assert(((p ^ q) ^ s) ^ ee == (s ^ (p ^ q)) ^ ee) by (bit_vector);
    }
    while n - i >= 32
        invariant
            vpclmul256(),
            n == d@.len(),
            i <= n,
            yl(k256) == seq![fold_pair(256), fold_pair(256)],
            crc_from(reg, d@.subrange(0, i as int)) == eff(yl(z)),
        decreases n - i,
    {
        let y = y_load(d, i);
        proof {
            lemma_prefix(reg, d@, i as int, 32);
            lemma_run(eff(yl(z)), yl(z), yl(y));
        }
        z = ystep(&z, &k256, &y, Ghost(256));
        i = i + 32;
    }
    // Two blocks to one.
    let b0 = y_block::<0>(&z);
    let b1 = y_block::<1>(&z);
    let k128 = x_set(K128);
    let mut x = xstep(&b0, &k128, &b1, Ghost(128));
    proof {
        assert(yl(z) =~= seq![xv(b0), xv(b1)]);
        lemma_eff2(yl(z));
    }
    while n - i >= 16
        invariant
            pclmul(),
            n == d@.len(),
            i <= n,
            xv(k128) == fold_pair(128),
            crc_from(reg, d@.subrange(0, i as int)) == crc16(xv(x)),
        decreases n - i,
    {
        let y = x_load(d, i);
        proof {
            lemma_prefix(reg, d@, i as int, 16);
            lemma_block_step(xv(x), xv(y));
        }
        x = xstep(&x, &k128, &y, Ghost(128));
        i = i + 16;
    }
    finish(reg, d, i, &x)
}

/// **CRC-32 with VPCLMULQDQ**: sixteen blocks (four 512-bit vectors)
/// folded 256 bytes at a time, then four 64 bytes at a time, then one 16
/// bytes at a time.
#[inline(always)]
pub fn crc32_vpclmul(reg: u32, d: &[u8]) -> (r: u32)
    requires
        vpclmul(),
        d@.len() >= 256,
    ensures
        r == crc_from(reg, d@),
{
    let n = d.len();
    let l0 = z_load(d, 0);
    let rv = z_reg(reg);
    let mut z0 = z_xor(&l0, &rv);
    let mut z1 = z_load(d, 64);
    let mut z2 = z_load(d, 128);
    let mut z3 = z_load(d, 192);
    proof {
        let xs = zl(l0) + zl(z1) + zl(z2) + zl(z3);
        lemma_flat_append(zl(l0), zl(z1));
        lemma_flat_append(zl(l0) + zl(z1), zl(z2));
        lemma_flat_append(zl(l0) + zl(z1) + zl(z2), zl(z3));
        assert(flat(xs) =~= d@.subrange(0, 256));
        lemma_eff_reg(reg, xs);
        assert(zl(z0) =~= zl(l0).update(0, zl(l0)[0] ^ (reg as u128))) by {
            assert forall|j: int| 1 <= j < 4 implies #[trigger] zl(l0)[j] ^ zl(rv)[j] == zl(l0)[j] by {
                let w = zl(l0)[j];
                assert(zl(rv)[j] == 0u128);
                assert(w ^ 0u128 == w) by (bit_vector);
            }
        }
        assert(xs.update(0, xs[0] ^ (reg as u128)) =~= zl(z0) + zl(z1) + zl(z2) + zl(z3));
    }
    let k2048 = z_splat(K2048);
    let mut i: usize = 256;
    while n - i >= 256
        invariant
            vpclmul(),
            n == d@.len(),
            256 <= i <= n,
            zl(k2048) == seq![fold_pair(2048), fold_pair(2048), fold_pair(2048), fold_pair(2048)],
            crc_from(reg, d@.subrange(0, i as int)) == eff(zl(z0) + zl(z1) + zl(z2) + zl(z3)),
        decreases n - i,
    {
        let y0 = z_load(d, i);
        let y1 = z_load(d, i + 64);
        let y2 = z_load(d, i + 128);
        let y3 = z_load(d, i + 192);
        let ghost xs = zl(z0) + zl(z1) + zl(z2) + zl(z3);
        let ghost ys = zl(y0) + zl(y1) + zl(y2) + zl(y3);
        proof {
            lemma_prefix(reg, d@, i as int, 256);
            lemma_flat_append(zl(y0), zl(y1));
            lemma_flat_append(zl(y0) + zl(y1), zl(y2));
            lemma_flat_append(zl(y0) + zl(y1) + zl(y2), zl(y3));
            assert(flat(ys) =~= d@.subrange(i as int, i + 256));
            lemma_run(eff(xs), xs, ys);
        }
        z0 = zstep(&z0, &k2048, &y0, Ghost(2048));
        z1 = zstep(&z1, &k2048, &y1, Ghost(2048));
        z2 = zstep(&z2, &k2048, &y2, Ghost(2048));
        z3 = zstep(&z3, &k2048, &y3, Ghost(2048));
        proof {
            assert(xors(folds(xs, 128 * xs.len()), ys) =~= zl(z0) + zl(z1) + zl(z2) + zl(z3));
        }
        i = i + 256;
    }
    // Four vectors to one: each folded to the last.
    let k1536 = z_splat(K1536);
    let k1024 = z_splat(K1024);
    let k512 = z_splat(K512);
    let f0 = z_fold(&z0, &k1536);
    let f1 = z_fold(&z1, &k1024);
    let t1 = z_xor(&f0, &f1);
    let t2 = zstep(&z2, &k512, &t1, Ghost(512));
    let mut z = z_xor(&t2, &z3);
    proof {
        let (a, b, c, e) = (zl(z0), zl(z1), zl(z2), zl(z3));
        lemma_eff_append(a + b + c, e);
        lemma_eff_append(a + b, c);
        lemma_eff_append(a, b);
        lemma_eff_folds(a, 1536);
        lemma_eff_folds(b, 1024);
        lemma_eff_folds(c, 512);
        lemma_steps_add(eff(a), 512, 512);
        lemma_steps_add(eff(a), 1024, 512);
        lemma_steps_add(eff(b), 512, 512);
        let (ea, eb, ec, ee) = (eff(a), eff(b), eff(c), eff(e));
        lemma_steps_xor(crc_steps(ea, 512), eb, 512);
        lemma_steps_xor(crc_steps(crc_steps(ea, 512) ^ eb, 512), ec, 512);
        lemma_steps_xor(crc_steps(ea, 1024), crc_steps(eb, 512), 512);
        let fa = folds(a, 1536);
        let fb = folds(b, 1024);
        let fc = folds(c, 512);
        lemma_eff_xor(fa, fb);
        lemma_eff_xor(xors(fa, fb), fc);
        lemma_eff_xor(xors(xors(fa, fb), fc), e);
        assert(zl(t1) =~= xors(fa, fb));
        assert(zl(t2) =~= xors(fc, xors(fa, fb)));
        lemma_eff_xor(fc, xors(fa, fb));
        assert(zl(z) =~= xors(xors(fc, xors(fa, fb)), e));
        lemma_eff_xor(xors(fc, xors(fa, fb)), e);
        let (p, q, s) = (crc_steps(ea, 1536), crc_steps(eb, 1024), crc_steps(ec, 512));
        assert(((p ^ q) ^ s) ^ ee == (s ^ (p ^ q)) ^ ee) by (bit_vector);
    }
    while n - i >= 64
        invariant
            vpclmul(),
            n == d@.len(),
            i <= n,
            zl(k512) == seq![fold_pair(512), fold_pair(512), fold_pair(512), fold_pair(512)],
            crc_from(reg, d@.subrange(0, i as int)) == eff(zl(z)),
        decreases n - i,
    {
        let y = z_load(d, i);
        proof {
            lemma_prefix(reg, d@, i as int, 64);
            lemma_run(eff(zl(z)), zl(z), zl(y));
        }
        z = zstep(&z, &k512, &y, Ghost(512));
        i = i + 64;
    }
    // Four blocks to one.
    let b0 = z_block::<0>(&z);
    let b1 = z_block::<1>(&z);
    let b2 = z_block::<2>(&z);
    let b3 = z_block::<3>(&z);
    let k384 = x_set(K384);
    let k256 = x_set(K256);
    let k128 = x_set(K128);
    let fa = x_fold(&b0, &k384);
    let fb = x_fold(&b1, &k256);
    let fc = x_fold(&b2, &k128);
    let u1 = x_xor(&fa, &fb);
    let u2 = x_xor(&u1, &fc);
    let mut x = x_xor(&u2, &b3);
    proof {
        assert(zl(z) =~= seq![xv(b0), xv(b1), xv(b2), xv(b3)]);
        lemma_eff4(zl(z));
    }
    while n - i >= 16
        invariant
            pclmul(),
            n == d@.len(),
            i <= n,
            xv(k128) == fold_pair(128),
            crc_from(reg, d@.subrange(0, i as int)) == crc16(xv(x)),
        decreases n - i,
    {
        let y = x_load(d, i);
        proof {
            lemma_prefix(reg, d@, i as int, 16);
            lemma_block_step(xv(x), xv(y));
        }
        x = xstep(&x, &k128, &y, Ghost(128));
        i = i + 16;
    }
    finish(reg, d, i, &x)
}

} // verus!

verus! {

/// One block folded onto the next.
pub proof fn lemma_block_step(x: u128, y: u128)
    ensures
        crc_from(crc16(x), bytes16(y)) == crc16(fold(x, 128) ^ y),
{
    let xs = seq![x];
    let ys = seq![y];
    lemma_crc16_zero();
    lemma_steps_zero(128);
    assert(xs.drop_last() =~= Seq::<u128>::empty());
    assert(ys.drop_last() =~= Seq::<u128>::empty());
    let t = crc16(x);
    assert(0u32 ^ t == t) by (bit_vector);
    assert(eff(Seq::<u128>::empty()) == 0);
    assert(xs.last() == x);
    assert(eff(xs) == crc_steps(eff(xs.drop_last()), 128) ^ crc16(xs.last()));
    assert(eff(xs) == t);
    lemma_flat_one(y);
    lemma_run(t, xs, ys);
    let zs = xors(folds(xs, 128), ys);
    assert(zs.drop_last() =~= Seq::<u128>::empty());
    assert(zs.last() == fold(x, 128) ^ y);
    let u = crc16(zs.last());
    assert(0u32 ^ u == u) by (bit_vector);
}

} // verus!
