//! Eight bytes at a time in a u64 ("SIMD within a register"): finds the
//! first byte of a host that is not a lowercase letter, digit, '-' or '.',
//! with each lane's formula proven exact by the bit-vector solver.
use crate::spec::*;
use crate::tables::*;
use vstd::compute::RangeAll;
use vstd::prelude::*;

verus! {

/// The bytes most hosts are made of. None of them ends a host or sends a
/// domain to the slow path.
pub open spec fn dplain(c: u8) -> bool {
    (0x61 <= c && c <= 0x7A) || (0x30 <= c && c <= 0x39) || c == 0x2D || c == 0x2E
}

pub open spec fn dplain64(c: u64) -> bool {
    (0x61 <= c && c <= 0x7A) || (0x30 <= c && c <= 0x39) || c == 0x2D || c == 0x2E
}

/// The classes a plain byte never has.
pub const PLAIN_FREE: u16 = AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW;

pub proof fn lemma_dplain_cls()
    ensures
        forall|c: u8| #[trigger] dplain(c) ==> CLS@[c as int] & PLAIN_FREE == 0,
{
    let p = |i: int| dplain(i as u8) ==> CLS@[i] & PLAIN_FREE == 0;
    assert((0..256int).all_spec(|i: int| dplain(i as u8) ==> CLS@[i] & PLAIN_FREE == 0)) by (compute_only);
    vstd::compute::all_spec_ensures(0..256int, p);
    assert forall|c: u8| #[trigger] dplain(c) implies CLS@[c as int] & PLAIN_FREE == 0 by {
        assert((c as int) as u8 == c);
        assert(p(c as int));
    }
}

/// The masks the host scans use have only classes plain bytes never have.
pub proof fn lemma_plain_free_masks()
    ensures
        DOMAIN_SLOW & PLAIN_FREE == DOMAIN_SLOW,
        AUTHORITY_STOP & PLAIN_FREE == AUTHORITY_STOP,
        (AUTHORITY_STOP | BACKSLASH) & PLAIN_FREE == AUTHORITY_STOP | BACKSLASH,
        (AUTHORITY_STOP | HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == AUTHORITY_STOP | HOST_STOP | DOMAIN_SLOW,
        (AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == AUTHORITY_STOP | BACKSLASH
            | HOST_STOP | DOMAIN_SLOW,
        HOST_STOP & PLAIN_FREE == HOST_STOP,
        (HOST_STOP | BACKSLASH) & PLAIN_FREE == HOST_STOP | BACKSLASH,
        (HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == HOST_STOP | DOMAIN_SLOW,
        (HOST_STOP | BACKSLASH | DOMAIN_SLOW) & PLAIN_FREE == HOST_STOP | BACKSLASH | DOMAIN_SLOW,
{
    assert(DOMAIN_SLOW & PLAIN_FREE == DOMAIN_SLOW) by (compute_only);
    assert(AUTHORITY_STOP & PLAIN_FREE == AUTHORITY_STOP) by (compute_only);
    assert((AUTHORITY_STOP | BACKSLASH) & PLAIN_FREE == AUTHORITY_STOP | BACKSLASH) by (compute_only);
    assert((AUTHORITY_STOP | HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == AUTHORITY_STOP | HOST_STOP
        | DOMAIN_SLOW) by (compute_only);
    assert((AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == AUTHORITY_STOP
        | BACKSLASH | HOST_STOP | DOMAIN_SLOW) by (compute_only);
    assert(HOST_STOP & PLAIN_FREE == HOST_STOP) by (compute_only);
    assert((HOST_STOP | BACKSLASH) & PLAIN_FREE == HOST_STOP | BACKSLASH) by (compute_only);
    assert((HOST_STOP | DOMAIN_SLOW) & PLAIN_FREE == HOST_STOP | DOMAIN_SLOW) by (compute_only);
    assert((HOST_STOP | BACKSLASH | DOMAIN_SLOW) & PLAIN_FREE == HOST_STOP | BACKSLASH | DOMAIN_SLOW) by (compute_only);
}

pub open spec fn lane(w: u64, i: u64) -> u64 {
    (w >> (8 * i)) & 0xff
}

/// Lane `i` of the result has its high bit set exactly when byte `i` of `w`
/// is not plain; every other bit is clear.
pub open spec fn nonplain_spec(w: u64) -> u64 {
    let x = w & 0x7f7f7f7f7f7f7f7f;
    // (x + (0x80 - c)) has its lane's high bit set iff the lane is >= c;
    // no lane carries since every lane of x is below 0x80.
    let lo = ((x + 0x1f1f1f1f1f1f1f1f) as u64) & !((x + 0x0505050505050505) as u64);
    let dg = ((x + 0x5050505050505050) as u64) & !((x + 0x4646464646464646) as u64);
    let dd = ((x + 0x5353535353535353) as u64) & !((x + 0x5151515151515151) as u64);
    (!(lo | dg | dd) | w) & 0x8080808080808080
}

pub proof fn lemma_nonplain_lane(w: u64, i: u64)
    requires
        i < 8,
    ensures
        ((nonplain_spec(w) >> (8 * i + 7)) & 1 == 1) == !dplain64(lane(w, i)),
{
    let r = nonplain_spec(w);
    if i == 0 {
        assert(((r >> 7) & 1 == 1) == !dplain64((w >> 0) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 1 {
        assert(((r >> 15) & 1 == 1) == !dplain64((w >> 8) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 2 {
        assert(((r >> 23) & 1 == 1) == !dplain64((w >> 16) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 3 {
        assert(((r >> 31) & 1 == 1) == !dplain64((w >> 24) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 4 {
        assert(((r >> 39) & 1 == 1) == !dplain64((w >> 32) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 5 {
        assert(((r >> 47) & 1 == 1) == !dplain64((w >> 40) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else if i == 6 {
        assert(((r >> 55) & 1 == 1) == !dplain64((w >> 48) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    } else {
        assert(((r >> 63) & 1 == 1) == !dplain64((w >> 56) & 0xff)) by (bit_vector)
            requires r == nonplain_spec(w);
    }
}

/// The little-endian word of `s[k..k + 8]`.
#[inline(always)]
fn load8(s: &[u8], k: usize) -> (w: u64)
    requires
        k + 8 <= s.len(),
    ensures
        forall|i: u64| i < 8 ==> lane(w, i) == s@[k + i] as u64,
{
    let v = vstd::slice::slice_subrange(s, k, k + 8);
    let b0 = v[0] as u64;
    let b1 = v[1] as u64;
    let b2 = v[2] as u64;
    let b3 = v[3] as u64;
    let b4 = v[4] as u64;
    let b5 = v[5] as u64;
    let b6 = v[6] as u64;
    let b7 = v[7] as u64;
    let w = b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56;
    proof {
        assert forall|i: u64| i < 8 implies lane(w, i) == s@[k + i] as u64 by {
            assert(s@[k + i] == v@[i as int]);
            let ghost wv = w;
            if i == 0 {
                assert((wv >> 0) & 0xff == b0) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 1 {
                assert((wv >> 8) & 0xff == b1) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 2 {
                assert((wv >> 16) & 0xff == b2) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 3 {
                assert((wv >> 24) & 0xff == b3) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 4 {
                assert((wv >> 32) & 0xff == b4) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 5 {
                assert((wv >> 40) & 0xff == b5) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else if i == 6 {
                assert((wv >> 48) & 0xff == b6) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            } else {
                assert((wv >> 56) & 0xff == b7) by (bit_vector)
                    requires wv == b0 | b1 << 8 | b2 << 16 | b3 << 24 | b4 << 32 | b5 << 40 | b6 << 48 | b7 << 56,
                        b0 < 256, b1 < 256, b2 < 256, b3 < 256, b4 < 256, b5 < 256, b6 < 256, b7 < 256;
            }
        }
    }
    w
}

#[inline(always)]
fn nonplain8(w: u64) -> (r: u64)
    ensures
        r == nonplain_spec(w),
{
    let x = w & 0x7f7f7f7f7f7f7f7f;
    assert(x <= 0x7f7f7f7f7f7f7f7f) by (bit_vector)
        requires x == w & 0x7f7f7f7f7f7f7f7f;
    let lo = (x + 0x1f1f1f1f1f1f1f1f) & !(x + 0x0505050505050505);
    let dg = (x + 0x5050505050505050) & !(x + 0x4646464646464646);
    let dd = (x + 0x5353535353535353) & !(x + 0x5151515151515151);
    let r = (!(lo | dg | dd) | w) & 0x8080808080808080;
    r
}

/// `8 * d` where `d` is the number of plain bytes at the start of
/// `s[k..k + 8]` (64 when all eight are), possibly plus 0..7.
#[inline(always)]
fn plain_prefix8(s: &[u8], k: usize) -> (z: u32)
    requires
        k + 8 <= s.len(),
    ensures
        z <= 64,
        forall|j: int| k <= j < k + z / 8 ==> dplain(#[trigger] s@[j]),
{
    let w = load8(s, k);
    let r = nonplain8(w);
    let z = r.trailing_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;

        let zz = z as u64;
        assert forall|j: int| k <= j < k + z / 8 implies dplain(#[trigger] s@[j]) by {
            let i = (j - k) as u64;
            assert(8 * i + 7 < zz);
            assert((r >> (8 * i + 7)) & 1 == 0);
            lemma_nonplain_lane(w, i);
        }
    }
    z
}

/// Skips plain bytes from `a`, a word at a time: stops at the first byte
/// that is not plain or when fewer than 8 bytes are left before `b`.
#[inline(always)]
pub fn skip_plain(s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
    ensures
        a <= k <= b,
        final(cost).n == old(cost).n + (k - a),
        forall|j: int| a <= j < k ==> dplain(#[trigger] s@[j]),
{
    let t = vstd::slice::slice_subrange(s, 0, b);
    let mut k = a;
    // Sixteen bytes at a time, with one vector compare chain per block.
    while b - k >= 16
        invariant
            a <= k <= b == t.len() <= s.len(),
            t@ == s@.subrange(0, b as int),
            forall|j: int| a <= j < k ==> dplain(#[trigger] s@[j]),
            cost.n == old(cost).n + (k - a),
        decreases b - k,
    {
        let m = nonplain_mask16(t, k);
        let r = verilith_simd::sse2::first_set16(m);
        proof {
            assert forall|j: int| a <= j < k + r implies dplain(#[trigger] s@[j]) by {
                if j >= k {
                    let jj = (j - k) as u32;
                    assert(!verilith_simd::sse2::bit(m, jj));
                    assert(t@[k + jj] == s@[j]);
                }
            }
            cost.n = cost.n + r as nat;
        }
        if r < 16 {
            return k + r;
        }
        k = k + 16;
    }
    while b - k >= 8
        invariant
            a <= k <= b == t.len() <= s.len(),
            t@ == s@.subrange(0, b as int),
            forall|j: int| a <= j < k ==> dplain(#[trigger] s@[j]),
            cost.n == old(cost).n + (k - a),
        decreases b - k,
    {
        let z = plain_prefix8(t, k);
        proof {
            assert forall|j: int| a <= j < k + z / 8 implies dplain(#[trigger] s@[j]) by {
                if j >= k {
                    assert(s@[j] == t@[j]);
                }
            }
            cost.n = cost.n + (z / 8) as nat;
        }
        if z != 64 {
            return k + (z / 8) as usize;
        }
        k = k + 8;
    }
    k
}

/// Bit `j` is set when `s[k + j]` is not `dplain`.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn nonplain_mask16(s: &[u8], k: usize) -> (m: u32)
    requires
        k + 16 <= s.len(),
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> #[trigger] verilith_simd::sse2::bit(m, j) == !dplain(s@[k + j]),
{
    crate::simd::nonplain_mask16_sse(s, k)
}

/// Bit `j` is set when `s[k + j]` is not `dplain`.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn nonplain_mask16(s: &[u8], k: usize) -> (m: u32)
    requires
        k + 16 <= s.len(),
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> #[trigger] verilith_simd::sse2::bit(m, j) == !dplain(s@[k + j]),
{
    if verilith_simd::neon::has_neon() {
        return crate::simd::nonplain_mask16_neon(s, k);
    }
    let mut m: u32 = 0;
    let mut i: u32 = 0;
    proof {
        assert((1u32 << 0u32) == 1u32) by (bit_vector);
    }
    while i < 16
        invariant
            i <= 16,
            k + 16 <= s.len(),
            m < (1u32 << i),
            forall|j: u32| j < i ==> #[trigger] verilith_simd::sse2::bit(m, j) == !dplain(s@[k + j]),
        decreases 16 - i,
    {
        let c = s[k + i as usize];
        let np = !((0x61 <= c && c <= 0x7A) || (0x30 <= c && c <= 0x39) || c == 0x2D || c == 0x2E);
        let x = np as u32;
        proof {
            assert forall|j: u32| j < i + 1 implies #[trigger] verilith_simd::sse2::bit(m | (x << i), j) == !dplain(
                s@[k + j],
            ) by {
                crate::encode::lemma_mask_bit(m, x, i, j);
                if j < i {
                    assert(verilith_simd::sse2::bit(m, j) == !dplain(s@[k + j]));
                } else {
                    assert(j == i);
                    assert(s@[k + j] == c);
                    assert((x == 1) == np);
                }
            }
            crate::encode::lemma_mask_bit(m, x, i, 0);
        }
        m = m | (x << i);
        i = i + 1;
    }
    proof {
        assert((1u32 << 16u32) == 0x10000u32) by (bit_vector);
    }
    m
}

/// `find_cls` for a mask of classes plain bytes never have: skips plain
/// words first.
#[inline(always)]
pub fn find_cls_plain(s: &[u8], a: usize, b: usize, m: u16, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
        m & PLAIN_FREE == m,
    ensures
        a <= k <= b,
        final(cost).n == old(cost).n + (k - a) + 1,
        forall|j: int| a <= j < k ==> !cls_has(#[trigger] s@[j], m),
        k < b ==> cls_has(s@[k as int], m),
{
    let w = skip_plain(s, a, b, Tracked(cost));
    let k = crate::encode::find_cls(s, w, b, m, Tracked(cost));
    proof {
        lemma_dplain_cls();
        assert forall|j: int| a <= j < k implies !cls_has(#[trigger] s@[j], m) by {
            if j < w {
                let x = CLS@[s@[j] as int];
                assert(dplain(s@[j]));
                assert(x & PLAIN_FREE == 0);
                assert(x & PLAIN_FREE == 0 && m & PLAIN_FREE == m ==> x & m == 0) by (bit_vector);
            }
        }
    }
    k
}

} // verus!

verus! {

pub proof fn lemma_lane_low_zero(x: u64, z: u64, j: u64)
    requires
        z <= 64,
        x << sub(64, z) == 0,
        8 * j + 8 <= z,
    ensures
        lane(x, j) == 0,
{
    assert((x >> (8 * j)) & 0xff == 0) by (bit_vector)
        requires z <= 64, x << sub(64, z) == 0, 8 * j + 8 <= z;
}

pub proof fn lemma_lane_tz_nonzero(x: u64, z: u64)
    requires
        z < 64,
        (x >> z) & 1 == 1,
    ensures
        lane(x, z / 8) != 0,
{
    assert((x >> (8 * (z / 8))) & 0xff != 0) by (bit_vector)
        requires z < 64, (x >> z) & 1 == 1;
}

pub proof fn lemma_lane_clear(x: u64, d: u64, i: u64)
    requires
        d < 8,
        i < 8,
    ensures
        lane(x & (0xffff_ffff_ffff_ffffu64 << (8 * d)), i) == if i < d { 0 } else { lane(x, i) },
{
    let y = x & (0xffff_ffff_ffff_ffffu64 << (8 * d));
    if i < d {
        assert((y >> (8 * i)) & 0xff == 0) by (bit_vector)
            requires y == x & (0xffff_ffff_ffff_ffffu64 << (8 * d)), d < 8, i < d;
    } else {
        assert((y >> (8 * i)) & 0xff == (x >> (8 * i)) & 0xff) by (bit_vector)
            requires y == x & (0xffff_ffff_ffff_ffffu64 << (8 * d)), d < 8, i < 8, d <= i;
    }
}

/// The index of the first nonzero lane of `x` as
/// `8 * index + 0..7`, or 64.
#[inline(always)]
fn first_lane(x: u64) -> (z: u32)
    ensures
        z <= 64,
        forall|j: u64| j < z / 8 ==> lane(x, j) == 0,
        z < 64 ==> lane(x, (z / 8) as u64) != 0,
{
    let z = x.trailing_zeros();
    proof {
        broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;

        let zz = z as u64;
        assert forall|j: u64| j < z / 8 implies lane(x, j) == 0 by {
            lemma_lane_low_zero(x, zz, j);
        }
        if z < 64 {
            lemma_lane_tz_nonzero(x, zz);
            assert(zz / 8 == (z / 8) as u64);
        }
    }
    z
}

/// The first index in `d..16` whose flag is nonzero, or 16.
#[inline(always)]
pub fn first_flag16(f: &[u8; 16], d: u32) -> (r: u32)
    requires
        d < 16,
    ensures
        d <= r <= 16,
        forall|j: int| d <= j < r ==> f@[j] == 0,
        r < 16 ==> f@[r as int] != 0,
{
    let s = f.as_slice();
    let lo0 = load8(s, 0);
    let hi0 = load8(s, 8);
    let lo = if d >= 8 {
        0
    } else {
        lo0 & (0xffff_ffff_ffff_ffffu64 << (8 * d as u64))
    };
    let hi = if d >= 8 {
        hi0 & (0xffff_ffff_ffff_ffffu64 << (8 * (d - 8) as u64))
    } else {
        hi0
    };
    proof {
        assert forall|i: u64| i < 8 implies lane(lo, i) == if (i as int) < d { 0 } else { s@[i as int] as u64 } by {
            if d >= 8 {
                assert(lane(0, i) == 0) by (bit_vector);
            } else {
                lemma_lane_clear(lo0, d as u64, i);
            }
        }
        assert forall|i: u64| i < 8 implies lane(hi, i) == if 8 + (i as int) < d { 0 } else { s@[8 + i as int] as u64 } by {
            if d >= 8 {
                lemma_lane_clear(hi0, (d - 8) as u64, i);
            }
        }
    }
    let z1 = first_lane(lo);
    let z2 = first_lane(hi);
    proof {
        assert(z1 <= 64 ==> (z1 >> 6u32 == 1) == (z1 == 64)) by (bit_vector);
        assert(z1 <= 64 ==> (z1 >> 6u32 == 0) == (z1 < 64)) by (bit_vector);
    }
    // z1 + z2 when the low word has no flag, else z1.
    let z = z1 + (z1 >> 6u32) * z2;
    let r = z / 8;
    proof {
        assert forall|j: int| d <= j < r implies f@[j] == 0 by {
            if j < 8 {
                assert(lane(lo, j as u64) == 0);
            } else {
                assert(z1 == 64);
                assert(lane(hi, (j - 8) as u64) == 0);
            }
        }
        if r < 16 {
            if z1 < 64 {
                assert(lane(lo, (z1 / 8) as u64) != 0);
            } else {
                assert(lane(hi, (z2 / 8) as u64) != 0);
            }
        }
    }
    r
}

} // verus!
