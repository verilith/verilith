//! Fast single-pixel arithmetic for the sequential predictor modes:
//! SWAR on the packed 32-bit pixel, and `psadbw` for the select predictor.
#[cfg(verus_only)]
use crate::pixels::lemma_argb;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::vlemmas::*;
use verilith_simd::arch::*;
use verilith_simd::cpu::*;
#[cfg(verus_only)]
use verilith_simd::lanes::*;
#[cfg(verus_only)]
use verilith_simd::ops::*;
use vstd::prelude::*;

verus! {

broadcast use {verilith_simd::lanes::group_lanes, verilith_simd::cpu::group_cpu};

/// `add_px`, two channels at a time.
#[inline(always)]
pub fn add_px_swar(a: u32, b: u32) -> (r: u32)
    ensures
        r == add_px(a, b),
{
    let hi = ((a & 0xff00ff00) as u64 + (b & 0xff00ff00) as u64) as u32 & 0xff00ff00;
    proof {
        assert((a & 0x00ff00ffu32) as int + (b & 0x00ff00ffu32) as int <= 0x01fe01fe) by {
            assert(a & 0x00ff00ffu32 <= 0x00ff00ffu32 && b & 0x00ff00ffu32 <= 0x00ff00ffu32) by (bit_vector);
        }
    }
    let lo = ((a & 0x00ff00ff) + (b & 0x00ff00ff)) & 0x00ff00ff;
    proof {
        let (aa, ar, ag, ab) = (a >> 24u32, (a >> 16u32) & 0xffu32, (a >> 8u32) & 0xffu32, a & 0xffu32);
        let (ba, br, bg, bb) = (b >> 24u32, (b >> 16u32) & 0xffu32, (b >> 8u32) & 0xffu32, b & 0xffu32);
        lemma_argb(((aa + ba) % 256) as u32, ((ar + br) % 256) as u32, ((ag + bg) % 256) as u32, ((ab + bb) % 256) as u32);
        assert(((((a & 0xff00ff00u32) as u64 + (b & 0xff00ff00u32) as u64) as u32) & 0xff00ff00u32) | ((((a
            & 0x00ff00ffu32) + (b & 0x00ff00ffu32)) as u32) & 0x00ff00ffu32) == (((((a >> 24u32) + (b >> 24u32)) % 256) as u32)
            << 24u32) | ((((((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) % 256) as u32) << 16u32) | ((((((a
            >> 8u32) & 0xffu32) + ((b >> 8u32) & 0xffu32)) % 256) as u32) << 8u32) | ((((a & 0xffu32) + (b & 0xffu32))
            % 256) as u32)) by (bit_vector);
    }
    hi | lo
}

/// `avg2`, all four channels at once.
#[inline(always)]
pub fn avg2_swar(a: u32, b: u32) -> (r: u32)
    ensures
        r == avg2(a, b),
{
    proof {
        let (aa, ar, ag, ab) = (a >> 24u32, (a >> 16u32) & 0xffu32, (a >> 8u32) & 0xffu32, a & 0xffu32);
        let (ba, br, bg, bb) = (b >> 24u32, (b >> 16u32) & 0xffu32, (b >> 8u32) & 0xffu32, b & 0xffu32);
        assert(a >> 24u32 < 256 && (a >> 16u32) & 0xffu32 < 256 && (a >> 8u32) & 0xffu32 < 256 && a & 0xffu32 < 256)
            by (bit_vector);
        assert(b >> 24u32 < 256 && (b >> 16u32) & 0xffu32 < 256 && (b >> 8u32) & 0xffu32 < 256 && b & 0xffu32 < 256)
            by (bit_vector);
        lemma_argb(((aa + ba) / 2) as u32, ((ar + br) / 2) as u32, ((ag + bg) / 2) as u32, ((ab + bb) / 2) as u32);
        assert(((a & b) + (((a ^ b) & 0xfefefefeu32) >> 1u32)) as u32 == (((((a >> 24u32) + (b >> 24u32)) / 2) as u32)
            << 24u32) | ((((((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) / 2) as u32) << 16u32) | ((((((a >> 8u32)
            & 0xffu32) + ((b >> 8u32) & 0xffu32)) / 2) as u32) << 8u32) | ((((a & 0xffu32) + (b & 0xffu32)) / 2) as u32))
            by (bit_vector);
        assert((a & b) as int + (((a ^ b) & 0xfefefefeu32) >> 1u32) as int <= 0xffff_ffff) by {
            assert((a & b) + (((a ^ b) & 0xfefefefeu32) >> 1u32) == ((a & b) as u64 + (((a ^ b) & 0xfefefefeu32)
                >> 1u32) as u64) as u32 && (a & b) as u64 + (((a ^ b) & 0xfefefefeu32) >> 1u32) as u64 <= 0xffff_ffff)
                by (bit_vector);
        }
    }
    (a & b) + (((a ^ b) & 0xfefefefe) >> 1)
}

/// The sum over channels of `|x - y|`, as `spec::select` measures it.
pub open spec fn chan_dist(x: u32, y: u32) -> int {
    abs(alpha(x) - alpha(y)) + abs(red(x) - red(y)) + abs(green(x) - green(y)) + abs(blue(x) - blue(y))
}

/// `chan_dist` with one `psadbw`.
#[inline]
#[inline(always)]
pub fn chan_dist_sad(x: u32, y: u32) -> (r: u64)
    requires
        avx2(),
    ensures
        r as int == chan_dist(x, y),
{
    let vx = _mm_cvtsi32_si128(i32_of_u32(x));
    let vy = _mm_cvtsi32_si128(i32_of_u32(y));
    let s = _mm_sad_epu8(vx, vy);
    let r = u64_of(_mm_cvtsi128_si64(s));
    proof {
        let (bx, by) = (b128(vx), b128(vy));
        lemma_u32s_bytes(bx);
        lemma_u32s_bytes(by);
        assert(u32x4(vx)[0] == x && u32x4(vx)[1] == 0 && u32x4(vy)[0] == y && u32x4(vy)[1] == 0);
        assert(byte32(0u32, 0) == 0 && byte32(0u32, 1) == 0 && byte32(0u32, 2) == 0 && byte32(0u32, 3) == 0) by (compute);
        assert forall|c: int| 0 <= c < 4 implies #[trigger] bx[c] == byte32(x, c) && by[c] == byte32(y, c) && bx[4 + c]
            == 0 && by[4 + c] == 0 by {
            assert(byte32(u32s(bx)[0], c) == bx[4 * 0 + c]);
            assert(byte32(u32s(bx)[1], c) == bx[4 * 1 + c]);
            assert(byte32(u32s(by)[0], c) == by[4 * 0 + c]);
            assert(byte32(u32s(by)[1], c) == by[4 * 1 + c]);
        }
        let (a8, b8) = (bx.subrange(0, 8), by.subrange(0, 8));
        reveal_with_fuel(sad_bytes, 9);
        assert(a8.drop_first() =~= bx.subrange(1, 8));
        assert(sad_bytes(a8, b8) == absdiff(bx[0], by[0]) + absdiff(bx[1], by[1]) + absdiff(bx[2], by[2])
            + absdiff(bx[3], by[3]) + absdiff(bx[4], by[4]) + absdiff(bx[5], by[5]) + absdiff(bx[6], by[6])
            + absdiff(bx[7], by[7])) by {
            lemma_sad_unroll(a8, b8);
        }
        lemma_px_bytes(x);
        lemma_px_bytes(y);
        assert(sad8(bx, by)[0] == sad_bytes(a8, b8) as u64);
        assert(u64x2(s)[0] == sad8(bx, by)[0]);
    }
    r
}

proof fn lemma_sad_unroll(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() == 8,
        b.len() == 8,
    ensures
        sad_bytes(a, b) == absdiff(a[0], b[0]) + absdiff(a[1], b[1]) + absdiff(a[2], b[2]) + absdiff(a[3], b[3])
            + absdiff(a[4], b[4]) + absdiff(a[5], b[5]) + absdiff(a[6], b[6]) + absdiff(a[7], b[7]),
{
    reveal_with_fuel(sad_bytes, 9);
    assert(a.drop_first()[0] == a[1]);
    assert(a.drop_first().drop_first()[0] == a[2]);
    assert(a.drop_first().drop_first().drop_first()[0] == a[3]);
    assert(a.drop_first().drop_first().drop_first().drop_first()[0] == a[4]);
    assert(a.drop_first().drop_first().drop_first().drop_first().drop_first()[0] == a[5]);
    assert(a.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()[0] == a[6]);
    assert(a.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()[0] == a[7]);
    assert(b.drop_first()[0] == b[1]);
    assert(b.drop_first().drop_first()[0] == b[2]);
    assert(b.drop_first().drop_first().drop_first()[0] == b[3]);
    assert(b.drop_first().drop_first().drop_first().drop_first()[0] == b[4]);
    assert(b.drop_first().drop_first().drop_first().drop_first().drop_first()[0] == b[5]);
    assert(b.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()[0] == b[6]);
    assert(b.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first()[0] == b[7]);
    assert(a.drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().drop_first().len() == 0);
}

/// `spec::select` with two `psadbw`s.
#[inline]
#[inline(always)]
pub fn select_sad(l: u32, t: u32, tl: u32) -> (r: u32)
    requires
        avx2(),
    ensures
        r == select(l, t, tl),
{
    let pl = chan_dist_sad(t, tl);
    let pt = chan_dist_sad(l, tl);
    if pl < pt {
        l
    } else {
        t
    }
}

/// The `i32` with the bits of `x`.
#[inline(always)]
pub fn i32_of_u32(x: u32) -> (r: i32)
    ensures
        u32_of_i32(r) == x,
{
    if x < 0x8000_0000 {
        x as i32
    } else {
        ((x - 0x8000_0000) as i32) - 0x7fff_ffff - 1
    }
}

/// The `u64` with the bits of `x`.
#[inline(always)]
pub fn u64_of(x: i64) -> (r: u64)
    ensures
        r == u64_of_i64(x),
{
    if x >= 0 {
        x as u64
    } else {
        ((x + 1 + 0x7fff_ffff_ffff_ffff) as u64) + 0x8000_0000_0000_0000
    }
}

} // verus!
