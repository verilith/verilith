//! Portable emulation of the NEON intrinsics that `crate::neon` wraps.
//!
//! On AArch64 `crate::neon` calls `core::arch::aarch64`; on every other
//! target it calls these, so NEON kernels build (and their proofs are
//! checked) on x86-64 too. They are never selected at run time off AArch64
//! (`has_neon` is false there), except by tests. Not verified;
//! `tests/neon.rs` compares the real instructions with the verified
//! references on AArch64.
#![allow(non_camel_case_types, clippy::missing_safety_doc)]
#![allow(unsafe_op_in_unsafe_fn)]

/// The NEON vector type `uint8x16_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct uint8x16_t(pub [u8; 16]);

/// The NEON vector type `uint16x8_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct uint16x8_t(pub [u16; 8]);

fn map(a: uint8x16_t, b: uint8x16_t, f: impl Fn(u8, u8) -> u8) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| f(a.0[i], b.0[i])))
}

/// The NEON intrinsic `vld1q_u8`, emulated.
///
/// # Safety
///
/// `p` must be valid for a read of the vector's size.
pub unsafe fn vld1q_u8(p: *const u8) -> uint8x16_t {
    core::ptr::read_unaligned(p as *const uint8x16_t)
}
/// The NEON intrinsic `vst1q_u8`, emulated.
///
/// # Safety
///
/// `p` must be valid for a write of the vector's size.
pub unsafe fn vst1q_u8(p: *mut u8, v: uint8x16_t) {
    core::ptr::write_unaligned(p as *mut uint8x16_t, v)
}
/// The NEON intrinsic `vld1q_u16`, emulated.
///
/// # Safety
///
/// `p` must be valid for a read of the vector's size.
pub unsafe fn vld1q_u16(p: *const u16) -> uint16x8_t {
    core::ptr::read_unaligned(p as *const uint16x8_t)
}
/// The NEON intrinsic `vst1q_u16`, emulated.
///
/// # Safety
///
/// `p` must be valid for a write of the vector's size.
pub unsafe fn vst1q_u16(p: *mut u16, v: uint16x8_t) {
    core::ptr::write_unaligned(p as *mut uint16x8_t, v)
}
/// The NEON intrinsic `vreinterpretq_u16_u8`, emulated.
pub fn vreinterpretq_u16_u8(a: uint8x16_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| u16::from_le_bytes([a.0[2 * i], a.0[2 * i + 1]])))
}
/// The NEON intrinsic `vreinterpretq_u8_u16`, emulated.
pub fn vreinterpretq_u8_u16(a: uint16x8_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| a.0[i / 2].to_le_bytes()[i % 2]))
}
/// The NEON intrinsic `vdupq_n_u8`, emulated.
pub fn vdupq_n_u8(x: u8) -> uint8x16_t {
    uint8x16_t([x; 16])
}
/// The NEON intrinsic `vandq_u8`, emulated.
pub fn vandq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| x & y)
}
/// The NEON intrinsic `vorrq_u8`, emulated.
pub fn vorrq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| x | y)
}
/// The NEON intrinsic `veorq_u8`, emulated.
pub fn veorq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| x ^ y)
}
/// The NEON intrinsic `vaddq_u8`, emulated.
pub fn vaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::wrapping_add)
}
/// The NEON intrinsic `vqsubq_u8`, emulated.
pub fn vqsubq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::saturating_sub)
}
/// The NEON intrinsic `vceqq_u8`, emulated.
pub fn vceqq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| if x == y { 0xff } else { 0 })
}
/// The NEON intrinsic `vshrq_n_u8`, emulated.
pub fn vshrq_n_u8<const N: i32>(a: uint8x16_t) -> uint8x16_t {
    uint8x16_t(a.0.map(|x| if N >= 8 { 0 } else { x >> N }))
}
/// The NEON intrinsic `vqtbl1q_u8`, emulated.
pub fn vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> uint8x16_t {
    uint8x16_t(idx.0.map(|k| if k < 16 { t.0[k as usize] } else { 0 }))
}
/// The NEON intrinsic `vextq_u8`, emulated.
pub fn vextq_u8<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| {
        let k = i + N as usize;
        if k < 16 {
            a.0[k]
        } else {
            b.0[k - 16]
        }
    }))
}
/// The NEON intrinsic `vzip1q_u8`, emulated.
pub fn vzip1q_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[i / 2] } else { b.0[i / 2] }))
}
/// The NEON intrinsic `vzip2q_u8`, emulated.
pub fn vzip2q_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[8 + i / 2] } else { b.0[8 + i / 2] }))
}
/// The NEON intrinsic `vuzp1q_u8`, emulated.
pub fn vuzp1q_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| if i < 8 { a.0[2 * i] } else { b.0[2 * i - 16] }))
}
/// The NEON intrinsic `vmaxvq_u8`, emulated.
pub fn vmaxvq_u8(a: uint8x16_t) -> u8 {
    a.0.into_iter().max().unwrap()
}
/// The NEON intrinsic `vmaxvq_u16`, emulated.
pub fn vmaxvq_u16(a: uint16x8_t) -> u16 {
    a.0.into_iter().max().unwrap()
}
/// The NEON intrinsic `vpaddq_u8`, emulated.
pub fn vpaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| {
        let src = if i < 8 { &a.0 } else { &b.0 };
        let j = 2 * (i % 8);
        src[j].wrapping_add(src[j + 1])
    }))
}

/// The NEON vector type `uint64x2_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct uint64x2_t(pub [u64; 2]);

/// The NEON intrinsic `vreinterpretq_u64_u8`, emulated.
pub fn vreinterpretq_u64_u8(a: uint8x16_t) -> uint64x2_t {
    uint64x2_t(core::array::from_fn(|i| u64::from_le_bytes(a.0[8 * i..8 * i + 8].try_into().unwrap())))
}
/// The NEON intrinsic `vgetq_lane_u64`, emulated.
pub fn vgetq_lane_u64<const N: i32>(a: uint64x2_t) -> u64 {
    a.0[N as usize]
}

/// The NEON vector type `uint8x8_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(8))]
pub struct uint8x8_t(pub [u8; 8]);

/// The NEON vector type `uint64x1_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(8))]
pub struct uint64x1_t(pub [u64; 1]);

/// The NEON intrinsic `vshrn_n_u16`, emulated.
pub fn vshrn_n_u16<const N: i32>(a: uint16x8_t) -> uint8x8_t {
    uint8x8_t(core::array::from_fn(|i| (a.0[i] >> N) as u8))
}
/// The NEON intrinsic `vreinterpret_u64_u8`, emulated.
pub fn vreinterpret_u64_u8(a: uint8x8_t) -> uint64x1_t {
    uint64x1_t([u64::from_le_bytes(a.0)])
}
/// The NEON intrinsic `vget_lane_u64`, emulated.
pub fn vget_lane_u64<const N: i32>(a: uint64x1_t) -> u64 {
    a.0[N as usize]
}

/// The NEON vector type `uint32x4_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct uint32x4_t(pub [u32; 4]);

/// The NEON intrinsic `vld1q_u32`, emulated.
///
/// # Safety
///
/// `p` must be valid for a read of the vector's size.
pub unsafe fn vld1q_u32(p: *const u32) -> uint32x4_t {
    core::ptr::read_unaligned(p as *const uint32x4_t)
}
/// The NEON intrinsic `vst1q_u32`, emulated.
///
/// # Safety
///
/// `p` must be valid for a write of the vector's size.
pub unsafe fn vst1q_u32(p: *mut u32, v: uint32x4_t) {
    core::ptr::write_unaligned(p as *mut uint32x4_t, v)
}
/// The NEON intrinsic `vreinterpretq_u32_u8`, emulated.
pub fn vreinterpretq_u32_u8(a: uint8x16_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| u32::from_le_bytes(a.0[4 * i..4 * i + 4].try_into().unwrap())))
}
/// The NEON intrinsic `vreinterpretq_u8_u32`, emulated.
pub fn vreinterpretq_u8_u32(a: uint32x4_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| a.0[i / 4].to_le_bytes()[i % 4]))
}
/// The NEON intrinsic `vdupq_n_u32`, emulated.
pub fn vdupq_n_u32(x: u32) -> uint32x4_t {
    uint32x4_t([x; 4])
}
/// The NEON intrinsic `vdupq_laneq_u32`, emulated.
pub fn vdupq_laneq_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    uint32x4_t([a.0[N as usize]; 4])
}

/// The NEON intrinsic `vreinterpretq_u8_u64`, emulated.
pub fn vreinterpretq_u8_u64(a: uint64x2_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| a.0[i / 8].to_le_bytes()[i % 8]))
}
/// The NEON intrinsic `vzip1q_u16`, emulated.
pub fn vzip1q_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[i / 2] } else { b.0[i / 2] }))
}
/// The NEON intrinsic `vzip2q_u16`, emulated.
pub fn vzip2q_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[4 + i / 2] } else { b.0[4 + i / 2] }))
}
/// The NEON intrinsic `vzip1q_u32`, emulated.
pub fn vzip1q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[i / 2] } else { b.0[i / 2] }))
}
/// The NEON intrinsic `vzip2q_u32`, emulated.
pub fn vzip2q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| if i % 2 == 0 { a.0[2 + i / 2] } else { b.0[2 + i / 2] }))
}
/// The NEON intrinsic `vzip1q_u64`, emulated.
pub fn vzip1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    uint64x2_t([a.0[0], b.0[0]])
}
/// The NEON intrinsic `vzip2q_u64`, emulated.
pub fn vzip2q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    uint64x2_t([a.0[1], b.0[1]])
}

/// The NEON vector type `int16x8_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct int16x8_t(pub [i16; 8]);

/// The NEON intrinsic `vreinterpretq_s16_u8`, emulated.
pub fn vreinterpretq_s16_u8(a: uint8x16_t) -> int16x8_t {
    int16x8_t(core::array::from_fn(|i| i16::from_le_bytes([a.0[2 * i], a.0[2 * i + 1]])))
}
/// The NEON intrinsic `vreinterpretq_u8_s16`, emulated.
pub fn vreinterpretq_u8_s16(a: int16x8_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| a.0[i / 2].to_le_bytes()[i % 2]))
}
/// The NEON intrinsic `vdupq_n_u16`, emulated.
pub fn vdupq_n_u16(x: u16) -> uint16x8_t {
    uint16x8_t([x; 8])
}
/// The NEON intrinsic `vaddq_u16`, emulated.
pub fn vaddq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].wrapping_add(b.0[i])))
}
/// The NEON intrinsic `vsubq_u16`, emulated.
pub fn vsubq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].wrapping_sub(b.0[i])))
}
/// The NEON intrinsic `vshrq_n_s16`, emulated.
pub fn vshrq_n_s16<const N: i32>(a: int16x8_t) -> int16x8_t {
    int16x8_t(core::array::from_fn(|i| a.0[i] >> N))
}
/// The NEON intrinsic `vqdmulhq_s16`, emulated.
pub fn vqdmulhq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    int16x8_t(core::array::from_fn(|i| ((2 * a.0[i] as i64 * b.0[i] as i64) >> 16).clamp(-0x8000, 0x7fff) as i16))
}

/// The NEON intrinsic `vrhaddq_u8`, emulated.
pub fn vrhaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| ((x as u16 + y as u16 + 1) >> 1) as u8)
}
/// The NEON intrinsic `vsubq_u8`, emulated.
pub fn vsubq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::wrapping_sub)
}
/// The NEON intrinsic `vqsubq_u16`, emulated.
pub fn vqsubq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].saturating_sub(b.0[i])))
}
/// The NEON intrinsic `vget_low_u8`, emulated.
pub fn vget_low_u8(a: uint8x16_t) -> uint8x8_t {
    uint8x8_t(core::array::from_fn(|i| a.0[i]))
}
/// The NEON intrinsic `vshll_n_u8`, emulated.
pub fn vshll_n_u8<const N: i32>(a: uint8x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| (a.0[i] as u16) << N))
}
/// The NEON intrinsic `vshll_high_n_u8`, emulated.
pub fn vshll_high_n_u8<const N: i32>(a: uint8x16_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| (a.0[8 + i] as u16) << N))
}
/// The NEON intrinsic `vqshrun_n_s16`, emulated.
pub fn vqshrun_n_s16<const N: i32>(a: int16x8_t) -> uint8x8_t {
    uint8x8_t(core::array::from_fn(|i| (a.0[i] >> N).clamp(0, 255) as u8))
}
/// The NEON intrinsic `vqshrun_high_n_s16`, emulated.
pub fn vqshrun_high_n_s16<const N: i32>(a: uint8x8_t, b: int16x8_t) -> uint8x16_t {
    let h = vqshrun_n_s16::<N>(b);
    uint8x16_t(core::array::from_fn(|i| if i < 8 { a.0[i] } else { h.0[i - 8] }))
}
/// The NEON intrinsic `vqshrn_n_u16`, emulated.
pub fn vqshrn_n_u16<const N: i32>(a: uint16x8_t) -> uint8x8_t {
    uint8x8_t(core::array::from_fn(|i| (a.0[i] >> N).min(255) as u8))
}
/// The NEON intrinsic `vqshrn_high_n_u16`, emulated.
pub fn vqshrn_high_n_u16<const N: i32>(a: uint8x8_t, b: uint16x8_t) -> uint8x16_t {
    let h = vqshrn_n_u16::<N>(b);
    uint8x16_t(core::array::from_fn(|i| if i < 8 { a.0[i] } else { h.0[i - 8] }))
}

/// The NEON vector type `int8x16_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct int8x16_t(pub [i8; 16]);
/// The NEON vector type `int8x8_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(8))]
pub struct int8x8_t(pub [i8; 8]);

/// The NEON intrinsic `vreinterpretq_s8_u8`, emulated.
pub fn vreinterpretq_s8_u8(a: uint8x16_t) -> int8x16_t {
    int8x16_t(a.0.map(|x| x as i8))
}
/// The NEON intrinsic `vreinterpretq_u8_s8`, emulated.
pub fn vreinterpretq_u8_s8(a: int8x16_t) -> uint8x16_t {
    uint8x16_t(a.0.map(|x| x as u8))
}
/// The NEON intrinsic `vmaxq_u8`, emulated.
pub fn vmaxq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::max)
}
/// The NEON intrinsic `vabdq_u8`, emulated.
pub fn vabdq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::abs_diff)
}
/// The NEON intrinsic `vcleq_u8`, emulated.
pub fn vcleq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| if x <= y { 0xff } else { 0 })
}
/// The NEON intrinsic `vqaddq_u8`, emulated.
pub fn vqaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::saturating_add)
}
/// The NEON intrinsic `vbicq_u8`, emulated.
pub fn vbicq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, |x, y| x & !y)
}
/// The NEON intrinsic `vqaddq_s8`, emulated.
pub fn vqaddq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    int8x16_t(core::array::from_fn(|i| a.0[i].saturating_add(b.0[i])))
}
/// The NEON intrinsic `vqsubq_s8`, emulated.
pub fn vqsubq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t {
    int8x16_t(core::array::from_fn(|i| a.0[i].saturating_sub(b.0[i])))
}
/// The NEON intrinsic `vshrq_n_s8`, emulated.
pub fn vshrq_n_s8<const N: i32>(a: int8x16_t) -> int8x16_t {
    int8x16_t(a.0.map(|x| x >> if N >= 8 { 7 } else { N }))
}
/// The NEON intrinsic `vqshrn_n_s16`, emulated.
pub fn vqshrn_n_s16<const N: i32>(a: int16x8_t) -> int8x8_t {
    int8x8_t(core::array::from_fn(|i| (a.0[i] >> N).clamp(-128, 127) as i8))
}
/// The NEON intrinsic `vqshrn_high_n_s16`, emulated.
pub fn vqshrn_high_n_s16<const N: i32>(a: int8x8_t, b: int16x8_t) -> int8x16_t {
    let h = vqshrn_n_s16::<N>(b);
    int8x16_t(core::array::from_fn(|i| if i < 8 { a.0[i] } else { h.0[i - 8] }))
}
/// The NEON intrinsic `vld1_u8`, emulated.
///
/// # Safety
///
/// `p` must be valid for a read of the vector's size.
pub unsafe fn vld1_u8(p: *const u8) -> uint8x8_t {
    core::ptr::read_unaligned(p as *const uint8x8_t)
}
/// The NEON intrinsic `vst1_u8`, emulated.
///
/// # Safety
///
/// `p` must be valid for a write of the vector's size.
pub unsafe fn vst1_u8(p: *mut u8, v: uint8x8_t) {
    core::ptr::write_unaligned(p as *mut uint8x8_t, v)
}
/// The NEON intrinsic `vdup_n_u8`, emulated.
pub fn vdup_n_u8(x: u8) -> uint8x8_t {
    uint8x8_t([x; 8])
}
/// The NEON intrinsic `vcombine_u8`, emulated.
pub fn vcombine_u8(a: uint8x8_t, b: uint8x8_t) -> uint8x16_t {
    uint8x16_t(core::array::from_fn(|i| if i < 8 { a.0[i] } else { b.0[i - 8] }))
}

/// The NEON intrinsic `vcreate_u64`, emulated.
pub fn vcreate_u64(x: u64) -> uint64x1_t {
    uint64x1_t([x])
}
/// The NEON intrinsic `vcombine_u64`, emulated.
pub fn vcombine_u64(a: uint64x1_t, b: uint64x1_t) -> uint64x2_t {
    uint64x2_t([a.0[0], b.0[0]])
}
/// The NEON intrinsic `vgetq_lane_u32`, emulated.
pub fn vgetq_lane_u32<const N: i32>(a: uint32x4_t) -> u32 {
    a.0[N as usize]
}

/// The NEON intrinsic `vmulq_u8`, emulated.
pub fn vmulq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    map(a, b, u8::wrapping_mul)
}
/// The NEON intrinsic `vmulq_u16`, emulated.
pub fn vmulq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].wrapping_mul(b.0[i])))
}
/// The NEON intrinsic `vmulq_u32`, emulated.
pub fn vmulq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| a.0[i].wrapping_mul(b.0[i])))
}
/// The NEON intrinsic `vpaddlq_u8`, emulated.
pub fn vpaddlq_u8(a: uint8x16_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[2 * i] as u16 + a.0[2 * i + 1] as u16))
}
/// The NEON intrinsic `vpaddlq_u16`, emulated.
pub fn vpaddlq_u16(a: uint16x8_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| a.0[2 * i] as u32 + a.0[2 * i + 1] as u32))
}
/// The NEON intrinsic `vpaddlq_u32`, emulated.
pub fn vpaddlq_u32(a: uint32x4_t) -> uint64x2_t {
    uint64x2_t(core::array::from_fn(|i| a.0[2 * i] as u64 + a.0[2 * i + 1] as u64))
}

/// The NEON vector type `int32x4_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct int32x4_t(pub [i32; 4]);
/// The NEON vector type `int16x4_t`, emulated: its lanes, lane 0 first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(8))]
pub struct int16x4_t(pub [i16; 4]);

/// The NEON intrinsic `vreinterpretq_s32_u8`, emulated.
pub fn vreinterpretq_s32_u8(a: uint8x16_t) -> int32x4_t {
    int32x4_t(vreinterpretq_u32_u8(a).0.map(|x| x as i32))
}
/// The NEON intrinsic `vreinterpretq_u8_s32`, emulated.
pub fn vreinterpretq_u8_s32(a: int32x4_t) -> uint8x16_t {
    vreinterpretq_u8_u32(uint32x4_t(a.0.map(|x| x as u32)))
}
/// The NEON intrinsic `vabsq_s16`, emulated.
pub fn vabsq_s16(a: int16x8_t) -> int16x8_t {
    int16x8_t(a.0.map(i16::wrapping_abs))
}
/// The NEON intrinsic `vmaxq_u16`, emulated.
pub fn vmaxq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].max(b.0[i])))
}
/// The NEON intrinsic `vget_low_s16`, emulated.
pub fn vget_low_s16(a: int16x8_t) -> int16x4_t {
    int16x4_t(core::array::from_fn(|i| a.0[i]))
}
/// The NEON intrinsic `vmull_s16`, emulated.
pub fn vmull_s16(a: int16x4_t, b: int16x4_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| a.0[i] as i32 * b.0[i] as i32))
}
/// The NEON intrinsic `vmull_high_s16`, emulated.
pub fn vmull_high_s16(a: int16x8_t, b: int16x8_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| a.0[4 + i] as i32 * b.0[4 + i] as i32))
}
/// The NEON intrinsic `vaddq_u32`, emulated.
pub fn vaddq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| a.0[i].wrapping_add(b.0[i])))
}
/// The NEON intrinsic `vsubq_u32`, emulated.
pub fn vsubq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t(core::array::from_fn(|i| a.0[i].wrapping_sub(b.0[i])))
}
/// The NEON intrinsic `vrshrq_n_s32`, emulated.
pub fn vrshrq_n_s32<const N: i32>(a: int32x4_t) -> int32x4_t {
    int32x4_t(a.0.map(|x| ((x as i64 + (1i64 << (N - 1))) >> N) as i32))
}
/// The NEON intrinsic `vshlq_n_u32`, emulated.
pub fn vshlq_n_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    uint32x4_t(a.0.map(|x| x << N))
}
/// The NEON intrinsic `vuzp2q_u16`, emulated.
pub fn vuzp2q_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| if i < 4 { a.0[2 * i + 1] } else { b.0[2 * i - 7] }))
}

/// The NEON type `uint8x16x3_t`, emulated: three vectors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct uint8x16x3_t(pub uint8x16_t, pub uint8x16_t, pub uint8x16_t);
/// The NEON intrinsic `vst3q_u8`, emulated.
///
/// # Safety
///
/// `p` must be valid for a write of 48 bytes (the three vectors, interleaved).
pub unsafe fn vst3q_u8(p: *mut u8, v: uint8x16x3_t) {
    for k in 0..16 {
        *p.add(3 * k) = v.0 .0[k];
        *p.add(3 * k + 1) = v.1 .0[k];
        *p.add(3 * k + 2) = v.2 .0[k];
    }
}

/// The NEON intrinsic `vmull_laneq_s16`, emulated.
pub fn vmull_laneq_s16<const L: i32>(a: int16x4_t, c: int16x8_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| a.0[i] as i32 * c.0[L as usize] as i32))
}
/// The NEON intrinsic `vmull_high_laneq_s16`, emulated.
pub fn vmull_high_laneq_s16<const L: i32>(a: int16x8_t, c: int16x8_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| a.0[4 + i] as i32 * c.0[L as usize] as i32))
}
/// The NEON intrinsic `vmlal_laneq_s16`, emulated.
pub fn vmlal_laneq_s16<const L: i32>(acc: int32x4_t, a: int16x4_t, c: int16x8_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| acc.0[i].wrapping_add(a.0[i] as i32 * c.0[L as usize] as i32)))
}
/// The NEON intrinsic `vmlal_high_laneq_s16`, emulated.
pub fn vmlal_high_laneq_s16<const L: i32>(acc: int32x4_t, a: int16x8_t, c: int16x8_t) -> int32x4_t {
    int32x4_t(core::array::from_fn(|i| acc.0[i].wrapping_add(a.0[4 + i] as i32 * c.0[L as usize] as i32)))
}
/// The NEON intrinsic `vrshrn_n_s32`, emulated.
pub fn vrshrn_n_s32<const N: i32>(a: int32x4_t) -> int16x4_t {
    int16x4_t(a.0.map(|x| ((x as i64 + (1i64 << (N - 1))) >> N) as i16))
}
/// The NEON intrinsic `vrshrn_high_n_s32`, emulated.
pub fn vrshrn_high_n_s32<const N: i32>(lo: int16x4_t, b: int32x4_t) -> int16x8_t {
    let h = vrshrn_n_s32::<N>(b);
    int16x8_t(core::array::from_fn(|i| if i < 4 { lo.0[i] } else { h.0[i - 4] }))
}
/// The NEON intrinsic `vdup_n_s16`, emulated.
pub fn vdup_n_s16(x: i16) -> int16x4_t {
    int16x4_t([x; 4])
}
/// The NEON intrinsic `vcombine_s16`, emulated.
pub fn vcombine_s16(a: int16x4_t, b: int16x4_t) -> int16x8_t {
    int16x8_t(core::array::from_fn(|i| if i < 4 { a.0[i] } else { b.0[i - 4] }))
}
/// The NEON intrinsic `vqaddq_u16`, emulated.
pub fn vqaddq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    uint16x8_t(core::array::from_fn(|i| a.0[i].saturating_add(b.0[i])))
}
/// The NEON intrinsic `vaddlvq_u16`, emulated.
pub fn vaddlvq_u16(a: uint16x8_t) -> u32 {
    a.0.iter().map(|&x| x as u32).sum()
}
