//! The SIMD128 instructions of `crate::wasm` that the NEON kernels use,
//! proven on x86-64 with SSE.
//!
//! Each function here has the name, signature, `requires` and `ensures` of
//! the function of the same name in `crate::wasm`, and is verified against
//! the trusted x86 intrinsic specifications in `crate::x86` (through their
//! safe wrappers in `crate::arch`). On x86-64, `crate::neon`'s wrappers
//! call `crate::wasm_neon` (proven on `crate::wasm`'s contracts), and
//! these functions of `crate::wasm` call the ones here. So a NEON kernel
//! runs on x86-64 as SSE code whose every step is proven on the strength
//! of the Intel intrinsic specifications, the same ones the crates' own
//! x86 kernels rely on, and of two trusted conversions between the vector
//! types (`m`, `u` below: the same 16 bytes).
//!
//! On x86-64 `neon()` means the CPU has SSE4.1 and SSSE3
//! (`crate::neon::has_neon_sse` checks both), which the axiom
//! `axiom_neon_x86` in `crate::neon` states. Most of these are one
//! instruction. The others:
//!
//! - widening multiplies (`i32x4.extmul_*_i16x8_s`) are `pmaddwd` of the
//!   lanes interleaved with zeros, so each product is added to `0 * 0`;
//! - `i32x4.extadd_pairwise_i16x8_u` is the low and the high 16 bits of
//!   each 32-bit lane, added;
//! - shifts by a run-time count use the count-in-a-register forms
//!   (`psllw`, `psraw`, `pslld`, `psrad`) with the count reduced as
//!   WebAssembly reduces it (modulo the lane width), so they never see a
//!   count past the lane width; a constant count compiles to the
//!   immediate form;
//! - lane splats and the fixed two-input shuffles (`i8x16.shuffle`) are
//!   `pshufb`, one per input, `or`ed: a mask byte of 128 gives 0;
//! - lane rotations and `i8x16.shuffle` by a constant offset are `palignr`.
//!
//! `tools/check_wasm_neon.py` checks that each contract here is, word for
//! word, the one in `crate::wasm`, and that each of those forwards here on
//! x86-64.
#![allow(unused_imports)]
use crate::arch::*;
use crate::cpu::*;
use crate::lanes::*;
#[cfg(verus_only)]
use crate::neon::{n8, neon};
use crate::neon::uint8x16_t;
use crate::ops::*;
#[cfg(verus_only)]
use crate::wasm::shuf;
use vstd::prelude::*;

verus! {

broadcast use {crate::neon::group_neon, crate::lanes::group_lanes};

/// The vector's 16 bytes as an SSE register (TRUSTED: both types are the
/// same 16 bytes; `uint8x16_t` is `crate::emu_neon`'s byte array off
/// AArch64).
#[verifier::external_body]
#[inline(always)]
fn m(v: uint8x16_t) -> (r: __m128i)
    ensures
        b128(r) == n8(v),
{
    unsafe { core::mem::transmute::<uint8x16_t, __m128i>(v) }
}

/// An SSE register's 16 bytes as the vector (TRUSTED, as `m`).
#[verifier::external_body]
#[inline(always)]
fn u(x: __m128i) -> (r: uint8x16_t)
    ensures
        n8(r) == b128(x),
{
    unsafe { core::mem::transmute::<__m128i, uint8x16_t>(x) }
}

/// A 16-bit lane as the `i16` an intrinsic takes.
#[inline(always)]
fn i16_of(x: u16) -> (r: i16)
    ensures
        u16_of_i16(r) == x,
{
    if x < 0x8000 {
        x as i16
    } else {
        (x as i32 - 0x1_0000) as i16
    }
}

/// A 32-bit lane as the `i32` an intrinsic takes.
#[inline(always)]
fn i32_of(x: u32) -> (r: i32)
    ensures
        u32_of_i32(r) == x,
{
    if x < 0x8000_0000 {
        x as i32
    } else {
        (x as i64 - 0x1_0000_0000) as i32
    }
}

/// An `i64` as the `u64` with the same bits.
#[inline(always)]
fn u64_from(x: i64) -> (r: u64)
    ensures
        r == u64_of_i64(x),
{
    if x >= 0 {
        x as u64
    } else {
        (x as i128 + 0x1_0000_0000_0000_0000) as u64
    }
}

/// The `pshufb` mask that picks byte `ix[i]` of the first input, or 0.
pub open spec fn mask_a(ix: Seq<int>) -> Seq<u8> {
    Seq::new(16, |i: int| if ix[i] < 16 { ix[i] as u8 } else { 128u8 })
}

/// The `pshufb` mask that picks byte `ix[i] - 16` of the second input, or 0.
pub open spec fn mask_b(ix: Seq<int>) -> Seq<u8> {
    Seq::new(16, |i: int| if ix[i] >= 16 { (ix[i] - 16) as u8 } else { 128u8 })
}

/// `i8x16.shuffle` by `ix`: one `pshufb` per input, `or`ed.
#[inline(always)]
fn sh2(a: uint8x16_t, b: uint8x16_t, ka: __m128i, kb: __m128i, Ghost(ix): Ghost<Seq<int>>) -> (r: uint8x16_t)
    requires
        neon(),
        ix.len() == 16,
        forall|i: int| 0 <= i < 16 ==> 0 <= #[trigger] ix[i] < 32,
        b128(ka) == mask_a(ix),
        b128(kb) == mask_b(ix),
    ensures
        n8(r) == shuf(n8(a), n8(b), ix),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let x = _mm_shuffle_epi8(m(a), ka);
    let y = _mm_shuffle_epi8(m(b), kb);
    let r = u(_mm_or_si128(x, y));
    proof {
        assert forall|i: int| 0 <= i < 16 implies #[trigger] n8(r)[i] == shuf(n8(a), n8(b), ix)[i] by {
            let (p, q) = (b128(x)[i], b128(y)[i]);
            if ix[i] < 16 {
                assert(q == 0);
                assert(p | 0u8 == p) by (bit_vector);
            } else {
                assert(p == 0);
                assert(0u8 | q == q) by (bit_vector);
            }
        }
        assert(n8(r) =~= shuf(n8(a), n8(b), ix));
    }
    r
}

/// Bytes `o..o + 8` of `a`, widened to 16 bits by interleaving with zeros.
proof fn lemma_zext(a: Seq<u8>, r: Seq<u8>, o: int)
    requires
        a.len() == 16,
        r.len() == 16,
        o == 0 || o == 8,
        forall|j: int| 0 <= j < 16 ==> #[trigger] r[j] == if j % 2 == 0 { a[o + j / 2] } else { 0u8 },
    ensures
        u16s(r) == Seq::new(8, |i: int| a[o + i] as u16),
{
    assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(r)[i] == a[o + i] as u16 by {
        assert(r[2 * i] == a[o + i] && r[2 * i + 1] == 0u8);
        let x = a[o + i];
        assert((x as u16) | ((0u8 as u16) << 8u16) == x as u16) by (bit_vector);
    }
    assert(u16s(r) =~= Seq::new(8, |i: int| a[o + i] as u16));
}

/// The low 16 bits of each 32-bit lane (by an `and` with a byte mask) and
/// the high 16 bits (a shift): the lane's two 16-bit lanes.
proof fn lemma_extadd(a: Seq<u8>, lo: Seq<u8>, hi: Seq<u32>)
    requires
        a.len() == 16,
        lo.len() == 16,
        hi.len() == 4,
        forall|j: int| 0 <= j < 16 ==> #[trigger] lo[j] == if j % 4 < 2 { a[j] } else { 0u8 },
        forall|i: int| 0 <= i < 4 ==> #[trigger] hi[i] == (u32s(a)[i] as nat / pow2_spec(16)) as u32,
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] u32s(lo)[i] as int == u16s(a)[2 * i] as int,
        forall|i: int| 0 <= i < 4 ==> #[trigger] hi[i] as int == u16s(a)[2 * i + 1] as int,
{
    lemma_u16s_of_u32s(a);
    assert(pow2_spec(16) == 0x10000) by {
        reveal_with_fuel(pow2_spec, 17);
    }
    assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(lo)[i] as int == u16s(a)[2 * i] as int by {
        let (b0, b1) = (a[4 * i], a[4 * i + 1]);
        assert(lo[4 * i] == b0 && lo[4 * i + 1] == b1 && lo[4 * i + 2] == 0u8 && lo[4 * i + 3] == 0u8);
        assert(((b0 as u32) | ((b1 as u32) << 8u32) | ((0u8 as u32) << 16u32) | ((0u8 as u32) << 24u32)) == ((b0
            as u16) | ((b1 as u16) << 8u16)) as u32) by (bit_vector);
    }
    assert forall|i: int| 0 <= i < 4 implies #[trigger] hi[i] as int == u16s(a)[2 * i + 1] as int by {
        let w = u32s(a)[i];
        assert(u16s(a)[2 * i] == (w & 0xffff) as u16);
        assert(u16s(a)[2 * i + 1] == (w >> 16u32) as u16);
        assert((w >> 16u32) as u16 as u32 == w / 0x10000u32) by (bit_vector);
        assert(w / 0x10000u32 < 0x10000u32) by (bit_vector);
        assert((w as nat / 0x10000) as u32 == w / 0x10000u32);
    }
}

/// `palignr` of a vector with itself by `4k` bytes rotates its 32-bit lanes by `k`.
proof fn lemma_rot_u32s(a: Seq<u8>, r: Seq<u8>, k: int)
    requires
        a.len() == 16,
        r.len() == 16,
        k == 1 || k == 2,
        r == alignr_lanes(a, a, 4 * k),
    ensures
        forall|i: int| 0 <= i < 4 ==> #[trigger] u32s(r)[i] == u32s(a)[(i + k) % 4],
{
    assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(r)[i] == u32s(a)[(i + k) % 4] by {
        let j = (i + k) % 4;
        assert(r[4 * i] == a[4 * j] && r[4 * i + 1] == a[4 * j + 1] && r[4 * i + 2] == a[4 * j + 2] && r[4 * i + 3]
            == a[4 * j + 3]);
    }
}

/// The even (`p == 0`) or odd (`p == 1`) 16-bit lanes of `a`, then of `b`.
proof fn lemma_pick16(a: Seq<u8>, b: Seq<u8>, r: Seq<u8>, p: int)
    requires
        a.len() == 16,
        b.len() == 16,
        r.len() == 16,
        p == 0 || p == 1,
        forall|j: int| 0 <= j < 16 ==> #[trigger] r[j] == if j < 8 { a[4 * (j / 2) + 2 * p + j % 2] } else { b[4 * ((j - 8) / 2) + 2 * p + j % 2] },
    ensures
        u16s(r) == seq![u16s(a)[p], u16s(a)[2 + p], u16s(a)[4 + p], u16s(a)[6 + p], u16s(b)[p], u16s(b)[2 + p], u16s(b)[4 + p], u16s(b)[6 + p]],
{
    assert(u16s(r) =~= seq![u16s(a)[p], u16s(a)[2 + p], u16s(a)[4 + p], u16s(a)[6 + p], u16s(b)[p], u16s(b)[2 + p], u16s(b)[4 + p], u16s(b)[6 + p]]);
}
