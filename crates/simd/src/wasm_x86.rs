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

/// `i16x8.abs`: wrapping, so -32768 stays -32768.
#[inline(always)]
pub fn w_abs16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| if u16s(n8(a))[i] <= 0x8000 { u16s(n8(a))[i] } else { (0x10000 - u16s(n8(a))[i]) as u16 }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_abs_epi16(m(a)))
}

/// `i16x8.add`: modulo 2^16.
#[inline(always)]
pub fn w_add16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((u16s(n8(a))[i] + u16s(n8(b))[i]) % 0x10000) as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_add_epi16(m(a), m(b)))
}

/// `i16x8.sub`: modulo 2^16.
#[inline(always)]
pub fn w_sub16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((u16s(n8(a))[i] - u16s(n8(b))[i] + 0x10000) % 0x10000) as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_sub_epi16(m(a), m(b)))
}

/// `i32x4.add`: modulo 2^32.
#[inline(always)]
pub fn w_add32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((u32s(n8(a))[i] + u32s(n8(b))[i]) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_add_epi32(m(a), m(b)))
}

/// `i32x4.sub`: modulo 2^32.
#[inline(always)]
pub fn w_sub32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((u32s(n8(a))[i] - u32s(n8(b))[i] + 0x1_0000_0000) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_sub_epi32(m(a), m(b)))
}

/// `i16x8.mul`: the low 16 bits of each product.
#[inline(always)]
pub fn w_mul16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((u16s(n8(a))[i] * u16s(n8(b))[i]) % 0x10000) as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_mullo_epi16(m(a), m(b)))
}

/// `i32x4.mul`: the low 32 bits of each product.
#[inline(always)]
pub fn w_mul32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((u32s(n8(a))[i] * u32s(n8(b))[i]) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_mullo_epi32(m(a), m(b)))
}

/// `i16x8.add_sat_u`.
#[inline(always)]
pub fn w_add_sat_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| if u16s(n8(a))[i] + u16s(n8(b))[i] > 0xffff { 0xffffu16 } else { (u16s(n8(a))[i] + u16s(n8(b))[i]) as u16 }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_adds_epu16(m(a), m(b)))
}

/// `i16x8.max_u`.
#[inline(always)]
pub fn w_max_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| if u16s(n8(a))[i] >= u16s(n8(b))[i] { u16s(n8(a))[i] } else { u16s(n8(b))[i] }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_max_epu16(m(a), m(b)))
}

/// `v128.xor`.
#[inline(always)]
pub fn w_xor(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| n8(a)[i] ^ n8(b)[i]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_xor_si128(m(a), m(b)))
}

/// `i8x16.splat`.
#[inline(always)]
pub fn w_splat8(x: u8) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| x),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_set1_epi8(crate::sse2::i8_of(x)));
    proof {
        assert(n8(r) =~= Seq::new(16, |i: int| x));
    }
    r
}

/// `i16x8.splat`.
#[inline(always)]
pub fn w_splat16(x: u16) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| x),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_set1_epi16(i16_of(x)));
    proof {
        assert(u16s(n8(r)) =~= Seq::new(8, |i: int| x));
    }
    r
}

/// `i32x4.splat`.
#[inline(always)]
pub fn w_splat32(x: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| x),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_set1_epi32(i32_of(x)));
    proof {
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| x));
    }
    r
}

/// `i16x8.shuffle` with every lane `L`: 16-bit lane `L` of `a`, eight times.
#[inline(always)]
pub fn w_dup16<const L: i32>(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= L <= 7,
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| u16s(n8(a))[L as int]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let l = (2 * L) as i8;
    let h = (2 * L + 1) as i8;
    let k = _mm_setr_epi8(l, h, l, h, l, h, l, h, l, h, l, h, l, h, l, h);
    let r = u(_mm_shuffle_epi8(m(a), k));
    proof {
        assert forall|i: int| 0 <= i < 8 implies #[trigger] u16s(n8(r))[i] == u16s(n8(a))[L as int] by {
            assert(b128(k)[2 * i] == 2 * L && b128(k)[2 * i + 1] == 2 * L + 1);
        }
        assert(u16s(n8(r)) =~= Seq::new(8, |i: int| u16s(n8(a))[L as int]));
    }
    r
}

/// `i16x8.extend_low_i8x16_u`: bytes 0..8, zero-extended.
#[inline(always)]
pub fn w_extend_lo8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| n8(a)[i] as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_unpacklo_epi8(m(a), _mm_setzero_si128()));
    proof {
        lemma_zext(n8(a), n8(r), 0);
    }
    r
}

/// `i16x8.extend_high_i8x16_u`: bytes 8..16, zero-extended.
#[inline(always)]
pub fn w_extend_hi8(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| n8(a)[8 + i] as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_unpackhi_epi8(m(a), _mm_setzero_si128()));
    proof {
        lemma_zext(n8(a), n8(r), 8);
    }
    r
}

/// `i32x4.extmul_low_i16x8_s`: products of signed 16-bit lanes 0..4.
#[inline(always)]
pub fn w_extmul_lo16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((s16(u16s(n8(a))[i]) * s16(u16s(n8(b))[i])) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let z = _mm_setzero_si128();
    let x = _mm_unpacklo_epi16(m(a), z);
    let y = _mm_unpacklo_epi16(m(b), z);
    let r = u(_mm_madd_epi16(x, y));
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == ((s16(u16s(n8(a))[0 + i]) * s16(u16s(n8(b))[0 + i])) % 0x1_0000_0000) as u32 by {
            assert((2 * i) / 8 == 0 && (2 * i) % 8 == 2 * i && (2 * i + 1) / 8 == 0 && (2 * i + 1) % 8 == 2 * i + 1);
            assert((2 * i) % 2 == 0 && (2 * i + 1) % 2 == 1 && (2 * i) / 2 == i && (2 * i + 1) / 2 == i);
            assert(u16x8(z)[i] == 0u16) by {
                assert(b128(z)[2 * i] == 0u8 && b128(z)[2 * i + 1] == 0u8);
                assert(((0u8 as u16) | ((0u8 as u16) << 8u16)) == 0u16) by (bit_vector);
            }
            assert(u16x8(x)[2 * i] == u16s(n8(a))[0 + i] && u16x8(x)[2 * i + 1] == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[0 + i] && u16x8(y)[2 * i + 1] == 0);
            assert(s16(0u16) == 0);
            assert(s16(u16x8(x)[2 * i + 1]) * s16(u16x8(y)[2 * i + 1]) == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[0 + i] && u16x8(y)[2 * i + 1] == 0);
        }
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| ((s16(u16s(n8(a))[0 + i]) * s16(u16s(n8(b))[0 + i])) % 0x1_0000_0000) as u32));
    }
    r
}

/// `i32x4.extmul_high_i16x8_s`: products of signed 16-bit lanes 4..8.
#[inline(always)]
pub fn w_extmul_hi16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((s16(u16s(n8(a))[4 + i]) * s16(u16s(n8(b))[4 + i])) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let z = _mm_setzero_si128();
    let x = _mm_unpackhi_epi16(m(a), z);
    let y = _mm_unpackhi_epi16(m(b), z);
    let r = u(_mm_madd_epi16(x, y));
    proof {
        assert forall|i: int| 0 <= i < 4 implies #[trigger] u32s(n8(r))[i] == ((s16(u16s(n8(a))[4 + i]) * s16(u16s(n8(b))[4 + i])) % 0x1_0000_0000) as u32 by {
            assert((2 * i) / 8 == 0 && (2 * i) % 8 == 2 * i && (2 * i + 1) / 8 == 0 && (2 * i + 1) % 8 == 2 * i + 1);
            assert((2 * i) % 2 == 0 && (2 * i + 1) % 2 == 1 && (2 * i) / 2 == i && (2 * i + 1) / 2 == i);
            assert(u16x8(z)[i] == 0u16) by {
                assert(b128(z)[2 * i] == 0u8 && b128(z)[2 * i + 1] == 0u8);
                assert(((0u8 as u16) | ((0u8 as u16) << 8u16)) == 0u16) by (bit_vector);
            }
            assert(u16x8(x)[2 * i] == u16s(n8(a))[4 + i] && u16x8(x)[2 * i + 1] == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[4 + i] && u16x8(y)[2 * i + 1] == 0);
            assert(s16(0u16) == 0);
            assert(s16(u16x8(x)[2 * i + 1]) * s16(u16x8(y)[2 * i + 1]) == 0);
            assert(u16x8(y)[2 * i] == u16s(n8(b))[4 + i] && u16x8(y)[2 * i + 1] == 0);
        }
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| ((s16(u16s(n8(a))[4 + i]) * s16(u16s(n8(b))[4 + i])) % 0x1_0000_0000) as u32));
    }
    r
}

/// `i32x4.dot_i16x8_s`: products of signed 16-bit lanes, added in adjacent
/// pairs.
#[inline(always)]
pub fn w_dot16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((s16(u16s(n8(a))[2 * i]) * s16(u16s(n8(b))[2 * i]) + s16(u16s(n8(a))[2 * i + 1]) * s16(u16s(n8(b))[2 * i + 1])) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = u(_mm_madd_epi16(m(a), m(b)));
    assert(u32s(n8(r)) =~= Seq::new(4, |i: int| ((s16(u16s(n8(a))[2 * i]) * s16(u16s(n8(b))[2 * i]) + s16(u16s(n8(a))[2 * i + 1]) * s16(u16s(n8(b))[2 * i + 1])) % 0x1_0000_0000) as u32));
    r
}

/// `i32x4.extadd_pairwise_i16x8_u`: sums of adjacent 16-bit pairs.
#[inline(always)]
pub fn w_extadd16(a: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| (u16s(n8(a))[2 * i] + u16s(n8(a))[2 * i + 1]) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let x = m(a);
    let lo = _mm_and_si128(x, _mm_setr_epi8(-1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0));
    let hi = _mm_srli_epi32::<16>(x);
    let r = u(_mm_add_epi32(lo, hi));
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] b128(lo)[j] == if j % 4 < 2 { n8(a)[j] } else { 0u8 } by {
            let c = n8(a)[j];
            assert(c & 255u8 == c) by (bit_vector);
            assert(c & 0u8 == 0u8) by (bit_vector);
        }
        lemma_extadd(n8(a), b128(lo), u32x4(hi));
        assert(u32s(n8(r)) =~= Seq::new(4, |i: int| (u16s(n8(a))[2 * i] + u16s(n8(a))[2 * i + 1]) as u32));
    }
    r
}

/// `i16x8.extract_lane_u 0`.
#[inline(always)]
pub fn w_extract16_0(a: uint8x16_t) -> (r: u16)
    requires
        neon(),
    ensures
        r == u16s(n8(a))[0],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let v = _mm_cvtsi128_si32(m(a));
    let w = crate::sse2::u32_from(v);
    proof {
        lemma_u16s_of_u32s(n8(a));
        assert((w & 0xffff) as u16 == w as u16) by (bit_vector);
    }
    w as u16
}

/// `i32x4.extract_lane 0`.
#[inline(always)]
pub fn w_extract32_0(a: uint8x16_t) -> (r: u32)
    requires
        neon(),
    ensures
        r == u32s(n8(a))[0],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let v = _mm_cvtsi128_si32(m(a));
    crate::sse2::u32_from(v)
}

/// `i64x2.extract_lane L`, for `L` in 0, 1.
#[inline(always)]
pub fn w_extract64<const L: u32>(a: uint8x16_t) -> (r: u64)
    requires
        neon(),
        L < 2,
    ensures
        r == u64s(n8(a))[L as int],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let x = m(a);
    if L == 0 {
        let v = _mm_cvtsi128_si64(x);
        u64_from(v)
    } else {
        let h = _mm_unpackhi_epi64(x, x);
        let v = _mm_cvtsi128_si64(h);
        proof {
            assert(u64x2(h)[0] == u64x2(x)[1]);
        }
        u64_from(v)
    }
}

/// `i8x16.narrow_i16x8_s`: `a`'s then `b`'s signed lanes, clamped to [-128, 127].
#[inline(always)]
pub fn w_narrow_s16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if i < 8 { (sat_s8(s16(u16s(n8(a))[i])) % 256) as u8 } else { (sat_s8(s16(u16s(n8(b))[i - 8])) % 256) as u8 }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_packs_epi16(m(a), m(b)))
}

/// `i8x16.narrow_i16x8_u`: `a`'s then `b`'s signed lanes, clamped to [0, 255].
#[inline(always)]
pub fn w_narrow_u16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == Seq::new(16, |i: int| if i < 8 { sat_u8(s16(u16s(n8(a))[i])) } else { sat_u8(s16(u16s(n8(b))[i - 8])) }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_packus_epi16(m(a), m(b)))
}

/// `i16x8.narrow_i32x4_s`: `a`'s then `b`'s signed lanes, clamped to 16 bits.
#[inline(always)]
pub fn w_narrow_s32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| if i < 4 { (sat_s16(s32(u32s(n8(a))[i])) % 0x10000) as u16 } else { (sat_s16(s32(u32s(n8(b))[i - 4])) % 0x10000) as u16 }),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_packs_epi32(m(a), m(b)))
}

/// Indices 0, 16, 1, 17, ..., 7, 23.
#[inline(always)]
pub fn w_zip_lo8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 16, 1, 17, 2, 18, 3, 19, 4, 20, 5, 21, 6, 22, 7, 23]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpacklo_epi8(m(a), m(b)))
}

/// Indices 8, 24, 9, 25, ..., 15, 31.
#[inline(always)]
pub fn w_zip_hi8(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![8int, 24, 9, 25, 10, 26, 11, 27, 12, 28, 13, 29, 14, 30, 15, 31]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpackhi_epi8(m(a), m(b)))
}

/// 16-bit lanes 0..4 of `a` and `b`, alternating (`i16x8.shuffle` with lanes 0, 8, 1, 9, 2, 10, 3, 11).
#[inline(always)]
pub fn w_zip_lo16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == seq![u16s(n8(a))[0], u16s(n8(b))[0], u16s(n8(a))[1], u16s(n8(b))[1], u16s(n8(a))[2], u16s(n8(b))[2], u16s(n8(a))[3], u16s(n8(b))[3]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpacklo_epi16(m(a), m(b)))
}

/// 16-bit lanes 4..8 of `a` and `b`, alternating (`i16x8.shuffle` with lanes 4, 12, 5, 13, 6, 14, 7, 15).
#[inline(always)]
pub fn w_zip_hi16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == seq![u16s(n8(a))[4], u16s(n8(b))[4], u16s(n8(a))[5], u16s(n8(b))[5], u16s(n8(a))[6], u16s(n8(b))[6], u16s(n8(a))[7], u16s(n8(b))[7]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpackhi_epi16(m(a), m(b)))
}

/// 32-bit lanes 0, 1 of `a` and `b`, alternating (`i32x4.shuffle` with lanes 0, 4, 1, 5).
#[inline(always)]
pub fn w_zip_lo32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == seq![u32s(n8(a))[0], u32s(n8(b))[0], u32s(n8(a))[1], u32s(n8(b))[1]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpacklo_epi32(m(a), m(b)))
}

/// 32-bit lanes 2, 3 of `a` and `b`, alternating (`i32x4.shuffle` with lanes 2, 6, 3, 7).
#[inline(always)]
pub fn w_zip_hi32(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == seq![u32s(n8(a))[2], u32s(n8(b))[2], u32s(n8(a))[3], u32s(n8(b))[3]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpackhi_epi32(m(a), m(b)))
}

/// 64-bit lane 0 of `a`, then of `b` (`i64x2.shuffle` with lanes 0, 2).
#[inline(always)]
pub fn w_zip_lo64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![u64s(n8(a))[0], u64s(n8(b))[0]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpacklo_epi64(m(a), m(b)))
}

/// 64-bit lane 1 of `a`, then of `b` (`i64x2.shuffle` with lanes 1, 3).
#[inline(always)]
pub fn w_zip_hi64(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u64s(n8(r)) == seq![u64s(n8(a))[1], u64s(n8(b))[1]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_unpackhi_epi64(m(a), m(b)))
}

/// The even 16-bit lanes of `a`, then of `b` (`i16x8.shuffle` with lanes 0, 2, 4, 6, 8, 10, 12, 14).
#[inline(always)]
pub fn w_even16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == seq![u16s(n8(a))[0], u16s(n8(a))[2], u16s(n8(a))[4], u16s(n8(a))[6], u16s(n8(b))[0], u16s(n8(b))[2], u16s(n8(b))[4], u16s(n8(b))[6]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = {
    let ka = _mm_setr_epi8(0, 1, 4, 5, 8, 9, 12, 13, -128, -128, -128, -128, -128, -128, -128, -128);
    let kb = _mm_setr_epi8(-128, -128, -128, -128, -128, -128, -128, -128, 0, 1, 4, 5, 8, 9, 12, 13);
    let ghost ix = seq![0int, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
    };
    proof {
        lemma_pick16(n8(a), n8(b), n8(r), 0);
    }
    r
}

/// The odd 16-bit lanes of `a`, then of `b` (`i16x8.shuffle` with lanes 1, 3, 5, 7, 9, 11, 13, 15).
#[inline(always)]
pub fn w_odd16(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == seq![u16s(n8(a))[1], u16s(n8(a))[3], u16s(n8(a))[5], u16s(n8(a))[7], u16s(n8(b))[1], u16s(n8(b))[3], u16s(n8(b))[5], u16s(n8(b))[7]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let r = {
    let ka = _mm_setr_epi8(2, 3, 6, 7, 10, 11, 14, 15, -128, -128, -128, -128, -128, -128, -128, -128);
    let kb = _mm_setr_epi8(-128, -128, -128, -128, -128, -128, -128, -128, 2, 3, 6, 7, 10, 11, 14, 15);
    let ghost ix = seq![2int, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22, 23, 26, 27, 30, 31];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
    };
    proof {
        lemma_pick16(n8(a), n8(b), n8(r), 1);
    }
    r
}

/// `a`'s 32-bit lanes rotated by 1 (`i32x4.shuffle` with lanes 1, 2, 3, 0).
#[inline(always)]
pub fn w_rot32_1(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == seq![u32s(n8(a))[1], u32s(n8(a))[2], u32s(n8(a))[3], u32s(n8(a))[0]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let x = m(a);
    let r = u(_mm_alignr_epi8::<4>(x, x));
    proof {
        lemma_rot_u32s(n8(a), n8(r), 1);
    }
    r
}

/// `a`'s 32-bit lanes rotated by 2 (`i32x4.shuffle` with lanes 2, 3, 0, 1).
#[inline(always)]
pub fn w_rot32_2(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == seq![u32s(n8(a))[2], u32s(n8(a))[3], u32s(n8(a))[0], u32s(n8(a))[1]],
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let x = m(a);
    let r = u(_mm_alignr_epi8::<8>(x, x));
    proof {
        lemma_rot_u32s(n8(a), n8(r), 2);
    }
    r
}

/// `i8x16.shuffle` with indices `N..N + 16`: bytes `N..16` of `a`, then
/// bytes of `b`.
#[inline(always)]
pub fn w_ext<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
        0 <= N <= 15,
    ensures
        n8(r) == shuf(n8(a), n8(b), Seq::new(16, |i: int| i + N)),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    u(_mm_alignr_epi8::<N>(m(b), m(a)))
}

/// `i16x8.shl`: the count modulo 16.
#[inline(always)]
pub fn w_shl16(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((u16s(n8(a))[i] as nat * pow2_spec((n % 16) as nat)) % 0x10000) as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let c = _mm_cvtsi64_si128((n % 16) as i64);
    let r = u(_mm_sll_epi16(m(a), c));
    proof {
        assert(u16s(n8(r)) =~= u16s(n8(r)));
    }
    r
}

/// `i32x4.shl`: the count modulo 32.
#[inline(always)]
pub fn w_shl32(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((u32s(n8(a))[i] as nat * pow2_spec((n % 32) as nat)) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let c = _mm_cvtsi64_si128((n % 32) as i64);
    let r = u(_mm_sll_epi32(m(a), c));
    proof {
        assert(u32s(n8(r)) =~= u32s(n8(r)));
    }
    r
}

/// `i16x8.shr_s`: arithmetic, the count modulo 16.
#[inline(always)]
pub fn w_shr_s16(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u16s(n8(r)) == Seq::new(8, |i: int| ((s16(u16s(n8(a))[i]) / pow2_spec((n % 16) as nat) as int) % 0x10000) as u16),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let c = _mm_cvtsi64_si128((n % 16) as i64);
    let r = u(_mm_sra_epi16(m(a), c));
    proof {
        assert(u16s(n8(r)) =~= u16s(n8(r)));
    }
    r
}

/// `i32x4.shr_s`: arithmetic, the count modulo 32.
#[inline(always)]
pub fn w_shr_s32(a: uint8x16_t, n: u32) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        u32s(n8(r)) == Seq::new(4, |i: int| ((s32(u32s(n8(a))[i]) / pow2_spec((n % 32) as nat) as int) % 0x1_0000_0000) as u32),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let c = _mm_cvtsi64_si128((n % 32) as i64);
    let r = u(_mm_sra_epi32(m(a), c));
    proof {
        assert(u32s(n8(r)) =~= u32s(n8(r)));
    }
    r
}

/// Bytes of `a` and `b` for block 0 of a three-way interleave (`i8x16.shuffle` with indices 0, 16, 0, 1, 17, 0, 2, 18, 0, 3, 19, 0, 4, 20, 0, 5).
#[inline(always)]
pub fn w_st3_ab0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 16, 0, 1, 17, 0, 2, 18, 0, 3, 19, 0, 4, 20, 0, 5]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(0, -128, 0, 1, -128, 0, 2, -128, 0, 3, -128, 0, 4, -128, 0, 5);
    let kb = _mm_setr_epi8(-128, 0, -128, -128, 1, -128, -128, 2, -128, -128, 3, -128, -128, 4, -128, -128);
    let ghost ix = seq![0int, 16, 0, 1, 17, 0, 2, 18, 0, 3, 19, 0, 4, 20, 0, 5];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

/// Bytes of `a` and `b` for block 1 of a three-way interleave (`i8x16.shuffle` with indices 21, 0, 6, 22, 0, 7, 23, 0, 8, 24, 0, 9, 25, 0, 10, 26).
#[inline(always)]
pub fn w_st3_ab1(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![21int, 0, 6, 22, 0, 7, 23, 0, 8, 24, 0, 9, 25, 0, 10, 26]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(-128, 0, 6, -128, 0, 7, -128, 0, 8, -128, 0, 9, -128, 0, 10, -128);
    let kb = _mm_setr_epi8(5, -128, -128, 6, -128, -128, 7, -128, -128, 8, -128, -128, 9, -128, -128, 10);
    let ghost ix = seq![21int, 0, 6, 22, 0, 7, 23, 0, 8, 24, 0, 9, 25, 0, 10, 26];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

/// Bytes of `a` and `b` for block 2 of a three-way interleave (`i8x16.shuffle` with indices 0, 11, 27, 0, 12, 28, 0, 13, 29, 0, 14, 30, 0, 15, 31, 0).
#[inline(always)]
pub fn w_st3_ab2(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 11, 27, 0, 12, 28, 0, 13, 29, 0, 14, 30, 0, 15, 31, 0]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(0, 11, -128, 0, 12, -128, 0, 13, -128, 0, 14, -128, 0, 15, -128, 0);
    let kb = _mm_setr_epi8(-128, -128, 11, -128, -128, 12, -128, -128, 13, -128, -128, 14, -128, -128, 15, -128);
    let ghost ix = seq![0int, 11, 27, 0, 12, 28, 0, 13, 29, 0, 14, 30, 0, 15, 31, 0];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

/// Block 0 of a three-way interleave: those, with `b`'s bytes from `c` (`i8x16.shuffle` with indices 0, 1, 16, 3, 4, 17, 6, 7, 18, 9, 10, 19, 12, 13, 20, 15).
#[inline(always)]
pub fn w_st3_c0(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 1, 16, 3, 4, 17, 6, 7, 18, 9, 10, 19, 12, 13, 20, 15]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(0, 1, -128, 3, 4, -128, 6, 7, -128, 9, 10, -128, 12, 13, -128, 15);
    let kb = _mm_setr_epi8(-128, -128, 0, -128, -128, 1, -128, -128, 2, -128, -128, 3, -128, -128, 4, -128);
    let ghost ix = seq![0int, 1, 16, 3, 4, 17, 6, 7, 18, 9, 10, 19, 12, 13, 20, 15];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

/// Block 1 of a three-way interleave: those, with `b`'s bytes from `c` (`i8x16.shuffle` with indices 0, 21, 2, 3, 22, 5, 6, 23, 8, 9, 24, 11, 12, 25, 14, 15).
#[inline(always)]
pub fn w_st3_c1(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![0int, 21, 2, 3, 22, 5, 6, 23, 8, 9, 24, 11, 12, 25, 14, 15]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(0, -128, 2, 3, -128, 5, 6, -128, 8, 9, -128, 11, 12, -128, 14, 15);
    let kb = _mm_setr_epi8(-128, 5, -128, -128, 6, -128, -128, 7, -128, -128, 8, -128, -128, 9, -128, -128);
    let ghost ix = seq![0int, 21, 2, 3, 22, 5, 6, 23, 8, 9, 24, 11, 12, 25, 14, 15];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

/// Block 2 of a three-way interleave: those, with `b`'s bytes from `c` (`i8x16.shuffle` with indices 26, 1, 2, 27, 4, 5, 28, 7, 8, 29, 10, 11, 30, 13, 14, 31).
#[inline(always)]
pub fn w_st3_c2(a: uint8x16_t, b: uint8x16_t) -> (r: uint8x16_t)
    requires
        neon(),
    ensures
        n8(r) == shuf(n8(a), n8(b), seq![26int, 1, 2, 27, 4, 5, 28, 7, 8, 29, 10, 11, 30, 13, 14, 31]),
{
    proof {
        crate::neon::axiom_neon_x86();
    }
    let ka = _mm_setr_epi8(-128, 1, 2, -128, 4, 5, -128, 7, 8, -128, 10, 11, -128, 13, 14, -128);
    let kb = _mm_setr_epi8(10, -128, -128, 11, -128, -128, 12, -128, -128, 13, -128, -128, 14, -128, -128, 15);
    let ghost ix = seq![26int, 1, 2, 27, 4, 5, 28, 7, 8, 29, 10, 11, 30, 13, 14, 31];
    proof {
        assert(b128(ka) =~= mask_a(ix));
        assert(b128(kb) =~= mask_b(ix));
    }
    sh2(a, b, ka, kb, Ghost(ix))
}

} // verus!

