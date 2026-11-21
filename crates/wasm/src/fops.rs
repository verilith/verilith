//! Floating-point operations (part of the trusted base).
//!
//! The spec leaves every float operation uninterpreted: the proofs only use
//! that each is a function of its operands' bits, so they say nothing about
//! IEEE 754 arithmetic, and isolation does not depend on it. The exec
//! versions below implement §4.3.3 (with NaN results left to the hardware,
//! which the spec allows) and are checked by the official spec tests.
use vstd::prelude::*;
use crate::ast::*;

verus! {

pub uninterp spec fn f_un(op: FUnOp, a: u64) -> u64;

pub uninterp spec fn f_bin(op: FBinOp, a: u64, b: u64) -> u64;

pub uninterp spec fn f_cmp(op: FCmpOp, a: u64, b: u64) -> bool;

/// `Err` for the trapping truncations' invalid conversion or overflow.
pub uninterp spec fn cvt(op: CvtOp, a: u64) -> Result<u64, Trap>;

#[verifier::external_body]
#[inline(always)]
pub fn exec_un(op: FUnOp, a: u64) -> (r: u64)
    ensures r == f_un(op, a),
{
    un(op, a)
}

#[verifier::external_body]
#[inline(always)]
pub fn exec_bin(op: FBinOp, a: u64, b: u64) -> (r: u64)
    ensures r == f_bin(op, a, b),
{
    bin(op, a, b)
}

#[verifier::external_body]
#[inline(always)]
pub fn exec_cmp(op: FCmpOp, a: u64, b: u64) -> (r: bool)
    ensures r == f_cmp(op, a, b),
{
    cmp(op, a, b)
}

#[verifier::external_body]
#[inline(always)]
pub fn exec_cvt(op: CvtOp, a: u64) -> (r: Result<u64, Trap>)
    ensures r == cvt(op, a),
{
    conv(op, a)
}

} // verus!

#[inline(always)]
fn f32_of(a: u64) -> f32 {
    f32::from_bits(a as u32)
}

#[inline(always)]
fn f64_of(a: u64) -> f64 {
    f64::from_bits(a)
}

#[inline(always)]
fn s32(x: f32) -> u64 {
    x.to_bits() as u64
}

#[inline(always)]
fn s64(x: f64) -> u64 {
    x.to_bits()
}

/// Rounding returns a NaN operand unchanged in Rust; Wasm wants it quiet.
fn q32(x: f32) -> u64 {
    if x.is_nan() { (x.to_bits() | 0x0040_0000) as u64 } else { s32(x) }
}

fn q64(x: f64) -> u64 {
    if x.is_nan() { x.to_bits() | 0x0008_0000_0000_0000 } else { s64(x) }
}

fn un(op: FUnOp, a: u64) -> u64 {
    use FUnOp::*;
    let a32 = a as u32;
    match op {
        F32Abs => (a32 & 0x7fff_ffff) as u64,
        F32Neg => (a32 ^ 0x8000_0000) as u64,
        F32Ceil => q32(f32_of(a).ceil()),
        F32Floor => q32(f32_of(a).floor()),
        F32Trunc => q32(f32_of(a).trunc()),
        F32Nearest => q32(f32_of(a).round_ties_even()),
        F32Sqrt => s32(f32_of(a).sqrt()),
        F64Abs => a & 0x7fff_ffff_ffff_ffff,
        F64Neg => a ^ 0x8000_0000_0000_0000,
        F64Ceil => q64(f64_of(a).ceil()),
        F64Floor => q64(f64_of(a).floor()),
        F64Trunc => q64(f64_of(a).trunc()),
        F64Nearest => q64(f64_of(a).round_ties_even()),
        F64Sqrt => s64(f64_of(a).sqrt()),
    }
}

fn min32(x: f32, y: f32) -> f32 {
    if x.is_nan() || y.is_nan() {
        f32::NAN
    } else if x == y {
        f32::from_bits(x.to_bits() | y.to_bits())
    } else if x < y {
        x
    } else {
        y
    }
}

fn max32(x: f32, y: f32) -> f32 {
    if x.is_nan() || y.is_nan() {
        f32::NAN
    } else if x == y {
        f32::from_bits(x.to_bits() & y.to_bits())
    } else if x > y {
        x
    } else {
        y
    }
}

fn min64(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if x == y {
        f64::from_bits(x.to_bits() | y.to_bits())
    } else if x < y {
        x
    } else {
        y
    }
}

fn max64(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        f64::NAN
    } else if x == y {
        f64::from_bits(x.to_bits() & y.to_bits())
    } else if x > y {
        x
    } else {
        y
    }
}

fn bin(op: FBinOp, a: u64, b: u64) -> u64 {
    use FBinOp::*;
    let (x, y) = (f32_of(a), f32_of(b));
    let (p, q) = (f64_of(a), f64_of(b));
    match op {
        F32Add => s32(x + y),
        F32Sub => s32(x - y),
        F32Mul => s32(x * y),
        F32Div => s32(x / y),
        F32Min => s32(min32(x, y)),
        F32Max => s32(max32(x, y)),
        F32Copysign => (((a as u32) & 0x7fff_ffff) | ((b as u32) & 0x8000_0000)) as u64,
        F64Add => s64(p + q),
        F64Sub => s64(p - q),
        F64Mul => s64(p * q),
        F64Div => s64(p / q),
        F64Min => s64(min64(p, q)),
        F64Max => s64(max64(p, q)),
        F64Copysign => (a & 0x7fff_ffff_ffff_ffff) | (b & 0x8000_0000_0000_0000),
    }
}

fn cmp(op: FCmpOp, a: u64, b: u64) -> bool {
    use FCmpOp::*;
    let (x, y) = (f32_of(a), f32_of(b));
    let (p, q) = (f64_of(a), f64_of(b));
    match op {
        F32Eq => x == y,
        F32Ne => x != y,
        F32Lt => x < y,
        F32Gt => x > y,
        F32Le => x <= y,
        F32Ge => x >= y,
        F64Eq => p == q,
        F64Ne => p != q,
        F64Lt => p < q,
        F64Gt => p > q,
        F64Le => p <= q,
        F64Ge => p >= q,
    }
}

/// Truncates toward zero, trapping on NaN or when the result is outside
/// `[lo, hi)` (bounds exactly representable in f64).
fn trunc(x: f64, lo: f64, hi: f64) -> Result<f64, Trap> {
    if x.is_nan() {
        return Err(Trap::InvalidConversion);
    }
    let t = x.trunc();
    if t < lo || t >= hi {
        return Err(Trap::IntOverflow);
    }
    Ok(t)
}

const I32_LO: f64 = -2147483648.0;
const I32_HI: f64 = 2147483648.0;
const U32_HI: f64 = 4294967296.0;
const I64_LO: f64 = -9223372036854775808.0;
const I64_HI: f64 = 9223372036854775808.0;
const U64_HI: f64 = 18446744073709551616.0;

fn conv(op: CvtOp, a: u64) -> Result<u64, Trap> {
    use CvtOp::*;
    let x = f32_of(a);
    let p = f64_of(a);
    // f32 -> f64 is exact, so f32 operands are checked in f64.
    let xf = x as f64;
    Ok(match op {
        I32TruncF32S => trunc(xf, I32_LO, I32_HI)? as i32 as u32 as u64,
        I32TruncF32U => utrunc(xf, U32_HI)? as u32 as u64,
        I32TruncF64S => trunc(p, I32_LO, I32_HI)? as i32 as u32 as u64,
        I32TruncF64U => utrunc(p, U32_HI)? as u32 as u64,
        I64TruncF32S => trunc(xf, I64_LO, I64_HI)? as i64 as u64,
        I64TruncF32U => utrunc(xf, U64_HI)? as u64,
        I64TruncF64S => trunc(p, I64_LO, I64_HI)? as i64 as u64,
        I64TruncF64U => utrunc(p, U64_HI)? as u64,
        F32ConvertI32S => s32(a as u32 as i32 as f32),
        F32ConvertI32U => s32(a as u32 as f32),
        F32ConvertI64S => s32(a as i64 as f32),
        F32ConvertI64U => s32(a as f32),
        F32DemoteF64 => s32(p as f32),
        F64ConvertI32S => s64(a as u32 as i32 as f64),
        F64ConvertI32U => s64(a as u32 as f64),
        F64ConvertI64S => s64(a as i64 as f64),
        F64ConvertI64U => s64(a as f64),
        F64PromoteF32 => s64(xf),
        I32ReinterpretF32 | F32ReinterpretI32 => a & 0xffff_ffff,
        I64ReinterpretF64 | F64ReinterpretI64 => a,
        // `as` saturates and maps NaN to 0, which is the spec's trunc_sat.
        I32TruncSatF32S => x as i32 as u32 as u64,
        I32TruncSatF32U => x as u32 as u64,
        I32TruncSatF64S => p as i32 as u32 as u64,
        I32TruncSatF64U => p as u32 as u64,
        I64TruncSatF32S => x as i64 as u64,
        I64TruncSatF32U => x as u64,
        I64TruncSatF64S => p as i64 as u64,
        I64TruncSatF64U => p as u64,
    })
}

/// Unsigned truncation: the result must lie in `(-1, hi)` before truncating.
fn utrunc(x: f64, hi: f64) -> Result<f64, Trap> {
    if x.is_nan() {
        return Err(Trap::InvalidConversion);
    }
    let t = x.trunc();
    if t <= -1.0 || t >= hi {
        return Err(Trap::IntOverflow);
    }
    Ok(t)
}
