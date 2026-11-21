//! Exec evaluation of the numeric instructions, proven equal to
//! [`crate::sem::eval_unop`] and [`crate::sem::eval_binop`].
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::sint;
use crate::fops;

verus! {

#[inline(always)]
fn bu(b: bool) -> (r: u64)
    ensures r == b2u(b),
{
    if b { 1 } else { 0 }
}

proof fn lemma_sext32_is_s32(a: u64)
    ensures sext(a as nat, 32) == s32(lo32(a)),
{
    lemma_pow2_values();
}

#[inline(always)]
pub fn exec_unop(i: Instr, a: u64) -> (r: Result<u64, Trap>)
    requires is_unop(i),
    ensures r == eval_unop(i, a),
{
    let x = lo(a);
    match i {
        Instr::I32Eqz => Ok(bu(x == 0)),
        Instr::I32Clz => Ok(sint::clz32(x) as u64),
        Instr::I32Ctz => Ok(sint::ctz32(x) as u64),
        Instr::I32Popcnt => Ok(sint::popcnt32(x) as u64),
        Instr::I64Eqz => Ok(bu(a == 0)),
        Instr::I64Clz => Ok(sint::clz64(a)),
        Instr::I64Ctz => Ok(sint::ctz64(a)),
        Instr::I64Popcnt => Ok(sint::popcnt64(a)),
        Instr::I32WrapI64 => Ok(x as u64),
        Instr::I64ExtendI32S => {
            proof { lemma_sext32_is_s32(a); }
            Ok(sint::sext64(a, 32))
        },
        Instr::I64ExtendI32U => Ok(x as u64),
        Instr::I32Extend8S => Ok(sint::sext32(x, 8) as u64),
        Instr::I32Extend16S => Ok(sint::sext32(x, 16) as u64),
        Instr::I64Extend8S => Ok(sint::sext64(a, 8)),
        Instr::I64Extend16S => Ok(sint::sext64(a, 16)),
        Instr::I64Extend32S => Ok(sint::sext64(a, 32)),
        Instr::FUn(op) => Ok(fops::exec_un(op, a)),
        Instr::Cvt(op) => fops::exec_cvt(op, a),
        _ => Ok(0),
    }
}

#[inline(always)]
pub fn exec_binop(i: Instr, a: u64, b: u64) -> (r: Result<u64, Trap>)
    requires is_binop(i),
    ensures r == eval_binop(i, a, b),
{
    let x = lo(a);
    let y = lo(b);
    match i {
        Instr::I32Eq => Ok(bu(x == y)),
        Instr::I32Ne => Ok(bu(x != y)),
        Instr::I32LtS => Ok(bu(sint::lt_s32(x, y))),
        Instr::I32LtU => Ok(bu(x < y)),
        Instr::I32GtS => Ok(bu(sint::lt_s32(y, x))),
        Instr::I32GtU => Ok(bu(x > y)),
        Instr::I32LeS => Ok(bu(!sint::lt_s32(y, x))),
        Instr::I32LeU => Ok(bu(x <= y)),
        Instr::I32GeS => Ok(bu(!sint::lt_s32(x, y))),
        Instr::I32GeU => Ok(bu(x >= y)),
        Instr::I32Add => Ok(add32(x, y) as u64),
        Instr::I32Sub => Ok(sub32(x, y) as u64),
        Instr::I32Mul => Ok(mul32(x, y) as u64),
        Instr::I32DivS => if y == 0 {
            Err(Trap::DivByZero)
        } else if x == 0x8000_0000 && y == 0xffff_ffff {
            Err(Trap::IntOverflow)
        } else {
            Ok(sint::div_s32(x, y) as u64)
        },
        Instr::I32DivU => if y == 0 { Err(Trap::DivByZero) } else { Ok((x / y) as u64) },
        Instr::I32RemS => if y == 0 { Err(Trap::DivByZero) } else { Ok(sint::rem_s32(x, y) as u64) },
        Instr::I32RemU => if y == 0 { Err(Trap::DivByZero) } else { Ok((x % y) as u64) },
        Instr::I32And => Ok((x & y) as u64),
        Instr::I32Or => Ok((x | y) as u64),
        Instr::I32Xor => Ok((x ^ y) as u64),
        Instr::I32Shl => Ok(shl32(x, y) as u64),
        Instr::I32ShrS => Ok(shr_s32(x, y) as u64),
        Instr::I32ShrU => Ok(shr_u32(x, y) as u64),
        Instr::I32Rotl => Ok(rotl32(x, y) as u64),
        Instr::I32Rotr => Ok(rotr32(x, y) as u64),
        Instr::I64Eq => Ok(bu(a == b)),
        Instr::I64Ne => Ok(bu(a != b)),
        Instr::I64LtS => Ok(bu(sint::lt_s64(a, b))),
        Instr::I64LtU => Ok(bu(a < b)),
        Instr::I64GtS => Ok(bu(sint::lt_s64(b, a))),
        Instr::I64GtU => Ok(bu(a > b)),
        Instr::I64LeS => Ok(bu(!sint::lt_s64(b, a))),
        Instr::I64LeU => Ok(bu(a <= b)),
        Instr::I64GeS => Ok(bu(!sint::lt_s64(a, b))),
        Instr::I64GeU => Ok(bu(a >= b)),
        Instr::I64Add => Ok(add64(a, b)),
        Instr::I64Sub => Ok(sub64(a, b)),
        Instr::I64Mul => Ok(mul64(a, b)),
        Instr::I64DivS => if b == 0 {
            Err(Trap::DivByZero)
        } else if a == 0x8000_0000_0000_0000 && b == 0xffff_ffff_ffff_ffff {
            Err(Trap::IntOverflow)
        } else {
            Ok(sint::div_s64(a, b))
        },
        Instr::I64DivU => if b == 0 { Err(Trap::DivByZero) } else { Ok(a / b) },
        Instr::I64RemS => if b == 0 { Err(Trap::DivByZero) } else { Ok(sint::rem_s64(a, b)) },
        Instr::I64RemU => if b == 0 { Err(Trap::DivByZero) } else { Ok(a % b) },
        Instr::I64And => Ok(a & b),
        Instr::I64Or => Ok(a | b),
        Instr::I64Xor => Ok(a ^ b),
        Instr::I64Shl => Ok(shl64(a, b)),
        Instr::I64ShrS => Ok(shr_s64(a, b)),
        Instr::I64ShrU => Ok(shr_u64(a, b)),
        Instr::I64Rotl => Ok(rotl64(a, b)),
        Instr::I64Rotr => Ok(rotr64(a, b)),
        Instr::FBin(op) => Ok(fops::exec_bin(op, a, b)),
        Instr::FCmp(op) => Ok(bu(fops::exec_cmp(op, a, b))),
        _ => Ok(0),
    }
}

} // verus!
