//! Register form: the translation of a checked function's instructions to
//! three-address operations on frame slots.
//!
//! The certificate fixes the operand-stack height at every live position,
//! so every operand-stack slot is at a fixed offset from the frame
//! pointer, just like a local. A register operation names its operands and
//! destinations by those offsets, and one operation can stand for a short
//! run of stack instructions (`local.get a; local.get b; i32.add;
//! local.set c` is one `Bin`). [`ROp`]s are kept per position: `rops[pc]`
//! is the operation for the run that starts at `pc`, so a branch into the
//! middle of a run lands on the operation for the rest of it.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::cert::*;
use crate::interp::*;
use crate::reg_ops::*;
use crate::prims::ROP_SIZE;
#[allow(unused_imports)]
use crate::mach::*;

verus! {

/// A branch's continuation: move `n` slots from `src` down to `dst` (frame
/// offsets), then continue at `pc`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Jmp {
    pub pc: u32,
    pub src: u32,
    pub dst: u32,
    pub n: u32,
}

/// One register operation. Slots are offsets from the frame pointer;
/// `k` is the number of instructions the operation stands for. A value
/// operation writes its result to `d1` and then to `d2` (the same slot
/// unless the run ends in `local.tee`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape {
    /// Runs the instruction at this position as a stack instruction;
    /// `top` is the operand-stack top (as a frame offset) there.
    Op { top: u32 },
    /// `nop`, `block`, `loop`, `end`, `drop`: nothing the machine keeps.
    Skip { k: u32 },
    Copy { src: u32, d1: u32, d2: u32, k: u32 },
    Const { v: u64, d1: u32, d2: u32, k: u32 },
    Un { op: Instr, a: u32, d1: u32, d2: u32, k: u32, x: u32 },
    Bin { op: Instr, a: u32, b: u32, d1: u32, d2: u32, k: u32, x: u32 },
    BinI { op: Instr, a: u32, b: u64, d1: u32, d2: u32, k: u32, x: u32 },
    Load { op: Instr, a: u32, d1: u32, d2: u32, k: u32, x: u32 },
    Store { op: Instr, a: u32, v: u32, k: u32, x: u32 },
    StoreI { op: Instr, a: u32, v: u64, k: u32, x: u32 },
    /// `select`: slot `a` if the low 32 bits of slot `c` are nonzero, else `b`.
    Sel { a: u32, b: u32, c: u32, d1: u32, d2: u32, k: u32, x: u32 },
    /// Branches to `t` if the low 32 bits of `c` are nonzero, else
    /// continues `k` instructions on.
    BrIf { c: u32, t: Jmp, k: u32 },
    /// `i32.eqz; br_if`: branches if they are zero.
    BrIfZ { c: u32, t: Jmp, k: u32 },
    /// A comparison followed by `br_if`.
    BrIfBin { op: Instr, a: u32, b: u32, t: Jmp, k: u32, x: u32 },
    BrIfBinI { op: Instr, a: u32, b: u64, t: Jmp, k: u32, x: u32 },
    Br { t: Jmp, k: u32 },
}

/// A register operation as the interpreter runs it: its [`OpCode`] and
/// fields (whose use depends on the code; see `lower`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ROp {
    pub imm: u64,
    pub a: u32,
    pub b: u32,
    pub d1: u32,
    pub d2: u32,
    pub k: u32,
    pub x: u32,
    /// The position of the run's first instruction.
    pub pc: u32,
    pub op: OpCode,
    /// The pre-copy (for the `P_` codes): slot `pa` to slot `pd`.
    pub pa: u32,
    pub pd: u32,
}

fn rop(op: OpCode, a: u32, b: u32, d1: u32, d2: u32, k: u32, x: u32, imm: u64) -> (r: ROp)
{
    ROp { imm, a, b, d1, d2, k, x, pc: 0, op, pa: 0, pd: 0 }
}

/// The ops whose `d1` is a branch target.
fn has_target(op: OpCode) -> (r: bool)
{
    match op {
        OpCode::BrIf | OpCode::BrIfZ | OpCode::A_BrIf | OpCode::A_BrIfZ | OpCode::Br | OpCode::BrIfRRG | OpCode::BrIfRIG => true,
        _ => is_brif_cmp(op),
    }
}

fn mem_off(i: Instr) -> (r: u32)
{
    match i {
        Instr::I32Load(o) | Instr::I64Load(o) | Instr::F32Load(o) | Instr::F64Load(o) |
        Instr::I32Load8S(o) | Instr::I32Load8U(o) | Instr::I32Load16S(o) | Instr::I32Load16U(o) |
        Instr::I64Load8S(o) | Instr::I64Load8U(o) | Instr::I64Load16S(o) | Instr::I64Load16U(o) |
        Instr::I64Load32S(o) | Instr::I64Load32U(o) | Instr::I32Store(o) | Instr::I64Store(o) |
        Instr::F32Store(o) | Instr::F64Store(o) | Instr::I32Store8(o) | Instr::I32Store16(o) |
        Instr::I64Store8(o) | Instr::I64Store16(o) | Instr::I64Store32(o) => o,
        _ => 0,
    }
}

/// The interpreter's form of a shape (`None` for one it runs as a stack
/// instruction: branches that move values).
fn lower(s: Shape) -> (r: Option<ROp>)
{
    match s {
        Shape::Op { top } => Some(rop(OpCode::Op, top, 0, 0, 0, 1, 0, 0)),
        Shape::Skip { k } => Some(rop(OpCode::Skip, 0, 0, 0, 0, k, 0, 0)),
        Shape::Copy { src, d1, d2, k } => Some(rop(OpCode::Copy, src, 0, d1, d2, k, 0, 0)),
        Shape::Const { v, d1, d2, k } => Some(rop(OpCode::Const, 0, 0, d1, d2, k, 0, v)),
        Shape::Un { op, a, d1, d2, k, x } => Some(rop(lower_un(op), a, 0, d1, d2, k, x, 0)),
        Shape::Bin { op, a, b, d1, d2, k, x } => Some(rop(lower_bin_rr(op), a, b, d1, d2, k, x, 0)),
        Shape::BinI { op, a, b, d1, d2, k, x } => Some(rop(lower_bin_ri(op), a, 0, d1, d2, k, x, b)),
        Shape::Load { op, a, d1, d2, k, x } => Some(rop(lower_load(op), a, 0, d1, d2, k, x, mem_off(op) as u64)),
        Shape::Store { op, a, v, k, x } => Some(rop(lower_store_rr(op), a, v, mem_off(op), 0, k, x, 0)),
        Shape::StoreI { op, a, v, k, x } => Some(rop(lower_store_ri(op), a, 0, mem_off(op), 0, k, x, v)),
        Shape::Sel { a, b, c, d1, d2, k, x } => Some(rop(OpCode::Sel, a, b, d1, d2, k, x, c as u64)),
        Shape::BrIf { c, t, k } => if t.n == 0 { Some(rop(OpCode::BrIf, c, 0, t.pc, 0, k, 0, 0)) } else { None },
        Shape::BrIfZ { c, t, k } => if t.n == 0 { Some(rop(OpCode::BrIfZ, c, 0, t.pc, 0, k, 0, 0)) } else { None },
        Shape::BrIfBin { op, a, b, t, k, x } => if t.n == 0 {
            Some(rop(lower_brif_rr(op), a, b, t.pc, 0, k, x, 0))
        } else { None },
        Shape::BrIfBinI { op, a, b, t, k, x } => if t.n == 0 {
            Some(rop(lower_brif_ri(op), a, 0, t.pc, 0, k, x, b))
        } else { None },
        Shape::Br { t, k } => if t.n == 0 { Some(rop(OpCode::Br, 0, 0, t.pc, 0, k, 0, 0)) } else { None },
    }
}

#[inline(always)]
pub fn is_noop_x(i: Instr) -> (r: bool)
    ensures r == is_noop(i),
{
    match i {
        Instr::Nop | Instr::Block { .. } | Instr::Loop { .. } | Instr::End => true,
        _ => false,
    }
}

/// An operand: a frame slot or an immediate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Src {
    R(u32),
    I(u64),
}

/// What `i` pushes, if it only pushes a local or a constant.
#[inline(always)]
fn producer(i: Instr, nl: u32) -> (r: Option<Src>)
{
    match i {
        Instr::LocalGet(x) => if x < nl { Some(Src::R(x)) } else { None },
        Instr::I32Const(v) => Some(Src::I(v as u64)),
        Instr::I64Const(v) => Some(Src::I(v)),
        Instr::F32Const(v) => Some(Src::I(v as u64)),
        Instr::F64Const(v) => Some(Src::I(v)),
        _ => None,
    }
}

#[inline(always)]
pub fn is_unop_x(i: Instr) -> (r: bool)
    ensures r == is_unop(i),
{
    match i {
        Instr::I32Eqz | Instr::I32Clz | Instr::I32Ctz | Instr::I32Popcnt | Instr::I64Eqz |
        Instr::I64Clz | Instr::I64Ctz | Instr::I64Popcnt | Instr::I32WrapI64 | Instr::I64ExtendI32S |
        Instr::I64ExtendI32U | Instr::I32Extend8S | Instr::I32Extend16S | Instr::I64Extend8S |
        Instr::I64Extend16S | Instr::I64Extend32S | Instr::FUn(_) | Instr::Cvt(_) => true,
        _ => false,
    }
}

#[inline(always)]
pub fn is_binop_x(i: Instr) -> (r: bool)
    ensures r == is_binop(i),
{
    match i {
        Instr::I32Eq | Instr::I32Ne | Instr::I32LtS | Instr::I32LtU | Instr::I32GtS | Instr::I32GtU |
        Instr::I32LeS | Instr::I32LeU | Instr::I32GeS | Instr::I32GeU | Instr::I32Add | Instr::I32Sub |
        Instr::I32Mul | Instr::I32DivS | Instr::I32DivU | Instr::I32RemS | Instr::I32RemU |
        Instr::I32And | Instr::I32Or | Instr::I32Xor | Instr::I32Shl | Instr::I32ShrS | Instr::I32ShrU |
        Instr::I32Rotl | Instr::I32Rotr | Instr::I64Eq | Instr::I64Ne | Instr::I64LtS | Instr::I64LtU |
        Instr::I64GtS | Instr::I64GtU | Instr::I64LeS | Instr::I64LeU | Instr::I64GeS | Instr::I64GeU |
        Instr::I64Add | Instr::I64Sub | Instr::I64Mul | Instr::I64DivS | Instr::I64DivU |
        Instr::I64RemS | Instr::I64RemU | Instr::I64And | Instr::I64Or | Instr::I64Xor | Instr::I64Shl |
        Instr::I64ShrS | Instr::I64ShrU | Instr::I64Rotl | Instr::I64Rotr | Instr::FBin(_) |
        Instr::FCmp(_) => true,
        _ => false,
    }
}

/// Comparisons: binary operations that never trap.
pub open spec fn is_cmp(i: Instr) -> bool {
    i is I32Eq || i is I32Ne || i is I32LtS || i is I32LtU || i is I32GtS || i is I32GtU
    || i is I32LeS || i is I32LeU || i is I32GeS || i is I32GeU
    || i is I64Eq || i is I64Ne || i is I64LtS || i is I64LtU || i is I64GtS || i is I64GtU
    || i is I64LeS || i is I64LeU || i is I64GeS || i is I64GeU
}

#[inline(always)]
pub fn is_cmp_x(i: Instr) -> (r: bool)
    ensures r == is_cmp(i),
{
    match i {
        Instr::I32Eq | Instr::I32Ne | Instr::I32LtS | Instr::I32LtU | Instr::I32GtS | Instr::I32GtU |
        Instr::I32LeS | Instr::I32LeU | Instr::I32GeS | Instr::I32GeU | Instr::I64Eq | Instr::I64Ne |
        Instr::I64LtS | Instr::I64LtU | Instr::I64GtS | Instr::I64GtU | Instr::I64LeS | Instr::I64LeU |
        Instr::I64GeS | Instr::I64GeU => true,
        _ => false,
    }
}

#[inline(always)]
pub fn is_load_x(i: Instr) -> (r: bool)
    ensures r == load_kind(i) is Some,
{
    match i {
        Instr::I32Load(_) | Instr::I64Load(_) | Instr::F32Load(_) | Instr::F64Load(_) |
        Instr::I32Load8S(_) | Instr::I32Load8U(_) | Instr::I32Load16S(_) | Instr::I32Load16U(_) |
        Instr::I64Load8S(_) | Instr::I64Load8U(_) | Instr::I64Load16S(_) | Instr::I64Load16U(_) |
        Instr::I64Load32S(_) | Instr::I64Load32U(_) => true,
        _ => false,
    }
}

#[inline(always)]
pub fn is_store_x(i: Instr) -> (r: bool)
    ensures r == store_kind(i) is Some,
{
    match i {
        Instr::I32Store(_) | Instr::I64Store(_) | Instr::F32Store(_) | Instr::F64Store(_) |
        Instr::I32Store8(_) | Instr::I32Store16(_) | Instr::I64Store8(_) | Instr::I64Store16(_) |
        Instr::I64Store32(_) => true,
        _ => false,
    }
}

/// The continuation of the branch at `b`, whose operand stack (after the
/// branch's own operands are popped) has height `h`.
#[verifier::external_body]
fn jmp_at(code: &Code, b: usize, nl: u32, h: u32) -> (r: Option<Jmp>)
    requires b < code.side@.len(),
{
    let t = code.side[b];
    if t.arity > h || t.height > h - t.arity {
        return None;
    }
    let src = h - t.arity;
    if nl as u64 + h as u64 > u32::MAX as u64 {
        return None;
    }
    Some(Jmp { pc: t.pc, src: nl + src, dst: nl + t.height, n: t.arity })
}

/// The destinations of a value computed by the instruction at `c` whose
/// result lands at stack height `rh`: a following `local.set` or
/// `local.tee` is fused. Returns `(d1, d2, instructions fused)`.
#[verifier::external_body]
fn sink(body: &Vec<Instr>, c: usize, nl: u32, rh: u32) -> (r: (u32, u32, u32))
    requires c < body@.len(), nl as nat + rh as nat <= u32::MAX,
{
    let r = nl + rh;
    if c + 1 < body.len() {
        match body[c + 1] {
            Instr::LocalSet(z) => if z < nl { (z, z, 1) } else { (r, r, 0) },
            Instr::LocalTee(z) => if z < nl { (z, r, 1) } else { (r, r, 0) },
            _ => (r, r, 0),
        }
    } else {
        (r, r, 0)
    }
}

/// The register operation for the run starting at live position `pc`
/// (operand-stack height `h`), or `None` for a stack instruction.
#[verifier::external_body]
fn tr_shape(code: &Code, body: &Vec<Instr>, nl: u32, frame: u32, pc: usize, h: u32, lim: usize) -> (r: Option<Shape>)
    requires pc < lim <= body@.len(), body@.len() < NONE, code.side@.len() == body@.len() + 1,
{
    // The run stays below `lim` (the next branch target).
    let len = lim;
    // `nop`, `block`, `loop` and `end` move no values.
    let mut q = pc;
    while q < len && q - pc < 8 && is_noop_x(body[q])
        invariant pc <= q <= len, len == body@.len(),
        decreases len - q,
    {
        q = q + 1;
    }
    let j0 = (q - pc) as u32;
    if q >= len {
        return if j0 > 0 { Some(Shape::Skip { k: j0 }) } else { None };
    }
    // Values in slots: a stack slot `j` is `nl + j`.
    if nl as u64 + h as u64 + 2 > u32::MAX as u64 {
        return if j0 > 0 { Some(Shape::Skip { k: j0 }) } else { None };
    }
    let top = nl + h; // first free slot
    // Up to two pushes of a local or a constant.
    let p0 = producer(body[q], nl);
    let p1 = if p0.is_some() && q + 1 < len { producer(body[q + 1], nl) } else { None };
    let np: usize = if p0.is_none() { 0 } else if p1.is_none() { 1 } else { 2 };
    let c = q + np;
    let skip = if j0 > 0 { Some(Shape::Skip { k: j0 }) } else { None };
    if c >= len {
        return match p0 {
            Some(Src::R(x)) => Some(Shape::Copy { src: x, d1: top, d2: top, k: j0 + 1 }),
            Some(Src::I(v)) => Some(Shape::Const { v, d1: top, d2: top, k: j0 + 1 }),
            None => skip,
        };
    }
    let i = body[c];
    let xc = (c - pc) as u32;
    let nh = h + np as u32; // stack height before the consumer
    let single = match p0 {
        Some(Src::R(x)) => Some(Shape::Copy { src: x, d1: top, d2: top, k: j0 + 1 }),
        Some(Src::I(v)) => Some(Shape::Const { v, d1: top, d2: top, k: j0 + 1 }),
        None => skip,
    };
    let kc = j0 + np as u32 + 1; // through the consumer
    if is_binop_x(i) && nh >= 2 {
        // Operands: a at height nh - 2, b at nh - 1, from the pushes if
        // they were fused.
        let b = if np >= 1 { if np == 2 { p1 } else { p0 } } else { Some(Src::R(nl + nh - 1)) };
        let a = if np == 2 { p0 } else { Some(Src::R(nl + nh - 2)) };
        let rh = nh - 2;
        // A comparison feeding br_if.
        if is_cmp_x(i) && c + 1 < len {
            if let Instr::BrIf(_) = body[c + 1] {
                if let Some(Src::R(ra)) = a {
                    if let Some(t) = jmp_at(code, c + 1, nl, rh) {
                        match b {
                            Some(Src::R(rb)) => return Some(Shape::BrIfBin { op: i, a: ra, b: rb, t, k: kc + 1, x: xc }),
                            Some(Src::I(v)) => return Some(Shape::BrIfBinI { op: i, a: ra, b: v, t, k: kc + 1, x: xc }),
                            None => {},
                        }
                    }
                }
            }
        }
        let (d1, d2, ks) = sink(body, c, nl, rh);
        return match (a, b) {
            (Some(Src::R(ra)), Some(Src::R(rb))) => Some(Shape::Bin { op: i, a: ra, b: rb, d1, d2, k: kc + ks, x: xc }),
            (Some(Src::R(ra)), Some(Src::I(v))) => Some(Shape::BinI { op: i, a: ra, b: v, d1, d2, k: kc + ks, x: xc }),
            _ => single,
        };
    }
    if is_store_x(i) && np == 2 {
        if let Some(Src::R(ra)) = p0 {
            return match p1 {
                Some(Src::R(x)) => Some(Shape::Store { op: i, a: ra, v: x, k: kc, x: xc }),
                Some(Src::I(v)) => Some(Shape::StoreI { op: i, a: ra, v, k: kc, x: xc }),
                None => single,
            };
        }
        return single;
    }
    if let Instr::Select = i {
        if nh >= 3 {
            // Operand j (at height nh - 3 + j) is a push if j >= 3 - np.
            let ps = [p0, p1];
            let mut o = [0u32; 3];
            let mut j = 0;
            while j < 3 {
                if j + np >= 3 {
                    match ps[j + np - 3] {
                        Some(Src::R(x)) => o[j] = x,
                        _ => return single,
                    }
                } else {
                    o[j] = nl + nh - 3 + j as u32;
                }
                j = j + 1;
            }
            let (d1, d2, ks) = sink(body, c, nl, nh - 3);
            return Some(Shape::Sel { a: o[0], b: o[1], c: o[2], d1, d2, k: kc + ks, x: xc });
        }
        return single;
    }
    if np == 2 {
        // The second push is not consumed here: take the first alone.
        return single;
    }
    let a = match p0 { Some(Src::R(x)) => Some(x), Some(Src::I(_)) => None, None => if nh >= 1 { Some(nl + nh - 1) } else { None } };
    if is_unop_x(i) && nh >= 1 {
        let rh = nh - 1;
        if let Some(ra) = a {
            if let Instr::I32Eqz = i {
                if c + 1 < len {
                    if let Instr::BrIf(_) = body[c + 1] {
                        if let Some(t) = jmp_at(code, c + 1, nl, rh) {
                            return Some(Shape::BrIfZ { c: ra, t, k: kc + 1 });
                        }
                    }
                }
            }
            let (d1, d2, ks) = sink(body, c, nl, rh);
            return Some(Shape::Un { op: i, a: ra, d1, d2, k: kc + ks, x: xc });
        }
        return single;
    }
    if is_load_x(i) && nh >= 1 {
        if let Some(ra) = a {
            let (d1, d2, ks) = sink(body, c, nl, nh - 1);
            return Some(Shape::Load { op: i, a: ra, d1, d2, k: kc + ks, x: xc });
        }
        return single;
    }
    if is_store_x(i) && nh >= 2 {
        // Address at nh - 2 (never a fused push here), value at nh - 1.
        if np == 1 {
            return match p0 {
                Some(Src::R(x)) => Some(Shape::Store { op: i, a: nl + nh - 2, v: x, k: kc, x: xc }),
                Some(Src::I(v)) => Some(Shape::StoreI { op: i, a: nl + nh - 2, v, k: kc, x: xc }),
                None => single,
            };
        }
        return Some(Shape::Store { op: i, a: nl + nh - 2, v: nl + nh - 1, k: kc, x: xc });
    }
    match i {
        Instr::LocalSet(z) => if z < nl && nh >= 1 {
            return match p0 {
                Some(Src::R(x)) => Some(Shape::Copy { src: x, d1: z, d2: z, k: kc }),
                Some(Src::I(v)) => Some(Shape::Const { v, d1: z, d2: z, k: kc }),
                None => Some(Shape::Copy { src: nl + nh - 1, d1: z, d2: z, k: kc }),
            };
        },
        Instr::LocalTee(z) => if z < nl && nh >= 1 {
            return match p0 {
                Some(Src::R(x)) => Some(Shape::Copy { src: x, d1: z, d2: nl + nh - 1, k: kc }),
                Some(Src::I(v)) => Some(Shape::Const { v, d1: z, d2: nl + nh - 1, k: kc }),
                None => Some(Shape::Copy { src: nl + nh - 1, d1: z, d2: nl + nh - 1, k: kc }),
            };
        },
        Instr::BrIf(_) => if nh >= 1 {
            if let Some(ra) = a {
                if let Some(t) = jmp_at(code, c, nl, nh - 1) {
                    return Some(Shape::BrIf { c: ra, t, k: kc });
                }
            }
        },
        Instr::Br(_) => if np == 0 {
            if let Some(t) = jmp_at(code, c, nl, nh) {
                return Some(Shape::Br { t, k: kc });
            }
        },
        Instr::Drop => if np == 0 && nh >= 1 {
            return Some(Shape::Skip { k: kc });
        },
        _ => {},
    }
    single
}

/// Every slot `op` names is below `frame`.
fn fits(op: Shape, frame: u32) -> (r: bool)
{
    match op {
        Shape::Op { .. } | Shape::Skip { .. } => true,
        Shape::Copy { src, d1, d2, .. } => src < frame && d1 < frame && d2 < frame,
        Shape::Const { d1, d2, .. } => d1 < frame && d2 < frame,
        Shape::Un { a, d1, d2, .. } | Shape::BinI { a, d1, d2, .. } | Shape::Load { a, d1, d2, .. } =>
            a < frame && d1 < frame && d2 < frame,
        Shape::Bin { a, b, d1, d2, .. } => a < frame && b < frame && d1 < frame && d2 < frame,
        Shape::Store { a, v, .. } => a < frame && v < frame,
        Shape::Sel { a, b, c, d1, d2, .. } => a < frame && b < frame && c < frame && d1 < frame && d2 < frame,
        Shape::StoreI { a, .. } => a < frame,
        Shape::BrIf { c, t, .. } | Shape::BrIfZ { c, t, .. } => c < frame && jmp_fits(t, frame),
        Shape::BrIfBin { a, b, t, .. } => a < frame && b < frame && jmp_fits(t, frame),
        Shape::BrIfBinI { a, t, .. } => a < frame && jmp_fits(t, frame),
        Shape::Br { t, .. } => jmp_fits(t, frame),
    }
}

fn jmp_fits(t: Jmp, frame: u32) -> (r: bool)
{
    t.dst <= t.src && t.src as u64 + t.n as u64 <= frame as u64
}

#[verifier::external_body]
fn tr_run(code: &Code, body: &Vec<Instr>, nl: u32, frame: u32, pc: usize, h: u32, lim: usize) -> (r: Option<Shape>)
    requires pc < lim <= body@.len(), body@.len() < NONE, code.side@.len() == body@.len() + 1,
{
    match tr_shape(code, body, nl, frame, pc, h, lim) {
        Some(op) => if fits(op, frame) { Some(op) } else { None },
        None => None,
    }
}

/// The register form of a compiled function: the operations, in order,
/// for consecutive runs of instructions, and for each position the index
/// of the operation whose run starts there (`NONE` inside a run). Runs
/// start at every branch target, so a branch's continuation is always an
/// operation.
#[verifier::external_body]
pub fn translate(code: &Code, fc: &FuncCert, body: &Vec<Instr>) -> (r: (Vec<ROp>, Vec<u32>))
    requires
        body@.len() < NONE,
        code.side@.len() == body@.len() + 1,
        fc.h@.len() == body@.len() + 1,
{
    let len = body.len();
    let nl = code.n_locals;
    let frame = code.frame;
    // Branch targets: label continuations and the targets of `if`.
    let mut tgt: Vec<bool> = vec![false; len + 1];
    tgt.set(0, true);
    tgt.set(len, true);
    let mut j = 0;
    while j < fc.labels.len() {
        let cont = fc.labels[j].cont as usize;
        if cont <= len { tgt.set(cont, true); }
        j = j + 1;
    }
    let mut p = 0;
    while p < len {
        if let Instr::If { else_, end, .. } = body[p] {
            if (else_ as usize) < len { tgt.set(else_ as usize + 1, true); }
            if (end as usize) <= len { tgt.set(end as usize, true); }
        }
        p = p + 1;
    }
    // The next target at or after each position.
    let mut nxt: Vec<u32> = vec![len as u32; len + 1];
    let mut p = len;
    while p > 0 {
        p = p - 1;
        let n1 = nxt[p + 1];
        nxt.set(p, if tgt[p + 1] { (p + 1) as u32 } else { n1 });
    }
    let mut r: Vec<ROp> = Vec::with_capacity(len + 1);
    let mut entry: Vec<u32> = vec![NONE; len + 1];
    let mut pc = 0;
    while pc < len
        decreases len - pc,
    {
        let h = fc.h[pc];
        let top = if h != NONE && nl as u64 + h as u64 <= u32::MAX as u64 { nl + h } else { 0 };
        let fallback = rop(OpCode::Op, top, 0, 0, 0, 1, 0, 0);
        let mut op = if h == NONE {
            fallback
        } else {
            match tr_run(code, body, nl, frame, pc, h, nxt[pc] as usize) {
                Some(sh) => match lower(sh) { Some(op) => op, None => fallback },
                None => fallback,
            }
        };
        op.pc = pc as u32;
        entry.set(pc, r.len() as u32);
        r.push(op);
        pc = pc + op.k as usize;
    }
    let h = fc.h[len];
    let top = if h != NONE && nl as u64 + h as u64 <= u32::MAX as u64 { nl + h } else { 0 };
    let mut op = rop(OpCode::Op, top, 0, 0, 0, 1, 0, 0);
    op.pc = len as u32;
    entry.set(len, r.len() as u32);
    r.push(op);
    let (r, entry) = fuse_copies(r, body, &tgt, len);
    let mut r = r;
    // An operation whose first operand is the previous operation's result
    // reads it from the accumulator, unless something can jump to it.
    let mut i = 1;
    while i < r.len() {
        let prev = r[i - 1];
        let cur = r[i];
        let wa = matches!(fam_x(prev.op), Fam::Copy | Fam::Const | Fam::Sel | Fam::Un | Fam::BinRR | Fam::BinRI | Fam::Load);
        if wa && !tgt[cur.pc as usize] && (prev.d1 == cur.a || prev.d2 == cur.a) && !has_pre_x(cur.op) {
            if let Some(a) = avar(cur.op) {
                let mut c2 = cur;
                c2.op = a;
                r.set(i, c2);
            }
        }
        i = i + 1;
    }
    // Branch targets as operation indices.
    let mut i = 0;
    while i < r.len() {
        let op = r[i];
        if has_target(op.op) {
            let t = entry[op.d1 as usize];
            let mut op2 = op;
            op2.d1 = t;
            // The target's byte offset, for the dispatch.
            op2.d2 = if t as u64 * ROP_SIZE as u64 <= u32::MAX as u64 { t * ROP_SIZE } else { 0 };
            r.set(i, op2);
        }
        i = i + 1;
    }
    (r, entry)
}

/// Folds a `local.get` that is an operation of its own into the next
/// operation, as that operation's pre-copy, where the next one has a `P_`
/// code and does not start at a branch target.
#[verifier::external_body]
fn fuse_copies(r: Vec<ROp>, body: &Vec<Instr>, tgt: &Vec<bool>, len: usize) -> (Vec<ROp>, Vec<u32>)
{
    let mut out: Vec<ROp> = Vec::with_capacity(r.len());
    let mut i = 0;
    while i < r.len() {
        let c = r[i];
        if c.op == OpCode::Copy && c.k == 1 && c.d1 == c.d2 && i + 1 < r.len()
            && matches!(body[c.pc as usize], Instr::LocalGet(_)) {
            let n = r[i + 1];
            if let Some(p) = crate::reg_ops::pvar(n.op) {
                if !tgt[n.pc as usize] {
                    let mut f = n;
                    f.op = p;
                    f.pa = c.a;
                    f.pd = c.d1;
                    f.pc = c.pc;
                    f.k = n.k + 1;
                    f.x = n.x + 1;
                    out.push(f);
                    i = i + 2;
                    continue;
                }
            }
        }
        out.push(c);
        i = i + 1;
    }
    let mut entry: Vec<u32> = vec![NONE; len + 1];
    let mut j = 0;
    while j < out.len() {
        entry[out[j].pc as usize] = j as u32;
        j = j + 1;
    }
    (out, entry)
}

/// The register form that runs every instruction as a stack instruction:
/// the fallback when [`translate`]'s output is rejected.
#[verifier::external_body]
pub fn trivial(code: &Code, fc: &FuncCert, len: usize) -> (r: (Vec<ROp>, Vec<u32>))
    requires len < NONE, fc.h@.len() == len + 1,
{
    let nl = code.n_locals;
    let mut r: Vec<ROp> = Vec::with_capacity(len + 1);
    let mut entry: Vec<u32> = Vec::with_capacity(len + 1);
    let mut pc = 0;
    while pc <= len
        invariant fc.h@.len() == len + 1, len < NONE,
        decreases len + 1 - pc,
    {
        let h = fc.h[pc];
        let top = if h != NONE && nl as u64 + h as u64 <= u32::MAX as u64 { nl + h } else { 0 };
        let mut op = rop(OpCode::Op, top, 0, 0, 0, 1, 0, 0);
        op.pc = pc as u32;
        entry.push(pc as u32);
        r.push(op);
        pc = pc + 1;
    }
    (r, entry)
}

} // verus!
