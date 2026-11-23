//! The execution semantics (§4.4) as a small-step machine over the decoded
//! module (the trusted specification of execution).
//!
//! The machine follows the spec's stack machine: each frame has its locals,
//! its operand stack, and a stack of labels, where a label records its
//! arity, its continuation, and the operand-stack height where it was
//! entered (the spec keeps labels on the operand stack itself; keeping
//! them beside it with their heights is the same structure). Structured
//! control uses the matching `end`/`else` positions the decoder resolved.
//!
//! Values are untyped 64-bit slots (see [`crate::num`]). On a validated
//! module every slot holds a value of the type the spec would give it, so
//! this reads exactly as the typed semantics; on an unvalidated module the
//! machine is still defined (or `Stuck`), which is what lets the isolation
//! theorem hold without trusting the validator.
use vstd::prelude::*;
use crate::ast::*;
use crate::num::*;
use crate::fops;

verus! {

pub const PAGE: u64 = 65536;

pub struct Label {
    pub arity: nat,
    /// Where a branch to this label continues: after the `end` of a block
    /// or `if`, at the `loop` instruction itself, or `body.len()` for the
    /// function's own label.
    pub cont: nat,
    /// Operand-stack height below the label's values.
    pub height: nat,
}

pub struct Frame {
    /// Index of the defined function (into `Module::funcs`).
    pub func: nat,
    pub pc: nat,
    pub locals: Seq<u64>,
    pub stack: Seq<u64>,
    pub labels: Seq<Label>,
}

pub struct Store {
    /// The linear memory's bytes (empty if the module has none).
    pub mem: Seq<u8>,
    /// Pages `memory.grow` may reach: the memory's maximum, capped by the
    /// embedder's limit.
    pub mem_max: nat,
    /// Each table's entries: a function index or null.
    pub tables: Seq<Seq<Option<nat>>>,
    pub globals: Seq<u64>,
    /// `data.drop` (and instantiation, for active segments) empties a
    /// data segment.
    pub data_dropped: Seq<bool>,
}

pub struct Config {
    pub store: Store,
    /// Innermost frame last.
    pub frames: Seq<Frame>,
}

pub enum Step {
    Next(Config),
    Trap(Trap, Store),
    /// The outermost frame returned these values.
    Done(Seq<u64>, Store),
    /// A call to imported function `func` with `args`. `cfg` is the state
    /// with the arguments popped and the caller still at the `call`;
    /// [`resume`] continues it with the host's results.
    Host { func: nat, args: Seq<u64>, cfg: Config },
    /// A `memory.grow` within the maximum, which may succeed (`ok`) or
    /// fail (`fail`, pushing -1): the spec (§4.4.7) lets it fail whenever
    /// the host cannot provide the memory. The run's [`HostResp::Grow`]
    /// says which.
    Grow { ok: Config, fail: Config },
    /// No rule applies (never reached from a validated module).
    Stuck,
}

// ---------------------------------------------------------------------------
// Module lookups
// ---------------------------------------------------------------------------

pub open spec fn n_imp(m: &Module) -> nat {
    m.n_imported_funcs as nat
}

/// The type of function index `x` (imported or defined).
pub open spec fn func_type(m: &Module, x: nat) -> &FuncType {
    &m.types@[m.func_types@[x as int] as int]
}

pub open spec fn n_params(t: &FuncType) -> nat {
    t.params@.len()
}

pub open spec fn n_results(t: &FuncType) -> nat {
    t.results@.len()
}

/// Structural equality of function types (§4.2.2 `call_indirect`).
pub open spec fn same_type(a: &FuncType, b: &FuncType) -> bool {
    a.params@ == b.params@ && a.results@ == b.results@
}

/// Parameter and result counts of a block type, if it is well formed.
pub open spec fn bt_arity(m: &Module, bt: BlockType) -> Option<(nat, nat)> {
    match bt {
        BlockType::Empty => Some((0, 0)),
        BlockType::Val(_) => Some((0, 1)),
        BlockType::Type(i) => if (i as nat) < m.types@.len() {
            Some((n_params(&m.types@[i as int]), n_results(&m.types@[i as int])))
        } else {
            None
        },
    }
}

pub open spec fn body(m: &Module, f: Frame) -> Seq<Instr> {
    m.funcs@[f.func as int].body@
}

/// The frame a call to defined function `d` starts with.
pub open spec fn new_frame(m: &Module, d: nat, args: Seq<u64>) -> Frame {
    let fd = &m.funcs@[d as int];
    Frame {
        func: d,
        pc: 0,
        locals: args + Seq::new(fd.locals@.len(), |_i| 0u64),
        stack: Seq::empty(),
        labels: seq![Label {
            arity: n_results(func_type(m, d + n_imp(m))),
            cont: fd.body@.len(),
            height: 0,
        }],
    }
}

// ---------------------------------------------------------------------------
// Frame and stack helpers
// ---------------------------------------------------------------------------

pub open spec fn top(c: Config) -> Frame {
    c.frames.last()
}

pub open spec fn with_top(c: Config, f: Frame) -> Config {
    Config { frames: c.frames.update(c.frames.len() - 1, f), ..c }
}

pub open spec fn next(c: Config, f: Frame) -> Step {
    Step::Next(with_top(c, f))
}

pub open spec fn adv(f: Frame) -> Frame {
    Frame { pc: f.pc + 1, ..f }
}

pub open spec fn push(f: Frame, v: u64) -> Frame {
    Frame { stack: f.stack.push(v), ..f }
}

/// Drops the top `n` values.
pub open spec fn popn(f: Frame, n: nat) -> Frame {
    Frame { stack: f.stack.subrange(0, f.stack.len() - n), ..f }
}

/// The `i`-th value from the top (0 = top).
pub open spec fn peek(f: Frame, i: nat) -> u64 {
    f.stack[f.stack.len() - 1 - i]
}

/// Leaves label `l` (0 = innermost): keeps its `arity` top values, cuts the
/// stack to the label's height, pops `l + 1` labels and continues at
/// `pc`. This is the spec's `br l` (§4.4.8) with the continuation given.
pub open spec fn exit_label(f: Frame, l: nat, pc: nat) -> Option<Frame> {
    if l >= f.labels.len() {
        None
    } else {
        let lab = f.labels[f.labels.len() - 1 - l];
        if f.stack.len() < lab.height + lab.arity {
            None
        } else {
            Some(Frame {
                pc,
                stack: f.stack.subrange(0, lab.height as int)
                    + f.stack.subrange(f.stack.len() - lab.arity, f.stack.len() as int),
                labels: f.labels.subrange(0, f.labels.len() - 1 - l),
                ..f
            })
        }
    }
}

pub open spec fn br(c: Config, f: Frame, l: nat) -> Step {
    if l >= f.labels.len() {
        Step::Stuck
    } else {
        match exit_label(f, l, f.labels[f.labels.len() - 1 - l].cont) {
            Some(g) => next(c, g),
            None => Step::Stuck,
        }
    }
}

// ---------------------------------------------------------------------------
// Memory
// ---------------------------------------------------------------------------

/// The little-endian value of the `n` bytes at `i`.
pub open spec fn le(s: Seq<u8>, i: int, n: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else { s[i] as nat + 256 * le(s, i + 1, (n - 1) as nat) }
}

/// `s` with the `n` bytes at `i` replaced by `v`'s little-endian bytes.
pub open spec fn write_le(s: Seq<u8>, i: int, v: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 { s } else { write_le(s.update(i, (v % 256) as u8), i + 1, v / 256, (n - 1) as nat) }
}

/// Width in bytes, whether to sign-extend, and whether the result is i64,
/// for each load.
pub open spec fn load_kind(i: Instr) -> Option<(nat, bool, bool, u32)> {
    match i {
        Instr::I32Load(o) => Some((4, false, false, o)),
        Instr::I64Load(o) => Some((8, false, true, o)),
        Instr::F32Load(o) => Some((4, false, false, o)),
        Instr::F64Load(o) => Some((8, false, true, o)),
        Instr::I32Load8S(o) => Some((1, true, false, o)),
        Instr::I32Load8U(o) => Some((1, false, false, o)),
        Instr::I32Load16S(o) => Some((2, true, false, o)),
        Instr::I32Load16U(o) => Some((2, false, false, o)),
        Instr::I64Load8S(o) => Some((1, true, true, o)),
        Instr::I64Load8U(o) => Some((1, false, true, o)),
        Instr::I64Load16S(o) => Some((2, true, true, o)),
        Instr::I64Load16U(o) => Some((2, false, true, o)),
        Instr::I64Load32S(o) => Some((4, true, true, o)),
        Instr::I64Load32U(o) => Some((4, false, true, o)),
        _ => None,
    }
}

/// Width in bytes and static offset of each store.
pub open spec fn store_kind(i: Instr) -> Option<(nat, u32)> {
    match i {
        Instr::I32Store(o) => Some((4, o)),
        Instr::I64Store(o) => Some((8, o)),
        Instr::F32Store(o) => Some((4, o)),
        Instr::F64Store(o) => Some((8, o)),
        Instr::I32Store8(o) => Some((1, o)),
        Instr::I32Store16(o) => Some((2, o)),
        Instr::I64Store8(o) => Some((1, o)),
        Instr::I64Store16(o) => Some((2, o)),
        Instr::I64Store32(o) => Some((4, o)),
        _ => None,
    }
}

/// The slot a load produces from the bytes' value `v`.
pub open spec fn load_result(v: nat, n: nat, signed: bool, is64: bool) -> u64 {
    if !signed {
        v as u64
    } else if is64 {
        m64(sext(v, 8 * n))
    } else {
        m32(sext(v, 8 * n)) as u64
    }
}

/// The value a store writes: the low `n` bytes of the slot.
pub open spec fn store_value(v: u64, n: nat) -> nat {
    if n == 8 { v as nat } else { v as nat % pow2(8 * n) as nat }
}

pub open spec fn data_bytes(m: &Module, s: Store, x: nat) -> Seq<u8> {
    if s.data_dropped[x as int] { Seq::empty() } else { m.datas@[x as int].bytes@ }
}

// ---------------------------------------------------------------------------
// Numeric instructions
// ---------------------------------------------------------------------------

pub open spec fn is_unop(i: Instr) -> bool {
    match i {
        Instr::I32Eqz | Instr::I32Clz | Instr::I32Ctz | Instr::I32Popcnt
        | Instr::I64Eqz | Instr::I64Clz | Instr::I64Ctz | Instr::I64Popcnt
        | Instr::I32WrapI64 | Instr::I64ExtendI32S | Instr::I64ExtendI32U
        | Instr::I32Extend8S | Instr::I32Extend16S
        | Instr::I64Extend8S | Instr::I64Extend16S | Instr::I64Extend32S
        | Instr::FUn(_) | Instr::Cvt(_) => true,
        _ => false,
    }
}

pub open spec fn eval_unop(i: Instr, a: u64) -> Result<u64, Trap> {
    let x = lo32(a);
    match i {
        Instr::I32Eqz => Ok(b2u(x == 0)),
        Instr::I32Clz => Ok(clz(x as nat, 32) as u64),
        Instr::I32Ctz => Ok(ctz(x as nat, 32) as u64),
        Instr::I32Popcnt => Ok(popcnt(x as nat) as u64),
        Instr::I64Eqz => Ok(b2u(a == 0)),
        Instr::I64Clz => Ok(clz(a as nat, 64) as u64),
        Instr::I64Ctz => Ok(ctz(a as nat, 64) as u64),
        Instr::I64Popcnt => Ok(popcnt(a as nat) as u64),
        Instr::I32WrapI64 => Ok(x as u64),
        Instr::I64ExtendI32S => Ok(m64(s32(x))),
        Instr::I64ExtendI32U => Ok(x as u64),
        Instr::I32Extend8S => Ok(m32(sext(x as nat, 8)) as u64),
        Instr::I32Extend16S => Ok(m32(sext(x as nat, 16)) as u64),
        Instr::I64Extend8S => Ok(m64(sext(a as nat, 8))),
        Instr::I64Extend16S => Ok(m64(sext(a as nat, 16))),
        Instr::I64Extend32S => Ok(m64(sext(a as nat, 32))),
        Instr::FUn(op) => Ok(fops::f_un(op, a)),
        Instr::Cvt(op) => fops::cvt(op, a),
        _ => Ok(0),
    }
}

pub open spec fn is_binop(i: Instr) -> bool {
    match i {
        Instr::I32Eq | Instr::I32Ne | Instr::I32LtS | Instr::I32LtU | Instr::I32GtS
        | Instr::I32GtU | Instr::I32LeS | Instr::I32LeU | Instr::I32GeS | Instr::I32GeU
        | Instr::I32Add | Instr::I32Sub | Instr::I32Mul | Instr::I32DivS | Instr::I32DivU
        | Instr::I32RemS | Instr::I32RemU | Instr::I32And | Instr::I32Or | Instr::I32Xor
        | Instr::I32Shl | Instr::I32ShrS | Instr::I32ShrU | Instr::I32Rotl | Instr::I32Rotr
        | Instr::I64Eq | Instr::I64Ne | Instr::I64LtS | Instr::I64LtU | Instr::I64GtS
        | Instr::I64GtU | Instr::I64LeS | Instr::I64LeU | Instr::I64GeS | Instr::I64GeU
        | Instr::I64Add | Instr::I64Sub | Instr::I64Mul | Instr::I64DivS | Instr::I64DivU
        | Instr::I64RemS | Instr::I64RemU | Instr::I64And | Instr::I64Or | Instr::I64Xor
        | Instr::I64Shl | Instr::I64ShrS | Instr::I64ShrU | Instr::I64Rotl | Instr::I64Rotr
        | Instr::FBin(_) | Instr::FCmp(_) => true,
        _ => false,
    }
}

/// `a` is the deeper operand (`i_1` in the spec), `b` the top (`i_2`).
pub open spec fn eval_binop(i: Instr, a: u64, b: u64) -> Result<u64, Trap> {
    let (x, y) = (lo32(a), lo32(b));
    match i {
        Instr::I32Eq => Ok(b2u(x == y)),
        Instr::I32Ne => Ok(b2u(x != y)),
        Instr::I32LtS => Ok(b2u(s32(x) < s32(y))),
        Instr::I32LtU => Ok(b2u(x < y)),
        Instr::I32GtS => Ok(b2u(s32(x) > s32(y))),
        Instr::I32GtU => Ok(b2u(x > y)),
        Instr::I32LeS => Ok(b2u(s32(x) <= s32(y))),
        Instr::I32LeU => Ok(b2u(x <= y)),
        Instr::I32GeS => Ok(b2u(s32(x) >= s32(y))),
        Instr::I32GeU => Ok(b2u(x >= y)),
        Instr::I32Add => Ok(m32(x + y) as u64),
        Instr::I32Sub => Ok(m32(x - y) as u64),
        Instr::I32Mul => Ok(m32(x * y) as u64),
        Instr::I32DivS => if y == 0 {
            Err(Trap::DivByZero)
        } else if x == 0x8000_0000 && y == 0xffff_ffff {
            Err(Trap::IntOverflow)
        } else {
            Ok(m32(tdiv(s32(x), s32(y))) as u64)
        },
        Instr::I32DivU => if y == 0 { Err(Trap::DivByZero) } else { Ok((x / y) as u64) },
        Instr::I32RemS => if y == 0 {
            Err(Trap::DivByZero)
        } else {
            Ok(m32(trem(s32(x), s32(y))) as u64)
        },
        Instr::I32RemU => if y == 0 { Err(Trap::DivByZero) } else { Ok((x % y) as u64) },
        Instr::I32And => Ok((x & y) as u64),
        Instr::I32Or => Ok((x | y) as u64),
        Instr::I32Xor => Ok((x ^ y) as u64),
        Instr::I32Shl => Ok(i32_shl(x, y) as u64),
        Instr::I32ShrS => Ok(i32_shr_s(x, y) as u64),
        Instr::I32ShrU => Ok(i32_shr_u(x, y) as u64),
        Instr::I32Rotl => Ok(i32_rotl(x, y) as u64),
        Instr::I32Rotr => Ok(i32_rotr(x, y) as u64),
        Instr::I64Eq => Ok(b2u(a == b)),
        Instr::I64Ne => Ok(b2u(a != b)),
        Instr::I64LtS => Ok(b2u(s64(a) < s64(b))),
        Instr::I64LtU => Ok(b2u(a < b)),
        Instr::I64GtS => Ok(b2u(s64(a) > s64(b))),
        Instr::I64GtU => Ok(b2u(a > b)),
        Instr::I64LeS => Ok(b2u(s64(a) <= s64(b))),
        Instr::I64LeU => Ok(b2u(a <= b)),
        Instr::I64GeS => Ok(b2u(s64(a) >= s64(b))),
        Instr::I64GeU => Ok(b2u(a >= b)),
        Instr::I64Add => Ok(m64(a + b)),
        Instr::I64Sub => Ok(m64(a - b)),
        Instr::I64Mul => Ok(m64(a * b)),
        Instr::I64DivS => if b == 0 {
            Err(Trap::DivByZero)
        } else if a == 0x8000_0000_0000_0000 && b == 0xffff_ffff_ffff_ffff {
            Err(Trap::IntOverflow)
        } else {
            Ok(m64(tdiv(s64(a), s64(b))))
        },
        Instr::I64DivU => if b == 0 { Err(Trap::DivByZero) } else { Ok(a / b) },
        Instr::I64RemS => if b == 0 { Err(Trap::DivByZero) } else { Ok(m64(trem(s64(a), s64(b)))) },
        Instr::I64RemU => if b == 0 { Err(Trap::DivByZero) } else { Ok(a % b) },
        Instr::I64And => Ok(a & b),
        Instr::I64Or => Ok(a | b),
        Instr::I64Xor => Ok(a ^ b),
        Instr::I64Shl => Ok(i64_shl(a, b)),
        Instr::I64ShrS => Ok(i64_shr_s(a, b)),
        Instr::I64ShrU => Ok(i64_shr_u(a, b)),
        Instr::I64Rotl => Ok(i64_rotl(a, b)),
        Instr::I64Rotr => Ok(i64_rotr(a, b)),
        Instr::FBin(op) => Ok(fops::f_bin(op, a, b)),
        Instr::FCmp(op) => Ok(b2u(fops::f_cmp(op, a, b))),
        _ => Ok(0),
    }
}

// ---------------------------------------------------------------------------
// One step
// ---------------------------------------------------------------------------

/// Calls function index `x` with the top values of `f` as arguments.
pub open spec fn call(m: &Module, c: Config, f: Frame, x: nat) -> Step {
    let t = func_type(m, x);
    let n = n_params(t);
    if f.stack.len() < n {
        Step::Stuck
    } else {
        let args = f.stack.subrange(f.stack.len() - n, f.stack.len() as int);
        let caller = popn(f, n);
        if x < n_imp(m) {
            Step::Host { func: x, args, cfg: with_top(c, caller) }
        } else {
            Step::Next(Config {
                frames: c.frames.update(c.frames.len() - 1, caller).push(
                    new_frame(m, (x - n_imp(m)) as nat, args),
                ),
                ..c
            })
        }
    }
}

/// Continues after a host call returned `results` (and possibly changed
/// the store to `s`).
pub open spec fn resume(c: Config, s: Store, results: Seq<u64>) -> Config {
    let f = top(c);
    with_top(Config { store: s, ..c }, Frame { pc: f.pc + 1, stack: f.stack + results, ..f })
}

/// The top frame ran past its last instruction: return its results.
pub open spec fn ret(m: &Module, c: Config, f: Frame) -> Step {
    let k = n_results(func_type(m, f.func + n_imp(m)));
    if f.stack.len() < k {
        Step::Stuck
    } else {
        let res = f.stack.subrange(f.stack.len() - k, f.stack.len() as int);
        if c.frames.len() == 1 {
            Step::Done(res, c.store)
        } else {
            let caller = c.frames[c.frames.len() - 2];
            Step::Next(Config {
                frames: c.frames.subrange(0, c.frames.len() - 1).update(
                    c.frames.len() - 2,
                    Frame { pc: caller.pc + 1, stack: caller.stack + res, ..caller },
                ),
                ..c
            })
        }
    }
}

pub open spec fn step(m: &Module, c: Config) -> Step {
    if c.frames.len() == 0 {
        Step::Stuck
    } else {
        let f = top(c);
        let s = c.store;
        if f.func >= m.funcs@.len() || f.pc > body(m, f).len() {
            Step::Stuck
        } else if f.pc == body(m, f).len() {
            ret(m, c, f)
        } else {
            step_instr(m, c, f, body(m, f)[f.pc as int])
        }
    }
}

#[verifier::opaque]
pub open spec fn step_instr(m: &Module, c: Config, f: Frame, i: Instr) -> Step {
    let s = c.store;
    let h = f.stack.len();
    if is_unop(i) {
        if h < 1 {
            Step::Stuck
        } else {
            match eval_unop(i, peek(f, 0)) {
                Ok(r) => next(c, adv(push(popn(f, 1), r))),
                Err(t) => Step::Trap(t, s),
            }
        }
    } else if is_binop(i) {
        if h < 2 {
            Step::Stuck
        } else {
            match eval_binop(i, peek(f, 1), peek(f, 0)) {
                Ok(r) => next(c, adv(push(popn(f, 2), r))),
                Err(t) => Step::Trap(t, s),
            }
        }
    } else if load_kind(i) is Some {
        let (n, signed, is64, off) = load_kind(i)->Some_0;
        if h < 1 {
            Step::Stuck
        } else {
            let ea = lo32(peek(f, 0)) as nat + off as nat;
            if ea + n > s.mem.len() {
                Step::Trap(Trap::MemoryOutOfBounds, s)
            } else {
                next(c, adv(push(popn(f, 1), load_result(le(s.mem, ea as int, n), n, signed, is64))))
            }
        }
    } else if store_kind(i) is Some {
        let (n, off) = store_kind(i)->Some_0;
        if h < 2 {
            Step::Stuck
        } else {
            let ea = lo32(peek(f, 1)) as nat + off as nat;
            if ea + n > s.mem.len() {
                Step::Trap(Trap::MemoryOutOfBounds, s)
            } else {
                Step::Next(with_top(
                    Config {
                        store: Store { mem: write_le(s.mem, ea as int, store_value(peek(f, 0), n), n), ..s },
                        ..c
                    },
                    adv(popn(f, 2)),
                ))
            }
        }
    } else {
        match i {
            Instr::Unreachable => Step::Trap(Trap::Unreachable, s),
            Instr::Nop => next(c, adv(f)),
            Instr::Block { bt, end } => match bt_arity(m, bt) {
                Some((np, nr)) => if h < np {
                    Step::Stuck
                } else {
                    next(c, Frame {
                        pc: f.pc + 1,
                        labels: f.labels.push(Label { arity: nr, cont: (end + 1) as nat, height: (h - np) as nat }),
                        ..f
                    })
                },
                None => Step::Stuck,
            },
            Instr::Loop { bt } => match bt_arity(m, bt) {
                Some((np, nr)) => if h < np {
                    Step::Stuck
                } else {
                    next(c, Frame {
                        pc: f.pc + 1,
                        labels: f.labels.push(Label { arity: np, cont: f.pc, height: (h - np) as nat }),
                        ..f
                    })
                },
                None => Step::Stuck,
            },
            Instr::If { bt, else_, end } => match bt_arity(m, bt) {
                Some((np, nr)) => if h < np + 1 {
                    Step::Stuck
                } else {
                    let g = popn(f, 1);
                    let lab = Label { arity: nr, cont: (end + 1) as nat, height: (h - 1 - np) as nat };
                    let pc = if lo32(peek(f, 0)) != 0 {
                        f.pc + 1
                    } else if else_ == end {
                        end as nat
                    } else {
                        (else_ + 1) as nat
                    };
                    next(c, Frame { pc, labels: g.labels.push(lab), ..g })
                },
                None => Step::Stuck,
            },
            // The end of an `if`'s then-branch leaves its label.
            Instr::Else { end } => br(c, f, 0),
            // Leaves the innermost label without touching the stack
            // (validation has left exactly its results there).
            Instr::End => if f.labels.len() == 0 {
                Step::Stuck
            } else {
                next(c, Frame { pc: f.pc + 1, labels: f.labels.drop_last(), ..f })
            },
            Instr::Br(l) => br(c, f, l as nat),
            Instr::BrIf(l) => if h < 1 {
                Step::Stuck
            } else if lo32(peek(f, 0)) != 0 {
                br(c, popn(f, 1), l as nat)
            } else {
                next(c, adv(popn(f, 1)))
            },
            Instr::BrTable { start, len } => if h < 1 || len == 0
                || start as nat + len as nat > m.br_table@.len() {
                Step::Stuck
            } else {
                let k = lo32(peek(f, 0));
                let j = if k < len - 1 { start + k } else { start + len - 1 };
                br(c, popn(f, 1), m.br_table@[j as int] as nat)
            },
            Instr::Return => if f.labels.len() == 0 {
                Step::Stuck
            } else {
                br(c, f, (f.labels.len() - 1) as nat)
            },
            Instr::Call(x) => if x as nat >= m.func_types@.len()
                || m.func_types@[x as int] as nat >= m.types@.len() {
                Step::Stuck
            } else {
                call(m, c, f, x as nat)
            },
            Instr::CallIndirect { ty, table } => if h < 1 || ty as nat >= m.types@.len()
                || table as nat >= s.tables.len() {
                Step::Stuck
            } else {
                let k = lo32(peek(f, 0)) as nat;
                let tab = s.tables[table as int];
                if k >= tab.len() {
                    Step::Trap(Trap::TableOutOfBounds, s)
                } else {
                    match tab[k as int] {
                        None => Step::Trap(Trap::UninitializedElement, s),
                        Some(x) => if x >= m.func_types@.len()
                            || m.func_types@[x as int] as nat >= m.types@.len() {
                            Step::Stuck
                        } else if !same_type(func_type(m, x), &m.types@[ty as int]) {
                            Step::Trap(Trap::IndirectCallTypeMismatch, s)
                        } else {
                            call(m, c, popn(f, 1), x)
                        },
                    }
                }
            },
            Instr::Drop => if h < 1 { Step::Stuck } else { next(c, adv(popn(f, 1))) },
            Instr::Select => if h < 3 {
                Step::Stuck
            } else {
                let v = if lo32(peek(f, 0)) != 0 { peek(f, 2) } else { peek(f, 1) };
                next(c, adv(push(popn(f, 3), v)))
            },
            Instr::LocalGet(x) => if x as nat >= f.locals.len() {
                Step::Stuck
            } else {
                next(c, adv(push(f, f.locals[x as int])))
            },
            Instr::LocalSet(x) => if x as nat >= f.locals.len() || h < 1 {
                Step::Stuck
            } else {
                next(c, adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..popn(f, 1) }))
            },
            Instr::LocalTee(x) => if x as nat >= f.locals.len() || h < 1 {
                Step::Stuck
            } else {
                next(c, adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..f }))
            },
            Instr::GlobalGet(x) => if x as nat >= s.globals.len() {
                Step::Stuck
            } else {
                next(c, adv(push(f, s.globals[x as int])))
            },
            Instr::GlobalSet(x) => if x as nat >= s.globals.len() || h < 1 {
                Step::Stuck
            } else {
                Step::Next(with_top(
                    Config { store: Store { globals: s.globals.update(x as int, peek(f, 0)), ..s }, ..c },
                    adv(popn(f, 1)),
                ))
            },
            Instr::MemorySize => next(c, adv(push(f, (s.mem.len() / PAGE as nat) as u64))),
            Instr::MemoryGrow => if h < 1 {
                Step::Stuck
            } else {
                let old = s.mem.len() / PAGE as nat;
                let n = lo32(peek(f, 0)) as nat;
                if old + n > s.mem_max {
                    next(c, adv(push(popn(f, 1), 0xffff_ffff)))
                } else {
                    Step::Grow {
                        ok: with_top(
                            Config {
                                store: Store { mem: s.mem + Seq::new(n * PAGE as nat, |_i| 0u8), ..s },
                                ..c
                            },
                            adv(push(popn(f, 1), old as u64)),
                        ),
                        fail: with_top(c, adv(push(popn(f, 1), 0xffff_ffff))),
                    }
                }
            },
            Instr::MemoryFill => if h < 3 {
                Step::Stuck
            } else {
                let (d, v, n) = (lo32(peek(f, 2)) as nat, lo32(peek(f, 1)), lo32(peek(f, 0)) as nat);
                if d + n > s.mem.len() {
                    Step::Trap(Trap::MemoryOutOfBounds, s)
                } else {
                    let mem = s.mem.subrange(0, d as int) + Seq::new(n, |_i| (v % 256) as u8)
                        + s.mem.subrange((d + n) as int, s.mem.len() as int);
                    Step::Next(with_top(Config { store: Store { mem, ..s }, ..c }, adv(popn(f, 3))))
                }
            },
            Instr::MemoryCopy => if h < 3 {
                Step::Stuck
            } else {
                let (d, sr, n) = (lo32(peek(f, 2)) as nat, lo32(peek(f, 1)) as nat, lo32(peek(f, 0)) as nat);
                if sr + n > s.mem.len() || d + n > s.mem.len() {
                    Step::Trap(Trap::MemoryOutOfBounds, s)
                } else {
                    let mem = s.mem.subrange(0, d as int) + s.mem.subrange(sr as int, (sr + n) as int)
                        + s.mem.subrange((d + n) as int, s.mem.len() as int);
                    Step::Next(with_top(Config { store: Store { mem, ..s }, ..c }, adv(popn(f, 3))))
                }
            },
            Instr::MemoryInit(x) => if h < 3 || x as nat >= m.datas@.len() || x as nat >= s.data_dropped.len() {
                Step::Stuck
            } else {
                let (d, sr, n) = (lo32(peek(f, 2)) as nat, lo32(peek(f, 1)) as nat, lo32(peek(f, 0)) as nat);
                let data = data_bytes(m, s, x as nat);
                if sr + n > data.len() || d + n > s.mem.len() {
                    Step::Trap(Trap::MemoryOutOfBounds, s)
                } else {
                    let mem = s.mem.subrange(0, d as int) + data.subrange(sr as int, (sr + n) as int)
                        + s.mem.subrange((d + n) as int, s.mem.len() as int);
                    Step::Next(with_top(Config { store: Store { mem, ..s }, ..c }, adv(popn(f, 3))))
                }
            },
            Instr::DataDrop(x) => if x as nat >= s.data_dropped.len() {
                Step::Stuck
            } else {
                Step::Next(with_top(
                    Config { store: Store { data_dropped: s.data_dropped.update(x as int, true), ..s }, ..c },
                    adv(f),
                ))
            },
            Instr::I32Const(v) => next(c, adv(push(f, v as u64))),
            Instr::I64Const(v) => next(c, adv(push(f, v))),
            Instr::F32Const(v) => next(c, adv(push(f, v as u64))),
            Instr::F64Const(v) => next(c, adv(push(f, v))),
            _ => Step::Stuck,
        }
    }
}

} // verus!

verus! {

/// What a host function did: returned results (possibly after changing
/// the store), or trapped.
pub enum HostResp {
    Ok(Store, Seq<u64>),
    Trap(Store),
    /// Whether a `memory.grow` ([`Step::Grow`]) got its memory.
    Grow(bool),
}

pub enum Outcome {
    Done(Seq<u64>, Store),
    Trap(Trap, Store),
    /// Still running after the given number of steps.
    Running(Config),
    Stuck,
}

/// `n` steps from `c`, taking host calls' responses from `hs` in order;
/// a run still going after `n` steps must have used all of `hs`.
pub open spec fn run(m: &Module, c: Config, hs: Seq<HostResp>, n: nat) -> Outcome
    decreases n,
{
    if n == 0 {
        if hs.len() == 0 { Outcome::Running(c) } else { Outcome::Stuck }
    } else {
        match step(m, c) {
            Step::Next(c2) => run(m, c2, hs, (n - 1) as nat),
            Step::Host { func, args, cfg } => if hs.len() == 0 {
                Outcome::Stuck
            } else {
                match hs[0] {
                    HostResp::Ok(s, res) => run(m, resume(cfg, s, res), hs.drop_first(), (n - 1) as nat),
                    HostResp::Trap(s) => Outcome::Trap(Trap::Host, s),
                    HostResp::Grow(_) => Outcome::Stuck,
                }
            },
            Step::Grow { ok, fail } => if hs.len() == 0 {
                Outcome::Stuck
            } else {
                match hs[0] {
                    HostResp::Grow(b) => run(m, if b { ok } else { fail }, hs.drop_first(), (n - 1) as nat),
                    _ => Outcome::Stuck,
                }
            },
            Step::Trap(t, s) => Outcome::Trap(t, s),
            Step::Done(r, s) => Outcome::Done(r, s),
            Step::Stuck => Outcome::Stuck,
        }
    }
}

/// One more step after a run that is still going.
pub proof fn lemma_run_step(m: &Module, c0: Config, hs: Seq<HostResp>, n: nat, c: Config)
    requires run(m, c0, hs, n) == Outcome::Running(c),
    ensures
        match step(m, c) {
            Step::Next(c2) => run(m, c0, hs, n + 1) == Outcome::Running(c2),
            Step::Trap(t, s) => run(m, c0, hs, n + 1) == Outcome::Trap(t, s),
            Step::Done(r, s) => run(m, c0, hs, n + 1) == Outcome::Done(r, s),
            _ => true,
        },
    decreases n,
{
    if n > 0 {
        match step(m, c0) {
            Step::Next(c2) => lemma_run_step(m, c2, hs, (n - 1) as nat, c),
            Step::Host { func, args, cfg } => {
                if let HostResp::Ok(s, res) = hs[0] {
                    lemma_run_step(m, resume(cfg, s, res), hs.drop_first(), (n - 1) as nat, c);
                }
            },
            Step::Grow { ok, fail } => {
                if let HostResp::Grow(b) = hs[0] {
                    lemma_run_step(m, if b { ok } else { fail }, hs.drop_first(), (n - 1) as nat, c);
                }
            },
            _ => {},
        }
    } else {
        reveal_with_fuel(run, 2);
    }
}

/// A host call after a run that is still going.
pub proof fn lemma_run_host(m: &Module, c0: Config, hs: Seq<HostResp>, n: nat, c: Config, r: HostResp)
    requires
        run(m, c0, hs, n) == Outcome::Running(c),
        step(m, c) is Host,
    ensures
        match r {
            HostResp::Ok(s, res) => run(m, c0, hs.push(r), n + 1)
                == Outcome::Running(resume(step(m, c)->cfg, s, res)),
            HostResp::Trap(s) => run(m, c0, hs.push(r), n + 1) == Outcome::Trap(Trap::Host, s),
            HostResp::Grow(_) => true,
        },
    decreases n,
{
    if n > 0 {
        match step(m, c0) {
            Step::Next(c2) => lemma_run_host(m, c2, hs, (n - 1) as nat, c, r),
            Step::Host { func, args, cfg } => {
                if let HostResp::Ok(s, res) = hs[0] {
                    assert(hs.push(r).drop_first() == hs.drop_first().push(r));
                    lemma_run_host(m, resume(cfg, s, res), hs.drop_first(), (n - 1) as nat, c, r);
                }
            },
            Step::Grow { ok, fail } => {
                if let HostResp::Grow(b) = hs[0] {
                    assert(hs.push(r).drop_first() == hs.drop_first().push(r));
                    lemma_run_host(m, if b { ok } else { fail }, hs.drop_first(), (n - 1) as nat, c, r);
                }
            },
            _ => {},
        }
    } else {
        reveal_with_fuel(run, 2);
        assert(hs.push(r) =~= seq![r]);
        assert(seq![r].drop_first() =~= Seq::<HostResp>::empty());
    }
}

/// A `memory.grow` after a run that is still going, with outcome `b`.
pub proof fn lemma_run_grow(m: &Module, c0: Config, hs: Seq<HostResp>, n: nat, c: Config, b: bool)
    requires
        run(m, c0, hs, n) == Outcome::Running(c),
        step(m, c) is Grow,
    ensures
        run(m, c0, hs.push(HostResp::Grow(b)), n + 1)
            == Outcome::Running(if b { step(m, c)->ok } else { step(m, c)->fail }),
    decreases n,
{
    let r = HostResp::Grow(b);
    if n > 0 {
        match step(m, c0) {
            Step::Next(c2) => lemma_run_grow(m, c2, hs, (n - 1) as nat, c, b),
            Step::Host { func, args, cfg } => {
                if let HostResp::Ok(s, res) = hs[0] {
                    assert(hs.push(r).drop_first() == hs.drop_first().push(r));
                    lemma_run_grow(m, resume(cfg, s, res), hs.drop_first(), (n - 1) as nat, c, b);
                }
            },
            Step::Grow { ok, fail } => {
                if let HostResp::Grow(b2) = hs[0] {
                    assert(hs.push(r).drop_first() == hs.drop_first().push(r));
                    lemma_run_grow(m, if b2 { ok } else { fail }, hs.drop_first(), (n - 1) as nat, c, b);
                }
            },
            _ => {},
        }
    } else {
        reveal_with_fuel(run, 2);
        assert(hs.push(r) =~= seq![r]);
        assert(seq![r].drop_first() =~= Seq::<HostResp>::empty());
    }
}

} // verus!
