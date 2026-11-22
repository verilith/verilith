//! Stack-height certificates and their verified checker.
//!
//! For each function the validator produces, for every instruction
//! position, the operand-stack height and the label stack there (or marks
//! the position dead). Label stacks are stored as a tree: each label record
//! points at its enclosing label. The checker here verifies the
//! certificate one instruction at a time; [`func_cert_ok`] is what it
//! proves. With a checked certificate, the machine in [`crate::sem`] never
//! gets stuck and its stack heights and labels at every position are the
//! certificate's (see [`crate::preserve`]), which is what lets the
//! interpreter resolve branches ahead of time and skip runtime stack checks.
//!
//! The validator that builds certificates is not trusted: a wrong
//! certificate is rejected here, so isolation never depends on it.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;

verus! {

/// Marks a dead position (height) or no label (label id).
pub const NONE: u32 = 0xffff_ffff;

/// Largest operand-stack height a function may use.
pub const MAX_HEIGHT: u32 = 0x10_0000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LabelRec {
    pub arity: u32,
    pub cont: u32,
    pub height: u32,
    /// The enclosing label (a smaller id), or `NONE`.
    pub parent: u32,
}

pub struct FuncCert {
    /// Operand-stack height before each instruction, and after the last
    /// (`body.len() + 1` entries); `NONE` where the code is dead.
    pub h: Vec<u32>,
    /// Innermost label before each instruction.
    pub lab: Vec<u32>,
    pub labels: Vec<LabelRec>,
    /// At least every live height.
    pub max_height: u32,
}

pub open spec fn to_label(r: LabelRec) -> Label {
    Label { arity: r.arity as nat, cont: r.cont as nat, height: r.height as nat }
}

/// The label stack whose innermost label is `l` (outermost first).
pub open spec fn chain(ls: Seq<LabelRec>, l: u32) -> Seq<Label>
    decreases l,
{
    if l as nat >= ls.len() {
        Seq::empty()
    } else {
        let r = ls[l as int];
        let pre = if r.parent < l { chain(ls, r.parent) } else { Seq::empty() };
        pre.push(to_label(r))
    }
}

/// The id of the `k`-th label out from `l` (0 is `l`).
pub open spec fn nth_id(ls: Seq<LabelRec>, l: u32, k: nat) -> Option<u32>
    decreases k,
{
    if l as nat >= ls.len() {
        None
    } else if k == 0 {
        Some(l)
    } else {
        let p = ls[l as int].parent;
        if p < l { nth_id(ls, p, (k - 1) as nat) } else { None }
    }
}

pub open spec fn live(fc: FuncCert, pc: int) -> bool {
    0 <= pc < fc.h@.len() && fc.h@[pc] != NONE
}

/// Position `q` is live with height `h` and innermost label `l`.
pub open spec fn at(fc: FuncCert, q: int, h: nat, l: u32) -> bool {
    live(fc, q) && q < fc.lab@.len() && fc.h@[q] as nat == h && fc.lab@[q] == l
}

pub open spec fn hgt(fc: FuncCert, pc: int) -> nat {
    fc.h@[pc] as nat
}

pub open spec fn lab(fc: FuncCert, pc: int) -> u32 {
    fc.lab@[pc]
}

pub open spec fn rec(fc: FuncCert, l: u32) -> LabelRec {
    fc.labels@[l as int]
}

/// Branching to the `k`-th label from position `pc` (with `pops` values
/// popped first) is well formed.
pub open spec fn br_ok(fc: FuncCert, pc: int, k: nat, pops: nat) -> bool {
    match nth_id(fc.labels@, lab(fc, pc), k) {
        Some(id) => hgt(fc, pc) >= pops + rec(fc, id).height + rec(fc, id).arity,
        None => false,
    }
}

/// The type of the function a call instruction calls.
pub open spec fn call_type(m: &Module, i: Instr) -> &FuncType {
    match i {
        Instr::Call(x) => func_type(m, x as nat),
        Instr::CallIndirect { ty, table } => &m.types@[ty as int],
        _ => &m.types@[0],
    }
}

/// Operands a call instruction pops: the arguments, and the table index
/// for `call_indirect`.
pub open spec fn call_pops(m: &Module, i: Instr) -> nat {
    n_params(call_type(m, i)) + if i is CallIndirect { 1nat } else { 0nat }
}

/// All locals of defined function `d`, parameters included.
pub open spec fn n_locals(m: &Module, d: nat) -> nat {
    n_params(func_type(m, d + n_imp(m))) + m.funcs@[d as int].locals@.len()
}

/// The instruction at a live position `pc` moves the certificate's
/// state as the semantics does.
pub open spec fn local_ok(m: &Module, d: nat, fc: FuncCert, pc: int) -> bool {
    let i = m.funcs@[d as int].body@[pc];
    let len = m.funcs@[d as int].body@.len();
    let h = hgt(fc, pc);
    let l = lab(fc, pc);
    let n = pc + 1;
    if is_unop(i) {
        h >= 1 && at(fc, n, h, l)
    } else if is_binop(i) {
        h >= 2 && at(fc, n, (h - 1) as nat, l)
    } else if load_kind(i) is Some {
        h >= 1 && at(fc, n, h, l)
    } else if store_kind(i) is Some {
        h >= 2 && at(fc, n, (h - 2) as nat, l)
    } else {
        match i {
            Instr::Unreachable => true,
            Instr::Nop => at(fc, n, h, l),
            Instr::Block { bt, end } => match bt_arity(m, bt) {
                Some((np, nr)) => h >= np && live(fc, n) && hgt(fc, n) == h
                    && (lab(fc, n) as nat) < fc.labels@.len()
                    && rec(fc, lab(fc, n)) == (LabelRec {
                        arity: nr as u32, cont: (end + 1) as u32, height: (h - np) as u32, parent: l })
                    && nr < NONE && end + 1 <= len,
                None => false,
            },
            Instr::Loop { bt } => match bt_arity(m, bt) {
                Some((np, nr)) => h >= np && live(fc, n) && hgt(fc, n) == h
                    && (lab(fc, n) as nat) < fc.labels@.len()
                    && rec(fc, lab(fc, n)) == (LabelRec {
                        arity: np as u32, cont: pc as u32, height: (h - np) as u32, parent: l })
                    && np < NONE,
                None => false,
            },
            Instr::If { bt, else_, end } => match bt_arity(m, bt) {
                Some((np, nr)) => h >= np + 1 && live(fc, n) && hgt(fc, n) == h - 1
                    && (lab(fc, n) as nat) < fc.labels@.len()
                    && rec(fc, lab(fc, n)) == (LabelRec {
                        arity: nr as u32, cont: (end + 1) as u32, height: (h - 1 - np) as u32, parent: l })
                    && nr < NONE && end + 1 <= len
                    && (if else_ == end {
                        at(fc, end as int, (h - 1) as nat, lab(fc, n))
                    } else {
                        at(fc, else_ + 1, (h - 1) as nat, lab(fc, n))
                    }),
                None => false,
            },
            // `else` leaves the innermost label with exactly its values
            // on the stack, so it never moves values.
            Instr::Else { end } => (l as nat) < fc.labels@.len()
                && h == rec(fc, l).height + rec(fc, l).arity,
            Instr::End => (l as nat) < fc.labels@.len()
                && at(fc, n, h, rec(fc, l).parent),
            Instr::Br(k) => br_ok(fc, pc, k as nat, 0),
            Instr::BrIf(k) => h >= 1 && br_ok(fc, pc, k as nat, 1) && at(fc, n, (h - 1) as nat, l),
            Instr::BrTable { start, len: tl } => h >= 1 && tl >= 1
                && start as nat + tl as nat <= m.br_table@.len()
                && forall|j: int| start <= j < start + tl ==> br_ok(fc, pc, #[trigger] m.br_table@[j] as nat, 1),
            Instr::Return => br_ok(fc, pc, (chain(fc.labels@, l).len() - 1) as nat, 0)
                && chain(fc.labels@, l).len() >= 1,
            Instr::Call(x) => x < m.func_types@.len() && h >= n_params(func_type(m, x as nat))
                && at(fc, n, (h - n_params(func_type(m, x as nat)) + n_results(func_type(m, x as nat))) as nat, l),
            Instr::CallIndirect { ty, table } => ty < m.types@.len() && table < m.tables@.len()
                && h >= 1 + n_params(&m.types@[ty as int])
                && at(fc, n, (h - 1 - n_params(&m.types@[ty as int]) + n_results(&m.types@[ty as int])) as nat, l),
            Instr::Drop => h >= 1 && at(fc, n, (h - 1) as nat, l),
            Instr::Select => h >= 3 && at(fc, n, (h - 2) as nat, l),
            Instr::LocalGet(x) => x < n_locals(m, d) && at(fc, n, h + 1, l),
            Instr::LocalSet(x) => x < n_locals(m, d) && h >= 1 && at(fc, n, (h - 1) as nat, l),
            Instr::LocalTee(x) => x < n_locals(m, d) && h >= 1 && at(fc, n, h, l),
            Instr::GlobalGet(x) => x < m.global_types@.len() && at(fc, n, h + 1, l),
            Instr::GlobalSet(x) => x < m.global_types@.len() && h >= 1 && at(fc, n, (h - 1) as nat, l),
            Instr::MemorySize => m.mems@.len() >= 1 && at(fc, n, h + 1, l),
            Instr::MemoryGrow => m.mems@.len() >= 1 && h >= 1 && at(fc, n, h, l),
            Instr::MemoryFill | Instr::MemoryCopy => m.mems@.len() >= 1 && h >= 3 && at(fc, n, (h - 3) as nat, l),
            Instr::MemoryInit(x) => m.mems@.len() >= 1 && x < m.datas@.len() && h >= 3 && at(fc, n, (h - 3) as nat, l),
            Instr::DataDrop(x) => x < m.datas@.len() && at(fc, n, h, l),
            Instr::I32Const(_) | Instr::I64Const(_) | Instr::F32Const(_) | Instr::F64Const(_) =>
                at(fc, n, h + 1, l),
            _ => false,
        }
    }
}

/// Label record `k` is well formed: its continuation is live with the
/// label's values on its stack and the enclosing labels.
pub open spec fn rec_ok(fc: FuncCert, len: nat, k: int) -> bool {
    let r = fc.labels@[k];
    (r.parent < k || r.parent == NONE) && r.cont as nat <= len
        && r.height as nat + r.arity as nat <= MAX_HEIGHT as nat
        && at(fc, r.cont as int, r.height as nat + r.arity as nat, r.parent)
}

/// Facts about the module the certificate relies on (all checked by
/// [`check_module`]).
pub open spec fn module_ok(m: &Module) -> bool {
    &&& m.n_imported_funcs as nat <= m.func_types@.len()
    &&& m.func_types@.len() < NONE as nat
    &&& m.funcs@.len() == m.func_types@.len() - m.n_imported_funcs as nat
    &&& forall|x: int| 0 <= x < m.func_types@.len() ==> (#[trigger] m.func_types@[x]) < m.types@.len()
    &&& m.mems@.len() <= 1
    &&& forall|d: nat| d < m.funcs@.len() ==> #[trigger] n_locals(m, d) <= MAX_LOCALS as nat
}

pub const MAX_LOCALS: u32 = 50_000;

pub open spec fn func_cert_ok(m: &Module, d: nat, fc: FuncCert) -> bool {
    let body = m.funcs@[d as int].body@;
    let len = body.len();
    let nres = n_results(func_type(m, d + n_imp(m)));
    &&& len >= 1 && len < NONE
    &&& fc.h@.len() == len + 1 && fc.lab@.len() == len + 1
    &&& fc.max_height <= MAX_HEIGHT
    &&& fc.labels@.len() >= 1 && fc.labels@.len() < NONE
    &&& fc.labels@[0] == (LabelRec { arity: nres as u32, cont: len as u32, height: 0, parent: NONE })
    &&& nres <= MAX_HEIGHT
    &&& at(fc, 0, 0, 0)
    &&& at(fc, len as int, nres, NONE)
    &&& forall|k: int| 0 <= k < fc.labels@.len() ==> #[trigger] rec_ok(fc, len, k)
    &&& forall|pc: int| 0 <= pc <= len && live(fc, pc) ==> #[trigger] hgt(fc, pc) <= fc.max_height
    &&& forall|pc: int| 0 <= pc < len ==> #[trigger] pc_ok(m, d, fc, pc)
}

/// The local check at `pc`, if it is live.
pub open spec fn pc_ok(m: &Module, d: nat, fc: FuncCert, pc: int) -> bool {
    live(fc, pc) ==> (lab(fc, pc) as nat) < fc.labels@.len() && local_ok(m, d, fc, pc)
}

pub open spec fn certs_ok(m: &Module, cs: Seq<FuncCert>) -> bool {
    &&& module_ok(m)
    &&& cs.len() == m.funcs@.len()
    &&& forall|d: nat| d < cs.len() ==> #[trigger] func_cert_ok(m, d, cs[d as int])
}

} // verus!
