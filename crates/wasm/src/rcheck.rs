//! What a correct register form is (`rcode_ok`), and its verified
//! checker.
//!
//! The translator in [`crate::reg`] is not trusted: [`check_rcode`] checks
//! its output one operation at a time against the function's body and
//! certificate, the way [`crate::check`] checks the validator's
//! certificates. An operation is correct when, on every value stack, it
//! computes what the instructions it stands for compute on the flat
//! machine (`crate::mach::msteps`), on the slots the semantics can see.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::cert::*;
use crate::interp::*;
use crate::mach::*;
use crate::reg::*;
use crate::reg_ops::*;
use crate::prims::ROP_SIZE;

verus! {

// ---------------------------------------------------------------------------
// What an operation computes
// ---------------------------------------------------------------------------

/// The result of a register operation: the value stack and the store, or
/// a trap.
pub enum RS {
    Next(Seq<u64>, crate::sem::Store),
    Trap(Trap, crate::sem::Store),
}

pub open spec fn is_generic(op: OpCode) -> bool {
    spec_instr(op, 0, 0) is None
}

/// The instruction an operation applies: its code's, or for a generic
/// code the one at `pc + x`.
pub open spec fn rop_instr(r: ROp, body: Seq<Instr>) -> Instr {
    match spec_instr(r.op, r.imm, r.d1) {
        Some(i) => i,
        None => body[r.pc + r.x],
    }
}

/// Writes `v` to the destinations.
pub open spec fn put(s: Seq<u64>, fp: int, r: ROp, v: u64) -> Seq<u64> {
    s.update(fp + r.d1, v).update(fp + r.d2, v)
}

pub open spec fn put_res(s: Seq<u64>, fp: int, r: ROp, v: Result<u64, Trap>, st: crate::sem::Store) -> RS {
    match v {
        Ok(x) => RS::Next(put(s, fp, r, x), st),
        Err(t) => RS::Trap(t, st),
    }
}

/// What a straight-line operation does, given its instruction `i`.
/// The stack after an operation's pre-copy (if it has one).
pub open spec fn pre_s(r: ROp, s: Seq<u64>, fp: int) -> Seq<u64> {
    if has_pre(r.op) { s.update(fp + r.pd, s[fp + r.pa]) } else { s }
}

/// What a straight-line operation does, given its instruction `i`: its
/// pre-copy, then its effect.
pub open spec fn reff(r: ROp, i: Instr, s: Seq<u64>, fp: int, st: crate::sem::Store) -> RS {
    reff_core(r, i, pre_s(r, s, fp), fp, st)
}

/// An operation's effect after its pre-copy.
pub open spec fn reff_core(r: ROp, i: Instr, s: Seq<u64>, fp: int, st: crate::sem::Store) -> RS {
    let x = s[fp + r.a];
    match fam(r.op) {
        Fam::Copy => RS::Next(put(s, fp, r, x), st),
        Fam::Const => RS::Next(put(s, fp, r, r.imm), st),
        Fam::Sel => RS::Next(put(s, fp, r, if lo32(s[fp + r.imm]) != 0 { x } else { s[fp + r.b] }), st),
        Fam::Un | Fam::Load => put_res(s, fp, r, vop(i, x, 0, st), st),
        Fam::BinRR => put_res(s, fp, r, vop(i, x, s[fp + r.b], st), st),
        Fam::BinRI => put_res(s, fp, r, vop(i, x, r.imm, st), st),
        Fam::StoreRR => match sop(i, x, s[fp + r.b], st) {
            Ok(st2) => RS::Next(s, st2),
            Err(t) => RS::Trap(t, st),
        },
        Fam::StoreRI => match sop(i, x, r.imm, st) {
            Ok(st2) => RS::Next(s, st2),
            Err(t) => RS::Trap(t, st),
        },
        _ => RS::Next(s, st),
    }
}

/// Whether a branch operation branches.
pub open spec fn rcond(r: ROp, i: Instr, s: Seq<u64>, fp: int) -> bool {
    let x = s[fp + r.a];
    match fam(r.op) {
        Fam::BrIf => lo32(x) != 0,
        Fam::BrIfZ => lo32(x) == 0,
        Fam::BrIfRR => lo32(eval_binop(i, x, s[fp + r.b])->Ok_0) != 0,
        Fam::BrIfRI => lo32(eval_binop(i, x, r.imm)->Ok_0) != 0,
        _ => true,
    }
}

pub open spec fn is_branch(f: Fam) -> bool {
    f is BrIf || f is BrIfZ || f is BrIfRR || f is BrIfRI || f is Br
}

/// The two agree on everything the semantics can see.
pub open spec fn agree(a: RS, b: MS) -> bool {
    match a {
        RS::Next(s1, st1) => match b {
            MS::Next(s2, sp2, st2) => s1.len() == s2.len() && 0 <= sp2 <= s1.len()
                && s1.subrange(0, sp2) == s2.subrange(0, sp2) && st1 == st2,
            MS::Trap(..) => false,
        },
        RS::Trap(t1, st1) => match b {
            MS::Trap(t2, st2) => t1 == t2 && st1 == st2,
            MS::Next(..) => false,
        },
    }
}

/// A branch operation's straight-line part (all but the final `br_if` or
/// `br`) leaves the stack below its `pops` operands as it was, and its
/// condition is the one `br_if` tests.
pub open spec fn agree_br(cond: bool, s: Seq<u64>, st: crate::sem::Store, b: MS, pops: int) -> bool {
    match b {
        MS::Next(s1, sp1, st1) => {
            &&& st1 == st
            &&& s1.len() == s.len()
            &&& pops <= sp1 <= s.len()
            &&& s1.subrange(0, sp1 - pops) == s.subrange(0, sp1 - pops)
            &&& (pops == 1 ==> cond == (lo32(s1[sp1 - 1]) != 0))
        },
        MS::Trap(..) => false,
    }
}

/// The slots an operation reads or writes are inside the frame.
pub open spec fn slots_ok(r: ROp, frame: nat) -> bool {
    &&& (has_pre(r.op) ==> r.pa < frame && r.pd < frame)
    &&& slots_base(r, frame)
}

pub open spec fn slots_base(r: ROp, frame: nat) -> bool {
    match fam(r.op) {
        Fam::Copy | Fam::Un | Fam::Load | Fam::BinRI => r.a < frame && r.d1 < frame && r.d2 < frame,
        Fam::Const => r.d1 < frame && r.d2 < frame,
        Fam::BinRR => r.a < frame && r.b < frame && r.d1 < frame && r.d2 < frame,
        Fam::Sel => r.a < frame && r.b < frame && r.imm < frame && r.d1 < frame && r.d2 < frame,
        Fam::StoreRR | Fam::BrIfRR => r.a < frame && r.b < frame,
        Fam::StoreRI | Fam::BrIf | Fam::BrIfZ | Fam::BrIfRI => r.a < frame,
        _ => true,
    }
}

/// Operation `r` of function `d` is correct (at a live position).
pub open spec fn rop_sem(m: &Module, d: nat, fc: FuncCert, code: &Code, r: ROp) -> bool {
    let body = m.funcs@[d as int].body@;
    let p = r.pc as int;
    let k = r.k as nat;
    let nl = code.n_locals as int;
    let h = hgt(fc, p) as int;
    let i = rop_instr(r, body);
    let f = fam(r.op);
    if f is Op {
        k == 1 && r.a as int == nl + h
    } else if is_branch(f) {
        let pb = p + k - 1;
        &&& k >= 1
        &&& straight(m, d, p, (k - 1) as nat)
        &&& pb < body.len()
        &&& (if f is Br { body[pb] is Br } else { body[pb] is BrIf })
        &&& code.side@[pb].arity == 0
        &&& (r.d1 as int) < code.rops@.len()
        &&& code.rops@[r.d1 as int].pc == code.side@[pb].pc
        &&& ((f is BrIfRR || f is BrIfRI) ==> is_cmp(i))
        &&& forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + code.frame <= s.len() ==>
            agree_br(rcond(r, i, s, fp), s, st,
                #[trigger] msteps(body, p, (k - 1) as nat, s, fp, fp + nl + h, st), if f is Br { 0 } else { 1 })
    } else {
        &&& k >= 1
        &&& straight(m, d, p, k)
        &&& (f is Un ==> is_unop(i))
        &&& (f is BinRR || f is BinRI ==> is_binop(i))
        &&& (f is Load ==> load_kind(i) is Some)
        &&& (f is StoreRR || f is StoreRI ==> store_kind(i) is Some)
        &&& forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + code.frame <= s.len() ==>
            agree(reff(r, i, s, fp, st), #[trigger] msteps(body, p, k, s, fp, fp + nl + h, st))
    }
}

pub open spec fn rop_ok(m: &Module, d: nat, fc: FuncCert, code: &Code, rpc: int) -> bool {
    op_ok(m, d, fc, code, code.rops@[rpc])
}

/// Operation `r` is correct where it starts.
pub open spec fn op_ok(m: &Module, d: nat, fc: FuncCert, code: &Code, r: ROp) -> bool {
    &&& r.pc as int <= m.funcs@[d as int].body@.len()
    &&& r.k >= 1
    &&& (live(fc, r.pc as int) && fam(r.op) is Op ==> r.a as int == code.n_locals as int + hgt(fc, r.pc as int))
    &&& (live(fc, r.pc as int) && (r.pc as int) < m.funcs@[d as int].body@.len() ==>
            slots_ok(r, code.frame as nat) && rop_sem(m, d, fc, code, r)
            && (!(fam(r.op) is Op) ==> r.x < r.k))
}

/// The entry of position `p` is an operation that starts there.
pub open spec fn entry_at(code: &Code, p: int) -> bool {
    &&& 0 <= p < code.entry@.len()
    &&& code.entry@[p] != NONE
    &&& (code.entry@[p] as int) < code.rops@.len()
    &&& code.rops@[code.entry@[p] as int].pc == p
}

/// The register form of defined function `d` is correct.
pub open spec fn rcode_ok(m: &Module, d: nat, fc: FuncCert, code: &Code) -> bool {
    let len = m.funcs@[d as int].body@.len();
    let n = code.rops@.len();
    &&& n >= 1
    &&& n < NONE
    &&& code.entry@.len() == len + 1
    &&& code.rops@[0].pc == 0
    &&& code.rops@[n - 1].pc == len
    &&& fam(code.rops@[n - 1].op) is Op
    // Consecutive runs.
    &&& forall|j: int| 0 <= j < n - 1 ==> (#[trigger] code.rops@[j + 1]).pc == code.rops@[j].pc + code.rops@[j].k
    // Every operation is the entry of its position.
    &&& forall|j: int| 0 <= j < n ==> code.rops@[j].pc <= len
        && code.entry@[#[trigger] code.rops@[j].pc as int] == j
    &&& forall|p: int| 0 <= p <= len && code.entry@[p] != NONE ==> #[trigger] entry_at(code, p)
    // Branch targets have entries.
    &&& forall|j: int| 0 <= j < fc.labels@.len() ==> #[trigger] entry_at(code, fc.labels@[j].cont as int)
    &&& forall|p: int| 0 <= p < len ==> #[trigger] if_ok(code, m.funcs@[d as int].body@[p])
    &&& forall|j: int| 0 <= j < n ==> #[trigger] rop_ok(m, d, fc, code, j)
    &&& fast_rules(code)
}

/// The families that put their result in the accumulator.
pub open spec fn is_val(f: Fam) -> bool {
    f is Copy || f is Const || f is Sel || f is Un || f is BinRR || f is BinRI || f is Load
}

/// Operation `j` reads the accumulator: it follows a value operation that
/// wrote its slot `a`.
pub open spec fn acc_src(code: &Code, j: int) -> bool {
    &&& 0 < j < code.rops@.len()
    &&& is_val(fam(code.rops@[j - 1].op))
    &&& (code.rops@[j].a == code.rops@[j - 1].d1 || code.rops@[j].a == code.rops@[j - 1].d2)
}

/// Branch operation `j`'s target does not read the accumulator, and `d2`
/// is its byte offset.
pub open spec fn br_fast(code: &Code, j: int) -> bool {
    let r = code.rops@[j];
    &&& (r.d1 as int) < code.rops@.len()
    &&& !is_acc(code.rops@[r.d1 as int].op)
    &&& r.d2 as int == r.d1 as int * ROP_SIZE as int
}

/// What the accumulator and the pointer dispatch rely on.
#[verifier::opaque]
pub open spec fn fast_rules(code: &Code) -> bool {
    &&& forall|j: int| 0 <= j < code.rops@.len() && is_acc(code.rops@[j].op) ==> #[trigger] acc_src(code, j)
    &&& forall|j: int| 0 <= j < code.rops@.len() && is_branch(fam(code.rops@[j].op)) ==> #[trigger] br_fast(code, j)
}

fn is_val_x(f: Fam) -> (r: bool)
    ensures r == is_val(f),
{
    matches!(f, Fam::Copy | Fam::Const | Fam::Sel | Fam::Un | Fam::BinRR | Fam::BinRI | Fam::Load)
}

fn is_branch_x(f: Fam) -> (r: bool)
    ensures r == is_branch(f),
{
    matches!(f, Fam::BrIf | Fam::BrIfZ | Fam::BrIfRR | Fam::BrIfRI | Fam::Br)
}

pub fn check_fast(code: &Code) -> (ok: bool)
    ensures ok ==> fast_rules(code),
{
    let n = code.rops.len();
    let mut j = 0;
    while j < n
        invariant
            n == code.rops@.len(), 0 <= j <= n,
            forall|j2: int| 0 <= j2 < j && is_acc(code.rops@[j2].op) ==> #[trigger] acc_src(code, j2),
            forall|j2: int| 0 <= j2 < j && is_branch(fam(code.rops@[j2].op)) ==> #[trigger] br_fast(code, j2),
        decreases n - j,
    {
        let r = code.rops[j];
        if is_acc_x(r.op) {
            if j == 0 {
                return false;
            }
            let p = code.rops[j - 1];
            if !is_val_x(fam_x(p.op)) || (r.a != p.d1 && r.a != p.d2) {
                return false;
            }
        }
        if is_branch_x(fam_x(r.op)) {
            if r.d1 as usize >= n || is_acc_x(code.rops[r.d1 as usize].op)
                || r.d2 as u64 != r.d1 as u64 * ROP_SIZE as u64 {
                return false;
            }
        }
        j = j + 1;
    }
    proof { reveal(fast_rules); }
    true
}

/// The targets of an `if` have entries.
pub open spec fn if_ok(code: &Code, i: Instr) -> bool {
    match i {
        Instr::If { else_, end, .. } => if else_ == end {
            entry_at(code, end as int)
        } else {
            entry_at(code, else_ + 1)
        },
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Shapes of straight-line runs
// ---------------------------------------------------------------------------

/// Pushes a local (below `nl`) or a constant.
pub open spec fn is_prod(i: Instr, nl: int) -> bool {
    (i matches Instr::LocalGet(x) && (x as int) < nl) || is_const(i)
}

pub open spec fn pval(i: Instr, s: Seq<u64>, fp: int) -> u64 {
    match i {
        Instr::LocalGet(x) => s[fp + x],
        _ => const_val(i),
    }
}

/// The stack after `np` (at most two) pushes from `q`.
pub open spec fn pushes(body: Seq<Instr>, q: int, np: nat, s: Seq<u64>, fp: int, sp: int) -> Seq<u64> {
    if np == 0 {
        s
    } else if np == 1 {
        s.update(sp, pval(body[q], s, fp))
    } else {
        s.update(sp, pval(body[q], s, fp)).update(sp + 1, pval(body[q + 1], s, fp))
    }
}

pub open spec fn noops(body: Seq<Instr>, p: int, j: nat) -> bool {
    forall|q: int| p <= q < p + j ==> #[trigger] is_noop(body[q])
}

pub open spec fn prods(body: Seq<Instr>, q: int, np: nat, nl: int) -> bool {
    &&& np <= 2
    &&& forall|j: int| q <= j < q + np ==> #[trigger] is_prod(body[j], nl)
}

#[verifier::rlimit(60)]
pub proof fn lemma_prods(body: Seq<Instr>, q: int, np: nat, nl: int, s: Seq<u64>, fp: int, sp: int,
    st: crate::sem::Store)
    requires prods(body, q, np, nl), 0 <= fp, fp + nl <= sp, sp + np <= s.len(),
    ensures
        msteps(body, q, np, s, fp, sp, st) == MS::Next(pushes(body, q, np, s, fp, sp), sp + np, st),
        pushes(body, q, np, s, fp, sp).len() == s.len(),
{
    reveal_with_fuel(msteps, 3);
    if np >= 1 {
        assert(is_prod(body[q], nl));
    }
    if np == 2 {
        assert(is_prod(body[q + 1], nl));
        let s1 = s.update(sp, pval(body[q], s, fp));
        if let Instr::LocalGet(x) = body[q + 1] {
            assert(s1[fp + x] == s[fp + x]);
        }
    }
}

/// The run `[p, p + k)`: `j0` no-ops, then `np` pushes, then the rest.
pub proof fn lemma_prefix(body: Seq<Instr>, p: int, j0: nat, np: nat, rest: nat, nl: int, s: Seq<u64>, fp: int,
    sp: int, st: crate::sem::Store)
    requires
        noops(body, p, j0),
        prods(body, p + j0, np, nl),
        0 <= fp, fp + nl <= sp, sp + np <= s.len(),
    ensures
        msteps(body, p, j0 + np + rest, s, fp, sp, st)
            == msteps(body, p + j0 + np, rest, pushes(body, p + j0, np, s, fp, sp), fp, sp + np, st),
        pushes(body, p + j0, np, s, fp, sp).len() == s.len(),
{
    lemma_msteps_split(body, p, j0, np + rest, s, fp, sp, st);
    lemma_noops(body, p, j0, s, fp, sp, st);
    lemma_msteps_split(body, p + j0, np, rest, s, fp, sp, st);
    lemma_prods(body, p + j0, np, nl, s, fp, sp, st);
    assert(j0 + np + rest == j0 + (np + rest));
}

/// Operand `j` (of `ar`, the last `np` of them pushed from `q`) as the
/// operation reads it from the stack before the run.
pub open spec fn opnd(body: Seq<Instr>, q: int, np: nat, ar: nat, j: nat, s: Seq<u64>, fp: int, sp: int) -> u64 {
    if j + np < ar { s[sp - ar + np + j] } else { pval(body[q + j + np - ar], s, fp) }
}

pub proof fn lemma_opnd(body: Seq<Instr>, q: int, np: nat, ar: nat, j: nat, nl: int, s: Seq<u64>, fp: int, sp: int)
    requires
        prods(body, q, np, nl), np <= ar, j < ar, ar <= 3,
        0 <= fp, fp + nl <= sp, sp + np <= s.len(), sp + np >= ar,
    ensures pushes(body, q, np, s, fp, sp)[sp + np - ar + j] == opnd(body, q, np, ar, j, s, fp, sp),
{
    if np >= 1 { assert(is_prod(body[q], nl)); }
    if np >= 2 { assert(is_prod(body[q + 1], nl)); }
}

/// The source of operand `j` is slot `a` (a stack slot below the pushes,
/// or the local a push reads).
pub open spec fn src_reg(body: Seq<Instr>, q: int, np: nat, ar: nat, j: nat, nl: int, h: int, a: int) -> bool {
    if j + np < ar {
        a == nl + h - ar + np + j
    } else {
        body[q + j + np - ar] == Instr::LocalGet(a as u32) && 0 <= a < nl
    }
}

/// The source of operand `j` is the constant `v`.
pub open spec fn src_imm(body: Seq<Instr>, q: int, np: nat, ar: nat, j: nat, v: u64) -> bool {
    j + np >= ar && is_const(body[q + j + np - ar]) && const_val(body[q + j + np - ar]) == v
}

pub proof fn lemma_src(body: Seq<Instr>, q: int, np: nat, ar: nat, j: nat, nl: int, h: int, a: int,
    s: Seq<u64>, fp: int)
    requires src_reg(body, q, np, ar, j, nl, h, a), j < ar, 0 <= a <= u32::MAX,
    ensures s[fp + a] == opnd(body, q, np, ar, j, s, fp, fp + nl + h),
{
}

/// Where a value computed at stack height `rh` goes: a `local.set` or
/// `local.tee` at `c` if `sink`, else the stack.
pub open spec fn dests_ok(body: Seq<Instr>, c: int, sink: bool, r: ROp, nl: int, rh: int) -> bool {
    if !sink {
        r.d1 as int == nl + rh && r.d2 as int == nl + rh
    } else {
        match body[c] {
            Instr::LocalSet(z) => (z as int) < nl && r.d1 == z && r.d2 == z,
            Instr::LocalTee(z) => (z as int) < nl && r.d1 == z && r.d2 as int == nl + rh,
            _ => false,
        }
    }
}

/// The run left the stack below `base = fp + nl + rh` alone and put `v`
/// at `base`; with the sink (if any) after it, it agrees with `put`.
pub proof fn lemma_sink(body: Seq<Instr>, c: int, sink: bool, r: ROp, nl: int, rh: int, s: Seq<u64>,
    s2: Seq<u64>, fp: int, v: u64, st: crate::sem::Store)
    requires
        dests_ok(body, c, sink, r, nl, rh),
        0 <= fp, 0 <= nl, 0 <= rh, fp + nl + rh < s.len(), s2.len() == s.len(),
        s2[fp + nl + rh] == v,
        s2.subrange(0, fp + nl + rh) == s.subrange(0, fp + nl + rh),
    ensures
        agree(RS::Next(put(s, fp, r, v), st),
            msteps(body, c, if sink { 1 } else { 0 }, s2, fp, fp + nl + rh + 1, st)),
{
    let base = fp + nl + rh;
    let sp = base + 1;
    let ps = put(s, fp, r, v);
    assert forall|q: int| 0 <= q < base && q != fp + r.d1 && q != fp + r.d2 implies ps[q] == s2[q] by {
        assert(s2.subrange(0, base)[q] == s.subrange(0, base)[q]);
    }
    if !sink {
        reveal_with_fuel(msteps, 1);
        assert(ps.subrange(0, sp) =~= s2.subrange(0, sp));
    } else {
        lemma_msteps_one(body, c, s2, fp, sp, st);
        match body[c] {
            Instr::LocalSet(z) => {
                let s3 = s2.update(fp + z, s2[sp - 1]);
                assert(ps.subrange(0, sp - 1) =~= s3.subrange(0, sp - 1));
            },
            Instr::LocalTee(z) => {
                let s3 = s2.update(fp + z, s2[sp - 1]);
                assert(ps.subrange(0, sp) =~= s3.subrange(0, sp));
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// Each kind of operation
// ---------------------------------------------------------------------------

/// A value operation (unary, binary, load): `j0` no-ops, `np` pushes, the
/// instruction `i` at `p + x`, and maybe a sink.
pub open spec fn vshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int) -> bool {
    let p = r.pc as int;
    let x = r.x as nat;
    let ar = vop_arity(i);
    let q = p + j0;
    let f = fam(r.op);
    &&& noops(body, p, j0)
    &&& prods(body, q, np, nl)
    &&& x == j0 + np
    &&& body[p + x] == i
    &&& is_vop(i)
    &&& (f is Un ==> is_unop(i))
    &&& (f is Load ==> load_kind(i) is Some)
    &&& (f is BinRR || f is BinRI ==> is_binop(i))
    &&& (f is Un || f is Load || f is BinRR || f is BinRI)
    &&& np <= ar
    &&& h + np >= ar
    &&& src_reg(body, q, np, ar, 0, nl, h, r.a as int)
    &&& (f is BinRR ==> src_reg(body, q, np, ar, 1, nl, h, r.b as int))
    &&& (f is BinRI ==> src_imm(body, q, np, ar, 1, r.imm))
    &&& (r.k == x + 1 || r.k == x + 2)
    &&& dests_ok(body, p + x + 1, r.k == x + 2, r, nl, h + np - ar)
}

#[verifier::rlimit(300)]
pub proof fn lemma_vshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int)
    requires
        vshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame,
        (r.d1 as int) < frame, (r.d2 as int) < frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree(reff_core(r, i, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let ar = vop_arity(i);
    let q = p + j0;
    let sink = r.k == x + 2;
    let rh = h + np - ar;
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree(reff_core(r, i, s, fp, st), #[trigger] msteps(body, p, r.k as nat, s, fp, fp + nl + h, st)) by {
        let sp = fp + nl + h;
        let rest = (r.k - x) as nat;
        lemma_prefix(body, p, j0, np, rest, nl, s, fp, sp, st);
        let s1 = pushes(body, q, np, s, fp, sp);
        let sp1 = sp + np;
        lemma_msteps_split(body, p + x, 1, (rest - 1) as nat, s1, fp, sp1, st);
        lemma_msteps_one(body, p + x, s1, fp, sp1, st);
        lemma_opnd(body, q, np, ar, 0, nl, s, fp, sp);
        lemma_src(body, q, np, ar, 0, nl, h, r.a as int, s, fp);
        let x0 = s1[sp1 - ar];
        assert(x0 == s[fp + r.a]);
        let x1 = s1[sp1 - ar + 1];
        let f = fam(r.op);
        if ar == 2 {
            lemma_opnd(body, q, np, ar, 1, nl, s, fp, sp);
            if f is BinRR {
                lemma_src(body, q, np, ar, 1, nl, h, r.b as int, s, fp);
                assert(x1 == s[fp + r.b]);
            } else {
                assert(f is BinRI);
                assert(x1 == r.imm);
            }
        }
        let y = if f is BinRR { s[fp + r.b] } else if f is BinRI { r.imm } else { 0 };
        assert(vop(i, x0, x1, st) == vop(i, s[fp + r.a], y, st));
        match vop(i, x0, x1, st) {
            Ok(v) => {
                let s2 = s1.update(sp1 - ar, v);
                assert(reff_core(r, i, s, fp, st) == RS::Next(put(s, fp, r, v), st));
                // Below the result slot, the run left the stack alone.
                assert(s2.subrange(0, fp + nl + rh) =~= s.subrange(0, fp + nl + rh));
                lemma_sink(body, p + x + 1, sink, r, nl, rh, s, s2, fp, v, st);
            },
            Err(t) => {},
        }
    }
}

/// A store: `j0` no-ops, `np` pushes, the store `i` at `p + x`.
pub open spec fn sshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int) -> bool {
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let f = fam(r.op);
    &&& noops(body, p, j0)
    &&& prods(body, q, np, nl)
    &&& x == j0 + np
    &&& body[p + x] == i
    &&& store_kind(i) is Some
    &&& (f is StoreRR || f is StoreRI)
    &&& h + np >= 2
    &&& src_reg(body, q, np, 2, 0, nl, h, r.a as int)
    &&& (f is StoreRR ==> src_reg(body, q, np, 2, 1, nl, h, r.b as int))
    &&& (f is StoreRI ==> src_imm(body, q, np, 2, 1, r.imm))
    &&& r.k == x + 1
}

#[verifier::rlimit(500)]
proof fn lemma_sshape_one(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int,
    s: Seq<u64>, fp: int, st: crate::sem::Store)
    requires
        sshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame, 0 <= fp, fp + frame <= s.len(),
    ensures
        agree(reff_core(r, i, s, fp, st), msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let sp = fp + nl + h;
    lemma_prefix(body, p, j0, np, 1, nl, s, fp, sp, st);
    let s1 = pushes(body, q, np, s, fp, sp);
    let sp1 = sp + np;
    lemma_msteps_one(body, p + x, s1, fp, sp1, st);
    lemma_opnd(body, q, np, 2, 0, nl, s, fp, sp);
    lemma_opnd(body, q, np, 2, 1, nl, s, fp, sp);
    lemma_src(body, q, np, 2, 0, nl, h, r.a as int, s, fp);
    let f = fam(r.op);
    if f is StoreRR {
        lemma_src(body, q, np, 2, 1, nl, h, r.b as int, s, fp);
    }
    assert(s1.subrange(0, sp1 - 2) =~= s.subrange(0, sp1 - 2));
}

pub proof fn lemma_sshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int)
    requires
        sshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree(reff_core(r, i, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree(reff_core(r, i, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)) by {
        lemma_sshape_one(body, r, i, j0, np, nl, h, frame, s, fp, st);
    }
}

/// A copy or a constant: `j0` no-ops, then a push and maybe a sink, or a
/// bare `local.set` / `local.tee` of the stack top.
pub open spec fn cshape(body: Seq<Instr>, r: ROp, j0: nat, np: nat, nl: int, h: int) -> bool {
    let p = r.pc as int;
    let q = p + j0;
    let f = fam(r.op);
    &&& noops(body, p, j0)
    &&& (f is Copy || f is Const)
    &&& if np == 1 {
        &&& (f is Copy ==> body[q] == Instr::LocalGet(r.a) && (r.a as int) < nl)
        &&& (f is Const ==> is_const(body[q]) && const_val(body[q]) == r.imm)
        &&& (r.k == j0 + 1 || r.k == j0 + 2)
        &&& dests_ok(body, q + 1, r.k == j0 + 2, r, nl, h)
    } else {
        &&& np == 0
        &&& f is Copy
        &&& h >= 1
        &&& r.a as int == nl + h - 1
        &&& r.k == j0 + 1
        &&& dests_ok(body, q, true, r, nl, h - 1)
    }
}

pub proof fn lemma_cshape(body: Seq<Instr>, r: ROp, j0: nat, np: nat, nl: int, h: int, frame: int)
    requires
        cshape(body, r, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree(reff_core(r, Instr::Nop, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    let q = p + j0;
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree(reff_core(r, Instr::Nop, s, fp, st), #[trigger] msteps(body, p, r.k as nat, s, fp, fp + nl + h, st)) by {
        let sp = fp + nl + h;
        let v = if fam(r.op) is Copy { s[fp + r.a] } else { r.imm };
        assert(reff_core(r, Instr::Nop, s, fp, st) == RS::Next(put(s, fp, r, v), st));
        if np == 1 {
            let rest = (r.k - j0 - 1) as nat;
            assert(is_prod(body[q], nl));
            lemma_prefix(body, p, j0, 1, rest, nl, s, fp, sp, st);
            let s1 = pushes(body, q, 1, s, fp, sp);
            assert(s1[sp] == v);
            assert(s1.subrange(0, sp) =~= s.subrange(0, sp));
            lemma_sink(body, q + 1, r.k == j0 + 2, r, nl, h, s, s1, fp, v, st);
        } else {
            lemma_msteps_split(body, p, j0, 1, s, fp, sp, st);
            lemma_noops(body, p, j0, s, fp, sp, st);
            lemma_sink(body, q, true, r, nl, h - 1, s, s, fp, v, st);
        }
    }
}

/// `j0` no-ops, then maybe a `drop`.
pub open spec fn kshape(body: Seq<Instr>, r: ROp, j0: nat, h: int) -> bool {
    &&& fam(r.op) is Skip
    &&& noops(body, r.pc as int, j0)
    &&& (r.k == j0 || (r.k == j0 + 1 && body[r.pc + j0] is Drop && h >= 1))
}

pub proof fn lemma_kshape(body: Seq<Instr>, r: ROp, j0: nat, nl: int, h: int, frame: int)
    requires
        kshape(body, r, j0, h),
        0 <= nl, 0 <= h, nl + h <= frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree(reff_core(r, Instr::Nop, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree(reff_core(r, Instr::Nop, s, fp, st), #[trigger] msteps(body, p, r.k as nat, s, fp, fp + nl + h, st)) by {
        let sp = fp + nl + h;
        let rest = (r.k - j0) as nat;
        lemma_msteps_split(body, p, j0, rest, s, fp, sp, st);
        lemma_noops(body, p, j0, s, fp, sp, st);
        if rest == 1 {
            lemma_msteps_one(body, p + j0, s, fp, sp, st);
        } else {
            reveal_with_fuel(msteps, 1);
        }
        assert(s.subrange(0, sp - 1) =~= s.subrange(0, sp - 1));
    }
}

/// `i32.eqz` makes 1 of a zero and 0 of anything else.
/// A `select`: `j0` no-ops, `np` pushes, the `select` at `p + x`, and
/// maybe a sink. Operand 0 is slot `a`, 1 slot `b`, the condition slot `imm`.
pub open spec fn selshape(body: Seq<Instr>, r: ROp, j0: nat, np: nat, nl: int, h: int) -> bool {
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    &&& noops(body, p, j0)
    &&& prods(body, q, np, nl)
    &&& x == j0 + np
    &&& body[p + x] == Instr::Select
    &&& np <= 3
    &&& h + np >= 3
    &&& r.imm <= u32::MAX
    &&& src_reg(body, q, np, 3, 0, nl, h, r.a as int)
    &&& src_reg(body, q, np, 3, 1, nl, h, r.b as int)
    &&& src_reg(body, q, np, 3, 2, nl, h, r.imm as int)
    &&& (r.k == x + 1 || r.k == x + 2)
    &&& dests_ok(body, p + x + 1, r.k == x + 2, r, nl, h + np - 3)
}

#[verifier::rlimit(300)]
pub proof fn lemma_selshape(body: Seq<Instr>, r: ROp, j0: nat, np: nat, nl: int, h: int, frame: int)
    requires
        selshape(body, r, j0, np, nl, h),
        fam(r.op) is Sel,
        0 <= nl, 0 <= h, nl + h + np <= frame,
        (r.d1 as int) < frame, (r.d2 as int) < frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree(reff_core(r, Instr::Select, s, fp, st), #[trigger] msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let sink = r.k == x + 2;
    let rh = h + np - 3;
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree(reff_core(r, Instr::Select, s, fp, st), #[trigger] msteps(body, p, r.k as nat, s, fp, fp + nl + h, st)) by {
        let sp = fp + nl + h;
        let rest = (r.k - x) as nat;
        lemma_prefix(body, p, j0, np, rest, nl, s, fp, sp, st);
        let s1 = pushes(body, q, np, s, fp, sp);
        let sp1 = sp + np;
        lemma_msteps_split(body, p + x, 1, (rest - 1) as nat, s1, fp, sp1, st);
        lemma_msteps_one(body, p + x, s1, fp, sp1, st);
        lemma_opnd(body, q, np, 3, 0, nl, s, fp, sp);
        lemma_opnd(body, q, np, 3, 1, nl, s, fp, sp);
        lemma_opnd(body, q, np, 3, 2, nl, s, fp, sp);
        lemma_src(body, q, np, 3, 0, nl, h, r.a as int, s, fp);
        lemma_src(body, q, np, 3, 1, nl, h, r.b as int, s, fp);
        lemma_src(body, q, np, 3, 2, nl, h, r.imm as int, s, fp);
        assert(s1[sp1 - 3] == s[fp + r.a]);
        assert(s1[sp1 - 2] == s[fp + r.b]);
        assert(s1[sp1 - 1] == s[fp + r.imm]);
        let v = if lo32(s1[sp1 - 1]) != 0 { s1[sp1 - 3] } else { s1[sp1 - 2] };
        let s2 = s1.update(sp1 - 3, v);
        assert(mstep(Instr::Select, s1, fp, sp1, st) == MS::Next(s2, sp1 - 2, st));
        assert(reff_core(r, Instr::Select, s, fp, st) == RS::Next(put(s, fp, r, v), st));
        assert(s2.subrange(0, fp + nl + rh) =~= s.subrange(0, fp + nl + rh));
        lemma_sink(body, p + x + 1, sink, r, nl, rh, s, s2, fp, v, st);
    }
}

pub proof fn lemma_eqz(x: u64)
    ensures
        eval_unop(Instr::I32Eqz, x) is Ok,
        (lo32(eval_unop(Instr::I32Eqz, x)->Ok_0) != 0) == (lo32(x) == 0),
{
    assert(lo32(1u64) == 1u32 && lo32(0u64) == 0u32);
}

/// Comparisons never trap.
pub proof fn lemma_cmp(i: Instr, a: u64, b: u64)
    requires is_cmp(i),
    ensures eval_binop(i, a, b) is Ok,
{
}

/// A branch: its straight-line part (`k - 1` instructions) and the final
/// `br_if` or `br`.
pub open spec fn bshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int) -> bool {
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let f = fam(r.op);
    &&& noops(body, p, j0)
    &&& match f {
        Fam::Br => np == 0 && r.k == j0 + 1,
        Fam::BrIf | Fam::BrIfZ => {
            &&& np <= 1
            &&& (np == 1 ==> body[q] == Instr::LocalGet(r.a) && (r.a as int) < nl)
            &&& (np == 0 ==> h >= 1 && r.a as int == nl + h - 1)
            &&& (f is BrIf ==> r.k == j0 + np + 1)
            &&& (f is BrIfZ ==> r.k == j0 + np + 2 && body[q + np] == Instr::I32Eqz)
        },
        Fam::BrIfRR | Fam::BrIfRI => {
            &&& prods(body, q, np, nl)
            &&& x == j0 + np
            &&& body[p + x] == i
            &&& is_cmp(i)
            &&& h + np >= 2
            &&& src_reg(body, q, np, 2, 0, nl, h, r.a as int)
            &&& (f is BrIfRR ==> src_reg(body, q, np, 2, 1, nl, h, r.b as int))
            &&& (f is BrIfRI ==> src_imm(body, q, np, 2, 1, r.imm))
            &&& r.k == x + 2
        },
        _ => false,
    }
}

proof fn lemma_bshape_br(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int,
    s: Seq<u64>, fp: int, st: crate::sem::Store)
    requires
        bshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame, 0 <= fp, fp + frame <= s.len(),
        fam(r.op) is Br,
    ensures
        agree_br(rcond(r, i, s, fp), s, st,
            msteps(body, r.pc as int, (r.k - 1) as nat, s, fp, fp + nl + h, st),
            if fam(r.op) is Br { 0 } else { 1 }),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let f = fam(r.op);
    let sp = fp + nl + h;
    lemma_noops(body, p, j0, s, fp, sp, st);
    assert(s.subrange(0, sp) =~= s.subrange(0, sp));
}

#[verifier::rlimit(500)]
proof fn lemma_bshape_brif(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int,
    s: Seq<u64>, fp: int, st: crate::sem::Store)
    requires
        bshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame, 0 <= fp, fp + frame <= s.len(),
        fam(r.op) is BrIf || fam(r.op) is BrIfZ,
    ensures
        agree_br(rcond(r, i, s, fp), s, st,
            msteps(body, r.pc as int, (r.k - 1) as nat, s, fp, fp + nl + h, st),
            if fam(r.op) is Br { 0 } else { 1 }),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let f = fam(r.op);
    let sp = fp + nl + h;
    if np == 1 {
        assert(is_prod(body[q], nl));
    }
    let rest: nat = if f is BrIfZ { 1 } else { 0 };
    lemma_prefix(body, p, j0, np, rest, nl, s, fp, sp, st);
    let s1 = pushes(body, q, np, s, fp, sp);
    let sp1 = sp + np;
    let xv = s[fp + r.a];
    assert(s1[sp1 - 1] == xv);
    assert(s1.subrange(0, sp1 - 1) =~= s.subrange(0, sp1 - 1));
    if f is BrIfZ {
        lemma_msteps_one(body, q + np, s1, fp, sp1, st);
        lemma_eqz(xv);
        let s2 = s1.update(sp1 - 1, eval_unop(Instr::I32Eqz, xv)->Ok_0);
        assert(s2.subrange(0, sp1 - 1) =~= s.subrange(0, sp1 - 1));
    } else {
        reveal_with_fuel(msteps, 1);
    }
}

proof fn lemma_bshape_cmp(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int,
    s: Seq<u64>, fp: int, st: crate::sem::Store)
    requires
        bshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame, 0 <= fp, fp + frame <= s.len(),
        fam(r.op) is BrIfRR || fam(r.op) is BrIfRI,
    ensures
        agree_br(rcond(r, i, s, fp), s, st,
            msteps(body, r.pc as int, (r.k - 1) as nat, s, fp, fp + nl + h, st),
            if fam(r.op) is Br { 0 } else { 1 }),
{
    let p = r.pc as int;
    let x = r.x as nat;
    let q = p + j0;
    let f = fam(r.op);
    let sp = fp + nl + h;
    let y = if f is BrIfRR { s[fp + r.b] } else { r.imm };
    lemma_prefix(body, p, j0, np, 1, nl, s, fp, sp, st);
    let s1 = pushes(body, q, np, s, fp, sp);
    let sp1 = sp + np;
    lemma_msteps_one(body, p + x, s1, fp, sp1, st);
    lemma_opnd(body, q, np, 2, 0, nl, s, fp, sp);
    lemma_opnd(body, q, np, 2, 1, nl, s, fp, sp);
    lemma_src(body, q, np, 2, 0, nl, h, r.a as int, s, fp);
    if f is BrIfRR {
        lemma_src(body, q, np, 2, 1, nl, h, r.b as int, s, fp);
    }
    assert(s1[sp1 - 2] == s[fp + r.a] && s1[sp1 - 1] == y);
    lemma_cmp(i, s[fp + r.a], y);
    let v = eval_binop(i, s[fp + r.a], y)->Ok_0;
    let s2 = s1.update(sp1 - 2, v);
    assert(s2.subrange(0, sp1 - 2) =~= s.subrange(0, sp1 - 2));
    assert(s2[sp1 - 2] == v);
}

pub proof fn lemma_bshape(body: Seq<Instr>, r: ROp, i: Instr, j0: nat, np: nat, nl: int, h: int, frame: int)
    requires
        bshape(body, r, i, j0, np, nl, h),
        0 <= nl, 0 <= h, nl + h + np <= frame,
    ensures
        forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() ==>
            agree_br(rcond(r, i, s, fp), s, st,
                #[trigger] msteps(body, r.pc as int, (r.k - 1) as nat, s, fp, fp + nl + h, st),
                if fam(r.op) is Br { 0 } else { 1 }),
{
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + frame <= s.len() implies
        agree_br(rcond(r, i, s, fp), s, st,
            #[trigger] msteps(body, r.pc as int, (r.k - 1) as nat, s, fp, fp + nl + h, st),
            if fam(r.op) is Br { 0 } else { 1 }) by {
        let f = fam(r.op);
        if f is Br {
            lemma_bshape_br(body, r, i, j0, np, nl, h, frame, s, fp, st);
        } else if f is BrIf || f is BrIfZ {
            lemma_bshape_brif(body, r, i, j0, np, nl, h, frame, s, fp, st);
        } else {
            lemma_bshape_cmp(body, r, i, j0, np, nl, h, frame, s, fp, st);
        }
    }
}

/// One state of `lemma_pre_sem`: the `local.get` step, then the rest of
/// the run as the operation without its pre-copy.
#[verifier::spinoff_prover]
proof fn lemma_pre_at(body: Seq<Instr>, r: ROp, r2: ROp, i: Instr, nl: int, h: int, s: Seq<u64>, fp: int,
    st: crate::sem::Store)
    requires
        r.k >= 2,
        r2.pc == r.pc + 1, r2.k == r.k - 1,
        0 <= r.pc < body.len(),
        body[r.pc as int] == Instr::LocalGet(r.pa),
        has_pre(r.op),
        !has_pre(r2.op),
        r.pd as int == nl + h,
        agree(reff(r2, i, s.update(fp + nl + h, s[fp + r.pa]), fp, st),
            msteps(body, r.pc + 1, (r.k - 1) as nat, s.update(fp + nl + h, s[fp + r.pa]), fp, fp + nl + h + 1, st)),
        reff(r2, i, s.update(fp + nl + h, s[fp + r.pa]), fp, st)
            == reff_core(r, i, s.update(fp + nl + h, s[fp + r.pa]), fp, st),
    ensures
        agree(reff(r, i, s, fp, st), msteps(body, r.pc as int, r.k as nat, s, fp, fp + nl + h, st)),
{
    let p = r.pc as int;
    let k = r.k as nat;
    let sp = fp + nl + h;
    let s1 = s.update(sp, s[fp + r.pa]);
    lemma_msteps_split(body, p, 1, (k - 1) as nat, s, fp, sp, st);
    lemma_msteps_one(body, p, s, fp, sp, st);
    assert(1 + (k - 1) as nat == k);
    assert(msteps(body, p, k, s, fp, sp, st) == msteps(body, p + 1, (k - 1) as nat, s1, fp, sp + 1, st));
    assert(pre_s(r, s, fp) == s1);
}

/// An operation with a pre-copy is correct when its `local.get` is, and
/// the operation without it is correct from the next position.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub proof fn lemma_pre_sem(m: &Module, d: nat, fc: FuncCert, code: &Code, r: ROp, r2: ROp)
    requires
        d < m.funcs@.len(),
        has_pre(r.op),
        !has_pre(r2.op),
        r2.op == unpre(r.op),
        r2.pc == r.pc + 1, r2.k == r.k - 1, r2.x == r.x - 1,
        r2.a == r.a, r2.b == r.b, r2.d1 == r.d1, r2.d2 == r.d2, r2.imm == r.imm,
        r2.pa == r.pa, r2.pd == r.pd,
        r.k >= 2, r.x >= 1,
        (r.pc as int) + 1 < m.funcs@[d as int].body@.len(),
        live(fc, r.pc as int), live(fc, r.pc + 1),
        hgt(fc, r.pc + 1) == hgt(fc, r.pc as int) + 1,
        m.funcs@[d as int].body@[r.pc as int] == Instr::LocalGet(r.pa),
        (r.pa as int) < code.n_locals as int,
        r.pd as int == code.n_locals as int + hgt(fc, r.pc as int),
        r.pa < code.frame, r.pd < code.frame,
        op_ok(m, d, fc, code, r2),
    ensures op_ok(m, d, fc, code, r),
{
    let body = m.funcs@[d as int].body@;
    let p = r.pc as int;
    let k = r.k as nat;
    let nl = code.n_locals as int;
    let h = hgt(fc, p) as int;
    lemma_unpre(r.op, r.imm, r.d1);
    let i = rop_instr(r, body);
    assert(rop_instr(r2, body) == i);
    let f = fam(r.op);
    assert(fam(r2.op) == f);
    assert(slots_ok(r2, code.frame as nat));
    assert(rop_sem(m, d, fc, code, r2));
    assert(!(f is Op) && !is_branch(f));
    assert(straight(m, d, p, k)) by {
        assert(simple(body[p]));
        assert forall|j: int| p <= j < p + k implies #[trigger] simple(body[j]) by {
            if j > p { assert(p + 1 <= j < (p + 1) + (k - 1)); }
        }
    }
    assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store| 0 <= fp && fp + code.frame <= s.len() implies
        agree(reff(r, i, s, fp, st), #[trigger] msteps(body, p, k, s, fp, fp + nl + h, st)) by {
        let s1 = s.update(fp + nl + h, s[fp + r.pa]);
        assert(agree(reff(r2, i, s1, fp, st), msteps(body, r2.pc as int, r2.k as nat, s1, fp, fp + nl + hgt(fc, r2.pc as int), st)));
        assert(reff(r2, i, s1, fp, st) == reff_core(r, i, s1, fp, st));
        lemma_pre_at(body, r, r2, i, nl, h, s, fp, st);
    }
    assert(rop_sem(m, d, fc, code, r));
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// The number of no-ops from `p`, up to `lim`.
fn count_noops(body: &Vec<Instr>, p: usize, lim: usize) -> (j: usize)
    requires p <= lim <= body@.len(),
    ensures p + j <= lim, noops(body@, p as int, j as nat),
{
    let mut q = p;
    while q < lim && is_noop_x(body[q])
        invariant p <= q <= lim, lim <= body@.len(), noops(body@, p as int, (q - p) as nat),
        decreases lim - q,
    {
        q = q + 1;
    }
    q - p
}

fn is_const_x(i: Instr) -> (r: bool)
    ensures r == is_const(i),
{
    match i {
        Instr::I32Const(_) | Instr::I64Const(_) | Instr::F32Const(_) | Instr::F64Const(_) => true,
        _ => false,
    }
}

fn const_val_x(i: Instr) -> (r: u64)
    ensures r == const_val(i),
{
    match i {
        Instr::I32Const(v) => v as u64,
        Instr::I64Const(v) => v,
        Instr::F32Const(v) => v as u64,
        Instr::F64Const(v) => v,
        _ => 0,
    }
}

fn prod_x(i: Instr, nl: u32) -> (r: bool)
    ensures r == is_prod(i, nl as int),
{
    match i {
        Instr::LocalGet(x) => x < nl,
        _ => is_const_x(i),
    }
}

fn simple_x(i: Instr) -> (r: bool)
    ensures r == simple(i),
{
    if is_unop_x(i) || is_binop_x(i) || is_load_x(i) || is_store_x(i) || is_noop_x(i) || is_const_x(i) {
        return true;
    }
    match i {
        Instr::Drop | Instr::Select | Instr::LocalGet(_) | Instr::LocalSet(_) | Instr::LocalTee(_) => true,
        _ => false,
    }
}

/// `[p, p + k)` is straight-line code.
fn check_straight(body: &Vec<Instr>, p: usize, k: usize) -> (r: bool)
    requires p + k <= body@.len(),
    ensures r ==> forall|j: int| p <= j < p + k ==> #[trigger] simple(body@[j]),
{
    let _n = body.len();
    let mut q = p;
    let e = p + k;
    while q < e
        invariant p <= q <= e, e == p + k, p + k <= body@.len(),
            forall|j: int| p <= j < q ==> #[trigger] simple(body@[j]),
        decreases e - q,
    {
        if !simple_x(body[q]) {
            return false;
        }
        q = q + 1;
    }
    true
}

/// The `np` instructions from `q` are pushes.
fn check_prods(body: &Vec<Instr>, q: usize, np: usize, nl: u32) -> (r: bool)
    requires q + np <= body@.len(),
    ensures r ==> prods(body@, q as int, np as nat, nl as int),
{
    let _n = body.len();
    if np > 2 {
        return false;
    }
    if np >= 1 && !prod_x(body[q], nl) {
        return false;
    }
    if np == 2 && !prod_x(body[q + 1], nl) {
        return false;
    }
    proof {
        assert forall|j: int| q <= j < q + np implies #[trigger] is_prod(body@[j], nl as int) by {
            assert(j == q || j == q + 1);
        }
    }
    true
}

fn src_reg_x(body: &Vec<Instr>, q: usize, np: usize, ar: usize, j: usize, nl: u32, h: u32, a: u32) -> (r: bool)
    requires q + np <= body@.len(), np <= ar <= 3, j < ar, h as int + np >= ar,
    ensures r ==> src_reg(body@, q as int, np as nat, ar as nat, j as nat, nl as int, h as int, a as int),
{
    let _n = body.len();
    if j + np < ar {
        a as u64 + ar as u64 == nl as u64 + h as u64 + np as u64 + j as u64
    } else {
        match body[q + (j + np - ar)] {
            Instr::LocalGet(y) => y == a && a < nl,
            _ => false,
        }
    }
}

fn src_imm_x(body: &Vec<Instr>, q: usize, np: usize, ar: usize, j: usize, v: u64) -> (r: bool)
    requires q + np <= body@.len(), np <= ar <= 2, j < ar,
    ensures r ==> src_imm(body@, q as int, np as nat, ar as nat, j as nat, v),
{
    let _n = body.len();
    if j + np >= ar && j + np - ar < np {
        let i = body[q + (j + np - ar)];
        is_const_x(i) && const_val_x(i) == v
    } else {
        false
    }
}

fn dests_ok_x(body: &Vec<Instr>, c: usize, sink: bool, r: ROp, nl: u32, rh: u64) -> (b: bool)
    requires sink ==> c < body@.len(), rh <= u32::MAX,
    ensures b ==> dests_ok(body@, c as int, sink, r, nl as int, rh as int),
{
    if !sink {
        r.d1 as u64 == nl as u64 + rh && r.d2 as u64 == nl as u64 + rh
    } else {
        match body[c] {
            Instr::LocalSet(z) => z < nl && r.d1 == z && r.d2 == z,
            Instr::LocalTee(z) => z < nl && r.d1 == z && r.d2 as u64 == nl as u64 + rh,
            _ => false,
        }
    }
}

fn slots_ok_x(r: ROp, frame: u32) -> (b: bool)
    ensures b == slots_ok(r, frame as nat),
{
    (!has_pre_x(r.op) || (r.pa < frame && r.pd < frame)) && slots_base_x(r, frame)
}

fn slots_base_x(r: ROp, frame: u32) -> (b: bool)
    ensures b == slots_base(r, frame as nat),
{
    match fam_x(r.op) {
        Fam::Copy | Fam::Un | Fam::Load | Fam::BinRI => r.a < frame && r.d1 < frame && r.d2 < frame,
        Fam::Const => r.d1 < frame && r.d2 < frame,
        Fam::BinRR => r.a < frame && r.b < frame && r.d1 < frame && r.d2 < frame,
        Fam::Sel => r.a < frame && r.b < frame && r.imm < frame as u64 && r.d1 < frame && r.d2 < frame,
        Fam::StoreRR | Fam::BrIfRR => r.a < frame && r.b < frame,
        Fam::StoreRI | Fam::BrIf | Fam::BrIfZ | Fam::BrIfRI => r.a < frame,
        _ => true,
    }
}

/// What a function's code has to have for its register form to be
/// checked.
pub open spec fn rcheck_pre(m: &Module, d: nat, fc: FuncCert, code: &Code) -> bool {
    let len = m.funcs@[d as int].body@.len();
    &&& d < m.funcs@.len()
    &&& len < NONE
    &&& code.side@.len() == len + 1
    &&& fc.h@.len() == len + 1
}

/// Checks operation `j`.
fn check_rop(m: &Module, d: usize, fc: &FuncCert, code: &Code, j: usize) -> (ok: bool)
    requires rcheck_pre(m, d as nat, *fc, code), j < code.rops@.len(),
    ensures ok ==> rop_ok(m, d as nat, *fc, code, j as int),
{
    let r = code.rops[j];
    if has_pre_x(r.op) {
        check_pre(m, d, fc, code, r)
    } else {
        check_op(m, d, fc, code, r)
    }
}

/// Checks an operation with a pre-copy: a `local.get` to the stack top,
/// then (from the next position) the operation without it.
fn check_pre(m: &Module, d: usize, fc: &FuncCert, code: &Code, r: ROp) -> (ok: bool)
    requires rcheck_pre(m, d as nat, *fc, code), has_pre(r.op),
    ensures ok ==> op_ok(m, d as nat, *fc, code, r),
{
    let body = &m.funcs[d].body;
    let len = body.len();
    if r.pc as usize >= len || r.k < 2 || r.x < 1 || r.k as usize > len - r.pc as usize {
        return false;
    }
    let p = r.pc as usize;
    if fc.h[p] == NONE {
        return true;
    }
    let h = fc.h[p];
    let nl = code.n_locals;
    let src_fits = match body[p] { Instr::LocalGet(y) => y == r.pa && r.pa < nl, _ => false };
    if !src_fits || r.pd as u64 != nl as u64 + h as u64 || fc.h[p + 1] == NONE || fc.h[p + 1] as u64 != h as u64 + 1
        || r.pa >= code.frame || r.pd >= code.frame {
        return false;
    }
    let r2 = ROp { op: unpre_x(r.op), pc: r.pc + 1, k: r.k - 1, x: r.x - 1, ..r };
    if has_pre_x(r2.op) || !check_op(m, d, fc, code, r2) {
        return false;
    }
    proof {
        assert(body@ == m.funcs@[d as int].body@);
        lemma_pre_sem(m, d as nat, *fc, code, r, r2);
    }
    true
}

/// Checks an operation without a pre-copy.
#[allow(unused_assignments)]
fn check_op(m: &Module, d: usize, fc: &FuncCert, code: &Code, r: ROp) -> (ok: bool)
    requires rcheck_pre(m, d as nat, *fc, code), !has_pre(r.op),
    ensures ok ==> op_ok(m, d as nat, *fc, code, r),
{
    let body = &m.funcs[d].body;
    let len = body.len();
    if r.pc as usize > len || r.k == 0 {
        return false;
    }
    let p = r.pc as usize;
    if fc.h[p] == NONE {
        return true;
    }
    let h = fc.h[p];
    let nl = code.n_locals;
    let frame = code.frame;
    if p == len {
        return !matches!(fam_x(r.op), Fam::Op) || r.a as u64 == nl as u64 + h as u64;
    }
    if !slots_ok_x(r, frame) || r.k as usize > len - p || (!matches!(fam_x(r.op), Fam::Op) && r.x >= r.k) {
        return false;
    }
    let k = r.k as usize;
    let hh = h as u64;
    let room = frame as u64;
    let nl64 = nl as u64;
    proof {
        assert(body@ == m.funcs@[d as int].body@);
        assert(hgt(*fc, p as int) == h);
    }
    match fam_x(r.op) {
        Fam::Op => {
            r.k == 1 && r.a as u64 == nl64 + hh
        },
        Fam::Un | Fam::Load | Fam::BinRR | Fam::BinRI => {
            let x = r.x as usize;
            if x >= k {
                return false;
            }
            let j0 = count_noops(body, p, p + x);
            let np = x - j0;
            let q = p + j0;
            let i = body[p + x];
            if !instr_matches(r.op, r.imm, r.d1, i) {
                return false;
            }
            let f = fam_x(r.op);
            let un = is_unop_x(i);
            let bin = is_binop_x(i);
            let ld = is_load_x(i);
            let fam_fits = match f {
                Fam::Un => un,
                Fam::Load => ld,
                _ => bin,
            };
            if !fam_fits {
                return false;
            }
            let ar: usize = if bin { 2 } else { 1 };
            if np > ar || hh + (np as u64) < ar as u64 || nl64 + hh + np as u64 > room {
                return false;
            }
            if !check_prods(body, q, np, nl) || !src_reg_x(body, q, np, ar, 0, nl, h, r.a) {
                return false;
            }
            if matches!(f, Fam::BinRR) && !src_reg_x(body, q, np, ar, 1, nl, h, r.b) {
                return false;
            }
            if matches!(f, Fam::BinRI) && !src_imm_x(body, q, np, ar, 1, r.imm) {
                return false;
            }
            if k != x + 1 && k != x + 2 {
                return false;
            }
            let sink = k == x + 2;
            if !dests_ok_x(body, p + x + 1, sink, r, nl, hh + np as u64 - ar as u64) {
                return false;
            }
            if !check_straight(body, p, k) {
                return false;
            }
            proof {
                assert(rop_instr(r, body@) == i);
                assert(vop_arity(i) == ar);
                assert(vshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int));
                lemma_vshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int, frame as int);
            }
            true
        },
        Fam::Sel => {
            let x = r.x as usize;
            if x >= k {
                return false;
            }
            let j0 = count_noops(body, p, p + x);
            let np = x - j0;
            let q = p + j0;
            if !matches!(body[p + x], Instr::Select) {
                return false;
            }
            if np > 3 || hh + (np as u64) < 3 || nl64 + hh + np as u64 > room || r.imm > u32::MAX as u64 {
                return false;
            }
            let c = r.imm as u32;
            if !check_prods(body, q, np, nl) || !src_reg_x(body, q, np, 3, 0, nl, h, r.a)
                || !src_reg_x(body, q, np, 3, 1, nl, h, r.b) || !src_reg_x(body, q, np, 3, 2, nl, h, c) {
                return false;
            }
            if k != x + 1 && k != x + 2 {
                return false;
            }
            let sink = k == x + 2;
            if !dests_ok_x(body, p + x + 1, sink, r, nl, hh + np as u64 - 3) {
                return false;
            }
            if !check_straight(body, p, k) {
                return false;
            }
            proof {
                assert(rop_instr(r, body@) == Instr::Select);
                assert(selshape(body@, r, j0 as nat, np as nat, nl as int, h as int));
                lemma_selshape(body@, r, j0 as nat, np as nat, nl as int, h as int, frame as int);
            }
            true
        },
        Fam::StoreRR | Fam::StoreRI => {
            let x = r.x as usize;
            if x >= k || k != x + 1 {
                return false;
            }
            let j0 = count_noops(body, p, p + x);
            let np = x - j0;
            let q = p + j0;
            let i = body[p + x];
            let f = fam_x(r.op);
            if !instr_matches(r.op, r.imm, r.d1, i) || !is_store_x(i) {
                return false;
            }
            if np > 2 || hh + (np as u64) < 2 || nl64 + hh + np as u64 > room {
                return false;
            }
            if !check_prods(body, q, np, nl) || !src_reg_x(body, q, np, 2, 0, nl, h, r.a) {
                return false;
            }
            if matches!(f, Fam::StoreRR) && !src_reg_x(body, q, np, 2, 1, nl, h, r.b) {
                return false;
            }
            if matches!(f, Fam::StoreRI) && !src_imm_x(body, q, np, 2, 1, r.imm) {
                return false;
            }
            if !check_straight(body, p, k) {
                return false;
            }
            proof {
                assert(rop_instr(r, body@) == i);
                assert(sshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int));
                lemma_sshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int, frame as int);
            }
            true
        },
        Fam::Copy | Fam::Const => {
            let j0 = count_noops(body, p, p + k - 1);
            let q = p + j0;
            let rest = k - j0;
            let f = fam_x(r.op);
            let np: usize;
            if prod_x(body[q], nl) {
                np = 1;
                let src_fits = match f {
                    Fam::Copy => match body[q] { Instr::LocalGet(y) => y == r.a && r.a < nl, _ => false },
                    _ => is_const_x(body[q]) && const_val_x(body[q]) == r.imm,
                };
                if !src_fits || rest > 2 || nl64 + hh + 1 > room {
                    return false;
                }
                if !dests_ok_x(body, q + 1, rest == 2, r, nl, hh) {
                    return false;
                }
            } else {
                np = 0;
                if !matches!(f, Fam::Copy) || hh < 1 || r.a as u64 != nl64 + hh - 1 || rest != 1 || nl64 + hh > room {
                    return false;
                }
                if !dests_ok_x(body, q, true, r, nl, hh - 1) {
                    return false;
                }
            }
            if !check_straight(body, p, k) {
                return false;
            }
            proof {
                assert(cshape(body@, r, j0 as nat, np as nat, nl as int, h as int));
                lemma_cshape(body@, r, j0 as nat, np as nat, nl as int, h as int, frame as int);
                let i = rop_instr(r, body@);
                assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store|
                    reff_core(r, i, s, fp, st) == reff_core(r, Instr::Nop, s, fp, st) by {}
            }
            true
        },
        Fam::Skip => {
            let j0 = count_noops(body, p, p + k);
            if j0 != k {
                let dr = match body[p + j0] { Instr::Drop => true, _ => false };
                if j0 + 1 != k || !dr || hh < 1 {
                    return false;
                }
            }
            if nl64 + hh > room || !check_straight(body, p, k) {
                return false;
            }
            proof {
                assert(kshape(body@, r, j0 as nat, h as int));
                lemma_kshape(body@, r, j0 as nat, nl as int, h as int, frame as int);
                let i = rop_instr(r, body@);
                assert forall|s: Seq<u64>, fp: int, st: crate::sem::Store|
                    reff_core(r, i, s, fp, st) == reff_core(r, Instr::Nop, s, fp, st) by {}
            }
            true
        },
        _ => check_branch(m, d, fc, code, r),
    }
}

/// Checks branch operation `j` (at a live position).
#[allow(unused_assignments)]
fn check_branch(m: &Module, d: usize, fc: &FuncCert, code: &Code, r: ROp) -> (ok: bool)
    requires
        rcheck_pre(m, d as nat, *fc, code),
        is_branch(fam(r.op)),
        r.k >= 1,
        r.pc + r.k <= m.funcs@[d as int].body@.len(),
        live(*fc, r.pc as int),
        slots_ok(r, code.frame as nat),
        r.x < r.k,
    ensures ok ==> op_ok(m, d as nat, *fc, code, r),
{
    let body = &m.funcs[d].body;
    let p = r.pc as usize;
    let k = r.k as usize;
    let h = fc.h[p];
    let hh = h as u64;
    let nl = code.n_locals;
    let nl64 = nl as u64;
    let room = code.frame as u64;
    let f = fam_x(r.op);
    let pb = p + k - 1;
    proof {
        assert(body@ == m.funcs@[d as int].body@);
        assert(hgt(*fc, p as int) == h);
    }
    // The final branch, its target, and nothing moved.
    let last_fits = match (f, body[pb]) {
        (Fam::Br, Instr::Br(_)) => true,
        (Fam::Br, _) => false,
        (_, Instr::BrIf(_)) => true,
        _ => false,
    };
    if !last_fits || code.side[pb].arity != 0 || r.d1 as usize >= code.rops.len()
        || code.rops[r.d1 as usize].pc != code.side[pb].pc {
        return false;
    }
    if !check_straight(body, p, k - 1) {
        return false;
    }
    let ghost i = rop_instr(r, body@);
    let np: usize;
    let j0: usize;
    match f {
        Fam::Br => {
            j0 = count_noops(body, p, p + k - 1);
            np = 0;
            if j0 != k - 1 || nl64 + hh > room {
                return false;
            }
        },
        Fam::BrIf | Fam::BrIfZ => {
            let z: usize = if matches!(f, Fam::BrIfZ) { 1 } else { 0 };
            if k < 1 + z {
                return false;
            }
            j0 = count_noops(body, p, p + k - 1 - z);
            let rest = k - 1 - z - j0;
            if rest > 1 {
                return false;
            }
            np = rest;
            let q = p + j0;
            if np == 1 {
                let src_fits = match body[q] { Instr::LocalGet(y) => y == r.a && r.a < nl, _ => false };
                if !src_fits {
                    return false;
                }
            } else if hh < 1 || r.a as u64 != nl64 + hh - 1 {
                return false;
            }
            if z == 1 {
                let eqz = match body[q + np] { Instr::I32Eqz => true, _ => false };
                if !eqz {
                    return false;
                }
            }
            if nl64 + hh + np as u64 > room {
                return false;
            }
        },
        _ => {
            let x = r.x as usize;
            if k < 2 || x != k - 2 {
                return false;
            }
            j0 = count_noops(body, p, p + x);
            np = x - j0;
            let q = p + j0;
            let ix = body[p + x];
            if !instr_matches(r.op, r.imm, r.d1, ix) || !is_cmp_x(ix) {
                return false;
            }
            if np > 2 || hh + (np as u64) < 2 || nl64 + hh + np as u64 > room {
                return false;
            }
            if !check_prods(body, q, np, nl) || !src_reg_x(body, q, np, 2, 0, nl, h, r.a) {
                return false;
            }
            if matches!(f, Fam::BrIfRR) && !src_reg_x(body, q, np, 2, 1, nl, h, r.b) {
                return false;
            }
            if matches!(f, Fam::BrIfRI) && !src_imm_x(body, q, np, 2, 1, r.imm) {
                return false;
            }
            proof { assert(i == ix); }
        },
    }
    proof {
        assert(bshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int));
        lemma_bshape(body@, r, i, j0 as nat, np as nat, nl as int, h as int, code.frame as int);
        assert(straight(m, d as nat, p as int, (k - 1) as nat));
        assert(rop_sem(m, d as nat, *fc, code, r));
    }
    true
}

pub fn entry_at_x(code: &Code, p: usize) -> (r: bool)
    ensures r == entry_at(code, p as int),
{
    if p >= code.entry.len() {
        return false;
    }
    let e = code.entry[p];
    e != NONE && (e as usize) < code.rops.len() && code.rops[e as usize].pc as usize == p
}

/// The per-operation half of `rcode_ok`.
pub open spec fn rops_ok(m: &Module, d: nat, fc: FuncCert, code: &Code) -> bool {
    let len = m.funcs@[d as int].body@.len();
    let n = code.rops@.len();
    &&& 1 <= n < NONE
    &&& code.entry@.len() == len + 1
    &&& code.rops@[0].pc == 0
    &&& code.rops@[n - 1].pc == len
    &&& fam(code.rops@[n - 1].op) is Op
    &&& forall|j: int| 0 <= j < n - 1 ==> (#[trigger] code.rops@[j + 1]).pc == code.rops@[j].pc + code.rops@[j].k
    &&& forall|j: int| 0 <= j < n ==> code.rops@[j].pc <= len
        && code.entry@[#[trigger] code.rops@[j].pc as int] == j
    &&& forall|j: int| 0 <= j < n ==> #[trigger] rop_ok(m, d, fc, code, j)
}

/// Checks the register form of defined function `d` against its body
/// and certificate.
pub fn check_rcode(m: &Module, d: usize, fc: &FuncCert, code: &Code) -> (ok: bool)
    requires rcheck_pre(m, d as nat, *fc, code),
    ensures ok ==> rcode_ok(m, d as nat, *fc, code),
{
    let body = &m.funcs[d].body;
    let len = body.len();
    let n = code.rops.len();
    if n < 1 || n >= NONE as usize || code.entry.len() != len + 1 || code.rops[0].pc != 0
        || code.rops[n - 1].pc as usize != len || !matches!(fam_x(code.rops[n - 1].op), Fam::Op) {
        return false;
    }
    let mut j = 0;
    while j < n
        invariant
            rcheck_pre(m, d as nat, *fc, code), body@ == m.funcs@[d as int].body@,
            n == code.rops@.len(), len == m.funcs@[d as int].body@.len(), code.entry@.len() == len + 1,
            1 <= n < NONE, code.rops@[0].pc == 0, code.rops@[n - 1].pc == len, fam(code.rops@[n - 1].op) is Op,
            0 <= j <= n,
            forall|j2: int| 0 <= j2 < j && j2 < n - 1 ==>
                (#[trigger] code.rops@[j2 + 1]).pc == code.rops@[j2].pc + code.rops@[j2].k,
            forall|j2: int| 0 <= j2 < j ==> code.rops@[j2].pc <= len
                && code.entry@[#[trigger] code.rops@[j2].pc as int] == j2,
            forall|j2: int| 0 <= j2 < j ==> #[trigger] rop_ok(m, d as nat, *fc, code, j2),
        decreases n - j,
    {
        let r = code.rops[j];
        if j + 1 < n && code.rops[j + 1].pc as u64 != r.pc as u64 + r.k as u64 {
            return false;
        }
        if r.pc as usize > len || code.entry[r.pc as usize] as usize != j {
            return false;
        }
        if !check_rop(m, d, fc, code, j) {
            return false;
        }
        j = j + 1;
    }
    let ghost ops = rops_ok(m, d as nat, *fc, code);
    proof { assert(ops); }
    let mut p = 0;
    while p <= len
        invariant
            ops, ops == rops_ok(m, d as nat, *fc, code), body@ == m.funcs@[d as int].body@,
            len == m.funcs@[d as int].body@.len(), code.entry@.len() == len + 1,
            0 <= p <= len + 1,
            forall|p2: int| 0 <= p2 < p && code.entry@[p2] != NONE ==> #[trigger] entry_at(code, p2),
            forall|p2: int| 0 <= p2 < p && p2 < len ==> #[trigger] if_ok(code, m.funcs@[d as int].body@[p2]),
        decreases len + 1 - p,
    {
        if code.entry[p] != NONE && !entry_at_x(code, p) {
            return false;
        }
        if p < len {
            match body[p] {
                Instr::If { else_, end, .. } => {
                    let t = if else_ == end { end as usize } else if (else_ as usize) < len { else_ as usize + 1 } else { return false };
                    if !entry_at_x(code, t) {
                        return false;
                    }
                },
                _ => {},
            }
        }
        p = p + 1;
    }
    let mut l = 0;
    while l < fc.labels.len()
        invariant
            ops == rops_ok(m, d as nat, *fc, code), ops,
            len == m.funcs@[d as int].body@.len(), code.entry@.len() == len + 1,
            forall|p2: int| 0 <= p2 <= len && code.entry@[p2] != NONE ==> #[trigger] entry_at(code, p2),
            forall|p2: int| 0 <= p2 < len ==> #[trigger] if_ok(code, m.funcs@[d as int].body@[p2]),
            0 <= l <= fc.labels@.len(),
            forall|l2: int| 0 <= l2 < l ==> #[trigger] entry_at(code, fc.labels@[l2].cont as int),
        decreases fc.labels@.len() - l,
    {
        if !entry_at_x(code, fc.labels[l].cont as usize) {
            return false;
        }
        l = l + 1;
    }
    check_fast(code)
}

} // verus!

