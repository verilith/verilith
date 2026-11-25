//! The register loop's invariant and one step of it per kind of
//! operation.
//!
//! [`crate::run::execute`] runs a function's register form
//! ([`crate::reg`]), checked against its body by [`crate::rcheck`]. Its
//! invariant `rinv` is the stack interpreter's (`loop_inv`) at the
//! position the current operation starts at. A straight-line operation
//! takes the semantics `k` steps (its run, through
//! `crate::mach::lemma_msteps`); a branch operation takes `k - 1`, then
//! the final `br` or `br_if`; an [`OpCode::Op`] runs its instruction with
//! the stack interpreter's step functions, then continues at the entry of
//! where that took it.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::cert::*;
use crate::preserve::*;
use crate::interp::*;
use crate::interp::Store;
use crate::run::*;
use crate::prims::*;
use crate::exec_num::*;
use crate::mach::*;
use crate::rcheck::*;
use crate::reg::*;
use crate::reg_ops::*;

verus! {

/// The ghost state of the loop: the configuration, the host responses so
/// far, the steps taken, and where the stack interpreter would be.
pub struct GS {
    pub c: Config,
    pub hs: Seq<HostResp>,
    pub n: nat,
    pub pc: usize,
    pub sp: usize,
}

/// Every caller resumes at an operation.
pub open spec fn calls_ret(codes: Seq<Code>, calls: Seq<CallFrame>) -> bool {
    forall|k: int| 0 <= k < calls.len() ==>
        entry_at(&codes[(#[trigger] calls[k]).func as int], calls[k].pc + 1)
}

/// The register loop's invariant: operation `rpc` of function `d` starts
/// where the stack interpreter is.
#[verifier::opaque]
pub open spec fn rinv(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store) -> bool
{
    &&& loop_inv(m, cs, codes, c0, g.hs, g.n, g.c, s, calls, d, g.pc, fp, g.sp, st)
    &&& rpc < codes[d as int].rops@.len()
    &&& codes[d as int].rops@[rpc as int].pc == g.pc
    &&& calls_ret(codes, calls)
}

/// What the step functions need: the invariant, the operation, and the
/// instruction it applies.
pub open spec fn rpre(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, r: ROp, op: Instr) -> bool
{
    &&& rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st)
    &&& r == codes[d as int].rops@[rpc as int]
    &&& op == rop_instr(r, m.funcs@[d as int].body@)
}

/// The result of a straight-line operation: the next ghost state, or a
/// trap and the steps the semantics took to reach it.
pub type RRes = Result<Ghost<GS>, (Trap, Ghost<nat>)>;

#[verifier::opaque]
pub open spec fn rpost(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    len0: nat, calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, res: RRes, acc2: u64) -> bool
{
    &&& s.len() == len0
    &&& match res {
        Ok(g2) => rinv(m, cs, codes, c0, g2@, s, calls, d, (rpc + 1) as usize, fp, st) && g2@.hs == g.hs
            && acc_ok(codes, d, (rpc + 1) as usize, acc2, s, fp),
        Err((t, n2)) => executed(m, c0, g.hs, n2@, Err(t), store_view(st)) && store_wf(st)
            && store_ok(m, store_view(st)),
    }
}

/// What `rpost` says when the step went on: the loop invariant at the next
/// operation. `execute` uses this instead of revealing `rpost`, so its proof
/// does not unfold the invariant's ingredients once per operation code.
pub proof fn lemma_rpost_ok(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    len0: nat, calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, g2: Ghost<GS>, acc2: u64)
    requires
        rpost(m, cs, codes, c0, g, s, len0, calls, d, rpc, fp, st, Ok(g2), acc2),
    ensures
        s.len() == len0,
        rinv(m, cs, codes, c0, g2@, s, calls, d, (rpc + 1) as usize, fp, st),
        g2@.hs == g.hs,
        acc_ok(codes, d, (rpc + 1) as usize, acc2, s, fp),
{
    reveal(rpost);
}

/// What `rpost` says when the step trapped: what `execute` returns.
pub proof fn lemma_rpost_err(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    len0: nat, calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, t: Trap, n2: Ghost<nat>, acc2: u64)
    requires
        rpost(m, cs, codes, c0, g, s, len0, calls, d, rpc, fp, st, Err((t, n2)), acc2),
    ensures
        s.len() == len0,
        executed(m, c0, g.hs, n2@, Err(t), store_view(st)),
        store_wf(st),
        store_ok(m, store_view(st)),
{
    reveal(rpost);
}

/// The accumulator holds slot `a` of operation `rpc`, if it reads it.
#[verifier::opaque]
pub open spec fn acc_ok(codes: Seq<Code>, d: usize, rpc: usize, acc: u64, s: Seq<u64>, fp: usize) -> bool {
    let r = codes[d as int].rops@[rpc as int];
    is_acc(r.op) ==> acc == s[fp + r.a]
}

// ---------------------------------------------------------------------------
// Facts
// ---------------------------------------------------------------------------

pub proof fn lemma_sub_eq(s1: Seq<u64>, s2: Seq<u64>, lim: int, a: int, b: int)
    requires 0 <= a <= b <= lim <= s1.len(), lim <= s2.len(), s1.subrange(0, lim) == s2.subrange(0, lim),
    ensures s1.subrange(a, b) == s2.subrange(a, b),
{
    assert(s1.subrange(a, b) =~= s1.subrange(0, lim).subrange(a, b));
    assert(s2.subrange(a, b) =~= s2.subrange(0, lim).subrange(a, b));
}

/// The operation after one that starts inside the body starts where it
/// ends, and is that position's entry.
pub proof fn lemma_next_op(m: &Module, d: nat, fc: FuncCert, code: &Code, rpc: int)
    requires
        rcode_ok(m, d, fc, code),
        0 <= rpc < code.rops@.len(),
        (code.rops@[rpc].pc as int) < m.funcs@[d as int].body@.len(),
    ensures
        rpc + 1 < code.rops@.len(),
        code.rops@[rpc + 1].pc == code.rops@[rpc].pc + code.rops@[rpc].k,
        code.entry@[code.rops@[rpc + 1].pc as int] == rpc + 1,
        entry_at(code, code.rops@[rpc + 1].pc as int),
{
    let n = code.rops@.len();
    if rpc == n - 1 {
        assert(code.rops@[n - 1].pc == m.funcs@[d as int].body@.len());
    }
    assert(code.rops@[rpc + 1].pc == code.rops@[rpc].pc + code.rops@[rpc].k);
    assert(code.rops@[rpc + 1].pc <= m.funcs@[d as int].body@.len()
        && code.entry@[code.rops@[rpc + 1].pc as int] == rpc + 1);
}

/// A call pushes a caller that resumes at an operation.
pub proof fn lemma_calls_push(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, calls: Seq<CallFrame>, d: usize,
    pc: usize, fp: usize)
    requires
        calls_ret(codes, calls),
        d <= u32::MAX, pc <= u32::MAX,
        entry_at(&codes[d as int], pc + 1),
    ensures calls_ret(codes, calls.push(CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 })),
{
    let c2 = calls.push(CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 });
    assert forall|k: int| 0 <= k < c2.len() implies
        entry_at(&codes[(#[trigger] c2[k]).func as int], c2[k].pc + 1) by {
        if k < calls.len() {
            assert(c2[k] == calls[k]);
        }
    }
}

/// A function starts at its first operation.
pub proof fn lemma_entry0(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, d: nat)
    requires codes_ok(m, cs, codes), d < codes.len(),
    ensures
        entry_at(&codes[d as int], 0),
        codes[d as int].entry@[0] == 0,
{
    assert(code_ok(m, cs, d, &codes[d as int]));
    let code = codes[d as int];
    assert(code.rops@[0].pc <= m.funcs@[d as int].body@.len() && code.entry@[code.rops@[0].pc as int] == 0);
}

/// A branch target of the instruction at `pc` has an entry.
pub proof fn lemma_target_entry(m: &Module, cs: Seq<FuncCert>, d: nat, code: &Code, pc: int, k: nat, pops: nat)
    requires
        certs_ok(m, cs),
        d < m.funcs@.len(),
        rcode_ok(m, d, cs[d as int], code),
        br_ok(cs[d as int], pc, k, pops),
    ensures entry_at(code, target_of(cs[d as int], pc, k).pc as int),
{
    let fc = cs[d as int];
    assert(func_cert_ok(m, d, fc));
    lemma_labels_wf(m, d, fc);
    lemma_nth(fc.labels@, lab(fc, pc), k);
    let id = nth_id(fc.labels@, lab(fc, pc), k)->Some_0;
    assert(entry_at(code, fc.labels@[id as int].cont as int));
}

/// What the invariant says about the current operation.
pub proof fn lemma_rfacts(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store)
    requires rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
    ensures ({
        let code = codes[d as int];
        let fc = cs[d as int];
        let r = code.rops@[rpc as int];
        let len = m.funcs@[d as int].body@.len();
        let nl = code.n_locals as int;
        let h = hgt(fc, g.pc as int) as int;
        &&& certs_ok(m, cs)
        &&& codes_ok(m, cs, codes)
        &&& d < codes.len()
        &&& d < m.funcs@.len()
        &&& code_ok(m, cs, d as nat, &codes[d as int])
        &&& rcode_ok(m, d as nat, fc, &codes[d as int])
        &&& rpc < code.rops@.len()
        &&& r.pc == g.pc
        &&& g.pc <= len
        &&& r.k >= 1
        &&& live(fc, g.pc as int)
        &&& h <= fc.max_height
        &&& nl == n_locals(m, d as nat)
        &&& g.sp == fp + nl + h
        &&& fp + code.frame <= s.len()
        &&& code.frame as int == nl + fc.max_height
        &&& s.len() <= MAX_STACK
        &&& top(g.c).func == d
        &&& top(g.c).pc == g.pc
        &&& g.c.store == store_view(st)
        &&& store_wf(st)
        &&& store_ok(m, store_view(st))
        &&& mpre(m, cs, codes, g.c, s, calls, fp as int, g.sp as int)
        &&& (fam(r.op) is Op ==> r.a as int == nl + h)
        &&& (fam(r.op) is Op && (g.pc as int) < len ==> r.k == 1)
        &&& (!(fam(r.op) is Op) ==> (g.pc as int) < len && slots_ok(r, code.frame as nat)
                && rop_sem(m, d as nat, fc, &codes[d as int], r))
        &&& run(m, c0, g.hs, g.n) == Outcome::Running(g.c)
        &&& inv(m, cs, g.c)
        &&& mach_ok(m, s, calls, fp as int, g.sp as int, g.c)
        &&& calls.len() <= MAX_CALLS
        &&& calls_fit(codes, calls, s.len())
        &&& calls_ret(codes, calls)
        &&& code.rops@.len() < NONE
        &&& (!(fam(r.op) is Op) ==> r.x < r.k && r.pc + r.k <= len
                && code.ops@[r.pc + r.x] == m.funcs@[d as int].body@[r.pc + r.x])
    }),
{
    reveal(rinv);
    reveal(loop_inv);
    let code = codes[d as int];
    let fc = cs[d as int];
    let r = code.rops@[rpc as int];
    let len = m.funcs@[d as int].body@.len();
    let n = code.rops@.len();
    let f = top(g.c);
    assert(code_ok(m, cs, d as nat, &codes[d as int]));
    assert(frame_at(m, cs, f));
    assert(func_cert_ok(m, d as nat, fc));
    assert(rop_ok(m, d as nat, fc, &codes[d as int], rpc as int));
    assert(f.stack.len() == hgt(fc, g.pc as int));
    assert(f.stack == s.subrange(fp + n_locals(m, d as nat), g.sp as int));
    assert(hgt(fc, g.pc as int) <= fc.max_height);
    if g.pc == len {
        assert(code.entry@[code.rops@[n - 1].pc as int] == n - 1);
        assert(code.entry@[code.rops@[rpc as int].pc as int] == rpc);
    }
    if !(fam(r.op) is Op) {
        assert(r.pc + r.k <= len);
        assert(code.ops@[r.pc + r.x] == m.funcs@[d as int].body@[r.pc + r.x]);
    }
}

// ---------------------------------------------------------------------------
// Straight-line operations
// ---------------------------------------------------------------------------

/// A straight-line operation that computed `s2` and `st2` takes the
/// semantics through its run.
pub proof fn lemma_rnext(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, s2: Seq<u64>, st2: &Store) -> (g2: GS)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        !(fam(codes[d as int].rops@[rpc as int].op) is Op),
        !is_branch(fam(codes[d as int].rops@[rpc as int].op)),
        reff(codes[d as int].rops@[rpc as int], rop_instr(codes[d as int].rops@[rpc as int], m.funcs@[d as int].body@),
            s, fp as int, store_view(st)) == RS::Next(s2, store_view(st2)),
        store_wf(st2),
    ensures
        rinv(m, cs, codes, c0, g2, s2, calls, d, (rpc + 1) as usize, fp, st2),
        g2.hs == g.hs,
        s2.len() == s.len(),
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
    let code = codes[d as int];
    let fc = cs[d as int];
    let r = code.rops@[rpc as int];
    let body = m.funcs@[d as int].body@;
    let nl = code.n_locals as int;
    let h = hgt(fc, g.pc as int) as int;
    let k = r.k as nat;
    let i = rop_instr(r, body);
    let st0 = g.c.store;
    let ms = msteps(body, g.pc as int, k, s, fp as int, fp + nl + h, st0);
    assert(agree(reff(r, i, s, fp as int, st0), ms));
    lemma_msteps(m, cs, codes, g.c, s, calls, fp as int, g.sp as int, k);
    match ms {
        MS::Next(s3, sp3, st3) => {
            let c2 = run(m, g.c, Seq::empty(), k)->Running_0;
            lemma_mach_ext(m, s3, s2, calls, fp as int, sp3, c2);
            lemma_run_concat(m, c0, g.hs, g.n, g.c, k);
            lemma_next_op(m, d as nat, fc, &codes[d as int], rpc as int);
            let g2 = GS { c: c2, hs: g.hs, n: g.n + k, pc: (g.pc + k) as usize, sp: sp3 as usize };
            reveal(loop_inv);
            assert(loop_inv(m, cs, codes, c0, g2.hs, g2.n, g2.c, s2, calls, d, g2.pc, fp, g2.sp, st2));
            reveal(rinv);
            g2
        },
        MS::Trap(..) => {
            assert(false);
            arbitrary()
        },
    }
}

/// A straight-line operation that trapped: so does the semantics.
pub proof fn lemma_rtrap(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, t: Trap) -> (n2: nat)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        !(fam(codes[d as int].rops@[rpc as int].op) is Op),
        !is_branch(fam(codes[d as int].rops@[rpc as int].op)),
        reff(codes[d as int].rops@[rpc as int], rop_instr(codes[d as int].rops@[rpc as int], m.funcs@[d as int].body@),
            s, fp as int, store_view(st)) == RS::Trap(t, store_view(st)),
    ensures
        executed(m, c0, g.hs, n2, Err(t), store_view(st)),
        store_wf(st),
        store_ok(m, store_view(st)),
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
    let code = codes[d as int];
    let fc = cs[d as int];
    let r = code.rops@[rpc as int];
    let body = m.funcs@[d as int].body@;
    let nl = code.n_locals as int;
    let h = hgt(fc, g.pc as int) as int;
    let k = r.k as nat;
    let i = rop_instr(r, body);
    let st0 = g.c.store;
    let ms = msteps(body, g.pc as int, k, s, fp as int, fp + nl + h, st0);
    assert(agree(reff(r, i, s, fp as int, st0), ms));
    lemma_msteps(m, cs, codes, g.c, s, calls, fp as int, g.sp as int, k);
    lemma_run_concat(m, c0, g.hs, g.n, g.c, k);
    reveal(executed);
    g.n + k
}

/// The current operation exists, and the one after it can be named.
pub proof fn lemma_rpc(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store)
    requires rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
    ensures rpc < codes[d as int].rops@.len() < NONE,
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
}

/// The slots of the current operation are inside the stack.
pub proof fn lemma_rslots(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        !(fam(codes[d as int].rops@[rpc as int].op) is Op),
    ensures ({
        let r = codes[d as int].rops@[rpc as int];
        &&& slots_ok(r, codes[d as int].frame as nat)
        &&& fp + codes[d as int].frame <= s.len()
        &&& s.len() <= MAX_STACK
        &&& store_wf(st)
        &&& codes[d as int].rops@.len() < NONE
        &&& rpc < codes[d as int].rops@.len()
    }),
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
}


/// After a value operation put `v` in its destinations, the accumulator
/// `v` is right for the next operation; after any other straight-line
/// operation, the next one does not read it.
pub proof fn lemma_acc_next(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, s2: Seq<u64>, v: u64)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        !(fam(codes[d as int].rops@[rpc as int].op) is Op),
        !is_branch(fam(codes[d as int].rops@[rpc as int].op)),
        is_val(fam(codes[d as int].rops@[rpc as int].op)) ==>
            s2[fp + codes[d as int].rops@[rpc as int].d1] == v && s2[fp + codes[d as int].rops@[rpc as int].d2] == v,
    ensures
        rpc + 1 < codes[d as int].rops@.len(),
        acc_ok(codes, d, (rpc + 1) as usize, v, s2, fp),
        !is_val(fam(codes[d as int].rops@[rpc as int].op)) ==> !is_acc(codes[d as int].rops@[rpc + 1].op),
{
    reveal(acc_ok);
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
    lemma_next_op(m, d as nat, cs[d as int], &codes[d as int], rpc as int);
    reveal(fast_rules);
    let code = codes[d as int];
    if is_acc(code.rops@[rpc + 1].op) {
        assert(acc_src(&codes[d as int], rpc + 1));
    }
}

/// The first operation does not read the accumulator.
pub proof fn lemma_acc_start(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, fp: usize, st: &Store)
    requires rinv(m, cs, codes, c0, g, s, calls, d, 0, fp, st),
    ensures forall|a: u64| acc_ok(codes, d, 0, a, s, fp),
{
    reveal(acc_ok);
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, 0, fp, st);
    reveal(fast_rules);
    if is_acc(codes[d as int].rops@[0].op) {
        assert(acc_src(&codes[d as int], 0));
    }
}

/// A branch's target and fall-through do not read the accumulator, and
/// `d2` is the target's byte offset.
pub proof fn lemma_acc_br(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        is_branch(fam(codes[d as int].rops@[rpc as int].op)),
    ensures ({
        let code = codes[d as int];
        let r = code.rops@[rpc as int];
        &&& (r.d1 as int) < code.rops@.len()
        &&& !is_acc(code.rops@[r.d1 as int].op)
        &&& r.d2 as int == r.d1 as int * ROP_SIZE as int
        &&& rpc + 1 < code.rops@.len()
        &&& !is_acc(code.rops@[rpc + 1].op)
    }),
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
    lemma_next_op(m, d as nat, cs[d as int], &codes[d as int], rpc as int);
    reveal(fast_rules);
    let code = codes[d as int];
    assert(br_fast(&codes[d as int], rpc as int));
    if is_acc(code.rops@[rpc + 1].op) {
        assert(acc_src(&codes[d as int], rpc + 1));
    }
}

/// The accumulator for operation `rpc`, wherever the loop came from:
/// slot `a` if it reads it.
#[inline(always)]
pub fn r_acc_fix(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp, acc: u64) -> (a: u64)
    requires
        rinv(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st),
        *r == codes[d as int].rops@[rpc as int],
    ensures acc_ok(codes, d, rpc, a, stack@, fp),
{
    proof { reveal(acc_ok); }
    if is_acc_x(r.op) {
        proof {
            lemma_acc_fam(r.op);
            lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        }
        sget(stack, fp + r.a as usize)
    } else {
        acc
    }
}

// ---------------------------------------------------------------------------
// Branch operations
// ---------------------------------------------------------------------------

#[verifier::rlimit(300)]
/// A branch operation: its straight-line part, then the branch (if
/// `taken`) to operation `r.d1`, or on to the next operation.
pub proof fn lemma_rbranch(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store, taken: bool) -> (g2: GS)
    requires
        rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
        is_branch(fam(codes[d as int].rops@[rpc as int].op)),
        taken == rcond(codes[d as int].rops@[rpc as int],
            rop_instr(codes[d as int].rops@[rpc as int], m.funcs@[d as int].body@), s, fp as int),
    ensures
        rinv(m, cs, codes, c0, g2, s, calls, d,
            if taken { codes[d as int].rops@[rpc as int].d1 as usize } else { (rpc + 1) as usize }, fp, st),
        g2.hs == g.hs,
{
    lemma_rfacts(m, cs, codes, c0, g, s, calls, d, rpc, fp, st);
    let code = codes[d as int];
    let fc = cs[d as int];
    let r = code.rops@[rpc as int];
    let body = m.funcs@[d as int].body@;
    let p = g.pc as int;
    let k = r.k as nat;
    let pb = p + k - 1;
    let nl = code.n_locals as int;
    let h = hgt(fc, p) as int;
    let i = rop_instr(r, body);
    let fm = fam(r.op);
    let pops: int = if fm is Br { 0 } else { 1 };
    let st0 = g.c.store;
    // The straight-line part.
    let ms = msteps(body, p, (k - 1) as nat, s, fp as int, fp + nl + h, st0);
    assert(agree_br(rcond(r, i, s, fp as int), s, st0, ms, pops));
    lemma_msteps(m, cs, codes, g.c, s, calls, fp as int, g.sp as int, (k - 1) as nat);
    let (s1, sp1) = match ms {
        MS::Next(s1, sp1, _) => (s1, sp1),
        MS::Trap(..) => { assert(false); (s, 0) },
    };
    let c1 = run(m, g.c, Seq::empty(), (k - 1) as nat)->Running_0;
    lemma_run_concat(m, c0, g.hs, g.n, g.c, (k - 1) as nat);
    let n1 = g.n + (k - 1) as nat;
    assert(run(m, c0, g.hs, n1) == Outcome::Running(c1));
    // The branch.
    assert(pre(m, cs, codes, c1, s1, calls, fp as int, sp1));
    lemma_facts(m, cs, codes, c1, s1, calls, fp as int, sp1);
    lemma_step_instr(m, c1);
    reveal(step_instr);
    let f = top(c1);
    let base = fp + nl;
    assert(cur(m, c1) == body[pb]);
    assert(code_ok(m, cs, d as nat, &codes[d as int]));
    assert(live(fc, pb));
    assert(side_ok(m, fc, code.side@, code.table@, pb, body[pb]));
    assert(f.locals == s1.subrange(fp as int, base));
    lemma_sub_eq(s1, s, sp1 - pops, 0, fp as int);
    lemma_sub_eq(s1, s, sp1 - pops, fp as int, base);
    let (gf, sp2): (Frame, int) = if fm is Br {
        let l = body[pb]->Br_0;
        assert(f.stack.subrange(0, f.stack.len() as int) =~= f.stack);
        assert(popn(f, 0) == f);
        lemma_br_frame(m, cs, c1, f, l as nat, 0);
        let t = target_of(fc, pb, l as nat);
        let gf = exit_label(f, l as nat, t.pc as nat)->Some_0;
        let sp2 = base + t.height;
        assert(gf.stack =~= f.stack.subrange(0, t.height as int));
        assert(f.stack.subrange(0, t.height as int) =~= s1.subrange(base, sp2));
        lemma_sub_eq(s1, s, sp1, base, sp2);
        (gf, sp2)
    } else {
        let l = body[pb]->BrIf_0;
        lemma_peek(s1, base, sp1, 0);
        lemma_pop(s1, base, sp1, 1);
        let f2 = popn(f, 1);
        if taken {
            lemma_br_frame(m, cs, c1, f2, l as nat, 1);
            let t = target_of(fc, pb, l as nat);
            let gf = exit_label(f2, l as nat, t.pc as nat)->Some_0;
            let sp2 = base + t.height;
            assert(gf.stack =~= f2.stack.subrange(0, t.height as int));
            assert(f2.stack.subrange(0, t.height as int) =~= s1.subrange(base, sp2));
            lemma_sub_eq(s1, s, sp1 - 1, base, sp2);
            (gf, sp2)
        } else {
            let gf = adv(f2);
            lemma_sub_eq(s1, s, sp1 - 1, base, sp1 - 1);
            (gf, sp1 - 1)
        }
    };
    assert(step(m, c1) == next(c1, gf));
    lemma_mach_top(m, s1, s, calls, fp as int, sp1, c1, gf, sp2);
    lemma_advance(m, cs, c0, g.hs, n1, c1);
    let c2 = with_top(c1, gf);
    if taken {
        assert(code.rops@[r.d1 as int].pc == code.side@[pb].pc);
    } else {
        lemma_next_op(m, d as nat, fc, &codes[d as int], rpc as int);
    }
    let g2 = GS { c: c2, hs: g.hs, n: n1 + 1, pc: gf.pc as usize, sp: sp2 as usize };
    reveal(loop_inv);
    assert(loop_inv(m, cs, codes, c0, g2.hs, g2.n, g2.c, s, calls, d, g2.pc, fp, g2.sp, st));
    reveal(rinv);
    g2
}

// ---------------------------------------------------------------------------
// The interpreter's side of each operation
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn r_copy(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, pre: bool, acc: &mut u64)
    -> (g2: Ghost<GS>)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        fam(r.op) is Copy,
        pre == has_pre(r.op),
    ensures
        rinv(m, cs, codes, c0, g2@, final(stack)@, calls, d, (rpc + 1) as usize, fp, st),
        acc_ok(codes, d, (rpc + 1) as usize, *final(acc), final(stack)@, fp),
        g2@.hs == g.hs,
        final(stack)@.len() == old(stack)@.len(),
{
    proof { reveal(acc_ok); }
    proof { lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let v = sget(stack, fp + r.a as usize);
    sset(stack, fp + r.d1 as usize, v);
    sset(stack, fp + r.d2 as usize, v);
    proof {
        assert(reff(*r, rop_instr(*r, m.funcs@[d as int].body@), s0, fp as int, store_view(st))
            == RS::Next(stack@, store_view(st)));
    }
    *acc = v;
    proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
    Ghost(g2)
}

/// A `select` of slot `a` or `b` on the condition in slot `imm`.
#[inline(always)]
pub fn r_sel(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, acc: &mut u64)
    -> (g2: Ghost<GS>)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        fam(r.op) is Sel,
        !has_pre(r.op),
    ensures
        rinv(m, cs, codes, c0, g2@, final(stack)@, calls, d, (rpc + 1) as usize, fp, st),
        acc_ok(codes, d, (rpc + 1) as usize, *final(acc), final(stack)@, fp),
        g2@.hs == g.hs,
        final(stack)@.len() == old(stack)@.len(),
{
    proof { reveal(acc_ok); }
    proof { lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    let ghost s0 = stack@;
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let cnd = sget(stack, fp + r.imm as usize);
    let v = if lo(cnd) != 0 { sget(stack, fp + r.a as usize) } else { sget(stack, fp + r.b as usize) };
    sset(stack, fp + r.d1 as usize, v);
    sset(stack, fp + r.d2 as usize, v);
    proof {
        assert(reff(*r, rop_instr(*r, m.funcs@[d as int].body@), s0, fp as int, store_view(st))
            == RS::Next(stack@, store_view(st)));
    }
    *acc = v;
    proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
    Ghost(g2)
}

#[inline(always)]
pub fn r_const(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, acc: &mut u64)
    -> (g2: Ghost<GS>)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        r.op == OpCode::Const,
    ensures
        rinv(m, cs, codes, c0, g2@, final(stack)@, calls, d, (rpc + 1) as usize, fp, st),
        acc_ok(codes, d, (rpc + 1) as usize, *final(acc), final(stack)@, fp),
        g2@.hs == g.hs,
        final(stack)@.len() == old(stack)@.len(),
{
    proof { reveal(acc_ok); }
    proof { lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); reveal(has_pre); }
    let ghost s0 = stack@;
    sset(stack, fp + r.d1 as usize, r.imm);
    sset(stack, fp + r.d2 as usize, r.imm);
    proof {
        assert(reff(*r, rop_instr(*r, m.funcs@[d as int].body@), s0, fp as int, store_view(st))
            == RS::Next(stack@, store_view(st)));
    }
    *acc = r.imm;
    proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, r.imm); }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
    Ghost(g2)
}

#[inline(always)]
pub fn r_skip(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp, acc: u64) -> (g2: Ghost<GS>)
    requires
        rpre(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        r.op == OpCode::Skip,
    ensures
        rinv(m, cs, codes, c0, g2@, stack@, calls, d, (rpc + 1) as usize, fp, st),
        acc_ok(codes, d, (rpc + 1) as usize, acc, stack@, fp),
        g2@.hs == g.hs,
{
    proof { reveal(acc_ok); }
    proof {
        lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        reveal(has_pre);
        assert(reff(*r, rop_instr(*r, m.funcs@[d as int].body@), stack@, fp as int, store_view(st))
            == RS::Next(stack@, store_view(st)));
        lemma_acc_next(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, stack@, acc);
    }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, stack@, st); }
    Ghost(g2)
}

/// A unary operation applying `op`.
#[inline(always)]
pub fn r_un(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is Un,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, st, res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
    }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let x = if ua { *acc } else { sget(stack, fp + r.a as usize) };
    match exec_unop(op, x) {
        Ok(v) => {
            sset(stack, fp + r.d1 as usize, v);
            sset(stack, fp + r.d2 as usize, v);
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Next(stack@, store_view(st))); }
            *acc = v;
            proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
            let ghost mut g2 = g;
            proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
            Ok(Ghost(g2))
        },
        Err(t) => {
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Trap(t, store_view(st))); }
            let ghost mut n2: nat = 0;
            proof { n2 = lemma_rtrap(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, t); }
            Err((t, Ghost(n2)))
        },
    }
}

/// A binary operation on two slots.
#[inline(always)]
pub fn r_bin_rr(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is BinRR,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, st, res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
    }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let x = if ua { *acc } else { sget(stack, fp + r.a as usize) };
    let y = sget(stack, fp + r.b as usize);
    match exec_binop(op, x, y) {
        Ok(v) => {
            sset(stack, fp + r.d1 as usize, v);
            sset(stack, fp + r.d2 as usize, v);
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Next(stack@, store_view(st))); }
            *acc = v;
            proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
            let ghost mut g2 = g;
            proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
            Ok(Ghost(g2))
        },
        Err(t) => {
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Trap(t, store_view(st))); }
            let ghost mut n2: nat = 0;
            proof { n2 = lemma_rtrap(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, t); }
            Err((t, Ghost(n2)))
        },
    }
}

/// A binary operation on a slot and an immediate.
#[inline(always)]
pub fn r_bin_ri(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is BinRI,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, st, res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
    }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let x = if ua { *acc } else { sget(stack, fp + r.a as usize) };
    match exec_binop(op, x, r.imm) {
        Ok(v) => {
            sset(stack, fp + r.d1 as usize, v);
            sset(stack, fp + r.d2 as usize, v);
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Next(stack@, store_view(st))); }
            *acc = v;
            proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
            let ghost mut g2 = g;
            proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
            Ok(Ghost(g2))
        },
        Err(t) => {
            proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Trap(t, store_view(st))); }
            let ghost mut n2: nat = 0;
            proof { n2 = lemma_rtrap(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, t); }
            Err((t, Ghost(n2)))
        },
    }
}

/// A load.
#[inline(always)]
pub fn r_load(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is Load,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, st, res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
    }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let (nb, signed, is64, off) = load_kind_x(op);
    let ea = lo(if ua { *acc } else { sget(stack, fp + r.a as usize) }) as u64 + off as u64;
    if ea + nb as u64 > st.mem.len() as u64 {
        proof {
            assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Trap(Trap::MemoryOutOfBounds, store_view(st)));
        }
        let ghost mut n2: nat = 0;
        proof { n2 = lemma_rtrap(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, Trap::MemoryOutOfBounds); }
        return Err((Trap::MemoryOutOfBounds, Ghost(n2)));
    }
    let v = load(&st.mem, ea as usize, nb);
    proof { lemma_le_bound(st.mem@, ea as int, nb as nat); }
    let v = load_res(v, nb, signed, is64);
    sset(stack, fp + r.d1 as usize, v);
    sset(stack, fp + r.d2 as usize, v);
    proof { assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Next(stack@, store_view(st))); }
    *acc = v;
    proof { lemma_acc_next(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, v); }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, stack@, st); }
    Ok(Ghost(g2))
}

/// A store of slot `b`.
#[inline(always)]
pub fn r_store_rr(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &mut Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, old(st), *r, op),
        fam(r.op) is StoreRR,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, final(st), res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_acc_next(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, stack@, *acc);
    }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    let v = sget(stack, fp + r.b as usize);
    r_store(Ghost(m), Ghost(cs), Ghost(codes), Ghost(calls), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), Ghost(s0),
        op, stack, fp, st, r, v, *acc, ua)
}

/// A store of the immediate.
#[inline(always)]
pub fn r_store_ri(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, op: Instr, stack: &mut Vec<u64>, fp: usize, st: &mut Store, r: &ROp, pre: bool,
    acc: &mut u64) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, old(stack)@, calls, d, rpc, fp, old(st), *r, op),
        fam(r.op) is StoreRI,
        pre == has_pre(r.op),
        acc_ok(codes, d, rpc, *old(acc), old(stack)@, fp),
    ensures rpost(m, cs, codes, c0, g, final(stack)@, old(stack)@.len(), calls, d, rpc, fp, final(st), res, *final(acc)),
{
    proof { reveal(rpost); }
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof { lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_acc_next(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, stack@, *acc); }
    let ghost s0 = stack@;
    if pre {
        let pv = sget(stack, fp + r.pa as usize);
        sset(stack, fp + r.pd as usize, pv);
    }
    proof { assert(stack@ =~= pre_s(*r, s0, fp as int)); }
    r_store(Ghost(m), Ghost(cs), Ghost(codes), Ghost(calls), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), Ghost(s0),
        op, stack, fp, st, r, r.imm, *acc, ua)
}

#[inline(always)]
fn r_store(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, Ghost(s0): Ghost<Seq<u64>>, op: Instr, stack: &Vec<u64>, fp: usize, st: &mut Store,
    r: &ROp, v: u64, acc: u64, ua: bool) -> (res: RRes)
    requires
        rpre(m, cs, codes, c0, g, s0, calls, d, rpc, fp, old(st), *r, op),
        stack@ == pre_s(*r, s0, fp as int),
        fam(r.op) is StoreRR || fam(r.op) is StoreRI,
        store_kind(op) is Some,
        v == if fam(r.op) is StoreRR { stack@[fp + r.b] } else { r.imm },
        ua ==> acc == stack@[fp + r.a],
        !is_acc(codes[d as int].rops@[rpc + 1].op),
    ensures rpost(m, cs, codes, c0, g, stack@, s0.len(), calls, d, rpc, fp, final(st), res, acc),
{
    proof { reveal(rpost); }
    proof { reveal(acc_ok); }
    proof { lemma_rfacts(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st); }
    let ghost st0 = *st;
    let (nb, off) = store_kind_x(op);
    let ea = lo(if ua { acc } else { sget(stack, fp + r.a as usize) }) as u64 + off as u64;
    if ea + nb as u64 > st.mem.len() as u64 {
        proof {
            assert(reff(*r, op, s0, fp as int, store_view(st)) == RS::Trap(Trap::MemoryOutOfBounds, store_view(st)));
        }
        let ghost mut n2: nat = 0;
        proof { n2 = lemma_rtrap(m, cs, codes, c0, g, s0, calls, d, rpc, fp, st, Trap::MemoryOutOfBounds); }
        return Err((Trap::MemoryOutOfBounds, Ghost(n2)));
    }
    let ghost m1 = st.mem@;
    store(&mut st.mem, ea as usize, v, nb);
    proof {
        lemma_write_le_len(m1, ea as int, store_value(v, nb as nat), nb as nat);
        let s2 = crate::sem::Store { mem: st.mem@, ..store_view(&st0) };
        assert(store_view(st) == s2);
        assert(reff(*r, op, s0, fp as int, store_view(&st0)) == RS::Next(stack@, store_view(st)));
    }
    let ghost mut g2 = g;
    proof { g2 = lemma_rnext(m, cs, codes, c0, g, s0, calls, d, rpc, fp, &st0, stack@, st); }
    Ok(Ghost(g2))
}

/// `br_if` on slot `a` (`z`: `i32.eqz; br_if`), or `br`; returns the next
/// operation.
#[inline(always)]
pub fn r_brif<'a>(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    rpc: usize, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp, z: bool,
    rops: &'a [ROp], cur: Cur<'a>, acc: u64) -> (res: (usize, Cur<'a>, Ghost<GS>))
    requires
        rpre(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        if z { fam(r.op) is BrIfZ } else { fam(r.op) is BrIf },
        rops@ == codes[d as int].rops@, cur.seq() == rops@, cur.idx() == rpc as int,
        acc_ok(codes, d, rpc, acc, stack@, fp),
    ensures
        rinv(m, cs, codes, c0, res.2@, stack@, calls, d, res.0, fp, st), res.2@.hs == g.hs,
        res.1.idx() == res.0 as int, res.1.seq() == rops@,
        acc_ok(codes, d, res.0, acc, stack@, fp),
{
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof { lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    let taken = (lo(if ua { acc } else { sget(stack, fp + r.a as usize) }) == 0) == z;
    let ghost mut g2 = g;
    proof { g2 = lemma_rbranch(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, taken); }
    proof { lemma_acc_br(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    if taken { (r.d1 as usize, cur_off(rops, r.d1, r.d2), Ghost(g2)) } else { (rpc + 1, cur_next(cur), Ghost(g2)) }
}

/// `br`; returns the next operation.
#[inline(always)]
pub fn r_br<'a>(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    rpc: usize, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp,
    rops: &'a [ROp], cur: Cur<'a>, acc: u64) -> (res: (usize, Cur<'a>, Ghost<GS>))
    requires
        rpre(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, *r, rop_instr(*r, m.funcs@[d as int].body@)),
        r.op == OpCode::Br,
        rops@ == codes[d as int].rops@, cur.seq() == rops@, cur.idx() == rpc as int,
        acc_ok(codes, d, rpc, acc, stack@, fp),
    ensures
        rinv(m, cs, codes, c0, res.2@, stack@, calls, d, res.0, fp, st), res.2@.hs == g.hs,
        res.1.idx() == res.0 as int, res.1.seq() == rops@,
        acc_ok(codes, d, res.0, acc, stack@, fp),
{
    proof { reveal(acc_ok); }
    let ghost mut g2 = g;
    proof { g2 = lemma_rbranch(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, true); }
    proof { lemma_acc_br(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    (r.d1 as usize, cur_off(rops, r.d1, r.d2), Ghost(g2))
}

/// A comparison of two slots, then `br_if`.
#[inline(always)]
pub fn r_brif_rr<'a>(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    rpc: usize, op: Instr, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp,
    rops: &'a [ROp], cur: Cur<'a>, acc: u64) -> (res: (usize, Cur<'a>, Ghost<GS>))
    requires
        rpre(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is BrIfRR,
        rops@ == codes[d as int].rops@, cur.seq() == rops@, cur.idx() == rpc as int,
        acc_ok(codes, d, rpc, acc, stack@, fp),
    ensures
        rinv(m, cs, codes, c0, res.2@, stack@, calls, d, res.0, fp, st), res.2@.hs == g.hs,
        res.1.idx() == res.0 as int, res.1.seq() == rops@,
        acc_ok(codes, d, res.0, acc, stack@, fp),
{
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_cmp_any(op);
    }
    let x = if ua { acc } else { sget(stack, fp + r.a as usize) };
    let y = sget(stack, fp + r.b as usize);
    let taken = cmp_x(op, x, y);
    let ghost mut g2 = g;
    proof { g2 = lemma_rbranch(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, taken); }
    proof { lemma_acc_br(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    if taken { (r.d1 as usize, cur_off(rops, r.d1, r.d2), Ghost(g2)) } else { (rpc + 1, cur_next(cur), Ghost(g2)) }
}

/// A comparison of a slot with the immediate, then `br_if`.
#[inline(always)]
pub fn r_brif_ri<'a>(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    rpc: usize, op: Instr, stack: &Vec<u64>, fp: usize, st: &Store, r: &ROp,
    rops: &'a [ROp], cur: Cur<'a>, acc: u64) -> (res: (usize, Cur<'a>, Ghost<GS>))
    requires
        rpre(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, *r, op),
        fam(r.op) is BrIfRI,
        rops@ == codes[d as int].rops@, cur.seq() == rops@, cur.idx() == rpc as int,
        acc_ok(codes, d, rpc, acc, stack@, fp),
    ensures
        rinv(m, cs, codes, c0, res.2@, stack@, calls, d, res.0, fp, st), res.2@.hs == g.hs,
        res.1.idx() == res.0 as int, res.1.seq() == rops@,
        acc_ok(codes, d, res.0, acc, stack@, fp),
{
    let ua = is_acc_x(r.op);
    proof { if ua { lemma_acc_fam(r.op); } }
    proof { reveal(acc_ok); }
    proof {
        lemma_rslots(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st);
        lemma_cmp_any(op);
    }
    let x = if ua { acc } else { sget(stack, fp + r.a as usize) };
    let taken = cmp_x(op, x, r.imm);
    let ghost mut g2 = g;
    proof { g2 = lemma_rbranch(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st, taken); }
    proof { lemma_acc_br(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    if taken { (r.d1 as usize, cur_off(rops, r.d1, r.d2), Ghost(g2)) } else { (rpc + 1, cur_next(cur), Ghost(g2)) }
}

/// Comparisons are binary operations.
pub proof fn lemma_cmp_any(op: Instr)
    ensures is_cmp(op) ==> is_binop(op),
{
}

/// A comparison's truth value, as `br_if` tests it.
#[inline(always)]
pub fn cmp_x(op: Instr, a: u64, b: u64) -> (r: bool)
    requires is_cmp(op),
    ensures r == (lo32(eval_binop(op, a, b)->Ok_0) != 0),
{
    match exec_binop(op, a, b) {
        Ok(r) => lo(r) != 0,
        Err(_) => false,
    }
}

/// The loop starts at the first operation.
pub proof fn lemma_rinit(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, fp: usize, st: &Store)
    requires
        loop_inv(m, cs, codes, c0, g.hs, g.n, g.c, s, calls, d, g.pc, fp, g.sp, st),
        g.pc == 0,
        calls.len() == 0,
    ensures rinv(m, cs, codes, c0, g, s, calls, d, 0, fp, st),
{
    reveal(loop_inv);
    lemma_entry0(m, cs, codes, d as nat);
    assert(code_ok(m, cs, d as nat, &codes[d as int]));
    reveal(rinv);
}

/// The instruction a generic operation applies, from the body.
#[inline(always)]
pub fn r_instr(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    Ghost(calls): Ghost<Seq<CallFrame>>, Ghost(c0): Ghost<Config>, Ghost(g): Ghost<GS>, Ghost(d): Ghost<usize>,
    Ghost(rpc): Ghost<usize>, stack: &Vec<u64>, fp: usize, st: &Store, code: &Code, r: &ROp) -> (op: Instr)
    requires
        rinv(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st),
        *code == codes[d as int],
        *r == codes[d as int].rops@[rpc as int],
        !(fam(r.op) is Op),
        spec_instr(r.op, r.imm, r.d1) is None,
    ensures op == rop_instr(*r, m.funcs@[d as int].body@),
{
    proof { lemma_rfacts(m, cs, codes, c0, g, stack@, calls, d, rpc, fp, st); }
    vget(&code.ops, r.pc as usize + r.x as usize)
}

} // verus!
