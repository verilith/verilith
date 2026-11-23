//! The flat machine's view of straight-line code: what a run of
//! instructions that stay in their frame does to the value stack and the
//! store, and the proof that the semantics does the same in as many steps.
//!
//! A register operation (see [`crate::reg`]) stands for such a run. Its
//! correctness is stated against [`msteps`] (an equation between two
//! functions of the stack, checked once per operation when the function is
//! compiled), and [`lemma_msteps`] carries that over to the semantics.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::cert::*;
use crate::preserve::*;
use crate::interp::*;
use crate::run::*;

verus! {

/// The result of straight-line code on the flat machine: the value
/// stack, the stack pointer and the store, or a trap.
pub enum MS {
    Next(Seq<u64>, int, crate::sem::Store),
    Trap(Trap, crate::sem::Store),
}

/// Instructions that stay in their frame and continue at the next
/// position (or trap).
pub open spec fn simple(i: Instr) -> bool {
    is_unop(i) || is_binop(i) || load_kind(i) is Some || store_kind(i) is Some
    || i is Nop || i is Block || i is Loop || i is End || i is Drop || i is Select
    || i is LocalGet || i is LocalSet || i is LocalTee
    || i is I32Const || i is I64Const || i is F32Const || i is F64Const
}

pub open spec fn is_const(i: Instr) -> bool {
    i is I32Const || i is I64Const || i is F32Const || i is F64Const
}

/// The slot a constant pushes.
pub open spec fn const_val(i: Instr) -> u64 {
    match i {
        Instr::I32Const(v) => v as u64,
        Instr::I64Const(v) => v,
        Instr::F32Const(v) => v as u64,
        Instr::F64Const(v) => v,
        _ => 0,
    }
}

/// Operands a value instruction (unary, binary, load) takes.
pub open spec fn vop_arity(i: Instr) -> nat {
    if is_binop(i) { 2 } else { 1 }
}

pub open spec fn is_vop(i: Instr) -> bool {
    is_unop(i) || is_binop(i) || load_kind(i) is Some
}

/// What a value instruction computes from its operands (`x0` deepest).
pub open spec fn vop(i: Instr, x0: u64, x1: u64, st: crate::sem::Store) -> Result<u64, Trap> {
    if is_unop(i) {
        eval_unop(i, x0)
    } else if is_binop(i) {
        eval_binop(i, x0, x1)
    } else {
        let (n, signed, is64, off) = load_kind(i)->Some_0;
        let ea = lo32(x0) as nat + off as nat;
        if ea + n > st.mem.len() {
            Err(Trap::MemoryOutOfBounds)
        } else {
            Ok(load_result(le(st.mem, ea as int, n), n, signed, is64))
        }
    }
}

/// What a store does with address `x0` and value `x1`.
pub open spec fn sop(i: Instr, x0: u64, x1: u64, st: crate::sem::Store) -> Result<crate::sem::Store, Trap> {
    let (n, off) = store_kind(i)->Some_0;
    let ea = lo32(x0) as nat + off as nat;
    if ea + n > st.mem.len() {
        Err(Trap::MemoryOutOfBounds)
    } else {
        Ok(crate::sem::Store { mem: write_le(st.mem, ea as int, store_value(x1, n), n), ..st })
    }
}

/// One straight-line instruction on the flat machine; locals are at `fp`.
pub open spec fn mstep(i: Instr, s: Seq<u64>, fp: int, sp: int, st: crate::sem::Store) -> MS {
    if is_vop(i) {
        let ar = vop_arity(i) as int;
        match vop(i, s[sp - ar], s[sp - ar + 1], st) {
            Ok(r) => MS::Next(s.update(sp - ar, r), sp - ar + 1, st),
            Err(t) => MS::Trap(t, st),
        }
    } else if store_kind(i) is Some {
        match sop(i, s[sp - 2], s[sp - 1], st) {
            Ok(st2) => MS::Next(s, sp - 2, st2),
            Err(t) => MS::Trap(t, st),
        }
    } else if is_const(i) {
        MS::Next(s.update(sp, const_val(i)), sp + 1, st)
    } else {
        match i {
            Instr::LocalGet(x) => MS::Next(s.update(sp, s[fp + x]), sp + 1, st),
            Instr::LocalSet(x) => MS::Next(s.update(fp + x, s[sp - 1]), sp - 1, st),
            Instr::LocalTee(x) => MS::Next(s.update(fp + x, s[sp - 1]), sp, st),
            Instr::Drop => MS::Next(s, sp - 1, st),
            Instr::Select => {
                let v = if lo32(s[sp - 1]) != 0 { s[sp - 3] } else { s[sp - 2] };
                MS::Next(s.update(sp - 3, v), sp - 2, st)
            },
            _ => MS::Next(s, sp, st),
        }
    }
}

/// `k` straight-line instructions from `pc`.
pub open spec fn msteps(body: Seq<Instr>, pc: int, k: nat, s: Seq<u64>, fp: int, sp: int,
    st: crate::sem::Store) -> MS
    decreases k,
{
    if k == 0 {
        MS::Next(s, sp, st)
    } else {
        match mstep(body[pc], s, fp, sp, st) {
            MS::Next(s1, sp1, st1) => msteps(body, pc + 1, (k - 1) as nat, s1, fp, sp1, st1),
            MS::Trap(t, st1) => MS::Trap(t, st1),
        }
    }
}

// ---------------------------------------------------------------------------
// The flat machine is the semantics
// ---------------------------------------------------------------------------

/// The machine depends only on the stack below `sp`.
pub proof fn lemma_mach_ext(m: &Module, s1: Seq<u64>, s2: Seq<u64>, calls: Seq<CallFrame>, fp: int, sp: int,
    c: Config)
    requires
        mach_ok(m, s1, calls, fp, sp, c),
        s1.len() == s2.len(),
        s1.subrange(0, sp) == s2.subrange(0, sp),
    ensures mach_ok(m, s2, calls, fp, sp, c),
{
    let f = top(c);
    let nl = n_locals(m, f.func);
    assert(s1.subrange(0, fp) =~= s1.subrange(0, sp).subrange(0, fp));
    assert(s2.subrange(0, fp) =~= s2.subrange(0, sp).subrange(0, fp));
    lemma_lower_same(m, s1, s2, calls, c.frames.subrange(0, c.frames.len() - 1), fp);
    assert(s1.subrange(fp, fp + nl) =~= s1.subrange(0, sp).subrange(fp, fp + nl));
    assert(s2.subrange(fp, fp + nl) =~= s2.subrange(0, sp).subrange(fp, fp + nl));
    assert(s1.subrange(fp + nl, sp) =~= s1.subrange(0, sp).subrange(fp + nl, sp));
    assert(s2.subrange(fp + nl, sp) =~= s2.subrange(0, sp).subrange(fp + nl, sp));
}

/// A configuration with the same frames has the same machine.
pub proof fn lemma_mach_frames(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fp: int, sp: int, c1: Config,
    c2: Config)
    requires mach_ok(m, s, calls, fp, sp, c1), c1.frames == c2.frames,
    ensures mach_ok(m, s, calls, fp, sp, c2),
{
}

/// One straight-line instruction: the flat machine takes the semantics'
/// step.
pub proof fn lemma_mstep(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: int, sp: int)
    requires
        pre(m, cs, codes, c, s, calls, fp, sp),
        simple(cur(m, c)),
    ensures
        match mstep(cur(m, c), s, fp, sp, c.store) {
            MS::Next(s2, sp2, st2) => stepped(m, c, s2, calls, fp, sp2, (top(c).pc + 1) as int, st2)
                && s2.len() == s.len(),
            MS::Trap(t, st2) => step(m, c) == Step::Trap(t, st2) && st2 == c.store,
        },
{
    lemma_facts(m, cs, codes, c, s, calls, fp, sp);
    lemma_step_instr(m, c);
    reveal(step_instr);
    let f = top(c);
    let i = cur(m, c);
    let nl = n_locals(m, f.func);
    let base = fp + nl;
    let st = c.store;
    if is_unop(i) {
        lemma_peek(s, base, sp, 0);
        assert(!is_binop(i));
        if let Ok(r) = eval_unop(i, s[sp - 1]) {
            lemma_set(s, base, sp, 1, r);
            let g = adv(push(popn(f, 1), r));
            let s2 = s.update(sp - 1, r);
            assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
            assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
            lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp);
        }
    } else if is_binop(i) {
        lemma_peek(s, base, sp, 0);
        lemma_peek(s, base, sp, 1);
        if let Ok(r) = eval_binop(i, s[sp - 2], s[sp - 1]) {
            lemma_set(s, base, sp, 2, r);
            let g = adv(push(popn(f, 2), r));
            let s2 = s.update(sp - 2, r);
            assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
            assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
            lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp - 1);
        }
    } else if load_kind(i) is Some {
        lemma_peek(s, base, sp, 0);
        let (n, signed, is64, off) = load_kind(i)->Some_0;
        let ea = lo32(s[sp - 1]) as nat + off as nat;
        if ea + n <= st.mem.len() {
            let r = load_result(le(st.mem, ea as int, n), n, signed, is64);
            lemma_set(s, base, sp, 1, r);
            let g = adv(push(popn(f, 1), r));
            let s2 = s.update(sp - 1, r);
            assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
            assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
            lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp);
        }
    } else if store_kind(i) is Some {
        lemma_peek(s, base, sp, 0);
        lemma_peek(s, base, sp, 1);
        let (n, off) = store_kind(i)->Some_0;
        let ea = lo32(s[sp - 2]) as nat + off as nat;
        if ea + n <= st.mem.len() {
            lemma_pop(s, base, sp, 2);
            let g = adv(popn(f, 2));
            lemma_mach_top(m, s, s, calls, fp, sp, c, g, sp - 2);
            let st2 = crate::sem::Store { mem: write_le(st.mem, ea as int, store_value(s[sp - 1], n), n), ..st };
            let c2 = with_top(Config { store: st2, ..c }, g);
            lemma_mach_frames(m, s, calls, fp, sp - 2, with_top(c, g), c2);
        }
    } else if is_const(i) {
        let v = const_val(i);
        let g = adv(push(f, v));
        let fc = cs[f.func as int];
        assert(i is I32Const || i is I64Const || i is F32Const || i is F64Const);
        assert(at(fc, (f.pc + 1) as int, hgt(fc, f.pc as int) + 1, lab(fc, f.pc as int)));
        assert(live(fc, (f.pc + 1) as int));
        assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
        assert(sp < s.len());
        let s2 = s.update(sp, v);
        assert(s2.subrange(base, sp + 1) =~= f.stack.push(v));
        assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
        assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
        lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp + 1);
    } else {
        match i {
            Instr::LocalGet(x) => {
                let v = s[fp + x];
                assert(f.locals[x as int] == v);
                let g = adv(push(f, v));
                let s2 = s.update(sp, v);
                assert(live(cs[f.func as int], (f.pc + 1) as int));
                assert(s2.subrange(base, sp + 1) =~= f.stack.push(v));
                assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
                assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
                lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp + 1);
            },
            Instr::LocalSet(x) => {
                lemma_peek(s, base, sp, 0);
                let v = s[sp - 1];
                let g = adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..popn(f, 1) });
                let s2 = s.update(fp + x, v);
                assert(s2.subrange(fp, base) =~= f.locals.update(x as int, v));
                assert(s2.subrange(base, sp - 1) =~= f.stack.subrange(0, f.stack.len() - 1));
                assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
                lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp - 1);
            },
            Instr::LocalTee(x) => {
                lemma_peek(s, base, sp, 0);
                let v = s[sp - 1];
                let g = adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..f });
                let s2 = s.update(fp + x, v);
                assert(s2.subrange(fp, base) =~= f.locals.update(x as int, v));
                assert(s2.subrange(base, sp) =~= f.stack);
                assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
                lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp);
            },
            Instr::Drop => {
                lemma_pop(s, base, sp, 1);
                lemma_mach_top(m, s, s, calls, fp, sp, c, adv(popn(f, 1)), sp - 1);
            },
            Instr::Select => {
                lemma_peek(s, base, sp, 0);
                lemma_peek(s, base, sp, 1);
                lemma_peek(s, base, sp, 2);
                let v = if lo32(s[sp - 1]) != 0 { s[sp - 3] } else { s[sp - 2] };
                lemma_set(s, base, sp, 3, v);
                let g = adv(push(popn(f, 3), v));
                let s2 = s.update(sp - 3, v);
                assert(s2.subrange(0, fp) =~= s.subrange(0, fp));
                assert(s2.subrange(fp, base) =~= s.subrange(fp, base));
                lemma_mach_top(m, s, s2, calls, fp, sp, c, g, sp - 2);
            },
            _ => {
                let fc = cs[f.func as int];
                let h = f.stack.len();
                let g = match i {
                    Instr::Block { bt, end } => {
                        let (np, nr) = bt_arity(m, bt)->Some_0;
                        Frame { pc: f.pc + 1, labels: f.labels.push(Label { arity: nr, cont: (end + 1) as nat, height: (h - np) as nat }), ..f }
                    },
                    Instr::Loop { bt } => {
                        let (np, nr) = bt_arity(m, bt)->Some_0;
                        Frame { pc: f.pc + 1, labels: f.labels.push(Label { arity: np, cont: f.pc, height: (h - np) as nat }), ..f }
                    },
                    Instr::End => Frame { pc: f.pc + 1, labels: f.labels.drop_last(), ..f },
                    _ => adv(f),
                };
                assert(step(m, c) == Step::Next(with_top(c, g)));
                lemma_mach_top(m, s, s, calls, fp, sp, c, g, sp);
            },
        }
    }
}

/// The window `[pc, pc + k)` of the top frame's function is straight-line
/// code.
pub open spec fn straight(m: &Module, d: nat, pc: int, k: nat) -> bool {
    &&& pc + k <= m.funcs@[d as int].body@.len()
    &&& forall|j: int| pc <= j < pc + k ==> #[trigger] simple(m.funcs@[d as int].body@[j])
}

/// What [`lemma_msteps`] needs about the machine.
pub open spec fn mpre(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: int, sp: int) -> bool
{
    &&& certs_ok(m, cs)
    &&& codes_ok(m, cs, codes)
    &&& inv(m, cs, c)
    &&& mach_ok(m, s, calls, fp, sp, c)
    &&& fp + codes[top(c).func as int].frame <= s.len()
    &&& s.len() <= MAX_STACK
}

/// `k` straight-line instructions: the semantics, run for `k` steps
/// (without host calls), ends where the flat machine does.
pub proof fn lemma_msteps(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: int, sp: int, k: nat)
    requires
        mpre(m, cs, codes, c, s, calls, fp, sp),
        top(c).func < m.funcs@.len(),
        straight(m, top(c).func, top(c).pc as int, k),
    ensures
        match msteps(m.funcs@[top(c).func as int].body@, top(c).pc as int, k, s, fp, sp, c.store) {
            MS::Next(s2, sp2, st2) => {
                &&& run(m, c, Seq::empty(), k) is Running
                &&& mpre(m, cs, codes, run(m, c, Seq::empty(), k)->Running_0, s2, calls, fp, sp2)
                &&& top(run(m, c, Seq::empty(), k)->Running_0).pc == top(c).pc + k
                &&& top(run(m, c, Seq::empty(), k)->Running_0).func == top(c).func
                &&& (run(m, c, Seq::empty(), k)->Running_0).store == st2
                &&& s2.len() == s.len()
            },
            MS::Trap(t, st2) => run(m, c, Seq::empty(), k) == Outcome::Trap(t, st2),
        },
    decreases k,
{
    let body = m.funcs@[top(c).func as int].body@;
    let pc = top(c).pc as int;
    if k == 0 {
        reveal_with_fuel(run, 1);
    } else {
        assert(simple(body[pc]));
        assert(at_instr(m, c));
        assert(pre(m, cs, codes, c, s, calls, fp, sp));
        lemma_mstep(m, cs, codes, c, s, calls, fp, sp);
        assert(cur(m, c) == body[pc]);
        match mstep(body[pc], s, fp, sp, c.store) {
            MS::Next(s1, sp1, st1) => {
                let c1 = step(m, c)->Next_0;
                lemma_step(m, cs, c);
                assert(inv(m, cs, c1));
                assert(straight(m, top(c1).func, top(c1).pc as int, (k - 1) as nat));
                lemma_msteps(m, cs, codes, c1, s1, calls, fp, sp1, (k - 1) as nat);
                assert(run(m, c, Seq::empty(), k) == run(m, c1, Seq::empty(), (k - 1) as nat));
            },
            MS::Trap(t, st1) => {
                assert(run(m, c, Seq::empty(), k) == Outcome::Trap(t, st1));
            },
        }
    }
}

/// A run that is still going, continued by a run without host calls from
/// where it is.
pub proof fn lemma_run_concat(m: &Module, c0: Config, hs: Seq<HostResp>, n: nat, c: Config, k: nat)
    requires
        run(m, c0, hs, n) == Outcome::Running(c),
        !(run(m, c, Seq::empty(), k) is Stuck),
    ensures run(m, c0, hs, n + k) == run(m, c, Seq::empty(), k),
    decreases n,
{
    if n == 0 {
        assert(hs =~= Seq::<HostResp>::empty());
        assert(c0 == c);
    } else {
        match step(m, c0) {
            Step::Next(c2) => {
                lemma_run_concat(m, c2, hs, (n - 1) as nat, c, k);
                assert((n + k - 1) as nat == (n - 1) as nat + k);
            },
            Step::Host { func, args, cfg } => {
                if let HostResp::Ok(st, res) = hs[0] {
                    lemma_run_concat(m, resume(cfg, st, res), hs.drop_first(), (n - 1) as nat, c, k);
                    assert((n + k - 1) as nat == (n - 1) as nat + k);
                }
            },
            Step::Grow { ok, fail } => {
                if let HostResp::Grow(b) = hs[0] {
                    lemma_run_concat(m, if b { ok } else { fail }, hs.drop_first(), (n - 1) as nat, c, k);
                    assert((n + k - 1) as nat == (n - 1) as nat + k);
                }
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// Algebra of straight-line runs
// ---------------------------------------------------------------------------

/// A run splits at any point.
pub proof fn lemma_msteps_split(body: Seq<Instr>, pc: int, a: nat, b: nat, s: Seq<u64>, fp: int, sp: int,
    st: crate::sem::Store)
    ensures
        msteps(body, pc, a + b, s, fp, sp, st) == match msteps(body, pc, a, s, fp, sp, st) {
            MS::Next(s1, sp1, st1) => msteps(body, pc + a, b, s1, fp, sp1, st1),
            MS::Trap(t, st1) => MS::Trap(t, st1),
        },
    decreases a,
{
    hide(mstep);
    if a > 0 {
        match mstep(body[pc], s, fp, sp, st) {
            MS::Next(s1, sp1, st1) => {
                lemma_msteps_split(body, pc + 1, (a - 1) as nat, b, s1, fp, sp1, st1);
                assert((a + b - 1) as nat == (a - 1) as nat + b);
            },
            MS::Trap(t, st1) => {},
        }
    }
}

/// Instructions that move no values.
pub open spec fn is_noop(i: Instr) -> bool {
    i is Nop || i is Block || i is Loop || i is End
}

pub proof fn lemma_noops(body: Seq<Instr>, pc: int, j: nat, s: Seq<u64>, fp: int, sp: int, st: crate::sem::Store)
    requires forall|q: int| pc <= q < pc + j ==> #[trigger] is_noop(body[q]),
    ensures msteps(body, pc, j, s, fp, sp, st) == MS::Next(s, sp, st),
    decreases j,
{
    if j > 0 {
        assert(is_noop(body[pc]));
        lemma_noops(body, pc + 1, (j - 1) as nat, s, fp, sp, st);
    }
}

/// One instruction as a run.
pub proof fn lemma_msteps_one(body: Seq<Instr>, pc: int, s: Seq<u64>, fp: int, sp: int, st: crate::sem::Store)
    ensures msteps(body, pc, 1, s, fp, sp, st) == mstep(body[pc], s, fp, sp, st),
{
    reveal_with_fuel(msteps, 2);
}

} // verus!
