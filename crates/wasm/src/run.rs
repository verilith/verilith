//! The interpreter loop and its instruction groups.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::cert::*;
use crate::preserve::*;
use crate::prims::*;
use crate::interp::*;
use crate::exec_num::*;
use crate::interp::Store;
use crate::reg::*;
use crate::rrun::*;
use crate::rsteps::*;
use crate::reg_ops::*;

verus! {

/// Most value-stack slots an instance may use.
pub const MAX_STACK: usize = 0x1000_0000;

/// What every instruction group may assume.
pub open spec fn pre(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: int, sp: int) -> bool
{
    &&& certs_ok(m, cs)
    &&& codes_ok(m, cs, codes)
    &&& inv(m, cs, c)
    &&& mach_ok(m, s, calls, fp, sp, c)
    &&& at_instr(m, c)
    &&& fp + codes[top(c).func as int].frame <= s.len()
    &&& s.len() <= MAX_STACK
}

/// The next configuration is `step(m, c)`, in the same frame, at `pc2`,
/// with the machine at `(s2, sp2)` and the store `st2`.
pub open spec fn stepped(m: &Module, c: Config, s2: Seq<u64>, calls: Seq<CallFrame>, fp: int, sp2: int,
    pc2: int, st2: crate::sem::Store) -> bool
{
    &&& step(m, c) is Next
    &&& mach_ok(m, s2, calls, fp, sp2, step(m, c)->Next_0)
    &&& top(step(m, c)->Next_0).pc == pc2
    &&& top(step(m, c)->Next_0).func == top(c).func
    &&& (step(m, c)->Next_0).store == st2
}

/// The certificate's facts at the current instruction.
pub proof fn lemma_facts(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: int, sp: int)
    requires pre(m, cs, codes, c, s, calls, fp, sp),
    ensures ({
        let f = top(c);
        let fc = cs[f.func as int];
        let nl = n_locals(m, f.func);
        &&& local_ok(m, f.func, fc, f.pc as int)
        &&& (lab(fc, f.pc as int) as nat) < fc.labels@.len()
        &&& labels_wf(fc.labels@)
        &&& f.stack.len() == hgt(fc, f.pc as int)
        &&& sp == fp + nl + f.stack.len()
        &&& hgt(fc, f.pc as int) <= fc.max_height
        &&& fp + nl + fc.max_height <= s.len()
        &&& f.labels == chain(fc.labels@, lab(fc, f.pc as int))
        &&& func_cert_ok(m, f.func, fc)
        &&& code_ok(m, cs, f.func, &codes[f.func as int])
        &&& (forall|q: int| 0 <= q <= m.funcs@[f.func as int].body@.len() && live(fc, q)
                ==> #[trigger] hgt(fc, q) <= fc.max_height)
    }),
{
    let f = top(c);
    let d = f.func;
    let fc = cs[d as int];
    assert(func_cert_ok(m, d, fc));
    assert(pc_ok(m, d, fc, f.pc as int));
    assert(code_ok(m, cs, d, &codes[d as int]));
    lemma_labels_wf(m, d, fc);
}

// ---------------------------------------------------------------------------
// Sequence facts
// ---------------------------------------------------------------------------

pub proof fn lemma_set(s: Seq<u64>, base: int, sp: int, k: int, r: u64)
    requires 0 <= base, base + k <= sp <= s.len(), k >= 1,
    ensures
        s.update(sp - k, r).subrange(base, sp - k + 1) == s.subrange(base, sp).subrange(0, sp - base - k).push(r),
        s.update(sp - k, r).subrange(0, base) == s.subrange(0, base),
{
    assert(s.update(sp - k, r).subrange(base, sp - k + 1) =~= s.subrange(base, sp).subrange(0, sp - base - k).push(r));
    assert(s.update(sp - k, r).subrange(0, base) =~= s.subrange(0, base));
}

pub proof fn lemma_pop(s: Seq<u64>, base: int, sp: int, k: int)
    requires 0 <= base, base + k <= sp <= s.len(), k >= 0,
    ensures s.subrange(base, sp - k) == s.subrange(base, sp).subrange(0, sp - base - k),
{
    assert(s.subrange(base, sp - k) =~= s.subrange(base, sp).subrange(0, sp - base - k));
}

/// The value `k` from the top of the operand stack is slot `sp - 1 - k`.
pub proof fn lemma_peek(s: Seq<u64>, base: int, sp: int, k: int)
    requires 0 <= base, base + k < sp <= s.len(), k >= 0,
    ensures s.subrange(base, sp)[sp - base - 1 - k] == s[sp - 1 - k],
{
}

// ---------------------------------------------------------------------------
// Instruction groups that stay in the frame
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn do_unop(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, i: Instr,
    Ghost(c): Ghost<Config>) -> (r: Result<(), Trap>)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        is_unop(i),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        match r {
            Ok(()) => stepped(m, c, final(stack)@, calls, fp as int, sp as int, (top(c).pc + 1) as int, c.store),
            Err(t) => step(m, c) == Step::Trap(t, c.store),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost base = fp + n_locals(m, f.func);
    let a = sget(stack, sp - 1);
    proof { lemma_peek(stack@, base, sp as int, 0); }
    match exec_unop(i, a) {
        Ok(r) => {
            let ghost s1 = stack@;
            sset(stack, sp - 1, r);
            proof {
                lemma_set(s1, base, sp as int, 1, r);
                let g = adv(push(popn(f, 1), r));
                assert(s1.update(sp - 1, r).subrange(0, fp as int) =~= s1.subrange(0, fp as int));
                assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
                lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp as int);
            }
            Ok(())
        },
        Err(t) => Err(t),
    }
}

#[inline(always)]
pub fn do_binop(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, i: Instr,
    Ghost(c): Ghost<Config>) -> (r: Result<(), Trap>)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        is_binop(i),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        sp >= 1,
        match r {
            Ok(()) => stepped(m, c, final(stack)@, calls, fp as int, sp - 1, (top(c).pc + 1) as int, c.store),
            Err(t) => step(m, c) == Step::Trap(t, c.store),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost base = fp + n_locals(m, f.func);
    let a = sget(stack, sp - 2);
    let b = sget(stack, sp - 1);
    proof {
        lemma_peek(stack@, base, sp as int, 0);
        lemma_peek(stack@, base, sp as int, 1);
    }
    match exec_binop(i, a, b) {
        Ok(r) => {
            let ghost s1 = stack@;
            sset(stack, sp - 2, r);
            proof {
                lemma_set(s1, base, sp as int, 2, r);
                let g = adv(push(popn(f, 2), r));
                assert(s1.update(sp - 2, r).subrange(0, fp as int) =~= s1.subrange(0, fp as int));
                assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
                lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp - 1);
            }
            Ok(())
        },
        Err(t) => Err(t),
    }
}


// ---------------------------------------------------------------------------
// Memory
// ---------------------------------------------------------------------------

pub proof fn lemma_le_bound(s: Seq<u8>, i: int, n: nat)
    ensures le(s, i, n) < pow2(8 * n),
    decreases n,
{
    if n == 0 {
        assert(pow2(0) == 1) by { lemma_pow2_values(); }
    } else {
        lemma_le_bound(s, i + 1, (n - 1) as nat);
        lemma_pow2_add(8, 8 * (n - 1) as nat);
        assert(pow2(8) == 256) by { lemma_pow2_values(); }
        assert(8 + 8 * (n - 1) as nat == 8 * n);
        let x = le(s, i + 1, (n - 1) as nat);
        let p = pow2(8 * (n - 1) as nat);
        assert(s[i] as nat + 256 * x < 256 * p) by (nonlinear_arith)
            requires s[i] < 256, x < p, x >= 0;
    }
}

pub proof fn lemma_write_le_len(s: Seq<u8>, i: int, v: nat, n: nat)
    requires 0 <= i, i + n <= s.len(),
    ensures write_le(s, i, v, n).len() == s.len(),
    decreases n,
{
    if n > 0 {
        lemma_write_le_len(s.update(i, (v % 256) as u8), i + 1, v / 256, (n - 1) as nat);
    }
}

#[inline(always)]
pub fn load_kind_x(i: Instr) -> (r: (usize, bool, bool, u32))
    requires load_kind(i) is Some,
    ensures load_kind(i) == Some((r.0 as nat, r.1, r.2, r.3)),
{
    match i {
        Instr::I32Load(o) => (4, false, false, o),
        Instr::I64Load(o) => (8, false, true, o),
        Instr::F32Load(o) => (4, false, false, o),
        Instr::F64Load(o) => (8, false, true, o),
        Instr::I32Load8S(o) => (1, true, false, o),
        Instr::I32Load8U(o) => (1, false, false, o),
        Instr::I32Load16S(o) => (2, true, false, o),
        Instr::I32Load16U(o) => (2, false, false, o),
        Instr::I64Load8S(o) => (1, true, true, o),
        Instr::I64Load8U(o) => (1, false, true, o),
        Instr::I64Load16S(o) => (2, true, true, o),
        Instr::I64Load16U(o) => (2, false, true, o),
        Instr::I64Load32S(o) => (4, true, true, o),
        Instr::I64Load32U(o) => (4, false, true, o),
        _ => (4, false, true, 0),
    }
}

#[inline(always)]
pub fn store_kind_x(i: Instr) -> (r: (usize, u32))
    requires store_kind(i) is Some,
    ensures store_kind(i) == Some((r.0 as nat, r.1)),
{
    match i {
        Instr::I32Store(o) => (4, o),
        Instr::I64Store(o) => (8, o),
        Instr::F32Store(o) => (4, o),
        Instr::F64Store(o) => (8, o),
        Instr::I32Store8(o) => (1, o),
        Instr::I32Store16(o) => (2, o),
        Instr::I64Store8(o) => (1, o),
        Instr::I64Store16(o) => (2, o),
        Instr::I64Store32(o) => (4, o),
        _ => (4, 0),
    }
}

#[inline(always)]
pub fn load_res(v: u64, n: usize, signed: bool, is64: bool) -> (r: u64)
    requires
        v < pow2(8 * n as nat),
        n == 1 || n == 2 || n == 4 || n == 8,
        signed ==> n <= 4,
        signed && !is64 ==> n <= 2,
    ensures r == load_result(v as nat, n as nat, signed, is64),
{
    if !signed {
        v
    } else if is64 {
        crate::sint::sext64(v, (8 * n) as u32)
    } else {
        proof { lemma_pow2_values(); }
        crate::sint::sext32(v as u32, (8 * n) as u32) as u64
    }
}

#[inline(always)]
pub fn do_load(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &Store, i: Instr,
    Ghost(c): Ghost<Config>) -> (r: Result<(), Trap>)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        load_kind(i) is Some,
        c.store == store_view(st),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        match r {
            Ok(()) => stepped(m, c, final(stack)@, calls, fp as int, sp as int, (top(c).pc + 1) as int, c.store),
            Err(t) => step(m, c) == Step::Trap(t, c.store),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost base = fp + n_locals(m, f.func);
    let (n, signed, is64, off) = load_kind_x(i);
    let a = sget(stack, sp - 1);
    proof { lemma_peek(stack@, base, sp as int, 0); }
    let ea = lo(a) as u64 + off as u64;
    if ea + n as u64 > st.mem.len() as u64 {
        return Err(Trap::MemoryOutOfBounds);
    }
    let v = load(&st.mem, ea as usize, n);
    proof {
        lemma_le_bound(st.mem@, ea as int, n as nat);
    }
    let r = load_res(v, n, signed, is64);
    let ghost s1 = stack@;
    sset(stack, sp - 1, r);
    proof {
        lemma_set(s1, base, sp as int, 1, r);
        let g = adv(push(popn(f, 1), r));
        assert(s1.update(sp - 1, r).subrange(0, fp as int) =~= s1.subrange(0, fp as int));
        assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
        lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp as int);
    }
    Ok(())
}

#[inline(always)]
pub fn do_store(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &mut Store, i: Instr,
    Ghost(c): Ghost<Config>) -> (r: Result<(), Trap>)
    requires
        pre(m, cs, codes, c, stack@, calls, fp as int, sp as int),
        cur(m, c) == i,
        store_kind(i) is Some,
        c.store == store_view(old(st)),
        store_wf(old(st)),
    ensures
        sp >= 2,
        store_wf(final(st)),
        match r {
            Ok(()) => stepped(m, c, stack@, calls, fp as int, sp - 2, (top(c).pc + 1) as int, store_view(final(st))),
            Err(t) => step(m, c) == Step::Trap(t, c.store) && *final(st) == *old(st),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost base = fp + n_locals(m, f.func);
    let (n, off) = store_kind_x(i);
    let v = sget(stack, sp - 1);
    let a = sget(stack, sp - 2);
    proof {
        lemma_peek(stack@, base, sp as int, 0);
        lemma_peek(stack@, base, sp as int, 1);
    }
    let ea = lo(a) as u64 + off as u64;
    if ea + n as u64 > st.mem.len() as u64 {
        return Err(Trap::MemoryOutOfBounds);
    }
    let ghost m1 = st.mem@;
    store(&mut st.mem, ea as usize, v, n);
    proof {
        lemma_write_le_len(m1, ea as int, store_value(v, n as nat), n as nat);
        lemma_pop(stack@, base, sp as int, 2);
        let g = adv(popn(f, 2));
        lemma_mach_top(m, stack@, stack@, calls, fp as int, sp as int, c, g, sp - 2);
        let s2 = crate::sem::Store { mem: st.mem@, ..c.store };
        assert(store_view(st) == s2);
    }
    Ok(())
}


// ---------------------------------------------------------------------------
// Structure, variables, constants
// ---------------------------------------------------------------------------

/// `nop`, `block`, `loop` and `end`: only the position (and the labels,
/// which the machine does not keep) change.
#[inline(always)]
pub fn do_nop(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, i: Instr,
    Ghost(c): Ghost<Config>)
    requires
        pre(m, cs, codes, c, stack@, calls, fp as int, sp as int),
        cur(m, c) == i,
        i is Nop || i is Block || i is Loop || i is End,
    ensures
        stepped(m, c, stack@, calls, fp as int, sp as int, (top(c).pc + 1) as int, c.store),
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
        let f = top(c);
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
            Instr::End => {
                Frame { pc: f.pc + 1, labels: f.labels.drop_last(), ..f }
            },
            _ => adv(f),
        };
        assert(step(m, c) == Step::Next(with_top(c, g)));
        lemma_mach_top(m, stack@, stack@, calls, fp as int, sp as int, c, g, sp as int);
    }
}

/// Locals, globals, constants, `drop` and `select`.
#[inline(always)]
pub fn do_var(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &mut Store, i: Instr,
    Ghost(c): Ghost<Config>) -> (sp2: usize)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        i is LocalGet || i is LocalSet || i is LocalTee || i is GlobalGet || i is GlobalSet
            || i is I32Const || i is I64Const || i is F32Const || i is F64Const || i is Drop || i is Select,
        c.store == store_view(old(st)),
        store_wf(old(st)),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        store_wf(final(st)),
        stepped(m, c, final(stack)@, calls, fp as int, sp2 as int, (top(c).pc + 1) as int, store_view(final(st))),
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    let ghost nl = n_locals(m, f.func);
    let ghost base = fp + nl;
    let ghost s1 = stack@;
    proof {
        assert(live(fc, (f.pc + 1) as int));
        assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
    }
    match i {
        Instr::I32Const(v) => push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v as u64, Ghost(c)),
        Instr::I64Const(v) => push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v, Ghost(c)),
        Instr::F32Const(v) => push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v as u64, Ghost(c)),
        Instr::F64Const(v) => push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v, Ghost(c)),
        Instr::GlobalGet(x) => {
            let v = vget(&st.globals, x as usize);
            push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v, Ghost(c))
        },
        Instr::LocalGet(x) => {
            let v = sget(stack, fp + x as usize);
            proof { assert(f.locals[x as int] == s1[fp + x]); }
            push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, v, Ghost(c))
        },
        Instr::LocalSet(x) => {
            let v = sget(stack, sp - 1);
            sset(stack, fp + x as usize, v);
            proof {
                lemma_peek(s1, base, sp as int, 0);
                let g = adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..popn(f, 1) });
                assert(stack@.subrange(fp as int, base) =~= f.locals.update(x as int, v));
                assert(stack@.subrange(base, sp - 1) =~= f.stack.subrange(0, f.stack.len() - 1));
                assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
                lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp - 1);
            }
            sp - 1
        },
        Instr::LocalTee(x) => {
            let v = sget(stack, sp - 1);
            sset(stack, fp + x as usize, v);
            proof {
                lemma_peek(s1, base, sp as int, 0);
                let g = adv(Frame { locals: f.locals.update(x as int, peek(f, 0)), ..f });
                assert(stack@.subrange(fp as int, base) =~= f.locals.update(x as int, v));
                assert(stack@.subrange(base, sp as int) =~= f.stack);
                assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
                lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp as int);
            }
            sp
        },
        Instr::GlobalSet(x) => {
            let v = sget(stack, sp - 1);
            let ghost st1 = store_view(st);
            vset(&mut st.globals, x as usize, v);
            proof {
                lemma_peek(s1, base, sp as int, 0);
                lemma_pop(s1, base, sp as int, 1);
                let g = adv(popn(f, 1));
                lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, g, sp - 1);
                assert(store_view(st) == crate::sem::Store { globals: st1.globals.update(x as int, v), ..st1 });
            }
            sp - 1
        },
        Instr::Drop => {
            proof {
                lemma_pop(s1, base, sp as int, 1);
                lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, adv(popn(f, 1)), sp - 1);
            }
            sp - 1
        },
        _ => {
            // select
            let cnd = sget(stack, sp - 1);
            proof {
                lemma_peek(s1, base, sp as int, 0);
                lemma_peek(s1, base, sp as int, 1);
                lemma_peek(s1, base, sp as int, 2);
            }
            let v = if lo(cnd) != 0 { sget(stack, sp - 3) } else { sget(stack, sp - 2) };
            sset(stack, sp - 3, v);
            proof {
                lemma_set(s1, base, sp as int, 3, v);
                let g = adv(push(popn(f, 3), v));
                assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
                assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
                lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp - 2);
            }
            sp - 2
        },
    }
}

/// Pushes `v`, for an instruction whose step is `adv(push(f, v))`.
#[inline(always)]
fn push_val(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, v: u64,
    Ghost(c): Ghost<Config>) -> (sp2: usize)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        step(m, c) == next(c, adv(push(top(c), v))),
        live(cs[top(c).func as int], (top(c).pc + 1) as int),
        hgt(cs[top(c).func as int], (top(c).pc + 1) as int) == top(c).stack.len() + 1,
        hgt(cs[top(c).func as int], (top(c).pc + 1) as int) <= cs[top(c).func as int].max_height,
    ensures
        final(stack)@.len() == old(stack)@.len(),
        sp2 == sp + 1,
        stepped(m, c, final(stack)@, calls, fp as int, sp2 as int, (top(c).pc + 1) as int, c.store),
{
    proof { lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int); }
    let ghost f = top(c);
    let ghost base = fp + n_locals(m, f.func);
    let ghost s1 = stack@;
    sset(stack, sp, v);
    proof {
        let g = adv(push(f, v));
        assert(stack@.subrange(base, sp + 1) =~= f.stack.push(v));
        assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
        assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
        lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp + 1);
    }
    sp + 1
}


/// `memory.size`, `memory.fill`, `memory.copy`, `memory.init` and
/// `data.drop`.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn do_mem(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &mut Store, i: Instr,
    Ghost(c): Ghost<Config>) -> (r: Result<usize, Trap>)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        i is MemorySize || i is MemoryFill || i is MemoryCopy || i is MemoryInit || i is DataDrop,
        c.store == store_view(old(st)),
        store_wf(old(st)),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        store_wf(final(st)),
        match r {
            Ok(sp2) => stepped(m, c, final(stack)@, calls, fp as int, sp2 as int, (top(c).pc + 1) as int,
                store_view(final(st))),
            Err(t) => step(m, c) == Step::Trap(t, c.store) && *final(st) == *old(st),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    let ghost nl = n_locals(m, f.func);
    let ghost base = fp + nl;
    let ghost s1 = stack@;
    let ghost st1 = store_view(st);
    proof {
        assert(live(fc, (f.pc + 1) as int));
        assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
    }
    match i {
        Instr::MemorySize => {
            let pages = (st.mem.len() / 65536) as u64;
            Ok(push_val(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, pages, Ghost(c)))
        },
        Instr::DataDrop(x) => {
            vset(&mut st.dropped, x as usize, true);
            proof {
                lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, adv(f), sp as int);
                assert(store_view(st) == crate::sem::Store { data_dropped: st1.data_dropped.update(x as int, true), ..st1 });
            }
            Ok(sp)
        },
        _ => {
            let a2 = lo(sget(stack, sp - 1));
            let a1 = lo(sget(stack, sp - 2));
            let a0 = lo(sget(stack, sp - 3));
            proof {
                lemma_peek(s1, base, sp as int, 0);
                lemma_peek(s1, base, sp as int, 1);
                lemma_peek(s1, base, sp as int, 2);
            }
            let (d, n) = (a0 as u64, a2 as u64);
            let len = st.mem.len() as u64;
            match i {
                Instr::MemoryFill => {
                    if d + n > len {
                        return Err(Trap::MemoryOutOfBounds);
                    }
                    fill(&mut st.mem, d as usize, (a1 % 256) as u8, n as usize);
                },
                Instr::MemoryCopy => {
                    let s = a1 as u64;
                    if s + n > len || d + n > len {
                        return Err(Trap::MemoryOutOfBounds);
                    }
                    copy_within(&mut st.mem, d as usize, s as usize, n as usize);
                },
                Instr::MemoryInit(x) => {
                    let s = a1 as u64;
                    let data = m.datas[x as usize].bytes.as_slice();
                    let dlen: u64 = if st.dropped[x as usize] { 0 } else { data.len() as u64 };
                    proof {
                        assert(dlen as nat == data_bytes(m, st1, x as nat).len());
                    }
                    if s + n > dlen || d + n > len {
                        return Err(Trap::MemoryOutOfBounds);
                    }
                    proof {
                        assert(data@.subrange(s as int, (s + n) as int)
                            =~= data_bytes(m, st1, x as nat).subrange(s as int, (s + n) as int));
                    }
                    copy_in(&mut st.mem, d as usize, data, s as usize, n as usize);
                },
                _ => {},
            }
            proof {
                lemma_pop(s1, base, sp as int, 3);
                lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, adv(popn(f, 3)), sp - 3);
                assert(store_view(st) == crate::sem::Store { mem: st.mem@, ..st1 });
            }
            Ok(sp - 3)
        },
    }
}


/// `memory.grow`. `None` if the request is over the maximum (an ordinary
/// step that pushes -1); otherwise whether the allocation succeeded, which
/// picks the outcome of the semantics' [`Step::Grow`].
#[inline(always)]
pub fn do_grow(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &mut Store,
    Ghost(c): Ghost<Config>) -> (r: Ghost<Option<bool>>)
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == Instr::MemoryGrow,
        c.store == store_view(old(st)),
        store_wf(old(st)),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        store_wf(final(st)),
        match r@ {
            None => stepped(m, c, final(stack)@, calls, fp as int, sp as int, (top(c).pc + 1) as int,
                store_view(final(st))),
            Some(b) => step(m, c) is Grow && ({
                let c2 = if b { step(m, c)->ok } else { step(m, c)->fail };
                &&& mach_ok(m, final(stack)@, calls, fp as int, sp as int, c2)
                &&& top(c2).pc == top(c).pc + 1
                &&& top(c2).func == top(c).func
                &&& c2.store == store_view(final(st))
            }),
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    let ghost nl = n_locals(m, f.func);
    let ghost base = fp + nl;
    let ghost s1 = stack@;
    let ghost st1 = store_view(st);
    proof {
        assert(live(fc, (f.pc + 1) as int));
        assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
    }
    let n = lo(sget(stack, sp - 1)) as u64;
    proof { lemma_peek(s1, base, sp as int, 0); }
    let old = (st.mem.len() / 65536) as u64;
    let ghost mut res: Option<bool> = None;
    let r: u64 = if old + n > st.mem_max as u64 {
        0xffff_ffff
    } else if try_grow(&mut st.mem, (n * 65536) as usize) {
        proof {
            res = Some(true);
            assert(store_view(st) == crate::sem::Store {
                mem: st1.mem + Seq::new(n as nat * PAGE as nat, |_i| 0u8), ..st1 });
            assert(st.mem@.len() == st1.mem.len() + n * 65536);
            assert(st.mem@.len() <= st.mem_max as nat * PAGE as nat) by (nonlinear_arith)
                requires
                    st.mem@.len() == st1.mem.len() + n * 65536,
                    st1.mem.len() % 65536 == 0,
                    old == st1.mem.len() / 65536,
                    old + n <= st.mem_max;
            assert(st.mem@.len() % 65536 == 0) by (nonlinear_arith)
                requires st.mem@.len() == st1.mem.len() + n * 65536, st1.mem.len() % 65536 == 0;
        }
        old
    } else {
        proof { res = Some(false); assert(store_view(st) == st1); }
        0xffff_ffff
    };
    sset(stack, sp - 1, r);
    proof {
        lemma_set(s1, base, sp as int, 1, r);
        let g = adv(push(popn(f, 1), r));
        assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
        assert(stack@.subrange(fp as int, base) =~= s1.subrange(fp as int, base));
        lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp as int);
        assert(Config { store: c.store, ..c } == c);
    }
    Ghost(res)
}


// ---------------------------------------------------------------------------
// Branches
// ---------------------------------------------------------------------------

/// Branching from `f2` (the top frame, with `pops` operands already
/// popped) to label `k` continues at the resolved target with the label's
/// values moved down to its height.
pub proof fn lemma_br_frame(m: &Module, cs: Seq<FuncCert>, c: Config, f2: Frame, k: nat, pops: nat)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        f2.func == top(c).func,
        f2.func < m.funcs@.len(),
        f2.pc < m.funcs@[f2.func as int].body@.len(),
        live(cs[f2.func as int], f2.pc as int),
        f2.stack.len() + pops == hgt(cs[f2.func as int], f2.pc as int),
        f2.labels == chain(cs[f2.func as int].labels@, lab(cs[f2.func as int], f2.pc as int)),
        br_ok(cs[f2.func as int], f2.pc as int, k, pops),
    ensures ({
        let t = target_of(cs[f2.func as int], f2.pc as int, k);
        let len = f2.stack.len();
        &&& t.height + t.arity <= len
        &&& exit_label(f2, k, t.pc as nat) is Some
        &&& br(c, f2, k) == next(c, exit_label(f2, k, t.pc as nat)->Some_0)
        &&& (exit_label(f2, k, t.pc as nat)->Some_0).stack
            == f2.stack.subrange(0, t.height as int) + f2.stack.subrange(len - t.arity, len as int)
        &&& (exit_label(f2, k, t.pc as nat)->Some_0).pc == t.pc
        &&& (exit_label(f2, k, t.pc as nat)->Some_0).func == f2.func
        &&& (exit_label(f2, k, t.pc as nat)->Some_0).locals == f2.locals
    }),
{
    let fc = cs[f2.func as int];
    assert(func_cert_ok(m, f2.func, fc));
    lemma_labels_wf(m, f2.func, fc);
    lemma_nth(fc.labels@, lab(fc, f2.pc as int), k);
}

/// Moves the top `t.arity` slots down to `base + t.height`.
#[inline(always)]
fn move_down(stack: &mut Vec<u64>, base: usize, sp: usize, t: BrTarget) -> (sp2: usize)
    requires base + t.height + t.arity <= sp <= old(stack)@.len(),
    ensures
        sp2 == base + t.height + t.arity,
        final(stack)@.len() == old(stack)@.len(),
        final(stack)@.subrange(0, base + t.height) == old(stack)@.subrange(0, base + t.height),
        final(stack)@.subrange(base + t.height, sp2 as int) == old(stack)@.subrange(sp - t.arity, sp as int),
{
    let dst = base + t.height as usize;
    let src = sp - t.arity as usize;
    if dst < src {
        scopy_down(stack, dst, src, t.arity as usize);
        assert(stack@.subrange(0, dst as int) =~= old(stack)@.subrange(0, dst as int));
        assert(stack@.subrange(dst as int, dst + t.arity) =~= old(stack)@.subrange(src as int, sp as int));
    }
    dst + t.arity as usize
}

pub proof fn lemma_move(s1: Seq<u64>, s2: Seq<u64>, fp: int, base: int, sp1: int, h: int, a: int, sp2: int)
    requires
        0 <= fp <= base, 0 <= h, 0 <= a, base + h + a <= sp1 <= s1.len(), s1.len() == s2.len(),
        sp2 == base + h + a,
        s2.subrange(0, base + h) == s1.subrange(0, base + h),
        s2.subrange(base + h, sp2) == s1.subrange(sp1 - a, sp1),
    ensures
        s2.subrange(base, sp2) == s1.subrange(base, sp1).subrange(0, h)
            + s1.subrange(base, sp1).subrange(sp1 - base - a, sp1 - base),
        s2.subrange(0, fp) == s1.subrange(0, fp),
        s2.subrange(fp, base) == s1.subrange(fp, base),
{
    assert(s2.subrange(0, fp) =~= s2.subrange(0, base + h).subrange(0, fp));
    assert(s1.subrange(0, fp) =~= s1.subrange(0, base + h).subrange(0, fp));
    assert(s2.subrange(fp, base) =~= s2.subrange(0, base + h).subrange(fp, base));
    assert(s1.subrange(fp, base) =~= s1.subrange(0, base + h).subrange(fp, base));
    assert(s2.subrange(base, base + h) =~= s2.subrange(0, base + h).subrange(base, base + h));
    assert(s1.subrange(base, base + h) =~= s1.subrange(0, base + h).subrange(base, base + h));
    assert(s2.subrange(base, sp2) =~= s2.subrange(base, base + h) + s2.subrange(base + h, sp2));
    assert(s1.subrange(base, sp1).subrange(0, h) =~= s1.subrange(base, base + h));
    assert(s1.subrange(base, sp1).subrange(sp1 - base - a, sp1 - base) =~= s1.subrange(sp1 - a, sp1));
}

/// Branches to label `k` from `f2`, the top frame with `sp - sp1`
/// operands popped.
#[inline(always)]
fn do_jump(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, base: usize, sp1: usize,
    t: BrTarget, Ghost(k): Ghost<nat>, Ghost(c): Ghost<Config>) -> (r: (usize, usize))
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        base == fp + n_locals(m, top(c).func),
        base <= sp1 <= sp,
        step(m, c) == br(c, popn(top(c), (sp - sp1) as nat), k),
        br_ok(cs[top(c).func as int], top(c).pc as int, k, (sp - sp1) as nat),
        t == target_of(cs[top(c).func as int], top(c).pc as int, k),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        stepped(m, c, final(stack)@, calls, fp as int, r.0 as int, r.1 as int, c.store),
        r.1 == t.pc,
{
    proof { lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int); }
    let ghost f = top(c);
    let ghost s1 = stack@;
    let ghost pops = (sp - sp1) as nat;
    let ghost f2 = popn(f, pops);
    proof {
        lemma_pop(s1, base as int, sp as int, pops as int);
        lemma_br_frame(m, cs, c, f2, k, pops);
    }
    let sp2 = move_down(stack, base, sp1, t);
    proof {
        let g = exit_label(f2, k, t.pc as nat)->Some_0;
        lemma_move(s1, stack@, fp as int, base as int, sp1 as int, t.height as int, t.arity as int, sp2 as int);
        lemma_mach_top(m, s1, stack@, calls, fp as int, sp as int, c, g, sp2 as int);
    }
    (sp2, t.pc as usize)
}

/// `if`, `else`, `br`, `br_if`, `br_table` and `return`.
#[inline(always)]
pub fn do_branch(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    code: &Code, stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, pc: usize,
    i: Instr, Ghost(c): Ghost<Config>) -> (r: (usize, usize))
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        cur(m, c) == i,
        i is If || i is Else || i is Br || i is BrIf || i is BrTable || i is Return,
        *code == codes[top(c).func as int],
        pc == top(c).pc,
    ensures
        final(stack)@.len() == old(stack)@.len(),
        stepped(m, c, final(stack)@, calls, fp as int, r.0 as int, r.1 as int, c.store),
        r.1 == pc + 1 || crate::rcheck::entry_at(code, r.1 as int),
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    let ghost s1 = stack@;
    let base = fp + code.n_locals as usize;
    proof {
        assert(side_ok(m, fc, code.side@, code.table@, pc as int, i));
        assert(f.stack.subrange(0, f.stack.len() as int) =~= f.stack);
        assert(popn(f, 0) == f);
        assert(crate::rcheck::rcode_ok(m, f.func, fc, code));
        assert(crate::rcheck::if_ok(code, m.funcs@[f.func as int].body@[pc as int]));
    }
    match i {
        Instr::If { bt, else_, end } => {
            let cnd = lo(sget(stack, sp - 1));
            proof {
                lemma_peek(s1, base as int, sp as int, 0);
                lemma_pop(s1, base as int, sp as int, 1);
            }
            let npc = if cnd != 0 {
                pc + 1
            } else if else_ == end {
                end as usize
            } else {
                else_ as usize + 1
            };
            proof {
                let (np, nr) = bt_arity(m, bt)->Some_0;
                let g = popn(f, 1);
                let lb = Label { arity: nr, cont: (end + 1) as nat, height: (f.stack.len() - 1 - np) as nat };
                let g2 = Frame { pc: npc as nat, labels: g.labels.push(lb), ..g };
                assert(step(m, c) == next(c, g2));
                lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, g2, sp - 1);
            }
            (sp - 1, npc)
        },
        Instr::BrIf(k) => {
            let cnd = lo(sget(stack, sp - 1));
            proof { lemma_peek(s1, base as int, sp as int, 0); }
            if cnd == 0 {
                proof {
                    lemma_pop(s1, base as int, sp as int, 1);
                    let g = adv(popn(f, 1));
                    assert(step(m, c) == next(c, g));
                    lemma_mach_top(m, s1, s1, calls, fp as int, sp as int, c, g, sp - 1);
                }
                (sp - 1, pc + 1)
            } else {
                proof { crate::rrun::lemma_target_entry(m, cs, f.func, code, pc as int, k as nat, 1); }
                do_jump(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, base, sp - 1,
                    vget(&code.side, pc), Ghost(k as nat), Ghost(c))
            }
        },
        Instr::BrTable { start, len } => {
            let kk = lo(sget(stack, sp - 1));
            proof { lemma_peek(s1, base as int, sp as int, 0); }
            let j = if kk < len - 1 { kk } else { len - 1 };
            let _ = code.table.len();
            let t = vget(&code.table, vget(&code.side, pc).pc as usize + j as usize);
            let ghost k = m.br_table@[start + j] as nat;
            proof {
                assert(br_ok(fc, pc as int, k, 1));
                crate::rrun::lemma_target_entry(m, cs, f.func, code, pc as int, k, 1);
            }
            do_jump(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, base, sp - 1, t, Ghost(k), Ghost(c))
        },
        Instr::Br(k) => {
            proof { crate::rrun::lemma_target_entry(m, cs, f.func, code, pc as int, k as nat, 0); }
            do_jump(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, base, sp,
                vget(&code.side, pc), Ghost(k as nat), Ghost(c))
        },
        Instr::Else { .. } => {
            proof {
                assert(nth_id(fc.labels@, lab(fc, pc as int), 0) == Some(lab(fc, pc as int)));
                crate::rrun::lemma_target_entry(m, cs, f.func, code, pc as int, 0, 0);
            }
            do_jump(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, base, sp,
                vget(&code.side, pc), Ghost(0), Ghost(c))
        },
        _ => {
            proof { crate::rrun::lemma_target_entry(m, cs, f.func, code, pc as int, (f.labels.len() - 1) as nat, 0); }
            do_jump(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, base, sp,
                vget(&code.side, pc), Ghost((f.labels.len() - 1) as nat), Ghost(c))
        },
    }
}


// ---------------------------------------------------------------------------
// Calls and returns
// ---------------------------------------------------------------------------

/// A run that takes one more ordinary step.
pub proof fn lemma_advance(m: &Module, cs: Seq<FuncCert>, c0: Config, hs: Seq<HostResp>, n: nat, c: Config)
    requires
        certs_ok(m, cs),
        inv(m, cs, c),
        run(m, c0, hs, n) == Outcome::Running(c),
        step(m, c) is Next,
    ensures
        inv(m, cs, step(m, c)->Next_0),
        run(m, c0, hs, n + 1) == Outcome::Running(step(m, c)->Next_0),
{
    lemma_step(m, cs, c);
    lemma_run_step(m, c0, hs, n, c);
}

pub proof fn lemma_lower_pop(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int)
    requires lower_ok(m, s, calls, fr, fp), calls.len() >= 1,
    ensures
        lower_ok(m, s, calls.drop_last(), fr.drop_last(), calls.last().fp as int),
        lower_frame_ok(m, s, calls, fr, fp, calls.len() - 1),
{
    let c2 = calls.drop_last();
    let f2 = fr.drop_last();
    let top = calls.last().fp as int;
    assert(lower_frame_ok(m, s, calls, fr, fp, calls.len() - 1));
    assert forall|k: int| 0 <= k < c2.len() implies #[trigger] lower_frame_ok(m, s, c2, f2, top, k) by {
        assert(lower_frame_ok(m, s, calls, fr, fp, k));
        assert(c2[k] == calls[k]);
        assert(f2[k] == fr[k]);
        assert(next_fp(c2, k, top) == next_fp(calls, k, fp));
        lemma_fp_mono(m, s, calls, fr, fp, k);
    }
}

/// Frame pointers grow toward the top.
pub proof fn lemma_fp_mono(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int, k: int)
    requires lower_ok(m, s, calls, fr, fp), 0 <= k < calls.len() - 1,
    ensures next_fp(calls, k, fp) <= calls.last().fp,
    decreases calls.len() - k,
{
    if k + 1 < calls.len() - 1 {
        lemma_fp_mono(m, s, calls, fr, fp, k + 1);
        assert(lower_frame_ok(m, s, calls, fr, fp, k + 1));
    }
}

pub proof fn lemma_lower_push(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int,
    cf: CallFrame, f: Frame, fp2: int)
    requires
        lower_ok(m, s, calls, fr, fp),
        cf.fp == fp,
        f.func == cf.func as nat, f.pc == cf.pc as nat,
        fp + n_locals(m, f.func) <= fp2,
        f.locals == s.subrange(fp, fp + n_locals(m, f.func)),
        f.stack == s.subrange(fp + n_locals(m, f.func), fp2),
    ensures
        lower_ok(m, s, calls.push(cf), fr.push(f), fp2),
{
    let c2 = calls.push(cf);
    let f2 = fr.push(f);
    assert forall|k: int| 0 <= k < c2.len() implies #[trigger] lower_frame_ok(m, s, c2, f2, fp2, k) by {
        if k < calls.len() {
            assert(lower_frame_ok(m, s, calls, fr, fp, k));
            assert(next_fp(c2, k, fp2) == next_fp(calls, k, fp));
        }
    }
}

#[inline(always)]
fn vt_eq(a: ValType, b: ValType) -> (r: bool)
    ensures r == (a == b),
{
    match (a, b) {
        (ValType::I32, ValType::I32) | (ValType::I64, ValType::I64)
        | (ValType::F32, ValType::F32) | (ValType::F64, ValType::F64) => true,
        _ => false,
    }
}

fn vts_eq(a: &Vec<ValType>, b: &Vec<ValType>) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if !vt_eq(a[i], b[i]) {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

pub fn same_type_x(a: &FuncType, b: &FuncType) -> (r: bool)
    ensures r == same_type(a, b),
{
    vts_eq(&a.params, &b.params) && vts_eq(&a.results, &b.results)
}

fn copy_out(stack: &Vec<u64>, from: usize, n: usize) -> (r: Vec<u64>)
    requires from + n <= stack@.len(), stack@.len() <= MAX_STACK,
    ensures r@ == stack@.subrange(from as int, from + n),
{
    let mut r = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            from + n <= stack@.len(),
            stack@.len() <= MAX_STACK,
            i <= n,
            r@ == stack@.subrange(from as int, from + i),
        decreases n - i,
    {
        r.push(sget(stack, from + i));
        assert(r@ =~= stack@.subrange(from as int, from + i + 1));
        i += 1;
    }
    r
}

fn copy_back(stack: &mut Vec<u64>, at: usize, v: &Vec<u64>)
    requires at + v@.len() <= old(stack)@.len(), old(stack)@.len() <= MAX_STACK,
    ensures
        final(stack)@.len() == old(stack)@.len(),
        final(stack)@.subrange(0, at as int) == old(stack)@.subrange(0, at as int),
        final(stack)@.subrange(at as int, at + v@.len()) == v@,
{
    let mut i = 0;
    while i < v.len()
        invariant
            at + v@.len() <= stack@.len(),
            stack@.len() == old(stack)@.len(),
            stack@.len() <= MAX_STACK,
            i <= v@.len(),
            stack@.subrange(0, at as int) == old(stack)@.subrange(0, at as int),
            stack@.subrange(at as int, at + i) == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        let ghost s1 = stack@;
        sset(stack, at + i, v[i]);
        assert(stack@.subrange(0, at as int) =~= s1.subrange(0, at as int));
        assert(stack@.subrange(at as int, at + i + 1) =~= v@.subrange(0, i + 1));
        i += 1;
    }
    assert(v@.subrange(0, v@.len() as int) =~= v@);
}


/// The frames below the top fit on the stack with their whole frames.
pub open spec fn calls_fit(codes: Seq<Code>, calls: Seq<CallFrame>, len: nat) -> bool {
    forall|k: int| 0 <= k < calls.len() ==> (#[trigger] calls[k]).func < codes.len()
        && calls[k].fp + codes[calls[k].func as int].frame <= len
}

/// A call to defined function `x - n_imp(m)` from the top frame with
/// `sp - sp1` operands (the table index) already popped. Returns the
/// callee's frame pointer and stack pointer, or `None` when its frame or
/// the call depth does not fit.
#[inline(always)]
fn do_call(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, codes: &Vec<Code>,
    stack: &mut Vec<u64>, calls: &mut Vec<CallFrame>, d: usize, pc: usize, fp: usize, sp: usize, sp1: usize,
    x: usize, Ghost(c): Ghost<Config>) -> (r: Option<(usize, usize)>)
    requires
        pre(m, cs, codes@, c, old(stack)@, old(calls)@, fp as int, sp as int),
        d == top(c).func, pc == top(c).pc,
        sp1 <= sp,
        x >= n_imp(m), x < m.func_types@.len(),
        step(m, c) == call(m, c, popn(top(c), (sp - sp1) as nat), x as nat),
        n_params(func_type(m, x as nat)) + fp + n_locals(m, d as nat) <= sp1,
        calls_fit(codes@, old(calls)@, old(stack)@.len()),
        old(calls)@.len() <= MAX_CALLS,
    ensures
        final(stack)@.len() == old(stack)@.len(),
        match r {
            Some((fp2, sp2)) => {
                &&& step(m, c) is Next
                &&& mach_ok(m, final(stack)@, final(calls)@, fp2 as int, sp2 as int, step(m, c)->Next_0)
                &&& top(step(m, c)->Next_0).func == x - n_imp(m)
                &&& top(step(m, c)->Next_0).pc == 0
                &&& fp2 + codes@[x - n_imp(m)].frame <= final(stack)@.len()
                &&& calls_fit(codes@, final(calls)@, final(stack)@.len())
                &&& final(calls)@.len() <= MAX_CALLS
                &&& (step(m, c)->Next_0).store == c.store
                &&& final(calls)@ == old(calls)@.push(CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 })
            },
            None => *final(stack) == *old(stack) && *final(calls) == *old(calls),
        },
{
    proof { lemma_facts(m, cs, codes@, c, stack@, calls@, fp as int, sp as int); }
    let dd = x - m.n_imported_funcs as usize;
    let code2 = &codes[dd];
    proof {
        assert(code_ok(m, cs, dd as nat, &codes@[dd as int]));
        assert(dd as nat + n_imp(m) == x);
        assert(n_locals(m, dd as nat) <= MAX_LOCALS as nat);
    }
    let np = code2.n_params as usize;
    let nl2 = code2.n_locals as usize;
    let fp2 = sp1 - np;
    if calls.len() >= MAX_CALLS || code2.frame as usize > stack.len() - fp2 {
        return None;
    }
    let ghost s1 = stack@;
    let ghost f = top(c);
    let ghost f1 = popn(f, (sp - sp1) as nat);
    let ghost nl = n_locals(m, d as nat);
    szero(stack, sp1, nl2 - np);
    calls.push(CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 });
    proof {
        let t = func_type(m, x as nat);
        let args = f1.stack.subrange(f1.stack.len() - np, f1.stack.len() as int);
        let caller = popn(f1, np as nat);
        let nf = new_frame(m, dd as nat, args);
        let c2 = step(m, c)->Next_0;
        assert(c2.frames == c.frames.update(c.frames.len() - 1, caller).push(nf));
        lemma_pop(s1, fp + nl, sp as int, (sp - sp1) as int);
        // The callee's locals: the arguments, then zeros.
        assert(stack@.subrange(fp2 as int, fp2 + nl2) =~= args + Seq::new((nl2 - np) as nat, |_i| 0u64));
        assert(nl2 == np + m.funcs@[dd as int].locals@.len());
        assert(nf.locals =~= args + Seq::new((nl2 - np) as nat, |_i| 0u64));
        assert(stack@.subrange(fp2 + nl2, fp2 + nl2) =~= nf.stack);
        // The caller keeps its locals and its stack below the arguments.
        assert(stack@.subrange(0, sp1 as int) =~= s1.subrange(0, sp1 as int));
        assert(stack@.subrange(fp as int, fp + nl) =~= s1.subrange(fp as int, fp + nl));
        assert(stack@.subrange(fp + nl, fp2 as int) =~= caller.stack);
        assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
        let lower = c.frames.subrange(0, c.frames.len() - 1);
        lemma_lower_same(m, s1, stack@, old(calls)@, lower, fp as int);
        lemma_lower_push(m, stack@, old(calls)@, lower, fp as int,
            CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 }, caller, fp2 as int);
        assert(c2.frames.subrange(0, c2.frames.len() - 1) =~= lower.push(caller));
        assert(calls@ == old(calls)@.push(CallFrame { func: d as u32, pc: pc as u32, fp: fp as u32 }));
        assert forall|k: int| 0 <= k < calls@.len() implies (#[trigger] calls@[k]).func < codes@.len()
            && calls@[k].fp + codes@[calls@[k].func as int].frame <= stack@.len() by {
            if k < old(calls)@.len() {
                assert(calls@[k] == old(calls)@[k]);
            }
        }
    }
    Some((fp2, fp2 + nl2))
}

/// Returns from the top frame (at `pc == body.len()`) to its caller.
#[inline(always)]
fn do_ret(Ghost(m): Ghost<&Module>, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, calls: &mut Vec<CallFrame>, fp: usize, sp: usize, nr: usize,
    Ghost(c): Ghost<Config>) -> (r: CallFrame)
    requires
        certs_ok(m, cs), codes_ok(m, cs, codes), inv(m, cs, c),
        mach_ok(m, old(stack)@, old(calls)@, fp as int, sp as int, c),
        old(calls)@.len() >= 1,
        top(c).pc == m.funcs@[top(c).func as int].body@.len(),
        nr == n_results(func_type(m, top(c).func + n_imp(m))),
        old(stack)@.len() <= MAX_STACK,
    ensures
        r == old(calls)@.last(),
        final(calls)@ == old(calls)@.drop_last(),
        final(stack)@.len() == old(stack)@.len(),
        step(m, c) is Next,
        mach_ok(m, final(stack)@, final(calls)@, r.fp as int, fp + nr, step(m, c)->Next_0),
        top(step(m, c)->Next_0).func == r.func,
        top(step(m, c)->Next_0).pc == r.pc + 1,
        (step(m, c)->Next_0).store == c.store,
        fp + nr <= sp,
{
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    let ghost s1 = stack@;
    let ghost nl = n_locals(m, f.func);
    proof {
        assert(func_cert_ok(m, f.func, fc));
        assert(frame_at(m, cs, f));
    }
    let cf = calls.pop().unwrap();
    proof {
        let lower = c.frames.subrange(0, c.frames.len() - 1);
        lemma_lower_pop(m, s1, old(calls)@, lower, fp as int);
        assert(lower_frame_ok(m, s1, old(calls)@, lower, fp as int, old(calls)@.len() - 1));
    }
    scopy_down(stack, fp, sp - nr, nr);
    proof {
        let n = c.frames.len();
        let caller = c.frames[n - 2];
        let res = f.stack.subrange(f.stack.len() - nr, f.stack.len() as int);
        let g = Frame { pc: caller.pc + 1, stack: caller.stack + res, ..caller };
        let c2 = step(m, c)->Next_0;
        assert(c2.frames == c.frames.subrange(0, n - 1).update(n - 2, g));
        let cnl = n_locals(m, cf.func as nat);
        assert(stack@.subrange(0, fp as int) =~= s1.subrange(0, fp as int));
        assert(stack@.subrange(cf.fp as int, cf.fp + cnl) =~= s1.subrange(cf.fp as int, cf.fp + cnl));
        assert(stack@.subrange(cf.fp + cnl, fp + nr) =~= g.stack);
        let lower2 = c.frames.subrange(0, n - 2);
        assert(lower2 =~= c.frames.subrange(0, n - 1).drop_last());
        assert(stack@.subrange(0, cf.fp as int) =~= s1.subrange(0, cf.fp as int));
        lemma_lower_same(m, s1, stack@, calls@, lower2, cf.fp as int);
        assert(c2.frames.subrange(0, c2.frames.len() - 1) =~= lower2);
    }
    cf
}


/// Store fields a host call cannot change.
pub open spec fn host_frame(a: &Store, b: &Store) -> bool {
    &&& a.mem@.len() == b.mem@.len()
    &&& a.mem_max == b.mem_max
    &&& a.globals@ == b.globals@
    &&& a.tables@ == b.tables@
    &&& a.dropped@ == b.dropped@
}

/// Calls imported function `x` with the top operands as arguments.
#[inline(always)]
fn do_host<H: Host>(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, sp1: usize, x: usize,
    st: &mut Store, host: &mut H, Ghost(c): Ghost<Config>) -> (r: (Option<usize>, Ghost<Seq<u64>>))
    requires
        pre(m, cs, codes, c, old(stack)@, calls, fp as int, sp as int),
        sp1 <= sp,
        x < n_imp(m), x < m.func_types@.len(),
        step(m, c) == call(m, c, popn(top(c), (sp - sp1) as nat), x as nat),
        n_params(func_type(m, x as nat)) + fp + n_locals(m, top(c).func) <= sp1,
        sp1 - n_params(func_type(m, x as nat)) + n_results(func_type(m, x as nat))
            <= fp + codes[top(c).func as int].frame,
        c.store == store_view(old(st)),
        store_wf(old(st)),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        store_wf(final(st)),
        host_frame(old(st), final(st)),
        step(m, c) is Host,
        match r.0 {
            Some(sp2) => {
                let cfg = step(m, c)->cfg;
                &&& r.1@.len() == n_results(func_type(m, x as nat))
                &&& mach_ok(m, final(stack)@, calls, fp as int, sp2 as int, resume(cfg, store_view(final(st)), r.1@))
            },
            None => true,
        },
{
    proof { lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int); }
    let t = &m.types[m.func_types[x] as usize];
    let np = t.params.len();
    let nr = t.results.len();
    let args = copy_out(stack, sp1 - np, np);
    let mut results: Vec<u64> = vec![0u64; nr];
    let ok = call_host(host, x as u32, args.as_slice(), &mut results, &mut st.mem);
    if !ok {
        return (None, Ghost(results@));
    }
    let ghost s1 = stack@;
    copy_back(stack, sp1 - np, &results);
    proof {
        let f = top(c);
        let nl = n_locals(m, f.func);
        let f1 = popn(f, (sp - sp1) as nat);
        let caller = popn(f1, np as nat);
        let cfg = step(m, c)->cfg;
        assert(cfg == with_top(c, caller));
        let c2 = resume(cfg, store_view(st), results@);
        let g = top(c2);
        lemma_pop(s1, fp + nl, sp as int, (sp - sp1 + np) as int);
        let at = (sp1 - np) as int;
        assert(stack@.subrange(0, fp as int) =~= stack@.subrange(0, at).subrange(0, fp as int));
        assert(s1.subrange(0, fp as int) =~= s1.subrange(0, at).subrange(0, fp as int));
        assert(stack@.subrange(fp as int, fp + nl) =~= stack@.subrange(0, at).subrange(fp as int, fp + nl));
        assert(s1.subrange(fp as int, fp + nl) =~= s1.subrange(0, at).subrange(fp as int, fp + nl));
        assert(stack@.subrange(fp + nl, at) =~= stack@.subrange(0, at).subrange(fp + nl, at));
        assert(s1.subrange(fp + nl, at) =~= s1.subrange(0, at).subrange(fp + nl, at));
        assert(caller.stack =~= s1.subrange(fp + nl, at));
        assert(stack@.subrange(fp + nl, sp1 - np + nr) =~= stack@.subrange(fp + nl, at) + stack@.subrange(at, at + nr));
        assert(stack@.subrange(fp + nl, sp1 - np + nr) =~= caller.stack + results@);
        assert(g == Frame { pc: f.pc + 1, stack: caller.stack + results@, ..caller });
        let lower = c.frames.subrange(0, c.frames.len() - 1);
        lemma_lower_same(m, s1, stack@, calls, lower, fp as int);
        assert(c2.frames.subrange(0, c2.frames.len() - 1) =~= lower);
    }
    (Some(sp1 - np + nr), Ghost(results@))
}


// ---------------------------------------------------------------------------
// The loop
// ---------------------------------------------------------------------------

/// What [`execute`] guarantees: the spec, run for `n` steps from `c0`
/// with host responses `hs`, ends exactly as the interpreter did.
#[verifier::opaque]
pub open spec fn executed(m: &Module, c0: Config, hs: Seq<HostResp>, n: nat, r: Result<Seq<u64>, Trap>,
    s: crate::sem::Store) -> bool
{
    match r {
        Ok(res) => run(m, c0, hs, n) == Outcome::Done(res, s),
        Err(t) => run(m, c0, hs, n) == Outcome::Trap(t, s)
            || (t == Trap::Exhausted && run(m, c0, hs, n) is Running && (run(m, c0, hs, n)->Running_0).store == s),
    }
}

#[verifier::opaque]
pub open spec fn loop_inv(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, hs: Seq<HostResp>, n: nat,
    c: Config, s: Seq<u64>, calls: Seq<CallFrame>, d: usize, pc: usize, fp: usize, sp: usize, st: &Store) -> bool
{
    &&& certs_ok(m, cs)
    &&& codes_ok(m, cs, codes)
    &&& inv(m, cs, c)
    &&& run(m, c0, hs, n) == Outcome::Running(c)
    &&& mach_ok(m, s, calls, fp as int, sp as int, c)
    &&& c.store == store_view(st)
    &&& store_wf(st)
    &&& d == top(c).func
    &&& pc == top(c).pc
    &&& d < codes.len()
    &&& fp + codes[d as int].frame <= s.len()
    &&& s.len() <= MAX_STACK
    &&& calls.len() <= MAX_CALLS
    &&& calls_fit(codes, calls, s.len())
}

proof fn lemma_pre(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, hs: Seq<HostResp>, n: nat,
    c: Config, s: Seq<u64>, calls: Seq<CallFrame>, d: usize, pc: usize, fp: usize, sp: usize, st: &Store, i: Instr)
    requires
        loop_inv(m, cs, codes, c0, hs, n, c, s, calls, d, pc, fp, sp, st),
        pc < codes[d as int].ops@.len(),
        i == codes[d as int].ops@[pc as int],
        i != Instr::Unreachable,
    ensures
        pre(m, cs, codes, c, s, calls, fp as int, sp as int),
        cur(m, c) == i,
{
    reveal(loop_inv);
    assert(code_ok(m, cs, d as nat, &codes[d as int]));
    assert(frame_at(m, cs, top(c)));
}

proof fn lemma_call_step(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, fp: usize, sp: usize, x: nat)
    requires
        pre(m, cs, codes, c, s, calls, fp as int, sp as int),
        x <= u32::MAX,
        cur(m, c) == Instr::Call(x as u32),
    ensures
        x < m.func_types@.len(),
        step(m, c) == call(m, c, popn(top(c), 0), x),
        n_params(func_type(m, x)) + fp + n_locals(m, top(c).func) <= sp,
        sp - n_params(func_type(m, x)) + n_results(func_type(m, x)) <= fp + codes[top(c).func as int].frame,
{
    lemma_facts(m, cs, codes, c, s, calls, fp as int, sp as int);
    lemma_step_instr(m, c);
    reveal(step_instr);
    let f = top(c);
    let i = cur(m, c);
    assert(!is_unop(i) && !is_binop(i));
    assert(x < m.func_types@.len());
    assert(m.func_types@[x as int] < m.types@.len());
    assert(f.stack.subrange(0, f.stack.len() as int) =~= f.stack);
    assert(popn(f, 0) == f);
    let fc = cs[f.func as int];
    let np = n_params(func_type(m, x));
    let nr = n_results(func_type(m, x));
    assert(live(fc, (f.pc + 1) as int));
    assert(hgt(fc, (f.pc + 1) as int) == f.stack.len() - np + nr);
    assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
}

/// Resolves a `call_indirect`: the callee, or the trap.
fn indirect(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>, stack: &Vec<u64>,
    Ghost(calls): Ghost<Seq<CallFrame>>, fp: usize, sp: usize, st: &Store, ty: u32, table: u32,
    Ghost(c): Ghost<Config>) -> (r: Result<usize, Trap>)
    requires
        pre(m, cs, codes, c, stack@, calls, fp as int, sp as int),
        cur(m, c) == (Instr::CallIndirect { ty, table }),
        c.store == store_view(st),
    ensures
        match r {
            Ok(x) => {
                &&& x < m.func_types@.len()
                &&& step(m, c) == call(m, c, popn(top(c), 1), x as nat)
                &&& sp >= 1
                &&& n_params(func_type(m, x as nat)) + fp + n_locals(m, top(c).func) <= sp - 1
                &&& sp - 1 - n_params(func_type(m, x as nat)) + n_results(func_type(m, x as nat))
                    <= fp + codes[top(c).func as int].frame
            },
            Err(t) => step(m, c) == Step::Trap(t, c.store) && t != Trap::Exhausted,
        },
{
    proof {
        lemma_facts(m, cs, codes, c, stack@, calls, fp as int, sp as int);
        lemma_step_instr(m, c);
        reveal(step_instr);
    }
    let ghost f = top(c);
    let ghost fc = cs[f.func as int];
    proof {
        let i = cur(m, c);
        assert(!is_unop(i) && !is_binop(i));
        assert(f.stack[f.stack.len() - 1] == stack@[sp - 1]);
        assert(live(fc, (f.pc + 1) as int));
    }
    let k = lo(sget(stack, sp - 1)) as usize;
    let tab = &st.tables[table as usize];
    proof {
        assert(store_view(st).tables[table as int] == view_tab(tab@));
    }
    if k >= tab.len() {
        return Err(Trap::TableOutOfBounds);
    }
    let x = vget(tab, k);
    proof { assert(view_tab(tab@)[k as int] == (if x == NONE { None } else { Some(x as nat) })); }
    if x == NONE {
        return Err(Trap::UninitializedElement);
    }
    proof {
        assert(c.store.tables[table as int][k as int] is Some);
        assert(x < m.func_types@.len());
        assert(m.func_types@[x as int] < m.types@.len());
    }
    let ft = &m.types[m.func_types[x as usize] as usize];
    if !same_type_x(ft, &m.types[ty as usize]) {
        return Err(Trap::IndirectCallTypeMismatch);
    }
    proof {
        let np = n_params(func_type(m, x as nat));
        let nr = n_results(func_type(m, x as nat));
        assert(n_params(func_type(m, x as nat)) == n_params(&m.types@[ty as int]));
        assert(n_results(func_type(m, x as nat)) == n_results(&m.types@[ty as int]));
        assert(hgt(fc, (f.pc + 1) as int) <= fc.max_height);
    }
    Ok(x as usize)
}

pub open spec fn is_local(i: Instr) -> bool {
    !(i is Unreachable || i is Call || i is CallIndirect || i is MemoryGrow)
}

/// One instruction that stays in the current frame (everything but calls
/// and the final return), as one loop iteration of [`execute`].
#[inline(always)]
fn local_step(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, Ghost(codes): Ghost<Seq<Code>>, code: &Code,
    stack: &mut Vec<u64>, Ghost(calls): Ghost<Seq<CallFrame>>, d: usize, pc: usize, fp: usize, sp: usize,
    st: &mut Store, i: Instr, Ghost(c0): Ghost<Config>, Ghost(hs): Ghost<Seq<HostResp>>, Ghost(n): Ghost<nat>,
    Ghost(c): Ghost<Config>) -> (r: Result<(usize, usize, Ghost<Config>), Trap>)
    requires
        loop_inv(m, cs, codes, c0, hs, n, c, old(stack)@, calls, d, pc, fp, sp, old(st)),
        *code == codes[d as int],
        pc < code.ops@.len(),
        i == code.ops@[pc as int],
        is_local(i),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        match r {
            Ok((sp2, pc2, c2)) => loop_inv(m, cs, codes, c0, hs, n + 1, c2@, final(stack)@, calls, d, pc2, fp, sp2, final(st))
                && (pc2 == pc + 1 || crate::rcheck::entry_at(code, pc2 as int)),
            Err(t) => executed(m, c0, hs, n + 1, Err(t), store_view(final(st))) && store_wf(final(st))
                && store_ok(m, store_view(final(st))),
        },
{
    proof { reveal(loop_inv); reveal(executed); }
    let mut pc = pc;
    let mut sp = sp;
    let ghost mut c = c;
    let ghost mut n = n;
    proof {
        assert(code_ok(m, cs, d as nat, &codes[d as int]));
        assert(frame_at(m, cs, top(c)));
        assert(func_cert_ok(m, d as nat, cs[d as int]));
    }
    match i {
            Instr::I32Eqz | Instr::I32Clz | Instr::I32Ctz | Instr::I32Popcnt | Instr::I64Eqz |
            Instr::I64Clz | Instr::I64Ctz | Instr::I64Popcnt | Instr::I32WrapI64 | Instr::I64ExtendI32S |
            Instr::I64ExtendI32U | Instr::I32Extend8S | Instr::I32Extend16S | Instr::I64Extend8S |
            Instr::I64Extend16S | Instr::I64Extend32S | Instr::FUn(_) | Instr::Cvt(_) => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                match do_unop(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, i, Ghost(c)) {
                    Ok(()) => {
                        proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                        pc = pc + 1;
                    },
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Err(t);
                    },
                }
            },
            Instr::I32Eq | Instr::I32Ne | Instr::I32LtS | Instr::I32LtU | Instr::I32GtS | Instr::I32GtU |
            Instr::I32LeS | Instr::I32LeU | Instr::I32GeS | Instr::I32GeU | Instr::I32Add | Instr::I32Sub |
            Instr::I32Mul | Instr::I32DivS | Instr::I32DivU | Instr::I32RemS | Instr::I32RemU |
            Instr::I32And | Instr::I32Or | Instr::I32Xor | Instr::I32Shl | Instr::I32ShrS | Instr::I32ShrU |
            Instr::I32Rotl | Instr::I32Rotr | Instr::I64Eq | Instr::I64Ne | Instr::I64LtS | Instr::I64LtU |
            Instr::I64GtS | Instr::I64GtU | Instr::I64LeS | Instr::I64LeU | Instr::I64GeS | Instr::I64GeU |
            Instr::I64Add | Instr::I64Sub | Instr::I64Mul | Instr::I64DivS | Instr::I64DivU |
            Instr::I64RemS | Instr::I64RemU | Instr::I64And | Instr::I64Or | Instr::I64Xor | Instr::I64Shl |
            Instr::I64ShrS | Instr::I64ShrU | Instr::I64Rotl | Instr::I64Rotr | Instr::FBin(_) |
            Instr::FCmp(_) => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                match do_binop(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, i, Ghost(c)) {
                    Ok(()) => {
                        proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                        pc = pc + 1;
                        sp = sp - 1;
                    },
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Err(t);
                    },
                }
            },
            Instr::I32Load(_) | Instr::I64Load(_) | Instr::F32Load(_) | Instr::F64Load(_) |
            Instr::I32Load8S(_) | Instr::I32Load8U(_) | Instr::I32Load16S(_) | Instr::I32Load16U(_) |
            Instr::I64Load8S(_) | Instr::I64Load8U(_) | Instr::I64Load16S(_) | Instr::I64Load16U(_) |
            Instr::I64Load32S(_) | Instr::I64Load32U(_) => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                match do_load(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, st, i, Ghost(c)) {
                    Ok(()) => {
                        proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                        pc = pc + 1;
                    },
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Err(t);
                    },
                }
            },
            Instr::I32Store(_) | Instr::I64Store(_) | Instr::F32Store(_) | Instr::F64Store(_) |
            Instr::I32Store8(_) | Instr::I32Store16(_) | Instr::I64Store8(_) | Instr::I64Store16(_) |
            Instr::I64Store32(_) => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                match do_store(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, st, i, Ghost(c)) {
                    Ok(()) => {
                        proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                        pc = pc + 1;
                        sp = sp - 2;
                    },
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Err(t);
                    },
                }
            },
            Instr::Nop | Instr::Block { .. } | Instr::Loop { .. } | Instr::End => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                do_nop(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, i, Ghost(c));
                proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                pc = pc + 1;
            },
            Instr::LocalGet(_) | Instr::LocalSet(_) | Instr::LocalTee(_) | Instr::GlobalGet(_)
            | Instr::GlobalSet(_) | Instr::I32Const(_) | Instr::I64Const(_) | Instr::F32Const(_)
            | Instr::F64Const(_) | Instr::Drop | Instr::Select => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                sp = do_var(Ghost(m), Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, st, i, Ghost(c));
                proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                pc = pc + 1;
            },
            Instr::MemorySize | Instr::MemoryFill | Instr::MemoryCopy
            | Instr::MemoryInit(_) | Instr::DataDrop(_) => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                match do_mem(m, Ghost(cs), Ghost(codes), stack, Ghost(calls), fp, sp, st, i, Ghost(c)) {
                    Ok(sp2) => {
                        proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                        pc = pc + 1;
                        sp = sp2;
                    },
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Err(t);
                    },
                }
            },
            Instr::If { .. } | Instr::Else { .. } | Instr::Br(_) | Instr::BrIf(_) | Instr::BrTable { .. }
            | Instr::Return => {
                proof { lemma_pre(m, cs, codes, c0, hs, n, c, stack@, calls, d, pc, fp, sp, st, i); }
                let (sp2, pc2) = do_branch(Ghost(m), Ghost(cs), Ghost(codes), code, stack, Ghost(calls), fp, sp, pc, i, Ghost(c));
                proof { lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1; }
                sp = sp2;
                pc = pc2;
            },
            _ => {
                proof { assert(false); }
                return Err(Trap::Unreachable);
            },
    }
    Ok((sp, pc, Ghost(c)))
}

pub enum Flow {
    Go { d: usize, pc: usize, fp: usize, sp: usize, c: Ghost<Config>, hs: Ghost<Seq<HostResp>>, n: Ghost<nat> },
    Stop(Result<Vec<u64>, Trap>, Ghost<Seq<HostResp>>, Ghost<nat>),
}

/// Calls, `call_indirect`, returns, `memory.grow` (whose outcome the run
/// records in `hs`) and `unreachable`, as one loop iteration of [`execute`].
#[inline(always)]
fn special_step<H: Host>(m: &Module, Ghost(cs): Ghost<Seq<FuncCert>>, codes: &Vec<Code>, stack: &mut Vec<u64>,
    calls: &mut Vec<CallFrame>, host: &mut H, st: &mut Store, d: usize, pc: usize, fp: usize, sp: usize, i: Instr,
    Ghost(c0): Ghost<Config>, Ghost(hs): Ghost<Seq<HostResp>>, Ghost(n): Ghost<nat>, Ghost(c): Ghost<Config>)
    -> (r: Flow)
    requires
        loop_inv(m, cs, codes@, c0, hs, n, c, old(stack)@, old(calls)@, d, pc, fp, sp, old(st)),
        pc < codes@[d as int].ops@.len(),
        i == codes@[d as int].ops@[pc as int],
        !is_local(i),
        crate::rrun::calls_ret(codes@, old(calls)@),
        pc + 1 < codes@[d as int].ops@.len() ==> crate::rcheck::entry_at(&codes@[d as int], pc + 1),
    ensures
        final(stack)@.len() == old(stack)@.len(),
        match r {
            Flow::Go { d: d2, pc: pc2, fp: fp2, sp: sp2, c: c2, hs: hs2, n: n2 } => d2 < codes@.len() &&
                loop_inv(m, cs, codes@, c0, hs2@, n2@, c2@, final(stack)@, final(calls)@, d2, pc2, fp2, sp2, final(st))
                && crate::rrun::calls_ret(codes@, final(calls)@)
                && crate::rcheck::entry_at(&codes@[d2 as int], pc2 as int),
            Flow::Stop(res, hs2, n2) =>
                executed(m, c0, hs2@, n2@, match res { Ok(v) => Ok(v@), Err(t) => Err(t) }, store_view(final(st)))
                && store_wf(final(st)) && store_ok(m, store_view(final(st))),
        },
{
    proof { reveal(loop_inv); reveal(executed); }
    let mut d = d;
    let mut pc = pc;
    let mut fp = fp;
    let mut sp = sp;
    let ghost mut c = c;
    let ghost mut hs = hs;
    let ghost mut n = n;
    let code = &codes[d];
    proof {
        assert(code_ok(m, cs, d as nat, &codes@[d as int]));
        assert(frame_at(m, cs, top(c)));
        assert(func_cert_ok(m, d as nat, cs[d as int]));
    }
    match i {
            Instr::Unreachable => {
                if pc == code.ops.len() - 1 {
                    // pc == body.len(): return.
                    let nr = code.n_results as usize;
                    proof {
                        let f = top(c);
                        let fc = cs[f.func as int];
                        assert(func_cert_ok(m, f.func, fc));
                        lemma_step(m, cs, c);
                        lemma_run_step(m, c0, hs, n, c);
                    }
                    if calls.len() == 0 {
                        let res = copy_out(stack, sp - nr, nr);
                        proof {
                            let f = top(c);
                            assert(res@ =~= f.stack.subrange(f.stack.len() - nr, f.stack.len() as int));
                        }
                        return Flow::Stop(Ok(res), Ghost(hs), Ghost(n + 1));
                    }
                    let cf = do_ret(Ghost(m), Ghost(cs), Ghost(codes@), stack, calls, fp, sp, nr, Ghost(c));
                    proof {
                        let k = old(calls)@.len() - 1;
                        assert(old(calls)@[k] == cf);
                        assert(crate::rcheck::entry_at(&codes@[cf.func as int], cf.pc + 1));
                        assert forall|j: int| 0 <= j < calls@.len() implies
                            crate::rcheck::entry_at(&codes@[(#[trigger] calls@[j]).func as int], calls@[j].pc + 1) by {
                            assert(calls@[j] == old(calls)@[j]);
                        }
                        lemma_advance(m, cs, c0, hs, n, c);
                        assert(calls_fit(codes@, old(calls)@, stack@.len()) || true);
                        c = step(m, c)->Next_0;
                        n = n + 1;
                    }
                    sp = fp + nr;
                    fp = cf.fp as usize;
                    d = cf.func as usize;
                    pc = cf.pc as usize + 1;
                    proof {
                        assert(calls_fit(codes@, calls@, stack@.len()));
                    }
                } else {
                    proof {
                        lemma_step_instr(m, c);
                        reveal(step_instr);
                        lemma_run_step(m, c0, hs, n, c);
                    }
                    return Flow::Stop(Err(Trap::Unreachable), Ghost(hs), Ghost(n + 1));
                }
            },
            Instr::Call(x) => {
                proof {
                    lemma_pre(m, cs, codes@, c0, hs, n, c, stack@, calls@, d, pc, fp, sp, st, i);
                    lemma_call_step(m, cs, codes@, c, stack@, calls@, fp, sp, x as nat);
                }
                if (x as usize) < m.n_imported_funcs as usize {
                    let ghost st0 = store_view(st);
                    let (r, Ghost(res)) = do_host(m, Ghost(cs), Ghost(codes@), stack, Ghost(calls@), fp, sp, sp, x as usize, st, host, Ghost(c));
                    proof { lemma_step(m, cs, c); }
                    match r {
                        Some(sp2) => {
                            let ghost resp = HostResp::Ok(store_view(st), res);
                            proof {
                                lemma_run_host(m, c0, hs, n, c, resp);
                                assert(store_ok(m, store_view(st)));
                                lemma_resume(m, cs, step(m, c)->cfg, x as nat, store_view(st), res);
                                c = resume(step(m, c)->cfg, store_view(st), res);
                                hs = hs.push(resp);
                                n = n + 1;
                            }
                            sp = sp2;
                            proof { assert(pc + 1 < codes@[d as int].ops@.len()); }
                            pc = pc + 1;
                        },
                        None => {
                            let ghost resp = HostResp::Trap(store_view(st));
                            proof { lemma_run_host(m, c0, hs, n, c, resp); }
                            return Flow::Stop(Err(Trap::Host), Ghost(hs.push(resp)), Ghost(n + 1));
                        },
                    }
                } else {
                    match do_call(m, Ghost(cs), codes, stack, calls, d, pc, fp, sp, sp, x as usize, Ghost(c)) {
                        Some((fp2, sp2)) => {
                            proof {
                                lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1;
                                crate::rrun::lemma_calls_push(m, cs, codes@, old(calls)@, d, pc, fp);
                                crate::rrun::lemma_entry0(m, cs, codes@, (x - n_imp(m)) as nat);
                            }
                            d = x as usize - m.n_imported_funcs as usize;
                            pc = 0;
                            fp = fp2;
                            sp = sp2;
                        },
                        None => {
                            return Flow::Stop(Err(Trap::Exhausted), Ghost(hs), Ghost(n));
                        },
                    }
                }
            },
            Instr::MemoryGrow => {
                proof { lemma_pre(m, cs, codes@, c0, hs, n, c, stack@, calls@, d, pc, fp, sp, st, i); }
                let b = do_grow(Ghost(m), Ghost(cs), Ghost(codes@), stack, Ghost(calls@), fp, sp, st, Ghost(c));
                proof {
                    lemma_step(m, cs, c);
                    match b@ {
                        None => {
                            lemma_advance(m, cs, c0, hs, n, c);
                            c = step(m, c)->Next_0;
                        },
                        Some(ok) => {
                            lemma_run_grow(m, c0, hs, n, c, ok);
                            c = if ok { step(m, c)->ok } else { step(m, c)->fail };
                            hs = hs.push(HostResp::Grow(ok));
                        },
                    }
                    n = n + 1;
                }
                proof { assert(pc + 1 < codes@[d as int].ops@.len()); }
                pc = pc + 1;
            },
            Instr::CallIndirect { ty, table } => {
                proof { lemma_pre(m, cs, codes@, c0, hs, n, c, stack@, calls@, d, pc, fp, sp, st, i); }
                let x = match indirect(m, Ghost(cs), Ghost(codes@), stack, Ghost(calls@), fp, sp, st, ty, table, Ghost(c)) {
                    Ok(x) => x,
                    Err(t) => {
                        proof { lemma_run_step(m, c0, hs, n, c); }
                        return Flow::Stop(Err(t), Ghost(hs), Ghost(n + 1));
                    },
                };
                if x < m.n_imported_funcs as usize {
                    let (r, Ghost(res)) = do_host(m, Ghost(cs), Ghost(codes@), stack, Ghost(calls@), fp, sp, sp - 1, x, st, host, Ghost(c));
                    proof { lemma_step(m, cs, c); }
                    match r {
                        Some(sp2) => {
                            let ghost resp = HostResp::Ok(store_view(st), res);
                            proof {
                                lemma_run_host(m, c0, hs, n, c, resp);
                                lemma_resume(m, cs, step(m, c)->cfg, x as nat, store_view(st), res);
                                c = resume(step(m, c)->cfg, store_view(st), res);
                                hs = hs.push(resp);
                                n = n + 1;
                            }
                            sp = sp2;
                            proof { assert(pc + 1 < codes@[d as int].ops@.len()); }
                            pc = pc + 1;
                        },
                        None => {
                            let ghost resp = HostResp::Trap(store_view(st));
                            proof { lemma_run_host(m, c0, hs, n, c, resp); }
                            return Flow::Stop(Err(Trap::Host), Ghost(hs.push(resp)), Ghost(n + 1));
                        },
                    }
                } else {
                    match do_call(m, Ghost(cs), codes, stack, calls, d, pc, fp, sp, sp - 1, x, Ghost(c)) {
                        Some((fp2, sp2)) => {
                            proof {
                                lemma_advance(m, cs, c0, hs, n, c); c = step(m, c)->Next_0; n = n + 1;
                                crate::rrun::lemma_calls_push(m, cs, codes@, old(calls)@, d, pc, fp);
                                crate::rrun::lemma_entry0(m, cs, codes@, (x - n_imp(m)) as nat);
                            }
                            d = x - m.n_imported_funcs as usize;
                            pc = 0;
                            fp = fp2;
                            sp = sp2;
                        },
                        None => {
                            return Flow::Stop(Err(Trap::Exhausted), Ghost(hs), Ghost(n));
                        },
                    }
                }
            },
            _ => {
                proof { assert(false); }
            },
    }
    proof { assert(loop_inv(m, cs, codes@, c0, hs, n, c, stack@, calls@, d, pc, fp, sp, st)); }
    Flow::Go { d, pc, fp, sp, c: Ghost(c), hs: Ghost(hs), n: Ghost(n) }
}

proof fn lemma_init(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, pc: usize, fp: usize, sp: usize, st: &Store)
    requires
        certs_ok(m, cs),
        codes_ok(m, cs, codes),
        inv(m, cs, c0),
        mach_ok(m, s, calls, fp as int, sp as int, c0),
        c0.store == store_view(st),
        store_wf(st),
        d == top(c0).func,
        pc == top(c0).pc,
        d < codes.len(),
        fp + codes[d as int].frame <= s.len(),
        s.len() <= MAX_STACK,
        calls.len() == 0,
        calls_fit(codes, calls, s.len()),
    ensures loop_inv(m, cs, codes, c0, Seq::empty(), 0, c0, s, calls, d, pc, fp, sp, st),
{
    reveal(loop_inv);
    reveal_with_fuel(run, 1);
}

proof fn lemma_loop_pc(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, hs: Seq<HostResp>, n: nat,
    c: Config, s: Seq<u64>, calls: Seq<CallFrame>, d: usize, pc: usize, fp: usize, sp: usize, st: &Store)
    requires loop_inv(m, cs, codes, c0, hs, n, c, s, calls, d, pc, fp, sp, st),
    ensures d < codes.len(), pc < codes[d as int].ops@.len(),
{
    reveal(loop_inv);
    assert(code_ok(m, cs, d as nat, &codes[d as int]));
    assert(frame_at(m, cs, top(c)));
}

/// Stopping for lack of fuel at an operation is an allowed outcome.
proof fn lemma_out_of_fuel(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>, c0: Config, g: GS, s: Seq<u64>,
    calls: Seq<CallFrame>, d: usize, rpc: usize, fp: usize, st: &Store)
    requires rinv(m, cs, codes, c0, g, s, calls, d, rpc, fp, st),
    ensures
        executed(m, c0, g.hs, g.n, Err(Trap::Exhausted), store_view(st)),
        store_wf(st),
        store_ok(m, store_view(st)),
{
    reveal(rinv);
    reveal(loop_inv);
    reveal(executed);
}

/// Runs defined function `d0` from the configuration `c0` the caller set
/// up (the arguments and zeroed locals at the bottom of `stack`).
#[verifier::exec_allows_no_decreases_clause]
#[verifier::spinoff_prover]
// Kept below 1431: Verus multiplies by 3,000,000, and Z3 prints a resource
// count above 2^32 as a decimal, which Verus cannot parse (it panics with
// "expected rlimit-count in smt statistics"). Under the cap, running out
// is reported as an ordinary rlimit error instead.
#[verifier::rlimit(1400)]
pub fn execute<H: Host>(m: &Module, codes: &Vec<Code>, Ghost(cs): Ghost<Seq<FuncCert>>, st: &mut Store,
    stack: &mut Vec<u64>, calls: &mut Vec<CallFrame>, host: &mut H, d0: usize, Ghost(c0): Ghost<Config>)
    -> (r: (Result<Vec<u64>, Trap>, Ghost<Seq<HostResp>>, Ghost<nat>))
    requires
        certs_ok(m, cs),
        codes_ok(m, cs, codes@),
        inv(m, cs, c0),
        c0.frames.len() == 1,
        top(c0).func == d0,
        top(c0).pc == 0,
        c0.store == store_view(old(st)),
        store_wf(old(st)),
        old(calls)@.len() == 0,
        old(stack)@.len() <= MAX_STACK,
        d0 < codes@.len(),
        top_ok(m, old(stack)@, top(c0), 0, n_locals(m, d0 as nat) as int),
        codes@[d0 as int].frame <= old(stack)@.len(),
    ensures
        store_wf(final(st)),
        store_ok(m, store_view(final(st))),
        final(stack)@.len() == old(stack)@.len(),
        executed(m, c0, r.1@, r.2@, match r.0 { Ok(v) => Ok(v@), Err(t) => Err(t) }, store_view(final(st))),
{
    let mut d = d0;
    let mut fp: usize = 0;
    let mut code = &codes[d0];
    let ghost sp: usize = code.n_locals as usize;
    proof {
        assert(code_ok(m, cs, d0 as nat, &codes@[d0 as int]));
        assert(c0.frames.subrange(0, 0) =~= Seq::<Frame>::empty());
        assert(calls_fit(codes@, calls@, stack@.len()));
        lemma_init(m, cs, codes@, c0, stack@, calls@, d, 0, fp, sp, st);
    }
    let ghost mut g = GS { c: c0, hs: Seq::empty(), n: 0, pc: 0, sp };
    proof { lemma_rinit(m, cs, codes@, c0, g, stack@, calls@, d, fp, st); }
    let mut rops: &[ROp] = code.rops.as_slice();
    let mut rpc: usize = 0;
    // The operation as a pointer, and the accumulator: the last value
    // operation's result, which the `A_` codes read in place of slot `a`.
    let mut cur = cur_at(rops, 0);
    let mut acc: u64 = 0;
    proof {
        lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
        lemma_acc_start(m, cs, codes@, c0, g, stack@, calls@, d, fp, st);
    }
    loop
        invariant
            rinv(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st),
            *code == codes@[d as int],
            rops@ == code.rops@,
            cur.seq() == rops@, cur.idx() == rpc as int,
            acc_ok(codes@, d, rpc, acc, stack@, fp),
            stack@.len() == old(stack)@.len(),
    {
        proof { lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st); lemma_pre_hand(); }
        let r = cur_get(cur);
        match r.op {
            OpCode::Skip => {
                let g2 = r_skip(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Copy => {
                let g2 = r_copy(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, false, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::P_Copy => {
                let g2 = r_copy(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, true, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Sel => {
                let g2 = r_sel(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Const => {
                let g2 = r_const(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::BrIf => {
                let (rpc2, cur2, g2) = r_brif(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, stack, fp, st, r, false, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::A_BrIf => {
                let (rpc2, cur2, g2) = r_brif(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, stack, fp, st, r, false, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::BrIfZ => {
                let (rpc2, cur2, g2) = r_brif(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, stack, fp, st, r, true, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::A_BrIfZ => {
                let (rpc2, cur2, g2) = r_brif(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, stack, fp, st, r, true, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::Br => {
                let (rpc2, cur2, g2) = r_br(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, stack, fp, st, r, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::UnG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_un(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::BinRRG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_bin_rr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::BinRIG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_bin_ri(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::LoadG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::StoreRRG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_store_rr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::StoreRIG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_store_ri(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) }
                }
            },
            OpCode::BrIfRRG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let (rpc2, cur2, g2) = r_brif_rr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, op, stack, fp, st, r, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::BrIfRIG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let (rpc2, cur2, g2) = r_brif_ri(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                    Ghost(d), rpc, op, stack, fp, st, r, rops, cur, acc);
                rpc = rpc2;
                cur = cur2;
                proof { g = g2@; }
            },
            OpCode::Op => {
                // Runs the instruction at `r.pc` as a stack instruction.
                proof {
                    lemma_rfacts(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                    reveal(rinv);
                    lemma_loop_pc(m, cs, codes@, c0, g.hs, g.n, g.c, stack@, calls@, d, g.pc, fp, g.sp, st);
                }
                let pc = r.pc as usize;
                let sp = fp + r.a as usize;
                let i = vget(&code.ops, pc);
                proof {
                    if pc + 1 < code.ops@.len() {
                        assert(code.ops@.len() == m.funcs@[d as int].body@.len() + 1);
                        lemma_next_op(m, d as nat, cs[d as int], code, rpc as int);
                    }
                }
                match i {
                    Instr::Unreachable | Instr::Call(_) | Instr::CallIndirect { .. } | Instr::MemoryGrow => {
                        match special_step(m, Ghost(cs), codes, stack, calls, host, st, d, pc, fp, sp, i,
                            Ghost(c0), Ghost(g.hs), Ghost(g.n), Ghost(g.c)) {
                            Flow::Go { d: d2, pc: pc2, fp: fp2, sp: sp2, c: c2, hs: hs2, n: n2 } => {
                                d = d2;
                                fp = fp2;
                                code = &codes[d];
                                rops = code.rops.as_slice();
                                rpc = vget(&code.entry, pc2) as usize;
                                proof {
                                    g = GS { c: c2@, hs: hs2@, n: n2@, pc: pc2, sp: sp2 };
                                    reveal(rinv);
                                    lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                                }
                                cur = cur_at(rops, rpc);
                                acc = r_acc_fix(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                                    Ghost(d), Ghost(rpc), stack, fp, st, cur_get(cur), acc);
                            },
                            Flow::Stop(r, hs2, n2) => return (r, hs2, n2),
                        }
                    },
                    _ => {
                        match local_step(m, Ghost(cs), Ghost(codes@), code, stack, Ghost(calls@), d, pc, fp, sp, st, i,
                            Ghost(c0), Ghost(g.hs), Ghost(g.n), Ghost(g.c)) {
                            Ok((sp2, pc2, c2)) => {
                                rpc = vget(&code.entry, pc2) as usize;
                                proof {
                                    g = GS { c: c2@, hs: g.hs, n: g.n + 1, pc: pc2, sp: sp2 };
                                    reveal(rinv);
                                    lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                                }
                                cur = cur_at(rops, rpc);
                                acc = r_acc_fix(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                                    Ghost(d), Ghost(rpc), stack, fp, st, cur_get(cur), acc);
                            },
                            Err(t) => return (Err(t), Ghost(g.hs), Ghost(g.n + 1)),
                        }
                    },
                }
            },
            // BEGIN GENERATED ARMS
            OpCode::Un_I32Eqz => { let ghost l0 = stack@.len(); match s_Un_I32Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Un_I32Eqz => { let ghost l0 = stack@.len(); match s_P_Un_I32Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I64Eqz => { let ghost l0 = stack@.len(); match s_Un_I64Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Un_I64Eqz => { let ghost l0 = stack@.len(); match s_P_Un_I64Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I32Clz => { let ghost l0 = stack@.len(); match s_Un_I32Clz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I32Ctz => { let ghost l0 = stack@.len(); match s_Un_I32Ctz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I32WrapI64 => { let ghost l0 = stack@.len(); match s_Un_I32WrapI64(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Un_I32WrapI64 => { let ghost l0 = stack@.len(); match s_P_Un_I32WrapI64(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I64ExtendI32S => { let ghost l0 = stack@.len(); match s_Un_I64ExtendI32S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Un_I64ExtendI32S => { let ghost l0 = stack@.len(); match s_P_Un_I64ExtendI32S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I64ExtendI32U => { let ghost l0 = stack@.len(); match s_Un_I64ExtendI32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Un_I64ExtendI32U => { let ghost l0 = stack@.len(); match s_P_Un_I64ExtendI32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I32Extend8S => { let ghost l0 = stack@.len(); match s_Un_I32Extend8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_I32Extend16S => { let ghost l0 = stack@.len(); match s_Un_I32Extend16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_F64Neg => { let ghost l0 = stack@.len(); match s_Un_F64Neg(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_F64Abs => { let ghost l0 = stack@.len(); match s_Un_F64Abs(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Un_F64Sqrt => { let ghost l0 = stack@.len(); match s_Un_F64Sqrt(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Eq => { let ghost l0 = stack@.len(); match s_BinRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Eq => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Eq => { let ghost l0 = stack@.len(); match s_BinRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Eq => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Ne => { let ghost l0 = stack@.len(); match s_BinRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Ne => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Ne => { let ghost l0 = stack@.len(); match s_BinRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Ne => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32LtS => { let ghost l0 = stack@.len(); match s_BinRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32LtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32LtS => { let ghost l0 = stack@.len(); match s_BinRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32LtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32LtU => { let ghost l0 = stack@.len(); match s_BinRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32LtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32LtU => { let ghost l0 = stack@.len(); match s_BinRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32LtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32GtS => { let ghost l0 = stack@.len(); match s_BinRR_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32GtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32GtS => { let ghost l0 = stack@.len(); match s_BinRI_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32GtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32GtU => { let ghost l0 = stack@.len(); match s_BinRR_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32GtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32GtU => { let ghost l0 = stack@.len(); match s_BinRI_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32GtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32LeS => { let ghost l0 = stack@.len(); match s_BinRR_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32LeS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32LeS => { let ghost l0 = stack@.len(); match s_BinRI_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32LeS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32LeU => { let ghost l0 = stack@.len(); match s_BinRR_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32LeU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32LeU => { let ghost l0 = stack@.len(); match s_BinRI_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32LeU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32GeS => { let ghost l0 = stack@.len(); match s_BinRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32GeS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32GeS => { let ghost l0 = stack@.len(); match s_BinRI_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32GeS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32GeU => { let ghost l0 = stack@.len(); match s_BinRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32GeU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32GeU => { let ghost l0 = stack@.len(); match s_BinRI_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32GeU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Eq => { let ghost l0 = stack@.len(); match s_BinRR_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Eq => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Eq => { let ghost l0 = stack@.len(); match s_BinRI_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Eq => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Ne => { let ghost l0 = stack@.len(); match s_BinRR_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Ne => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Ne => { let ghost l0 = stack@.len(); match s_BinRI_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Ne => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64LtS => { let ghost l0 = stack@.len(); match s_BinRR_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64LtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64LtS => { let ghost l0 = stack@.len(); match s_BinRI_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64LtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64LtU => { let ghost l0 = stack@.len(); match s_BinRR_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64LtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64LtU => { let ghost l0 = stack@.len(); match s_BinRI_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64LtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64GtS => { let ghost l0 = stack@.len(); match s_BinRR_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64GtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64GtS => { let ghost l0 = stack@.len(); match s_BinRI_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64GtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64GtU => { let ghost l0 = stack@.len(); match s_BinRR_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64GtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64GtU => { let ghost l0 = stack@.len(); match s_BinRI_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64GtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64LeS => { let ghost l0 = stack@.len(); match s_BinRR_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64LeS => { let ghost l0 = stack@.len(); match s_BinRI_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64LeU => { let ghost l0 = stack@.len(); match s_BinRR_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64LeU => { let ghost l0 = stack@.len(); match s_BinRI_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64GeS => { let ghost l0 = stack@.len(); match s_BinRR_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64GeS => { let ghost l0 = stack@.len(); match s_BinRI_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64GeU => { let ghost l0 = stack@.len(); match s_BinRR_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64GeU => { let ghost l0 = stack@.len(); match s_BinRI_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Add => { let ghost l0 = stack@.len(); match s_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Add => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32Add => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Add => { let ghost l0 = stack@.len(); match s_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Add => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Add => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32And => { let ghost l0 = stack@.len(); match s_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32And => { let ghost l0 = stack@.len(); match s_P_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32And => { let ghost l0 = stack@.len(); match s_A_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32And => { let ghost l0 = stack@.len(); match s_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32And => { let ghost l0 = stack@.len(); match s_P_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32And => { let ghost l0 = stack@.len(); match s_A_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Or => { let ghost l0 = stack@.len(); match s_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Or => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32Or => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Or => { let ghost l0 = stack@.len(); match s_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Or => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Or => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Shl => { let ghost l0 = stack@.len(); match s_BinRR_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Shl => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32ShrS => { let ghost l0 = stack@.len(); match s_BinRR_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32ShrS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_A_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32ShrU => { let ghost l0 = stack@.len(); match s_BinRR_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32ShrU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_A_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Rotl => { let ghost l0 = stack@.len(); match s_BinRR_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Rotl => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I32Rotr => { let ghost l0 = stack@.len(); match s_BinRR_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I32Rotr => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Add => { let ghost l0 = stack@.len(); match s_BinRR_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Add => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Add => { let ghost l0 = stack@.len(); match s_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Add => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_BinRI_I64Add => { let ghost l0 = stack@.len(); match s_A_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Sub => { let ghost l0 = stack@.len(); match s_BinRR_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Sub => { let ghost l0 = stack@.len(); match s_BinRI_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Mul => { let ghost l0 = stack@.len(); match s_BinRR_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Mul => { let ghost l0 = stack@.len(); match s_BinRI_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64And => { let ghost l0 = stack@.len(); match s_BinRR_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64And => { let ghost l0 = stack@.len(); match s_P_BinRR_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64And => { let ghost l0 = stack@.len(); match s_BinRI_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64And => { let ghost l0 = stack@.len(); match s_P_BinRI_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Or => { let ghost l0 = stack@.len(); match s_BinRR_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Or => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Or => { let ghost l0 = stack@.len(); match s_BinRI_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Or => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Xor => { let ghost l0 = stack@.len(); match s_BinRR_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Xor => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Xor => { let ghost l0 = stack@.len(); match s_BinRI_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Xor => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Shl => { let ghost l0 = stack@.len(); match s_BinRR_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64Shl => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Shl => { let ghost l0 = stack@.len(); match s_BinRI_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64Shl => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64ShrS => { let ghost l0 = stack@.len(); match s_BinRR_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64ShrS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64ShrS => { let ghost l0 = stack@.len(); match s_BinRI_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64ShrS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64ShrU => { let ghost l0 = stack@.len(); match s_BinRR_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_I64ShrU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64ShrU => { let ghost l0 = stack@.len(); match s_BinRI_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_I64ShrU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Rotl => { let ghost l0 = stack@.len(); match s_BinRR_I64Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Rotl => { let ghost l0 = stack@.len(); match s_BinRI_I64Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_I64Rotr => { let ghost l0 = stack@.len(); match s_BinRR_I64Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_I64Rotr => { let ghost l0 = stack@.len(); match s_BinRI_I64Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F32Add => { let ghost l0 = stack@.len(); match s_BinRR_F32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F32Add => { let ghost l0 = stack@.len(); match s_BinRI_F32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F32Sub => { let ghost l0 = stack@.len(); match s_BinRR_F32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F32Sub => { let ghost l0 = stack@.len(); match s_BinRI_F32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F32Mul => { let ghost l0 = stack@.len(); match s_BinRR_F32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F32Mul => { let ghost l0 = stack@.len(); match s_BinRI_F32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F32Div => { let ghost l0 = stack@.len(); match s_BinRR_F32Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F32Div => { let ghost l0 = stack@.len(); match s_BinRI_F32Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F64Add => { let ghost l0 = stack@.len(); match s_BinRR_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_F64Add => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F64Add => { let ghost l0 = stack@.len(); match s_BinRI_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_F64Add => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F64Sub => { let ghost l0 = stack@.len(); match s_BinRR_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_F64Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F64Sub => { let ghost l0 = stack@.len(); match s_BinRI_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_F64Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F64Mul => { let ghost l0 = stack@.len(); match s_BinRR_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_F64Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F64Mul => { let ghost l0 = stack@.len(); match s_BinRI_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_F64Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRR_F64Div => { let ghost l0 = stack@.len(); match s_BinRR_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRR_F64Div => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BinRI_F64Div => { let ghost l0 = stack@.len(); match s_BinRI_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_BinRI_F64Div => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I32Load => { let ghost l0 = stack@.len(); match s_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I32Load => { let ghost l0 = stack@.len(); match s_P_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_Load_I32Load => { let ghost l0 = stack@.len(); match s_A_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I64Load => { let ghost l0 = stack@.len(); match s_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I64Load => { let ghost l0 = stack@.len(); match s_P_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_Load_I64Load => { let ghost l0 = stack@.len(); match s_A_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_F32Load => { let ghost l0 = stack@.len(); match s_Load_F32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_F32Load => { let ghost l0 = stack@.len(); match s_P_Load_F32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_F64Load => { let ghost l0 = stack@.len(); match s_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_F64Load => { let ghost l0 = stack@.len(); match s_P_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_Load_F64Load => { let ghost l0 = stack@.len(); match s_A_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I32Load8S => { let ghost l0 = stack@.len(); match s_Load_I32Load8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I32Load8S => { let ghost l0 = stack@.len(); match s_P_Load_I32Load8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I32Load8U => { let ghost l0 = stack@.len(); match s_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I32Load8U => { let ghost l0 = stack@.len(); match s_P_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_Load_I32Load8U => { let ghost l0 = stack@.len(); match s_A_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I32Load16S => { let ghost l0 = stack@.len(); match s_Load_I32Load16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I32Load16S => { let ghost l0 = stack@.len(); match s_P_Load_I32Load16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I32Load16U => { let ghost l0 = stack@.len(); match s_Load_I32Load16U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I32Load16U => { let ghost l0 = stack@.len(); match s_P_Load_I32Load16U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I64Load8U => { let ghost l0 = stack@.len(); match s_Load_I64Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I64Load8U => { let ghost l0 = stack@.len(); match s_P_Load_I64Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::Load_I64Load32U => { let ghost l0 = stack@.len(); match s_Load_I64Load32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_Load_I64Load32U => { let ghost l0 = stack@.len(); match s_P_Load_I64Load32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_A_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_A_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I64Store => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I64Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I64Store => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I64Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_F32Store => { let ghost l0 = stack@.len(); match s_StoreRR_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_F32Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_F32Store => { let ghost l0 = stack@.len(); match s_StoreRI_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_F32Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_A_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_F64Store => { let ghost l0 = stack@.len(); match s_StoreRI_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_F64Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I32Store8 => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I32Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::A_StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_A_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I32Store16 => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I32Store16 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I32Store16 => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I32Store16 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I64Store8 => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I64Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I64Store8 => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I64Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRR_I64Store32 => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRR_I64Store32 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::StoreRI_I64Store32 => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::P_StoreRI_I64Store32 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2) } } },
            OpCode::BrIfRR_I32Eq => { let (rpc2, cur2, g2) = s_BrIfRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32Eq => { let (rpc2, cur2, g2) = s_BrIfRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32Eq => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRI_I32Eq => { let (rpc2, cur2, g2) = s_A_BrIfRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32Ne => { let (rpc2, cur2, g2) = s_BrIfRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32Ne => { let (rpc2, cur2, g2) = s_BrIfRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32Ne => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRI_I32Ne => { let (rpc2, cur2, g2) = s_A_BrIfRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32LtS => { let (rpc2, cur2, g2) = s_BrIfRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32LtS => { let (rpc2, cur2, g2) = s_BrIfRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32LtS => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRI_I32LtS => { let (rpc2, cur2, g2) = s_A_BrIfRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32LtU => { let (rpc2, cur2, g2) = s_BrIfRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32LtU => { let (rpc2, cur2, g2) = s_BrIfRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32LtU => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRI_I32LtU => { let (rpc2, cur2, g2) = s_A_BrIfRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32GtS => { let (rpc2, cur2, g2) = s_BrIfRR_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32GtS => { let (rpc2, cur2, g2) = s_BrIfRI_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32GtU => { let (rpc2, cur2, g2) = s_BrIfRR_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32GtU => { let (rpc2, cur2, g2) = s_BrIfRI_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32LeS => { let (rpc2, cur2, g2) = s_BrIfRR_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32LeS => { let (rpc2, cur2, g2) = s_BrIfRI_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32LeU => { let (rpc2, cur2, g2) = s_BrIfRR_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32LeU => { let (rpc2, cur2, g2) = s_BrIfRI_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32GeS => { let (rpc2, cur2, g2) = s_BrIfRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32GeS => { let (rpc2, cur2, g2) = s_BrIfRI_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32GeS => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I32GeU => { let (rpc2, cur2, g2) = s_BrIfRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I32GeU => { let (rpc2, cur2, g2) = s_BrIfRI_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::A_BrIfRR_I32GeU => { let (rpc2, cur2, g2) = s_A_BrIfRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64Eq => { let (rpc2, cur2, g2) = s_BrIfRR_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64Eq => { let (rpc2, cur2, g2) = s_BrIfRI_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64Ne => { let (rpc2, cur2, g2) = s_BrIfRR_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64Ne => { let (rpc2, cur2, g2) = s_BrIfRI_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64LtS => { let (rpc2, cur2, g2) = s_BrIfRR_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64LtS => { let (rpc2, cur2, g2) = s_BrIfRI_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64LtU => { let (rpc2, cur2, g2) = s_BrIfRR_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64LtU => { let (rpc2, cur2, g2) = s_BrIfRI_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64GtS => { let (rpc2, cur2, g2) = s_BrIfRR_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64GtS => { let (rpc2, cur2, g2) = s_BrIfRI_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64GtU => { let (rpc2, cur2, g2) = s_BrIfRR_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64GtU => { let (rpc2, cur2, g2) = s_BrIfRI_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64LeS => { let (rpc2, cur2, g2) = s_BrIfRR_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64LeS => { let (rpc2, cur2, g2) = s_BrIfRI_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64LeU => { let (rpc2, cur2, g2) = s_BrIfRR_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64LeU => { let (rpc2, cur2, g2) = s_BrIfRI_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64GeS => { let (rpc2, cur2, g2) = s_BrIfRR_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64GeS => { let (rpc2, cur2, g2) = s_BrIfRI_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRR_I64GeU => { let (rpc2, cur2, g2) = s_BrIfRR_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            OpCode::BrIfRI_I64GeU => { let (rpc2, cur2, g2) = s_BrIfRI_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            // END GENERATED ARMS
        }
    }
}


/// [`execute`] with `fuel` units of fuel; returns the fuel left (`r.3`).
///
/// Every branch operation and every operation run as a stack instruction
/// (calls and returns among them) costs one unit, and the run stops with
/// [`Trap::Exhausted`] when an operation that costs fuel finds none left,
/// which `executed` allows at any point. Every loop iteration and every
/// call goes through one of these, so a run with finite fuel ends.
///
/// The loop is [`execute`]'s, except that all the branch codes share one
/// arm, which charges and then dispatches again (`s_branch`): with an exit
/// for running out of fuel in each branch code's own arm, the loop's proof
/// exceeds its resource limit (as it does with a `break` in each), and
/// with them merged it takes a few minutes. With the check, the second
/// dispatch costs metered runs 8 to 35% more instructions on the
/// benchmarks; unmetered runs use [`execute`], which has neither. The loop
/// has no `decreases` clause.
#[verifier::exec_allows_no_decreases_clause]
#[verifier::spinoff_prover]
// Kept below 1431: Verus multiplies by 3,000,000, and Z3 prints a resource
// count above 2^32 as a decimal, which Verus cannot parse (it panics with
// "expected rlimit-count in smt statistics"). Under the cap, running out
// is reported as an ordinary rlimit error instead.
#[verifier::rlimit(1400)]
pub fn execute_metered<H: Host>(m: &Module, codes: &Vec<Code>, Ghost(cs): Ghost<Seq<FuncCert>>, st: &mut Store,
    stack: &mut Vec<u64>, calls: &mut Vec<CallFrame>, host: &mut H, d0: usize, Ghost(c0): Ghost<Config>,
    fuel: u64) -> (r: (Result<Vec<u64>, Trap>, Ghost<Seq<HostResp>>, Ghost<nat>, u64))
    requires
        certs_ok(m, cs),
        codes_ok(m, cs, codes@),
        inv(m, cs, c0),
        c0.frames.len() == 1,
        top(c0).func == d0,
        top(c0).pc == 0,
        c0.store == store_view(old(st)),
        store_wf(old(st)),
        old(calls)@.len() == 0,
        old(stack)@.len() <= MAX_STACK,
        d0 < codes@.len(),
        top_ok(m, old(stack)@, top(c0), 0, n_locals(m, d0 as nat) as int),
        codes@[d0 as int].frame <= old(stack)@.len(),
    ensures
        store_wf(final(st)),
        store_ok(m, store_view(final(st))),
        final(stack)@.len() == old(stack)@.len(),
        executed(m, c0, r.1@, r.2@, match r.0 { Ok(v) => Ok(v@), Err(t) => Err(t) }, store_view(final(st))),
{
    let mut fl = fuel;
    let mut d = d0;
    let mut fp: usize = 0;
    let mut code = &codes[d0];
    let ghost sp: usize = code.n_locals as usize;
    proof {
        assert(code_ok(m, cs, d0 as nat, &codes@[d0 as int]));
        assert(c0.frames.subrange(0, 0) =~= Seq::<Frame>::empty());
        assert(calls_fit(codes@, calls@, stack@.len()));
        lemma_init(m, cs, codes@, c0, stack@, calls@, d, 0, fp, sp, st);
    }
    let ghost mut g = GS { c: c0, hs: Seq::empty(), n: 0, pc: 0, sp };
    proof { lemma_rinit(m, cs, codes@, c0, g, stack@, calls@, d, fp, st); }
    let mut rops: &[ROp] = code.rops.as_slice();
    let mut rpc: usize = 0;
    // The operation as a pointer, and the accumulator: the last value
    // operation's result, which the `A_` codes read in place of slot `a`.
    let mut cur = cur_at(rops, 0);
    let mut acc: u64 = 0;
    proof {
        lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
        lemma_acc_start(m, cs, codes@, c0, g, stack@, calls@, d, fp, st);
    }
    loop
        invariant
            rinv(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st),
            *code == codes@[d as int],
            rops@ == code.rops@,
            cur.seq() == rops@, cur.idx() == rpc as int,
            acc_ok(codes@, d, rpc, acc, stack@, fp),
            stack@.len() == old(stack)@.len(),
    {
        proof { lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st); lemma_pre_hand(); }
        let r = cur_get(cur);
        match r.op {
            OpCode::Skip => {
                let g2 = r_skip(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Copy => {
                let g2 = r_copy(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, false, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::P_Copy => {
                let g2 = r_copy(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, true, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Sel => {
                let g2 = r_sel(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::Const => {
                let g2 = r_const(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, r, &mut acc);
                rpc = rpc + 1;
                cur = cur_next(cur);
                proof { g = g2@; }
            },
            OpCode::UnG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_un(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::BinRRG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_bin_rr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::BinRIG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_bin_ri(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::LoadG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::StoreRRG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_store_rr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::StoreRIG => {
                let op = r_instr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), stack, fp, st, code, r);
                let ghost l0 = stack@.len();
                match r_store_ri(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d),
                    Ghost(rpc), op, stack, fp, st, r, false, &mut acc) {
                    Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } },
                    Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) }
                }
            },
            OpCode::Op => {
                if fl == 0 { proof { lemma_out_of_fuel(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st); } return (Err(Trap::Exhausted), Ghost(g.hs), Ghost(g.n), 0); } fl = fl - 1;
                // Runs the instruction at `r.pc` as a stack instruction.
                proof {
                    lemma_rfacts(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                    reveal(rinv);
                    lemma_loop_pc(m, cs, codes@, c0, g.hs, g.n, g.c, stack@, calls@, d, g.pc, fp, g.sp, st);
                }
                let pc = r.pc as usize;
                let sp = fp + r.a as usize;
                let i = vget(&code.ops, pc);
                proof {
                    if pc + 1 < code.ops@.len() {
                        assert(code.ops@.len() == m.funcs@[d as int].body@.len() + 1);
                        lemma_next_op(m, d as nat, cs[d as int], code, rpc as int);
                    }
                }
                match i {
                    Instr::Unreachable | Instr::Call(_) | Instr::CallIndirect { .. } | Instr::MemoryGrow => {
                        match special_step(m, Ghost(cs), codes, stack, calls, host, st, d, pc, fp, sp, i,
                            Ghost(c0), Ghost(g.hs), Ghost(g.n), Ghost(g.c)) {
                            Flow::Go { d: d2, pc: pc2, fp: fp2, sp: sp2, c: c2, hs: hs2, n: n2 } => {
                                d = d2;
                                fp = fp2;
                                code = &codes[d];
                                rops = code.rops.as_slice();
                                rpc = vget(&code.entry, pc2) as usize;
                                proof {
                                    g = GS { c: c2@, hs: hs2@, n: n2@, pc: pc2, sp: sp2 };
                                    reveal(rinv);
                                    lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                                }
                                cur = cur_at(rops, rpc);
                                acc = r_acc_fix(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                                    Ghost(d), Ghost(rpc), stack, fp, st, cur_get(cur), acc);
                            },
                            Flow::Stop(r, hs2, n2) => return (r, hs2, n2, fl),
                        }
                    },
                    _ => {
                        match local_step(m, Ghost(cs), Ghost(codes@), code, stack, Ghost(calls@), d, pc, fp, sp, st, i,
                            Ghost(c0), Ghost(g.hs), Ghost(g.n), Ghost(g.c)) {
                            Ok((sp2, pc2, c2)) => {
                                rpc = vget(&code.entry, pc2) as usize;
                                proof {
                                    g = GS { c: c2@, hs: g.hs, n: g.n + 1, pc: pc2, sp: sp2 };
                                    reveal(rinv);
                                    lemma_rpc(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st);
                                }
                                cur = cur_at(rops, rpc);
                                acc = r_acc_fix(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g),
                                    Ghost(d), Ghost(rpc), stack, fp, st, cur_get(cur), acc);
                            },
                            Err(t) => return (Err(t), Ghost(g.hs), Ghost(g.n + 1), fl),
                        }
                    },
                }
            },
            // BEGIN GENERATED METERED ARMS
            OpCode::Un_I32Eqz => { let ghost l0 = stack@.len(); match s_Un_I32Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Un_I32Eqz => { let ghost l0 = stack@.len(); match s_P_Un_I32Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I64Eqz => { let ghost l0 = stack@.len(); match s_Un_I64Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Un_I64Eqz => { let ghost l0 = stack@.len(); match s_P_Un_I64Eqz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I32Clz => { let ghost l0 = stack@.len(); match s_Un_I32Clz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I32Ctz => { let ghost l0 = stack@.len(); match s_Un_I32Ctz(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I32WrapI64 => { let ghost l0 = stack@.len(); match s_Un_I32WrapI64(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Un_I32WrapI64 => { let ghost l0 = stack@.len(); match s_P_Un_I32WrapI64(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I64ExtendI32S => { let ghost l0 = stack@.len(); match s_Un_I64ExtendI32S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Un_I64ExtendI32S => { let ghost l0 = stack@.len(); match s_P_Un_I64ExtendI32S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I64ExtendI32U => { let ghost l0 = stack@.len(); match s_Un_I64ExtendI32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Un_I64ExtendI32U => { let ghost l0 = stack@.len(); match s_P_Un_I64ExtendI32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I32Extend8S => { let ghost l0 = stack@.len(); match s_Un_I32Extend8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_I32Extend16S => { let ghost l0 = stack@.len(); match s_Un_I32Extend16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_F64Neg => { let ghost l0 = stack@.len(); match s_Un_F64Neg(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_F64Abs => { let ghost l0 = stack@.len(); match s_Un_F64Abs(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Un_F64Sqrt => { let ghost l0 = stack@.len(); match s_Un_F64Sqrt(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Eq => { let ghost l0 = stack@.len(); match s_BinRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Eq => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Eq => { let ghost l0 = stack@.len(); match s_BinRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Eq => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Ne => { let ghost l0 = stack@.len(); match s_BinRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Ne => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Ne => { let ghost l0 = stack@.len(); match s_BinRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Ne => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32LtS => { let ghost l0 = stack@.len(); match s_BinRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32LtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32LtS => { let ghost l0 = stack@.len(); match s_BinRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32LtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32LtU => { let ghost l0 = stack@.len(); match s_BinRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32LtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32LtU => { let ghost l0 = stack@.len(); match s_BinRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32LtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32GtS => { let ghost l0 = stack@.len(); match s_BinRR_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32GtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32GtS => { let ghost l0 = stack@.len(); match s_BinRI_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32GtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32GtU => { let ghost l0 = stack@.len(); match s_BinRR_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32GtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32GtU => { let ghost l0 = stack@.len(); match s_BinRI_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32GtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32LeS => { let ghost l0 = stack@.len(); match s_BinRR_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32LeS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32LeS => { let ghost l0 = stack@.len(); match s_BinRI_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32LeS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32LeU => { let ghost l0 = stack@.len(); match s_BinRR_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32LeU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32LeU => { let ghost l0 = stack@.len(); match s_BinRI_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32LeU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32GeS => { let ghost l0 = stack@.len(); match s_BinRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32GeS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32GeS => { let ghost l0 = stack@.len(); match s_BinRI_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32GeS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32GeU => { let ghost l0 = stack@.len(); match s_BinRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32GeU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32GeU => { let ghost l0 = stack@.len(); match s_BinRI_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32GeU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Eq => { let ghost l0 = stack@.len(); match s_BinRR_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Eq => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Eq => { let ghost l0 = stack@.len(); match s_BinRI_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Eq => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Eq(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Ne => { let ghost l0 = stack@.len(); match s_BinRR_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Ne => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Ne => { let ghost l0 = stack@.len(); match s_BinRI_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Ne => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Ne(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64LtS => { let ghost l0 = stack@.len(); match s_BinRR_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64LtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64LtS => { let ghost l0 = stack@.len(); match s_BinRI_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64LtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64LtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64LtU => { let ghost l0 = stack@.len(); match s_BinRR_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64LtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64LtU => { let ghost l0 = stack@.len(); match s_BinRI_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64LtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64LtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64GtS => { let ghost l0 = stack@.len(); match s_BinRR_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64GtS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64GtS => { let ghost l0 = stack@.len(); match s_BinRI_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64GtS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64GtS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64GtU => { let ghost l0 = stack@.len(); match s_BinRR_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64GtU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64GtU => { let ghost l0 = stack@.len(); match s_BinRI_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64GtU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64GtU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64LeS => { let ghost l0 = stack@.len(); match s_BinRR_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64LeS => { let ghost l0 = stack@.len(); match s_BinRI_I64LeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64LeU => { let ghost l0 = stack@.len(); match s_BinRR_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64LeU => { let ghost l0 = stack@.len(); match s_BinRI_I64LeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64GeS => { let ghost l0 = stack@.len(); match s_BinRR_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64GeS => { let ghost l0 = stack@.len(); match s_BinRI_I64GeS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64GeU => { let ghost l0 = stack@.len(); match s_BinRR_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64GeU => { let ghost l0 = stack@.len(); match s_BinRI_I64GeU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Add => { let ghost l0 = stack@.len(); match s_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Add => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32Add => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Add => { let ghost l0 = stack@.len(); match s_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Add => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Add => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32Sub => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Sub => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32Mul => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Mul => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32And => { let ghost l0 = stack@.len(); match s_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32And => { let ghost l0 = stack@.len(); match s_P_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32And => { let ghost l0 = stack@.len(); match s_A_BinRR_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32And => { let ghost l0 = stack@.len(); match s_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32And => { let ghost l0 = stack@.len(); match s_P_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32And => { let ghost l0 = stack@.len(); match s_A_BinRI_I32And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Or => { let ghost l0 = stack@.len(); match s_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Or => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32Or => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Or => { let ghost l0 = stack@.len(); match s_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Or => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Or => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRR_I32Xor => { let ghost l0 = stack@.len(); match s_A_BinRR_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Xor => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Shl => { let ghost l0 = stack@.len(); match s_BinRR_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Shl => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Shl => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32ShrS => { let ghost l0 = stack@.len(); match s_BinRR_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32ShrS => { let ghost l0 = stack@.len(); match s_P_BinRR_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_P_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32ShrS => { let ghost l0 = stack@.len(); match s_A_BinRI_I32ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32ShrU => { let ghost l0 = stack@.len(); match s_BinRR_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32ShrU => { let ghost l0 = stack@.len(); match s_P_BinRR_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_P_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32ShrU => { let ghost l0 = stack@.len(); match s_A_BinRI_I32ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Rotl => { let ghost l0 = stack@.len(); match s_BinRR_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Rotl => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Rotl => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I32Rotr => { let ghost l0 = stack@.len(); match s_BinRR_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I32Rotr => { let ghost l0 = stack@.len(); match s_P_BinRR_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_P_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I32Rotr => { let ghost l0 = stack@.len(); match s_A_BinRI_I32Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Add => { let ghost l0 = stack@.len(); match s_BinRR_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Add => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Add => { let ghost l0 = stack@.len(); match s_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Add => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_BinRI_I64Add => { let ghost l0 = stack@.len(); match s_A_BinRI_I64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Sub => { let ghost l0 = stack@.len(); match s_BinRR_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Sub => { let ghost l0 = stack@.len(); match s_BinRI_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Mul => { let ghost l0 = stack@.len(); match s_BinRR_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Mul => { let ghost l0 = stack@.len(); match s_BinRI_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64And => { let ghost l0 = stack@.len(); match s_BinRR_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64And => { let ghost l0 = stack@.len(); match s_P_BinRR_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64And => { let ghost l0 = stack@.len(); match s_BinRI_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64And => { let ghost l0 = stack@.len(); match s_P_BinRI_I64And(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Or => { let ghost l0 = stack@.len(); match s_BinRR_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Or => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Or => { let ghost l0 = stack@.len(); match s_BinRI_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Or => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Or(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Xor => { let ghost l0 = stack@.len(); match s_BinRR_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Xor => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Xor => { let ghost l0 = stack@.len(); match s_BinRI_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Xor => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Xor(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Shl => { let ghost l0 = stack@.len(); match s_BinRR_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64Shl => { let ghost l0 = stack@.len(); match s_P_BinRR_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Shl => { let ghost l0 = stack@.len(); match s_BinRI_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64Shl => { let ghost l0 = stack@.len(); match s_P_BinRI_I64Shl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64ShrS => { let ghost l0 = stack@.len(); match s_BinRR_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64ShrS => { let ghost l0 = stack@.len(); match s_P_BinRR_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64ShrS => { let ghost l0 = stack@.len(); match s_BinRI_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64ShrS => { let ghost l0 = stack@.len(); match s_P_BinRI_I64ShrS(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64ShrU => { let ghost l0 = stack@.len(); match s_BinRR_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_I64ShrU => { let ghost l0 = stack@.len(); match s_P_BinRR_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64ShrU => { let ghost l0 = stack@.len(); match s_BinRI_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_I64ShrU => { let ghost l0 = stack@.len(); match s_P_BinRI_I64ShrU(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Rotl => { let ghost l0 = stack@.len(); match s_BinRR_I64Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Rotl => { let ghost l0 = stack@.len(); match s_BinRI_I64Rotl(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_I64Rotr => { let ghost l0 = stack@.len(); match s_BinRR_I64Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_I64Rotr => { let ghost l0 = stack@.len(); match s_BinRI_I64Rotr(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F32Add => { let ghost l0 = stack@.len(); match s_BinRR_F32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F32Add => { let ghost l0 = stack@.len(); match s_BinRI_F32Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F32Sub => { let ghost l0 = stack@.len(); match s_BinRR_F32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F32Sub => { let ghost l0 = stack@.len(); match s_BinRI_F32Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F32Mul => { let ghost l0 = stack@.len(); match s_BinRR_F32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F32Mul => { let ghost l0 = stack@.len(); match s_BinRI_F32Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F32Div => { let ghost l0 = stack@.len(); match s_BinRR_F32Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F32Div => { let ghost l0 = stack@.len(); match s_BinRI_F32Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F64Add => { let ghost l0 = stack@.len(); match s_BinRR_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_F64Add => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F64Add => { let ghost l0 = stack@.len(); match s_BinRI_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_F64Add => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Add(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F64Sub => { let ghost l0 = stack@.len(); match s_BinRR_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_F64Sub => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F64Sub => { let ghost l0 = stack@.len(); match s_BinRI_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_F64Sub => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Sub(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F64Mul => { let ghost l0 = stack@.len(); match s_BinRR_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_F64Mul => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F64Mul => { let ghost l0 = stack@.len(); match s_BinRI_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_F64Mul => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Mul(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRR_F64Div => { let ghost l0 = stack@.len(); match s_BinRR_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRR_F64Div => { let ghost l0 = stack@.len(); match s_P_BinRR_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BinRI_F64Div => { let ghost l0 = stack@.len(); match s_BinRI_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_BinRI_F64Div => { let ghost l0 = stack@.len(); match s_P_BinRI_F64Div(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I32Load => { let ghost l0 = stack@.len(); match s_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I32Load => { let ghost l0 = stack@.len(); match s_P_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_Load_I32Load => { let ghost l0 = stack@.len(); match s_A_Load_I32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I64Load => { let ghost l0 = stack@.len(); match s_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I64Load => { let ghost l0 = stack@.len(); match s_P_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_Load_I64Load => { let ghost l0 = stack@.len(); match s_A_Load_I64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_F32Load => { let ghost l0 = stack@.len(); match s_Load_F32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_F32Load => { let ghost l0 = stack@.len(); match s_P_Load_F32Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_F64Load => { let ghost l0 = stack@.len(); match s_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_F64Load => { let ghost l0 = stack@.len(); match s_P_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_Load_F64Load => { let ghost l0 = stack@.len(); match s_A_Load_F64Load(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I32Load8S => { let ghost l0 = stack@.len(); match s_Load_I32Load8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I32Load8S => { let ghost l0 = stack@.len(); match s_P_Load_I32Load8S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I32Load8U => { let ghost l0 = stack@.len(); match s_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I32Load8U => { let ghost l0 = stack@.len(); match s_P_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_Load_I32Load8U => { let ghost l0 = stack@.len(); match s_A_Load_I32Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I32Load16S => { let ghost l0 = stack@.len(); match s_Load_I32Load16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I32Load16S => { let ghost l0 = stack@.len(); match s_P_Load_I32Load16S(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I32Load16U => { let ghost l0 = stack@.len(); match s_Load_I32Load16U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I32Load16U => { let ghost l0 = stack@.len(); match s_P_Load_I32Load16U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I64Load8U => { let ghost l0 = stack@.len(); match s_Load_I64Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I64Load8U => { let ghost l0 = stack@.len(); match s_P_Load_I64Load8U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::Load_I64Load32U => { let ghost l0 = stack@.len(); match s_Load_I64Load32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_Load_I64Load32U => { let ghost l0 = stack@.len(); match s_P_Load_I64Load32U(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_StoreRR_I32Store => { let ghost l0 = stack@.len(); match s_A_StoreRR_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_StoreRI_I32Store => { let ghost l0 = stack@.len(); match s_A_StoreRI_I32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I64Store => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I64Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I64Store => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I64Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_F32Store => { let ghost l0 = stack@.len(); match s_StoreRR_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_F32Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_F32Store => { let ghost l0 = stack@.len(); match s_StoreRI_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_F32Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_F32Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_P_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_StoreRR_F64Store => { let ghost l0 = stack@.len(); match s_A_StoreRR_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_F64Store => { let ghost l0 = stack@.len(); match s_StoreRI_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_F64Store => { let ghost l0 = stack@.len(); match s_P_StoreRI_F64Store(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I32Store8 => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I32Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::A_StoreRI_I32Store8 => { let ghost l0 = stack@.len(); match s_A_StoreRI_I32Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I32Store16 => { let ghost l0 = stack@.len(); match s_StoreRR_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I32Store16 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I32Store16 => { let ghost l0 = stack@.len(); match s_StoreRI_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I32Store16 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I32Store16(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I64Store8 => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I64Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I64Store8 => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I64Store8 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store8(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRR_I64Store32 => { let ghost l0 = stack@.len(); match s_StoreRR_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRR_I64Store32 => { let ghost l0 = stack@.len(); match s_P_StoreRR_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::StoreRI_I64Store32 => { let ghost l0 = stack@.len(); match s_StoreRI_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::P_StoreRI_I64Store32 => { let ghost l0 = stack@.len(); match s_P_StoreRI_I64Store32(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), Ghost(rpc), stack, fp, st, r, &mut acc) { Ok(g2) => { proof { lemma_rpost_ok(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, g2, acc); } rpc = rpc + 1; cur = cur_next(cur); proof { g = g2@; } }, Err((t, n2)) => { proof { lemma_rpost_err(m, cs, codes@, c0, g, stack@, l0, calls@, d, rpc, fp, st, t, n2, acc); } return (Err(t), Ghost(g.hs), n2, fl) } } },
            OpCode::BrIf | OpCode::A_BrIf | OpCode::BrIfZ | OpCode::A_BrIfZ | OpCode::Br | OpCode::BrIfRRG | OpCode::BrIfRIG | OpCode::BrIfRR_I32Eq | OpCode::BrIfRI_I32Eq | OpCode::A_BrIfRR_I32Eq | OpCode::A_BrIfRI_I32Eq | OpCode::BrIfRR_I32Ne | OpCode::BrIfRI_I32Ne | OpCode::A_BrIfRR_I32Ne | OpCode::A_BrIfRI_I32Ne | OpCode::BrIfRR_I32LtS | OpCode::BrIfRI_I32LtS | OpCode::A_BrIfRR_I32LtS | OpCode::A_BrIfRI_I32LtS | OpCode::BrIfRR_I32LtU | OpCode::BrIfRI_I32LtU | OpCode::A_BrIfRR_I32LtU | OpCode::A_BrIfRI_I32LtU | OpCode::BrIfRR_I32GtS | OpCode::BrIfRI_I32GtS | OpCode::BrIfRR_I32GtU | OpCode::BrIfRI_I32GtU | OpCode::BrIfRR_I32LeS | OpCode::BrIfRI_I32LeS | OpCode::BrIfRR_I32LeU | OpCode::BrIfRI_I32LeU | OpCode::BrIfRR_I32GeS | OpCode::BrIfRI_I32GeS | OpCode::A_BrIfRR_I32GeS | OpCode::BrIfRR_I32GeU | OpCode::BrIfRI_I32GeU | OpCode::A_BrIfRR_I32GeU | OpCode::BrIfRR_I64Eq | OpCode::BrIfRI_I64Eq | OpCode::BrIfRR_I64Ne | OpCode::BrIfRI_I64Ne | OpCode::BrIfRR_I64LtS | OpCode::BrIfRI_I64LtS | OpCode::BrIfRR_I64LtU | OpCode::BrIfRI_I64LtU | OpCode::BrIfRR_I64GtS | OpCode::BrIfRI_I64GtS | OpCode::BrIfRR_I64GtU | OpCode::BrIfRI_I64GtU | OpCode::BrIfRR_I64LeS | OpCode::BrIfRI_I64LeS | OpCode::BrIfRR_I64LeU | OpCode::BrIfRI_I64LeU | OpCode::BrIfRR_I64GeS | OpCode::BrIfRI_I64GeS | OpCode::BrIfRR_I64GeU | OpCode::BrIfRI_I64GeU => { if fl == 0 { proof { lemma_out_of_fuel(m, cs, codes@, c0, g, stack@, calls@, d, rpc, fp, st); } return (Err(Trap::Exhausted), Ghost(g.hs), Ghost(g.n), 0); } fl = fl - 1; let (rpc2, cur2, g2) = s_branch(Ghost(m), Ghost(cs), Ghost(codes@), Ghost(calls@), Ghost(c0), Ghost(g), Ghost(d), rpc, stack, fp, st, code, r, rops, cur, acc); rpc = rpc2; cur = cur2; proof { g = g2@; } },
            // END GENERATED METERED ARMS
        }
    }
}

} // verus!
