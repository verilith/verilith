//! The interpreter, proven to refine [`crate::sem`].
//!
//! All frames share one value stack: a frame's locals start at its frame
//! pointer `fp` and its operand stack follows them. Branch targets, label
//! heights and frame sizes come from the checked certificate, so there is
//! no label stack at run time and no stack check on push or pop; a call
//! checks once that the callee's whole frame fits.
//!
//! [`execute`] ends with ghost evidence `(hs, n)`: the spec, run for `n`
//! steps from the initial configuration with host responses `hs`, gives
//! exactly the returned result and store (or is still running, if the
//! interpreter stopped with [`Trap::Exhausted`]).
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::num::*;
use crate::cert::*;
use crate::preserve::*;
use crate::prims::*;

verus! {

/// Most nested calls; deeper ones trap with [`Trap::Exhausted`].
pub const MAX_CALLS: usize = 100_000;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BrTarget {
    pub pc: u32,
    pub arity: u32,
    pub height: u32,
}

/// A defined function prepared for the interpreter.
pub struct Code {
    /// The body followed by `Unreachable`, which at `pc == body.len()`
    /// stands for "return".
    pub ops: Vec<Instr>,
    /// The resolved target of the branch at each position, or for
    /// `br_table` the start of its targets in `table`.
    pub side: Vec<BrTarget>,
    pub table: Vec<BrTarget>,
    pub n_params: u32,
    /// Locals, parameters included.
    pub n_locals: u32,
    pub n_results: u32,
    /// Locals plus the certified maximum operand-stack height.
    pub frame: u32,
    /// The register form (see [`crate::reg`]): one operation per position.
    pub rops: Vec<crate::reg::ROp>,
    /// For each position, the index in `rops` of the operation that
    /// starts there, or `NONE`.
    pub entry: Vec<u32>,
}

#[derive(Clone, Copy)]
pub struct CallFrame {
    pub func: u32,
    pub pc: u32,
    pub fp: u32,
}

/// The mutable state of an instance.
pub struct Store {
    pub mem: Vec<u8>,
    /// Page limit for `memory.grow` (at most 65536).
    pub mem_max: u32,
    pub globals: Vec<u64>,
    /// Function indices, `NONE` for null.
    pub tables: Vec<Vec<u32>>,
    pub dropped: Vec<bool>,
}

/// Embedder-supplied imported functions.
pub trait Host {
    /// Runs imported function `func` (an index among the module's
    /// functions) on `args`, writing `results`. It may read and write the
    /// guest's linear memory. `false` (or a panic) traps.
    fn call(&mut self, func: u32, args: &[u64], results: &mut [u64], mem: &mut [u8]) -> bool;
}

#[verifier::external_body]
pub fn call_host<H: Host>(h: &mut H, func: u32, args: &[u64], results: &mut Vec<u64>, mem: &mut Vec<u8>) -> (r: bool)
    ensures
        final(results)@.len() == old(results)@.len(),
        final(mem)@.len() == old(mem)@.len(),
{
    // A panicking host traps; it can only have changed the contents of
    // `results` and `mem`, not their lengths.
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        h.call(func, args, results.as_mut_slice(), mem.as_mut_slice())
    }));
    matches!(r, Ok(true))
}

// ---------------------------------------------------------------------------
// Views and the relation to the spec
// ---------------------------------------------------------------------------

pub open spec fn view_tab(t: Seq<u32>) -> Seq<Option<nat>> {
    t.map_values(|x: u32| if x == NONE { None } else { Some(x as nat) })
}

pub open spec fn store_view(st: &Store) -> crate::sem::Store {
    crate::sem::Store {
        mem: st.mem@,
        mem_max: st.mem_max as nat,
        tables: st.tables@.map_values(|t: Vec<u32>| view_tab(t@)),
        globals: st.globals@,
        data_dropped: st.dropped@,
    }
}

pub open spec fn store_wf(st: &Store) -> bool {
    &&& st.mem_max <= 65536
    &&& st.mem@.len() <= st.mem_max as nat * PAGE as nat
    &&& st.mem@.len() % PAGE as nat == 0
}

pub open spec fn target_of(fc: FuncCert, pc: int, k: nat) -> BrTarget {
    let r = fc.labels@[nth_id(fc.labels@, lab(fc, pc), k)->Some_0 as int];
    BrTarget { pc: r.cont, arity: r.arity, height: r.height }
}

pub open spec fn side_ok(m: &Module, fc: FuncCert, side: Seq<BrTarget>, table: Seq<BrTarget>, pc: int,
    i: Instr) -> bool
{
    match i {
        Instr::Br(k) => side[pc] == target_of(fc, pc, k as nat),
        Instr::BrIf(k) => side[pc] == target_of(fc, pc, k as nat),
        Instr::Else { .. } => side[pc] == target_of(fc, pc, 0),
        Instr::Return => side[pc] == target_of(fc, pc, (chain(fc.labels@, lab(fc, pc)).len() - 1) as nat),
        Instr::BrTable { start, len } => side[pc].pc as nat + len as nat <= table.len()
            && forall|j: int| 0 <= j < len ==> #[trigger] table[side[pc].pc + j]
                == target_of(fc, pc, m.br_table@[start + j] as nat),
        _ => true,
    }
}

pub open spec fn code_ok(m: &Module, cs: Seq<FuncCert>, d: nat, code: &Code) -> bool {
    let body = m.funcs@[d as int].body@;
    let len = body.len();
    let fc = cs[d as int];
    &&& code.ops@.len() == len + 1
    &&& forall|pc: int| 0 <= pc < len ==> code.ops@[pc] == #[trigger] body[pc]
    &&& code.ops@[len as int] == Instr::Unreachable
    &&& code.side@.len() == len + 1
    &&& code.n_params as nat == n_params(func_type(m, d + n_imp(m)))
    &&& code.n_locals as nat == n_locals(m, d)
    &&& code.n_results as nat == n_results(func_type(m, d + n_imp(m)))
    &&& code.frame as nat == code.n_locals as nat + fc.max_height as nat
    &&& forall|pc: int| 0 <= pc < len && live(fc, pc) ==> #[trigger] side_ok(m, fc, code.side@, code.table@, pc, body[pc])
    &&& crate::rcheck::rcode_ok(m, d, fc, code)
}

pub open spec fn codes_ok(m: &Module, cs: Seq<FuncCert>, codes: Seq<Code>) -> bool {
    &&& codes.len() == m.funcs@.len()
    &&& forall|d: nat| d < codes.len() ==> #[trigger] code_ok(m, cs, d, &codes[d as int])
}

pub open spec fn next_fp(calls: Seq<CallFrame>, k: int, fp: int) -> int {
    if k + 1 < calls.len() { calls[k + 1].fp as int } else { fp }
}

pub open spec fn lower_frame_ok(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int, k: int) -> bool {
    let cf = calls[k];
    let f = fr[k];
    let nl = n_locals(m, cf.func as nat);
    let e = next_fp(calls, k, fp);
    &&& f.func == cf.func as nat
    &&& f.pc == cf.pc as nat
    &&& cf.fp + nl <= e
    &&& e <= fp
    &&& f.locals == s.subrange(cf.fp as int, cf.fp + nl)
    &&& f.stack == s.subrange(cf.fp + nl, e)
}

pub open spec fn lower_ok(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int) -> bool {
    &&& calls.len() == fr.len()
    &&& forall|k: int| 0 <= k < calls.len() ==> #[trigger] lower_frame_ok(m, s, calls, fr, fp, k)
}

pub open spec fn top_ok(m: &Module, s: Seq<u64>, f: Frame, fp: int, sp: int) -> bool {
    let nl = n_locals(m, f.func);
    &&& 0 <= fp && fp + nl <= sp <= s.len()
    &&& f.locals == s.subrange(fp, fp + nl)
    &&& f.stack == s.subrange(fp + nl, sp)
}

/// The machine `(stack, calls, fp, sp)` is configuration `c`'s frames.
pub open spec fn mach_ok(m: &Module, s: Seq<u64>, calls: Seq<CallFrame>, fp: int, sp: int, c: Config) -> bool {
    &&& c.frames.len() == calls.len() + 1
    &&& lower_ok(m, s, calls, c.frames.subrange(0, c.frames.len() - 1), fp)
    &&& top_ok(m, s, c.frames.last(), fp, sp)
}

// ---------------------------------------------------------------------------
// Relation lemmas
// ---------------------------------------------------------------------------

/// Lower frames only depend on the stack below the top frame.
pub proof fn lemma_lower_same(m: &Module, s1: Seq<u64>, s2: Seq<u64>, calls: Seq<CallFrame>, fr: Seq<Frame>, fp: int)
    requires
        lower_ok(m, s1, calls, fr, fp),
        0 <= fp <= s1.len(), fp <= s2.len(),
        s1.subrange(0, fp) == s2.subrange(0, fp),
    ensures lower_ok(m, s2, calls, fr, fp),
{
    assert forall|k: int| 0 <= k < calls.len() implies #[trigger] lower_frame_ok(m, s2, calls, fr, fp, k) by {
        assert(lower_frame_ok(m, s1, calls, fr, fp, k));
        let cf = calls[k];
        let nl = n_locals(m, cf.func as nat);
        let e = next_fp(calls, k, fp);
        assert(s1.subrange(cf.fp as int, cf.fp + nl) =~= s1.subrange(0, fp).subrange(cf.fp as int, cf.fp + nl));
        assert(s2.subrange(cf.fp as int, cf.fp + nl) =~= s2.subrange(0, fp).subrange(cf.fp as int, cf.fp + nl));
        assert(s1.subrange(cf.fp + nl, e) =~= s1.subrange(0, fp).subrange(cf.fp + nl, e));
        assert(s2.subrange(cf.fp + nl, e) =~= s2.subrange(0, fp).subrange(cf.fp + nl, e));
    }
}

/// The top frame moves to `g` (same function and frame pointer) with the
/// stack changed only at or above the operand base.
pub proof fn lemma_mach_top(m: &Module, s1: Seq<u64>, s2: Seq<u64>, calls: Seq<CallFrame>, fp: int, sp: int, c: Config,
    g: Frame, sp2: int)
    requires
        mach_ok(m, s1, calls, fp, sp, c),
        g.func == top(c).func,
        s1.len() == s2.len(),
        0 <= fp, fp + n_locals(m, g.func) <= sp2 <= s2.len(),
        s2.subrange(0, fp) == s1.subrange(0, fp),
        g.locals == s2.subrange(fp, fp + n_locals(m, g.func)),
        g.stack == s2.subrange(fp + n_locals(m, g.func), sp2),
    ensures
        mach_ok(m, s2, calls, fp, sp2, with_top(c, g)),
{
    let c2 = with_top(c, g);
    assert(c2.frames.subrange(0, c2.frames.len() - 1) =~= c.frames.subrange(0, c.frames.len() - 1));
    lemma_lower_same(m, s1, s2, calls, c.frames.subrange(0, c.frames.len() - 1), fp);
}

// ---------------------------------------------------------------------------
// Steps of the spec, one instruction group at a time
// ---------------------------------------------------------------------------

pub open spec fn cur(m: &Module, c: Config) -> Instr {
    m.funcs@[top(c).func as int].body@[top(c).pc as int]
}

pub open spec fn at_instr(m: &Module, c: Config) -> bool {
    &&& c.frames.len() >= 1
    &&& top(c).func < m.funcs@.len()
    &&& top(c).pc < m.funcs@[top(c).func as int].body@.len()
}

pub proof fn lemma_step_instr(m: &Module, c: Config)
    requires at_instr(m, c),
    ensures step(m, c) == step_instr(m, c, top(c), cur(m, c)),
{
}

} // verus!
