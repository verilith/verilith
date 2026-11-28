//! A checked, ready-to-run module instance: the boundary between verified
//! and unverified code.
//!
//! A [`Checked`] instance can only be built by [`Checked::new`], which checks the
//! certificates and the initial store, and its fields are private, so its
//! type invariant (checked certificates, compiled code, a well-formed
//! store) holds for every instance whatever unverified code does with it.
//! [`Checked::invoke`] is therefore safe to call from anywhere, and every
//! call runs the proven interpreter.
use vstd::prelude::*;
use crate::ast::*;
use crate::sem::*;
use crate::cert::*;
use crate::preserve::*;
use crate::check::*;
use crate::interp::*;
use crate::run::*;
use crate::compile::*;
use crate::prims::*;
use crate::interp::Store;

verus! {

/// Value-stack slots per instance (8 MiB).
pub const STACK_SLOTS: usize = 0x10_0000;

pub struct Checked {
    m: Module,
    cs: Ghost<Seq<FuncCert>>,
    codes: Vec<Code>,
    st: Store,
    stack: Vec<u64>,
    calls: Vec<CallFrame>,
}

/// Checks that `st` is a well-formed store for `m`.
pub fn check_store(m: &Module, st: &Store) -> (r: bool)
    ensures r ==> store_ok(m, store_view(st)) && store_wf(st),
{
    if st.globals.len() != m.global_types.len() || st.tables.len() != m.tables.len()
        || st.dropped.len() != m.datas.len() || st.mem_max > crate::interp::MAX_PAGES
        || st.mem.len() as u64 > st.mem_max as u64 * PAGE || st.mem.len() % PAGE as usize != 0 {
        return false;
    }
    let nf = m.func_types.len();
    let mut t = 0;
    while t < st.tables.len()
        invariant
            nf == m.func_types@.len(),
            0 <= t <= st.tables@.len(),
            forall|t2: int, k: int| 0 <= t2 < t && 0 <= k < st.tables@[t2]@.len()
                ==> (#[trigger] st.tables@[t2]@[k]) == NONE || st.tables@[t2]@[k] < nf,
        decreases st.tables@.len() - t,
    {
        let tab = &st.tables[t];
        let mut k = 0;
        while k < tab.len()
            invariant
                nf == m.func_types@.len(),
                0 <= t < st.tables@.len(),
                *tab == st.tables@[t as int],
                0 <= k <= tab@.len(),
                forall|t2: int, k2: int| 0 <= t2 < t && 0 <= k2 < st.tables@[t2]@.len()
                    ==> (#[trigger] st.tables@[t2]@[k2]) == NONE || st.tables@[t2]@[k2] < nf,
                forall|k2: int| 0 <= k2 < k ==> (#[trigger] tab@[k2]) == NONE || tab@[k2] < nf,
            decreases tab@.len() - k,
        {
            let x = tab[k];
            if x != NONE && x as usize >= nf {
                return false;
            }
            k = k + 1;
        }
        t = t + 1;
    }
    proof {
        let s = store_view(st);
        assert forall|t2: int, k2: int| 0 <= t2 < s.tables.len() && 0 <= k2 < s.tables[t2].len()
            && (#[trigger] s.tables[t2][k2]) is Some implies s.tables[t2][k2]->Some_0 < m.func_types@.len() by {
            assert(s.tables[t2] == view_tab(st.tables@[t2]@));
            assert(st.tables@[t2]@[k2] == NONE || st.tables@[t2]@[k2] < m.func_types@.len());
        }
    }
    true
}

/// A copy of an instance's store, to start later calls from
/// ([`Checked::snapshot`], [`Checked::restore`]).
pub struct Snapshot {
    st: Store,
}

impl Snapshot {
    /// The store the snapshot holds.
    pub closed spec fn view(&self) -> crate::sem::Store {
        store_view(&self.st)
    }

    /// The page limit for `memory.grow` that the snapshot holds.
    pub fn mem_max(&self) -> (r: u32)
        ensures r as nat == self.view().mem_max,
    {
        self.st.mem_max
    }
}

fn copy_bytes(src: &Vec<u8>) -> (r: Vec<u8>)
    ensures r@ == src@,
{
    let n = src.len();
    let mut v = vec![0u8; n];
    copy_in(&mut v, 0, src.as_slice(), 0, n);
    proof { assert(v@ =~= src@); }
    v
}

fn copy_u32s(src: &Vec<u32>) -> (r: Vec<u32>)
    ensures r@ == src@,
{
    let mut v: Vec<u32> = Vec::with_capacity(src.len());
    let mut i = 0;
    while i < src.len()
        invariant
            0 <= i <= src@.len(),
            v@ == src@.subrange(0, i as int),
        decreases src@.len() - i,
    {
        v.push(src[i]);
        i += 1;
        proof { assert(v@ =~= src@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= src@); }
    v
}

fn copy_u64s(src: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == src@,
{
    let mut v: Vec<u64> = Vec::with_capacity(src.len());
    let mut i = 0;
    while i < src.len()
        invariant
            0 <= i <= src@.len(),
            v@ == src@.subrange(0, i as int),
        decreases src@.len() - i,
    {
        v.push(src[i]);
        i += 1;
        proof { assert(v@ =~= src@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= src@); }
    v
}

fn copy_bools(src: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == src@,
{
    let mut v: Vec<bool> = Vec::with_capacity(src.len());
    let mut i = 0;
    while i < src.len()
        invariant
            0 <= i <= src@.len(),
            v@ == src@.subrange(0, i as int),
        decreases src@.len() - i,
    {
        v.push(src[i]);
        i += 1;
        proof { assert(v@ =~= src@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= src@); }
    v
}

fn copy_tables(src: &Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
    ensures
        r@.len() == src@.len(),
        forall|t: int| 0 <= t < src@.len() ==> (#[trigger] r@[t])@ == src@[t]@,
{
    let mut v: Vec<Vec<u32>> = Vec::with_capacity(src.len());
    let mut i = 0;
    while i < src.len()
        invariant
            0 <= i <= src@.len(),
            v@.len() == i,
            forall|t: int| 0 <= t < i ==> (#[trigger] v@[t])@ == src@[t]@,
        decreases src@.len() - i,
    {
        v.push(copy_u32s(&src[i]));
        i += 1;
    }
    v
}

/// A copy of `st`, with the same view.
fn copy_store(st: &Store) -> (r: Store)
    ensures
        store_view(&r) == store_view(st),
        r.mem_max == st.mem_max,
{
    let r = Store {
        mem: copy_bytes(&st.mem),
        mem_max: st.mem_max,
        globals: copy_u64s(&st.globals),
        tables: copy_tables(&st.tables),
        dropped: copy_bools(&st.dropped),
    };
    proof {
        let a = store_view(&r);
        let b = store_view(st);
        assert(a.tables =~= b.tables) by {
            assert forall|t: int| 0 <= t < a.tables.len() implies a.tables[t] == b.tables[t] by {
                assert(r.tables@[t]@ == st.tables@[t]@);
            }
        }
        assert(a =~= b);
    }
    r
}

impl Checked {
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        &&& certs_ok(&self.m, self.cs@)
        &&& codes_ok(&self.m, self.cs@, self.codes@)
        &&& store_ok(&self.m, store_view(&self.st))
        &&& store_wf(&self.st)
        &&& self.stack@.len() == STACK_SLOTS
    }

    /// Checks `certs` against `m` and `store` and prepares the instance.
    /// `None` if a certificate or the store is rejected.
    pub fn new(m: Module, certs: Vec<FuncCert>, store: Store) -> (r: Option<Checked>) {
        if !check_certs(&m, &certs) || !check_store(&m, &store) {
            return None;
        }
        let codes = match compile_all(&m, &certs) {
            Some(c) => c,
            None => return None,
        };
        Some(Checked {
            m,
            cs: Ghost(certs@),
            codes,
            st: store,
            stack: vec![0u64; STACK_SLOTS],
            calls: Vec::new(),
        })
    }

    /// The instance's store, as the semantics sees it.
    pub closed spec fn view(&self) -> crate::sem::Store {
        store_view(&self.st)
    }

    /// The memory never exceeds the page limit for `memory.grow`, which
    /// is at most [`MAX_PAGES`]. (From the type invariant: it holds
    /// after any call.) Does nothing at run time.
    #[inline(always)]
    pub fn mem_bound(&self)
        ensures
            self.view().mem_max <= MAX_PAGES as nat,
            self.view().mem.len() <= self.view().mem_max * PAGE as nat,
    {
        proof { use_type_invariant(self); }
    }

    /// The page limit for `memory.grow`.
    pub fn mem_max(&self) -> (r: u32)
        ensures r as nat == self.view().mem_max,
    {
        self.st.mem_max
    }

    /// A copy of the store as it is now.
    pub fn snapshot(&self) -> (r: Snapshot)
        ensures r.view() == self.view(),
    {
        Snapshot { st: copy_store(&self.st) }
    }

    /// Puts the store back to `snap`: memory (contents and size), globals,
    /// tables and dropped data segments. On `true` the store is exactly
    /// the snapshot's; on `false` (a snapshot that does not fit this
    /// module) it is unchanged. Memory of the same size is copied in
    /// place, without allocating.
    pub fn restore(self, snap: &Snapshot) -> (r: (Checked, bool))
        ensures
            r.1 ==> r.0.view() == snap.view(),
            !r.1 ==> r.0.view() == self.view(),
    {
        proof { use_type_invariant(&self); }
        let Checked { m, cs, codes, st, stack, calls } = self;
        let s = &snap.st;
        if !check_store(&m, s) {
            return (Checked { m, cs, codes, st, stack, calls }, false);
        }
        let mut mem = st.mem;
        if mem.len() == s.mem.len() {
            let n = mem.len();
            copy_in(&mut mem, 0, s.mem.as_slice(), 0, n);
            proof { assert(mem@ =~= s.mem@); }
        } else {
            mem = copy_bytes(&s.mem);
        }
        let mut globals = st.globals;
        if globals.len() == s.globals.len() {
            let mut i = 0;
            while i < globals.len()
                invariant
                    globals@.len() == s.globals@.len(),
                    0 <= i <= globals@.len(),
                    forall|j: int| 0 <= j < i ==> #[trigger] globals@[j] == s.globals@[j],
                decreases globals@.len() - i,
            {
                globals.set(i, s.globals[i]);
                i += 1;
            }
            proof { assert(globals@ =~= s.globals@); }
        } else {
            globals = copy_u64s(&s.globals);
        }
        let st2 = Store {
            mem,
            mem_max: s.mem_max,
            globals,
            tables: copy_tables(&s.tables),
            dropped: copy_bools(&s.dropped),
        };
        proof {
            let a = store_view(&st2);
            let b = store_view(s);
            assert(a.tables =~= b.tables) by {
                assert forall|t: int| 0 <= t < a.tables.len() implies a.tables[t] == b.tables[t] by {
                    assert(st2.tables@[t]@ == s.tables@[t]@);
                }
            }
            assert(a =~= b);
        }
        (Checked { m, cs, codes, st: st2, stack, calls }, true)
    }

    pub fn module(&self) -> &Module {
        &self.m
    }

    pub fn memory(&self) -> &[u8] {
        self.st.mem.as_slice()
    }

    /// Mutable access to the linear memory. Its length cannot change
    /// through the slice, and the invariant does not depend on contents.
    #[verifier::external_body]
    pub fn memory_mut(&mut self) -> &mut [u8] {
        self.st.mem.as_mut_slice()
    }

    pub fn globals(&self) -> &[u64] {
        self.st.globals.as_slice()
    }

    /// Writes `bytes` to linear memory at `offset`; `false` if out of bounds.
    pub fn write_memory(self, offset: usize, bytes: &[u8]) -> (r: (Checked, bool)) {
        proof { use_type_invariant(&self); }
        let Checked { m, cs, codes, mut st, stack, calls } = self;
        if offset > st.mem.len() || bytes.len() > st.mem.len() - offset {
            return (Checked { m, cs, codes, st, stack, calls }, false);
        }
        copy_in(&mut st.mem, offset, bytes, 0, bytes.len());
        (Checked { m, cs, codes, st, stack, calls }, true)
    }

    /// Runs function `func` (an index among all the module's functions)
    /// on `args`. If `metered`, the call has `*fuel` units of fuel (see
    /// [`execute_metered`]) and leaves the fuel that remains in `*fuel`;
    /// otherwise it is unlimited ([`execute`]) and `*fuel` is unchanged. A
    /// wrong number of arguments traps with `Unreachable`.
    pub fn invoke<H: Host>(self, func: u32, args: &[u64], host: &mut H, metered: bool, fuel: &mut u64)
        -> (r: (Checked, Result<Vec<u64>, Trap>))
    {
        proof { use_type_invariant(&self); }
        let Checked { m, cs, codes, mut st, mut stack, mut calls } = self;
        let nf = m.func_types.len();
        let ni = m.n_imported_funcs as usize;
        if func as usize >= nf {
            return (Checked { m, cs, codes, st, stack, calls }, Err(Trap::Unreachable));
        }
        proof {
            assert(m.func_types@[func as int] < m.types@.len());
        }
        let t = &m.types[m.func_types[func as usize] as usize];
        let np = t.params.len();
        if args.len() != np {
            return (Checked { m, cs, codes, st, stack, calls }, Err(Trap::Unreachable));
        }
        if (func as usize) < ni {
            let mut results = vec![0u64; t.results.len()];
            let ok = call_host(host, func, args, &mut results, &mut st.mem);
            let r = if ok { Ok(results) } else { Err(Trap::Host) };
            return (Checked { m, cs, codes, st, stack, calls }, r);
        }
        let d = func as usize - ni;
        let code = &codes[d];
        proof {
            assert(code_ok(&m, cs@, d as nat, &codes@[d as int]));
            assert(n_locals(&m, d as nat) <= MAX_LOCALS as nat);
        }
        if code.frame as usize > STACK_SLOTS {
            return (Checked { m, cs, codes, st, stack, calls }, Err(Trap::Exhausted));
        }
        let nl = code.n_locals as usize;
        let mut i = 0;
        while i < np
            invariant
                np == args@.len(),
                np <= nl,
                nl <= STACK_SLOTS,
                stack@.len() == STACK_SLOTS,
                0 <= i <= np,
                forall|j: int| 0 <= j < i ==> #[trigger] stack@[j] == args@[j],
            decreases np - i,
        {
            sset(&mut stack, i, args[i]);
            i = i + 1;
        }
        szero(&mut stack, np, nl - np);
        calls.clear();
        let ghost f = new_frame(&m, d as nat, args@);
        let ghost c0 = Config { store: store_view(&st), frames: seq![f] };
        proof {
            let fc = cs@[d as int];
            assert(func_cert_ok(&m, d as nat, fc));
            lemma_labels_wf(&m, d as nat, fc);
            assert(at(fc, 0, 0, 0));
            assert(chain(fc.labels@, 0) =~= seq![to_label(fc.labels@[0])]);
            assert(f.locals =~= stack@.subrange(0, nl as int));
            assert(f.stack =~= stack@.subrange(nl as int, nl as int));
            assert(frame_at(&m, cs@, f));
            assert(c0.frames.last() == f);
            assert(inv(&m, cs@, c0));
        }
        let r = if metered {
            let (r, _, _, left) = execute_metered(&m, &codes, Ghost(cs@), &mut st, &mut stack, &mut calls, host, d,
                Ghost(c0), *fuel);
            *fuel = left;
            r
        } else {
            let (r, _, _) = execute(&m, &codes, Ghost(cs@), &mut st, &mut stack, &mut calls, host, d, Ghost(c0));
            r
        };
        (Checked { m, cs, codes, st, stack, calls }, r)
    }
}

} // verus!
