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
    /// on `args`. A wrong number of arguments traps with `Unreachable`.
    pub fn invoke<H: Host>(self, func: u32, args: &[u64], host: &mut H) -> (r: (Checked, Result<Vec<u64>, Trap>)) {
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
        let (r, _, _) = execute(&m, &codes, Ghost(cs@), &mut st, &mut stack, &mut calls, host, d, Ghost(c0));
        (Checked { m, cs, codes, st, stack, calls }, r)
    }
}

} // verus!
