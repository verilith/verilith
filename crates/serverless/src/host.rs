//! One function: a checked instance, the snapshot every request starts
//! from, and the per-request limits ([`Func::serve`]); and the router
//! ([`route`]).
//!
//! The theorems:
//!
//! - **Requests are isolated.** [`Func::serve`] puts the instance's store
//!   (linear memory, its size, globals, tables, dropped segments) back to
//!   the snapshot taken right after instantiation before it calls the
//!   guest, and gives the guest a new, empty [`Reply`]. Its contract
//!   returns the store the call started from, proven equal to the
//!   snapshot: nothing one request leaves in the instance is there for the
//!   next. If the store cannot be put back, the guest is not called.
//! - **Memory is capped.** Every request starts with a `memory.grow` limit
//!   of at most the configured cap (the [`Func`] type invariant), and the
//!   interpreter's refinement theorem (verilith-wasm `run::execute`) has
//!   `memory.grow` fail past that limit.
//! - **Every call is metered**, with the configured fuel, so it ends.
use vstd::prelude::*;
use verilith_wasm::ast::Trap;
use verilith_wasm::instance::{Checked, Snapshot};
use crate::abi::*;

verus! {

/// What a request came to.
pub enum Outcome {
    /// The guest returned; this is its reply.
    Done(Reply),
    /// The guest trapped (or ran out of fuel: `Trap::Exhausted`).
    Trap(Trap),
    /// The store could not be put back to the snapshot; the guest was not run.
    Fault,
}

/// A loaded function.
pub struct Func {
    inst: Checked,
    snap: Snapshot,
    ops: Vec<u8>,
    entry: u32,
    fuel: u64,
    cap: u32,
}

impl Func {
    /// The store every request starts from.
    pub closed spec fn template(&self) -> verilith_wasm::sem::Store {
        self.snap.view()
    }

    /// The memory cap, in pages.
    pub closed spec fn cap(&self) -> nat {
        self.cap as nat
    }

    pub closed spec fn fuel(&self) -> nat {
        self.fuel as nat
    }

    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        &&& self.snap.view().mem_max <= self.cap
        &&& self.inst.mem_base() == self.snap.view().mem
    }

    /// Takes an instance just instantiated (its start function run),
    /// snapshots its store, and serves requests from that snapshot.
    /// `ops[i]` is the ABI function of import `i`, `entry` the function
    /// each request calls, `fuel` each request's fuel, `cap` the memory
    /// cap in pages. `None` if the instance's `memory.grow` limit is above
    /// the cap.
    pub fn new(inst: Checked, ops: Vec<u8>, entry: u32, fuel: u64, cap: u32) -> (r: Option<Func>)
        ensures
            r is Some ==> r->Some_0.template() == inst.view() && r->Some_0.cap() == cap
                && r->Some_0.fuel() == fuel,
    {
        if inst.mem_max() > cap {
            return None;
        }
        let (inst, snap) = inst.snapshot_clean();
        Some(Func { inst, snap, ops, entry, fuel, cap })
    }

    /// Serves one request. On anything but [`Outcome::Fault`], the guest
    /// ran from exactly [`Func::template`] (returned as ghost `start`),
    /// with at most [`Func::fuel`] fuel and a new reply; on
    /// [`Outcome::Done`] the reply satisfies [`reply_ok`] for `lim`.
    pub fn serve(self, req: Req, lim: Limits) -> (r: (Func, Outcome, Ghost<verilith_wasm::sem::Store>))
        ensures
            r.0.template() == self.template(),
            r.0.cap() == self.cap(),
            r.0.fuel() == self.fuel(),
            !(r.1 is Fault) ==> r.2@ == self.template() && r.2@.mem_max <= self.cap(),
            r.1 matches Outcome::Done(rep) ==> rep.limits() == lim && reply_ok(lim, rep.view()),
    {
        proof { use_type_invariant(&self); }
        let Func { inst, snap, ops, entry, fuel, cap } = self;
        // Copies back only the memory the last request wrote.
        let (inst, ok) = inst.reset(&snap);
        if !ok {
            return (Func { inst, snap, ops, entry, fuel, cap }, Outcome::Fault, Ghost(snap.view()));
        }
        let ghost start = inst.view();
        let mut abi = Abi { req, ops: ops.as_slice(), reply: Reply::new(lim) };
        let mut left = fuel;
        let args: [u64; 0] = [];
        let (inst, res) = inst.invoke(entry, &args, &mut abi, true, &mut left);
        let out = match res {
            Ok(_) => {
                let rep = abi.reply;
                rep.lemma_ok();
                // The verified host never changes a reply's limits, but
                // `invoke` is generic over the host and says nothing of it.
                let l = rep.lim();
                if l.max_body == lim.max_body && l.max_fields == lim.max_fields
                    && l.max_field_bytes == lim.max_field_bytes {
                    Outcome::Done(rep)
                } else {
                    Outcome::Fault
                }
            }
            Err(t) => Outcome::Trap(t),
        };
        (Func { inst, snap, ops, entry, fuel, cap }, out, Ghost(start))
    }
}

// ---------------------------------------------------------------------------
// Routing: /fn/<name>[/...]
// ---------------------------------------------------------------------------

/// Longest function name.
pub const MAX_NAME: usize = 64;

/// A function name's bytes: lower-case letters, digits, `-` and `_`.
pub open spec fn name_char(c: u8) -> bool {
    (0x61 <= c <= 0x7a) || (0x30 <= c <= 0x39) || c == 0x2d || c == 0x5f
}

pub open spec fn prefix() -> Seq<u8> {
    seq![0x2fu8, 0x66, 0x6e, 0x2f]
}

/// `p` is `/fn/` then a name ending at `e`, then the end or `/`.
pub open spec fn routes(p: Seq<u8>, e: int) -> bool {
    &&& p.len() >= 4 && p.subrange(0, 4) == prefix()
    &&& 4 < e <= 4 + MAX_NAME && e <= p.len()
    &&& forall|i: int| 4 <= i < e ==> name_char(#[trigger] p[i])
    &&& e == p.len() || p[e] == 0x2f
}

/// The end of the function name in a request path (the name is
/// `p[4..e]`), or `None` if the path names no function.
pub fn route(p: &[u8]) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> routes(p@, e as int),
        r is None ==> forall|e: int| !routes(p@, e),
{
    if p.len() < 4 || p[0] != 0x2f || p[1] != 0x66 || p[2] != 0x6e || p[3] != 0x2f {
        proof {
            assert forall|e: int| !routes(p@, e) by {
                if p@.len() >= 4 && p@.subrange(0, 4) == prefix() {
                    assert(p@[0] == p@.subrange(0, 4)[0] && p@[1] == p@.subrange(0, 4)[1]
                        && p@[2] == p@.subrange(0, 4)[2] && p@[3] == p@.subrange(0, 4)[3]);
                }
            }
        }
        return None;
    }
    assert(p@.subrange(0, 4) =~= prefix());
    let mut j = 4;
    while j < p.len() && j <= 4 + MAX_NAME && {
        let c = p[j];
        (c >= 0x61 && c <= 0x7a) || (c >= 0x30 && c <= 0x39) || c == 0x2d || c == 0x5f
    }
        invariant
            4 <= j <= p@.len(),
            j <= 5 + MAX_NAME,
            forall|i: int| 4 <= i < j ==> name_char(#[trigger] p@[i]),
        decreases p@.len() - j,
    {
        j += 1;
    }
    if j > 4 && j <= 4 + MAX_NAME && (j == p.len() || p[j] == 0x2f) {
        return Some(j);
    }
    proof {
        assert forall|e: int| !routes(p@, e) by {
            if routes(p@, e) {
                // Every byte before `e` is a name byte and `p[e]`, if any, is `/`,
                // so the scan stopped exactly at `e`.
                if e < j {
                    assert(name_char(p@[e]));
                } else if e > j {
                    assert(name_char(p@[j as int]));
                }
            }
        }
    }
    None
}

} // verus!
