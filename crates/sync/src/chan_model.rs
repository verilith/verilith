//! The channel's progress model as a ghost resource the code must follow.
//!
//! A [`Model`] holds a state of `progress::channel` together with the
//! execution that led to it. The only way to change it is `Model::step`,
//! which demands a proof that the change is a step of the model, by the
//! thread whose token the caller holds. `src/chan_sync.rs` keeps one
//! `Model` per direction inside the channel's invariant, next to the
//! permissions for the real atomics, and the invariant ties the two
//! together (the count of handles is `alive`, a waiter's flag is set
//! exactly when its ticket is in `notified`, and so on). So Verus checks,
//! at every access the channel code makes to shared state, that the model
//! can make the same move: the executions of the code are executions of
//! the model, and the progress theorems are about them.
//!
//! A thread of the model is a call in progress, not an OS thread: a call
//! takes an idle model thread from a pool when it starts (`Model::enter`)
//! and gives it back when it returns (`Model::leave`). The model has a
//! fixed number of threads, so this is where the one assumption of this
//! module is: `Model::pool_nonempty`.
// Some parameters and imports are used only in specifications and proofs.
#![allow(unused_variables, unused_imports, unused_mut)]
#[allow(unused_imports)]
use crate::progress::channel::*;
use vstd::prelude::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

/// The right to take steps as one thread of the model, with that thread's
/// current phase.
pub type ThreadTok = GhostPointsTo<nat, Th>;

/// `trace` is an execution of the model with `n` threads: it starts in an
/// initial state, and step `i` is a step of thread `sched[i]`.
pub open spec fn is_run(trace: Seq<St>, sched: Seq<nat>, n: nat) -> bool {
    &&& trace.len() == sched.len() + 1
    &&& init(trace[0], n)
    &&& forall|i: int| 0 <= i < sched.len() ==> #[trigger] step_at(trace, sched, n, i)
}

/// Step `i` of `trace` is a step of the model, by thread `sched[i]`.
pub open spec fn step_at(trace: Seq<St>, sched: Seq<nat>, n: nat, i: int) -> bool {
    sched[i] < n && step(trace[i], sched[i], trace[i + 1])
}

pub tracked struct Model {
    ghost trace: Seq<St>,
    ghost sched: Seq<nat>,
    ghost n: nat,
    tracked th: GhostMapAuth<nat, Th>,
    /// The tokens of the threads no call is using. All are idle.
    tracked pool: GhostSubmap<nat, Th>,
}

proof fn lemma_run_inv(trace: Seq<St>, sched: Seq<nat>, n: nat, i: int)
    requires
        is_run(trace, sched, n),
        0 <= i < trace.len(),
    ensures
        inv(trace[i], n),
    decreases i,
{
    if i == 0 {
        lemma_init(trace[0], n);
    } else {
        lemma_run_inv(trace, sched, n, i - 1);
        assert(step_at(trace, sched, n, i - 1));
        lemma_step(trace[i - 1], n, sched[i - 1], trace[i]);
    }
}

impl Model {
    /// The model's current state.
    pub closed spec fn view(&self) -> St {
        self.trace.last()
    }

    /// The execution so far.
    pub closed spec fn trace(&self) -> Seq<St> {
        self.trace
    }

    pub closed spec fn sched(&self) -> Seq<nat> {
        self.sched
    }

    /// The number of threads.
    pub closed spec fn n(&self) -> nat {
        self.n
    }

    pub closed spec fn loc(&self) -> Loc {
        self.th.id()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& is_run(self.trace, self.sched, self.n)
        &&& self.th@.dom() =~= Set::range(0, self.n)
        &&& forall|t: nat| t < self.n ==> #[trigger] self.th@[t] == self@.th[t as int]
        &&& self.pool.id() == self.th.id()
        &&& forall|t: nat| #[trigger] self.pool@.contains_key(t) ==> self.pool@[t].ph == Ph::Idle
    }

    /// A model in initial state `s0`, with every thread in the pool.
    pub proof fn new(s0: St, n: nat) -> (tracked r: Model)
        requires
            init(s0, n),
        ensures
            r.wf(),
            r@ == s0,
            r.n() == n,
    {
        broadcast use vstd::set_lib::range_set_properties;

        let m = Map::new(Set::range(0, n), |t: nat| s0.th[t as int]);
        let tracked (th, pool) = GhostMapAuth::new(m);
        let tracked r = Model { trace: seq![s0], sched: Seq::empty(), n, th, pool };
        assert forall|t: nat| #[trigger] r.pool@.contains_key(t) implies r.pool@[t].ph == Ph::Idle by {
            assert(s0.th[t as int].ph == Ph::Idle);
        }
        r
    }

    /// Every state the code reaches is the last state of an execution of
    /// the model.
    pub proof fn lemma_is_run(tracked &self)
        requires
            self.wf(),
        ensures
            is_run(self.trace(), self.sched(), self.n()),
            self@ == self.trace().last(),
    {
    }

    /// The invariant of `progress::channel` holds of the current state.
    pub proof fn lemma_inv(tracked &self)
        requires
            self.wf(),
        ensures
            inv(self@, self.n()),
            self@.th.len() == self.n(),
    {
        lemma_run_inv(self.trace, self.sched, self.n, self.trace.len() - 1);
    }

    /// A thread's token says what phase the model has that thread in.
    pub proof fn agree(tracked &self, tracked tok: &ThreadTok)
        requires
            self.wf(),
            tok.id() == self.loc(),
        ensures
            tok.key() < self.n(),
            self@.th.len() == self.n(),
            self@.th[tok.key() as int] == tok.value(),
    {
        broadcast use vstd::set_lib::range_set_properties;

        self.lemma_inv();
        tok.agree(&self.th);
        assert(self.th@.dom().contains(tok.key()));
    }

    /// The model takes a step of the token's thread.
    pub proof fn step(tracked &mut self, tracked tok: &mut ThreadTok, s2: St)
        requires
            old(self).wf(),
            old(tok).id() == old(self).loc(),
            step(old(self)@, old(tok).key(), s2),
        ensures
            final(self).wf(),
            final(self)@ == s2,
            final(self).loc() == old(self).loc(),
            final(self).n() == old(self).n(),
            final(self).trace() == old(self).trace().push(s2),
            final(self).sched() == old(self).sched().push(old(tok).key()),
            final(tok).id() == old(tok).id(),
            final(tok).key() == old(tok).key(),
            final(tok).value() == s2.th[old(tok).key() as int],
    {
        broadcast use vstd::set_lib::range_set_properties;

        let s = self@;
        let t = tok.key();
        let n = self.n;
        self.agree(tok);
        self.lemma_inv();
        lemma_step_frame(s, n, t, s2);
        tok.disjoint_submap(&self.pool);
        tok.update(&mut self.th, s2.th[t as int]);
        let ghost trace0 = self.trace;
        let ghost sched0 = self.sched;
        self.trace = trace0.push(s2);
        self.sched = sched0.push(t);
        assert forall|i: int| 0 <= i < self.sched.len() implies #[trigger] step_at(self.trace, self.sched, n, i) by {
            if i < sched0.len() {
                assert(step_at(trace0, sched0, n, i));
            }
        }
        assert(self.th@.dom() =~= Set::range(0, n));
        assert forall|u: nat| u < n implies #[trigger] self.th@[u] == s2.th[u as int] by {
            if u != t {
                assert(s2.th[u as int] == s.th[u as int]);
            }
        }
    }

    /// TRUSTED. Some thread of the model is in no call.
    ///
    /// The model has `n` threads, for an `n` fixed when the channel is
    /// created, and a call acts as one of them from start to return. So
    /// this assumes that fewer than `n` calls are ever in progress on one
    /// channel at once. `n` is not a number in the program: nothing bounds
    /// it, and the progress theorems hold for every `n`. So the assumption
    /// is that the number of calls in progress at once is bounded at all,
    /// which holds for any program whose number of threads is.
    axiom fn pool_nonempty(tracked &self)
        requires
            self.wf(),
        ensures
            exists|t: nat| self.pool@.contains_key(t),
    ;

    /// A call starts: it takes an idle thread from the pool.
    pub proof fn enter(tracked &mut self) -> (tracked tok: ThreadTok)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@,
            final(self).loc() == old(self).loc(),
            final(self).n() == old(self).n(),
            final(self).trace() == old(self).trace(),
            final(self).sched() == old(self).sched(),
            tok.id() == final(self).loc(),
            tok.value().ph == Ph::Idle,
    {
        self.pool_nonempty();
        let t = choose|t: nat| self.pool@.contains_key(t);
        self.pool.split_points_to(t)
    }

    /// A call returns: its thread, idle again, goes back to the pool.
    pub proof fn leave(tracked &mut self, tracked tok: ThreadTok)
        requires
            old(self).wf(),
            tok.id() == old(self).loc(),
            tok.value().ph == Ph::Idle,
        ensures
            final(self).wf(),
            final(self)@ == old(self)@,
            final(self).loc() == old(self).loc(),
            final(self).n() == old(self).n(),
            final(self).trace() == old(self).trace(),
            final(self).sched() == old(self).sched(),
    {
        self.pool.combine_points_to(tok);
    }
}

} // verus!
