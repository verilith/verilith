//! A progress model as a ghost resource the code must follow, for any
//! protocol of `src/progress/`.
//!
//! A [`Model`] holds a state of a protocol together with the execution
//! that led to it. The only way to change it is `Model::step`, which
//! demands a proof that the change is a step of the protocol, by the
//! thread whose token the caller holds. A primitive keeps its `Model`
//! inside its invariant, next to the permissions for its atomics, and the
//! invariant ties the two together. So Verus checks, at every access the
//! code makes to shared state, that the model can make the same move: the
//! executions of the code are executions of the model, and the progress
//! theorems are about them.
//!
//! A thread of the model is a call in progress, not an OS thread: a call
//! takes an idle model thread from a pool when it starts (`Model::enter`)
//! and gives it back when it returns (`Model::leave`). The model has a
//! fixed number of threads, so this is where the one assumption of this
//! module is: `Model::pool_nonempty`.
//!
//! The channel (`src/chan_sync.rs`, through `src/chan_model.rs`), the
//! mutex, the RwLock and the MPMC queue each keep one.
// Some parameters and imports are used only in specifications and proofs.
#![allow(unused_variables, unused_imports, unused_mut)]
use vstd::prelude::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

/// A protocol of `src/progress/`, as `Model` needs it: its states, its
/// steps, and an inductive invariant that keeps the thread count.
pub trait Protocol {
    /// A state of the protocol.
    type St;
    /// One thread's part of a state: its phase.
    type Th;

    spec fn init(s: Self::St, n: nat) -> bool;

    spec fn step(s: Self::St, t: nat, s2: Self::St) -> bool;

    spec fn inv(s: Self::St, n: nat) -> bool;

    /// Each thread's part of the state.
    spec fn threads(s: Self::St) -> Seq<Self::Th>;

    /// The thread is in no call.
    spec fn idle(th: Self::Th) -> bool;

    proof fn lemma_init(s: Self::St, n: nat)
        requires
            Self::init(s, n),
        ensures
            Self::inv(s, n),
            Self::threads(s).len() == n,
            forall|t: int| 0 <= t < n ==> Self::idle(#[trigger] Self::threads(s)[t]),
    ;

    proof fn lemma_step(s: Self::St, n: nat, t: nat, s2: Self::St)
        requires
            Self::inv(s, n),
            t < n,
            Self::step(s, t, s2),
        ensures
            Self::inv(s2, n),
            Self::threads(s2).len() == n,
            forall|u: int| 0 <= u < n && u != t ==> #[trigger] Self::threads(s2)[u] == Self::threads(s)[u],
    ;

    proof fn lemma_len(s: Self::St, n: nat)
        requires
            Self::inv(s, n),
        ensures
            Self::threads(s).len() == n,
    ;
}

/// The right to take steps as one thread of the model, with that thread's
/// current phase.
pub type Tok<P> = GhostPointsTo<nat, <P as Protocol>::Th>;

/// `trace` is an execution of the protocol with `n` threads: it starts in
/// an initial state, and step `i` is a step of thread `sched[i]`.
pub open spec fn is_run<P: Protocol>(trace: Seq<P::St>, sched: Seq<nat>, n: nat) -> bool {
    &&& trace.len() == sched.len() + 1
    &&& P::init(trace[0], n)
    &&& forall|i: int| 0 <= i < sched.len() ==> #[trigger] step_at::<P>(trace, sched, n, i)
}

/// Step `i` of `trace` is a step of the protocol, by thread `sched[i]`.
pub open spec fn step_at<P: Protocol>(trace: Seq<P::St>, sched: Seq<nat>, n: nat, i: int) -> bool {
    sched[i] < n && P::step(trace[i], sched[i], trace[i + 1])
}

pub tracked struct Model<P: Protocol> {
    ghost trace: Seq<P::St>,
    ghost sched: Seq<nat>,
    ghost n: nat,
    tracked th: GhostMapAuth<nat, P::Th>,
    /// The tokens of the threads no call is using. All are idle.
    tracked pool: GhostSubmap<nat, P::Th>,
}

proof fn lemma_run_inv<P: Protocol>(trace: Seq<P::St>, sched: Seq<nat>, n: nat, i: int)
    requires
        is_run::<P>(trace, sched, n),
        0 <= i < trace.len(),
    ensures
        P::inv(trace[i], n),
    decreases i,
{
    if i == 0 {
        P::lemma_init(trace[0], n);
    } else {
        lemma_run_inv::<P>(trace, sched, n, i - 1);
        assert(step_at::<P>(trace, sched, n, i - 1));
        P::lemma_step(trace[i - 1], n, sched[i - 1], trace[i]);
    }
}

impl<P: Protocol> Model<P> {
    /// The model's current state.
    pub closed spec fn view(&self) -> P::St {
        self.trace.last()
    }

    /// The execution so far.
    pub closed spec fn trace(&self) -> Seq<P::St> {
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
        &&& is_run::<P>(self.trace, self.sched, self.n)
        &&& self.th@.dom() =~= Set::range(0, self.n)
        &&& forall|t: nat| t < self.n ==> #[trigger] self.th@[t] == P::threads(self@)[t as int]
        &&& self.pool.id() == self.th.id()
        &&& forall|t: nat| #[trigger] self.pool@.contains_key(t) ==> P::idle(self.pool@[t])
    }

    /// A model in initial state `s0`, with every thread in the pool.
    pub proof fn new(s0: P::St, n: nat) -> (tracked r: Model<P>)
        requires
            P::init(s0, n),
        ensures
            r.wf(),
            r@ == s0,
            r.n() == n,
    {
        broadcast use vstd::set_lib::range_set_properties;

        P::lemma_init(s0, n);
        let m = Map::new(Set::range(0, n), |t: nat| P::threads(s0)[t as int]);
        let tracked (th, pool) = GhostMapAuth::new(m);
        let tracked r = Model { trace: seq![s0], sched: Seq::empty(), n, th, pool };
        assert forall|t: nat| #[trigger] r.pool@.contains_key(t) implies P::idle(r.pool@[t]) by {
            assert(P::idle(P::threads(s0)[t as int]));
        }
        assert forall|i: int| 0 <= i < r.sched.len() implies #[trigger] step_at::<P>(r.trace, r.sched, n, i) by {}
        r
    }

    /// Every state the code reaches is the last state of an execution of
    /// the protocol.
    pub proof fn lemma_is_run(tracked &self)
        requires
            self.wf(),
        ensures
            is_run::<P>(self.trace(), self.sched(), self.n()),
            self@ == self.trace().last(),
    {
    }

    /// The protocol's invariant holds of the current state.
    pub proof fn lemma_inv(tracked &self)
        requires
            self.wf(),
        ensures
            P::inv(self@, self.n()),
            P::threads(self@).len() == self.n(),
    {
        lemma_run_inv::<P>(self.trace, self.sched, self.n, self.trace.len() - 1);
        P::lemma_len(self@, self.n);
    }

    /// A thread's token says what phase the model has that thread in.
    pub proof fn agree(tracked &self, tracked tok: &Tok<P>)
        requires
            self.wf(),
            tok.id() == self.loc(),
        ensures
            tok.key() < self.n(),
            P::threads(self@).len() == self.n(),
            P::threads(self@)[tok.key() as int] == tok.value(),
    {
        broadcast use vstd::set_lib::range_set_properties;

        self.lemma_inv();
        tok.agree(&self.th);
        assert(self.th@.dom().contains(tok.key()));
    }

    /// The model takes a step of the token's thread.
    pub proof fn step(tracked &mut self, tracked tok: &mut Tok<P>, s2: P::St)
        requires
            old(self).wf(),
            old(tok).id() == old(self).loc(),
            P::step(old(self)@, old(tok).key(), s2),
        ensures
            final(self).wf(),
            final(self)@ == s2,
            final(self).loc() == old(self).loc(),
            final(self).n() == old(self).n(),
            final(self).trace() == old(self).trace().push(s2),
            final(self).sched() == old(self).sched().push(old(tok).key()),
            final(tok).id() == old(tok).id(),
            final(tok).key() == old(tok).key(),
            final(tok).value() == P::threads(s2)[old(tok).key() as int],
    {
        broadcast use vstd::set_lib::range_set_properties;

        let s = self@;
        let t = tok.key();
        let n = self.n;
        self.agree(tok);
        self.lemma_inv();
        P::lemma_step(s, n, t, s2);
        tok.disjoint_submap(&self.pool);
        tok.update(&mut self.th, P::threads(s2)[t as int]);
        let ghost trace0 = self.trace;
        let ghost sched0 = self.sched;
        self.trace = trace0.push(s2);
        self.sched = sched0.push(t);
        assert forall|i: int| 0 <= i < self.sched.len() implies #[trigger] step_at::<P>(self.trace, self.sched, n, i) by {
            if i < sched0.len() {
                assert(step_at::<P>(trace0, sched0, n, i));
            }
        }
        assert(self.th@.dom() =~= Set::range(0, n));
        assert forall|u: nat| u < n implies #[trigger] self.th@[u] == P::threads(s2)[u as int] by {
            if u != t {
                assert(P::threads(s2)[u as int] == P::threads(s)[u as int]);
            }
        }
    }

    /// TRUSTED. Some thread of the model is in no call.
    ///
    /// The model has `n` threads, for an `n` fixed when the primitive is
    /// created, and a call acts as one of them from start to return (a
    /// lock call, until its guard is dropped). So this assumes that fewer
    /// than `n` calls are ever in progress on one primitive at once. `n` is
    /// not a number in the program: nothing bounds it, and the progress
    /// theorems hold for every `n`. So the assumption is that the number
    /// of calls in progress at once is bounded at all, which holds for any
    /// program whose number of threads is (a guard leaked with
    /// `mem::forget` counts as a call that never returns).
    axiom fn pool_nonempty(tracked &self)
        requires
            self.wf(),
        ensures
            exists|t: nat| self.pool@.contains_key(t),
    ;

    /// A call starts: it takes an idle thread from the pool.
    pub proof fn enter(tracked &mut self) -> (tracked tok: Tok<P>)
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
            P::idle(tok.value()),
    {
        self.pool_nonempty();
        let t = choose|t: nat| self.pool@.contains_key(t);
        self.pool.split_points_to(t)
    }

    /// A call returns: its thread, idle again, goes back to the pool.
    pub proof fn leave(tracked &mut self, tracked tok: Tok<P>)
        requires
            old(self).wf(),
            tok.id() == old(self).loc(),
            P::idle(tok.value()),
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
