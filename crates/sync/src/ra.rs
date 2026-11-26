//! A release/acquire memory model for Verus proofs.
//!
//! Verus's own atomics (`vstd::atomic`) are sequentially consistent. This
//! module axiomatizes atomics with weaker orderings, following the
//! view-based operational model of ORC11 (Dang, Jourdan, Kaiser and Dreyer,
//! "RustBelt Meets Relaxed Memory", POPL 2020), which is sound for C11/Rust
//! release, acquire and relaxed accesses:
//!
//! - Each atomic location has a *history*: the sequence of messages written
//!   to it, in modification order. A message carries a value and a *view*.
//! - A *view* maps each location to a timestamp (an index into its history).
//!   Each thread has a current view: the messages it has observed, directly
//!   or through synchronization.
//! - A load may read any message at or after the thread's timestamp for the
//!   location (coherence). An acquire load also joins the message's view
//!   into the thread's view.
//! - A release store appends a message whose view is the thread's view; a
//!   relaxed store's message carries only its own timestamp.
//! - A read-modify-write reads the *last* message and appends a new one
//!   right after it.
//!
//! C11 may instead place a store anywhere after the messages its thread
//! has seen (but never between an RMW and the message it read), and let
//! an RMW read any message no other RMW has read. The operations below
//! append only where C11 leaves no other choice: a store or RMW by a
//! thread that has seen the last message (`Hist::seen_last`), or an RMW
//! on a location that only RMWs have written (`Hist::rmw_only`). Proofs
//! that use only them hold for C11. The `_sra` operations append
//! unconditionally: that is the strong release/acquire model of x86,
//! ARMv8 and POWER, not C11, and only `spsc` uses them (TRUST.md, "Where
//! writes go").
//!
//! In proofs, [`Tid`] is a lower bound on the current thread's view, and
//! [`Hist`] is a location's history. Resources whose validity depends on
//! the thread's view ("subjective" resources: cell permissions, and `Tid`
//! itself) may cross threads only inside [`Published`], which records the
//! view they were published at and releases them only to a thread whose
//! view has caught up. Shared invariants must hold only *objective*
//! resources (ghost state, histories, `Published`), which [`ObjInvariant`]
//! enforces through the [`Objective`] trait.
//!
//! Everything here is trusted: the `external_body` functions and `axiom`s
//! are the model. See TRUST.md for the argument that they are sound.
use std::sync::atomic::{AtomicU64, Ordering};
use vstd::invariant::*;
use vstd::prelude::*;

verus! {

/// A view: a timestamp for every location.
pub ghost struct RaView {
    pub ts: spec_fn(int) -> nat,
}

impl RaView {
    pub open spec fn bot() -> RaView {
        RaView { ts: |l: int| 0nat }
    }

    pub open spec fn at(self, l: int) -> nat {
        (self.ts)(l)
    }

    pub open spec fn le(self, o: RaView) -> bool {
        forall|l: int| #[trigger] self.at(l) <= o.at(l)
    }

    pub open spec fn join(self, o: RaView) -> RaView {
        RaView { ts: |l: int| if self.at(l) >= o.at(l) { self.at(l) } else { o.at(l) } }
    }

    pub open spec fn single(l: int, t: nat) -> RaView {
        RaView { ts: |k: int| if k == l { t } else { 0nat } }
    }
}

pub proof fn lemma_view_le_refl(a: RaView)
    ensures
        a.le(a),
{
}

pub proof fn lemma_view_le_trans(a: RaView, b: RaView, c: RaView)
    requires
        a.le(b),
        b.le(c),
    ensures
        a.le(c),
{
    assert forall|l: int| #[trigger] a.at(l) <= c.at(l) by {
        assert(a.at(l) <= b.at(l));
        assert(b.at(l) <= c.at(l));
    }
}

pub proof fn lemma_view_join(a: RaView, b: RaView)
    ensures
        a.le(a.join(b)),
        b.le(a.join(b)),
        forall|c: RaView| a.le(c) && b.le(c) ==> #[trigger] a.join(b).le(c),
{
    assert forall|l: int| #[trigger] a.at(l) <= a.join(b).at(l) by {}
    assert forall|l: int| #[trigger] b.at(l) <= a.join(b).at(l) by {}
    assert forall|c: RaView| a.le(c) && b.le(c) implies #[trigger] a.join(b).le(c) by {
        assert forall|l: int| #[trigger] a.join(b).at(l) <= c.at(l) by {
            assert(a.at(l) <= c.at(l));
            assert(b.at(l) <= c.at(l));
        }
    }
}

/// After an acquire of message `m`, the thread's view covers `m`'s view and
/// everything it covered before.
pub proof fn lemma_acquired(before: RaView, m: RaView, l: int, i: nat, after: RaView)
    requires
        after == before.join(m).join(RaView::single(l, i)),
    ensures
        before.le(after),
        m.le(after),
{
    lemma_view_join(before, m);
    lemma_view_join(before.join(m), RaView::single(l, i));
    lemma_view_le_trans(before, before.join(m), after);
    lemma_view_le_trans(m, before.join(m), after);
}

/// After a release store, the thread's view covers what it covered before.
pub proof fn lemma_stored(before: RaView, l: int, i: nat, after: RaView)
    requires
        after == before.join(RaView::single(l, i)),
    ensures
        before.le(after),
{
    lemma_view_join(before, RaView::single(l, i));
}

/// A lower bound on the current thread's view.
///
/// It is subjective: it stays with the code that holds it, and moves to
/// another thread only along with a synchronizing transfer (spawning,
/// a channel, a lock, or a `Published` handed over through an atomic).
///
/// `Tid` is neither `Send` nor `Sync`, so the type system enforces that:
/// a `Tid` cannot be put in a shared vstd invariant or otherwise handed to
/// another thread except inside a type that opts back in with an
/// `unsafe impl Send` justified by a synchronizing transfer (`Producer`,
/// `Consumer`).
///
/// ```compile_fail
/// fn assert_send<T: Send>() {}
/// assert_send::<verilith_sync::ra::Tid>();
/// ```
///
/// ```compile_fail
/// fn assert_sync<T: Sync>() {}
/// assert_sync::<verilith_sync::ra::Tid>();
/// ```
#[verifier::external_body]
pub tracked struct Tid {
    _not_send: core::marker::PhantomData<*const ()>,
}

impl Tid {
    pub uninterp spec fn view(&self) -> RaView;

    /// The bottom view is a lower bound on every thread's view.
    pub axiom fn new() -> (tracked t: Tid)
        ensures
            t.view() == RaView::bot();

    /// A lower bound can be copied.
    pub axiom fn dup(tracked &self) -> (tracked t: Tid)
        ensures
            t.view() == self.view();

    /// Two lower bounds on the same thread's view combine.
    pub axiom fn join(tracked &mut self, tracked other: &Tid)
        ensures
            final(self).view() == old(self).view().join(other.view());
}

/// A subjective resource made objective by recording the view it was
/// published at.
#[verifier::external_body]
#[verifier::reject_recursive_types_in_ground_variants(T)]
pub tracked struct Published<T> {
    _t: core::marker::PhantomData<T>,
}

impl<T> Published<T> {
    pub uninterp spec fn view(&self) -> RaView;

    pub uninterp spec fn value(&self) -> T;

    pub axiom fn publish(tracked t: T, tracked tid: &Tid) -> (tracked p: Published<T>)
        ensures
            p.view() == tid.view(),
            p.value() == t;

    /// Recovers the resource in a thread that has seen everything the
    /// publishing thread had seen.
    pub axiom fn acquire(tracked self, tracked tid: &Tid) -> (tracked t: T)
        requires
            self.view().le(tid.view()),
        ensures
            t == self.value();
}

/// Resources whose meaning does not depend on any thread's view, and so may
/// live in a shared invariant.
///
/// Implementing it is a trusted claim: the type must not contain a `Tid` or
/// a raw cell permission except inside `Published`.
pub trait Objective {}

/// An atomic invariant whose contents are objective.
pub struct ObjInvariant<K, V: Objective, Pred: InvariantPredicate<K, V>> {
    inv: AtomicInvariant<K, V, Pred>,
}

impl<K, V: Objective, Pred: InvariantPredicate<K, V>> ObjInvariant<K, V, Pred> {
    pub closed spec fn constant(&self) -> K {
        self.inv.constant()
    }

    pub closed spec fn namespace(&self) -> int {
        self.inv.namespace()
    }

    pub proof fn new(k: K, tracked v: V, ns: int) -> (tracked i: Self)
        requires
            Pred::inv(k, v),
        ensures
            i.constant() == k,
            i.namespace() == ns,
    {
        ObjInvariant { inv: AtomicInvariant::new(k, v, ns) }
    }

    /// The invariant, for `open_atomic_invariant!`.
    pub proof fn inner(tracked &self) -> (tracked i: &AtomicInvariant<K, V, Pred>)
        ensures
            i.constant() == self.constant(),
            i.namespace() == self.namespace(),
    {
        &self.inv
    }

    pub proof fn into_inner(tracked self) -> (tracked v: V)
        ensures
            Pred::inv(self.constant(), v),
        opens_invariants [ self.namespace() ]
    {
        self.inv.into_inner()
    }
}

/// One write to an atomic location.
pub ghost struct Msg {
    pub val: u64,
    pub view: RaView,
}

/// The history of an atomic location, oldest message first.
#[verifier::external_body]
pub tracked struct Hist {}

impl Objective for Hist {}

impl Hist {
    pub uninterp spec fn loc(&self) -> int;

    pub uninterp spec fn msgs(&self) -> Seq<Msg>;

    pub open spec fn last(&self) -> Msg {
        self.msgs().last()
    }

    /// Every message but the first was written by a read-modify-write of
    /// the message before it. In C11 no other write can then come between
    /// two of them, so the only message an RMW can read is the last.
    pub uninterp spec fn rmw_only(&self) -> bool;

    /// The thread has seen the last message: no write it has not seen
    /// can go after its next one.
    pub open spec fn seen_last(&self, tid: &Tid) -> bool {
        tid.view().at(self.loc()) == self.msgs().len() - 1
    }

    /// What C11 needs for a read-modify-write to read the last message.
    pub open spec fn rmw_reads_last(&self, tid: &Tid) -> bool {
        self.rmw_only() || self.seen_last(tid)
    }

    /// Every location has its initial message.
    pub axiom fn nonempty_lemma(tracked &self)
        ensures
            self.msgs().len() > 0;

    /// No thread has seen past the end of a history: views are built only
    /// from timestamps of messages that exist.
    pub axiom fn bounded_lemma(tracked &self, tracked tid: &Tid)
        ensures
            tid.view().at(self.loc()) < self.msgs().len();

    /// A snapshot of the history so far. Histories only grow, so the
    /// snapshot stays a prefix of the history forever.
    pub axiom fn lb(tracked &self) -> (tracked l: HistLb)
        ensures
            l.loc() == self.loc(),
            l.msgs() == self.msgs();

    pub axiom fn lb_prefix(tracked &self, tracked l: &HistLb)
        requires
            l.loc() == self.loc(),
        ensures
            l.msgs().len() <= self.msgs().len(),
            forall|i: int| 0 <= i < l.msgs().len() ==> #[trigger] l.msgs()[i] == self.msgs()[i];
}

/// A persistent lower bound on a history: a prefix of it.
#[verifier::external_body]
pub tracked struct HistLb {}

impl Objective for HistLb {}

impl HistLb {
    pub uninterp spec fn loc(&self) -> int;

    pub uninterp spec fn msgs(&self) -> Seq<Msg>;

    pub axiom fn dup(tracked &self) -> (tracked l: HistLb)
        ensures
            l.loc() == self.loc(),
            l.msgs() == self.msgs();
}

/// A 64-bit atomic with release/acquire/relaxed operations.
#[verifier::external_body]
pub struct RaU64 {
    a: AtomicU64,
}

impl RaU64 {
    pub uninterp spec fn id(&self) -> int;

    #[verifier::external_body]
    pub fn new(v: u64, Tracked(tid): Tracked<&mut Tid>) -> (r: (RaU64, Tracked<Hist>))
        ensures
            r.1@.loc() == r.0.id(),
            r.1@.msgs() == seq![Msg { val: v, view: final(tid).view() }],
            r.1@.rmw_only(),
            final(tid).view() == old(tid).view().join(RaView::single(r.0.id(), 0)),
    {
        (RaU64 { a: AtomicU64::new(v) }, Tracked::assume_new())
    }

    /// An acquire load. Returns the value and the index of the message read.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_acquire(&self, Tracked(h): Tracked<&Hist>, Tracked(tid): Tracked<&mut Tid>) -> (r: (u64, Ghost<nat>))
        requires
            h.loc() == self.id(),
        ensures
            old(tid).view().at(self.id()) <= r.1@ < h.msgs().len(),
            r.0 == h.msgs()[r.1@ as int].val,
            final(tid).view() == old(tid).view().join(h.msgs()[r.1@ as int].view).join(RaView::single(self.id(), r.1@)),
        opens_invariants none
        no_unwind
    {
        (self.a.load(Ordering::Acquire), Ghost::assume_new())
    }

    /// A relaxed load: coherence, but no synchronization.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn load_relaxed(&self, Tracked(h): Tracked<&Hist>, Tracked(tid): Tracked<&mut Tid>) -> (r: (u64, Ghost<nat>))
        requires
            h.loc() == self.id(),
        ensures
            old(tid).view().at(self.id()) <= r.1@ < h.msgs().len(),
            r.0 == h.msgs()[r.1@ as int].val,
            final(tid).view() == old(tid).view().join(RaView::single(self.id(), r.1@)),
        opens_invariants none
        no_unwind
    {
        (self.a.load(Ordering::Relaxed), Ghost::assume_new())
    }

    /// A release store: the new message carries the thread's view.
    ///
    /// C11 lets a store take any place in modification order after the
    /// messages the thread has seen, except between a read-modify-write
    /// and the message it read. A thread that has seen the last message
    /// leaves it one place: the end.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, v: u64)
        requires
            old(h).loc() == self.id(),
            old(h).seen_last(old(tid)),
        ensures
            final(h).loc() == self.id(),
            !final(h).rmw_only(),
            final(tid).view() == old(tid).view().join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: v, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.store(v, Ordering::Release)
    }

    /// A release store, in the SRA model: appended whether or not the
    /// thread has seen the last message. This is what x86, ARMv8 and POWER
    /// provide (TRUST.md, "Where writes go"),
    /// but not every C11 execution; only `spsc` uses it.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn store_release_sra(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, v: u64)
        requires
            old(h).loc() == self.id(),
        ensures
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: v, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.store(v, Ordering::Release)
    }

    /// An acquire-release fetch-and-add. It reads the last message, so it
    /// sees the location's current value.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn fetch_add_acqrel(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, n: u64) -> (r: u64)
        requires
            old(h).loc() == self.id(),
            old(h).last().val + n <= u64::MAX,
            old(h).rmw_reads_last(old(tid)),
        ensures
            final(h).rmw_only() == old(h).rmw_only(),
            r == old(h).last().val,
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: (r + n) as u64, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.fetch_add(n, Ordering::AcqRel)
    }

    /// An acquire-release fetch-and-add, in the SRA model: it reads the
    /// last message whatever the thread has seen. Only `spsc` uses it
    /// (TRUST.md, "Where writes go").
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn fetch_add_acqrel_sra(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, n: u64) -> (r: u64)
        requires
            old(h).loc() == self.id(),
            old(h).last().val + n <= u64::MAX,
        ensures
            r == old(h).last().val,
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: (r + n) as u64, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.fetch_add(n, Ordering::AcqRel)
    }

    /// A SeqCst fetch-and-add, with the same (acquire-release) meaning in
    /// this model as `fetch_add_acqrel`. The MPMC queue uses it, adding 0,
    /// to confirm that it is full or empty; the extra SeqCst ordering is
    /// for the channel's parking handshake, as for
    /// `compare_exchange_seqcst` below (TRUST.md, "The channel"). On x86
    /// and ARMv8 it compiles to the same instructions as AcqRel.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn fetch_add_seqcst(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, n: u64) -> (r: u64)
        requires
            old(h).loc() == self.id(),
            old(h).last().val + n <= u64::MAX,
            old(h).rmw_reads_last(old(tid)),
        ensures
            final(h).rmw_only() == old(h).rmw_only(),
            r == old(h).last().val,
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: (r + n) as u64, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.fetch_add(n, Ordering::SeqCst)
    }

    /// An acquire-release fetch-and-subtract.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn fetch_sub_acqrel(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, n: u64) -> (r: u64)
        requires
            old(h).loc() == self.id(),
            old(h).last().val >= n,
            old(h).rmw_reads_last(old(tid)),
        ensures
            final(h).rmw_only() == old(h).rmw_only(),
            r == old(h).last().val,
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: (r - n) as u64, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.fetch_sub(n, Ordering::AcqRel)
    }

    /// An acquire-release fetch-and-subtract, in the SRA model (see
    /// `fetch_add_acqrel_sra`). Only `spsc` uses it.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn fetch_sub_acqrel_sra(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, n: u64) -> (r: u64)
        requires
            old(h).loc() == self.id(),
            old(h).last().val >= n,
        ensures
            r == old(h).last().val,
            final(h).loc() == self.id(),
            final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len())),
            final(h).msgs() == old(h).msgs().push(Msg { val: (r - n) as u64, view: final(tid).view() }),
        opens_invariants none
        no_unwind
    {
        self.a.fetch_sub(n, Ordering::AcqRel)
    }

    /// A compare-and-swap, SeqCst on success and relaxed on failure. The
    /// model gives it only acquire-release meaning, which SeqCst includes:
    /// on success it is a read-modify-write of the last message; on failure
    /// it is a relaxed load, which may read any message the thread has not
    /// seen past. The extra SeqCst ordering is for the channel's parking
    /// handshake (`src/chan_sync.rs`), whose proof treats SeqCst operations
    /// as interleaved (TRUST.md, "The channel"); on x86 and ARMv8 it compiles to the same instruction as
    /// AcqRel.
    #[inline(always)]
    #[verifier::external_body]
    #[verifier::atomic]
    pub fn compare_exchange_seqcst(&self, Tracked(h): Tracked<&mut Hist>, Tracked(tid): Tracked<&mut Tid>, current: u64, new: u64) -> (r: (Result<u64, u64>, Ghost<nat>))
        requires
            old(h).loc() == self.id(),
            old(h).rmw_reads_last(old(tid)),
        ensures
            final(h).loc() == self.id(),
            match r.0 {
                Ok(v) => {
                    &&& v == current
                    &&& old(h).last().val == current
                    &&& final(tid).view() == old(tid).view().join(old(h).last().view).join(RaView::single(self.id(), old(h).msgs().len()))
                    &&& final(h).msgs() == old(h).msgs().push(Msg { val: new, view: final(tid).view() })
                    &&& final(h).rmw_only() == old(h).rmw_only()
                },
                Err(v) => {
                    &&& old(tid).view().at(self.id()) <= r.1@ < old(h).msgs().len()
                    &&& v == old(h).msgs()[r.1@ as int].val
                    &&& final(tid).view() == old(tid).view().join(RaView::single(self.id(), r.1@))
                    &&& *final(h) == *old(h)
                },
            },
        opens_invariants none
        no_unwind
    {
        (self.a.compare_exchange(current, new, Ordering::SeqCst, Ordering::Relaxed), Ghost::assume_new())
    }

    /// A thread with exclusive access to an atomic has synchronized with
    /// every write to it: Rust only hands out `&mut` after the accesses
    /// through shared references are over and happen before it (which is
    /// what makes `AtomicU64::get_mut` safe). Does nothing at run time.
    #[inline(always)]
    #[verifier::external_body]
    pub fn sync_exclusive(&mut self, Tracked(h): Tracked<&Hist>, Tracked(tid): Tracked<&mut Tid>)
        requires
            h.loc() == old(self).id(),
            h.msgs().len() > 0,
        ensures
            final(self).id() == old(self).id(),
            final(tid).view() == old(tid).view().join(h.last().view).join(RaView::single(old(self).id(), (h.msgs().len() - 1) as nat)),
    {
    }
}

} // verus!
