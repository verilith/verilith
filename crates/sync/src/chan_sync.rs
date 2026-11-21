//! The channel's blocking protocol, verified against the progress model.
//!
//! This is the code under `src/channel.rs`: the waiter lists, the handle
//! counts, and the loops that run a send or a receive. Every access it
//! makes to shared state (a load or store of an atomic, a queue operation's
//! linearization point) is made with the channel's invariant open, and the
//! invariant holds, next to the permissions for those atomics, one
//! [`Model`] per direction: a state of `progress::channel` that can only be
//! changed by a proven step of that model. So each access is checked to be
//! the model step `chan_core` says it is, and the invariant is checked to
//! tie the real state to the model's after it:
//!
//! - the other side's handle count is the model's `alive`;
//! - the queue's length is `c` for receivers, and capacity minus length is
//!   `c` for senders;
//! - a waiter's `notified` flag is set exactly when its ticket is in the
//!   model's `notified`;
//! - the waiter list under the lock is the model's `list`, and `empty`,
//!   when it says so, is right.
//!
//! The model has two copies, one per direction. In direction `true` the
//! takers are receivers (`c` counts messages and `alive` counts senders);
//! in direction `false` they are senders (`c` counts free slots and
//! `alive` counts receivers). A successful pop is a take in direction
//! `true` and a give in direction `false`, both at the pop's linearization
//! point; a push is the reverse.
//!
//! What is not proved here is listed in `TRUST.md`.
// Some parameters and imports are used only in specifications and proofs.
#![allow(unused_variables, unused_imports, unused_mut)]
use crate::array_queue::*;
use crate::chan_core::*;
use crate::chan_model::*;
#[allow(unused_imports)]
use crate::progress::channel::*;
use crate::util::*;
use std::collections::VecDeque;
use std::sync::Arc;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

broadcast use {vstd::set_lib::range_set_properties, vstd::set::lemma_set_contains_len, vstd::set::lemma_set_insert_len, vstd::set::lemma_set_remove_len, vstd::set::lemma_set_empty_len};

/// The namespace of a channel's invariant.
pub open spec const CHAN_NS: int = 0x6368;

/// The number of threads in each model: any number (see
/// `chan_model::Model::pool_nonempty`).
pub uninterp spec fn model_threads() -> nat;

/// How many times a call snoozes before it registers and parks: what
/// `Backoff::is_completed` allows.
pub const SNOOZES: u8 = 11;

/// A waiter list as the model sees it.
pub ghost struct ListG {
    pub list: Set<nat>,
    pub next: nat,
}

/// One direction's constants.
pub ghost struct DirK {
    pub model: Loc,
    pub empty: AtomicCellId,
    pub alive: AtomicCellId,
    pub handles: Loc,
    pub ids: Loc,
    pub list: Loc,
}

/// One handle on the side that direction's model counts in `alive`.
pub type HandleTok = GhostPointsTo<nat, ()>;

/// One direction's shared ghost state and permissions.
pub tracked struct DirG {
    pub model: Model,
    /// The waiter list's `empty` flag.
    pub empty: PermissionBool,
    /// The count of handles on the giving side.
    pub alive: PermissionUsize,
    pub handles: GhostMapAuth<nat, ()>,
    pub ghost hnext: nat,
    /// Every waiter's `notified` flag, by ticket.
    pub flags: Map<nat, PermissionBool>,
    /// Which atomic is the flag of which ticket.
    pub ids: GhostPersistentSubmap<nat, AtomicCellId>,
    /// The list; the lock holds the other half.
    pub list: GhostVarAuth<ListG>,
}

pub open spec fn dir_inv(k: DirK, g: DirG) -> bool {
    let s = g.model@;
    &&& g.model.wf()
    &&& g.model.loc() == k.model
    &&& g.model.n() == model_threads()
    &&& g.empty.id() == k.empty
    &&& g.empty.value() ==> s.list.is_empty()
    &&& g.alive.id() == k.alive
    &&& g.alive.value() == s.alive
    &&& g.handles.id() == k.handles
    &&& g.handles@.dom().len() == s.alive
    &&& forall|h: nat| #[trigger] g.handles@.contains_key(h) ==> h < g.hnext
    &&& g.ids.id() == k.ids
    &&& g.ids@.dom() =~= Set::range(0, s.next_tk)
    &&& g.flags.dom() =~= Set::range(0, s.next_tk)
    &&& forall|tk: nat| tk < s.next_tk ==> {
        &&& (#[trigger] g.flags[tk]).id() == g.ids@[tk]
        &&& g.flags[tk].value() == s.notified.contains(tk)
    }
    &&& g.list.id() == k.list
    &&& g.list@ == (ListG { list: s.list, next: s.next_tk })
}

pub ghost struct ChanK {
    pub r: DirK,
    pub s: DirK,
    pub q: Loc,
    pub cap: nat,
}

impl ChanK {
    pub open spec fn dir(self, d: bool) -> DirK {
        if d {
            self.r
        } else {
            self.s
        }
    }
}

pub tracked struct ChanG<T> {
    pub d: Map<bool, DirG>,
    pub q: QueueView<T>,
}

pub struct ChanPred;

impl<T> InvariantPredicate<ChanK, ChanG<T>> for ChanPred {
    open spec fn inv(k: ChanK, g: ChanG<T>) -> bool {
        &&& g.d.dom() =~= set![true, false]
        &&& dir_inv(k.r, g.d[true])
        &&& dir_inv(k.s, g.d[false])
        &&& g.q.id() == k.q
        &&& g.q@.len() <= k.cap
        &&& g.d[true].model@.c == g.q@.len()
        &&& g.d[false].model@.c == k.cap - g.q@.len()
        &&& g.d[true].model@.cap == k.cap
        &&& g.d[false].model@.cap == k.cap
    }
}

/// A thread waiting on a list.
pub struct Waiter {
    /// Its ticket.
    pub id: u64,
    pub thread: Unparker,
    pub notified: PAtomicBool,
    pub pers: Tracked<GhostPersistentPointsTo<nat, AtomicCellId>>,
}

impl Waiter {
    pub open spec fn wf(&self, k: DirK) -> bool {
        &&& self.pers@.id() == k.ids
        &&& self.pers@.key() == self.id as nat
        &&& self.pers@.value() == self.notified.id()
    }
}

/// What a waiter list's lock protects.
pub struct WaitList {
    pub q: VecDeque<Arc<Waiter>>,
    /// The next ticket.
    pub next: u64,
    pub ids: Tracked<GhostMapAuth<nat, AtomicCellId>>,
    pub half: Tracked<GhostVar<ListG>>,
}

impl WaitList {
    pub open spec fn wf(&self, k: DirK) -> bool {
        &&& self.ids@.id() == k.ids
        &&& self.ids@@.dom() =~= Set::range(0, self.next as nat)
        &&& self.half@.id() == k.list
        &&& self.half@@.next == self.next as nat
        &&& list_ok(self.q@, k, self.next, self.half@@.list)
    }
}

/// The waiters in `q` are exactly the tickets in `list`, each once.
pub open spec fn list_ok(q: Seq<Arc<Waiter>>, k: DirK, next: u64, list: Set<nat>) -> bool {
    &&& forall|i: int| 0 <= i < q.len() ==> (#[trigger] q[i]).wf(k) && q[i].id < next
    &&& forall|i: int, j: int| 0 <= i < j < q.len() ==> (#[trigger] q[i]).id != (#[trigger] q[j]).id
    &&& forall|i: int| 0 <= i < q.len() ==> list.contains((#[trigger] q[i]).id as nat)
    &&& forall|tk: nat| #[trigger] list.contains(tk) ==> exists|i: int| 0 <= i < q.len() && (#[trigger] q[i]).id as nat == tk
}

proof fn lemma_list_push(q: Seq<Arc<Waiter>>, k: DirK, next: u64, list: Set<nat>, w: Arc<Waiter>)
    requires
        list_ok(q, k, next, list),
        w.wf(k),
        w.id == next,
        next < u64::MAX,
    ensures
        list_ok(q.push(w), k, (next + 1) as u64, list.insert(next as nat)),
{
    let q1 = q.push(w);
    let list1 = list.insert(next as nat);
    assert forall|tk: nat| #[trigger] list1.contains(tk) implies exists|i: int| 0 <= i < q1.len() && (#[trigger] q1[i]).id as nat == tk by {
        if tk == next as nat {
            assert(q1[q.len() as int].id as nat == tk);
        } else {
            let i = choose|i: int| 0 <= i < q.len() && (#[trigger] q[i]).id as nat == tk;
            assert(q1[i] == q[i]);
        }
    }
    assert forall|i: int, j: int| 0 <= i < j < q1.len() implies (#[trigger] q1[i]).id != (#[trigger] q1[j]).id by {
        assert(q1[i] == q[i]);
        if j < q.len() {
            assert(q1[j] == q[j]);
        }
    }
    assert forall|i: int| 0 <= i < q1.len() implies (#[trigger] q1[i]).wf(k) && q1[i].id < next + 1 && list1.contains(q1[i].id as nat) by {
        if i < q.len() {
            assert(q1[i] == q[i]);
        }
    }
}

proof fn lemma_list_remove(q: Seq<Arc<Waiter>>, k: DirK, next: u64, list: Set<nat>, i: int)
    requires
        list_ok(q, k, next, list),
        0 <= i < q.len(),
    ensures
        list_ok(q.remove(i), k, next, list.remove(q[i].id as nat)),
        list.contains(q[i].id as nat),
{
    let q1 = q.remove(i);
    let list1 = list.remove(q[i].id as nat);
    assert forall|j: int| 0 <= j < q1.len() implies (#[trigger] q1[j]).wf(k) && q1[j].id < next && list1.contains(q1[j].id as nat) by {
        let j0 = if j < i { j } else { j + 1 };
        assert(q1[j] == q[j0]);
        assert(q[j0].id != q[i].id);
    }
    assert forall|a: int, b: int| 0 <= a < b < q1.len() implies (#[trigger] q1[a]).id != (#[trigger] q1[b]).id by {
        let a0 = if a < i { a } else { a + 1 };
        let b0 = if b < i { b } else { b + 1 };
        assert(q1[a] == q[a0]);
        assert(q1[b] == q[b0]);
    }
    assert forall|x: nat| #[trigger] list1.contains(x) implies exists|j: int| 0 <= j < q1.len() && (#[trigger] q1[j]).id as nat == x by {
        let j = choose|j: int| 0 <= j < q.len() && (#[trigger] q[j]).id as nat == x;
        assert(j != i);
        let j1 = if j < i { j } else { j - 1 };
        assert(q1[j1] == q[j]);
    }
}

/// A ticket no waiter in `q` holds is not on the list.
proof fn lemma_list_absent(q: Seq<Arc<Waiter>>, k: DirK, next: u64, list: Set<nat>, id: u64)
    requires
        list_ok(q, k, next, list),
        forall|j: int| 0 <= j < q.len() ==> (#[trigger] q[j]).id != id,
    ensures
        !list.contains(id as nat),
        list.remove(id as nat) =~= list,
{
    if list.contains(id as nat) {
        let j = choose|j: int| 0 <= j < q.len() && (#[trigger] q[j]).id as nat == id as nat;
        assert(q[j].id == id);
    }
}

proof fn lemma_list_empty(q: Seq<Arc<Waiter>>, k: DirK, next: u64, list: Set<nat>)
    requires
        list_ok(q, k, next, list),
        q.len() == 0,
    ensures
        list.is_empty(),
{
    assert forall|x: nat| !list.contains(x) by {
        if list.contains(x) {
            let j = choose|j: int| 0 <= j < q.len() && (#[trigger] q[j]).id as nat == x;
        }
    }
    assert(list =~= Set::empty());
}

pub struct ListPred;

impl LockInv<DirK, WaitList> for ListPred {
    open spec fn inv(k: DirK, l: WaitList) -> bool {
        l.wf(k)
    }
}

/// Threads parked until some condition may have changed.
///
/// A waiter adds itself to the list and clears `empty`, then re-checks its
/// condition, then parks; a notifier changes the state, then reads `empty`.
/// A notified waiter is taken off the list at once, so notifiers stop
/// paying for it while it wakes up.
pub struct Waiters {
    pub empty: PAtomicBool,
    pub lock: Lock<DirK, WaitList, ListPred>,
}

impl Waiters {
    pub open spec fn wf(&self, k: DirK) -> bool {
        &&& self.empty.id() == k.empty
        &&& self.lock.k() == k
    }
}

pub struct Chan<T> {
    pub queue: ArrayQueue<T>,
    senders: PAtomicUsize,
    receivers: PAtomicUsize,
    /// Receivers waiting for a message.
    recv_waiters: Waiters,
    /// Senders waiting for space.
    send_waiters: Waiters,
    inv: Tracked<AtomicInvariant<ChanK, ChanG<T>, ChanPred>>,
}

/// The token is for a thread of direction `k`'s model, in phase `p`.
pub open spec fn tok_at(tok: ThreadTok, k: DirK, p: Ph) -> bool {
    tok.id() == k.model && tok.value().ph == p
}

/// A step of a take, on the model: `chan_core::theorem_next_refines`,
/// applied.
proof fn take_step(tracked model: &mut Model, tracked tok: &mut ThreadTok, pc: Pc, cfg: Cfg, flag: bool, aux: bool, tk: nat, left: nat, m: St)
    requires
        old(model).wf(),
        old(tok).id() == old(model).loc(),
        old(tok).value().ph == abs(pc, tk, left),
        reads(old(model)@, pc, tk, flag),
        writes(old(model)@, pc, if pc is Reg { old(tok).key() } else { tk }, flag, m),
        cfg.nonblocking ==> old(tok).value().timed,
        pc is Park && aux ==> old(tok).value().timed,
        pc is Take && !flag ==> (aux <==> left > 0),
        pc is Reg || pc is Ready1 || pc is Ready2 || pc is Remove || pc is Park ==> left == 0,
    ensures
        final(model).wf(),
        final(model).loc() == old(model).loc(),
        final(model).n() == old(model).n(),
        final(model)@ == go(m, old(tok).key(), abs(next_spec(pc, cfg, flag, aux), tk_next(old(model)@, pc, tk), left_next(pc, flag, aux, left))),
        final(tok).id() == old(tok).id(),
        final(tok).key() == old(tok).key(),
        final(tok).value().ph == abs(next_spec(pc, cfg, flag, aux), tk_next(old(model)@, pc, tk), left_next(pc, flag, aux, left)),
        final(tok).value().timed == old(tok).value().timed,
{
    let s = model@;
    let t = tok.key();
    model.agree(tok);
    theorem_next_refines(s, t, pc, cfg, flag, aux, tk, left, m);
    model.step(tok, go(m, t, abs(next_spec(pc, cfg, flag, aux), tk_next(s, pc, tk), left_next(pc, flag, aux, left))));
}

impl<T> Chan<T> {
    pub closed spec fn k(&self) -> ChanK {
        self.inv@.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.queue.wf()
        &&& self.queue.qid() == self.k().q
        &&& self.queue.capacity_spec() == self.k().cap
        &&& self.queue.ns() == QUEUE_NS
        &&& self.inv@.namespace() == CHAN_NS
        &&& self.senders.id() == self.k().r.alive
        &&& self.receivers.id() == self.k().s.alive
        &&& self.recv_waiters.wf(self.k().r)
        &&& self.send_waiters.wf(self.k().s)
    }

    /// The takers' waiter list in direction `d`.
    #[inline(always)]
    fn waiters(&self, d: bool) -> (r: &Waiters)
        requires
            self.wf(),
        ensures
            r.wf(self.k().dir(d)),
    {
        if d {
            &self.recv_waiters
        } else {
            &self.send_waiters
        }
    }

    /// The count of handles on the giving side of direction `d`.
    #[inline(always)]
    fn count(&self, d: bool) -> (r: &PAtomicUsize)
        requires
            self.wf(),
        ensures
            r.id() == self.k().dir(d).alive,
    {
        if d {
            &self.senders
        } else {
            &self.receivers
        }
    }

    /// `Pc::Gone` and `Pc::Ready1`: reads whether the other side is gone.
    #[inline(always)]
    fn read_gone(&self, d: bool, pc: Pc, cfg: Cfg, Tracked(tok): Tracked<&mut ThreadTok>, Ghost(tk): Ghost<nat>, Ghost(left): Ghost<nat>) -> (flag: bool)
        requires
            self.wf(),
            pc is Gone || pc is Ready1,
            tok_at(*old(tok), self.k().dir(d), abs(pc, tk, left)),
            cfg.nonblocking ==> old(tok).value().timed,
            pc is Ready1 ==> left == 0,
        ensures
            tok_at(*final(tok), self.k().dir(d), abs(next_spec(pc, cfg, flag, false), tk, left)),
            final(tok).value().timed == old(tok).value().timed,
    {
        let flag;
        let count = self.count(d);
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            let v = count.load(Tracked(&dg.alive));
            flag = v == 0;
            proof {
                let s = dg.model@;
                take_step(&mut dg.model, tok, pc, cfg, flag, false, tk, left, s);
                g.d.tracked_insert(d, dg);
            }
        });
        flag
    }

    /// `Pc::Take` for a receiver: the pop. If it takes a message, that is
    /// also a give in the senders' direction (a slot is free), at the same
    /// instant.
    #[inline(always)]
    fn pop_step(&self, cfg: Cfg, aux: bool, Ghost(gone): Ghost<bool>, Ghost(left): Ghost<nat>, Tracked(tok): Tracked<&mut ThreadTok>, Tracked(gtok): Tracked<&mut ThreadTok>, Tracked(h): Tracked<&HandleTok>) -> (r: Option<T>)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().r, Ph::TTake { gone, left }),
            tok_at(*old(gtok), self.k().s, Ph::Idle),
            h.id() == self.k().s.handles,
            cfg.nonblocking ==> old(tok).value().timed,
            aux <==> left > 0,
        ensures
            tok_at(*final(tok), self.k().r, abs(next_spec(Pc::Take { gone }, cfg, r is Some, aux), 0, left_next(Pc::Take { gone }, r is Some, aux, left))),
            final(tok).value().timed == old(tok).value().timed,
            tok_at(*final(gtok), self.k().s, if r is Some { Ph::GNotify } else { Ph::Idle }),
    {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        let ghost mut flag = false;
        let ghost pc = Pc::Take { gone };
        let r = self.queue.pop() atomically |update| {
            open_atomic_invariant!(credit => self.inv.borrow() => g => {
                let tracked ChanG { d: mut dm, q } = g;
                flag = q@.len() > 0;
                let tracked Commit(y) = update(q);
                let tracked mut dt = dm.tracked_remove(true);
                let tracked mut dv = dm.tracked_remove(false);
                let s = dt.model@;
                let m = if flag { St { c: (s.c - 1) as nat, ..s } } else { s };
                take_step(&mut dt.model, tok, pc, cfg, flag, aux, 0, left, m);
                if flag {
                    Self::give_step(&mut dv, gtok, h, self.k().cap);
                }
                dm.tracked_insert(true, dt);
                dm.tracked_insert(false, dv);
                g = ChanG { d: dm, q: y };
            });
        };
        r
    }

    /// `Pc::Take` for a sender: the push. If it takes a slot, that is also
    /// a give in the receivers' direction (a message is there).
    #[inline(always)]
    fn push_step(&self, value: T, cfg: Cfg, aux: bool, Ghost(gone): Ghost<bool>, Ghost(left): Ghost<nat>, Tracked(tok): Tracked<&mut ThreadTok>, Tracked(gtok): Tracked<&mut ThreadTok>, Tracked(h): Tracked<&HandleTok>) -> (r: Result<(), T>)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().s, Ph::TTake { gone, left }),
            tok_at(*old(gtok), self.k().r, Ph::Idle),
            h.id() == self.k().r.handles,
            cfg.nonblocking ==> old(tok).value().timed,
            aux <==> left > 0,
        ensures
            tok_at(*final(tok), self.k().s, abs(next_spec(Pc::Take { gone }, cfg, r is Ok, aux), 0, left_next(Pc::Take { gone }, r is Ok, aux, left))),
            final(tok).value().timed == old(tok).value().timed,
            tok_at(*final(gtok), self.k().r, if r is Ok { Ph::GNotify } else { Ph::Idle }),
    {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        let ghost mut flag = false;
        let ghost pc = Pc::Take { gone };
        let r = self.queue.push(value) atomically |update| {
            open_atomic_invariant!(credit => self.inv.borrow() => g => {
                let tracked ChanG { d: mut dm, q } = g;
                flag = q@.len() < self.k().cap;
                let tracked Commit(y) = update(q);
                let tracked mut dt = dm.tracked_remove(false);
                let tracked mut dv = dm.tracked_remove(true);
                let s = dt.model@;
                let m = if flag { St { c: (s.c - 1) as nat, ..s } } else { s };
                take_step(&mut dt.model, tok, pc, cfg, flag, aux, 0, left, m);
                if flag {
                    Self::give_step(&mut dv, gtok, h, self.k().cap);
                }
                dm.tracked_insert(false, dt);
                dm.tracked_insert(true, dv);
                g = ChanG { d: dm, q: y };
            });
        };
        r
    }

    /// A give, on the model: the holder of a handle adds one to `c` and
    /// owes the takers a `notify_one`.
    proof fn give_step(tracked dv: &mut DirG, tracked gtok: &mut ThreadTok, tracked h: &HandleTok, cap: nat)
        requires
            old(dv).model.wf(),
            old(gtok).id() == old(dv).model.loc(),
            old(gtok).value().ph == Ph::Idle,
            h.id() == old(dv).handles.id(),
            old(dv).handles@.dom().len() == old(dv).model@.alive,
            old(dv).model@.c < old(dv).model@.cap,
        ensures
            final(dv).model.wf(),
            final(dv).model.loc() == old(dv).model.loc(),
            final(dv).model.n() == old(dv).model.n(),
            final(dv).model@ == (St { c: old(dv).model@.c + 1, ..go(old(dv).model@, old(gtok).key(), Ph::GNotify) }),
            final(dv).empty == old(dv).empty,
            final(dv).alive == old(dv).alive,
            final(dv).handles == old(dv).handles,
            final(dv).hnext == old(dv).hnext,
            final(dv).flags == old(dv).flags,
            final(dv).ids == old(dv).ids,
            final(dv).list == old(dv).list,
            final(gtok).id() == old(gtok).id(),
            final(gtok).value().ph == Ph::GNotify,
    {
        let s = dv.model@;
        dv.model.agree(gtok);
        h.agree(&dv.handles);
        assert(dv.handles@.dom().contains(h.key()));
        assert(s.alive > 0);
        let s2 = St { c: s.c + 1, ..go(s, gtok.key(), Ph::GNotify) };
        dv.model.step(gtok, s2);
    }

    /// `Pc::Reg`: one critical section that adds this thread to the list.
    /// The model's step is at the store to `empty`: until then no notifier
    /// that skips the lock can know of the waiter.
    #[cold]
    fn register(&self, d: bool, cfg: Cfg, Tracked(tok): Tracked<&mut ThreadTok>) -> (me: Arc<Waiter>)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().dir(d), Ph::TReg),
            cfg.nonblocking ==> old(tok).value().timed,
        ensures
            me.wf(self.k().dir(d)),
            tok_at(*final(tok), self.k().dir(d), Ph::TReady1 { tk: me.id as nat }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost k = self.k().dir(d);
        let w = self.waiters(d);
        let (guard, mut l) = w.lock.lock();
        if l.next == u64::MAX {
            exhausted();
        }
        let id = l.next;
        let (notified, Tracked(perm)) = PAtomicBool::new(false);
        let tracked pers;
        let tracked pers2;
        proof {
            let tracked p = l.ids.borrow_mut().insert(id as nat, notified.id());
            let tracked pp = p.persist();
            pers2 = pp.duplicate();
            pers = pp;
        }
        let me = Arc::new(Waiter { id, thread: Unparker::current(), notified, pers: Tracked(pers) });
        let ghost q0 = l.q@;
        let ghost list0 = l.half@@.list;
        l.q.push_back(arc_clone(&me));
        l.next = id + 1;
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            w.empty.store(Tracked(&mut dg.empty), false);
            proof {
                dg.list.agree(l.half.borrow());
                dg.model.lemma_inv();
                dg.model.agree(tok);
                let s = dg.model@;
                let t = tok.key();
                let m = St { list: s.list.insert(s.next_tk), owner: s.owner.insert(s.next_tk, t), next_tk: s.next_tk + 1, ..s };
                take_step(&mut dg.model, tok, Pc::Reg, cfg, false, false, 0, 0, m);
                dg.flags.tracked_insert(id as nat, perm);
                dg.ids.combine_points_to(pers2);
                dg.list.update(l.half.borrow_mut(), ListG { list: s.list.insert(id as nat), next: id as nat + 1 });
                g.d.tracked_insert(d, dg);
            }
        });
        proof {
            lemma_list_push(q0, k, id, list0, me);
            assert(l.q@ =~= q0.push(me));
        }
        guard.unlock(l);
        me
    }

    /// `Pc::Ready2`: the re-check of the queue. `false` means there was
    /// nothing to take at one instant after this thread went on the list.
    #[cold]
    fn recheck(&self, d: bool, cfg: Cfg, Tracked(tok): Tracked<&mut ThreadTok>, Ghost(tk): Ghost<nat>) -> (flag: bool)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().dir(d), Ph::TReady2 { tk }),
            cfg.nonblocking ==> old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.k().dir(d), abs(next_spec(Pc::Ready2, cfg, flag, false), tk, 0)),
            final(tok).value().timed == old(tok).value().timed,
    {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        let nothing = if d {
            self.queue.confirm_empty() atomically |update| {
                open_atomic_invariant!(credit => self.inv.borrow() => g => {
                    let tracked ChanG { d: mut dm, q } = g;
                    let tracked Commit(ye): Commit<(QueueView<T>, Ghost<bool>)> = update(q);
                    let tracked (y, e) = ye;
                    let tracked mut dg = dm.tracked_remove(d);
                    let s = dg.model@;
                    take_step(&mut dg.model, tok, Pc::Ready2, cfg, !e@, false, tk, 0, s);
                    dm.tracked_insert(d, dg);
                    g = ChanG { d: dm, q: y };
                });
            }
        } else {
            self.queue.confirm_full() atomically |update| {
                open_atomic_invariant!(credit => self.inv.borrow() => g => {
                    let tracked ChanG { d: mut dm, q } = g;
                    let tracked Commit(ye): Commit<(QueueView<T>, Ghost<bool>)> = update(q);
                    let tracked (y, e) = ye;
                    let tracked mut dg = dm.tracked_remove(d);
                    let s = dg.model@;
                    take_step(&mut dg.model, tok, Pc::Ready2, cfg, !e@, false, tk, 0, s);
                    dm.tracked_insert(d, dg);
                    g = ChanG { d: dm, q: y };
                });
            }
        };
        !nothing
    }

    /// `Pc::Remove` and `Pc::Timeout`: one critical section that takes `me`
    /// off the list. Returns false if a notifier already did.
    fn remove(&self, d: bool, pc: Pc, cfg: Cfg, me: &Arc<Waiter>, Tracked(tok): Tracked<&mut ThreadTok>) -> (found: bool)
        requires
            self.wf(),
            pc is Remove || pc is Timeout,
            me.wf(self.k().dir(d)),
            tok_at(*old(tok), self.k().dir(d), abs(pc, me.id as nat, 0)),
            cfg.nonblocking ==> old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.k().dir(d), abs(next_spec(pc, cfg, found, false), me.id as nat, 0)),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost k = self.k().dir(d);
        let ghost tk = me.id as nat;
        let w = self.waiters(d);
        let (guard, mut l) = w.lock.lock();
        let ghost q0 = l.q@;
        let n = l.q.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == l.q@.len(),
                l.q@ == q0,
                i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] l.q@[j]).id != me.id,
            ensures
                i <= n,
                i < n ==> l.q@[i as int].id == me.id,
                forall|j: int| 0 <= j < i ==> (#[trigger] l.q@[j]).id != me.id,
            decreases n - i,
        {
            if l.q[i].id == me.id {
                break;
            }
            i += 1;
        }
        let found = i < n;
        if found {
            l.q.remove(i);
        }
        let empty = l.q.len() == 0;
        let ghost list0 = l.half@@.list;
        let ghost list1 = list0.remove(tk);
        proof {
            // `me` is on the model's list exactly if it was found.
            if found {
                lemma_list_remove(q0, k, l.next, list0, i as int);
                assert(l.q@ =~= q0.remove(i as int));
            } else {
                lemma_list_absent(q0, k, l.next, list0, me.id);
            }
            assert(list_ok(l.q@, k, l.next, list1));
            if empty {
                lemma_list_empty(l.q@, k, l.next, list1);
            }
        }
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            w.empty.store(Tracked(&mut dg.empty), empty);
            proof {
                dg.list.agree(l.half.borrow());
                let s = dg.model@;
                let m = St { list: s.list.remove(tk), ..s };
                take_step(&mut dg.model, tok, pc, cfg, found, false, tk, 0, m);
                dg.list.update(l.half.borrow_mut(), ListG { list: s.list.remove(tk), next: s.next_tk });
                g.d.tracked_insert(d, dg);
            }
        });
        guard.unlock(l);
        found
    }

    /// `Pc::Park`: reads the waiter's flag and, if it is clear, sleeps
    /// until unparked or until the deadline. Returns the flag and whether
    /// the deadline has passed.
    #[cold]
    fn park(&self, d: bool, cfg: Cfg, me: &Arc<Waiter>, deadline: &Deadline, Tracked(tok): Tracked<&mut ThreadTok>) -> (r: (bool, bool))
        requires
            self.wf(),
            me.wf(self.k().dir(d)),
            tok_at(*old(tok), self.k().dir(d), Ph::TPark { tk: me.id as nat }),
            cfg.nonblocking ==> old(tok).value().timed,
            has_deadline(*deadline) ==> old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.k().dir(d), abs(next_spec(Pc::Park, cfg, r.0, r.1), me.id as nat, 0)),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost tk = me.id as nat;
        let (late, left) = time_left(deadline);
        let flag;
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            proof {
                dg.model.lemma_inv();
                dg.model.agree(tok);
                assert(ticket(ph(dg.model@, tok.key())) == Some(tk));
                dg.ids.intersection_agrees_points_to(me.pers.borrow());
            }
            flag = me.notified.load(Tracked(dg.flags.tracked_borrow(tk)));
            proof {
                let s = dg.model@;
                take_step(&mut dg.model, tok, Pc::Park, cfg, flag, late, tk, 0, s);
                g.d.tracked_insert(d, dg);
            }
        });
        if !flag && !late {
            park_for(left);
        }
        (flag, late)
    }

    /// A notifier's load of `empty` (`Pc::Pass`, `Npc::Load`): if it reads
    /// "empty" the list is empty and the thread is done; otherwise it goes
    /// on to the critical section, in phase `pop`.
    #[inline(always)]
    fn load_empty(&self, d: bool, Tracked(tok): Tracked<&mut ThreadTok>, Ghost(pop): Ghost<Ph>) -> (flag: bool)
        requires
            self.wf(),
            old(tok).id() == self.k().dir(d).model,
            match old(tok).value().ph {
                Ph::TPass => pop == Ph::TPassPop,
                Ph::GNotify => pop == Ph::GNotifyPop,
                Ph::GNotifyAll => pop == Ph::GNotifyAllPop,
                _ => false,
            },
        ensures
            tok_at(*final(tok), self.k().dir(d), if flag { Ph::Idle } else { pop }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let flag;
        let w = self.waiters(d);
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            flag = w.empty.load(Tracked(&dg.empty));
            proof {
                dg.model.agree(tok);
                let s = dg.model@;
                dg.model.step(tok, go(s, tok.key(), if flag { Ph::Idle } else { pop }));
                g.d.tracked_insert(d, dg);
            }
        });
        flag
    }

    /// `Npc::Pop` and `Pc::PassPop`: the critical section that takes the
    /// first waiter (or, for `all`, every waiter) off the list and sets its
    /// flag. Each store to a flag is one step of the model; the last store,
    /// to `empty`, is the step that leaves if nobody was woken by this
    /// thread's last step.
    #[cold]
    fn notify(&self, d: bool, all: bool, Tracked(tok): Tracked<&mut ThreadTok>, Ghost(p): Ghost<Ph>)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().dir(d), p),
            all ==> p == Ph::GNotifyAllPop,
            !all ==> p == Ph::TPassPop || p == Ph::GNotifyPop,
        ensures
            tok_at(*final(tok), self.k().dir(d), Ph::Idle),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost k = self.k().dir(d);
        let ghost timed = tok.value().timed;
        let w = self.waiters(d);
        let (guard, mut l) = w.lock.lock();
        let mut more = true;
        let mut woke = false;
        while more
            invariant
                self.wf(),
                k == self.k().dir(d),
                w.wf(k),
                l.wf(k),
                tok_at(*tok, k, if woke && !all { Ph::Idle } else { p }),
                tok.value().timed == timed,
                all ==> p == Ph::GNotifyAllPop,
                !all ==> p == Ph::TPassPop || p == Ph::GNotifyPop,
                !more && !(woke && !all) ==> l.q@.len() == 0,
                more ==> !(woke && !all),
            decreases l.q@.len() + if more { 1nat } else { 0nat },
        {
            let ghost q0 = l.q@;
            match l.q.pop_front() {
                None => {
                    more = false;
                },
                Some(x) => {
                    let ghost xk = x.id as nat;
                    let ghost list0 = l.half@@.list;
                    proof {
                        assert(x == q0[0]);
                        lemma_list_remove(q0, k, l.next, list0, 0);
                        assert(l.q@ =~= q0.remove(0));
                    }
                    open_atomic_invariant!(self.inv.borrow() => g => {
                        let tracked mut dg = g.d.tracked_remove(d);
                        proof {
                            dg.list.agree(l.half.borrow());
                            dg.ids.intersection_agrees_points_to(x.pers.borrow());
                        }
                        let tracked mut fp = dg.flags.tracked_remove(xk);
                        x.notified.store(Tracked(&mut fp), true);
                        proof {
                            dg.flags.tracked_insert(xk, fp);
                            dg.model.agree(tok);
                            let s = dg.model@;
                            let t = tok.key();
                            let p2 = if all { p } else { Ph::Idle };
                            let s2 = St { list: s.list.remove(xk), notified: s.notified.insert(xk), ..go(s, t, p2) };
                            assert(pops(s, t, xk, p2, s2));
                            dg.model.step(tok, s2);
                            dg.list.update(l.half.borrow_mut(), ListG { list: s.list.remove(xk), next: s.next_tk });
                            g.d.tracked_insert(d, dg);
                        }
                    });
                    x.thread.unpark();
                    woke = true;
                    if !all {
                        more = false;
                    }
                },
            }
        }
        let empty = l.q.len() == 0;
        proof {
            if empty {
                lemma_list_empty(l.q@, k, l.next, l.half@@.list);
            }
        }
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            w.empty.store(Tracked(&mut dg.empty), empty);
            proof {
                dg.list.agree(l.half.borrow());
                let s = dg.model@;
                if !(woke && !all) {
                    // Nobody left to wake: the model's step out of the
                    // critical section.
                    dg.model.agree(tok);
                    dg.model.step(tok, go(s, tok.key(), Ph::Idle));
                }
                g.d.tracked_insert(d, dg);
            }
        });
        guard.unlock(l);
    }

    /// `notify_one`, owed after a give.
    #[inline(always)]
    fn notify_one(&self, d: bool, Tracked(tok): Tracked<&mut ThreadTok>)
        requires
            self.wf(),
            tok_at(*old(tok), self.k().dir(d), Ph::GNotify),
        ensures
            tok_at(*final(tok), self.k().dir(d), Ph::Idle),
    {
        let e = self.load_empty(d, Tracked(&mut *tok), Ghost(Ph::GNotifyPop));
        match notify_next(Npc::Load, false, e) {
            Npc::Pop => self.notify(d, false, Tracked(&mut *tok), Ghost(Ph::GNotifyPop)),
            _ => {},
        }
    }

    /// A call starts acting as an idle thread of direction `d`'s model.
    #[inline(always)]
    fn enter(&self, d: bool) -> (r: Tracked<ThreadTok>)
        requires
            self.wf(),
        ensures
            tok_at(r@, self.k().dir(d), Ph::Idle),
    {
        let tracked tok;
        open_atomic_invariant!(self.inv.borrow() => g => {
            proof {
                let tracked mut dg = g.d.tracked_remove(d);
                tok = dg.model.enter();
                g.d.tracked_insert(d, dg);
            }
        });
        Tracked(tok)
    }

    /// A call is done with its thread of direction `d`'s model.
    #[inline(always)]
    fn leave(&self, d: bool, Tracked(tok): Tracked<ThreadTok>)
        requires
            self.wf(),
            tok_at(tok, self.k().dir(d), Ph::Idle),
    {
        open_atomic_invariant!(self.inv.borrow() => g => {
            proof {
                let tracked mut dg = g.d.tracked_remove(d);
                dg.model.leave(tok);
                g.d.tracked_insert(d, dg);
            }
        });
    }

    /// A take starts in direction `d`: one thread of that model starts a
    /// take, and one of the other model stands by for the give.
    #[inline(always)]
    fn begin(&self, d: bool, Ghost(timed): Ghost<bool>, Ghost(left): Ghost<nat>) -> (r: (Tracked<ThreadTok>, Tracked<ThreadTok>))
        requires
            self.wf(),
        ensures
            tok_at(r.0@, self.k().dir(d), Ph::TGone { left }),
            r.0@.value().timed == timed,
            tok_at(r.1@, self.k().dir(!d), Ph::Idle),
    {
        let tracked tok;
        open_atomic_invariant!(self.inv.borrow() => g => {
            proof {
                let tracked mut dg = g.d.tracked_remove(d);
                let tracked mut t0 = dg.model.enter();
                dg.model.agree(&t0);
                let s = dg.model@;
                let s2 = St { th: s.th.update(t0.key() as int, Th { ph: Ph::TGone { left }, timed }), ..s };
                dg.model.step(&mut t0, s2);
                g.d.tracked_insert(d, dg);
                tok = t0;
            }
        });
        let gtok = self.enter(!d);
        (Tracked(tok), gtok)
    }

    /// A take from its first failed attempt on: the part that snoozes,
    /// registers, parks and times out. The loop is an interpreter for
    /// `chan_core::next`: each arm makes the one access to shared state its
    /// `Pc` names and reports what it read, and `next` decides everything
    /// else. For a receiver (`d`) the message comes back in the slot; a
    /// sender passes its message in and gets it back if it gives up.
    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn slow(&self, d: bool, cfg: Cfg, deadline: Deadline, slot: Option<T>, Tracked(tok): Tracked<ThreadTok>, Tracked(gtok): Tracked<ThreadTok>, Tracked(h): Tracked<&HandleTok>) -> (r: (Option<T>, End))
        requires
            self.wf(),
            !cfg.nonblocking,
            tok_at(tok, self.k().dir(d), Ph::TGone { left: (SNOOZES - 1) as nat }),
            has_deadline(deadline) ==> tok.value().timed,
            tok_at(gtok, self.k().dir(!d), Ph::Idle),
            h.id() == self.k().dir(!d).handles,
            d == (slot is None),
        ensures
            r.1 is Taken <==> (d == (r.0 is Some)),
    {
        let ghost kd = self.k().dir(d);
        let ghost timed = tok.value().timed;
        let tracked mut tok = tok;
        let tracked mut gtok = gtok;
        let mut slot = slot;
        let mut pc = Pc::Gone;
        let mut left: u8 = SNOOZES - 1;
        let mut me: Option<Arc<Waiter>> = None;
        let backoff = Backoff::new();
        backoff.snooze();
        loop
            invariant
                self.wf(),
                kd == self.k().dir(d),
                !cfg.nonblocking,
                tok_at(tok, kd, abs(pc, if me is Some { me->0.id as nat } else { 0 }, left as nat)),
                tok.value().timed == timed,
                has_deadline(deadline) ==> timed,
                tok_at(gtok, self.k().dir(!d), Ph::Idle),
                h.id() == self.k().dir(!d).handles,
                pc is Reg || pc is Ready1 || pc is Ready2 || pc is Remove || pc is Park ==> left == 0,
                pc is Ready1 || pc is Ready2 || pc is Remove || pc is Park || pc is Timeout ==> me is Some && me->0.wf(kd),
                (pc == Pc::Done(End::Taken)) == (d == (slot is Some)),
        {
            let ghost tk: nat = if me is Some { me->0.id as nat } else { 0 };
            match pc {
                Pc::Gone => {
                    let f = self.read_gone(d, pc, cfg, Tracked(&mut tok), Ghost(tk), Ghost(left as nat));
                    pc = next(pc, cfg, f, false);
                },
                Pc::Take { gone } => {
                    let aux = left > 0;
                    let ok;
                    if d {
                        slot = self.pop_step(cfg, aux, Ghost(gone), Ghost(left as nat), Tracked(&mut tok), Tracked(&mut gtok), Tracked(h));
                        ok = slot.is_some();
                    } else {
                        match self.push_step(slot.unwrap(), cfg, aux, Ghost(gone), Ghost(left as nat), Tracked(&mut tok), Tracked(&mut gtok), Tracked(h)) {
                            Ok(()) => {
                                slot = None;
                                ok = true;
                            },
                            Err(v) => {
                                slot = Some(v);
                                ok = false;
                            },
                        }
                    }
                    pc = next(pc, cfg, ok, aux);
                    if ok {
                        self.notify_one(!d, Tracked(&mut gtok));
                    } else if aux {
                        left = left - 1;
                        backoff.snooze();
                    }
                },
                Pc::Reg => {
                    me = Some(self.register(d, cfg, Tracked(&mut tok)));
                    pc = next(pc, cfg, false, false);
                },
                Pc::Ready1 => {
                    let f = self.read_gone(d, pc, cfg, Tracked(&mut tok), Ghost(tk), Ghost(0));
                    pc = next(pc, cfg, f, false);
                },
                Pc::Ready2 => {
                    let f = self.recheck(d, cfg, Tracked(&mut tok), Ghost(tk));
                    pc = next(pc, cfg, f, false);
                },
                Pc::Remove => {
                    match &me {
                        Some(m) => {
                            let f = self.remove(d, pc, cfg, m, Tracked(&mut tok));
                            pc = next(pc, cfg, f, false);
                        },
                        None => {},
                    }
                },
                Pc::Park => {
                    match &me {
                        Some(m) => {
                            let (notified, late) = self.park(d, cfg, m, &deadline, Tracked(&mut tok));
                            pc = next(pc, cfg, notified, late);
                        },
                        None => {},
                    }
                },
                Pc::Timeout => {
                    match &me {
                        Some(m) => {
                            let f = self.remove(d, pc, cfg, m, Tracked(&mut tok));
                            pc = next(pc, cfg, f, false);
                        },
                        None => {},
                    }
                },
                Pc::Pass => {
                    let f = self.load_empty(d, Tracked(&mut tok), Ghost(Ph::TPassPop));
                    pc = next(pc, cfg, f, false);
                },
                Pc::PassPop => {
                    self.notify(d, false, Tracked(&mut tok), Ghost(Ph::TPassPop));
                    pc = next(pc, cfg, false, false);
                },
                Pc::Done(e) => {
                    self.leave(d, Tracked(tok));
                    self.leave(!d, Tracked(gtok));
                    return (slot, e);
                },
            }
        }
    }

    /// One receive: `try_recv` when `nonblocking`. The sender count is
    /// read before the pop: if it is zero, every send has finished, so an
    /// empty queue afterwards means no more messages.
    #[inline]
    pub fn recv_as(&self, nonblocking: bool, deadline: Deadline, Tracked(h): Tracked<&HandleTok>) -> (r: Result<T, End>)
        requires
            self.wf(),
            h.id() == self.k().dir(false).handles,
    {
        let cfg = Cfg { nonblocking, stop_when_gone: false };
        let ghost timed = nonblocking || has_deadline(deadline);
        let (Tracked(tok), Tracked(gtok)) = self.begin(true, Ghost(timed), Ghost(SNOOZES as nat));
        let tracked mut tok = tok;
        let tracked mut gtok = gtok;
        let gone = self.read_gone(true, Pc::Gone, cfg, Tracked(&mut tok), Ghost(0), Ghost(SNOOZES as nat));
        let pc = next(Pc::Gone, cfg, gone, false);
        match self.pop_step(cfg, true, Ghost(gone), Ghost(SNOOZES as nat), Tracked(&mut tok), Tracked(&mut gtok), Tracked(h)) {
            Some(v) => {
                self.notify_one(false, Tracked(&mut gtok));
                self.leave(true, Tracked(tok));
                self.leave(false, Tracked(gtok));
                Ok(v)
            },
            None => match next(pc, cfg, false, true) {
                Pc::Done(e) => {
                    self.leave(true, Tracked(tok));
                    self.leave(false, Tracked(gtok));
                    Err(e)
                },
                _ => {
                    let (slot, e) = self.slow(true, cfg, deadline, None, Tracked(tok), Tracked(gtok), Tracked(h));
                    match e {
                        End::Taken => Ok(slot.unwrap()),
                        e => Err(e),
                    }
                },
            },
        }
    }

    /// One send: `try_send` when `nonblocking`. Gives the message back if
    /// it was not sent.
    #[inline]
    pub fn send_as(&self, msg: T, nonblocking: bool, deadline: Deadline, Tracked(h): Tracked<&HandleTok>) -> (r: Result<(), (T, End)>)
        requires
            self.wf(),
            h.id() == self.k().dir(true).handles,
    {
        let cfg = Cfg { nonblocking, stop_when_gone: true };
        let ghost timed = nonblocking || has_deadline(deadline);
        let (Tracked(tok), Tracked(gtok)) = self.begin(false, Ghost(timed), Ghost(SNOOZES as nat));
        let tracked mut tok = tok;
        let tracked mut gtok = gtok;
        let gone = self.read_gone(false, Pc::Gone, cfg, Tracked(&mut tok), Ghost(0), Ghost(SNOOZES as nat));
        let pc = next(Pc::Gone, cfg, gone, false);
        if let Pc::Done(e) = pc {
            self.leave(false, Tracked(tok));
            self.leave(true, Tracked(gtok));
            return Err((msg, e));
        }
        match self.push_step(msg, cfg, true, Ghost(gone), Ghost(SNOOZES as nat), Tracked(&mut tok), Tracked(&mut gtok), Tracked(h)) {
            Ok(()) => {
                self.notify_one(true, Tracked(&mut gtok));
                self.leave(false, Tracked(tok));
                self.leave(true, Tracked(gtok));
                Ok(())
            },
            Err(m) => match next(pc, cfg, false, true) {
                Pc::Done(e) => {
                    self.leave(false, Tracked(tok));
                    self.leave(true, Tracked(gtok));
                    Err((m, e))
                },
                _ => {
                    let (slot, e) = self.slow(false, cfg, deadline, Some(m), Tracked(tok), Tracked(gtok), Tracked(h));
                    match e {
                        End::Taken => Ok(()),
                        e => Err((slot.unwrap(), e)),
                    }
                },
            },
        }
    }

    /// Cloning a handle of the side direction `d` counts in `alive`. The
    /// count goes up by a compare-and-swap, which cannot overflow; a retry
    /// means another clone or drop on the same side got in first.
    #[verifier::exec_allows_no_decreases_clause]
    fn add_handle(&self, d: bool, Tracked(h): Tracked<&HandleTok>) -> (r: Tracked<HandleTok>)
        requires
            self.wf(),
            h.id() == self.k().dir(d).handles,
        ensures
            r@.id() == self.k().dir(d).handles,
    {
        let count = self.count(d);
        let Tracked(tok) = self.enter(d);
        let tracked mut tok = tok;
        let tracked mut new: Option<HandleTok> = None;
        let mut c: usize;
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked dg = g.d.tracked_remove(d);
            c = count.load(Tracked(&dg.alive));
            proof {
                g.d.tracked_insert(d, dg);
            }
        });
        loop
            invariant
                self.wf(),
                count.id() == self.k().dir(d).alive,
                tok_at(tok, self.k().dir(d), Ph::Idle),
                h.id() == self.k().dir(d).handles,
                new is None,
        {
            if c == usize::MAX {
                exhausted();
            }
            let r;
            open_atomic_invariant!(self.inv.borrow() => g => {
                let tracked mut dg = g.d.tracked_remove(d);
                r = count.compare_exchange(Tracked(&mut dg.alive), c, c + 1);
                proof {
                    if r is Ok {
                        dg.model.agree(&tok);
                        h.agree(&dg.handles);
                        assert(dg.handles@.dom().contains(h.key()));
                        let s = dg.model@;
                        dg.model.step(&mut tok, St { alive: s.alive + 1, ..s });
                        let hn = dg.hnext;
                        new = Some(dg.handles.insert(hn, ()));
                        dg.hnext = hn + 1;
                    }
                    g.d.tracked_insert(d, dg);
                }
            });
            match r {
                Ok(_) => {
                    self.leave(d, Tracked(tok));
                    return Tracked(new.tracked_unwrap());
                },
                Err(v) => {
                    c = v;
                },
            }
        }
    }

    /// Dropping a handle of the side direction `d` counts in `alive`; the
    /// last one wakes every taker.
    fn drop_handle(&self, d: bool, Tracked(h): Tracked<HandleTok>)
        requires
            self.wf(),
            h.id() == self.k().dir(d).handles,
    {
        let count = self.count(d);
        let Tracked(tok) = self.enter(d);
        let tracked mut tok = tok;
        let old;
        open_atomic_invariant!(self.inv.borrow() => g => {
            let tracked mut dg = g.d.tracked_remove(d);
            proof {
                h.agree(&dg.handles);
                assert(dg.handles@.dom().contains(h.key()));
            }
            old = count.fetch_sub(Tracked(&mut dg.alive), 1);
            proof {
                dg.model.agree(&tok);
                let s = dg.model@;
                let t = tok.key();
                dg.model.step(&mut tok, St { alive: (s.alive - 1) as nat, ..go(s, t, if s.alive == 1 { Ph::GNotifyAll } else { Ph::Idle }) });
                dg.handles.delete_points_to(h);
                g.d.tracked_insert(d, dg);
            }
        });
        if old == 1 {
            let e = self.load_empty(d, Tracked(&mut tok), Ghost(Ph::GNotifyAllPop));
            match notify_next(Npc::Load, true, e) {
                Npc::Pop => self.notify(d, true, Tracked(&mut tok), Ghost(Ph::GNotifyAllPop)),
                _ => {},
            }
        }
        self.leave(d, Tracked(tok));
    }

    /// One direction of a new channel, with one handle on its giving side.
    fn new_dir(Tracked(alive): Tracked<PermissionUsize>, Ghost(c): Ghost<nat>, Ghost(cap): Ghost<nat>) -> (r: (Waiters, Tracked<DirG>, Tracked<HandleTok>, Ghost<DirK>))
        requires
            alive.value() == 1,
            c <= cap,
        ensures
            r.0.wf(r.3@),
            dir_inv(r.3@, r.1@),
            r.1@.model@.c == c,
            r.1@.model@.cap == cap,
            r.3@.alive == alive.id(),
            r.2@.id() == r.3@.handles,
    {
        let (empty, Tracked(ep)) = PAtomicBool::new(true);
        let ghost k;
        let tracked g;
        let tracked h;
        let tracked ids_auth;
        let tracked list_var;
        proof {
            let n = model_threads();
            let s0 = St {
                c,
                cap,
                alive: 1,
                th: Seq::new(n, |i: int| Th { ph: Ph::Idle, timed: false }),
                list: Set::empty(),
                owner: Map::empty(),
                notified: Set::empty(),
                next_tk: 0,
            };
            let tracked model = Model::new(s0, n);
            let tracked (mut handles, _hs) = GhostMapAuth::<nat, ()>::new(Map::empty());
            h = handles.insert(0, ());
            let tracked (ia, isub) = GhostMapAuth::<nat, AtomicCellId>::new(Map::empty());
            let tracked ids = isub.persist();
            let tracked (la, lv) = GhostVarAuth::new(ListG { list: Set::empty(), next: 0 });
            k = DirK { model: model.loc(), empty: ep.id(), alive: alive.id(), handles: handles.id(), ids: ia.id(), list: la.id() };
            assert(handles@.dom() =~= set![0nat]);
            g = DirG { model, empty: ep, alive, handles, hnext: 1, flags: Map::tracked_empty(), ids, list: la };
            ids_auth = ia;
            list_var = lv;
        }
        let wl = WaitList { q: VecDeque::new(), next: 0, ids: Tracked(ids_auth), half: Tracked(list_var) };
        let lock = Lock::new(wl, Ghost(k));
        (Waiters { empty, lock }, Tracked(g), Tracked(h), Ghost(k))
    }
}

/// One end of a channel: a counted reference to it. `channel.rs` wraps
/// this as `Sender` and `Receiver`.
pub struct Handle<T> {
    pub chan: Arc<Chan<T>>,
    /// A receiver (or a sender).
    pub rx: Ghost<bool>,
    /// `Some` until the handle is dropped.
    pub tok: Tracked<Option<HandleTok>>,
}

impl<T> Handle<T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.chan.wf()
        &&& self.tok@ is Some
        &&& self.tok@->0.id() == self.chan.k().dir(!self.rx@).handles
    }

    /// Creates a channel that holds up to `cap` messages: its sender and
    /// its receiver.
    pub fn pair(cap: usize) -> (r: (Handle<T>, Handle<T>))
        requires
            0 < cap < 0x8000_0000,
        ensures
            r.0.wf(),
            !r.0.rx@,
            r.1.wf(),
            r.1.rx@,
    {
        let (queue, Tracked(qv)) = ArrayQueue::new_with_view(cap);
        let (senders, Tracked(sp)) = PAtomicUsize::new(1);
        let (receivers, Tracked(rp)) = PAtomicUsize::new(1);
        let (recv_waiters, Tracked(rg), Tracked(sh), Ghost(rk)) = Chan::<T>::new_dir(Tracked(sp), Ghost(0), Ghost(cap as nat));
        let (send_waiters, Tracked(sg), Tracked(rh), Ghost(sk)) = Chan::<T>::new_dir(Tracked(rp), Ghost(cap as nat), Ghost(cap as nat));
        let ghost k = ChanK { r: rk, s: sk, q: qv.id(), cap: cap as nat };
        let tracked inv;
        proof {
            let tracked mut d = Map::<bool, DirG>::tracked_empty();
            d.tracked_insert(true, rg);
            d.tracked_insert(false, sg);
            let tracked g = ChanG { d, q: qv };
            inv = AtomicInvariant::<_, _, ChanPred>::new(k, g, CHAN_NS);
        }
        let chan = Arc::new(Chan { queue, senders, receivers, recv_waiters, send_waiters, inv: Tracked(inv) });
        let tx = Handle { chan: arc_clone(&chan), rx: Ghost(false), tok: Tracked(Some(sh)) };
        let rx = Handle { chan, rx: Ghost(true), tok: Tracked(Some(rh)) };
        (tx, rx)
    }

    /// A receive on a receiver.
    #[inline]
    pub fn recv_as(&self, nonblocking: bool, deadline: Deadline) -> Result<T, End>
        requires
            self.wf(),
            self.rx@,
    {
        self.chan.recv_as(nonblocking, deadline, Tracked(self.tok.borrow().tracked_borrow()))
    }

    /// A send on a sender.
    #[inline]
    pub fn send_as(&self, msg: T, nonblocking: bool, deadline: Deadline) -> Result<(), (T, End)>
        requires
            self.wf(),
            !self.rx@,
    {
        self.chan.send_as(msg, nonblocking, deadline, Tracked(self.tok.borrow().tracked_borrow()))
    }

    /// Another handle on the same side.
    pub fn clone_handle(&self, rx: bool) -> (r: Self)
        requires
            self.wf(),
            rx == self.rx@,
        ensures
            r.wf(),
            r.rx@ == rx,
    {
        let Tracked(h) = self.chan.add_handle(!rx, Tracked(self.tok.borrow().tracked_borrow()));
        Handle { chan: arc_clone(&self.chan), rx: Ghost(rx), tok: Tracked(Some(h)) }
    }

    /// Gives the handle up. Called once, when the handle is dropped.
    pub fn disconnect(&mut self, rx: bool)
        requires
            old(self).wf(),
            rx == old(self).rx@,
    {
        let tracked h = self.tok.borrow_mut().tracked_take();
        self.chan.drop_handle(!rx, Tracked(h));
    }
}

} // verus!
