//! A bounded single-producer single-consumer ring buffer.
//!
//! The algorithm is the one in rtrb and most SPSC queues: the producer owns
//! `tail`, the consumer owns `head`, and each side caches the other side's
//! index so that most operations touch only their own cache line. Index
//! stores are Release and index loads Acquire, as in rtrb. When a side's
//! cached index says the queue is full (or empty), it re-reads the other
//! index with an Acquire load, and only if that still says full (or empty)
//! does it confirm with a read-modify-write, which reads the latest value.
//!
//! What is proven, under the release/acquire model in [`crate::ra`]:
//! - memory safety: every slot access is justified by a cell permission,
//!   which passes between the threads only through a release store and an
//!   acquire load that reads it, so the producer and consumer never race on
//!   a slot, and every value popped was initialized by a push;
//! - linearizability: `push`, `pop` and the batch operations are logically
//!   atomic. Each takes effect at a single atomic instruction, where it
//!   updates an abstract `Seq<T>` that clients hold through a [`QueueView`]
//!   ghost token, exactly as a sequential FIFO of capacity `cap` would;
//! - values left in the queue are dropped exactly once, by whichever side
//!   is dropped last.

// Each `atomically` clause defines a predicate struct (`XPred`) that the
// `verus!` macro gives no docs and no place to attach one. Every other item
// here is documented.
#![allow(missing_docs)]
use crate::ra::*;
use crate::util::{arc_clone, exhausted, CachePadded};
use std::sync::Arc;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::atomic::Commit;
use vstd::cell::CellId;
use vstd::try_open_atomic_update;
#[allow(unused_imports)]
use vstd::simple_pptr::MemContents;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::Loc;

verus! {

broadcast use vstd::set_lib::range_set_properties;

/// A client's view of the queue's contents, oldest first.
pub type QueueView<T> = GhostVar<Seq<T>>;

/// The producer's ghost state.
pub ghost struct ProdGhost {
    /// The next position the producer fills.
    pub tail: nat,
    /// The head the producer last read.
    pub head_cache: nat,
    /// The producer's latest message in the tail history, and its view.
    pub tidx: nat,
    /// The view of that message.
    pub tview: RaView,
    /// Set once the producer has been dropped.
    pub left: bool,
}

/// The consumer's ghost state.
pub ghost struct ConsGhost<T> {
    /// The next position the consumer takes.
    pub head: nat,
    /// The tail the consumer last read.
    pub tail_cache: nat,
    /// The values in the slots the consumer has claimed, `[head, tail_cache)`.
    pub held: Seq<T>,
    /// The consumer's latest message in the head history, and its view.
    pub hidx: nat,
    /// The view of that message.
    pub hview: RaView,
    /// Set once the consumer has been dropped.
    pub left: bool,
}

/// The ring buffer's constants: its capacity and the ids of its atomics, cells and ghost resources.
pub ghost struct Consts {
    /// The capacity.
    pub cap: nat,
    /// The id of the `head` atomic.
    pub head_id: int,
    /// The id of the `tail` atomic.
    pub tail_id: int,
    /// The id of the `refs` atomic.
    pub refs_id: int,
    /// The ids of the slots' cells.
    pub cells: Seq<CellId>,
    /// The id of the cell the producer leaves its final tail in.
    pub tail_out: CellId,
    /// The id of the cell the consumer leaves its final head in.
    pub head_out: CellId,
    /// The location of the abstract queue (`QueueView`).
    pub q_id: Loc,
    /// The location of the producer's ghost state.
    pub prod_id: Loc,
    /// The location of the consumer's ghost state.
    pub cons_id: Loc,
}

/// What the producer leaves behind when dropped: its ghost state, and its
/// final tail in a cell, for whichever side cleans up.
pub tracked struct ProdLeft {
    /// The producer's ghost state.
    pub g: GhostVar<ProdGhost>,
    /// Its final tail.
    pub tail_out: Published<PointsTo<u64>>,
}

/// What the consumer leaves behind when dropped: its ghost state, the slots
/// it had claimed, its final head, and its view when it left.
pub tracked struct ConsLeft<T> {
    /// The consumer's ghost state.
    pub g: GhostVar<ConsGhost<T>>,
    /// The cells of the slots it had claimed.
    pub held: Map<nat, Published<PointsTo<T>>>,
    /// Its final head.
    pub head_out: Published<PointsTo<u64>>,
    /// Its view when it left.
    pub ghost view: RaView,
}

/// Everything shared between the two sides: the histories of the three
/// atomics, the authoritative abstract queue and both sides' ghost state,
/// and the slot permissions that neither side holds, each published at the
/// view of the store that handed it over. Slot permissions are keyed by
/// absolute position, so a slot freed at position `p` is filed under
/// `p + cap`.
pub tracked struct Shared<T> {
    /// The history of `head`.
    pub head: Hist,
    /// The history of `tail`.
    pub tail: Hist,
    /// The history of `refs`.
    pub refs: Hist,
    /// The authoritative abstract queue.
    pub q: GhostVarAuth<Seq<T>>,
    /// The authority over the producer's ghost state.
    pub prod: GhostVarAuth<ProdGhost>,
    /// The authority over the consumer's ghost state.
    pub cons: GhostVarAuth<ConsGhost<T>>,
    /// The cells neither side holds, by absolute position.
    pub cells: Map<nat, Published<PointsTo<T>>>,
    /// What the producer left, once it has been dropped.
    pub prod_left: Option<ProdLeft>,
    /// What the consumer left, once it has been dropped.
    pub cons_left: Option<ConsLeft<T>>,
    /// Set by the last side to leave, once it has taken the values out.
    pub dead: bool,
}

// Histories, ghost variables and published permissions only.
impl<T> Objective for Shared<T> {}

pub open spec fn slot_ok<T>(c: Consts, p: nat, perm: PointsTo<T>) -> bool {
    perm.id() == c.cells[(p % c.cap) as int]
}

/// `m` holds initialized slots for positions `[lo, hi)`, with `q[p - base]`.
pub open spec fn full_perms<T>(
    m: Map<nat, PointsTo<T>>,
    c: Consts,
    lo: nat,
    hi: nat,
    q: Seq<T>,
    base: nat,
) -> bool {
    forall|p: nat|
        lo <= p < hi ==> {
            &&& #[trigger] m.dom().contains(p)
            &&& slot_ok(c, p, m[p])
            &&& m[p].is_init()
            &&& m[p].value() == q[p - base]
        }
}

/// `m` holds uninitialized slots for positions `[lo, hi)`.
pub open spec fn empty_perms<T>(m: Map<nat, PointsTo<T>>, c: Consts, lo: nat, hi: nat) -> bool {
    forall|p: nat|
        lo <= p < hi ==> {
            &&& #[trigger] m.dom().contains(p)
            &&& slot_ok(c, p, m[p])
            &&& m[p].is_uninit()
        }
}

/// `full_perms` for published permissions.
pub open spec fn full_pub<T>(
    m: Map<nat, Published<PointsTo<T>>>,
    c: Consts,
    lo: nat,
    hi: nat,
    q: Seq<T>,
    base: nat,
) -> bool {
    forall|p: nat|
        lo <= p < hi ==> {
            &&& #[trigger] m.dom().contains(p)
            &&& slot_ok(c, p, m[p].value())
            &&& m[p].value().is_init()
            &&& m[p].value().value() == q[p - base]
        }
}

/// `empty_perms` for published permissions.
pub open spec fn empty_pub<T>(m: Map<nat, Published<PointsTo<T>>>, c: Consts, lo: nat, hi: nat) -> bool {
    forall|p: nat|
        lo <= p < hi ==> {
            &&& #[trigger] m.dom().contains(p)
            &&& slot_ok(c, p, m[p].value())
            &&& m[p].value().is_uninit()
        }
}

/// Every permission in `[lo, hi)` was published at a view below `v`, so a
/// thread that has acquired `v` may take them.
pub open spec fn seen_by<T>(m: Map<nat, Published<PointsTo<T>>>, lo: nat, hi: nat, v: RaView) -> bool {
    forall|p: nat| lo <= p < hi ==> (#[trigger] m[p]).view().le(v)
}

/// The ring buffer's invariant (see its `inv`).
pub struct SpscPred;

impl<T> InvariantPredicate<Consts, Shared<T>> for SpscPred {
    open spec fn inv(c: Consts, s: Shared<T>) -> bool {
        let pg = s.prod@;
        let cg = s.cons@;
        let q = s.q@;
        let th = s.tail.msgs();
        let hh = s.head.msgs();
        &&& s.head.loc() == c.head_id
        &&& s.tail.loc() == c.tail_id
        &&& s.refs.loc() == c.refs_id
        &&& s.q.id() == c.q_id
        &&& s.prod.id() == c.prod_id
        &&& s.cons.id() == c.cons_id
        &&& c.cap > 0
        // The histories: the latest values are the true indices, no message
        // is ahead of them, and each side's own latest message is recorded.
        &&& th.len() > 0
        &&& hh.len() > 0
        &&& s.tail.last().val == pg.tail
        &&& s.head.last().val == cg.head
        &&& forall|i: int| 0 <= i < th.len() ==> #[trigger] th[i].val <= pg.tail
        &&& forall|i: int| 0 <= i < hh.len() ==> #[trigger] hh[i].val <= cg.head
        &&& pg.tidx < th.len()
        &&& th[pg.tidx as int] == (Msg { val: pg.tail as u64, view: pg.tview })
        &&& cg.hidx < hh.len()
        &&& hh[cg.hidx as int] == (Msg { val: cg.head as u64, view: cg.hview })
        // The queue.
        &&& pg.head_cache <= cg.head <= cg.tail_cache <= pg.tail <= pg.head_cache + c.cap
        &&& q.len() == pg.tail - cg.head
        &&& cg.held == q.subrange(0, cg.tail_cache - cg.head)
        // Who has left.
        &&& s.refs.msgs().len() > 0
        &&& s.refs.last().val as int == 2 - (if pg.left { 1int } else { 0 }) - (if cg.left { 1int } else { 0 })
        &&& s.dead ==> pg.left && cg.left
        // What the sides left behind, the slots, and the cells for the final
        // indices, until the last side to leave has taken them out.
        &&& !s.dead ==> {
            &&& pg.left == (s.prod_left is Some)
            &&& cg.left == (s.cons_left is Some)
            &&& s.prod_left matches Some(pl) ==> {
                &&& pl.g.id() == c.prod_id
                &&& pg.tview.le(s.refs.last().view)
            }
            &&& s.cons_left matches Some(cl) ==> {
                &&& cl.g.id() == c.cons_id
                &&& cl.view.le(s.refs.last().view)
            }
            &&& full_pub(s.cells, c, cg.tail_cache, pg.tail, q, cg.head)
            &&& empty_pub(s.cells, c, pg.head_cache + c.cap, cg.head + c.cap)
            &&& forall|i: int| 0 <= i < th.len() ==> seen_by(s.cells, cg.tail_cache, #[trigger] th[i].val as nat, th[i].view)
            &&& forall|i: int| 0 <= i < hh.len() ==> seen_by(s.cells, pg.head_cache + c.cap, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view)
            &&& s.prod_left matches Some(pl) ==> {
                &&& pl.tail_out.value().id() == c.tail_out
                &&& pl.tail_out.value().mem_contents() == MemContents::Init(pg.tail as u64)
                &&& pl.tail_out.view().le(s.refs.last().view)
            }
            &&& s.cons_left matches Some(cl) ==> {
                &&& full_pub(cl.held, c, cg.head, cg.tail_cache, cg.held, cg.head)
                &&& seen_by(cl.held, cg.head, cg.tail_cache, cl.view)
                &&& cl.head_out.value().id() == c.head_out
                &&& cl.head_out.value().mem_contents() == MemContents::Init(cg.head as u64)
                &&& cl.head_out.view().le(cl.view)
            }
        }
    }
}

/// The storage a `Producer` and `Consumer` share.
pub struct RingBuffer<T> {
    head: CachePadded<RaU64>,
    tail: CachePadded<RaU64>,
    /// How many of the producer and consumer are still alive.
    refs: RaU64,
    buf: Vec<PCell<T>>,
    /// The final indices, written by each side as it leaves.
    tail_out: PCell<u64>,
    head_out: PCell<u64>,
    cap: u64,
    inv: Tracked<ObjInvariant<Consts, Shared<T>, SpscPred>>,
}

impl<T> RingBuffer<T> {
    pub closed spec fn consts(&self) -> Consts {
        self.inv@.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        let c = self.consts();
        &&& c.cap == self.cap as nat
        &&& self.cap > 0
        &&& c.head_id == self.head.0.id()
        &&& c.tail_id == self.tail.0.id()
        &&& c.refs_id == self.refs.id()
        &&& c.tail_out == self.tail_out.id()
        &&& c.head_out == self.head_out.id()
        &&& c.cells.len() == c.cap
        &&& self.buf@.len() == c.cap
        &&& forall|i: int| 0 <= i < c.cap ==> #[trigger] self.buf@[i].id() == c.cells[i]
    }

    pub closed spec fn ns(&self) -> int {
        self.inv@.namespace()
    }

    pub closed spec fn qid(&self) -> Loc {
        self.consts().q_id
    }
}

/// The sending half of a single-producer single-consumer ring buffer, with rtrb's API.
pub struct Producer<T> {
    rb: Arc<RingBuffer<T>>,
    tail: u64,
    idx: u64,
    /// `head_cache + cap`: the producer may fill positions below this.
    limit: u64,
    g: Tracked<GhostVar<ProdGhost>>,
    perms: Tracked<Map<nat, PointsTo<T>>>,
    tail_out: Tracked<PointsTo<u64>>,
    tid: Tracked<Tid>,
}

/// The receiving half of a single-producer single-consumer ring buffer, with rtrb's API.
pub struct Consumer<T> {
    rb: Arc<RingBuffer<T>>,
    head: u64,
    idx: u64,
    tail_cache: u64,
    g: Tracked<GhostVar<ConsGhost<T>>>,
    perms: Tracked<Map<nat, PointsTo<T>>>,
    head_out: Tracked<PointsTo<u64>>,
    tid: Tracked<Tid>,
}

proof fn lemma_mod_next(p: nat, cap: nat)
    requires
        cap > 0,
    ensures
        (p + 1) % cap == if p % cap + 1 == cap { 0 } else { p % cap + 1 },
{
    use vstd::arithmetic::div_mod::*;
    let q = p as int / cap as int;
    let r = p as int % cap as int;
    lemma_fundamental_div_mod(p as int, cap as int);
    assert(p == q * cap + r) by (nonlinear_arith)
        requires p == cap * q + r;
    if r + 1 < cap {
        lemma_fundamental_div_mod_converse_mod((p + 1) as int, cap as int, q, r + 1);
    } else {
        assert(p + 1 == (q + 1) * cap + 0) by (nonlinear_arith)
            requires p == q * cap + r, r + 1 == cap;
        lemma_fundamental_div_mod_converse_mod((p + 1) as int, cap as int, q + 1, 0);
    }
}

proof fn lemma_mod_plus_cap(p: nat, cap: nat)
    requires
        cap > 0,
    ensures
        (p + cap) % cap == p % cap,
{
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(p as int, cap as int);
}

/// Takes the published permissions for `[lo, hi)` out of `m`, given a view
/// that has seen them all.
proof fn acquire_range<T>(tracked m: &mut Map<nat, Published<PointsTo<T>>>, lo: nat, hi: nat, tracked tid: &Tid) -> (tracked r: Map<nat, PointsTo<T>>)
    requires
        forall|p: nat| lo <= p < hi ==> #[trigger] old(m).dom().contains(p),
        seen_by(*old(m), lo, hi, tid.view()),
    ensures
        forall|p: nat| #![trigger r.dom().contains(p)] lo <= p < hi ==> r.dom().contains(p) && r[p] == old(m)[p].value(),
        forall|p: nat| #[trigger] r.dom().contains(p) ==> lo <= p < hi,
        forall|p: nat| #![trigger final(m).dom().contains(p)] #![trigger final(m)[p]] !(lo <= p < hi) ==> (final(m).dom().contains(p) == old(m).dom().contains(p) && final(m)[p] == old(m)[p]),
        same_outside(*final(m), *old(m), lo, hi),
    decreases hi - lo,
{
    reveal(same_outside);
    if lo >= hi {
        Map::tracked_empty()
    } else {
        let tracked x = m.tracked_remove(lo);
        assert(x.view().le(tid.view()));
        let tracked mut r = acquire_range(m, lo + 1, hi, tid);
        r.tracked_insert(lo, x.acquire(tid));
        r
    }
}

/// Publishes the permissions for `[lo, hi)` at `tid`'s view into `m`.
proof fn publish_range<T>(tracked src: Map<nat, PointsTo<T>>, tracked m: &mut Map<nat, Published<PointsTo<T>>>, lo: nat, hi: nat, tracked tid: &Tid)
    requires
        forall|p: nat| lo <= p < hi ==> #[trigger] src.dom().contains(p),
    ensures
        forall|p: nat| #![trigger final(m).dom().contains(p)] lo <= p < hi ==> final(m).dom().contains(p) && final(m)[p].value() == src[p] && final(m)[p].view() == tid.view(),
        forall|p: nat| #![trigger final(m).dom().contains(p)] #![trigger final(m)[p]] !(lo <= p < hi) ==> (final(m).dom().contains(p) == old(m).dom().contains(p) && final(m)[p] == old(m)[p]),
        same_outside(*final(m), *old(m), lo, hi),
    decreases hi - lo,
{
    reveal(same_outside);
    if lo < hi {
        let tracked mut src = src;
        let ghost s0 = src;
        let tracked x = src.tracked_remove(lo);
        m.tracked_insert(lo, Published::publish(x, tid));
        publish_range(src, m, lo + 1, hi, tid);
    }
}

impl<T> Producer<T> {
    pub closed spec fn wf(&self) -> bool {
        let c = self.rb.consts();
        &&& self.rb.wf()
        &&& self.g@.id() == c.prod_id
        &&& self.g@@.tail == self.tail as nat
        &&& self.g@@.head_cache + c.cap == self.limit as nat
        &&& !self.g@@.left
        &&& self.g@@.tview.le(self.tid@.view())
        &&& self.idx as nat == self.tail as nat % c.cap
        &&& self.tail <= self.limit
        &&& empty_perms(self.perms@, c, self.tail as nat, self.limit as nat)
        &&& self.tail_out@.id() == c.tail_out
        &&& self.tail_out@.is_uninit()
    }

    pub closed spec fn qid(&self) -> Loc {
        self.rb.qid()
    }

    pub closed spec fn ns(&self) -> int {
        self.rb.ns()
    }

    pub closed spec fn capacity_spec(&self) -> nat {
        self.rb.cap as nat
    }

    /// Re-reads the head with an acquire load and claims the slots the
    /// consumer has freed since. Not a linearization point.
    #[verifier::spinoff_prover]
    fn refresh(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).rb == old(self).rb,
            final(self).tail == old(self).tail,
            final(self).limit >= old(self).limit,
    {
        let ghost c = self.rb.consts();
        let head;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let (h, Ghost(i)) = self.rb.head.0.load_acquire(Tracked(&s.head), Tracked(self.tid.borrow_mut()));
            head = h;
            proof {
                s.prod.agree(self.g.borrow());
                let ghost pg = s.prod@;
                let ghost cg = s.cons@;
                let ghost hh = s.head.msgs();
                let ghost m = hh[i as int];
                assert(m.val <= cg.head);
                lemma_acquired(tid0, m.view, c.head_id, i, self.tid@.view());
                lemma_view_le_trans(pg.tview, tid0, self.tid@.view());
                if h as nat > pg.head_cache {
                    let ghost lo = pg.head_cache + c.cap;
                    let ghost hi = h as nat + c.cap;
                    let ghost old_cells = s.cells;
                    let ghost old_perms = self.perms@;
                    assert(seen_by(s.cells, lo, hi, self.tid@.view())) by {
                        assert forall|p: nat| lo <= p < hi implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            assert(seen_by(s.cells, lo, (m.val + c.cap) as nat, m.view));
                            lemma_view_le_trans(s.cells[p].view(), m.view, self.tid@.view());
                        }
                    }
                    let tracked got = acquire_range(&mut s.cells, lo, hi, self.tid.borrow());
                    self.perms.borrow_mut().tracked_union_prefer_right(got);
                    s.prod.update(self.g.borrow_mut(), ProdGhost { head_cache: h as nat, ..pg });
                    assert(empty_perms(self.perms@, c, self.tail as nat, hi)) by {
                        assert forall|p: nat| self.tail <= p < hi implies {
                            &&& #[trigger] self.perms@.dom().contains(p)
                            &&& slot_ok(c, p, self.perms@[p])
                            &&& self.perms@[p].is_uninit()
                        } by {
                            if p < lo {
                                assert(old_perms.dom().contains(p));
                                assert(!got.dom().contains(p));
                            } else {
                                assert(got.dom().contains(p));
                                assert(old_cells.dom().contains(p));
                            }
                        }
                    }
                    lemma_cells_frame(c, s.cells, old_cells, s.prod@, cg, s.q@, s.tail.msgs(), hh, lo, hi);
                }
            }
        });
        if head > u64::MAX - self.rb.cap {
            exhausted();
        }
        if head + self.rb.cap > self.limit {
            self.limit = head + self.rb.cap;
        }
    }

    /// Appends `value`, or gives it back if the queue holds `capacity` values.
    #[verifier::spinoff_prover]
    pub fn push(&mut self, value: T) -> (r: Result<(), T>)
        atomically (au) {
            type PushPred,
            (x: QueueView<T>) -> (y: Commit<QueueView<T>>),
            requires
                x.id() == self.qid(),
            ensures
                y@.id() == x.id(),
                if x@.len() < self.capacity_spec() {
                    y@@ == x@.push(value)
                } else {
                    y@@ == x@
                },
            outer_mask any / [this.ns()],
        },
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).qid() == old(self).qid(),
            final(self).ns() == old(self).ns(),
            final(self).capacity_spec() == old(self).capacity_spec(),
            r is Ok <==> x@.len() < old(self).capacity_spec(),
            r matches Err(v) ==> v == value,
    {
        // Held in an option so that the failure path and the success path can
        // each consume it.
        let tracked mut au_opt = Some(au);
        let ghost c = self.rb.consts();
        if self.tail == self.limit {
            self.refresh();
        }
        if self.tail == self.limit {
            // Still full by an acquire load, which may be stale: read the
            // latest head with a read-modify-write.
            let head;
            open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
                let ghost tid0 = self.tid@.view();
                let ghost hh = s.head.msgs();
                proof {
                    s.head.nonempty_lemma();
                    s.prod.agree(self.g.borrow());
                }
                head = self.rb.head.0.fetch_add_acqrel(Tracked(&mut s.head), Tracked(self.tid.borrow_mut()), 0);
                proof {
                    let ghost pg = s.prod@;
                    let ghost cg = s.cons@;
                    let ghost last = hh.last();
                    lemma_acquired(tid0, last.view, c.head_id, hh.len(), self.tid@.view());
                    lemma_view_le_trans(pg.tview, tid0, self.tid@.view());
                    assert(s.head.msgs() == hh.push(Msg { val: last.val, view: self.tid@.view() }));
                    assert(head as nat == cg.head);
                    let ghost lo = pg.head_cache + c.cap;
                    let ghost hi = cg.head + c.cap;
                    let ghost old_cells = s.cells;
                    let ghost old_perms = self.perms@;
                    assert(seen_by(s.cells, lo, hi, self.tid@.view())) by {
                        assert(seen_by(s.cells, lo, (hh[hh.len() - 1].val + c.cap) as nat, hh[hh.len() - 1].view));
                        assert forall|p: nat| lo <= p < hi implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            lemma_view_le_trans(s.cells[p].view(), last.view, self.tid@.view());
                        }
                    }
                    lemma_rmw_seen(s.cells, lo, c.cap, hh, s.head.msgs(), self.tid@.view());
                    let tracked got = acquire_range(&mut s.cells, lo, hi, self.tid.borrow());
                    self.perms.borrow_mut().tracked_union_prefer_right(got);
                    s.prod.update(self.g.borrow_mut(), ProdGhost { head_cache: cg.head, ..pg });
                    assert(empty_perms(self.perms@, c, self.tail as nat, hi)) by {
                        assert forall|p: nat| self.tail <= p < hi implies {
                            &&& #[trigger] self.perms@.dom().contains(p)
                            &&& slot_ok(c, p, self.perms@[p])
                            &&& self.perms@[p].is_uninit()
                        } by {
                            if p < lo {
                                assert(old_perms.dom().contains(p));
                                assert(!got.dom().contains(p));
                            } else {
                                assert(got.dom().contains(p));
                                assert(old_cells.dom().contains(p));
                            }
                        }
                    }
                    lemma_cells_frame(c, s.cells, old_cells, s.prod@, cg, s.q@, s.tail.msgs(), s.head.msgs(), lo, hi);
                }
                if head == self.tail - self.rb.cap {
                    // Full: this read is where `push` fails.
                    let tracked au = au_opt.tracked_take();
                    try_open_atomic_update!(au, x => {
                        proof { s.q.agree(&x); }
                        Tracked(Commit(x))
                    });
                }
            });
            if head == self.tail - self.rb.cap {
                return Err(value);
            }
            if head > u64::MAX - self.rb.cap {
                exhausted();
            }
            self.limit = head + self.rb.cap;
        }
        assert(self.tail < self.limit);
        let ghost tail = self.tail as nat;
        assert(self.perms@.dom().contains(tail));
        let ghost pre_perms = self.perms@;
        let tracked mut perm = self.perms.borrow_mut().tracked_remove(tail);
        let cell = &self.rb.buf[self.idx as usize];
        cell.put(Tracked(&mut perm), value);
        let next = self.tail + 1;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let ghost th = s.tail.msgs();
            let ghost n = th.len();
            proof {
                s.prod.agree(self.g.borrow());
            }
            self.rb.tail.0.store_release(Tracked(&mut s.tail), Tracked(self.tid.borrow_mut()), next);
            let ghost old_cells = s.cells;
            let ghost old_q = s.q@;
            let ghost pg = s.prod@;
            let ghost cg = s.cons@;
            proof {
                lemma_stored(tid0, c.tail_id, n, self.tid@.view());
                lemma_view_le_trans(pg.tview, tid0, self.tid@.view());
                let tracked pp = Published::publish(perm, self.tid.borrow());
                s.cells.tracked_insert(tail, pp);
                s.prod.update(self.g.borrow_mut(), ProdGhost { tail: next as nat, tidx: n, tview: self.tid@.view(), ..pg });
                assert(seen_by(old_cells, cg.tail_cache, tail, pg.tview)) by {
                    assert(seen_by(old_cells, cg.tail_cache, th[pg.tidx as int].val as nat, th[pg.tidx as int].view));
                }
                assert(same_outside(s.cells, old_cells, tail, tail + 1)) by { reveal(same_outside); }
                lemma_publish_tail(old_cells, s.cells, th, s.tail.msgs(), cg.tail_cache, tail, 1, pg.tview, self.tid@.view());
                lemma_seen_frame(old_cells, s.cells, tail, tail + 1, pg.head_cache + c.cap, c.cap, s.head.msgs());
            }
            let tracked au = au_opt.tracked_take();
            try_open_atomic_update!(au, x => {
                let tracked mut x = x;
                proof {
                    s.q.agree(&x);
                    s.q.update(&mut x, s.q@.push(value));
                }
                Tracked(Commit(x))
            });
            proof {
                assert(full_pub(s.cells, c, cg.tail_cache, next as nat, s.q@, cg.head)) by {
                    assert forall|p: nat| cg.tail_cache <= p < next implies {
                        &&& #[trigger] s.cells.dom().contains(p)
                        &&& slot_ok(c, p, s.cells[p].value())
                        &&& s.cells[p].value().is_init()
                        &&& s.cells[p].value().value() == s.q@[p - cg.head]
                    } by {
                        if p < tail {
                            assert(old_cells.dom().contains(p));
                        }
                    }
                }
                assert(empty_pub(s.cells, c, pg.head_cache + c.cap, cg.head + c.cap)) by {
                    assert forall|p: nat| pg.head_cache + c.cap <= p < cg.head + c.cap implies {
                        &&& #[trigger] s.cells.dom().contains(p)
                        &&& slot_ok(c, p, s.cells[p].value())
                        &&& s.cells[p].value().is_uninit()
                    } by {
                        assert(p != tail);
                        assert(old_cells.dom().contains(p));
                    }
                }
                assert(s.q@.subrange(0, cg.tail_cache - cg.head) =~= old_q.subrange(0, cg.tail_cache - cg.head));
            }
        });
        proof {
            lemma_mod_next(tail, c.cap);
            assert(empty_perms(self.perms@, c, next as nat, self.limit as nat)) by {
                assert forall|p: nat| next <= p < self.limit implies {
                    &&& #[trigger] self.perms@.dom().contains(p)
                    &&& slot_ok(c, p, self.perms@[p])
                    &&& self.perms@[p].is_uninit()
                } by {
                    assert(pre_perms.dom().contains(p));
                }
            }
        }
        self.tail = next;
        self.idx = if self.idx + 1 == self.rb.cap { 0 } else { self.idx + 1 };
        Ok(())
    }
}


impl<T> Consumer<T> {
    pub closed spec fn wf(&self) -> bool {
        let c = self.rb.consts();
        &&& self.rb.wf()
        &&& self.g@.id() == c.cons_id
        &&& self.g@@.head == self.head as nat
        &&& self.g@@.tail_cache == self.tail_cache as nat
        &&& self.g@@.held.len() == self.tail_cache - self.head
        &&& !self.g@@.left
        &&& self.g@@.hview.le(self.tid@.view())
        &&& self.idx as nat == self.head as nat % c.cap
        &&& self.head <= self.tail_cache
        &&& full_perms(self.perms@, c, self.head as nat, self.tail_cache as nat, self.g@@.held, self.head as nat)
        &&& self.head_out@.id() == c.head_out
        &&& self.head_out@.is_uninit()
    }

    pub closed spec fn qid(&self) -> Loc {
        self.rb.qid()
    }

    pub closed spec fn ns(&self) -> int {
        self.rb.ns()
    }

    /// Takes the published slots `[tc, newt)` and records them as held.
    proof fn claim(tracked &mut self, tracked s: &mut Shared<T>, c: Consts, newt: nat)
        requires
            old(self).wf(),
            c == old(self).rb.consts(),
            SpscPred::inv(c, *old(s)),
            old(s).cons@ == old(self).g@@,
            old(self).tail_cache <= newt <= old(s).prod@.tail,
            seen_by(old(s).cells, old(self).tail_cache as nat, newt, old(self).tid@.view()),
        ensures
            final(self).g@@ == (ConsGhost { tail_cache: newt, held: old(s).q@.subrange(0, newt - old(self).head), ..old(self).g@@ }),
            final(self).g@.id() == old(self).g@.id(),
            final(self).rb == old(self).rb,
            final(self).tid == old(self).tid,
            final(self).head == old(self).head,
            final(self).tail_cache == old(self).tail_cache,
            final(self).idx == old(self).idx,
            final(self).head_out == old(self).head_out,
            full_perms(final(self).perms@, c, final(self).head as nat, newt, final(self).g@@.held, final(self).head as nat),
            final(self).g@@.held.len() == newt - old(self).head,
            SpscPred::inv(c, *final(s)),
            final(s).cons@ == final(self).g@@,
            final(s).prod == old(s).prod,
            final(s).q == old(s).q,
            final(s).head == old(s).head,
            final(s).tail == old(s).tail,
            final(s).refs == old(s).refs,
    {
        let ghost cg = s.cons@;
        let ghost pg = s.prod@;
        let ghost tc = cg.tail_cache;
        let ghost old_cells = s.cells;
        let ghost old_perms = self.perms@;
        let ghost held = s.q@.subrange(0, newt - cg.head);
        assert(!s.dead);
        let tracked got = acquire_range(&mut s.cells, tc, newt, self.tid.borrow());
        self.perms.borrow_mut().tracked_union_prefer_right(got);
        s.cons.update(self.g.borrow_mut(), ConsGhost { tail_cache: newt, held, ..cg });
        assert(full_perms(self.perms@, c, cg.head, newt, held, cg.head)) by {
            assert forall|p: nat| cg.head <= p < newt implies {
                &&& #[trigger] self.perms@.dom().contains(p)
                &&& slot_ok(c, p, self.perms@[p])
                &&& self.perms@[p].is_init()
                &&& self.perms@[p].value() == held[p - cg.head]
            } by {
                if p < tc {
                    assert(old_perms.dom().contains(p));
                    assert(!got.dom().contains(p));
                } else {
                    assert(got.dom().contains(p));
                    assert(old_cells.dom().contains(p));
                }
            }
        }
        lemma_cells_frame_cons(c, s.cells, old_cells, pg, cg, newt, s.q@, s.tail.msgs(), s.head.msgs());
        assert(s.q@.subrange(0, newt - cg.head) == held);
    }

    /// Re-reads the tail with an acquire load and claims the slots the
    /// producer has filled since. Not a linearization point.
    #[verifier::spinoff_prover]
    fn refresh(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).rb == old(self).rb,
            final(self).head == old(self).head,
            final(self).tail_cache >= old(self).tail_cache,
    {
        let ghost c = self.rb.consts();
        let tail;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let (t, Ghost(i)) = self.rb.tail.0.load_acquire(Tracked(&s.tail), Tracked(self.tid.borrow_mut()));
            tail = t;
            proof {
                s.cons.agree(self.g.borrow());
                let ghost th = s.tail.msgs();
                let ghost m = th[i as int];
                lemma_acquired(tid0, m.view, c.tail_id, i, self.tid@.view());
                lemma_view_le_trans(s.cons@.hview, tid0, self.tid@.view());
                if t > self.tail_cache {
                    assert(seen_by(s.cells, self.tail_cache as nat, t as nat, self.tid@.view())) by {
                        assert(seen_by(s.cells, s.cons@.tail_cache, m.val as nat, m.view));
                        assert forall|p: nat| self.tail_cache <= p < t implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            lemma_view_le_trans(s.cells[p].view(), m.view, self.tid@.view());
                        }
                    }
                    self.claim(&mut s, c, t as nat);
                    assert(self.g@@.tail_cache == t as nat);
                }
            }
            assert(t > self.tail_cache ==> self.g@@.tail_cache == t as nat);
            assert(t <= self.tail_cache ==> self.g@@.tail_cache == self.tail_cache as nat);
        });
        assert(tail > self.tail_cache ==> self.g@@.tail_cache == tail as nat);
        if tail > self.tail_cache {
            self.tail_cache = tail;
        }
    }

    /// Removes the oldest value, or returns `None` if the queue is empty.
    #[verifier::spinoff_prover]
    pub fn pop(&mut self) -> (r: Option<T>)
        atomically (au) {
            type PopPred,
            (x: QueueView<T>) -> (y: Commit<QueueView<T>>),
            requires
                x.id() == self.qid(),
            ensures
                y@.id() == x.id(),
                if x@.len() > 0 {
                    y@@ == x@.drop_first()
                } else {
                    y@@ == x@
                },
            outer_mask any / [this.ns()],
        },
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).qid() == old(self).qid(),
            final(self).ns() == old(self).ns(),
            r is Some <==> x@.len() > 0,
            r matches Some(v) ==> v == x@[0],
    {
        let tracked mut au_opt = Some(au);
        let ghost c = self.rb.consts();
        if self.head == self.tail_cache {
            self.refresh();
        }
        if self.head == self.tail_cache {
            // Still empty by an acquire load, which may be stale: read the
            // latest tail with a read-modify-write.
            let tail;
            open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
                let ghost tid0 = self.tid@.view();
                let ghost th = s.tail.msgs();
                proof {
                    s.tail.nonempty_lemma();
                    s.cons.agree(self.g.borrow());
                }
                tail = self.rb.tail.0.fetch_add_acqrel(Tracked(&mut s.tail), Tracked(self.tid.borrow_mut()), 0);
                proof {
                    let ghost last = th.last();
                    lemma_acquired(tid0, last.view, c.tail_id, th.len(), self.tid@.view());
                    lemma_view_le_trans(s.cons@.hview, tid0, self.tid@.view());
                    assert(s.tail.msgs() == th.push(Msg { val: last.val, view: self.tid@.view() }));
                    lemma_rmw_seen_tail(s.cells, s.cons@.tail_cache, th, s.tail.msgs(), self.tid@.view());
                    assert(tail as nat == s.prod@.tail);
                    assert(seen_by(s.cells, self.tail_cache as nat, tail as nat, self.tid@.view())) by {
                        assert(seen_by(s.cells, s.cons@.tail_cache, th[th.len() - 1].val as nat, th[th.len() - 1].view));
                        assert forall|p: nat| self.tail_cache <= p < tail implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            lemma_view_le_trans(s.cells[p].view(), last.view, self.tid@.view());
                        }
                    }
                    self.claim(&mut s, c, tail as nat);
                }
                if tail == self.head {
                    // Empty: this read is where `pop` fails.
                    let tracked au = au_opt.tracked_take();
                    try_open_atomic_update!(au, x => {
                        proof { s.q.agree(&x); }
                        Tracked(Commit(x))
                    });
                }
            });
            if tail == self.head {
                return None;
            }
            self.tail_cache = tail;
        }
        assert(self.head < self.tail_cache);
        let ghost head = self.head as nat;
        assert(self.perms@.dom().contains(head));
        let ghost pre_perms = self.perms@;
        let tracked mut perm = self.perms.borrow_mut().tracked_remove(head);
        let cell = &self.rb.buf[self.idx as usize];
        let value = cell.take(Tracked(&mut perm));
        assert(slot_ok(c, head, perm) && perm.is_uninit());
        let next = self.head + 1;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let ghost hh = s.head.msgs();
            let ghost n = hh.len();
            proof {
                s.cons.agree(self.g.borrow());
            }
            self.rb.head.0.store_release(Tracked(&mut s.head), Tracked(self.tid.borrow_mut()), next);
            let ghost old_cells = s.cells;
            let ghost old_q = s.q@;
            let ghost pg = s.prod@;
            let ghost cg = s.cons@;
            let ghost perm_v = perm;
            proof {
                lemma_stored(tid0, c.head_id, n, self.tid@.view());
                lemma_view_le_trans(cg.hview, tid0, self.tid@.view());
                lemma_mod_plus_cap(head, c.cap);
                let tracked pp = Published::publish(perm, self.tid.borrow());
                s.cells.tracked_insert(head + c.cap, pp);
                s.cons.update(self.g.borrow_mut(), ConsGhost {
                    head: next as nat,
                    held: cg.held.drop_first(),
                    hidx: n,
                    hview: self.tid@.view(),
                    ..cg
                });
                assert(value == old_q[0]);
                assert(seen_by(old_cells, pg.head_cache + c.cap, head + c.cap, cg.hview)) by {
                    assert(seen_by(old_cells, pg.head_cache + c.cap, (hh[cg.hidx as int].val + c.cap) as nat, hh[cg.hidx as int].view));
                }
                assert(same_outside(s.cells, old_cells, head + c.cap, head + 1 + c.cap)) by { reveal(same_outside); }
                lemma_publish_head(old_cells, s.cells, hh, s.head.msgs(), pg.head_cache + c.cap, head, 1, c.cap, cg.hview, self.tid@.view());
                lemma_seen_frame_above(old_cells, s.cells, head + c.cap, head + c.cap + 1, cg.tail_cache, s.tail.msgs());
            }
            let tracked au = au_opt.tracked_take();
            try_open_atomic_update!(au, x => {
                let tracked mut x = x;
                proof {
                    s.q.agree(&x);
                    s.q.update(&mut x, s.q@.drop_first());
                }
                Tracked(Commit(x))
            });
            proof {
                assert(s.q@.subrange(0, s.cons@.tail_cache - s.cons@.head) =~= cg.held.drop_first());
                {
                    assert forall|p: nat| cg.tail_cache <= p < pg.tail implies {
                        &&& #[trigger] s.cells.dom().contains(p)
                        &&& slot_ok(c, p, s.cells[p].value())
                        &&& s.cells[p].value().is_init()
                        &&& s.cells[p].value().value() == s.q@[p - next]
                    } by {
                        assert(p != head + c.cap);
                        assert(old_cells.dom().contains(p));
                        assert(old_q[p - head] == s.q@[p - next]);
                    }
                    let ghost lo = cg.tail_cache;
                    let ghost hi = pg.tail;
                    let ghost nb = next as nat;
                    assert(forall|p: nat| lo <= p < hi ==> #[trigger] s.cells.dom().contains(p));
                    assert(full_pub(s.cells, c, lo, hi, s.q@, nb));
                }
                {
                    assert forall|p: nat| pg.head_cache + c.cap <= p < next + c.cap implies {
                        &&& #[trigger] s.cells.dom().contains(p)
                        &&& slot_ok(c, p, s.cells[p].value())
                        &&& s.cells[p].value().is_uninit()
                    } by {
                        if p < head + c.cap {
                            assert(old_cells.dom().contains(p));
                        } else {
                            assert(p == head + c.cap);
                            assert(s.cells[p].value() == perm_v);
                        }
                    }
                    let ghost lo = pg.head_cache + c.cap;
                    let ghost hi = (next + c.cap) as nat;
                    assert(forall|p: nat| lo <= p < hi ==> #[trigger] s.cells.dom().contains(p));
                    assert(empty_pub(s.cells, c, lo, hi));
                }
            }
        });
        proof {
            lemma_mod_next(head, c.cap);
            assert(full_perms(self.perms@, c, next as nat, self.tail_cache as nat, self.g@@.held, next as nat)) by {
                assert forall|p: nat| next <= p < self.tail_cache implies {
                    &&& #[trigger] self.perms@.dom().contains(p)
                    &&& slot_ok(c, p, self.perms@[p])
                    &&& self.perms@[p].is_init()
                    &&& self.perms@[p].value() == self.g@@.held[p - next]
                } by {
                    assert(pre_perms.dom().contains(p));
                }
            }
        }
        self.head = next;
        self.idx = if self.idx + 1 == self.rb.cap { 0 } else { self.idx + 1 };
        Some(value)
    }
}

/// A release store of `h + k` to the head, publishing the freed slots at
/// `[h + off, h + k + off)` at the store's view `v`, keeps every message's
/// `seen_by` fact.
proof fn lemma_publish_head<T>(
    old_cells: Map<nat, Published<PointsTo<T>>>,
    cells: Map<nat, Published<PointsTo<T>>>,
    hh: Seq<Msg>,
    hh2: Seq<Msg>,
    lo: nat,
    h: nat,
    k: nat,
    off: nat,
    pv: RaView,
    v: RaView,
)
    requires
        same_outside(cells, old_cells, h + off, h + k + off),
        forall|p: nat| #![trigger cells.dom().contains(p)] h + off <= p < h + k + off ==> cells.dom().contains(p) && cells[p].view() == v,
        hh2 == hh.push(Msg { val: (h + k) as u64, view: v }),
        h + k <= u64::MAX,
        lo <= h + off,
        forall|i: int| 0 <= i < hh.len() ==> #[trigger] hh[i].val <= h,
        forall|i: int| 0 <= i < hh.len() ==> seen_by(old_cells, lo, #[trigger] (hh[i].val + off) as nat, hh[i].view),
        seen_by(old_cells, lo, h + off, pv),
        pv.le(v),
    ensures
        forall|i: int| 0 <= i < hh2.len() ==> seen_by(cells, lo, #[trigger] (hh2[i].val + off) as nat, hh2[i].view),
{
    reveal(same_outside);
    assert forall|i: int| 0 <= i < hh2.len() implies seen_by(cells, lo, #[trigger] (hh2[i].val + off) as nat, hh2[i].view) by {
        if i < hh.len() {
            assert(hh2[i] == hh[i]);
            assert(seen_by(old_cells, lo, (hh[i].val + off) as nat, hh[i].view));
            assert forall|p: nat| lo <= p < (hh2[i].val + off) as nat implies (#[trigger] cells[p]).view().le(hh2[i].view) by {
                assert(cells.dom().contains(p) == old_cells.dom().contains(p));
            }
        } else {
            assert forall|p: nat| lo <= p < (hh2[i].val + off) as nat implies (#[trigger] cells[p]).view().le(hh2[i].view) by {
                if p < h + off {
                    assert(cells.dom().contains(p) == old_cells.dom().contains(p));
                    lemma_view_le_trans(old_cells[p].view(), pv, v);
                } else {
                    assert(cells.dom().contains(p));
                    lemma_view_le_refl(v);
                }
            }
        }
    }
}

/// Changing cells only at or above every tail message's range keeps the
/// tail's `seen_by` facts.
proof fn lemma_seen_frame_above<T>(old_cells: Map<nat, Published<PointsTo<T>>>, cells: Map<nat, Published<PointsTo<T>>>, a: nat, b: nat, lo: nat, th: Seq<Msg>)
    requires
        same_outside(cells, old_cells, a, b),
        forall|i: int| 0 <= i < th.len() ==> #[trigger] th[i].val <= a,
        forall|i: int| 0 <= i < th.len() ==> seen_by(old_cells, lo, #[trigger] th[i].val as nat, th[i].view),
    ensures
        forall|i: int| 0 <= i < th.len() ==> seen_by(cells, lo, #[trigger] th[i].val as nat, th[i].view),
{
    reveal(same_outside);
    assert forall|i: int| 0 <= i < th.len() implies seen_by(cells, lo, #[trigger] th[i].val as nat, th[i].view) by {
        assert(seen_by(old_cells, lo, th[i].val as nat, th[i].view));
        assert forall|p: nat| lo <= p < th[i].val as nat implies (#[trigger] cells[p]).view().le(th[i].view) by {
            assert(cells.dom().contains(p) == old_cells.dom().contains(p));
        }
    }
}

/// The consumer claiming the published slots `[tc, newt)` preserves the cell
/// conditions of the invariant.
proof fn lemma_cells_frame_cons<T>(
    c: Consts,
    cells: Map<nat, Published<PointsTo<T>>>,
    old_cells: Map<nat, Published<PointsTo<T>>>,
    pg: ProdGhost,
    cg: ConsGhost<T>,
    newt: nat,
    q: Seq<T>,
    th: Seq<Msg>,
    hh: Seq<Msg>,
)
    requires
        same_outside(cells, old_cells, cg.tail_cache, newt),
        cg.tail_cache <= newt <= pg.tail,
        pg.tail <= pg.head_cache + c.cap,
        full_pub(old_cells, c, cg.tail_cache, pg.tail, q, cg.head),
        empty_pub(old_cells, c, pg.head_cache + c.cap, cg.head + c.cap),
        forall|i: int| 0 <= i < th.len() ==> seen_by(old_cells, cg.tail_cache, #[trigger] th[i].val as nat, th[i].view),
        forall|i: int| 0 <= i < hh.len() ==> seen_by(old_cells, pg.head_cache + c.cap, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view),
    ensures
        full_pub(cells, c, newt, pg.tail, q, cg.head),
        empty_pub(cells, c, pg.head_cache + c.cap, cg.head + c.cap),
        forall|i: int| 0 <= i < th.len() ==> seen_by(cells, newt, #[trigger] th[i].val as nat, th[i].view),
        forall|i: int| 0 <= i < hh.len() ==> seen_by(cells, pg.head_cache + c.cap, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view),
{
    reveal(same_outside);
    assert forall|p: nat| newt <= p < pg.tail implies #[trigger] cells.dom().contains(p) by {
        assert(old_cells.dom().contains(p));
    }
    assert forall|p: nat| pg.head_cache + c.cap <= p < cg.head + c.cap implies #[trigger] cells.dom().contains(p) by {
        assert(old_cells.dom().contains(p));
    }
    assert forall|i: int| 0 <= i < th.len() implies seen_by(cells, newt, #[trigger] th[i].val as nat, th[i].view) by {
        assert(seen_by(old_cells, cg.tail_cache, th[i].val as nat, th[i].view));
        assert forall|p: nat| newt <= p < th[i].val as nat implies (#[trigger] cells[p]).view().le(th[i].view) by {
            assert(cells.dom().contains(p) == old_cells.dom().contains(p));
        }
    }
    lemma_seen_frame(old_cells, cells, cg.tail_cache, newt, pg.head_cache + c.cap, c.cap, hh);
}

/// `a` and `b` agree outside `[lo, hi)`.
#[verifier::opaque]
pub open spec fn same_outside<T>(a: Map<nat, Published<PointsTo<T>>>, b: Map<nat, Published<PointsTo<T>>>, lo: nat, hi: nat) -> bool {
    forall|p: nat| #![trigger a.dom().contains(p)] #![trigger a[p]] !(lo <= p < hi) ==> (a.dom().contains(p) == b.dom().contains(p) && a[p] == b[p])
}

/// A read-modify-write appends a copy of the last message with a larger
/// view; every `seen_by` fact about the history still holds.
proof fn lemma_rmw_seen<T>(cells: Map<nat, Published<PointsTo<T>>>, lo: nat, off: nat, h: Seq<Msg>, h2: Seq<Msg>, v: RaView)
    requires
        h.len() > 0,
        h2 == h.push(Msg { val: h.last().val, view: v }),
        h.last().view.le(v),
        forall|i: int| 0 <= i < h.len() ==> seen_by(cells, lo, #[trigger] (h[i].val + off) as nat, h[i].view),
    ensures
        forall|i: int| 0 <= i < h2.len() ==> seen_by(cells, lo, #[trigger] (h2[i].val + off) as nat, h2[i].view),
{
    assert forall|i: int| 0 <= i < h2.len() implies seen_by(cells, lo, #[trigger] (h2[i].val + off) as nat, h2[i].view) by {
        if i < h.len() {
            assert(h2[i] == h[i]);
        } else {
            let j = h.len() - 1;
            assert(seen_by(cells, lo, (h[j].val + off) as nat, h[j].view));
            assert forall|p: nat| lo <= p < (h2[i].val + off) as nat implies (#[trigger] cells[p]).view().le(h2[i].view) by {
                lemma_view_le_trans(cells[p].view(), h[j].view, v);
            }
        }
    }
}

/// The same, for the tail's form of the facts.
proof fn lemma_rmw_seen_tail<T>(cells: Map<nat, Published<PointsTo<T>>>, lo: nat, h: Seq<Msg>, h2: Seq<Msg>, v: RaView)
    requires
        h.len() > 0,
        h2 == h.push(Msg { val: h.last().val, view: v }),
        h.last().view.le(v),
        forall|i: int| 0 <= i < h.len() ==> seen_by(cells, lo, #[trigger] h[i].val as nat, h[i].view),
    ensures
        forall|i: int| 0 <= i < h2.len() ==> seen_by(cells, lo, #[trigger] h2[i].val as nat, h2[i].view),
{
    assert forall|i: int| 0 <= i < h2.len() implies seen_by(cells, lo, #[trigger] h2[i].val as nat, h2[i].view) by {
        if i < h.len() {
            assert(h2[i] == h[i]);
        } else {
            let j = h.len() - 1;
            assert(seen_by(cells, lo, h[j].val as nat, h[j].view));
            assert forall|p: nat| lo <= p < h2[i].val as nat implies (#[trigger] cells[p]).view().le(h2[i].view) by {
                lemma_view_le_trans(cells[p].view(), h[j].view, v);
            }
        }
    }
}

/// A release store of `t + k` to the tail, publishing the slots `[t, t + k)`
/// at the store's view `v`, keeps every message's `seen_by` fact.
proof fn lemma_publish_tail<T>(
    old_cells: Map<nat, Published<PointsTo<T>>>,
    cells: Map<nat, Published<PointsTo<T>>>,
    th: Seq<Msg>,
    th2: Seq<Msg>,
    tc: nat,
    t: nat,
    k: nat,
    pv: RaView,
    v: RaView,
)
    requires
        same_outside(cells, old_cells, t, t + k),
        forall|p: nat| #![trigger cells.dom().contains(p)] t <= p < t + k ==> cells.dom().contains(p) && cells[p].view() == v,
        th2 == th.push(Msg { val: (t + k) as u64, view: v }),
        t + k <= u64::MAX,
        tc <= t,
        forall|i: int| 0 <= i < th.len() ==> #[trigger] th[i].val <= t,
        forall|i: int| 0 <= i < th.len() ==> seen_by(old_cells, tc, #[trigger] th[i].val as nat, th[i].view),
        seen_by(old_cells, tc, t, pv),
        pv.le(v),
    ensures
        forall|i: int| 0 <= i < th2.len() ==> seen_by(cells, tc, #[trigger] th2[i].val as nat, th2[i].view),
{
    reveal(same_outside);
    assert forall|i: int| 0 <= i < th2.len() implies seen_by(cells, tc, #[trigger] th2[i].val as nat, th2[i].view) by {
        if i < th.len() {
            assert(th2[i] == th[i]);
            assert(seen_by(old_cells, tc, th[i].val as nat, th[i].view));
            assert forall|p: nat| tc <= p < th2[i].val as nat implies (#[trigger] cells[p]).view().le(th2[i].view) by {
                assert(cells.dom().contains(p) == old_cells.dom().contains(p));
            }
        } else {
            assert forall|p: nat| tc <= p < th2[i].val as nat implies (#[trigger] cells[p]).view().le(th2[i].view) by {
                if p < t {
                    assert(cells.dom().contains(p) == old_cells.dom().contains(p));
                    lemma_view_le_trans(old_cells[p].view(), pv, v);
                } else {
                    assert(cells.dom().contains(p));
                    lemma_view_le_refl(v);
                }
            }
        }
    }
}

/// Changing cells only below `lo` keeps the `seen_by` facts above it.
proof fn lemma_seen_frame<T>(old_cells: Map<nat, Published<PointsTo<T>>>, cells: Map<nat, Published<PointsTo<T>>>, a: nat, b: nat, lo: nat, off: nat, h: Seq<Msg>)
    requires
        same_outside(cells, old_cells, a, b),
        b <= lo,
        forall|i: int| 0 <= i < h.len() ==> seen_by(old_cells, lo, #[trigger] (h[i].val + off) as nat, h[i].view),
    ensures
        forall|i: int| 0 <= i < h.len() ==> seen_by(cells, lo, #[trigger] (h[i].val + off) as nat, h[i].view),
{
    reveal(same_outside);
    assert forall|i: int| 0 <= i < h.len() implies seen_by(cells, lo, #[trigger] (h[i].val + off) as nat, h[i].view) by {
        assert(seen_by(old_cells, lo, (h[i].val + off) as nat, h[i].view));
        assert forall|p: nat| lo <= p < (h[i].val + off) as nat implies (#[trigger] cells[p]).view().le(h[i].view) by {
            assert(cells.dom().contains(p) == old_cells.dom().contains(p));
        }
    }
}

/// Removing the cells in `[lo, hi)`, which are freed slots now claimed by
/// the producer, preserves the cell conditions of the invariant.
proof fn lemma_cells_frame<T>(
    c: Consts,
    cells: Map<nat, Published<PointsTo<T>>>,
    old_cells: Map<nat, Published<PointsTo<T>>>,
    pg: ProdGhost,
    cg: ConsGhost<T>,
    q: Seq<T>,
    th: Seq<Msg>,
    hh: Seq<Msg>,
    lo: nat,
    hi: nat,
)
    requires
        same_outside(cells, old_cells, lo, hi),
        lo <= hi,
        hi <= pg.head_cache + c.cap,
        pg.tail <= lo,
        full_pub(old_cells, c, cg.tail_cache, pg.tail, q, cg.head),
        empty_pub(old_cells, c, lo, cg.head + c.cap),
        forall|i: int| 0 <= i < th.len() ==> seen_by(old_cells, cg.tail_cache, #[trigger] th[i].val as nat, th[i].view),
        forall|i: int| 0 <= i < hh.len() ==> seen_by(old_cells, lo, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view),
        forall|i: int| 0 <= i < th.len() ==> #[trigger] th[i].val <= pg.tail,
    ensures
        full_pub(cells, c, cg.tail_cache, pg.tail, q, cg.head),
        empty_pub(cells, c, pg.head_cache + c.cap, cg.head + c.cap),
        forall|i: int| 0 <= i < th.len() ==> seen_by(cells, cg.tail_cache, #[trigger] th[i].val as nat, th[i].view),
        forall|i: int| 0 <= i < hh.len() ==> seen_by(cells, pg.head_cache + c.cap, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view),
{
    reveal(same_outside);
    assert forall|p: nat| cg.tail_cache <= p < pg.tail implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_init()
        &&& cells[p].value().value() == q[p - cg.head]
    } by {
        assert(!(lo <= p < hi));
        assert(old_cells.dom().contains(p));
        assert(old_cells[p] == cells[p]);
    }
    assert forall|p: nat| pg.head_cache + c.cap <= p < cg.head + c.cap implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_uninit()
    } by {
        assert(!(lo <= p < hi));
        assert(old_cells.dom().contains(p));
        assert(old_cells[p] == cells[p]);
    }
    assert forall|i: int| 0 <= i < th.len() implies seen_by(cells, cg.tail_cache, #[trigger] th[i].val as nat, th[i].view) by {
        assert(seen_by(old_cells, cg.tail_cache, th[i].val as nat, th[i].view));
        assert forall|p: nat| cg.tail_cache <= p < th[i].val implies (#[trigger] cells[p]).view().le(th[i].view) by {
            assert(!(lo <= p < hi));
            assert(cells.dom().contains(p) == old_cells.dom().contains(p));
            assert(old_cells[p] == cells[p]);
        }
    }
    assert forall|i: int| 0 <= i < hh.len() implies seen_by(cells, pg.head_cache + c.cap, #[trigger] (hh[i].val + c.cap) as nat, hh[i].view) by {
        assert(seen_by(old_cells, lo, (hh[i].val + c.cap) as nat, hh[i].view));
        assert forall|p: nat| pg.head_cache + c.cap <= p < hh[i].val + c.cap implies (#[trigger] cells[p]).view().le(hh[i].view) by {
            assert(!(lo <= p < hi));
            assert(cells.dom().contains(p) == old_cells.dom().contains(p));
            assert(old_cells[p] == cells[p]);
        }
    }
}




impl<T> Producer<T> {
    /// Takes the published freed slots `[head_cache + cap, newh + cap)`.
    proof fn claim(tracked &mut self, tracked s: &mut Shared<T>, c: Consts, newh: nat)
        requires
            old(self).wf(),
            c == old(self).rb.consts(),
            SpscPred::inv(c, *old(s)),
            old(s).prod@ == old(self).g@@,
            old(self).g@@.head_cache <= newh <= old(s).cons@.head,
            seen_by(old(s).cells, old(self).g@@.head_cache + c.cap, newh + c.cap, old(self).tid@.view()),
        ensures
            final(self).g@@ == (ProdGhost { head_cache: newh, ..old(self).g@@ }),
            final(self).g@.id() == old(self).g@.id(),
            final(self).rb == old(self).rb,
            final(self).tid == old(self).tid,
            final(self).tail == old(self).tail,
            final(self).limit == old(self).limit,
            final(self).idx == old(self).idx,
            final(self).tail_out == old(self).tail_out,
            empty_perms(final(self).perms@, c, final(self).tail as nat, newh + c.cap),
            SpscPred::inv(c, *final(s)),
            final(s).prod@ == final(self).g@@,
            final(s).cons == old(s).cons,
            final(s).q == old(s).q,
            final(s).head == old(s).head,
            final(s).tail == old(s).tail,
            final(s).refs == old(s).refs,
    {
        let ghost pg = s.prod@;
        let ghost cg = s.cons@;
        let ghost lo = pg.head_cache + c.cap;
        let ghost hi = newh + c.cap;
        let ghost old_cells = s.cells;
        let ghost old_perms = self.perms@;
        assert(!s.dead);
        let tracked got = acquire_range(&mut s.cells, lo, hi, self.tid.borrow());
        self.perms.borrow_mut().tracked_union_prefer_right(got);
        s.prod.update(self.g.borrow_mut(), ProdGhost { head_cache: newh, ..pg });
        assert forall|p: nat| self.tail <= p < hi implies {
            &&& #[trigger] self.perms@.dom().contains(p)
            &&& slot_ok(c, p, self.perms@[p])
            &&& self.perms@[p].is_uninit()
        } by {
            if p < lo {
                assert(old_perms.dom().contains(p));
                assert(!got.dom().contains(p));
            } else {
                assert(got.dom().contains(p));
                assert(old_cells.dom().contains(p));
            }
        }
        lemma_cells_frame(c, s.cells, old_cells, s.prod@, cg, s.q@, s.tail.msgs(), s.head.msgs(), lo, hi);
    }
}

/// The cell conditions after the producer publishes the batch `[t0, t0 + k)`.
proof fn lemma_push_frame<T>(
    c: Consts,
    cells: Map<nat, Published<PointsTo<T>>>,
    old_cells: Map<nat, Published<PointsTo<T>>>,
    w: Map<nat, PointsTo<T>>,
    values: Seq<T>,
    old_q: Seq<T>,
    tc: nat,
    head: nat,
    hc: nat,
    t0: nat,
    k: nat,
)
    requires
        same_outside(cells, old_cells, t0, t0 + k),
        forall|p: nat| #![trigger cells.dom().contains(p)] t0 <= p < t0 + k ==> cells.dom().contains(p) && cells[p].value() == w[p],
        full_perms(w, c, t0, t0 + k, values, t0),
        k <= values.len(),
        full_pub(old_cells, c, tc, t0, old_q, head),
        empty_pub(old_cells, c, hc + c.cap, head + c.cap),
        t0 + k <= hc + c.cap,
        hc <= head,
        head <= tc <= t0,
        old_q.len() == t0 - head,
    ensures
        full_pub(cells, c, tc, t0 + k, old_q + values.subrange(0, k as int), head),
        empty_pub(cells, c, hc + c.cap, head + c.cap),
{
    reveal(same_outside);
    let vals = values.subrange(0, k as int);
    assert forall|p: nat| tc <= p < t0 + k implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_init()
        &&& cells[p].value().value() == (old_q + vals)[p - head]
    } by {
        assert((old_q + vals).len() == old_q.len() + k);
        if p < t0 {
            assert(old_cells.dom().contains(p));
            assert(cells[p] == old_cells[p]);
            assert(0 <= p - head < old_q.len());
            assert(old_q[p - head] == (old_q + vals)[p - head]);
        } else {
            assert(t0 <= p < t0 + k);
            assert(cells.dom().contains(p));
            assert(cells[p].value() == w[p]);
            assert(w.dom().contains(p));
            assert(0 <= p - t0 < k);
            assert(p - head == old_q.len() + (p - t0));
            assert(vals[p - t0 as int] == values[p - t0 as int]);
            assert(vals[p - t0] == (old_q + vals)[p - head]);
        }
    }
    assert forall|p: nat| hc + c.cap <= p < head + c.cap implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_uninit()
    } by {
        assert(old_cells.dom().contains(p));
    }
}

/// The cell conditions after the consumer frees the batch `[h0, h0 + k)`,
/// publishing the slots at `[h0 + cap, h0 + k + cap)`.
proof fn lemma_pop_frame<T>(
    c: Consts,
    cells: Map<nat, Published<PointsTo<T>>>,
    old_cells: Map<nat, Published<PointsTo<T>>>,
    f: Map<nat, PointsTo<T>>,
    old_q: Seq<T>,
    tc: nat,
    tail: nat,
    hc: nat,
    h0: nat,
    k: nat,
)
    requires
        same_outside(cells, old_cells, h0 + c.cap, h0 + k + c.cap),
        forall|p: nat| #![trigger cells.dom().contains(p)] h0 + c.cap <= p < h0 + k + c.cap ==> cells.dom().contains(p) && cells[p].value() == f[p],
        empty_perms(f, c, h0 + c.cap, h0 + k + c.cap),
        full_pub(old_cells, c, tc, tail, old_q, h0),
        empty_pub(old_cells, c, hc + c.cap, h0 + c.cap),
        h0 + k <= tc <= tail <= hc + c.cap,
        hc <= h0,
        old_q.len() == tail - h0,
    ensures
        full_pub(cells, c, tc, tail, old_q.subrange(k as int, old_q.len() as int), h0 + k),
        empty_pub(cells, c, hc + c.cap, h0 + k + c.cap),
{
    reveal(same_outside);
    let nq = old_q.subrange(k as int, old_q.len() as int);
    assert forall|p: nat| tc <= p < tail implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_init()
        &&& cells[p].value().value() == nq[p - (h0 + k)]
    } by {
        assert(!(h0 + c.cap <= p < h0 + k + c.cap));
        assert(old_cells.dom().contains(p));
        assert(cells[p] == old_cells[p]);
        assert(old_q[p - h0] == nq[p - (h0 + k)]);
    }
    assert forall|p: nat| hc + c.cap <= p < h0 + k + c.cap implies {
        &&& #[trigger] cells.dom().contains(p)
        &&& slot_ok(c, p, cells[p].value())
        &&& cells[p].value().is_uninit()
    } by {
        if p < h0 + c.cap {
            assert(old_cells.dom().contains(p));
            assert(cells[p] == old_cells[p]);
        } else {
            assert(f.dom().contains(p));
            assert(cells.dom().contains(p));
            assert(cells[p].value() == f[p]);
        }
    }
}


impl<T> Consumer<T> {
    /// Moves the values in the claimed slots `[head, head + k)` to `out`,
    /// and returns the emptied slots, filed under `p + cap`, and the index
    /// of slot `head + k`. Leaves `head` itself alone.
    #[verifier::spinoff_prover]
    fn take_slots(&mut self, out: &mut Vec<T>, k: u64) -> (r: (u64, Tracked<Map<nat, PointsTo<T>>>))
        requires
            old(self).wf(),
            old(self).head + k <= old(self).tail_cache,
        ensures
            final(self).rb == old(self).rb,
            final(self).head == old(self).head,
            final(self).tail_cache == old(self).tail_cache,
            final(self).idx == old(self).idx,
            final(self).g == old(self).g,
            final(self).tid == old(self).tid,
            final(self).head_out == old(self).head_out,
            r.0 as nat == (old(self).head + k) as nat % old(self).rb.consts().cap,
            r.0 < old(self).rb.cap,
            full_perms(final(self).perms@, old(self).rb.consts(), (old(self).head + k) as nat, old(self).tail_cache as nat, old(self).g@@.held, old(self).head as nat),
            empty_perms(r.1@, old(self).rb.consts(), (old(self).head + old(self).rb.consts().cap) as nat, (old(self).head + k + old(self).rb.consts().cap) as nat),
            forall|p: nat| #[trigger] r.1@.dom().contains(p) ==> old(self).head + old(self).rb.consts().cap <= p < old(self).head + k + old(self).rb.consts().cap,
            final(out)@ == old(out)@ + old(self).g@@.held.subrange(0, k as int),
    {
        let ghost c = self.rb.consts();
        let ghost out0 = out@;
        let ghost h0 = self.head as nat;
        let ghost held = self.g@@.held;
        let tracked mut freed: Map<nat, PointsTo<T>> = Map::tracked_empty();
        let mut i: u64 = 0;
        let mut idx = self.idx;
        assert(idx < self.rb.cap) by {
            vstd::arithmetic::div_mod::lemma_mod_bound(h0 as int, c.cap as int);
        }
        while i < k
            invariant
                self.rb.wf(),
                c == self.rb.consts(),
                h0 == self.head as nat,
                held == self.g@@.held,
                held.len() == self.tail_cache - self.head,
                self.head + k <= self.tail_cache,
                i <= k,
                idx as nat == (h0 + i as nat) % c.cap,
                idx < self.rb.cap,
                full_perms(self.perms@, c, h0 + i as nat, self.tail_cache as nat, held, h0),
                empty_perms(freed, c, h0 + c.cap, h0 + i as nat + c.cap),
                forall|p: nat| #[trigger] freed.dom().contains(p) ==> h0 + c.cap <= p < h0 + i as nat + c.cap,
                out@ == out0 + held.subrange(0, i as int),
            decreases k - i,
        {
            let ghost p = h0 + i as nat;
            assert(self.perms@.dom().contains(p));
            let ghost old_perms = self.perms@;
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(p);
            let cell = &self.rb.buf[idx as usize];
            let v = cell.take(Tracked(&mut perm));
            out.push(v);
            let ghost old_freed = freed;
            proof {
                lemma_mod_plus_cap(p, c.cap);
                freed.tracked_insert(p + c.cap, perm);
                lemma_mod_next(p, c.cap);
                assert forall|q: nat| h0 + c.cap <= q < p + 1 + c.cap implies {
                    &&& #[trigger] freed.dom().contains(q)
                    &&& slot_ok(c, q, freed[q])
                    &&& freed[q].is_uninit()
                } by {
                    if q < p + c.cap {
                        assert(old_freed.dom().contains(q));
                    }
                }
                assert forall|q: nat| p + 1 <= q < self.tail_cache implies {
                    &&& #[trigger] self.perms@.dom().contains(q)
                    &&& slot_ok(c, q, self.perms@[q])
                    &&& self.perms@[q].is_init()
                    &&& self.perms@[q].value() == held[q - h0]
                } by {
                    assert(old_perms.dom().contains(q));
                }
                assert(held.subrange(0, i as int + 1) =~= held.subrange(0, i as int).push(v));
            }
            idx = if idx + 1 == self.rb.cap { 0 } else { idx + 1 };
            i = i + 1;
        }
        (idx, Tracked(freed))
    }
}

impl<T: Copy> Producer<T> {
    /// Appends a prefix of `values`, as long as fits, with one index store
    /// for the whole batch. Returns how many were appended: none only if
    /// `values` is empty or the queue was full.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    pub fn push_slice(&mut self, values: &[T]) -> (n: usize)
        atomically (au) {
            type PushSlicePred,
            (x: QueueView<T>) -> (y: Commit<QueueView<T>>),
            requires
                x.id() == self.qid(),
            ensures
                y@.id() == x.id(),
                x@.len() <= y@@.len() <= x@.len() + values@.len(),
                y@@.len() <= self.capacity_spec(),
                y@@ == x@ + values@.subrange(0, y@@.len() - x@.len()),
                values@.len() > 0 && x@.len() < self.capacity_spec() ==> y@@.len() > x@.len(),
            outer_mask any / [this.ns()],
        },
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).qid() == old(self).qid(),
            final(self).ns() == old(self).ns(),
            final(self).capacity_spec() == old(self).capacity_spec(),
            n == y@@.len() - x@.len(),
    {
        let tracked mut au_opt = Some(au);
        let ghost c = self.rb.consts();
        if self.limit - self.tail < values.len() as u64 {
            // The cached head leaves less room than the batch: look again.
            self.refresh();
        }
        if self.tail == self.limit {
            // Still full by an acquire load, which may be stale: read the
            // latest head with a read-modify-write.
            let head;
            open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
                let ghost tid0 = self.tid@.view();
                let ghost hh = s.head.msgs();
                proof {
                    s.head.nonempty_lemma();
                    s.prod.agree(self.g.borrow());
                }
                head = self.rb.head.0.fetch_add_acqrel(Tracked(&mut s.head), Tracked(self.tid.borrow_mut()), 0);
                proof {
                    let ghost pg = s.prod@;
                    let ghost cg = s.cons@;
                    let ghost last = hh.last();
                    lemma_acquired(tid0, last.view, c.head_id, hh.len(), self.tid@.view());
                    lemma_view_le_trans(pg.tview, tid0, self.tid@.view());
                    assert(s.head.msgs() == hh.push(Msg { val: last.val, view: self.tid@.view() }));
                    assert(head as nat == cg.head);
                    let ghost lo = pg.head_cache + c.cap;
                    let ghost hi = cg.head + c.cap;
                    assert(seen_by(s.cells, lo, hi, self.tid@.view())) by {
                        assert(seen_by(s.cells, lo, (hh[hh.len() - 1].val + c.cap) as nat, hh[hh.len() - 1].view));
                        assert forall|p: nat| lo <= p < hi implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            lemma_view_le_trans(s.cells[p].view(), last.view, self.tid@.view());
                        }
                    }
                    lemma_rmw_seen(s.cells, lo, c.cap, hh, s.head.msgs(), self.tid@.view());
                    self.claim(&mut s, c, cg.head);
                }
                if head == self.tail - self.rb.cap {
                    // Full: this read is where `push_slice` fails.
                    let tracked au = au_opt.tracked_take();
                    try_open_atomic_update!(au, x => {
                        proof {
                            s.q.agree(&x);
                            assert(x@ =~= x@ + values@.subrange(0, 0));
                        }
                        Tracked(Commit(x))
                    });
                }
            });
            if head == self.tail - self.rb.cap {
                return 0;
            }
            if head > u64::MAX - self.rb.cap {
                exhausted();
            }
            self.limit = head + self.rb.cap;
        }
        assert(self.tail < self.limit);
        let room = self.limit - self.tail;
        let k: u64 = if (values.len() as u64) < room { values.len() as u64 } else { room };
        let ghost t0 = self.tail as nat;
        let tracked mut written: Map<nat, PointsTo<T>> = Map::tracked_empty();
        let mut i: u64 = 0;
        let mut idx = self.idx;
        while i < k
            invariant
                self.rb.wf(),
                c == self.rb.consts(),
                t0 == self.tail as nat,
                self.g@.id() == c.prod_id,
                self.g@@.tail == t0,
                self.g@@.head_cache + c.cap == self.limit as nat,
                !self.g@@.left,
                self.g@@.tview.le(self.tid@.view()),
                self.idx as nat == t0 % c.cap,
                self.tail_out@.id() == c.tail_out,
                self.tail_out@.is_uninit(),
                self.tail < self.limit,
                self.tail + k <= self.limit,
                k <= values@.len(),
                i <= k,
                idx as nat == (t0 + i as nat) % c.cap,
                empty_perms(self.perms@, c, t0 + i as nat, self.limit as nat),
                full_perms(written, c, t0, t0 + i as nat, values@, t0),
                forall|p: nat| #[trigger] written.dom().contains(p) ==> t0 <= p < t0 + i as nat,
            decreases k - i,
        {
            let ghost p = t0 + i as nat;
            assert(self.perms@.dom().contains(p));
            let ghost old_perms = self.perms@;
            let tracked mut perm = self.perms.borrow_mut().tracked_remove(p);
            assert(idx < self.rb.cap) by {
                vstd::arithmetic::div_mod::lemma_mod_bound(p as int, c.cap as int);
            }
            let cell = &self.rb.buf[idx as usize];
            cell.put(Tracked(&mut perm), values[i as usize]);
            let ghost old_written = written;
            proof {
                written.tracked_insert(p, perm);
                lemma_mod_next(p, c.cap);
                assert(full_perms(written, c, t0, p + 1, values@, t0)) by {
                    assert forall|q: nat| t0 <= q < p + 1 implies {
                        &&& #[trigger] written.dom().contains(q)
                        &&& slot_ok(c, q, written[q])
                        &&& written[q].is_init()
                        &&& written[q].value() == values@[q - t0]
                    } by {
                        if q < p {
                            assert(old_written.dom().contains(q));
                        }
                    }
                }
                assert(empty_perms(self.perms@, c, p + 1, self.limit as nat)) by {
                    assert forall|q: nat| p + 1 <= q < self.limit implies {
                        &&& #[trigger] self.perms@.dom().contains(q)
                        &&& slot_ok(c, q, self.perms@[q])
                        &&& self.perms@[q].is_uninit()
                    } by {
                        assert(old_perms.dom().contains(q));
                    }
                }
            }
            idx = if idx + 1 == self.rb.cap { 0 } else { idx + 1 };
            i = i + 1;
        }
        let next = self.tail + k;
        let ghost vals = values@.subrange(0, k as int);
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let ghost th = s.tail.msgs();
            let ghost n = th.len();
            proof {
                s.prod.agree(self.g.borrow());
            }
            self.rb.tail.0.store_release(Tracked(&mut s.tail), Tracked(self.tid.borrow_mut()), next);
            let ghost old_cells = s.cells;
            let ghost old_q = s.q@;
            let ghost pg = s.prod@;
            let ghost cg = s.cons@;
            proof {
                lemma_stored(tid0, c.tail_id, n, self.tid@.view());
                lemma_view_le_trans(pg.tview, tid0, self.tid@.view());
                let ghost w = written;
                let ghost hi = t0 + k as nat;
                assert(hi == next as nat);
                publish_range(written, &mut s.cells, t0, hi, self.tid.borrow());
                s.prod.update(self.g.borrow_mut(), ProdGhost { tail: next as nat, tidx: n, tview: self.tid@.view(), ..pg });
                assert(seen_by(old_cells, cg.tail_cache, t0, pg.tview)) by {
                    assert(seen_by(old_cells, cg.tail_cache, th[pg.tidx as int].val as nat, th[pg.tidx as int].view));
                }
                lemma_publish_tail(old_cells, s.cells, th, s.tail.msgs(), cg.tail_cache, t0, k as nat, pg.tview, self.tid@.view());
                lemma_seen_frame(old_cells, s.cells, t0, hi, pg.head_cache + c.cap, c.cap, s.head.msgs());
                lemma_push_frame(c, s.cells, old_cells, w, values@, old_q, cg.tail_cache, cg.head, pg.head_cache, t0, k as nat);
            }
            let tracked au = au_opt.tracked_take();
            try_open_atomic_update!(au, x => {
                let tracked mut x = x;
                proof {
                    s.q.agree(&x);
                    s.q.update(&mut x, old_q + vals);
                    assert(x@ == old_q + values@.subrange(0, x@.len() - old_q.len()));
                }
                Tracked(Commit(x))
            });
            proof {
                assert(s.q@.subrange(0, cg.tail_cache - cg.head) =~= old_q.subrange(0, cg.tail_cache - cg.head));
            }
        });
        self.tail = next;
        self.idx = idx;
        k as usize
    }
}

impl<T> Consumer<T> {
    /// Moves up to `max` of the oldest values to the end of `out`, with one
    /// index store for the whole batch. Returns how many were moved: none
    /// only if `max` is zero or the queue was empty.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    pub fn pop_into(&mut self, out: &mut Vec<T>, max: usize) -> (n: usize)
        atomically (au) {
            type PopIntoPred,
            (x: QueueView<T>) -> (y: Commit<QueueView<T>>),
            requires
                x.id() == self.qid(),
            ensures
                y@.id() == x.id(),
                y@@.len() <= x@.len(),
                x@.len() - y@@.len() <= max,
                y@@ == x@.subrange(x@.len() - y@@.len(), x@.len() as int),
                max > 0 && x@.len() > 0 ==> y@@.len() < x@.len(),
            outer_mask any / [this.ns()],
        },
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).qid() == old(self).qid(),
            final(self).ns() == old(self).ns(),
            n == x@.len() - y@@.len(),
            final(out)@ == old(out)@ + x@.subrange(0, n as int),
    {
        let tracked mut au_opt = Some(au);
        let ghost c = self.rb.consts();
        let ghost out0 = out@;
        if self.head == self.tail_cache || ((self.tail_cache - self.head) as usize) < max {
            // The cached tail offers less than asked for: look again.
            self.refresh();
        }
        if self.head == self.tail_cache {
            // Still empty by an acquire load, which may be stale: read the
            // latest tail with a read-modify-write.
            let tail;
            open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
                let ghost tid0 = self.tid@.view();
                let ghost th = s.tail.msgs();
                proof {
                    s.tail.nonempty_lemma();
                    s.cons.agree(self.g.borrow());
                }
                tail = self.rb.tail.0.fetch_add_acqrel(Tracked(&mut s.tail), Tracked(self.tid.borrow_mut()), 0);
                proof {
                    let ghost last = th.last();
                    lemma_acquired(tid0, last.view, c.tail_id, th.len(), self.tid@.view());
                    lemma_view_le_trans(s.cons@.hview, tid0, self.tid@.view());
                    assert(s.tail.msgs() == th.push(Msg { val: last.val, view: self.tid@.view() }));
                    lemma_rmw_seen_tail(s.cells, s.cons@.tail_cache, th, s.tail.msgs(), self.tid@.view());
                    assert(tail as nat == s.prod@.tail);
                    assert(seen_by(s.cells, self.tail_cache as nat, tail as nat, self.tid@.view())) by {
                        assert(seen_by(s.cells, s.cons@.tail_cache, th[th.len() - 1].val as nat, th[th.len() - 1].view));
                        assert forall|p: nat| self.tail_cache <= p < tail implies (#[trigger] s.cells[p]).view().le(self.tid@.view()) by {
                            lemma_view_le_trans(s.cells[p].view(), last.view, self.tid@.view());
                        }
                    }
                    self.claim(&mut s, c, tail as nat);
                }
                if tail == self.head {
                    // Empty: this read is where `pop_into` fails.
                    let tracked au = au_opt.tracked_take();
                    try_open_atomic_update!(au, x => {
                        proof {
                            s.q.agree(&x);
                            assert(x@ =~= x@.subrange(0, x@.len() as int));
                        }
                        Tracked(Commit(x))
                    });
                }
            });
            if tail == self.head {
                return 0;
            }
            self.tail_cache = tail;
        }
        assert(self.head < self.tail_cache);
        let avail = self.tail_cache - self.head;
        let k: u64 = if (max as u64) < avail { max as u64 } else { avail };
        let ghost h0 = self.head as nat;
        let ghost held = self.g@@.held;
        let (idx, Tracked(freed)) = self.take_slots(out, k);
        let next = self.head + k;
        let ghost new_held = held.subrange(k as int, held.len() as int);
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = self.tid@.view();
            let ghost hh = s.head.msgs();
            let ghost n = hh.len();
            proof {
                s.cons.agree(self.g.borrow());
            }
            self.rb.head.0.store_release(Tracked(&mut s.head), Tracked(self.tid.borrow_mut()), next);
            let ghost old_cells = s.cells;
            let ghost old_q = s.q@;
            let ghost pg = s.prod@;
            let ghost cg = s.cons@;
            proof {
                lemma_stored(tid0, c.head_id, n, self.tid@.view());
                lemma_view_le_trans(cg.hview, tid0, self.tid@.view());
                let ghost f = freed;
                let ghost lo = h0 + c.cap;
                let ghost hi = h0 + k as nat + c.cap;
                publish_range(freed, &mut s.cells, lo, hi, self.tid.borrow());
                assert forall|p: nat| #![trigger s.cells.dom().contains(p)] h0 + c.cap <= p < h0 + k as nat + c.cap implies s.cells.dom().contains(p) && s.cells[p].view() == self.tid@.view() by {
                    assert(lo <= p < hi);
                    assert(s.cells.dom().contains(p));
                    assert(s.cells[p].view() == self.tid@.view());
                }
                let ghost cells1 = s.cells;
                let ghost kn = k as nat;
                assert forall|p: nat| #![trigger cells1.dom().contains(p)] h0 + c.cap <= p < h0 + kn + c.cap implies cells1.dom().contains(p) && cells1[p].value() == f[p] by {
                    assert(lo <= p < hi);
                    assert(s.cells.dom().contains(p));
                    assert(s.cells[p].value() == f[p]);
                }
                assert(same_outside(cells1, old_cells, h0 + c.cap, h0 + kn + c.cap));
                lemma_pop_frame(c, cells1, old_cells, f, old_q, cg.tail_cache, pg.tail, pg.head_cache, h0, kn);
                assert(old_q.subrange(0, k as int) =~= held.subrange(0, k as int));
                assert(seen_by(old_cells, pg.head_cache + c.cap, h0 + c.cap, cg.hview)) by {
                    assert(seen_by(old_cells, pg.head_cache + c.cap, (hh[cg.hidx as int].val + c.cap) as nat, hh[cg.hidx as int].view));
                }
                assert(same_outside(s.cells, old_cells, h0 + c.cap, h0 + k as nat + c.cap));
                lemma_publish_head(old_cells, s.cells, hh, s.head.msgs(), pg.head_cache + c.cap, h0, k as nat, c.cap, cg.hview, self.tid@.view());
                lemma_seen_frame_above(old_cells, s.cells, lo, hi, cg.tail_cache, s.tail.msgs());
                s.cons.update(self.g.borrow_mut(), ConsGhost {
                    head: next as nat,
                    held: new_held,
                    hidx: n,
                    hview: self.tid@.view(),
                    ..cg
                });
            }
            let tracked au = au_opt.tracked_take();
            try_open_atomic_update!(au, x => {
                let tracked mut x = x;
                proof {
                    s.q.agree(&x);
                    s.q.update(&mut x, old_q.subrange(k as int, old_q.len() as int));
                }
                Tracked(Commit(x))
            });
            proof {
                assert(s.q@.subrange(0, s.cons@.tail_cache - s.cons@.head) =~= new_held);
            }
        });
        proof {
            let ghost nn = next as nat;
            let ghost tcn = self.tail_cache as nat;
            assert forall|p: nat| nn <= p < tcn implies {
                &&& #[trigger] self.perms@.dom().contains(p)
                &&& slot_ok(c, p, self.perms@[p])
                &&& self.perms@[p].is_init()
                &&& self.perms@[p].value() == new_held[p - nn]
            } by {
                assert(h0 + k as nat <= p);
                assert(self.perms@.dom().contains(p));
                assert(new_held[p - nn] == held[p - h0]);
            }
            assert(full_perms(self.perms@, c, nn, tcn, new_held, nn));
        }
        self.head = next;
        self.idx = idx;
        k as usize
    }
}

/// Every slot in `[lo, hi)` is initialized, with its permission in `m`.
pub open spec fn init_perms<T>(m: Map<nat, PointsTo<T>>, c: Consts, lo: nat, hi: nat) -> bool {
    forall|p: nat|
        lo <= p < hi ==> {
            &&& #[trigger] m.dom().contains(p)
            &&& slot_ok(c, p, m[p])
            &&& m[p].is_init()
        }
}

/// Drops the values in the slots `[lo, hi)`.
#[verifier::spinoff_prover]
fn drain<T>(rb: &RingBuffer<T>, Tracked(perms): Tracked<Map<nat, PointsTo<T>>>, lo: u64, hi: u64)
    requires
        rb.wf(),
        lo <= hi,
        init_perms(perms, rb.consts(), lo as nat, hi as nat),
{
    let ghost c = rb.consts();
    let tracked mut perms = perms;
    let mut p = lo;
    let mut idx = lo % rb.cap;
    while p < hi
        invariant
            rb.wf(),
            c == rb.consts(),
            lo <= p <= hi,
            idx as nat == p as nat % c.cap,
            init_perms(perms, c, p as nat, hi as nat),
        decreases hi - p,
    {
        let ghost pp = p as nat;
        let ghost pre = perms;
        assert(perms.dom().contains(pp));
        assert(slot_ok(c, pp, perms[pp]) && perms[pp].is_init());
        let tracked mut perm = perms.tracked_remove(pp);
        assert(idx < rb.cap) by {
            vstd::arithmetic::div_mod::lemma_mod_bound(pp as int, c.cap as int);
        }
        assert(rb.buf@[idx as int].id() == c.cells[idx as int]);
        let cell = &rb.buf[idx as usize];
        // Dropped at the end of this iteration.
        let _v = cell.take(Tracked(&mut perm));
        proof {
            lemma_mod_next(pp, c.cap);
            assert forall|q: nat| pp + 1 <= q < hi implies {
                &&& #[trigger] perms.dom().contains(q)
                &&& slot_ok(c, q, perms[q])
                &&& perms[q].is_init()
            } by {
                assert(pre.dom().contains(q));
            }
        }
        p = p + 1;
        idx = if idx + 1 == rb.cap { 0 } else { idx + 1 };
    }
}

proof fn lemma_seen_mono<T>(m: Map<nat, Published<PointsTo<T>>>, lo: nat, hi: nat, a: RaView, b: RaView)
    requires
        seen_by(m, lo, hi, a),
        a.le(b),
    ensures
        seen_by(m, lo, hi, b),
{
    assert forall|p: nat| lo <= p < hi implies (#[trigger] m[p]).view().le(b) by {
        lemma_view_le_trans(m[p].view(), a, b);
    }
}

/// Acquires the published full slots `[lo, hi)` as plain initialized slots.
proof fn acquire_full<T>(tracked m: &mut Map<nat, Published<PointsTo<T>>>, c: Consts, lo: nat, hi: nat, q: Seq<T>, base: nat, tracked tid: &Tid) -> (tracked r: Map<nat, PointsTo<T>>)
    requires
        full_pub(*old(m), c, lo, hi, q, base),
        seen_by(*old(m), lo, hi, tid.view()),
    ensures
        init_perms(r, c, lo, hi),
        forall|p: nat| #[trigger] r.dom().contains(p) ==> lo <= p < hi,
{
    let ghost m0 = *m;
    let tracked r = acquire_range(m, lo, hi, tid);
    assert forall|p: nat| lo <= p < hi implies {
        &&& #[trigger] r.dom().contains(p)
        &&& slot_ok(c, p, r[p])
        &&& r[p].is_init()
    } by {
        assert(m0.dom().contains(p));
    }
    r
}

impl<T> Producer<T> {
    /// Hands the producer's state to the shared state when it is dropped.
    /// If the consumer is already gone, drops the values left in the queue.
    #[verifier::spinoff_prover]
    fn leave(&mut self)
        requires
            old(self).wf(),
    {
        let ghost c = self.rb.consts();
        let tracked mut to;
        let tracked mut g;
        proof {
            let tracked (_a, dummy) = GhostVarAuth::new(self.g@@);
            g = dummy;
            vstd::modes::tracked_swap(self.g.borrow_mut(), &mut g);
        }
        let (_dummy_cell, Tracked(dp)) = PCell::<u64>::empty();
        proof {
            to = dp;
            vstd::modes::tracked_swap(self.tail_out.borrow_mut(), &mut to);
        }
        self.rb.tail_out.put(Tracked(&mut to), self.tail);
        let tracked mut tid = self.tid.borrow().dup();
        let tracked mut loot: Map<nat, PointsTo<T>> = Map::tracked_empty();
        let tracked mut head_perm: Option<PointsTo<u64>> = None;
        let old;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = tid.view();
            let ghost rl = s.refs.last();
            proof {
                s.refs.nonempty_lemma();
                s.prod.agree(&g);
            }
            old = self.rb.refs.fetch_sub_acqrel(Tracked(&mut s.refs), Tracked(&mut tid), 1);
            proof {
                let ghost pg = s.prod@;
                let ghost cg = s.cons@;
                lemma_acquired(tid0, rl.view, c.refs_id, (s.refs.msgs().len() - 1) as nat, tid.view());
                lemma_view_le_trans(pg.tview, tid0, tid.view());
                assert(!s.dead);
                if old == 1 {
                    // The consumer has left: take everything out.
                    assert(cg.left);
                    let tracked cl = s.cons_left.tracked_take();
                    let tracked ConsLeft { g: _, held: mut held, head_out, view: _ } = cl;
                    lemma_view_le_trans(cl.view, rl.view, tid.view());
                    lemma_seen_mono(held, cg.head, cg.tail_cache, cl.view, tid.view());
                    loot = acquire_full(&mut held, c, cg.head, cg.tail_cache, cg.held, cg.head, &tid);
                    let ghost th = s.tail.msgs();
                    assert(seen_by(s.cells, cg.tail_cache, th[pg.tidx as int].val as nat, th[pg.tidx as int].view));
                    lemma_seen_mono(s.cells, cg.tail_cache, pg.tail, pg.tview, tid.view());
                    let tracked rest = acquire_full(&mut s.cells, c, cg.tail_cache, pg.tail, s.q@, cg.head, &tid);
                    let ghost l0 = loot;
                    loot.tracked_union_prefer_right(rest);
                    assert(init_perms(loot, c, cg.head, pg.tail)) by {
                        assert forall|p: nat| cg.head <= p < pg.tail implies {
                            &&& #[trigger] loot.dom().contains(p)
                            &&& slot_ok(c, p, loot[p])
                            &&& loot[p].is_init()
                        } by {
                            if p < cg.tail_cache {
                                assert(l0.dom().contains(p));
                                assert(!rest.dom().contains(p) || p >= cg.tail_cache);
                            } else {
                                assert(rest.dom().contains(p));
                            }
                        }
                    }
                    lemma_view_le_trans(head_out.view(), cl.view, tid.view());
                    head_perm = Some(head_out.acquire(&tid));
                    s.prod.update(&mut g, ProdGhost { left: true, ..pg });
                    s.dead = true;
                } else {
                    let tracked pub_to = Published::publish(to, &tid);
                    s.prod.update(&mut g, ProdGhost { left: true, ..pg });
                    s.prod_left = Some(ProdLeft { g, tail_out: pub_to });
                    lemma_view_le_refl(tid.view());
                }
            }
        });
        if old == 1 {
            let tracked mut hp = head_perm.tracked_unwrap();
            let head = self.rb.head_out.take(Tracked(&mut hp));
            drain(&self.rb, Tracked(loot), head, self.tail);
        }
    }
}

impl<T> Consumer<T> {
    /// Hands the consumer's state and slots to the shared state when it is
    /// dropped. If the producer is already gone, drops the values left in
    /// the queue.
    #[verifier::spinoff_prover]
    fn leave(&mut self)
        requires
            old(self).wf(),
    {
        let ghost c = self.rb.consts();
        let tracked mut ho;
        let tracked mut g;
        let tracked mut perms = Map::tracked_empty();
        proof {
            let tracked (_a, dummy) = GhostVarAuth::new(self.g@@);
            g = dummy;
            vstd::modes::tracked_swap(self.g.borrow_mut(), &mut g);
            vstd::modes::tracked_swap(self.perms.borrow_mut(), &mut perms);
        }
        let (_dummy_cell, Tracked(dp)) = PCell::<u64>::empty();
        proof {
            ho = dp;
            vstd::modes::tracked_swap(self.head_out.borrow_mut(), &mut ho);
        }
        self.rb.head_out.put(Tracked(&mut ho), self.head);
        let tracked mut tid = self.tid.borrow().dup();
        let tracked mut loot: Map<nat, PointsTo<T>> = Map::tracked_empty();
        let tracked mut tail_perm: Option<PointsTo<u64>> = None;
        let ghost head = self.head as nat;
        let ghost tc = self.tail_cache as nat;
        let old;
        open_atomic_invariant!(self.rb.inv.borrow().inner() => s => {
            let ghost tid0 = tid.view();
            let ghost rl = s.refs.last();
            proof {
                s.refs.nonempty_lemma();
                s.cons.agree(&g);
            }
            old = self.rb.refs.fetch_sub_acqrel(Tracked(&mut s.refs), Tracked(&mut tid), 1);
            proof {
                let ghost pg = s.prod@;
                let ghost cg = s.cons@;
                lemma_acquired(tid0, rl.view, c.refs_id, (s.refs.msgs().len() - 1) as nat, tid.view());
                lemma_view_le_trans(cg.hview, tid0, tid.view());
                assert(!s.dead);
                if old == 1 {
                    // The producer has left: take everything out.
                    assert(pg.left);
                    let tracked pl = s.prod_left.tracked_take();
                    let tracked ProdLeft { g: _, tail_out } = pl;
                    lemma_view_le_trans(pg.tview, rl.view, tid.view());
                    let ghost th = s.tail.msgs();
                    assert(seen_by(s.cells, cg.tail_cache, th[pg.tidx as int].val as nat, th[pg.tidx as int].view));
                    lemma_seen_mono(s.cells, cg.tail_cache, pg.tail, pg.tview, tid.view());
                    let tracked rest = acquire_full(&mut s.cells, c, cg.tail_cache, pg.tail, s.q@, cg.head, &tid);
                    let ghost p0 = perms;
                    loot = perms;
                    loot.tracked_union_prefer_right(rest);
                    assert(init_perms(loot, c, cg.head, pg.tail)) by {
                        assert forall|p: nat| cg.head <= p < pg.tail implies {
                            &&& #[trigger] loot.dom().contains(p)
                            &&& slot_ok(c, p, loot[p])
                            &&& loot[p].is_init()
                        } by {
                            if p < cg.tail_cache {
                                assert(p0.dom().contains(p));
                                assert(!rest.dom().contains(p) || p >= cg.tail_cache);
                            } else {
                                assert(rest.dom().contains(p));
                            }
                        }
                    }
                    lemma_view_le_trans(tail_out.view(), rl.view, tid.view());
                    tail_perm = Some(tail_out.acquire(&tid));
                    s.cons.update(&mut g, ConsGhost { left: true, ..cg });
                    s.dead = true;
                } else {
                    let tracked mut held: Map<nat, Published<PointsTo<T>>> = Map::tracked_empty();
                    let ghost p0 = perms;
                    publish_range(perms, &mut held, head, tc, &tid);
                    assert(full_pub(held, c, head, tc, cg.held, head)) by {
                        assert forall|p: nat| head <= p < tc implies {
                            &&& #[trigger] held.dom().contains(p)
                            &&& slot_ok(c, p, held[p].value())
                            &&& held[p].value().is_init()
                            &&& held[p].value().value() == cg.held[p - head]
                        } by {
                            assert(p0.dom().contains(p));
                            assert(held.dom().contains(p));
                        }
                    }
                    assert(seen_by(held, head, tc, tid.view())) by {
                        assert forall|p: nat| head <= p < tc implies (#[trigger] held[p]).view().le(tid.view()) by {
                            assert(held.dom().contains(p));
                            lemma_view_le_refl(tid.view());
                        }
                    }
                    lemma_view_le_refl(tid.view());
                    let tracked pub_ho = Published::publish(ho, &tid);
                    s.cons.update(&mut g, ConsGhost { left: true, ..cg });
                    s.cons_left = Some(ConsLeft { g, held, head_out: pub_ho, view: tid.view() });
                }
            }
        });
        if old == 1 {
            let tracked mut tp = tail_perm.tracked_unwrap();
            let tail = self.rb.tail_out.take(Tracked(&mut tp));
            drain(&self.rb, Tracked(loot), self.head, tail);
        }
    }
}

/// Creates a queue that holds up to `cap` values, and a view of its
/// (empty) contents.
#[verifier::spinoff_prover]
pub fn new<T>(cap: u64) -> (r: (Producer<T>, Consumer<T>, Tracked<QueueView<T>>))
    requires
        cap > 0,
    ensures
        r.0.wf(),
        r.1.wf(),
        r.0.qid() == r.1.qid(),
        r.0.qid() == r.2@.id(),
        r.0.ns() == r.1.ns(),
        r.0.capacity_spec() == cap,
        r.2@@ == Seq::<T>::empty(),
{
    let mut buf: Vec<PCell<T>> = Vec::with_capacity(cap as usize);
    // The producer starts out holding every slot, at positions [0, cap).
    let tracked mut pperms: Map<nat, PointsTo<T>> = Map::tracked_empty();
    let ghost mut ids: Seq<CellId> = Seq::empty();
    let mut i: u64 = 0;
    while i < cap
        invariant
            i <= cap,
            buf@.len() == i,
            ids.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] buf@[j].id() == ids[j],
            forall|p: nat| p < i ==> {
                &&& #[trigger] pperms.dom().contains(p)
                &&& pperms[p].id() == ids[p as int]
                &&& pperms[p].is_uninit()
            },
        decreases cap - i,
    {
        let (cell, Tracked(perm)) = PCell::empty();
        proof {
            let ghost old_ids = ids;
            let ghost old_pperms = pperms;
            pperms.tracked_insert(i as nat, perm);
            ids = ids.push(cell.id());
            assert forall|p: nat| p < i + 1 implies {
                &&& #[trigger] pperms.dom().contains(p)
                &&& pperms[p].id() == ids[p as int]
                &&& pperms[p].is_uninit()
            } by {
                if p < i {
                    assert(old_pperms.dom().contains(p));
                    assert(ids[p as int] == old_ids[p as int]);
                }
            }
        }
        buf.push(cell);
        i = i + 1;
    }
    let tracked mut tid = Tid::new();
    let (head, Tracked(hh)) = RaU64::new(0, Tracked(&mut tid));
    let ghost hview = tid.view();
    let (tail, Tracked(th)) = RaU64::new(0, Tracked(&mut tid));
    let ghost tview = tid.view();
    let (refs, Tracked(rh)) = RaU64::new(2, Tracked(&mut tid));
    proof {
        lemma_view_join(hview, RaView::single(tail.id(), 0));
        lemma_view_join(tview, RaView::single(refs.id(), 0));
        lemma_view_le_trans(hview, tview, tid.view());
    }
    let (tail_out, Tracked(top)) = PCell::<u64>::empty();
    let (head_out, Tracked(hop)) = PCell::<u64>::empty();
    let tracked (qa, qv) = GhostVarAuth::new(Seq::<T>::empty());
    let tracked (pa, pv) = GhostVarAuth::new(ProdGhost { tail: 0, head_cache: 0, tidx: 0, tview, left: false });
    let tracked (ca, cv) = GhostVarAuth::new(ConsGhost { head: 0, tail_cache: 0, held: Seq::empty(), hidx: 0, hview, left: false });
    let ghost c = Consts {
        cap: cap as nat,
        head_id: head.id(),
        tail_id: tail.id(),
        refs_id: refs.id(),
        cells: ids,
        tail_out: tail_out.id(),
        head_out: head_out.id(),
        q_id: qa.id(),
        prod_id: pa.id(),
        cons_id: ca.id(),
    };
    proof {
        assert(empty_perms(pperms, c, 0, cap as nat)) by {
            assert forall|p: nat| 0 <= p < cap implies {
                &&& #[trigger] pperms.dom().contains(p)
                &&& slot_ok(c, p, pperms[p])
                &&& pperms[p].is_uninit()
            } by {
                vstd::arithmetic::div_mod::lemma_small_mod(p, cap as nat);
            }
        }
    }
    let tracked cells: Map<nat, Published<PointsTo<T>>> = Map::tracked_empty();
    let tracked s = Shared {
        head: hh,
        tail: th,
        refs: rh,
        q: qa,
        prod: pa,
        cons: ca,
        cells,
        prod_left: None,
        cons_left: None,
        dead: false,
    };
    proof {
        assert(s.tail.msgs()[0] == Msg { val: 0, view: tview });
        assert(s.cons@.held =~= s.q@.subrange(0, 0));
        assert(full_pub(s.cells, c, 0, 0, s.q@, 0));
        assert(empty_pub(s.cells, c, cap as nat, cap as nat));
    }
    let tracked inv = ObjInvariant::<_, _, SpscPred>::new(c, s, 0x5b5c);
    let rb = RingBuffer {
        head: CachePadded(head),
        tail: CachePadded(tail),
        refs,
        buf,
        tail_out,
        head_out,
        cap,
        inv: Tracked(inv),
    };
    assert(rb.wf());
    let rb = Arc::new(rb);
    let rb2 = arc_clone(&rb);
    let tracked ctid = tid.dup();
    let p = Producer {
        rb,
        tail: 0,
        idx: 0,
        limit: cap,
        g: Tracked(pv),
        perms: Tracked(pperms),
        tail_out: Tracked(top),
        tid: Tracked(tid),
    };
    let tracked cperms: Map<nat, PointsTo<T>> = Map::tracked_empty();
    let cons = Consumer {
        rb: rb2,
        head: 0,
        idx: 0,
        tail_cache: 0,
        g: Tracked(cv),
        perms: Tracked(cperms),
        head_out: Tracked(hop),
        tid: Tracked(ctid),
    };
    assert(full_perms(cons.perms@, c, 0, 0, Seq::empty(), 0));
    (p, cons, Tracked(qv))
}

} // verus!

impl<T> Drop for Producer<T> {
    fn drop(&mut self) {
        self.leave();
    }
}

impl<T> Drop for Consumer<T> {
    fn drop(&mut self) {
        self.leave();
    }
}

// SAFETY: `Producer` and `Consumer` hold a `Tid`, which is `!Send` so that
// it can only reach another thread through a synchronizing transfer. Moving
// an owned `Producer` or `Consumer` to another thread is such a transfer: it
// happens by spawning, joining, a channel or a lock, each of which creates
// happens-before, so the receiving thread's view covers the sender's and the
// `Tid`'s lower bound stays true (TRUST.md, "A `Tid` stays with its thread").
// The bounds are those Rust would infer for the other fields.
unsafe impl<T> Send for Producer<T> where
    Arc<RingBuffer<T>>: Send,
    Tracked<GhostVar<ProdGhost>>: Send,
    Tracked<Map<nat, PointsTo<T>>>: Send,
    Tracked<PointsTo<u64>>: Send,
{
}

// SAFETY: as for `Producer`.
unsafe impl<T> Send for Consumer<T> where
    Arc<RingBuffer<T>>: Send,
    Tracked<GhostVar<ConsGhost<T>>>: Send,
    Tracked<Map<nat, PointsTo<T>>>: Send,
    Tracked<PointsTo<u64>>: Send,
{
}
