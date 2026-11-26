//! A bounded multi-producer multi-consumer queue: the algorithm of
//! crossbeam's `ArrayQueue` (Dmitry Vyukov's bounded queue, with crossbeam's
//! linearizable emptiness and fullness checks).
//!
//! Each slot carries a stamp. A position `p` is stored packed as
//! `(p / cap) * one_lap + p % cap`, where `one_lap` is a power of two above
//! `cap`, so the slot index is a mask. A slot whose stamp is `pk(p)` is free
//! for the push at position `p`; `pk(p) + 1` means it holds the value pushed
//! at `p`; the pop of `p` then sets it to `pk(p + cap)`.
//!
//! Unlike crossbeam, positions never wrap: the counters are 64 bits and the
//! queue aborts if one would overflow (after at least 2^62 pushes, whatever the capacity). This is
//! what makes the compare-and-swaps on `head` and `tail` ABA-free in the
//! proof; crossbeam lets them wrap.
//!
//! What is proven:
//! - memory safety: a slot's value is written only by the one pusher whose
//!   compare-and-swap claimed that position, and read only by the one popper
//!   that claimed it after the value was written;
//! - linearizability: `push` and `pop` are logically atomic with respect to
//!   an abstract `Seq<T>` held through a [`QueueView`]. A push takes effect
//!   at its `tail` compare-and-swap, or, if the queue is full, at the `head`
//!   load that shows it full; a pop at its `head` compare-and-swap, or, if
//!   the queue is empty, at the `tail` load that shows it empty.

// Each `atomically` clause defines a predicate struct (`XPred`) that the
// `verus!` macro gives no docs and no place to attach one. Every other item
// here is documented.
#![allow(missing_docs)]
use crate::model::*;
use crate::mono::*;
use crate::progress::queue::{P, Ph, St};
#[cfg(verus_only)]
use crate::progress::queue::{go, rank, ret, sc_step, stale_step, step};
use crate::ra::*;
use crate::util::{exhausted, Backoff, CachePadded};
use vstd::atomic::Commit;
use vstd::try_open_atomic_update;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

broadcast use {vstd::arithmetic::power2::lemma_pow2_unfold, vstd::set_lib::range_set_properties};

/// The namespace of every queue's invariant. A client that keeps its own
/// invariant open across a queue operation's linearization point uses a
/// different one.
pub open spec const QUEUE_NS: int = 0x5b4d;

/// A client's view of the queue's contents, oldest first.
pub type QueueView<T> = GhostVar<Seq<T>>;

/// Where the slot for a position is in its life.
pub ghost enum Phase {
    /// Waiting for the push at `pos`; its cell is uninitialized and shared.
    Free,
    /// A pusher has claimed `pos` and holds the cell.
    Claimed,
    /// Holds the value pushed at `pos`; the cell is shared.
    Full,
    /// A popper has claimed `pos` and holds the cell.
    Taken,
}

/// The ghost state of one slot.
pub ghost struct SlotG {
    /// The position the slot is for now.
    pub pos: nat,
    /// Where that position's push and pop are.
    pub phase: Phase,
}

/// What a thread that holds a slot is obliged to do with it.
pub ghost enum Ticket<T> {
    /// Write `v` into the slot claimed for position `pos`.
    Push {
        /// The position.
        pos: nat,
        /// The value.
        v: T,
    },
    /// Take the value out of the slot claimed for position `pos`.
    Pop {
        /// The position.
        pos: nat,
    },
}

/// The queue's constants: its capacity, how positions are packed, and the ids of its atomics, cells and ghost resources.
pub ghost struct Consts {
    /// The capacity.
    pub cap: nat,
    /// `one_lap`: a power of two above `cap`, the stride of a packed position's lap.
    pub lap: nat,
    /// `lap == 2^shift`.
    pub shift: nat,
    /// The id of the `head` atomic.
    pub head_id: int,
    /// The id of the `tail` atomic.
    pub tail_id: int,
    /// The ids of the slots' stamp atomics.
    pub stamp_ids: Seq<int>,
    /// The ids of the slots' cells.
    pub cells: Seq<CellId>,
    /// The location of the abstract queue (`QueueView`).
    pub q_id: Loc,
    /// The location of the tickets.
    pub tk_id: Loc,
    /// The location of `head`'s monotonic counter.
    pub head_mono: Loc,
    /// The location of `tail`'s monotonic counter.
    pub tail_mono: Loc,
    /// The locations of the stamps' monotonic counters.
    pub stamp_mono: Seq<Loc>,
    /// The location of the progress model.
    pub model: Loc,
}

pub open spec fn pk(c: Consts, p: nat) -> nat {
    (p / c.cap) * c.lap + p % c.cap
}

pub open spec fn consts_ok(c: Consts) -> bool {
    &&& 0 < c.cap < c.lap
    &&& c.lap == vstd::arithmetic::power2::pow2(c.shift)
    &&& c.shift < 61
    &&& c.lap < 0x2000_0000_0000_0000
    &&& c.stamp_ids.len() == c.cap
    &&& c.cells.len() == c.cap
    &&& c.stamp_mono.len() == c.cap
}

/// What the queue's invariant owns: the histories of every atomic, the abstract queue, and the cells no thread holds.
pub tracked struct Shared<T> {
    /// The history of `head`.
    pub head: Hist,
    /// The history of `tail`.
    pub tail: Hist,
    /// The authority of `head`'s monotonic counter.
    pub hm: MonoAuth,
    /// The authority of `tail`'s monotonic counter.
    pub tm: MonoAuth,
    /// The history of each slot's stamp.
    pub stamps: Map<nat, Hist>,
    /// The authority of each stamp's monotonic counter.
    pub sm: Map<nat, MonoAuth>,
    /// The cells of free and full slots, each published at the view of the
    /// stamp store that made it free or full.
    pub cells: Map<nat, Published<PointsTo<T>>>,
    /// The authoritative abstract queue.
    pub q: GhostVarAuth<Seq<T>>,
    /// The authority over the tickets of threads that hold a slot.
    pub tk: GhostMapAuth<nat, Ticket<T>>,
    /// The head position.
    pub hd: Ghost<nat>,
    /// The tail position.
    pub tl: Ghost<nat>,
    /// Each slot's ghost state.
    pub slots: Ghost<Map<nat, SlotG>>,
    /// The value pushed at each position not yet popped.
    pub vals: Ghost<Map<nat, T>>,
    /// The progress model, which the code follows step by step.
    pub model: Model<P>,
}

// Histories, ghost resources and published permissions only.
impl<T> Objective for Shared<T> {}

/// The packed position `x` decoded.
pub open spec fn unpk(c: Consts, x: nat) -> nat {
    (x / c.lap) * c.cap + x % c.lap
}

/// The history of `head` or `tail`: every message holds a packed position
/// no later than the current one, `cur`.
pub open spec fn pos_hist(c: Consts, h: Hist, cur: nat) -> bool {
    &&& h.msgs().len() > 0
    &&& h.last().val == pk(c, cur)
    &&& forall|k: int| 0 <= k < h.msgs().len() ==> {
        &&& pk(c, unpk(c, #[trigger] h.msgs()[k].val as nat)) == h.msgs()[k].val
        &&& unpk(c, h.msgs()[k].val as nat) <= cur
    }
}

/// A stamp's history: no message is above the current value `st`, and every
/// message holding `st` carries a view that covers `v`.
pub open spec fn stamp_hist(h: Hist, st: nat, v: RaView) -> bool {
    &&& h.msgs().len() > 0
    &&& h.last().val == st
    &&& forall|k: int| 0 <= k < h.msgs().len() ==> #[trigger] h.msgs()[k].val <= st
    &&& forall|k: int| 0 <= k < h.msgs().len() && h.msgs()[k].val == st ==> v.le(#[trigger] h.msgs()[k].view)
}

pub open spec fn abs_queue<T>(vals: Map<nat, T>, h: nat, t: nat) -> Seq<T> {
    Seq::new((t - h) as nat, |k: int| vals[(h + k) as nat])
}

pub open spec fn slot_inv<T>(c: Consts, s: Shared<T>, i: nat) -> bool {
    let h = s.hd@;
    let t = s.tl@;
    let g = s.slots@[i];
    let st = s.stamps[i].last().val as nat;
    &&& s.slots@.contains_key(i)
    &&& s.stamps.contains_key(i)
    &&& s.sm.contains_key(i)
    &&& s.stamps[i].loc() == c.stamp_ids[i as int]
    &&& s.stamps[i].msgs().len() > 0
    &&& forall|k: int| 0 <= k < s.stamps[i].msgs().len() ==> #[trigger] s.stamps[i].msgs()[k].val <= st
    &&& s.sm[i].wf()
    &&& s.sm[i].loc() == c.stamp_mono[i as int]
    &&& s.sm[i]@ == st
    &&& g.pos % c.cap == i
    &&& match g.phase {
        Phase::Free => {
            &&& st == pk(c, g.pos)
            &&& t <= g.pos < h + c.cap
            &&& s.cells.contains_key(i)
            &&& s.cells[i].value().id() == c.cells[i as int]
            &&& s.cells[i].value().is_uninit()
            &&& stamp_hist(s.stamps[i], st, s.cells[i].view())
            &&& !s.tk@.contains_key(i)
        },
        Phase::Claimed => {
            &&& st == pk(c, g.pos)
            &&& h <= g.pos < t
            &&& s.tk@.contains_key(i)
            &&& s.tk@[i] == Ticket::Push { pos: g.pos, v: s.vals@[g.pos] }
        },
        Phase::Full => {
            &&& st == pk(c, g.pos) + 1
            &&& h <= g.pos < t
            &&& s.cells.contains_key(i)
            &&& s.cells[i].value().id() == c.cells[i as int]
            &&& s.cells[i].value().is_init()
            &&& s.cells[i].value().value() == s.vals@[g.pos]
            &&& stamp_hist(s.stamps[i], st, s.cells[i].view())
            &&& !s.tk@.contains_key(i)
        },
        Phase::Taken => {
            &&& st == pk(c, g.pos) + 1
            &&& g.pos < h
            &&& t <= g.pos + c.cap
            &&& s.tk@.contains_key(i)
            &&& s.tk@[i] == Ticket::<T>::Pop { pos: g.pos }
        },
    }
}

/// A slot's stamp as the progress model's rank: `2p` while it is free for
/// (or being pushed at) position `p`, `2p + 1` while it holds (or is being
/// popped at) `p`.
pub open spec fn srank(g: SlotG) -> nat {
    match g.phase {
        Phase::Free | Phase::Claimed => 2 * g.pos,
        Phase::Full | Phase::Taken => 2 * g.pos + 1,
    }
}

/// The number of threads in each queue's model: any number (see
/// `model::Model::pool_nonempty`).
pub uninterp spec fn model_threads() -> nat;

/// The progress model's state matches the queue's ghost state.
pub open spec fn model_ok<T>(c: Consts, s: Shared<T>) -> bool {
    let m = s.model@;
    &&& s.model.wf()
    &&& s.model.loc() == c.model
    &&& s.model.n() == model_threads()
    &&& m.cap == c.cap
    &&& m.head == s.hd@
    &&& m.tail == s.tl@
    &&& m.st.len() == c.cap
    &&& forall|i: nat| i < c.cap ==> #[trigger] m.st[i as int] == srank(s.slots@[i])
}

/// The queue's invariant (see its `inv`).
pub struct QueuePred;

impl<T> InvariantPredicate<Consts, Shared<T>> for QueuePred {
    open spec fn inv(c: Consts, s: Shared<T>) -> bool {
        let h = s.hd@;
        let t = s.tl@;
        &&& consts_ok(c)
        &&& s.head.loc() == c.head_id
        &&& s.tail.loc() == c.tail_id
        &&& pos_hist(c, s.head, h)
        &&& pos_hist(c, s.tail, t)
        &&& s.hm.wf()
        &&& s.hm.loc() == c.head_mono
        &&& s.hm@ == pk(c, h)
        &&& s.tm.wf()
        &&& s.tm.loc() == c.tail_mono
        &&& s.tm@ == pk(c, t)
        &&& h <= t <= h + c.cap
        &&& (t / c.cap) * c.lap + 4 * c.lap <= u64::MAX
        &&& s.q.id() == c.q_id
        &&& s.q@ == abs_queue(s.vals@, h, t)
        &&& s.tk.id() == c.tk_id
        &&& forall|i: nat| i < c.cap ==> #[trigger] slot_inv(c, s, i)
        &&& model_ok(c, s)
    }
}

/// The token is for a thread of the queue's model, in phase `p`.
pub open spec fn tok_at(tok: Tok<P>, c: Consts, p: Ph) -> bool {
    tok.id() == c.model && tok.value() == p
}

/// Where a load of the tail that sees position `t` takes a thread.
pub open spec fn tail_next(p: Ph, t: nat) -> Ph {
    match p {
        Ph::PLoad => Ph::PStamp { a: t },
        Ph::QTail { a } => if t == a { Ph::QConfirm { a } } else { Ph::QLoad },
        Ph::LTail => Ph::LHead { a: t },
        Ph::LTail2 { a } => if t == a { Ph::Idle } else { Ph::LTail },
        _ => p,
    }
}

/// Where a load of the head that sees position `h` takes a thread.
pub open spec fn head_next(c: Consts, p: Ph, h: nat) -> Ph {
    match p {
        Ph::QLoad => Ph::QStamp { a: h },
        Ph::PHead { a } => if h + c.cap == a { Ph::PConfirm { a } } else { Ph::PLoad },
        Ph::LHead { a } => Ph::LTail2 { a },
        _ => p,
    }
}

/// Where a load of the stamp of position `a`'s slot that sees `v` takes
/// a thread: the code's tests on the packed stamp.
pub open spec fn stamp_next(c: Consts, p: Ph, v: nat) -> Ph {
    match p {
        Ph::PStamp { a } => if v == pk(c, a) {
            Ph::PCas { a }
        } else if pk(c, a) + 1 >= c.lap && v == pk(c, a) + 1 - c.lap {
            Ph::PHead { a }
        } else {
            Ph::PLoad
        },
        Ph::QStamp { a } => if v == pk(c, a) + 1 {
            Ph::QCas { a }
        } else if v == pk(c, a) {
            Ph::QTail { a }
        } else {
            Ph::QLoad
        },
        _ => p,
    }
}

/// What a stamp `v` read for position `a`'s slot says about the slot's
/// rank, given that no message is above the current stamp `st`.
proof fn lemma_stamp_rank(c: Consts, g: SlotG, st: nat, v: nat, a: nat)
    requires
        consts_ok(c),
        g.pos % c.cap == a % c.cap,
        st == (match g.phase {
            Phase::Free | Phase::Claimed => pk(c, g.pos),
            Phase::Full | Phase::Taken => pk(c, g.pos) + 1,
        }),
        v <= st,
    ensures
        v == pk(c, a) ==> srank(g) >= 2 * a,
        v == pk(c, a) + 1 ==> srank(g) >= 2 * a + 1,
        pk(c, a) + 1 >= c.lap && v == pk(c, a) + 1 - c.lap ==> a >= c.cap && srank(g) >= 2 * (a - c.cap) + 1,
{
    if g.pos < a {
        lemma_same_slot(c, g.pos, a);
    } else if g.pos > a {
        lemma_same_slot(c, a, g.pos);
    }
    if pk(c, a) + 1 >= c.lap && v == pk(c, a) + 1 - c.lap {
        if a < c.cap {
            lemma_pk_small(c, a);
        }
        let b = (a - c.cap) as nat;
        lemma_pk_cap(c, b);
        vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(b as int, c.cap as int);
        assert((b + c.cap) % c.cap == b % c.cap);
        if g.pos < b {
            lemma_same_slot(c, g.pos, b);
        } else if g.pos > b {
            lemma_same_slot(c, b, g.pos);
        }
    }
}

/// Packing is one to one.
proof fn lemma_pk_inj(c: Consts, p: nat, q: nat)
    requires
        consts_ok(c),
        pk(c, p) == pk(c, q),
    ensures
        p == q,
{
    if p < q {
        lemma_pk_mono(c, p, q);
    } else if q < p {
        lemma_pk_mono(c, q, p);
    }
}

/// The code's "full" test on packed positions is the model's.
proof fn lemma_full_test(c: Consts, h: nat, t: nat)
    requires
        consts_ok(c),
    ensures
        (pk(c, t) >= c.lap && pk(c, h) == pk(c, t) - c.lap) == (h + c.cap == t),
{
    lemma_pk_cap(c, h);
    if pk(c, t) >= c.lap && pk(c, h) == pk(c, t) - c.lap {
        lemma_pk_inj(c, h + c.cap, t);
    }
}

// ---------------------------------------------------------------------------
// Arithmetic on packed positions

proof fn lemma_div_mod(p: nat, cap: nat)
    requires
        cap > 0,
    ensures
        p == (p / cap) * cap + p % cap,
        p % cap < cap,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, cap as int);
    assert((p / cap) * cap == cap * (p / cap)) by (nonlinear_arith);
}

/// Splitting `p` as `a * cap + r` is unique.
proof fn lemma_split(p: nat, cap: nat, a: nat, r: nat)
    requires
        cap > 0,
        r < cap,
        p == a * cap + r,
    ensures
        p / cap == a,
        p % cap == r,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(p as int, cap as int, a as int, r as int);
}

pub proof fn lemma_pk_mono(c: Consts, p: nat, q: nat)
    requires
        consts_ok(c),
        p < q,
    ensures
        pk(c, p) < pk(c, q),
{
    lemma_div_mod(p, c.cap);
    lemma_div_mod(q, c.cap);
    let (a, r) = (p / c.cap, p % c.cap);
    let (b, s) = (q / c.cap, q % c.cap);
    if a < b {
        assert(a * c.lap + c.lap <= b * c.lap) by (nonlinear_arith)
            requires a < b;
    } else {
        assert(a == b) by (nonlinear_arith)
            requires p < q, p == a * c.cap + r, q == b * c.cap + s, r < c.cap, s < c.cap, b <= a, c.cap > 0;
    }
}

pub proof fn lemma_pk_cap(c: Consts, p: nat)
    requires
        consts_ok(c),
    ensures
        pk(c, p + c.cap) == pk(c, p) + c.lap,
{
    lemma_div_mod(p, c.cap);
    let (a, r) = (p / c.cap, p % c.cap);
    assert(p + c.cap == (a + 1) * c.cap + r) by (nonlinear_arith)
        requires p == a * c.cap + r;
    lemma_split(p + c.cap, c.cap, a + 1, r);
    assert((a + 1) * c.lap == a * c.lap + c.lap) by (nonlinear_arith);
}

/// Positions of the same slot are at least `cap` apart.
pub proof fn lemma_same_slot(c: Consts, p: nat, q: nat)
    requires
        consts_ok(c),
        p < q,
        p % c.cap == q % c.cap,
    ensures
        p + c.cap <= q,
        pk(c, p) + 1 < pk(c, q),
{
    lemma_div_mod(p, c.cap);
    lemma_div_mod(q, c.cap);
    let (a, r) = (p / c.cap, p % c.cap);
    let b = q / c.cap;
    assert(a < b) by (nonlinear_arith)
        requires p < q, p == a * c.cap + r, q == b * c.cap + r, c.cap > 0;
    assert(p + c.cap <= q) by (nonlinear_arith)
        requires a < b, p == a * c.cap + r, q == b * c.cap + r;
    if p + c.cap < q {
        lemma_pk_mono(c, p + c.cap, q);
    }
    lemma_pk_cap(c, p);
}

/// Decoding a packed position with a mask, and the packed successor.
pub proof fn lemma_decode(c: Consts, x: u64, mask: u64, p: nat)
    requires
        consts_ok(c),
        x as nat == pk(c, p),
        mask as nat == c.lap - 1,
    ensures
        (x & mask) as nat == p % c.cap,
        (x - (x & mask)) as nat == (p / c.cap) * c.lap,
        pk(c, p + 1) == if p % c.cap + 1 < c.cap { pk(c, p) + 1 } else { (p / c.cap) * c.lap + c.lap },
        ((p + 1) / c.cap) * c.lap == if p % c.cap + 1 < c.cap { (p / c.cap) * c.lap } else { (p / c.cap) * c.lap + c.lap },
        (p + 1) % c.cap == if p % c.cap + 1 < c.cap { p % c.cap + 1 } else { 0 },
{
    lemma_div_mod(p, c.cap);
    let (a, r) = (p / c.cap, p % c.cap);
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(c.shift, 61);
    assert(vstd::bits::low_bits_mask(c.shift) == c.lap - 1);
    vstd::bits::lemma_u64_low_bits_mask_is_mod(x, c.shift);
    assert(c.lap < 0x2000_0000_0000_0000);
    assert((x as nat) % c.lap == r) by {
        lemma_split(x as nat, c.lap, a, r);
    }
    if r + 1 < c.cap {
        assert(p + 1 == a * c.cap + (r + 1));
        lemma_split(p + 1, c.cap, a, r + 1);
    } else {
        assert(p + 1 == (a + 1) * c.cap + 0) by (nonlinear_arith)
            requires p == a * c.cap + r, r + 1 == c.cap;
        lemma_split(p + 1, c.cap, a + 1, 0);
        assert((a + 1) * c.lap == a * c.lap + c.lap) by (nonlinear_arith);
    }
}

proof fn lemma_pk_bound(c: Consts, p: nat)
    requires
        consts_ok(c),
    ensures
        pk(c, p) < (p / c.cap) * c.lap + c.lap,
{
    lemma_div_mod(p, c.cap);
}

/// The lap counter only grows with the position.
proof fn lemma_lap_mono(c: Consts, p: nat, q: nat)
    requires
        consts_ok(c),
        p <= q,
    ensures
        (p / c.cap) * c.lap <= (q / c.cap) * c.lap,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(p as int, q as int, c.cap as int);
    vstd::arithmetic::mul::lemma_mul_inequality((p / c.cap) as int, (q / c.cap) as int, c.lap as int);
}

proof fn lemma_abs_push<T>(vals: Map<nat, T>, h: nat, t: nat, v: T)
    requires
        h <= t,
    ensures
        abs_queue(vals.insert(t, v), h, t + 1) == abs_queue(vals, h, t).push(v),
{
    assert(abs_queue(vals.insert(t, v), h, t + 1) =~= abs_queue(vals, h, t).push(v));
}

proof fn lemma_abs_pop<T>(vals: Map<nat, T>, h: nat, t: nat)
    requires
        h < t,
    ensures
        abs_queue(vals, h + 1, t) == abs_queue(vals, h, t).drop_first(),
        abs_queue(vals, h, t)[0] == vals[h],
{
    assert(abs_queue(vals, h + 1, t) =~= abs_queue(vals, h, t).drop_first());
}

// ---------------------------------------------------------------------------

/// One slot: its stamp and its cell.
pub struct Slot<T> {
    stamp: RaU64,
    value: PCell<T>,
}

/// A bounded multi-producer multi-consumer queue, with crossbeam's `ArrayQueue` API.
pub struct ArrayQueue<T> {
    head: CachePadded<RaU64>,
    tail: CachePadded<RaU64>,
    buffer: Vec<Slot<T>>,
    cap: u64,
    one_lap: u64,
    mask: u64,
    /// `None` only while the queue is being dropped.
    inv: Tracked<Option<ObjInvariant<Consts, Shared<T>, QueuePred>>>,
}

/// Decoding a packed position gives the position back.
proof fn lemma_unpk_pk(c: Consts, p: nat)
    requires
        consts_ok(c),
    ensures
        unpk(c, pk(c, p)) == p,
{
    lemma_div_mod(p, c.cap);
    let (a, r) = (p / c.cap, p % c.cap);
    lemma_split(pk(c, p), c.lap, a, r);
}

/// A position no later than `q` packs no higher, and keeps the lap bound.
proof fn lemma_pk_le(c: Consts, p: nat, q: nat)
    requires
        consts_ok(c),
        p <= q,
    ensures
        pk(c, p) <= pk(c, q),
        (p / c.cap) * c.lap <= (q / c.cap) * c.lap,
{
    if p < q {
        lemma_pk_mono(c, p, q);
    }
    lemma_lap_mono(c, p, q);
}

/// A read-modify-write that adds 0 keeps a position history valid.
proof fn lemma_pos_hist_rmw(c: Consts, h: Hist, h2: Hist, cur: nat, v: RaView)
    requires
        pos_hist(c, h, cur),
        h2.msgs() == h.msgs().push(Msg { val: h.last().val, view: v }),
    ensures
        pos_hist(c, h2, cur),
{
    assert forall|k: int| 0 <= k < h2.msgs().len() implies {
        &&& pk(c, unpk(c, #[trigger] h2.msgs()[k].val as nat)) == h2.msgs()[k].val
        &&& unpk(c, h2.msgs()[k].val as nat) <= cur
    } by {
        if k < h.msgs().len() {
            assert(h2.msgs()[k] == h.msgs()[k]);
        } else {
            assert(h2.msgs()[k].val == h.msgs()[h.msgs().len() - 1].val);
        }
    }
}

/// A compare-and-swap from position `cur` to `cur + 1` keeps a position
/// history valid.
proof fn lemma_pos_hist_advance(c: Consts, h: Hist, h2: Hist, cur: nat, new: u64, v: RaView)
    requires
        consts_ok(c),
        pos_hist(c, h, cur),
        new as nat == pk(c, cur + 1),
        h2.msgs() == h.msgs().push(Msg { val: new, view: v }),
    ensures
        pos_hist(c, h2, cur + 1),
{
    lemma_unpk_pk(c, cur + 1);
    assert forall|k: int| 0 <= k < h2.msgs().len() implies {
        &&& pk(c, unpk(c, #[trigger] h2.msgs()[k].val as nat)) == h2.msgs()[k].val
        &&& unpk(c, h2.msgs()[k].val as nat) <= cur + 1
    } by {
        if k < h.msgs().len() {
            assert(h2.msgs()[k] == h.msgs()[k]);
        }
    }
}

/// A release store of `st2`, above every message, at view `v`, publishing a
/// cell at `v`.
proof fn lemma_stamp_store(h: Hist, h2: Hist, st: nat, st2: u64, v: RaView)
    requires
        h.msgs().len() > 0,
        forall|k: int| 0 <= k < h.msgs().len() ==> #[trigger] h.msgs()[k].val <= st,
        st < st2,
        h2.msgs() == h.msgs().push(Msg { val: st2, view: v }),
    ensures
        stamp_hist(h2, st2 as nat, v),
        forall|k: int| 0 <= k < h2.msgs().len() ==> #[trigger] h2.msgs()[k].val <= st2,
{
    assert forall|k: int| 0 <= k < h2.msgs().len() implies #[trigger] h2.msgs()[k].val <= st2 by {
        if k < h.msgs().len() {
            assert(h2.msgs()[k] == h.msgs()[k]);
        }
    }
    assert forall|k: int| 0 <= k < h2.msgs().len() && h2.msgs()[k].val == st2 implies v.le(#[trigger] h2.msgs()[k].view) by {
        if k < h.msgs().len() {
            assert(h2.msgs()[k] == h.msgs()[k]);
        } else {
            lemma_view_le_refl(v);
        }
    }
}

impl<T> ArrayQueue<T> {
    pub closed spec fn consts(&self) -> Consts {
        self.inv@->0.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        let c = self.consts();
        &&& self.inv@ is Some
        &&& consts_ok(c)
        &&& c.cap == self.cap as nat
        &&& c.lap == self.one_lap as nat
        &&& self.mask as nat == c.lap - 1
        &&& c.head_id == self.head.0.id()
        &&& c.tail_id == self.tail.0.id()
        &&& self.buffer@.len() == c.cap
        // The slots are a Vec: on 32-bit targets, fewer than 2^32.
        &&& c.cap <= usize::MAX
        &&& forall|i: int| 0 <= i < c.cap ==> #[trigger] self.buffer@[i].stamp.id() == c.stamp_ids[i]
        &&& forall|i: int| 0 <= i < c.cap ==> #[trigger] self.buffer@[i].value.id() == c.cells[i]
    }

    pub closed spec fn ns(&self) -> int {
        self.inv@->0.namespace()
    }

    pub closed spec fn qid(&self) -> Loc {
        self.consts().q_id
    }

    pub closed spec fn capacity_spec(&self) -> nat {
        self.cap as nat
    }

    /// A relaxed load of the tail: some position the tail has held.
    fn load_tail(&self) -> (r: (u64, Ghost<nat>, Tracked<MonoLb>))
        requires
            self.wf(),
        ensures
            r.0 as nat == pk(self.consts(), r.1@),
            r.2@.loc() == self.consts().tail_mono,
            r.2@@ == r.0 as nat,
            (r.1@ / self.consts().cap) * self.consts().lap + 4 * self.consts().lap <= u64::MAX,
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let tail;
        let ghost mut t = 0;
        let tracked mut lb;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let (v, Ghost(k)) = self.tail.0.load_relaxed(Tracked(&s.tail), Tracked(&mut tid));
            tail = v;
            proof {
                let ghost m = s.tail.msgs()[k as int];
                t = unpk(c, v as nat);
                lemma_pk_le(c, t, s.tl@);
                lb = s.tm.lb().weaken(v as nat);
            }
        });
        (tail, Ghost(t), Tracked(lb))
    }

    /// A relaxed load of the head: some position the head has held.
    fn load_head(&self) -> (r: (u64, Ghost<nat>, Tracked<MonoLb>))
        requires
            self.wf(),
        ensures
            r.0 as nat == pk(self.consts(), r.1@),
            r.2@.loc() == self.consts().head_mono,
            r.2@@ == r.0 as nat,
            (r.1@ / self.consts().cap) * self.consts().lap + 4 * self.consts().lap <= u64::MAX,
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let head;
        let ghost mut h = 0;
        let tracked mut lb;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let (v, Ghost(k)) = self.head.0.load_relaxed(Tracked(&s.head), Tracked(&mut tid));
            head = v;
            proof {
                let ghost m = s.head.msgs()[k as int];
                h = unpk(c, v as nat);
                lemma_pk_le(c, h, s.hd@);
                lemma_lap_mono(c, s.hd@, s.tl@);
                lb = s.hm.lb().weaken(v as nat);
            }
        });
        (head, Ghost(h), Tracked(lb))
    }

    /// An acquire load of a stamp. Returns a lower bound on the stamp and
    /// a snapshot of its history that identifies the message read, whose
    /// view the thread has now seen.
    fn load_stamp(&self, index: u64, Tracked(tid): Tracked<&mut Tid>) -> (r: (u64, Tracked<MonoLb>, Tracked<HistLb>, Ghost<nat>))
        requires
            self.wf(),
            index < self.cap,
        ensures
            r.1@.loc() == self.consts().stamp_mono[index as int],
            r.1@@ == r.0 as nat,
            r.2@.loc() == self.consts().stamp_ids[index as int],
            r.3@ < r.2@.msgs().len(),
            r.2@.msgs()[r.3@ as int].val == r.0,
            r.2@.msgs()[r.3@ as int].view.le(final(tid).view()),
            old(tid).view().le(final(tid).view()),
    {
        let ghost c = self.consts();
        let ghost i = index as nat;
        let slot = &self.buffer[index as usize];
        let stamp;
        let tracked mut lb;
        let tracked mut hl;
        let ghost mut k = 0;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            proof {
                assert(slot_inv(c, s, i));
            }
            let ghost tid0 = tid.view();
            let (v, Ghost(kk)) = slot.stamp.load_acquire(Tracked(s.stamps.tracked_borrow(i)), Tracked(&mut *tid));
            stamp = v;
            proof {
                k = kk;
                let ghost m = s.stamps[i].msgs()[kk as int];
                lemma_acquired(tid0, m.view, c.stamp_ids[i as int], kk, tid.view());
                lb = s.sm.tracked_borrow(i).lb().weaken(v as nat);
                hl = s.stamps.tracked_borrow(i).lb();
            }
        });
        (stamp, Tracked(lb), Tracked(hl), Ghost(k))
    }

    /// A call starts: it takes an idle model thread and starts `push`
    /// (`PLoad`), `pop` (`QLoad`) or `len` (`LTail`).
    fn enter(&self, Ghost(p): Ghost<Ph>) -> (r: Tracked<Tok<P>>)
        requires
            self.wf(),
            p == Ph::PLoad || p == Ph::QLoad || p == Ph::LTail,
        ensures
            tok_at(r@, self.consts(), p),
    {
        let ghost c = self.consts();
        let tracked mut tok;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            proof {
                tok = s.model.enter();
                s.model.agree(&tok);
                let m = s.model@;
                let u = tok.key();
                let s2 = go(m, u, p);
                assert(sc_step(m, u, s2));
                s.model.step(&mut tok, s2);
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        Tracked(tok)
    }

    /// A call returns: its model thread, idle again, goes back.
    fn leave(&self, Tracked(tok): Tracked<Tok<P>>)
        requires
            self.wf(),
            tok_at(tok, self.consts(), Ph::Idle),
    {
        let ghost c = self.consts();
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            proof {
                s.model.leave(tok);
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
    }

    /// `load_tail` in a call, with the model's step: `PLoad`, `QTail`,
    /// `LTail` or `LTail2`.
    fn load_tail_at(&self, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: (u64, Ghost<nat>, Tracked<MonoLb>))
        requires
            self.wf(),
            old(tok).id() == self.consts().model,
            old(tok).value() is PLoad || old(tok).value() is QTail || old(tok).value() is LTail || old(tok).value() is LTail2,
        ensures
            r.0 as nat == pk(self.consts(), r.1@),
            r.2@.loc() == self.consts().tail_mono,
            r.2@@ == r.0 as nat,
            (r.1@ / self.consts().cap) * self.consts().lap + 4 * self.consts().lap <= u64::MAX,
            tok_at(*final(tok), self.consts(), tail_next(old(tok).value(), r.1@)),
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let tail;
        let ghost mut t = 0;
        let tracked mut lb;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            let (v, Ghost(k)) = self.tail.0.load_relaxed(Tracked(&s.tail), Tracked(&mut tid));
            tail = v;
            proof {
                let ghost m0 = s.tail.msgs()[k as int];
                t = unpk(c, v as nat);
                lemma_pk_le(c, t, s.tl@);
                lb = s.tm.lb().weaken(v as nat);
                s.model.agree(tok);
                let m = s.model@;
                let u = tok.key();
                let p2 = tail_next(tok.value(), t);
                let s2 = if p2 == Ph::Idle { ret(m, u) } else { go(m, u, p2) };
                assert(stale_step(m, u, s2));
                s.model.step(tok, s2);
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        (tail, Ghost(t), Tracked(lb))
    }

    /// `load_head` in a call, with the model's step: `QLoad`, `PHead` or
    /// `LHead`.
    fn load_head_at(&self, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: (u64, Ghost<nat>, Tracked<MonoLb>))
        requires
            self.wf(),
            old(tok).id() == self.consts().model,
            old(tok).value() is QLoad || old(tok).value() is PHead || old(tok).value() is LHead,
        ensures
            r.0 as nat == pk(self.consts(), r.1@),
            r.2@.loc() == self.consts().head_mono,
            r.2@@ == r.0 as nat,
            (r.1@ / self.consts().cap) * self.consts().lap + 4 * self.consts().lap <= u64::MAX,
            tok_at(*final(tok), self.consts(), head_next(self.consts(), old(tok).value(), r.1@)),
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let head;
        let ghost mut h = 0;
        let tracked mut lb;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            let (v, Ghost(k)) = self.head.0.load_relaxed(Tracked(&s.head), Tracked(&mut tid));
            head = v;
            proof {
                let ghost m0 = s.head.msgs()[k as int];
                h = unpk(c, v as nat);
                lemma_pk_le(c, h, s.hd@);
                lemma_lap_mono(c, s.hd@, s.tl@);
                lb = s.hm.lb().weaken(v as nat);
                s.model.agree(tok);
                let m = s.model@;
                let u = tok.key();
                let s2 = go(m, u, head_next(c, tok.value(), h));
                assert(step(m, u, s2));
                s.model.step(tok, s2);
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        (head, Ghost(h), Tracked(lb))
    }

    /// `load_stamp` in a call, for position `a`, with the model's step:
    /// `PStamp` or `QStamp`.
    fn load_stamp_at(&self, index: u64, Tracked(tid): Tracked<&mut Tid>, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(a): Ghost<nat>) -> (r: (u64, Tracked<MonoLb>, Tracked<HistLb>, Ghost<nat>))
        requires
            self.wf(),
            index < self.cap,
            index as nat == a % self.consts().cap,
            old(tok).id() == self.consts().model,
            old(tok).value() == (Ph::PStamp { a }) || old(tok).value() == (Ph::QStamp { a }),
        ensures
            r.1@.loc() == self.consts().stamp_mono[index as int],
            r.1@@ == r.0 as nat,
            r.2@.loc() == self.consts().stamp_ids[index as int],
            r.3@ < r.2@.msgs().len(),
            r.2@.msgs()[r.3@ as int].val == r.0,
            r.2@.msgs()[r.3@ as int].view.le(final(tid).view()),
            old(tid).view().le(final(tid).view()),
            tok_at(*final(tok), self.consts(), stamp_next(self.consts(), old(tok).value(), r.0 as nat)),
    {
        let ghost c = self.consts();
        let ghost i = index as nat;
        let slot = &self.buffer[index as usize];
        let stamp;
        let tracked mut lb;
        let tracked mut hl;
        let ghost mut k = 0;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            proof {
                assert(slot_inv(c, s, i));
            }
            let ghost tid0 = tid.view();
            let (v, Ghost(kk)) = slot.stamp.load_acquire(Tracked(s.stamps.tracked_borrow(i)), Tracked(&mut *tid));
            stamp = v;
            proof {
                k = kk;
                let ghost m0 = s.stamps[i].msgs()[kk as int];
                lemma_acquired(tid0, m0.view, c.stamp_ids[i as int], kk, tid.view());
                lb = s.sm.tracked_borrow(i).lb().weaken(v as nat);
                hl = s.stamps.tracked_borrow(i).lb();
                s.model.agree(tok);
                let m = s.model@;
                let u = tok.key();
                lemma_stamp_rank(c, s.slots@[i], (s.stamps[i].last().val) as nat, v as nat, a);
                assert(rank(m, a) == srank(s.slots@[i]));
                let s2 = go(m, u, stamp_next(c, tok.value(), v as nat));
                assert(stale_step(m, u, s2));
                s.model.step(tok, s2);
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        (stamp, Tracked(lb), Tracked(hl), Ghost(k))
    }

    /// Appends `value`, or gives it back if the queue holds `capacity` values.
    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub fn push_atomic(&self, value: T) -> (r: Result<(), T>)
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
            self.wf(),
        ensures
            r is Ok <==> x@.len() < self.capacity_spec(),
            r matches Err(v) ==> v == value,
    {
        let ghost c = self.consts();
        let ghost au_g = au;
        let tracked mut au_opt = Some(au);
        let tracked mut tid = Tid::new();
        let backoff = Backoff::new();
        let Tracked(mut tok) = self.enter(Ghost(Ph::PLoad));
        let (mut tail, Ghost(mut t), Tracked(mut tlb)) = self.load_tail_at(Tracked(&mut tok));
        loop
            invariant
                self.wf(),
                c == self.consts(),
                au_opt == Some(au_g),
                tail as nat == pk(c, t),
                tlb.loc() == c.tail_mono,
                tlb@ == tail as nat,
                (t / c.cap) * c.lap + 4 * c.lap <= u64::MAX,
                tok_at(tok, c, Ph::PStamp { a: t }),
        {
            proof {
                lemma_decode(c, tail, self.mask, t);
                lemma_pk_bound(c, t);
            }
            let index = tail & self.mask;
            let lap = tail - index;
            let new_tail = if index + 1 < self.cap {
                tail + 1
            } else {
                if lap > u64::MAX - 5 * self.one_lap {
                    exhausted();
                }
                lap + self.one_lap
            };
            let ghost i = index as nat;
            let (stamp, Tracked(slb), Tracked(shl), Ghost(sk)) = self.load_stamp_at(index, Tracked(&mut tid), Tracked(&mut tok), Ghost(t));
            if tail == stamp {
                let res;
                let tracked mut claim: Option<(PointsTo<T>, GhostPointsTo<nat, Ticket<T>>)> = None;
                let ghost mut cur = 0nat;
                let tracked mut cur_lb = tlb.dup();
                open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                    let ghost s0 = s;
                    let ghost tid0 = tid.view();
                    let (r0, Ghost(fk)) = self.tail.0.compare_exchange_seqcst(Tracked(&mut s.tail), Tracked(&mut tid), tail, new_tail);
                    res = r0;
                    match res {
                        Ok(_) => {
                            proof {
                                lemma_acquired(tid0, s0.tail.last().view, c.tail_id, s0.tail.msgs().len(), tid.view());
                                if s.tl@ != t {
                                    if s.tl@ < t { lemma_pk_mono(c, s.tl@, t); } else { lemma_pk_mono(c, t, s.tl@); }
                                }
                                assert(s.tl@ == t);
                                assert(slot_inv(c, s0, i));
                                s.sm.tracked_borrow_mut(i).check(&slb);
                                let g = s.slots@[i];
                                match g.phase {
                                    Phase::Free => {
                                        if g.pos > t { lemma_same_slot(c, t, g.pos); }
                                    },
                                    Phase::Taken => { lemma_same_slot(c, g.pos, t); },
                                    _ => { lemma_same_slot(c, g.pos, t); },
                                }
                                assert(g.phase == Phase::Free && g.pos == t);
                                // The message we read holds the current stamp, so its view
                                // covers the cell's.
                                s.stamps.tracked_borrow(i).lb_prefix(&shl);
                                let ghost m = s.stamps[i].msgs()[sk as int];
                                assert(m == shl.msgs()[sk as int]);
                                lemma_view_le_trans(s.cells[i].view(), m.view, tid0);
                                lemma_view_le_trans(s.cells[i].view(), tid0, tid.view());
                                let tracked pp = s.cells.tracked_remove(i);
                                let tracked perm = pp.acquire(&tid);
                                let tracked ticket = s.tk.insert(i, Ticket::Push { pos: t, v: value });
                                s.slots = Ghost(s.slots@.insert(i, SlotG { pos: t, phase: Phase::Claimed }));
                                s.vals = Ghost(s.vals@.insert(t, value));
                                s.tl = Ghost(t + 1);
                                lemma_pos_hist_advance(c, s0.tail, s.tail, t, new_tail, tid.view());
                                s.tm.advance(new_tail as nat);
                                claim = Some((perm, ticket));
                                lemma_abs_push(s0.vals@, s.hd@, t, value);
                                // The model's `PCas`, succeeding.
                                s.model.agree(&tok);
                                let m = s0.model@;
                                let u = tok.key();
                                let s2 = St { tail: t + 1, ..go(m, u, Ph::PWrite { a: t }) };
                                assert(sc_step(m, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] s.model@.st[j as int] == srank(s.slots@[j]) by {
                                    assert(s0.model@.st[j as int] == srank(s0.slots@[j]));
                                }
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
                                assert(s.tm@ == pk(c, s.tl@));
                                assert(s.hd@ <= s.tl@ <= s.hd@ + c.cap);
                                assert((s.tl@ / c.cap) * c.lap + 4 * c.lap <= u64::MAX);
                                assert(s.q@ == abs_queue(s.vals@, s.hd@, s.tl@));
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                    if j != i {
                                        let gj = s.slots@[j];
                                        if gj.phase == Phase::Taken {
                                            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(gj.pos as int, c.cap as int);
                                        }
                                    }
                                }
                            }
                        }
                        Err(v) => {
                            proof {
                                let ghost m = s.tail.msgs()[fk as int];
                                cur = unpk(c, v as nat);
                                lemma_pk_le(c, cur, s.tl@);
                                cur_lb = s.tm.lb().weaken(v as nat);
                                // The model's `PCas`, failing: a load.
                                s.model.agree(&tok);
                                let mm = s.model@;
                                let u = tok.key();
                                let s2 = go(mm, u, Ph::PStamp { a: cur });
                                assert(step(mm, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                }
                            }
                        }
                    }
                });
                match res {
                    Ok(_) => {
                        let tracked (mut perm, ticket) = claim.tracked_unwrap();
                        let slot = &self.buffer[index as usize];
                        slot.value.put(Tracked(&mut perm), value);
                        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                            let ghost s0 = s;
                            proof {
                                ticket.agree(&s.tk);
                                assert(slot_inv(c, s0, i));
                            }
                            let tracked mut sh = s.stamps.tracked_remove(i);
                            let ghost h0 = sh;
                            slot.stamp.store_release(Tracked(&mut sh), Tracked(&mut tid), tail + 1);
                            proof {
                                lemma_stamp_store(h0, sh, pk(c, t), (tail + 1) as u64, tid.view());
                                s.stamps.tracked_insert(i, sh);
                                s.cells.tracked_insert(i, Published::publish(perm, &tid));
                                s.tk.delete_points_to(ticket);
                                s.slots = Ghost(s.slots@.insert(i, SlotG { pos: t, phase: Phase::Full }));
                                s.sm.tracked_borrow_mut(i).advance((tail + 1) as nat);
                                // The model's `PWrite`: the call returns.
                                s.model.agree(&tok);
                                let m = s0.model@;
                                let u = tok.key();
                                let s2 = St { st: m.st.update((t % m.cap) as int, 2 * t + 1), ..ret(m, u) };
                                assert(sc_step(m, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] s.model@.st[j as int] == srank(s.slots@[j]) by {
                                    assert(s0.model@.st[j as int] == srank(s0.slots@[j]));
                                }
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                }
                            }
                        });
                        self.leave(Tracked(tok));
                        return Ok(());
                    }
                    Err(cur_tail) => {
                        tail = cur_tail;
                        proof {
                            t = cur;
                            tlb = cur_lb;
                        }
                        backoff.spin();
                    }
                }
            } else if tail + 1 >= self.one_lap && stamp == tail + 1 - self.one_lap {
                // The slot still holds the value from the previous lap: the
                // queue may be full. A relaxed load of the head says whether
                // to look closer; a read-modify-write, which reads the latest
                // head, decides.
                let (head, Ghost(hh), _) = self.load_head_at(Tracked(&mut tok));
                proof {
                    lemma_full_test(c, hh, t);
                }
                if tail >= self.one_lap && head == tail - self.one_lap {
                    let cur;
                    open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                        let ghost s0 = s;
                        cur = self.head.0.fetch_add_seqcst(Tracked(&mut s.head), Tracked(&mut tid), 0);
                        proof {
                            lemma_pos_hist_rmw(c, s0.head, s.head, s.hd@, tid.view());
                            // The model's `PConfirm`.
                            lemma_full_test(c, s.hd@, t);
                            s.model.agree(&tok);
                            let m = s.model@;
                            let u = tok.key();
                            let s2 = if m.head + m.cap == t { ret(m, u) } else { go(m, u, Ph::PLoad) };
                            assert(sc_step(m, u, s2));
                            s.model.step(&mut tok, s2);
                        }
                        if tail >= self.one_lap && cur == tail - self.one_lap {
                            proof {
                                // head + one_lap == tail means H + cap == t, and
                                // T >= t from our lower bound, so T == H + cap.
                                lemma_pk_cap(c, s.hd@);
                                if s.hd@ + c.cap != t {
                                    if s.hd@ + c.cap < t { lemma_pk_mono(c, s.hd@ + c.cap, t); } else { lemma_pk_mono(c, t, s.hd@ + c.cap); }
                                }
                                s.tm.check(&tlb);
                                if s.tl@ < t { lemma_pk_mono(c, s.tl@, t); }
                                assert(s.tl@ == s.hd@ + c.cap);
                            }
                            let tracked au = au_opt.tracked_take();
                            try_open_atomic_update!(au, x => {
                                proof { s.q.agree(&x); }
                                Tracked(Commit(x))
                            });
                        }
                        proof {
                            assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                assert(slot_inv(c, s0, j));
                            }
                        }
                    });
                    if tail >= self.one_lap && cur == tail - self.one_lap {
                        self.leave(Tracked(tok));
                        return Err(value);
                    }
                }
                backoff.spin();
                let (t2, Ghost(ta), Tracked(lb2)) = self.load_tail_at(Tracked(&mut tok));
                tail = t2;
                proof {
                    t = ta;
                    tlb = lb2;
                }
            } else {
                // Another thread is mid-operation on this slot: wait.
                backoff.snooze();
                let (t2, Ghost(ta), Tracked(lb2)) = self.load_tail_at(Tracked(&mut tok));
                tail = t2;
                proof {
                    t = ta;
                    tlb = lb2;
                }
            }
        }
    }

    /// Removes the oldest value, or returns `None` if the queue is empty.
    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub fn pop_atomic(&self) -> (r: Option<T>)
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
            self.wf(),
        ensures
            r is Some <==> x@.len() > 0,
            r matches Some(v) ==> v == x@[0],
    {
        let ghost c = self.consts();
        let ghost au_g = au;
        let tracked mut au_opt = Some(au);
        let tracked mut tid = Tid::new();
        let backoff = Backoff::new();
        let Tracked(mut tok) = self.enter(Ghost(Ph::QLoad));
        let (mut head, Ghost(mut h), Tracked(mut hlb)) = self.load_head_at(Tracked(&mut tok));
        loop
            invariant
                self.wf(),
                c == self.consts(),
                au_opt == Some(au_g),
                head as nat == pk(c, h),
                hlb.loc() == c.head_mono,
                hlb@ == head as nat,
                (h / c.cap) * c.lap + 4 * c.lap <= u64::MAX,
                tok_at(tok, c, Ph::QStamp { a: h }),
        {
            proof {
                lemma_decode(c, head, self.mask, h);
                lemma_pk_bound(c, h);
            }
            let index = head & self.mask;
            let lap = head - index;
            let new_head = if index + 1 < self.cap {
                head + 1
            } else {
                lap + self.one_lap
            };
            let ghost i = index as nat;
            let (stamp, Tracked(slb), Tracked(shl), Ghost(sk)) = self.load_stamp_at(index, Tracked(&mut tid), Tracked(&mut tok), Ghost(h));
            if head + 1 == stamp {
                let res;
                let tracked mut claim: Option<(PointsTo<T>, GhostPointsTo<nat, Ticket<T>>)> = None;
                let ghost mut cur = 0nat;
                let tracked mut cur_lb = hlb.dup();
                open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                    let ghost s0 = s;
                    let ghost tid0 = tid.view();
                    let (r0, Ghost(fk)) = self.head.0.compare_exchange_seqcst(Tracked(&mut s.head), Tracked(&mut tid), head, new_head);
                    res = r0;
                    match res {
                        Ok(_) => {
                            proof {
                                lemma_acquired(tid0, s0.head.last().view, c.head_id, s0.head.msgs().len(), tid.view());
                                if s.hd@ != h {
                                    if s.hd@ < h { lemma_pk_mono(c, s.hd@, h); } else { lemma_pk_mono(c, h, s.hd@); }
                                }
                                assert(s.hd@ == h);
                                assert(slot_inv(c, s0, i));
                                s.sm.tracked_borrow_mut(i).check(&slb);
                                let g = s.slots@[i];
                                match g.phase {
                                    Phase::Taken => { lemma_same_slot(c, g.pos, h); },
                                    _ => {
                                        if g.pos > h { lemma_same_slot(c, h, g.pos); }
                                    },
                                }
                                assert(g.phase == Phase::Full && g.pos == h);
                                s.stamps.tracked_borrow(i).lb_prefix(&shl);
                                let ghost m = s.stamps[i].msgs()[sk as int];
                                assert(m == shl.msgs()[sk as int]);
                                lemma_view_le_trans(s.cells[i].view(), m.view, tid0);
                                lemma_view_le_trans(s.cells[i].view(), tid0, tid.view());
                                lemma_decode(c, new_head, self.mask, h + 1);
                                let tracked pp = s.cells.tracked_remove(i);
                                let tracked perm = pp.acquire(&tid);
                                let tracked ticket = s.tk.insert(i, Ticket::Pop { pos: h });
                                s.slots = Ghost(s.slots@.insert(i, SlotG { pos: h, phase: Phase::Taken }));
                                s.hd = Ghost(h + 1);
                                lemma_pk_mono(c, h, h + 1);
                                lemma_pos_hist_advance(c, s0.head, s.head, h, new_head, tid.view());
                                s.hm.advance(new_head as nat);
                                claim = Some((perm, ticket));
                                lemma_abs_pop(s0.vals@, h, s.tl@);
                                // The model's `QCas`, succeeding.
                                s.model.agree(&tok);
                                let m = s0.model@;
                                let u = tok.key();
                                let s2 = St { head: h + 1, ..go(m, u, Ph::QRead { a: h }) };
                                assert(sc_step(m, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] s.model@.st[j as int] == srank(s.slots@[j]) by {
                                    assert(s0.model@.st[j as int] == srank(s0.slots@[j]));
                                }
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
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                }
                            }
                        }
                        Err(v) => {
                            proof {
                                let ghost m = s.head.msgs()[fk as int];
                                cur = unpk(c, v as nat);
                                lemma_pk_le(c, cur, s.hd@);
                                lemma_lap_mono(c, s.hd@, s.tl@);
                                cur_lb = s.hm.lb().weaken(v as nat);
                                // The model's `QCas`, failing: a load.
                                s.model.agree(&tok);
                                let mm = s.model@;
                                let u = tok.key();
                                let s2 = go(mm, u, Ph::QStamp { a: cur });
                                assert(step(mm, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                }
                            }
                        }
                    }
                });
                match res {
                    Ok(_) => {
                        let tracked (mut perm, ticket) = claim.tracked_unwrap();
                        let slot = &self.buffer[index as usize];
                        let value = slot.value.take(Tracked(&mut perm));
                        let released = head + self.one_lap;
                        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                            let ghost s0 = s;
                            proof {
                                ticket.agree(&s.tk);
                                assert(slot_inv(c, s0, i));
                                lemma_pk_cap(c, h);
                                vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(h as int, c.cap as int);
                            }
                            let tracked mut sh = s.stamps.tracked_remove(i);
                            let ghost h0 = sh;
                            slot.stamp.store_release(Tracked(&mut sh), Tracked(&mut tid), released);
                            proof {
                                lemma_stamp_store(h0, sh, (pk(c, h) + 1) as nat, released, tid.view());
                                s.stamps.tracked_insert(i, sh);
                                s.cells.tracked_insert(i, Published::publish(perm, &tid));
                                s.tk.delete_points_to(ticket);
                                s.slots = Ghost(s.slots@.insert(i, SlotG { pos: h + c.cap, phase: Phase::Free }));
                                s.sm.tracked_borrow_mut(i).advance(released as nat);
                                // The model's `QRead`: the call returns.
                                s.model.agree(&tok);
                                let m = s0.model@;
                                let u = tok.key();
                                let s2 = St { st: m.st.update((h % m.cap) as int, 2 * (h + m.cap)), ..ret(m, u) };
                                assert(sc_step(m, u, s2));
                                s.model.step(&mut tok, s2);
                                assert forall|j: nat| j < c.cap implies #[trigger] s.model@.st[j as int] == srank(s.slots@[j]) by {
                                    assert(s0.model@.st[j as int] == srank(s0.slots@[j]));
                                }
                                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                    assert(slot_inv(c, s0, j));
                                }
                            }
                        });
                        self.leave(Tracked(tok));
                        return Some(value);
                    }
                    Err(cur_head) => {
                        head = cur_head;
                        proof {
                            h = cur;
                            hlb = cur_lb;
                        }
                        backoff.spin();
                    }
                }
            } else if stamp == head {
                // The slot is waiting for the push at this position: the
                // queue may be empty. As in `push`, a relaxed load of the
                // tail says whether to look closer, and a read-modify-write
                // decides.
                let (tail, Ghost(tt), _) = self.load_tail_at(Tracked(&mut tok));
                proof {
                    if tail == head {
                        lemma_pk_inj(c, tt, h);
                    }
                }
                if tail == head {
                    let cur;
                    open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
                        let ghost s0 = s;
                        cur = self.tail.0.fetch_add_seqcst(Tracked(&mut s.tail), Tracked(&mut tid), 0);
                        proof {
                            lemma_pos_hist_rmw(c, s0.tail, s.tail, s.tl@, tid.view());
                            // The model's `QConfirm`.
                            if cur == head {
                                lemma_pk_inj(c, s.tl@, h);
                            }
                            s.model.agree(&tok);
                            let m = s.model@;
                            let u = tok.key();
                            let s2 = if m.tail == h { ret(m, u) } else { go(m, u, Ph::QLoad) };
                            assert(sc_step(m, u, s2));
                            s.model.step(&mut tok, s2);
                        }
                        if cur == head {
                            proof {
                                // tail == head means T == h, and H >= h from our
                                // lower bound, so H == T.
                                if s.tl@ != h {
                                    if s.tl@ < h { lemma_pk_mono(c, s.tl@, h); } else { lemma_pk_mono(c, h, s.tl@); }
                                }
                                s.hm.check(&hlb);
                                if s.hd@ < h { lemma_pk_mono(c, s.hd@, h); }
                                assert(s.hd@ == s.tl@);
                            }
                            let tracked au = au_opt.tracked_take();
                            try_open_atomic_update!(au, x => {
                                proof { s.q.agree(&x); }
                                Tracked(Commit(x))
                            });
                        }
                        proof {
                            assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                                assert(slot_inv(c, s0, j));
                            }
                        }
                    });
                    if cur == head {
                        self.leave(Tracked(tok));
                        return None;
                    }
                }
                backoff.spin();
                let (h2, Ghost(ha), Tracked(lb2)) = self.load_head_at(Tracked(&mut tok));
                head = h2;
                proof {
                    h = ha;
                    hlb = lb2;
                }
            } else {
                // Another thread is mid-operation on this slot: wait.
                backoff.snooze();
                let (h2, Ghost(ha), Tracked(lb2)) = self.load_head_at(Tracked(&mut tok));
                head = h2;
                proof {
                    h = ha;
                    hlb = lb2;
                }
            }
        }
    }

    /// The number of values in the queue. Other threads may change it at any
    /// time, so this is a hint; it is at most the capacity.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn len(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r <= self.capacity_spec(),
    {
        let ghost c = self.consts();
        let Tracked(mut tok) = self.enter(Ghost(Ph::LTail));
        loop
            invariant
                self.wf(),
                c == self.consts(),
                tok_at(tok, c, Ph::LTail),
        {
            let (tail, Ghost(t), _) = self.load_tail_at(Tracked(&mut tok));
            let (head, Ghost(h), _) = self.load_head_at(Tracked(&mut tok));
            let (tail2, Ghost(t2), _) = self.load_tail_at(Tracked(&mut tok));
            proof {
                if tail2 == tail {
                    lemma_pk_inj(c, t2, t);
                }
            }
            if tail2 == tail {
                proof {
                    lemma_decode(c, tail, self.mask, t);
                    lemma_decode(c, head, self.mask, h);
                }
                self.leave(Tracked(tok));
                let hix = head & self.mask;
                let tix = tail & self.mask;
                return if hix < tix {
                    (tix - hix) as usize
                } else if hix > tix {
                    (self.cap - hix + tix) as usize
                } else if tail == head {
                    0
                } else {
                    self.cap as usize
                };
            }
        }
    }

    /// Whether the queue is empty, for a thread that will sleep on the
    /// answer: `true` means it was empty at one instant during the call
    /// (the caller's atomic update runs at that instant and is told the
    /// answer).
    /// `false` means only "maybe not": the head is read relaxed and may be
    /// stale. The tail is read with a read-modify-write (adding 0), which
    /// reads its latest value, as in `pop`.
    pub fn confirm_empty_atomic(&self) -> (r: bool)
        atomically (au) {
            type ConfirmEmptyPred,
            (x: QueueView<T>) -> (y: Commit<(QueueView<T>, Ghost<bool>)>),
            requires
                x.id() == self.qid(),
            ensures
                y@.0.id() == x.id(),
                y@.0@ == x@,
                y@.1@ ==> x@.len() == 0,
            outer_mask any / [this.ns()],
        },
        requires
            self.wf(),
        ensures
            r == y@.1@,
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let (head, Ghost(h), Tracked(hlb)) = self.load_head();
        let cur;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            cur = self.tail.0.fetch_add_seqcst(Tracked(&mut s.tail), Tracked(&mut tid), 0);
            proof {
                lemma_pos_hist_rmw(c, s0.tail, s.tail, s.tl@, tid.view());
                if cur == head {
                    // tail == head means T == h, and H >= h from our lower
                    // bound, so H == T.
                    if s.tl@ != h {
                        if s.tl@ < h { lemma_pk_mono(c, s.tl@, h); } else { lemma_pk_mono(c, h, s.tl@); }
                    }
                    s.hm.check(&hlb);
                    if s.hd@ < h { lemma_pk_mono(c, s.hd@, h); }
                    assert(s.hd@ == s.tl@);
                }
            }
            try_open_atomic_update!(au, x => {
                proof { s.q.agree(&x); }
                Tracked(Commit((x, Ghost(cur == head))))
            });
            proof {
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        cur == head
    }

    /// Whether the queue is full, for a thread that will sleep on the
    /// answer: `true` means it was full at one instant during the call,
    /// `false` only "maybe not". The tail is read relaxed and the head with
    /// a read-modify-write, as in `push`.
    pub fn confirm_full_atomic(&self) -> (r: bool)
        atomically (au) {
            type ConfirmFullPred,
            (x: QueueView<T>) -> (y: Commit<(QueueView<T>, Ghost<bool>)>),
            requires
                x.id() == self.qid(),
            ensures
                y@.0.id() == x.id(),
                y@.0@ == x@,
                y@.1@ ==> x@.len() == self.capacity_spec(),
            outer_mask any / [this.ns()],
        },
        requires
            self.wf(),
        ensures
            r == y@.1@,
    {
        let ghost c = self.consts();
        let tracked mut tid = Tid::new();
        let (tail, Ghost(t), Tracked(tlb)) = self.load_tail();
        let cur;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow().inner() => s => {
            let ghost s0 = s;
            cur = self.head.0.fetch_add_seqcst(Tracked(&mut s.head), Tracked(&mut tid), 0);
            proof {
                lemma_pos_hist_rmw(c, s0.head, s.head, s.hd@, tid.view());
                if tail >= self.one_lap && cur == tail - self.one_lap {
                    // head + one_lap == tail means H + cap == t, and
                    // T >= t from our lower bound, so T == H + cap.
                    lemma_pk_cap(c, s.hd@);
                    if s.hd@ + c.cap != t {
                        if s.hd@ + c.cap < t { lemma_pk_mono(c, s.hd@ + c.cap, t); } else { lemma_pk_mono(c, t, s.hd@ + c.cap); }
                    }
                    s.tm.check(&tlb);
                    if s.tl@ < t { lemma_pk_mono(c, s.tl@, t); }
                    assert(s.tl@ == s.hd@ + c.cap);
                }
            }
            try_open_atomic_update!(au, x => {
                proof { s.q.agree(&x); }
                Tracked(Commit((x, Ghost(tail >= self.one_lap && cur == tail - self.one_lap))))
            });
            proof {
                assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                    assert(slot_inv(c, s0, j));
                }
            }
        });
        tail >= self.one_lap && cur == tail - self.one_lap
    }

    /// The queue's capacity.
    pub fn capacity(&self) -> (r: usize)
        requires
            self.wf(),
        ensures
            r == self.capacity_spec(),
    {
        self.cap as usize
    }
}

proof fn lemma_pk_small(c: Consts, p: nat)
    requires
        consts_ok(c),
        p < c.cap,
    ensures
        pk(c, p) == p,
{
    lemma_split(p, c.cap, 0, p);
}

impl<T> ArrayQueue<T> {
    /// The smallest power of two above `cap`.
    fn lap_for(cap: u64) -> (r: (u64, Ghost<nat>))
        requires
            0 < cap < 0x1000_0000_0000_0000,
        ensures
            cap < r.0 < 0x2000_0000_0000_0000,
            r.0 == vstd::arithmetic::power2::pow2(r.1@),
            r.1@ < 61,
    {
        proof {
            vstd::arithmetic::power2::lemma2_to64();
        }
        let mut one_lap: u64 = 1;
        let ghost mut shift: nat = 0;
        while one_lap <= cap
            invariant
                one_lap == vstd::arithmetic::power2::pow2(shift),
                1 <= one_lap <= 2 * cap,
                cap < 0x1000_0000_0000_0000,
            decreases 2 * cap - one_lap,
        {
            one_lap = one_lap * 2;
            proof {
                vstd::arithmetic::power2::lemma_pow2_unfold(shift + 1);
                shift = shift + 1;
            }
        }
        proof {
            vstd::arithmetic::power2::lemma2_to64();
            if shift > 61 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(61, shift);
            }
        }
        (one_lap, Ghost(shift))
    }

    /// Allocates the slots: slot `i` starts free for the push at position `i`.
    fn make_slots(cap: u64, Tracked(tid): Tracked<&mut Tid>) -> (r: (
        Vec<Slot<T>>,
        Tracked<Map<nat, Hist>>,
        Tracked<Map<nat, MonoAuth>>,
        Tracked<Map<nat, Published<PointsTo<T>>>>,
        Ghost<(Seq<int>, Seq<CellId>, Seq<Loc>)>,
    ))
        ensures
            ({
                let (buffer, stamps, sm, cells, ids) = r;
                let (stamp_ids, cell_ids, mono_locs) = ids@;
                &&& buffer@.len() == cap
                &&& stamp_ids.len() == cap
                &&& cell_ids.len() == cap
                &&& mono_locs.len() == cap
                &&& forall|j: int| 0 <= j < cap ==> #[trigger] buffer@[j].stamp.id() == stamp_ids[j]
                &&& forall|j: int| 0 <= j < cap ==> #[trigger] buffer@[j].value.id() == cell_ids[j]
                &&& forall|j: nat| j < cap ==> {
                    &&& #[trigger] stamps@.contains_key(j)
                    &&& stamps@[j].loc() == stamp_ids[j as int]
                    &&& stamps@[j].msgs().len() > 0
                    &&& forall|k: int| 0 <= k < stamps@[j].msgs().len() ==> #[trigger] stamps@[j].msgs()[k].val <= j
                    &&& stamp_hist(stamps@[j], j, cells@[j].view())
                    &&& sm@.contains_key(j)
                    &&& sm@[j].wf()
                    &&& sm@[j].loc() == mono_locs[j as int]
                    &&& sm@[j]@ == j
                    &&& cells@.contains_key(j)
                    &&& cells@[j].value().id() == cell_ids[j as int]
                    &&& cells@[j].value().is_uninit()
                }
            }),
    {
        let mut buffer: Vec<Slot<T>> = Vec::with_capacity(cap as usize);
        let tracked mut stamps: Map<nat, Hist> = Map::tracked_empty();
        let tracked mut sm: Map<nat, MonoAuth> = Map::tracked_empty();
        let tracked mut cells: Map<nat, Published<PointsTo<T>>> = Map::tracked_empty();
        let ghost mut stamp_ids: Seq<int> = Seq::empty();
        let ghost mut cell_ids: Seq<CellId> = Seq::empty();
        let ghost mut mono_locs: Seq<Loc> = Seq::empty();
        let mut i: u64 = 0;
        while i < cap
            invariant
                i <= cap,
                buffer@.len() == i,
                stamp_ids.len() == i,
                cell_ids.len() == i,
                mono_locs.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] buffer@[j].stamp.id() == stamp_ids[j],
                forall|j: int| 0 <= j < i ==> #[trigger] buffer@[j].value.id() == cell_ids[j],
                forall|j: nat| j < i ==> {
                    &&& #[trigger] stamps.contains_key(j)
                    &&& stamps[j].loc() == stamp_ids[j as int]
                    &&& stamps[j].msgs().len() > 0
                    &&& forall|k: int| 0 <= k < stamps[j].msgs().len() ==> #[trigger] stamps[j].msgs()[k].val <= j
                    &&& stamp_hist(stamps[j], j, cells[j].view())
                    &&& sm.contains_key(j)
                    &&& sm[j].wf()
                    &&& sm[j].loc() == mono_locs[j as int]
                    &&& sm[j]@ == j
                    &&& cells.contains_key(j)
                    &&& cells[j].value().id() == cell_ids[j as int]
                    &&& cells[j].value().is_uninit()
                },
            decreases cap - i,
        {
            // Publish the empty cell first, so that the stamp's first message,
            // written after, covers it.
            let (value, Tracked(cp)) = PCell::empty();
            let tracked pc = Published::publish(cp, &*tid);
            let ghost v0 = tid.view();
            let (stamp, Tracked(sh)) = RaU64::new(i, Tracked(&mut *tid));
            proof {
                lemma_view_join(v0, RaView::single(stamp.id(), 0));
                let tracked m = MonoAuth::alloc(i as nat);
                let ghost (old_sids, old_cids, old_mls) = (stamp_ids, cell_ids, mono_locs);
                let ghost (old_st, old_sm, old_cells) = (stamps, sm, cells);
                stamp_ids = stamp_ids.push(stamp.id());
                cell_ids = cell_ids.push(value.id());
                mono_locs = mono_locs.push(m.loc());
                assert(stamp_hist(sh, i as nat, pc.view())) by {
                    assert(sh.msgs()[0] == Msg { val: i, view: tid.view() });
                }
                stamps.tracked_insert(i as nat, sh);
                sm.tracked_insert(i as nat, m);
                cells.tracked_insert(i as nat, pc);
                assert forall|j: nat| j < i + 1 implies {
                    &&& #[trigger] stamps.contains_key(j)
                    &&& stamps[j].loc() == stamp_ids[j as int]
                    &&& stamps[j].msgs().len() > 0
                    &&& forall|k: int| 0 <= k < stamps[j].msgs().len() ==> #[trigger] stamps[j].msgs()[k].val <= j
                    &&& stamp_hist(stamps[j], j, cells[j].view())
                    &&& sm.contains_key(j)
                    &&& sm[j].wf()
                    &&& sm[j].loc() == mono_locs[j as int]
                    &&& sm[j]@ == j
                    &&& cells.contains_key(j)
                    &&& cells[j].value().id() == cell_ids[j as int]
                    &&& cells[j].value().is_uninit()
                } by {
                    if j < i {
                        assert(old_st.contains_key(j));
                        assert(stamp_ids[j as int] == old_sids[j as int]);
                        assert(cell_ids[j as int] == old_cids[j as int]);
                        assert(mono_locs[j as int] == old_mls[j as int]);
                    }
                }
            }
            buffer.push(Slot { stamp, value });
            i = i + 1;
        }
        (buffer, Tracked(stamps), Tracked(sm), Tracked(cells), Ghost((stamp_ids, cell_ids, mono_locs)))
    }

    /// Creates a queue that holds up to `cap` values, and a view of its
    /// (empty) contents.
    pub fn new_with_view(cap: usize) -> (r: (ArrayQueue<T>, Tracked<QueueView<T>>))
        requires
            0 < cap < 0x1000_0000_0000_0000,
        ensures
            r.0.wf(),
            r.0.capacity_spec() == cap,
            r.0.qid() == r.1@.id(),
            r.1@@ == Seq::<T>::empty(),
            r.0.ns() == QUEUE_NS,
    {
        let cap = cap as u64;
        let tracked mut tid = Tid::new();
        let (one_lap, Ghost(shift)) = Self::lap_for(cap);
        let (buffer, Tracked(stamps), Tracked(sm), Tracked(cells), Ghost(ids)) = Self::make_slots(cap, Tracked(&mut tid));
        let ghost (stamp_ids, cell_ids, mono_locs) = ids;
        let (head, Tracked(hp)) = RaU64::new(0, Tracked(&mut tid));
        let (tail, Tracked(tp)) = RaU64::new(0, Tracked(&mut tid));
        let tracked hm = MonoAuth::alloc(0);
        let tracked tm = MonoAuth::alloc(0);
        let tracked (qa, qv) = GhostVarAuth::new(Seq::<T>::empty());
        let tracked (tk, _sub) = GhostMapAuth::<nat, Ticket<T>>::new(Map::empty());
        let ghost slots = Map::new(Set::<nat>::range(0, cap as nat), |j: nat| SlotG { pos: j, phase: Phase::Free });
        let ghost n = model_threads();
        let ghost s0 = St {
            cap: cap as nat,
            head: 0,
            tail: 0,
            st: Seq::new(cap as nat, |k: int| (2 * k) as nat),
            th: Seq::new(n, |i: int| Ph::Idle),
            done: 0,
        };
        let tracked model = Model::<P>::new(s0, n);
        let ghost c = Consts {
            cap: cap as nat,
            lap: one_lap as nat,
            shift,
            head_id: head.id(),
            tail_id: tail.id(),
            stamp_ids,
            cells: cell_ids,
            q_id: qa.id(),
            tk_id: tk.id(),
            head_mono: hm.loc(),
            tail_mono: tm.loc(),
            stamp_mono: mono_locs,
            model: model.loc(),
        };
        let tracked s = Shared {
            head: hp,
            tail: tp,
            hm,
            tm,
            stamps,
            sm,
            cells,
            q: qa,
            tk,
            hd: Ghost(0),
            tl: Ghost(0),
            slots: Ghost(slots),
            vals: Ghost(Map::empty()),
            model,
        };
        proof {
            assert(consts_ok(c));
            lemma_pk_small(c, 0);
            lemma_unpk_pk(c, 0);
            assert(s.head.msgs()[0].val == 0);
            assert(s.tail.msgs()[0].val == 0);
            assert(pos_hist(c, s.head, 0));
            assert(pos_hist(c, s.tail, 0));
            assert(s.q@ =~= abs_queue(s.vals@, 0, 0));
            assert forall|j: nat| j < c.cap implies #[trigger] slot_inv(c, s, j) by {
                lemma_pk_small(c, j);
                vstd::arithmetic::div_mod::lemma_small_mod(j, c.cap);
            }
        }
        let tracked inv = ObjInvariant::<_, _, QueuePred>::new(c, s, QUEUE_NS);
        let q = ArrayQueue {
            head: CachePadded(head),
            tail: CachePadded(tail),
            buffer,
            cap,
            one_lap,
            mask: one_lap - 1,
            inv: Tracked(Some(inv)),
        };
        (q, Tracked(qv))
    }
}

/// Every position in `[H, T)` is held by its slot, pushed or being pushed.
proof fn lemma_coverage<T>(c: Consts, s: Shared<T>, q: nat)
    requires
        QueuePred::inv(c, s),
        s.hd@ <= q < s.tl@,
    ensures
        slot_inv(c, s, q % c.cap),
        s.slots@[q % c.cap].pos == q,
        s.slots@[q % c.cap].phase == Phase::Claimed || s.slots@[q % c.cap].phase == Phase::Full,
{
    let j = q % c.cap;
    lemma_div_mod(q, c.cap);
    assert(slot_inv(c, s, j));
    let g = s.slots@[j];
    if g.pos < q {
        lemma_same_slot(c, g.pos, q);
    } else if g.pos > q {
        lemma_same_slot(c, q, g.pos);
    }
}

impl<T> ArrayQueue<T> {
    /// Drops the values still in the queue. `&mut self` means no push or
    /// pop is in progress.
    fn destroy(&mut self)
        requires
            old(self).wf(),
    {
        let ghost c = self.consts();
        let tracked inv = self.inv.borrow_mut().tracked_take();
        let tracked mut s = inv.into_inner();
        let ghost s0 = s;
        let tracked mut tid = Tid::new();
        // With `&mut self`, this thread has seen every write to the queue.
        self.head.0.sync_exclusive(Tracked(&s.head), Tracked(&mut tid));
        let (head, _) = self.head.0.load_relaxed(Tracked(&s.head), Tracked(&mut tid));
        self.tail.0.sync_exclusive(Tracked(&s.tail), Tracked(&mut tid));
        let (tail, _) = self.tail.0.load_relaxed(Tracked(&s.tail), Tracked(&mut tid));
        let ghost h = s.hd@;
        let ghost t = s.tl@;
        proof {
            lemma_view_join(RaView::bot(), RaView::bot());
        }
        let mut pos = head;
        let ghost mut p = h;
        proof {
            lemma_lap_mono(c, h, t);
        }
        while pos != tail
            invariant
                consts_ok(c),
                c.cap == self.cap as nat,
                c.lap == self.one_lap as nat,
                self.mask as nat == c.lap - 1,
                self.buffer@.len() == c.cap,
                c.cap <= usize::MAX,
                forall|i: int| 0 <= i < c.cap ==> #[trigger] self.buffer@[i].stamp.id() == c.stamp_ids[i],
                forall|i: int| 0 <= i < c.cap ==> #[trigger] self.buffer@[i].value.id() == c.cells[i],
                QueuePred::inv(c, s0),
                h == s0.hd@,
                t == s0.tl@,
                tail as nat == pk(c, t),
                pos as nat == pk(c, p),
                h <= p <= t,
                (t / c.cap) * c.lap + 4 * c.lap <= u64::MAX,
                s.stamps == s0.stamps,
                s.slots == s0.slots,
                forall|q: nat| p <= q < t ==> {
                    let j = #[trigger] (q % c.cap);
                    &&& s.cells.contains_key(j) == s0.cells.contains_key(j)
                    &&& s.cells[j] == s0.cells[j]
                },
            decreases t - p,
        {
            proof {
                assert(p < t);
                lemma_coverage(c, s0, p);
                lemma_decode(c, pos, self.mask, p);
                lemma_lap_mono(c, p, t);
                lemma_pk_bound(c, p);
            }
            let index = pos & self.mask;
            let lap = pos - index;
            let ghost j = index as nat;
            let ghost sh = s.stamps[j];
            let ghost tid0 = tid.view();
            self.buffer[index as usize].stamp.sync_exclusive(Tracked(s.stamps.tracked_borrow(j)), Tracked(&mut tid));
            let slot = &self.buffer[index as usize];
            let (stamp, _) = slot.stamp.load_relaxed(Tracked(s.stamps.tracked_borrow(j)), Tracked(&mut tid));
            if stamp == pos + 1 {
                // Full: the value pushed at `p` is still here, published at
                // a view this thread has now seen.
                proof {
                    lemma_view_join(tid0, sh.last().view);
                    lemma_view_join(tid0.join(sh.last().view), RaView::single(c.stamp_ids[j as int], (sh.msgs().len() - 1) as nat));
                    lemma_view_le_trans(s.cells[j].view(), sh.last().view, tid0.join(sh.last().view));
                    lemma_view_le_trans(s.cells[j].view(), tid0.join(sh.last().view), tid.view());
                }
                let tracked pp = s.cells.tracked_remove(j);
                let tracked mut perm = pp.acquire(&tid);
                let _v = slot.value.take(Tracked(&mut perm));
            }
            let next = if index + 1 < self.cap { pos + 1 } else { lap + self.one_lap };
            proof {
                assert forall|q: nat| p + 1 <= q < t implies {
                    let jq = #[trigger] (q % c.cap);
                    &&& s.cells.contains_key(jq) == s0.cells.contains_key(jq)
                    &&& s.cells[jq] == s0.cells[jq]
                } by {
                    lemma_div_mod(q, c.cap);
                    if q % c.cap == p % c.cap {
                        lemma_same_slot(c, p, q);
                    }
                }
                p = p + 1;
            }
            pos = next;
        }
    }
}

} // verus!

// The plain-Rust API. Each queue operation is verified as a logically
// atomic function (`*_atomic`), which since Verus 2026-11-22 takes its
// atomic update as a `Tracked` argument that survives erasure. These
// one-line wrappers are what code outside Verus calls: they pass a ghost
// value that does not exist at run time (`Tracked::assume_new()`, nothing
// is assumed about the data) and return what the verified function returns.
// A Verus caller uses the `*_atomic` form with an `atomically` block.
impl<T> ArrayQueue<T> {
    /// Appends `value`, or gives it back if the queue holds `capacity` values.
    #[inline]
    pub fn push(&self, value: T) -> Result<(), T> {
        self.push_atomic(value, Tracked::assume_new())
    }

    /// Removes the oldest value, or returns `None` if the queue is empty.
    #[inline]
    pub fn pop(&self) -> Option<T> {
        self.pop_atomic(Tracked::assume_new())
    }

    /// Whether the queue is empty, for a thread that will sleep on the
    /// answer: `true` means it was empty at one instant during the call,
    /// `false` only "maybe not" (see `confirm_empty_atomic`).
    #[inline]
    pub fn confirm_empty(&self) -> bool {
        self.confirm_empty_atomic(Tracked::assume_new())
    }

    /// Whether the queue is full, for a thread that will sleep on the
    /// answer: `true` means it was full at one instant during the call,
    /// `false` only "maybe not" (see `confirm_full_atomic`).
    #[inline]
    pub fn confirm_full(&self) -> bool {
        self.confirm_full_atomic(Tracked::assume_new())
    }
}


impl<T> Drop for ArrayQueue<T> {
    fn drop(&mut self) {
        self.destroy();
    }
}

impl<T> ArrayQueue<T> {
    /// Creates a queue that holds up to `cap` values.
    ///
    /// # Panics
    ///
    /// If `cap` is zero or at least 2^60 (more than can be allocated).
    pub fn new(cap: usize) -> ArrayQueue<T> {
        assert!(cap > 0, "capacity must be non-zero");
        assert!((cap as u64) < 0x1000_0000_0000_0000, "capacity must be below 2^60");
        Self::new_with_view(cap).0
    }
}
