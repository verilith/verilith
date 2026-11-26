//! A verified reader-writer lock with parking_lot's `RwLock` API.
//!
//! One 32-bit word holds the whole lock: bit 0 is the writer, bit 1 says
//! threads may be parked, bit 2 says a writer is waiting (which holds off
//! new readers, so writers do not starve), and the rest counts readers.
//! What is proved: a write guard excludes every other guard, read guards
//! only ever see the data shared, and the data is dropped exactly once. The
//! proof does not depend on the parking code, nor on bits 1 and 2.
#![allow(non_snake_case, non_shorthand_field_patterns, unused_imports)]
use crate::lot::*;
use crate::model::*;
use crate::progress::rwlock::{P, Ph, St, Th, Word};
#[cfg(verus_only)]
use crate::progress::rwlock::{blocks_read, blocks_write, go, gow, inv, lists, ph, step, zero};
use crate::util::*;
use std::sync::Arc;
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::resource::Loc;
use verus_state_machines_macros::tokenized_state_machine;

// The state machine's generated items (its tokens, steps and lemmas) get
// no docs from the macro.
#[allow(missing_docs)]
mod toks {
    use super::*;

    tokenized_state_machine!(
    RwToks<T> {
        fields {
            #[sharding(constant)]
            pub cell: CellId,

            /// A writer holds the lock.
            #[sharding(variable)]
            pub exc: bool,

            /// How many readers hold the lock.
            #[sharding(variable)]
            pub rc: nat,

            /// The data, while no writer holds it.
            #[sharding(storage_option)]
            pub storage: Option<PointsTo<T>>,

            #[sharding(option)]
            pub writer: Option<()>,

            /// Each reader's view of the data.
            #[sharding(multiset)]
            pub reader: Multiset<PointsTo<T>>,
        }

        pub open spec fn ok(cell: CellId, p: PointsTo<T>) -> bool {
            p.id() == cell && p.is_init()
        }

        init!{
            initialize(cell: CellId, p: PointsTo<T>) {
                require Self::ok(cell, p);
                init cell = cell;
                init exc = false;
                init rc = 0;
                init storage = Option::Some(p);
                init writer = Option::None;
                init reader = Multiset::empty();
            }
        }

        transition!{
            acquire_read() {
                require !pre.exc;
                update rc = pre.rc + 1;
                birds_eye let p = pre.storage->0;
                add reader += {p};
                assert Self::ok(pre.cell, p);
            }
        }

        transition!{
            acquire_write() {
                require !pre.exc;
                require pre.rc == 0;
                update exc = true;
                add writer += Some(());
                birds_eye let p = pre.storage->0;
                withdraw storage -= Some(p);
                assert Self::ok(pre.cell, p);
            }
        }

        transition!{
            release_write(p: PointsTo<T>) {
                require Self::ok(pre.cell, p);
                remove writer -= Some(());
                update exc = false;
                deposit storage += Some(p);
            }
        }

        transition!{
            release_read(p: PointsTo<T>) {
                remove reader -= {p};
                assert pre.rc >= 1 by {
                    assert(pre.storage == Option::Some(p));
                };
                update rc = (pre.rc - 1) as nat;
            }
        }

        transition!{
            downgrade(p: PointsTo<T>) {
                require Self::ok(pre.cell, p);
                remove writer -= Some(());
                update exc = false;
                update rc = pre.rc + 1;
                deposit storage += Some(p);
                add reader += {p};
            }
        }

        property!{
            read_guard(p: PointsTo<T>) {
                have reader >= {p};
                guard storage >= Some(p);
            }
        }

        property!{
            reader_counted(p: PointsTo<T>) {
                have reader >= {p};
                assert pre.rc >= 1 by {
                    assert(pre.storage == Option::Some(p));
                };
            }
        }

        property!{
            writer_alone() {
                have writer >= Some(());
                assert pre.rc == 0 && pre.exc;
            }
        }

        #[invariant]
        pub fn exc_is_writer(&self) -> bool {
            self.exc == (self.writer is Some)
        }

        #[invariant]
        pub fn writer_took_storage(&self) -> bool {
            (self.writer is Some) == (self.storage is None)
        }

        #[invariant]
        pub fn rc_counts_readers(&self) -> bool {
            self.rc == self.reader.count(self.storage->0)
        }

        #[invariant]
        pub fn readers_see_storage(&self) -> bool {
            forall|p: PointsTo<T>| #[trigger] self.reader.count(p) > 0 ==> self.storage == Option::Some(p)
        }

        #[invariant]
        pub fn storage_ok(&self) -> bool {
            self.storage matches Option::Some(p) ==> Self::ok(self.cell, p)
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cell: CellId, p: PointsTo<T>) {
            broadcast use group_multiset_axioms;
        }

        #[inductive(acquire_read)]
        fn acquire_read_inductive(pre: Self, post: Self) {
            broadcast use group_multiset_axioms;
        }

        #[inductive(acquire_write)]
        fn acquire_write_inductive(pre: Self, post: Self) {
            broadcast use group_multiset_axioms;
            assert forall|p: PointsTo<T>| #[trigger] post.reader.count(p) == 0 by {
                if post.reader.count(p) > 0 {
                    assert(pre.storage == Option::Some(p));
                }
            }
        }

        #[inductive(release_write)]
        fn release_write_inductive(pre: Self, post: Self, p: PointsTo<T>) {
            broadcast use group_multiset_axioms;
            assert forall|q: PointsTo<T>| #[trigger] pre.reader.count(q) == 0 by {
                if pre.reader.count(q) > 0 {
                    assert(pre.storage == Option::Some(q));
                }
            }
        }

        #[inductive(release_read)]
        fn release_read_inductive(pre: Self, post: Self, p: PointsTo<T>) {
            broadcast use group_multiset_axioms;
            assert(pre.storage == Option::Some(p));
        }

        #[inductive(downgrade)]
        fn downgrade_inductive(pre: Self, post: Self, p: PointsTo<T>) {
            broadcast use group_multiset_axioms;
            assert forall|q: PointsTo<T>| #[trigger] pre.reader.count(q) == 0 by {
                if pre.reader.count(q) > 0 {
                    assert(pre.storage == Option::Some(q));
                }
            }
        }
    });
}
/// The ghost tokens of the lock: see the module docs.
pub use toks::RwToks;

verus! {

const WRITER: u32 = 1;
const PARKED: u32 = 2;
// Named for the docs. The masks below are literals, not `WRITER |
// WRITER_WAITING` and so on, because the proofs about them need the values.
#[allow(dead_code)]
const WRITER_WAITING: u32 = 4;
const ONE_READER: u32 = 8;
/// Bits that keep new readers out: `WRITER | WRITER_WAITING`.
const BLOCKS_READ: u32 = 5;
/// Both flag bits: `PARKED | WRITER_WAITING`.
const FLAGS: u32 = 6;
const NOT_FLAGS: u32 = 0xffff_fff9;
/// The largest state a reader may add itself to.
const MAX_FOR_READ: u32 = 0xffff_fff0;

pub open spec fn has_writer(s: u32) -> bool {
    s & 1 == 1
}

pub open spec fn readers(s: u32) -> nat {
    (s >> 3) as nat
}

proof fn lemma_add_reader(s: u32)
    requires
        s & 1 == 0,
        s <= 0xffff_fff0,
    ensures
        (add(s, 8) as u32) & 1 == 0,
        (add(s, 8) as u32) >> 3 == (s >> 3) + 1,
{
    assert((add(s, 8) as u32) & 1 == 0 && (add(s, 8) as u32) >> 3 == (s >> 3) + 1) by (bit_vector)
        requires
            s & 1 == 0,
            s <= 0xffff_fff0,
    ;
}

proof fn lemma_sub_reader(s: u32)
    requires
        s >> 3 >= 1,
    ensures
        s >= 8,
        (sub(s, 8) as u32) & 1 == s & 1,
        (sub(s, 8) as u32) >> 3 == (s >> 3) - 1,
{
    assert(s >= 8 && (sub(s, 8) as u32) & 1 == s & 1 && (sub(s, 8) as u32) >> 3 == (s >> 3) - 1) by (bit_vector)
        requires
            s >> 3 >= 1,
    ;
}

proof fn lemma_set_writer(s: u32)
    requires
        s & 1 == 0,
        s >> 3 == 0,
    ensures
        (s | 1) & 1 == 1,
        (s | 1) >> 3 == 0,
{
    assert((s | 1) & 1 == 1 && (s | 1) >> 3 == 0) by (bit_vector)
        requires
            s & 1 == 0,
            s >> 3 == 0,
    ;
}

proof fn lemma_flag_bits(s: u32, b: u32)
    requires
        b == 2 || b == 6,
    ensures
        (s | b) & 1 == s & 1,
        (s | b) >> 3 == s >> 3,
        (s & 0xffff_fff9) & 1 == s & 1,
        (s & 0xffff_fff9) >> 3 == s >> 3,
        s & 5 == 0 ==> s & 1 == 0,
{
    assert((s | b) & 1 == s & 1 && (s | b) >> 3 == s >> 3 && (s & 0xffff_fff9) & 1 == s & 1 && (s & 0xffff_fff9) >> 3 == s >> 3
        && (s & 5 == 0 ==> s & 1 == 0)) by (bit_vector)
        requires
            b == 2 || b == 6,
    ;
}

proof fn lemma_downgrade(s: u32)
    requires
        s & 1 == 1,
        s >> 3 == 0,
    ensures
        s <= 7,
        (add(s, 7) as u32) & 1 == 0,
        (add(s, 7) as u32) >> 3 == 1,
{
    assert(s <= 7 && (add(s, 7) as u32) & 1 == 0 && (add(s, 7) as u32) >> 3 == 1) by (bit_vector)
        requires
            s & 1 == 1,
            s >> 3 == 0,
    ;
}

proof fn lemma_zero()
    ensures
        0u32 & 1 == 0,
        0u32 >> 3 == 0,
{
    assert(0u32 & 1 == 0 && 0u32 >> 3 == 0) by (bit_vector);
}

/// The lock word as the model's fields.
pub open spec fn word(v: u32) -> Word {
    Word { w: v & 1 == 1, pk: v & 2 == 2, ww: v & 4 == 4, rc: (v >> 3) as nat }
}

/// The word is free for this kind of lock.
pub open spec fn free(wr: bool, x: Word) -> bool {
    if wr { !blocks_write(x) } else { !blocks_read(x) }
}

/// The hints this kind of waiter sets before it sleeps are all set.
pub open spec fn hinted(wr: bool, x: Word) -> bool {
    if wr { x.pk && x.ww } else { x.pk }
}

/// Where the model's `Load` step goes on seeing `x`; `give_up` is a
/// `try_*` call that fails at once.
pub open spec fn after_load(wr: bool, x: Word, left: nat, give_up: bool) -> Ph {
    if free(wr, x) {
        Ph::Cas { wr, s: x, left }
    } else if give_up {
        Ph::Idle
    } else if !x.pk && left > 0 {
        Ph::Load { wr, left: (left - 1) as nat }
    } else if !hinted(wr, x) {
        Ph::Flag { wr, s: x, left }
    } else {
        Ph::Check { wr, left }
    }
}

/// The tests the code makes on the word, as the model's.
proof fn lemma_word_tests(s: u32)
    ensures
        free(false, word(s)) == (s & 5 == 0),
        free(true, word(s)) == (s & 1 == 0 && s >> 3 == 0),
        word(s).pk == (s & 2 != 0),
        hinted(true, word(s)) == (s & 6 == 6),
        (word(s).pk || word(s).ww) == (s & 6 != 0),
        word(s).w == (s & 1 != 0),
        free(false, word(s)) ==> s & 1 == 0,
{
    assert(((s & 5 == 0) == !(s & 1 == 1 || s & 4 == 4)) && ((s & 2 != 0) == (s & 2 == 2)) && ((s & 6 == 6) == (s & 2 == 2 && s & 4 == 4))
        && ((s & 6 != 0) == (s & 2 == 2 || s & 4 == 4)) && ((s & 1 != 0) == (s & 1 == 1)) && ((s & 5 == 0) ==> s & 1 == 0)) by (bit_vector);
}

/// The word determines the value.
proof fn lemma_word_inj(a: u32, b: u32)
    requires
        word(a) == word(b),
    ensures
        a == b,
{
    assert(word(a).rc == word(b).rc);
    assert(a >> 3 == b >> 3);
    assert(a == b) by (bit_vector)
        requires
            (a & 1 == 1) == (b & 1 == 1),
            (a & 2 == 2) == (b & 2 == 2),
            (a & 4 == 4) == (b & 4 == 4),
            a >> 3 == b >> 3,
    ;
}

/// The word after each update the code makes.
proof fn lemma_word_updates(s: u32)
    ensures
        s <= 0xffff_fff0 ==> word(add(s, 8) as u32) == (Word { rc: word(s).rc + 1, ..word(s) }),
        s >> 3 >= 1 ==> s >= 8 && word(sub(s, 8) as u32) == (Word { rc: (word(s).rc - 1) as nat, ..word(s) }),
        word(s | 1) == (Word { w: true, ..word(s) }),
        word(s | 2) == (Word { pk: true, ..word(s) }),
        word(s | 6) == (Word { pk: true, ww: true, ..word(s) }),
        word(s & 0xffff_fff9) == (Word { pk: false, ww: false, ..word(s) }),
        s & 1 == 1 && s >> 3 == 0 ==> s <= 7 && word(add(s, 7) as u32) == (Word { w: false, rc: 1, ..word(s) }),
        word(0) == zero(),
{
    if s <= 0xffff_fff0 {
        let t = add(s, 8) as u32;
        assert(t & 1 == s & 1 && t & 2 == s & 2 && t & 4 == s & 4 && t >> 3 == (s >> 3) + 1) by (bit_vector)
            requires
                s <= 0xffff_fff0,
                t == add(s, 8) as u32,
        ;
    }
    if s >> 3 >= 1 {
        assert(s >= 8) by (bit_vector)
            requires
                s >> 3 >= 1,
        ;
        let t = sub(s, 8) as u32;
        assert(t & 1 == s & 1 && t & 2 == s & 2 && t & 4 == s & 4 && t >> 3 == (s >> 3) - 1) by (bit_vector)
            requires
                s >> 3 >= 1,
                t == sub(s, 8) as u32,
        ;
    }
    assert((s | 1) & 1 == 1 && (s | 1) & 2 == s & 2 && (s | 1) & 4 == s & 4 && (s | 1) >> 3 == s >> 3) by (bit_vector);
    assert((s | 2) & 1 == s & 1 && (s | 2) & 2 == 2 && (s | 2) & 4 == s & 4 && (s | 2) >> 3 == s >> 3) by (bit_vector);
    assert((s | 6) & 1 == s & 1 && (s | 6) & 2 == 2 && (s | 6) & 4 == 4 && (s | 6) >> 3 == s >> 3) by (bit_vector);
    assert((s & 0xffff_fff9) & 1 == s & 1 && (s & 0xffff_fff9) & 2 == 0 && (s & 0xffff_fff9) & 4 == 0 && (s & 0xffff_fff9) >> 3 == s >> 3) by (bit_vector);
    if s & 1 == 1 && s >> 3 == 0 {
        assert(s <= 7) by (bit_vector)
            requires
                s >> 3 == 0,
        ;
        let t = add(s, 7) as u32;
        assert(t & 1 == 0 && t & 2 == s & 2 && t & 4 == s & 4 && t >> 3 == 1) by (bit_vector)
            requires
                s & 1 == 1,
                s >> 3 == 0,
                t == add(s, 7) as u32,
        ;
    }
    assert(0u32 & 1 == 0 && 0u32 & 2 == 0 && 0u32 & 4 == 0 && 0u32 >> 3 == 0) by (bit_vector);
}

/// The number of threads in each lock's model: any number (see
/// `model::Model::pool_nonempty`).
pub uninterp spec fn model_threads() -> nat;

/// How many times a waiter snoozes before it sets the parking hints: what
/// `Backoff::is_completed` allows.
pub const SPINS: u8 = 11;

/// The lock's constants: the ids of its atomic, its token instance and its
/// ghost state.
pub ghost struct RwConsts {
    /// The id of the state atomic.
    pub state: int,
    /// The id of the `RwToks` instance.
    pub inst: vstd::resource::Loc,
    /// The progress model's.
    pub model: Loc,
    /// The waiter list's (`lot`'s `list`).
    pub list: Loc,
    /// The waiters' records'.
    pub recs: Loc,
}

/// What the lock's invariant owns.
pub tracked struct RwShared<T> {
    /// The state atomic's permission.
    pub state: PermissionU32,
    /// The token saying whether a writer holds the lock.
    pub exc: RwToks::exc<T>,
    /// The token counting readers.
    pub rc: RwToks::rc<T>,
    /// The progress model, which the code follows step by step.
    pub model: Model<P>,
    /// The model's list, with each ticket's waiter id; the parking lot
    /// holds the other half.
    pub list: GhostVarAuth<Map<nat, u64>>,
    /// Every waiter's record, by ticket: the authority.
    pub recs_auth: GhostMapAuth<nat, Rec>,
    /// Every waiter's record, by ticket.
    pub recs: GhostPersistentSubmap<nat, Rec>,
    /// Every waiter's `notified` flag, by ticket.
    pub flags: Map<nat, PermissionBool>,
}

/// The lock's invariant (see its `inv`).
pub struct RwPred;

impl<T> InvariantPredicate<RwConsts, RwShared<T>> for RwPred {
    open spec fn inv(c: RwConsts, s: RwShared<T>) -> bool {
        let m = s.model@;
        &&& s.state@.patomic == c.state
        &&& s.exc.instance_id() == c.inst
        &&& s.rc.instance_id() == c.inst
        &&& s.exc.value() == has_writer(s.state@.value)
        &&& s.rc.value() == readers(s.state@.value)
        &&& s.model.wf()
        &&& s.model.loc() == c.model
        &&& s.model.n() == model_threads()
        &&& m.word == word(s.state@.value)
        &&& s.list.id() == c.list
        &&& s.list@.dom() == m.list
        &&& s.recs_auth.id() == c.recs
        &&& s.recs.id() == c.recs
        &&& s.recs_auth@ == s.recs@
        &&& s.recs@.dom() =~= Set::range(0, m.next_tk)
        &&& forall|tk: nat| #[trigger] s.list@.contains_key(tk) ==> s.list@[tk] == s.recs@[tk].1
        &&& s.flags.dom() =~= Set::range(0, m.next_tk)
        &&& forall|tk: nat| tk < m.next_tk ==> {
            &&& (#[trigger] s.flags[tk]).id() == s.recs@[tk].0
            &&& s.flags[tk].value() == m.notified.contains(tk)
        }
    }
}

/// A reader-writer lock, with parking_lot's `RwLock` API.
pub struct RwLock<T> {
    state: PAtomicU32,
    data: PCell<T>,
    inst: Tracked<RwToks::Instance<T>>,
    /// `None` only while the lock is being dropped.
    inv: Tracked<Option<AtomicInvariant<RwConsts, RwShared<T>, RwPred>>>,
}

/// Proof that the holder reads the data, shared with other readers.
pub struct RwLockReadGuard<'a, T> {
    lock: &'a RwLock<T>,
    /// `Some` until the guard is dropped.
    handle: Tracked<Option<RwToks::reader<T>>>,
    /// The model thread of the call that took the lock, holding it.
    tok: Tracked<Option<Tok<P>>>,
}

/// Proof that the holder alone has the data.
pub struct RwLockWriteGuard<'a, T> {
    lock: &'a RwLock<T>,
    /// `Some` until the guard is dropped or downgraded.
    perm: Tracked<Option<PointsTo<T>>>,
    handle: Tracked<Option<RwToks::writer<T>>>,
    /// The model thread of the call that took the lock, holding it.
    tok: Tracked<Option<Tok<P>>>,
}

/// The token is for a thread of the lock's model, in phase `p`.
pub open spec fn tok_at(tok: Tok<P>, c: RwConsts, p: Ph) -> bool {
    tok.id() == c.model && tok.value().ph == p
}

impl<T> RwLock<T> {
    pub closed spec fn consts(&self) -> RwConsts {
        self.inv@->0.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.inv@ is Some
        &&& self.consts().state == self.state.id()
        &&& self.consts().inst == self.inst@.id()
        &&& self.inst@.cell() == self.data.id()
    }

    /// What the parking lot knows of this lock.
    pub closed spec fn lot(&self) -> LotId {
        LotId { list: self.consts().list, recs: self.consts().recs }
    }

    pub closed spec fn reads(&self, h: Option<RwToks::reader<T>>) -> bool {
        h matches Some(r) && {
            &&& r.instance_id() == self.inst@.id()
            &&& r.element().id() == self.data.id()
            &&& r.element().is_init()
        }
    }

    pub closed spec fn writes(&self, w: Option<(PointsTo<T>, RwToks::writer<T>)>) -> bool {
        w matches Some((p, h)) && {
            &&& h.instance_id() == self.inst@.id()
            &&& p.id() == self.data.id()
            &&& p.is_init()
        }
    }

    /// A lock holding `value`, unlocked.
    pub fn new(value: T) -> (l: Self)
        ensures
            l.wf(),
    {
        let (data, Tracked(perm)) = PCell::new(value);
        let (state, Tracked(sp)) = PAtomicU32::new(0);
        let tracked (Tracked(inst), Tracked(exc), Tracked(rc), _, _) = RwToks::Instance::initialize(
            data.id(),
            perm,
            Some(perm),
        );
        proof {
            lemma_zero();
            lemma_word_updates(0);
            lemma_zero();
        }
        let ghost n = model_threads();
        let ghost s0 = St {
            word: zero(),
            th: Seq::new(n, |i: int| Th { ph: Ph::Idle, timed: false }),
            list: Set::empty(),
            owner: Map::empty(),
            notified: Set::empty(),
            next_tk: 0,
        };
        let tracked model = Model::<P>::new(s0, n);
        // The parking lot owns the other half of the list.
        let tracked (list, _lot_half) = GhostVarAuth::<Map<nat, u64>>::new(Map::empty());
        let tracked (recs_auth, recs0) = GhostMapAuth::<nat, Rec>::new(Map::empty());
        let tracked recs = recs0.persist();
        let ghost c = RwConsts {
            state: state.id(),
            inst: inst.id(),
            model: model.loc(),
            list: list.id(),
            recs: recs_auth.id(),
        };
        let tracked s = RwShared { state: sp, exc, rc, model, list, recs_auth, recs, flags: Map::tracked_empty() };
        proof {
            assert(s.list@.dom() =~= Set::<nat>::empty());
        }
        let tracked inv = AtomicInvariant::<_, _, RwPred>::new(c, s, 0x7277);
        RwLock { state, data, inst: Tracked(inst), inv: Tracked(Some(inv)) }
    }

    /// The parking-lot key: the address of the lock word (see
    /// `Mutex::key` for why not the lock's own address).
    ///
    /// TRUSTED (`lot`): the proof that this is the key.
    #[verifier::external_body]
    fn key(&self) -> (r: (usize, Tracked<KeyOf>))
        ensures
            r.1@.key() == r.0,
            r.1@.lot() == self.lot(),
    {
        (&self.state as *const PAtomicU32 as usize, Tracked::assume_new())
    }

    /// A call starts: it takes an idle model thread and starts a read
    /// (at its first load) or a write (at its CAS from 0), `timed` for the
    /// `try_*` calls, with `left` snoozes.
    #[inline(always)]
    fn enter(&self, Ghost(wr): Ghost<bool>, Ghost(timed): Ghost<bool>, Ghost(left): Ghost<nat>) -> (r: Tracked<Tok<P>>)
        requires
            self.wf(),
        ensures
            tok_at(r@, self.consts(), if wr { Ph::Cas { wr: true, s: zero(), left } } else { Ph::Load { wr: false, left } }),
            r@.value().timed == timed,
    {
        let tracked mut tok;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                tok = s.model.enter();
                s.model.agree(&tok);
                let m = s.model@;
                let t = tok.key();
                let a = St { th: m.th.update(t as int, Th { ph: Ph::Load { wr: false, left }, timed }), ..m };
                let b = St { th: m.th.update(t as int, Th { ph: Ph::Cas { wr: true, s: zero(), left }, timed }), ..m };
                let s2 = if wr { b } else { a };
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
            }
        });
        Tracked(tok)
    }

    /// A call returns: its model thread, idle again, goes back.
    #[inline(always)]
    fn leave(&self, Tracked(tok): Tracked<Tok<P>>)
        requires
            self.wf(),
            tok_at(tok, self.consts(), Ph::Idle),
    {
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.leave(tok);
            }
        });
    }

    #[inline(always)]
    fn load(&self) -> u32
        requires
            self.wf(),
    {
        let v;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            v = self.state.load(Tracked(&s.state));
        });
        v
    }

    /// The load of the word in a lock call, the model's `Load`.
    #[inline(always)]
    fn load_at(&self, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(wr): Ghost<bool>, Ghost(left): Ghost<nat>, Ghost(give_up): Ghost<bool>) -> (v: u32)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Load { wr, left }),
            give_up ==> old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.consts(), after_load(wr, word(v), left, give_up)),
            final(tok).value().timed == old(tok).value().timed,
    {
        let v;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            v = self.state.load(Tracked(&s.state));
            proof {
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = go(m, t, after_load(wr, word(v), left, give_up));
                assert(s2.th[t as int].ph == after_load(wr, word(v), left, give_up));
                assert(go(m, t, Ph::Idle).th[t as int].ph == Ph::Idle);
                assert(step(m, t, s2));
                s.model.step(tok, s2);
            }
        });
        v
    }

    /// Adds a reader if the word still holds `cur`, the model's `Cas` for
    /// a reader. On failure the thread reloads, or gives up.
    #[inline(always)]
    fn cas_read(&self, cur: u32, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(left): Ghost<nat>, Ghost(give_up): Ghost<bool>) -> (r: (bool, Tracked<Option<RwToks::reader<T>>>))
        requires
            self.wf(),
            cur & 1 == 0,
            cur <= MAX_FOR_READ,
            tok_at(*old(tok), self.consts(), Ph::Cas { wr: false, s: word(cur), left }),
            give_up ==> old(tok).value().timed,
        ensures
            r.0 ==> self.reads(r.1@),
            tok_at(*final(tok), self.consts(), if r.0 { Ph::RCrit } else if give_up { Ph::Idle } else { Ph::Load { wr: false, left } }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(tok);
                s.model.lemma_inv();
                lemma_word_tests(cur);
                lemma_word_updates(cur);
            }
            let ghost v0 = s.state@.value;
            ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur + ONE_READER) {
                Ok(_) => true,
                Err(_) => false,
            };
            proof {
                let m = s.model@;
                let t = tok.key();
                if ok {
                    lemma_add_reader(cur);
                    let tracked (_, Tracked(h)) = self.inst.borrow().acquire_read(&s.exc, &mut s.rc);
                    got = Some(h);
                    let s2 = gow(m, t, Ph::RCrit, Word { rc: m.word.rc + 1, ..m.word });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                } else {
                    if m.word == word(cur) {
                        lemma_word_inj(v0, cur);
                    }
                    let s2 = go(m, t, if give_up { Ph::Idle } else { Ph::Load { wr: false, left } });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            }
        });
        (ok, Tracked(got))
    }

    /// Sets the writer bit if the word still holds `cur`, the model's `Cas`
    /// for a writer. On failure the thread reloads, or gives up.
    #[inline(always)]
    fn cas_write(&self, cur: u32, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(left): Ghost<nat>, Ghost(give_up): Ghost<bool>) -> (r: (bool, Tracked<Option<(PointsTo<T>, RwToks::writer<T>)>>))
        requires
            self.wf(),
            cur & 1 == 0,
            cur >> 3 == 0,
            tok_at(*old(tok), self.consts(), Ph::Cas { wr: true, s: word(cur), left }),
            give_up ==> old(tok).value().timed,
        ensures
            r.0 ==> self.writes(r.1@),
            tok_at(*final(tok), self.consts(), if r.0 { Ph::WCrit } else if give_up { Ph::Idle } else { Ph::Load { wr: true, left } }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(tok);
                s.model.lemma_inv();
                lemma_word_tests(cur);
                lemma_word_updates(cur);
            }
            let ghost v0 = s.state@.value;
            ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur | WRITER) {
                Ok(_) => true,
                Err(_) => false,
            };
            proof {
                let m = s.model@;
                let t = tok.key();
                if ok {
                    lemma_set_writer(cur);
                    let tracked (_, Tracked(p), Tracked(h)) = self.inst.borrow().acquire_write(&mut s.exc, &s.rc);
                    got = Some((p, h));
                    let s2 = gow(m, t, Ph::WCrit, Word { w: true, ..m.word });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                } else {
                    if m.word == word(cur) {
                        lemma_word_inj(v0, cur);
                    }
                    let s2 = go(m, t, if give_up { Ph::Idle } else { Ph::Load { wr: true, left } });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            }
        });
        (ok, Tracked(got))
    }

    /// Sets the hints (`PARKED` for a reader, that and `WRITER_WAITING`
    /// for a writer) if the word still holds `cur`, the model's `Flag`.
    #[inline(always)]
    fn cas_flags(&self, cur: u32, bits: u32, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(wr): Ghost<bool>, Ghost(left): Ghost<nat>)
        requires
            self.wf(),
            bits == if wr { FLAGS } else { PARKED },
            tok_at(*old(tok), self.consts(), Ph::Flag { wr, s: word(cur), left }),
        ensures
            tok_at(*final(tok), self.consts(), Ph::Load { wr, left }),
            final(tok).value().timed == old(tok).value().timed,
    {
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                lemma_flag_bits(cur, bits);
                lemma_word_updates(cur);
                s.model.agree(tok);
            }
            let ghost v0 = s.state@.value;
            let ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur | bits) {
                Ok(_) => true,
                Err(_) => false,
            };
            proof {
                let m = s.model@;
                let t = tok.key();
                if ok {
                    let s2 = gow(m, t, Ph::Load { wr, left }, Word { pk: true, ww: m.word.ww || wr, ..m.word });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                } else {
                    if m.word == word(cur) {
                        lemma_word_inj(v0, cur);
                    }
                    let s2 = go(m, t, Ph::Load { wr, left });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            }
        });
    }

    /// What a waiter does when the word is not free: snooze, set the
    /// hints, or sleep. False when it gives up at the deadline.
    #[cold]
    fn wait(&self, s: u32, wr: bool, left: &mut u8, backoff: &Backoff, deadline: &Deadline, Tracked(tok): Tracked<&mut Tok<P>>) -> (ok: bool)
        requires
            self.wf(),
            !free(wr, word(s)),
            tok_at(*old(tok), self.consts(), after_load(wr, word(s), *old(left) as nat, false)),
            has_deadline(*deadline) ==> old(tok).value().timed,
        ensures
            final(tok).value().timed == old(tok).value().timed,
            ok ==> tok_at(*final(tok), self.consts(), Ph::Load { wr, left: *final(left) as nat }),
            !ok ==> tok_at(*final(tok), self.consts(), Ph::Idle) && old(tok).value().timed,
    {
        proof {
            lemma_word_tests(s);
        }
        let unhinted = if wr { s & FLAGS != FLAGS } else { s & PARKED == 0 };
        if s & PARKED == 0 && *left > 0 {
            backoff.snooze();
            *left = *left - 1;
            true
        } else if unhinted {
            self.cas_flags(s, if wr { FLAGS } else { PARKED }, Tracked(&mut *tok), Ghost(wr), Ghost(*left as nat));
            true
        } else {
            self.park(wr, *left, deadline, Tracked(&mut *tok))
        }
    }

    /// The model's `Check` and `Asleep`: sleeps while still blocked with
    /// the parked hint set. False when it gives up at the deadline.
    #[verifier::exec_allows_no_decreases_clause]
    fn park(&self, wr: bool, left: u8, deadline: &Deadline, Tracked(tok): Tracked<&mut Tok<P>>) -> (ok: bool)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Check { wr, left: left as nat }),
            has_deadline(*deadline) ==> old(tok).value().timed,
        ensures
            final(tok).value().timed == old(tok).value().timed,
            ok ==> tok_at(*final(tok), self.consts(), Ph::Load { wr, left: left as nat }),
            !ok ==> tok_at(*final(tok), self.consts(), Ph::Idle) && old(tok).value().timed,
    {
        let ghost timed = tok.value().timed;
        let (late, _) = time_left(deadline);
        match self.check(wr, left, late, Tracked(&mut *tok)) {
            None => !late,
            Some(me) => {
                loop
                    invariant
                        self.wf(),
                        me.wf(),
                        me.lot@ == self.lot(),
                        me.brec@.id() == bucket_loc(me.key),
                        tok_at(*tok, self.consts(), Ph::Asleep { wr, tk: me.tk@, left: left as nat }),
                        tok.value().timed == timed,
                        timed == old(tok).value().timed,
                        has_deadline(*deadline) ==> timed,
                {
                    if self.wait_flag(&me, wr, left, Tracked(&mut *tok)) {
                        return true;
                    }
                    let (late, rest) = time_left(deadline);
                    if late {
                        match self.timeout(&me, wr, left, Tracked(&mut *tok)) {
                            Some(again) => return again,
                            None => {},
                        }
                    }
                    park_for(rest);
                }
            },
        }
    }

    /// The model's `Check`: the bucket's critical section that re-checks
    /// the word and, if it is still blocked with the parked hint set, lists
    /// the thread and gives it its waiter. If not, it reloads, or gives up
    /// if it is `late`.
    #[cold]
    fn check(&self, wr: bool, left: u8, late: bool, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: Option<Arc<Waiter>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Check { wr, left: left as nat }),
            late ==> old(tok).value().timed,
        ensures
            final(tok).value().timed == old(tok).value().timed,
            r matches Some(me) ==> {
                &&& me.wf()
                &&& me.lot@ == self.lot()
                &&& me.brec@.id() == bucket_loc(me.key)
                &&& tok_at(*final(tok), self.consts(), Ph::Asleep { wr, tk: me.tk@, left: left as nat })
            },
            r is None ==> tok_at(*final(tok), self.consts(), if late { Ph::Idle } else { Ph::Load { wr, left: left as nat } }),
    {
        let (key, Tracked(kf)) = self.key();
        let (notified, Tracked(perm)) = PAtomicBool::new(false);
        let (g, mut l, Tracked(half), Tracked(bids)) = lock_bucket(key, Tracked(&kf));
        let tracked mut half = half;
        let tracked mut bids = bids;
        if l.next == u64::MAX {
            exhausted();
        }
        let id = l.next;
        let ghost q0 = l.q@;
        let ghost half0 = half@;
        let ghost mut tk: nat = 0;
        let tracked mut rec: Option<GhostPersistentPointsTo<nat, Rec>> = None;
        let v;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            v = self.state.load(Tracked(&s.state));
            proof {
                s.list.agree(&half);
                s.model.agree(tok);
                s.model.lemma_inv();
                lemma_word_tests(v);
                let m = s.model@;
                let t = tok.key();
                if !free(wr, word(v)) && word(v).pk {
                    tk = m.next_tk;
                    let s2 = St {
                        list: m.list.insert(tk),
                        owner: m.owner.insert(tk, t),
                        next_tk: tk + 1,
                        ..go(m, t, Ph::Asleep { wr, tk, left: left as nat })
                    };
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    assert(!m.list.contains(tk));
                    let tracked p = s.recs_auth.insert(tk, (notified.id(), id));
                    let tracked pp = p.persist();
                    rec = Some(pp.duplicate());
                    s.recs.combine_points_to(pp);
                    s.flags.tracked_insert(tk, perm);
                    s.list.update(&mut half, half0.insert(tk, id));
                    assert(s.list@.dom() =~= s2.list);
                    assert(s.recs@ == s.recs_auth@);
                    assert(s.recs@.dom() =~= Set::range(0, s2.next_tk));
                    assert(s.flags.dom() =~= Set::range(0, s2.next_tk));
                    assert forall|x: nat| x < s2.next_tk implies {
                        &&& (#[trigger] s.flags[x]).id() == s.recs@[x].0
                        &&& s.flags[x].value() == s2.notified.contains(x)
                    } by {
                        if x != tk {
                            assert(x < m.next_tk);
                        }
                    }
                    assert forall|x: nat| #[trigger] s.list@.contains_key(x) implies s.list@[x] == s.recs@[x].1 by {
                        if x != tk {
                            assert(half0.contains_key(x));
                        }
                    }
                } else {
                    let s2 = go(m, t, if late { Ph::Idle } else { Ph::Load { wr, left: left as nat } });
                    assert(s2.th[t as int].ph == (if late { Ph::Idle } else { Ph::Load { wr, left: left as nat } }));
                    assert(go(m, t, Ph::Idle).th[t as int].ph == Ph::Idle);
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            }
        });
        proof {
            lemma_word_tests(v);
        }
        let blocked = if wr { v & WRITER != 0 || v >> 3 != 0 } else { v & BLOCKS_READ != 0 };
        if blocked && v & PARKED != 0 {
            let ghost b0 = bids;
            let tracked brec = bids.insert(id, (self.lot(), tk, key)).persist();
            let me = Arc::new(Waiter {
                key,
                id,
                thread: Unparker::current(),
                notified,
                lot: Ghost(self.lot()),
                tk: Ghost(tk),
                rec: Tracked(rec.tracked_unwrap()),
                brec: Tracked(brec),
            });
            let w = arc_clone(&me);
            let ghost l0 = l;
            l.q.push(w);
            l.next = id + 1;
            proof {
                lemma_push(q0, key, self.lot(), half0, w);
                lemma_push_wf(l0, w);
                assert(bids@.dom() =~= b0@.dom().insert(id));
                lemma_bids_push(q0, id, b0, bids, w);
            }
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
            Some(me)
        } else {
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
            None
        }
    }

    /// The model's `Asleep`: the load of the waiter's flag. True if it is
    /// set, and the thread goes on to reload.
    #[inline]
    fn wait_flag(&self, me: &Arc<Waiter>, wr: bool, left: u8, Tracked(tok): Tracked<&mut Tok<P>>) -> (flag: bool)
        requires
            self.wf(),
            me.wf(),
            me.lot@ == self.lot(),
            tok_at(*old(tok), self.consts(), Ph::Asleep { wr, tk: me.tk@, left: left as nat }),
        ensures
            tok_at(*final(tok), self.consts(), if flag { Ph::Load { wr, left: left as nat } } else { Ph::Asleep { wr, tk: me.tk@, left: left as nat } }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost tk = me.tk@;
        let flag;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(tok);
                s.model.lemma_inv();
                let t = tok.key();
                assert(t < model_threads());
                assert(ph(s.model@, t) == (Ph::Asleep { wr, tk, left: left as nat }));
                assert(tk < s.model@.next_tk);
                s.recs.intersection_agrees_points_to(me.rec.borrow());
            }
            flag = me.notified.load(Tracked(s.flags.tracked_borrow(tk)));
            proof {
                if flag {
                    let m = s.model@;
                    let t = tok.key();
                    let s2 = go(m, t, Ph::Load { wr, left: left as nat });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            }
        });
        flag
    }

    /// Past the deadline: the bucket's critical section that takes the
    /// waiter off the list (`Some(false)`: the call gives up), unless a
    /// waker already has (`Some(true)`: the thread reloads). `None` only
    /// if the key changed, which it cannot: the thread just sleeps on.
    #[cold]
    fn timeout(&self, me: &Arc<Waiter>, wr: bool, left: u8, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: Option<bool>)
        requires
            self.wf(),
            me.wf(),
            me.lot@ == self.lot(),
            me.brec@.id() == bucket_loc(me.key),
            tok_at(*old(tok), self.consts(), Ph::Asleep { wr, tk: me.tk@, left: left as nat }),
            old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.consts(), match r {
                Some(true) => Ph::Load { wr, left: left as nat },
                Some(false) => Ph::Idle,
                None => Ph::Asleep { wr, tk: me.tk@, left: left as nat },
            }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost tk = me.tk@;
        let (key, Tracked(kf)) = self.key();
        if key != me.key {
            return None;
        }
        let (g, mut l, Tracked(half), Tracked(bids)) = lock_bucket(key, Tracked(&kf));
        let tracked mut half = half;
        let tracked bids = bids;
        let ghost q0 = l.q@;
        let ghost half0 = half@;
        let i = find_id(&l, me.id);
        if i < l.q.len() {
            let e = &l.q[i];
            proof {
                // The same id in the same bucket: the same waiter.
                e.brec.borrow().agree(&bids);
                me.brec.borrow().agree(&bids);
                assert(q0[i as int].tk@ == tk);
                assert(q0[i as int].key == key);
            }
            open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
                proof {
                    s.list.agree(&half);
                    s.model.agree(tok);
                    s.model.lemma_inv();
                    let m = s.model@;
                    let t = tok.key();
                    assert(t < model_threads());
                    assert(ph(m, t) == (Ph::Asleep { wr, tk, left: left as nat }));
                    assert(half0.contains_key(tk));
                    let s2 = St { list: m.list.remove(tk), ..go(m, t, Ph::Idle) };
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    s.list.update(&mut half, half0.remove(tk));
                    assert(s.list@.dom() =~= s2.list);
                }
            });
            let ghost l0 = l;
            let _ = l.q.remove(i);
            proof {
                lemma_remove(q0, key, self.lot(), half0, i as int);
                lemma_remove_wf(l0, l.q@, i as int);
                lemma_bids_remove(q0, l.next, bids, i as int);
            }
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
            Some(false)
        } else {
            open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
                proof {
                    s.list.agree(&half);
                    s.model.agree(tok);
                    s.model.lemma_inv();
                    let m = s.model@;
                    let t = tok.key();
                    assert(t < model_threads());
                    assert(ph(m, t) == (Ph::Asleep { wr, tk, left: left as nat }));
                    assert(tk < m.next_tk);
                    s.recs.intersection_agrees_points_to(me.rec.borrow());
                    // Not in the bucket, so not on the list.
                    if m.list.contains(tk) {
                        assert(half0.contains_key(tk));
                        let j = choose|j: int| 0 <= j < q0.len() && (#[trigger] q0[j]).key == key && q0[j].tk@ == tk;
                        assert(q0[j].id == half0[tk]);
                        assert(q0[j].id != me.id);
                    }
                    let s2 = go(m, t, Ph::Load { wr, left: left as nat });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
            });
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
            Some(true)
        }
    }

    /// The model's `Unpark` and `Notify`: `unpark_all`. Its bucket
    /// section takes every waiter under the key off the list, then it sets
    /// their flags and wakes their threads, one at a time. A reader that
    /// downgraded (`rd`) goes on holding its read lock.
    #[cold]
    fn unpark_all(&self, Ghost(rd): Ghost<bool>, Tracked(tok): Tracked<&mut Tok<P>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Unpark { rd }),
        ensures
            tok_at(*final(tok), self.consts(), if rd { Ph::RCrit } else { Ph::Idle }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let (key, Tracked(kf)) = self.key();
        let (g, mut l, Tracked(half), Tracked(bids)) = lock_bucket(key, Tracked(&kf));
        let tracked mut half = half;
        let tracked bids = bids;
        let ghost q0 = l.q@;
        let ghost half0 = half@;
        let ghost lot = self.lot();
        let ghost mut cur: Map<nat, u64> = half0;
        let mut woken: Vec<Arc<Waiter>> = Vec::new();
        loop
            invariant
                l.wf(),
                listed(l.q@, key, lot, cur),
                same_others(l.q@, q0, key),
                bids_ok(l.q@, l.next, bids),
                lot == self.lot(),
                forall|j: int| 0 <= j < woken@.len() ==> {
                    &&& (#[trigger] woken@[j]).wf()
                    &&& woken@[j].lot@ == lot
                    &&& half0.contains_key(woken@[j].tk@)
                    &&& !cur.contains_key(woken@[j].tk@)
                },
                forall|x: nat| #[trigger] half0.contains_key(x) ==> cur.contains_key(x) || exists|j: int| 0 <= j < woken@.len() && (#[trigger] woken@[j]).tk@ == x,
                forall|x: nat| #[trigger] cur.contains_key(x) ==> half0.contains_key(x),
            ensures
                forall|j: int| 0 <= j < l.q@.len() ==> (#[trigger] l.q@[j]).key != key,
            decreases l.q@.len(),
        {
            let i = find_key(&l, key);
            if i == l.q.len() {
                break;
            }
            let ghost l0 = l;
            let ghost cur0 = cur;
            let ghost woken0 = woken@;
            let w = l.q.remove(i);
            proof {
                lemma_remove(l0.q@, key, lot, cur0, i as int);
                lemma_remove_wf(l0, l.q@, i as int);
                lemma_bids_remove(l0.q@, l.next, bids, i as int);
                lemma_same_others_trans(l.q@, l0.q@, q0, key);
                cur = cur0.remove(w.tk@);
            }
            woken.push(w);
            proof {
                assert forall|x: nat| #[trigger] half0.contains_key(x) implies cur.contains_key(x) || exists|j: int| 0 <= j < woken@.len() && (#[trigger] woken@[j]).tk@ == x by {
                    if x == w.tk@ {
                        assert(woken@[woken0.len() as int] == w);
                    } else if !cur0.contains_key(x) {
                        let j = choose|j: int| 0 <= j < woken0.len() && (#[trigger] woken0[j]).tk@ == x;
                        assert(woken@[j] == woken0[j]);
                    }
                }
                assert forall|j: int| 0 <= j < woken@.len() implies {
                    &&& (#[trigger] woken@[j]).wf()
                    &&& woken@[j].lot@ == lot
                    &&& half0.contains_key(woken@[j].tk@)
                    &&& !cur.contains_key(woken@[j].tk@)
                } by {
                    if j < woken0.len() {
                        assert(woken@[j] == woken0[j]);
                    }
                }
            }
        }
        let ghost tks = woken@.map_values(|w: Arc<Waiter>| w.tk@);
        proof {
            // Nobody is left under the key, so nobody is left on the list.
            assert(cur =~= Map::empty()) by {
                assert forall|x: nat| !cur.contains_key(x) by {
                    if cur.contains_key(x) {
                        let j = choose|j: int| 0 <= j < l.q@.len() && (#[trigger] l.q@[j]).key == key && l.q@[j].tk@ == x;
                    }
                }
            }
            assert forall|x: nat| #[trigger] tks.contains(x) <==> half0.contains_key(x) by {
                if tks.contains(x) {
                    let j = choose|j: int| 0 <= j < tks.len() && tks[j] == x;
                    assert(woken@[j].tk@ == x);
                }
                if half0.contains_key(x) {
                    let j = choose|j: int| 0 <= j < woken@.len() && (#[trigger] woken@[j]).tk@ == x;
                    assert(tks[j] == x);
                }
            }
        }
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.list.agree(&half);
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                assert(lists(tks, m.list));
                let s2 = St { list: Set::empty(), ..go(m, t, Ph::Notify { rd, woken: tks }) };
                assert(step(m, t, s2));
                s.model.step(tok, s2);
                s.list.update(&mut half, Map::empty());
                assert(s.list@.dom() =~= s2.list);
            }
        });
        unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
        let n = woken.len();
        let mut j: usize = 0;
        assert(tks.subrange(0, n as int) =~= tks);
        while j < n
            invariant
                self.wf(),
                n == woken@.len(),
                j <= n,
                tks == woken@.map_values(|w: Arc<Waiter>| w.tk@),
                lot == self.lot(),
                forall|k: int| 0 <= k < woken@.len() ==> (#[trigger] woken@[k]).wf() && woken@[k].lot@ == lot,
                tok_at(*tok, self.consts(), Ph::Notify { rd, woken: tks.subrange(j as int, n as int) }),
                tok.value().timed == old(tok).value().timed,
            decreases n - j,
        {
            let w = &woken[j];
            let ghost tk = w.tk@;
            open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
                proof {
                    s.model.agree(tok);
                    s.model.lemma_inv();
                    let m = s.model@;
                    let t = tok.key();
                    assert(t < model_threads());
                    let rest = tks.subrange(j as int, n as int);
                    assert(ph(m, t) == (Ph::Notify { rd, woken: rest }));
                    assert(rest[0] == tk);
                    assert(rest.contains(tk));
                    assert(inv(m, model_threads()));
                    assert(match ph(m, t) {
                        Ph::Notify { woken, .. } => forall|x: nat| #[trigger] woken.contains(x) ==> x < m.next_tk && !m.list.contains(x),
                        _ => true,
                    });
                    let wk = ph(m, t)->Notify_woken;
                    assert(wk == rest);
                    assert(wk.contains(tk));
                    assert(tk < m.next_tk);
                    s.recs.intersection_agrees_points_to(w.rec.borrow());
                }
                let ghost flags0 = s.flags;
                let tracked mut fp = s.flags.tracked_remove(tk);
                w.notified.store(Tracked(&mut fp), true);
                proof {
                    s.flags.tracked_insert(tk, fp);
                    let m = s.model@;
                    let t = tok.key();
                    let rest = tks.subrange(j as int, n as int);
                    assert(rest.drop_first() =~= tks.subrange(j + 1, n as int));
                    let s2 = St { notified: m.notified.insert(tk), ..go(m, t, Ph::Notify { rd, woken: rest.drop_first() }) };
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    assert(s.flags.dom() =~= Set::range(0, s2.next_tk));
                    assert forall|x: nat| x < s2.next_tk implies {
                        &&& (#[trigger] s.flags[x]).id() == s.recs@[x].0
                        &&& s.flags[x].value() == s2.notified.contains(x)
                    } by {
                        if x != tk {
                            assert(s.flags[x] == flags0[x]);
                        }
                    }
                }
            });
            w.thread.unpark();
            j += 1;
        }
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                assert(tks.subrange(n as int, n as int).len() == 0);
                let s2 = go(m, t, if rd { Ph::RCrit } else { Ph::Idle });
                assert(step(m, t, s2));
                s.model.step(tok, s2);
            }
        });
    }

    fn read_guard(&self, Tracked(h): Tracked<Option<RwToks::reader<T>>>, Tracked(tok): Tracked<Tok<P>>) -> (g: RwLockReadGuard<'_, T>)
        requires
            self.wf(),
            self.reads(h),
            tok_at(tok, self.consts(), Ph::RCrit),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        RwLockReadGuard { lock: self, handle: Tracked(h), tok: Tracked(Some(tok)) }
    }

    fn write_guard(&self, Tracked(w): Tracked<Option<(PointsTo<T>, RwToks::writer<T>)>>, Tracked(tok): Tracked<Tok<P>>) -> (g: RwLockWriteGuard<'_, T>)
        requires
            self.wf(),
            self.writes(w),
            tok_at(tok, self.consts(), Ph::WCrit),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        let tracked (p, h) = w.tracked_unwrap();
        RwLockWriteGuard { lock: self, perm: Tracked(Some(p)), handle: Tracked(Some(h)), tok: Tracked(Some(tok)) }
    }

    /// Takes a shared lock if no writer holds or waits for the lock.
    #[inline]
    pub fn try_read(&self) -> (r: Option<RwLockReadGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        let Tracked(mut tok) = self.enter(Ghost(false), Ghost(true), Ghost(0));
        let s = self.load_at(Tracked(&mut tok), Ghost(false), Ghost(0), Ghost(true));
        proof {
            lemma_word_tests(s);
        }
        if s & BLOCKS_READ == 0 {
            if s > MAX_FOR_READ {
                // The reader count would overflow.
                exhausted();
            }
            let (ok, h) = self.cas_read(s, Tracked(&mut tok), Ghost(0), Ghost(true));
            if ok {
                return Some(self.read_guard(h, Tracked(tok)));
            }
        }
        self.leave(Tracked(tok));
        None
    }

    /// Takes the exclusive lock if the lock is free.
    #[inline]
    pub fn try_write(&self) -> (r: Option<RwLockWriteGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        proof {
            lemma_word_updates(0);
            lemma_zero();
        }
        let Tracked(mut tok) = self.enter(Ghost(true), Ghost(true), Ghost(0));
        let (ok, w) = self.cas_write(0, Tracked(&mut tok), Ghost(0), Ghost(false));
        if ok {
            return Some(self.write_guard(w, Tracked(tok)));
        }
        // Free but for a hint: look again.
        let s = self.load_at(Tracked(&mut tok), Ghost(true), Ghost(0), Ghost(true));
        proof {
            lemma_word_tests(s);
        }
        if s & WRITER == 0 && s >> 3 == 0 {
            let (ok, w) = self.cas_write(s, Tracked(&mut tok), Ghost(0), Ghost(true));
            if ok {
                return Some(self.write_guard(w, Tracked(tok)));
            }
        }
        self.leave(Tracked(tok));
        None
    }

    /// Takes a shared lock, sleeping while a writer holds or waits for it.
    #[inline]
    pub fn read(&self) -> (g: RwLockReadGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        let Tracked(mut tok) = self.enter(Ghost(false), Ghost(false), Ghost(SPINS as nat));
        let mut left = SPINS;
        let s = self.load_at(Tracked(&mut tok), Ghost(false), Ghost(SPINS as nat), Ghost(false));
        proof {
            lemma_word_tests(s);
        }
        if s & BLOCKS_READ == 0 {
            if s > MAX_FOR_READ {
                crate::util::exhausted();
            }
            let (ok, h) = self.cas_read(s, Tracked(&mut tok), Ghost(SPINS as nat), Ghost(false));
            if ok {
                return self.read_guard(h, Tracked(tok));
            }
        } else if !self.wait(s, false, &mut left, &Backoff::new(), &no_deadline(), Tracked(&mut tok)) {
            vstd::pervasive::unreached::<()>();
        }
        // Without a deadline read_slow only returns with the lock.
        match self.read_slow(no_deadline(), Tracked(tok), left) {
            Some(g) => g,
            None => vstd::pervasive::unreached(),
        }
    }

    /// Takes the exclusive lock, sleeping while others hold it.
    #[inline]
    pub fn write(&self) -> (g: RwLockWriteGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        proof {
            lemma_word_updates(0);
            lemma_zero();
        }
        let Tracked(mut tok) = self.enter(Ghost(true), Ghost(false), Ghost(SPINS as nat));
        let (ok, w) = self.cas_write(0, Tracked(&mut tok), Ghost(SPINS as nat), Ghost(false));
        if ok {
            return self.write_guard(w, Tracked(tok));
        }
        // Without a deadline write_slow only returns with the lock.
        match self.write_slow(no_deadline(), Tracked(tok), SPINS) {
            Some(g) => g,
            None => vstd::pervasive::unreached(),
        }
    }

    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn read_slow(&self, deadline: Deadline, Tracked(tok0): Tracked<Tok<P>>, left0: u8) -> (r: Option<RwLockReadGuard<'_, T>>)
        requires
            self.wf(),
            tok_at(tok0, self.consts(), Ph::Load { wr: false, left: left0 as nat }),
            has_deadline(deadline) ==> tok0.value().timed,
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
            r is None ==> tok0.value().timed,
    {
        let ghost timed = tok0.value().timed;
        let tracked mut tok = tok0;
        let backoff = Backoff::new();
        let mut left = left0;
        loop
            invariant
                self.wf(),
                tok_at(tok, self.consts(), Ph::Load { wr: false, left: left as nat }),
                tok.value().timed == timed,
                timed == tok0.value().timed,
                has_deadline(deadline) ==> timed,
        {
            let s = self.load_at(Tracked(&mut tok), Ghost(false), Ghost(left as nat), Ghost(false));
            proof {
                lemma_word_tests(s);
            }
            if s & BLOCKS_READ == 0 {
                if s > MAX_FOR_READ {
                    crate::util::exhausted();
                }
                let (ok, h) = self.cas_read(s, Tracked(&mut tok), Ghost(left as nat), Ghost(false));
                if ok {
                    return Some(self.read_guard(h, Tracked(tok)));
                }
                backoff.spin();
            } else if !self.wait(s, false, &mut left, &backoff, &deadline, Tracked(&mut tok)) {
                self.leave(Tracked(tok));
                return None;
            }
        }
    }

    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn write_slow(&self, deadline: Deadline, Tracked(tok0): Tracked<Tok<P>>, left0: u8) -> (r: Option<RwLockWriteGuard<'_, T>>)
        requires
            self.wf(),
            tok_at(tok0, self.consts(), Ph::Load { wr: true, left: left0 as nat }),
            has_deadline(deadline) ==> tok0.value().timed,
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
            r is None ==> tok0.value().timed,
    {
        let ghost timed = tok0.value().timed;
        let tracked mut tok = tok0;
        let backoff = Backoff::new();
        let mut left = left0;
        loop
            invariant
                self.wf(),
                tok_at(tok, self.consts(), Ph::Load { wr: true, left: left as nat }),
                tok.value().timed == timed,
                timed == tok0.value().timed,
                has_deadline(deadline) ==> timed,
        {
            let s = self.load_at(Tracked(&mut tok), Ghost(true), Ghost(left as nat), Ghost(false));
            proof {
                lemma_word_tests(s);
            }
            if s & WRITER == 0 && s >> 3 == 0 {
                let (ok, w) = self.cas_write(s, Tracked(&mut tok), Ghost(left as nat), Ghost(false));
                if ok {
                    return Some(self.write_guard(w, Tracked(tok)));
                }
                backoff.spin();
            } else if !self.wait(s, true, &mut left, &backoff, &deadline, Tracked(&mut tok)) {
                self.leave(Tracked(tok));
                return None;
            }
        }
    }

    fn try_read_until_deadline(&self, deadline: Deadline) -> (r: Option<RwLockReadGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        let Tracked(tok) = self.enter(Ghost(false), Ghost(true), Ghost(SPINS as nat));
        self.read_slow(deadline, Tracked(tok), SPINS)
    }

    fn try_write_until_deadline(&self, deadline: Deadline) -> (r: Option<RwLockWriteGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        proof {
            lemma_word_updates(0);
            lemma_zero();
        }
        let Tracked(mut tok) = self.enter(Ghost(true), Ghost(true), Ghost(SPINS as nat));
        let (ok, w) = self.cas_write(0, Tracked(&mut tok), Ghost(SPINS as nat), Ghost(false));
        if ok {
            return Some(self.write_guard(w, Tracked(tok)));
        }
        self.write_slow(deadline, Tracked(tok), SPINS)
    }

    /// `fetch_sub(ONE_READER)`, the model's `RCrit`; the last reader out
    /// with a hint set clears the hints (`Clear`) and wakes everyone.
    fn unlock_read(&self, Tracked(h): Tracked<RwToks::reader<T>>, Tracked(tok): Tracked<Tok<P>>)
        requires
            self.wf(),
            self.reads(Some(h)),
            tok_at(tok, self.consts(), Ph::RCrit),
    {
        let tracked mut tok = tok;
        let old;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().reader_counted(h.element(), &s.rc, &h);
                lemma_sub_reader(s.state@.value);
                lemma_word_updates(s.state@.value);
                lemma_word_tests(s.state@.value);
            }
            old = self.state.fetch_sub(Tracked(&mut s.state), ONE_READER);
            proof {
                self.inst.borrow().release_read(h.element(), &mut s.rc, h);
                s.model.agree(&tok);
                let m = s.model@;
                let t = tok.key();
                let x = m.word;
                let s2 = gow(m, t, if x.rc == 1 && (x.pk || x.ww) { Ph::Clear } else { Ph::Idle }, Word { rc: (x.rc - 1) as nat, ..x });
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
            }
        });
        proof {
            lemma_word_tests(old);
        }
        if old >> 3 == 1 && old & FLAGS != 0 {
            self.clear_flags(Tracked(&mut tok));
            self.unpark_all(Ghost(false), Tracked(&mut tok));
        }
        self.leave(Tracked(tok));
    }

    /// Clears both hints, the model's `Clear`.
    #[inline(always)]
    fn clear_flags(&self, Tracked(tok): Tracked<&mut Tok<P>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Clear),
        ensures
            tok_at(*final(tok), self.consts(), Ph::Unpark { rd: false }),
            final(tok).value().timed == old(tok).value().timed,
    {
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                lemma_flag_bits(s.state@.value, 6);
                lemma_word_updates(s.state@.value);
            }
            let _ = self.state.fetch_and(Tracked(&mut s.state), NOT_FLAGS);
            proof {
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = gow(m, t, Ph::Unpark { rd: false }, Word { pk: false, ww: false, ..m.word });
                assert(step(m, t, s2));
                s.model.step(tok, s2);
            }
        });
    }

    /// `swap(0)`, the model's `WCrit` for an unlock; wakes everyone if a
    /// hint was set.
    fn unlock_write(&self, Tracked(p): Tracked<PointsTo<T>>, Tracked(h): Tracked<RwToks::writer<T>>, Tracked(tok): Tracked<Tok<P>>)
        requires
            self.wf(),
            self.writes(Some((p, h))),
            tok_at(tok, self.consts(), Ph::WCrit),
    {
        let tracked mut tok = tok;
        let old;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().writer_alone(&s.exc, &s.rc, &h);
                lemma_zero();
                lemma_word_updates(s.state@.value);
                lemma_word_tests(s.state@.value);
            }
            old = self.state.swap(Tracked(&mut s.state), 0);
            proof {
                self.inst.borrow().release_write(p, &mut s.exc, p, h);
                s.model.agree(&tok);
                let m = s.model@;
                let t = tok.key();
                let x = m.word;
                let s2 = gow(m, t, if x.pk || x.ww { Ph::Unpark { rd: false } } else { Ph::Idle }, zero());
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
            }
        });
        proof {
            lemma_word_tests(old);
        }
        if old & FLAGS != 0 {
            self.unpark_all(Ghost(false), Tracked(&mut tok));
        }
        self.leave(Tracked(tok));
    }

    /// Turns a write lock into a read lock without letting a writer in:
    /// `fetch_add(ONE_READER - WRITER)`, the model's `WCrit` for a
    /// downgrade, then waking everyone if the parked hint is set.
    fn downgrade_lock(&self, Tracked(p): Tracked<PointsTo<T>>, Tracked(h): Tracked<RwToks::writer<T>>, Tracked(tok): Tracked<Tok<P>>) -> (r: (Tracked<Option<RwToks::reader<T>>>, Tracked<Tok<P>>))
        requires
            self.wf(),
            self.writes(Some((p, h))),
            tok_at(tok, self.consts(), Ph::WCrit),
        ensures
            self.reads(r.0@),
            tok_at(r.1@, self.consts(), Ph::RCrit),
    {
        let tracked mut tok = tok;
        let old;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().writer_alone(&s.exc, &s.rc, &h);
                lemma_downgrade(s.state@.value);
                lemma_word_updates(s.state@.value);
                lemma_word_tests(s.state@.value);
            }
            old = self.state.fetch_add(Tracked(&mut s.state), ONE_READER - WRITER);
            proof {
                let tracked r = self.inst.borrow().downgrade(p, &mut s.exc, &mut s.rc, p, h);
                got = Some(r);
                s.model.agree(&tok);
                s.model.lemma_inv();
                let m = s.model@;
                let t = tok.key();
                let x = m.word;
                let s2 = gow(m, t, if x.pk { Ph::Unpark { rd: true } } else { Ph::RCrit }, Word { w: false, rc: x.rc + 1, ..x });
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
            }
        });
        proof {
            lemma_word_tests(old);
        }
        if old & PARKED != 0 {
            self.unpark_all(Ghost(true), Tracked(&mut tok));
        }
        (Tracked(got), Tracked(tok))
    }

    /// Takes the value out if the lock is free. `&mut self` means no guard
    /// exists, unless one was leaked with `mem::forget`. The lock is not
    /// usable afterwards: only `drop` and `into_inner` call this.
    fn take_inner(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
    {
        let tracked inv = self.inv.borrow_mut().tracked_take();
        let tracked mut s = inv.into_inner();
        let st = self.state.load(Tracked(&s.state));
        if st & WRITER == 0 && st >> 3 == 0 {
            proof {
                lemma_zero();
                lemma_set_writer(st);
            }
            let tracked (_, Tracked(mut p), Tracked(_h)) = self.inst.borrow().acquire_write(&mut s.exc, &s.rc);
            let v = self.data.take(Tracked(&mut p));
            Some(v)
        } else {
            None
        }
    }

    /// Consumes the lock, returning the value.
    ///
    /// # Panics
    ///
    /// If a guard was leaked with `mem::forget`, since the value went with it.
    pub fn into_inner(mut self) -> T
        requires
            self.wf(),
    {
        match self.take_inner() {
            Some(v) => v,
            None => crate::util::leaked_guard(),
        }
    }

    /// Whether a writer holds the lock right now.
    pub fn is_locked_exclusive(&self) -> bool
        requires
            self.wf(),
    {
        self.load() & WRITER != 0
    }

    /// Whether anyone holds the lock right now.
    pub fn is_locked(&self) -> bool
        requires
            self.wf(),
    {
        let s = self.load();
        s & WRITER != 0 || s >> 3 != 0
    }
}

impl<'a, T> RwLockReadGuard<'a, T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.reads(self.handle@)
        &&& self.tok@ matches Some(t) && tok_at(t, self.lock.consts(), Ph::RCrit)
    }

    pub closed spec fn rwlock(&self) -> &'a RwLock<T> {
        self.lock
    }

    /// The data, shared.
    pub fn get(&self) -> &T
        requires
            self.wf(),
    {
        let tracked h = self.handle.borrow().tracked_borrow();
        let tracked p = self.lock.inst.borrow().read_guard(h.element(), h);
        self.lock.data.borrow(Tracked(p))
    }

    fn release(&mut self)
        requires
            old(self).wf(),
    {
        let tracked h = self.handle.borrow_mut().tracked_take();
        let tracked tok = self.tok.borrow_mut().tracked_take();
        self.lock.unlock_read(Tracked(h), Tracked(tok));
    }
}

impl<'a, T> RwLockWriteGuard<'a, T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@ is Some
        &&& self.handle@ is Some
        &&& self.lock.writes(Some((self.perm@->0, self.handle@->0)))
        &&& self.tok@ matches Some(t) && tok_at(t, self.lock.consts(), Ph::WCrit)
    }

    pub closed spec fn rwlock(&self) -> &'a RwLock<T> {
        self.lock
    }

    /// The data.
    pub fn get(&self) -> &T
        requires
            self.wf(),
    {
        self.lock.data.borrow(Tracked(self.perm.borrow().tracked_borrow()))
    }

    /// The data, mutably.
    pub fn get_mut(&mut self) -> &mut T
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        self.lock.data.borrow_mut(Tracked(crate::util::tracked_borrow_mut(self.perm.borrow_mut())))
    }

    fn release(&mut self)
        requires
            old(self).wf(),
    {
        let tracked p = self.perm.borrow_mut().tracked_take();
        let tracked h = self.handle.borrow_mut().tracked_take();
        let tracked tok = self.tok.borrow_mut().tracked_take();
        self.lock.unlock_write(Tracked(p), Tracked(h), Tracked(tok));
    }

    fn downgrade_inner(&mut self) -> (g: RwLockReadGuard<'a, T>)
        requires
            old(self).wf(),
        ensures
            g.wf(),
            final(self).perm@ is None,
            final(self).handle@ is None,
    {
        let tracked p = self.perm.borrow_mut().tracked_take();
        let tracked h = self.handle.borrow_mut().tracked_take();
        let tracked tok = self.tok.borrow_mut().tracked_take();
        let (r, Tracked(tok)) = self.lock.downgrade_lock(Tracked(p), Tracked(h), Tracked(tok));
        RwLockReadGuard { lock: self.lock, handle: r, tok: Tracked(Some(tok)) }
    }
}

} // verus!

impl<'a, T> Drop for RwLockReadGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.release();
    }
}

impl<'a, T> Drop for RwLockWriteGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.release();
    }
}

impl<'a, T> RwLockWriteGuard<'a, T> {
    /// Turns the write lock into a read lock, with no writer getting in
    /// between.
    pub fn downgrade(mut s: Self) -> RwLockReadGuard<'a, T> {
        let r = s.downgrade_inner();
        // The lock now belongs to `r`; `s` has nothing left to release.
        std::mem::forget(s);
        r
    }
}

impl<T> Drop for RwLock<T> {
    fn drop(&mut self) {
        let _ = self.take_inner();
    }
}

impl<'a, T> std::ops::Deref for RwLockReadGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.get()
    }
}

impl<'a, T> std::ops::Deref for RwLockWriteGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.get()
    }
}

impl<'a, T> std::ops::DerefMut for RwLockWriteGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.get_mut()
    }
}

// SAFETY: the proof shows writers get the data alone and readers only
// shared, so sharing the lock between threads needs `T: Send + Sync`, as
// for std's RwLock.
unsafe impl<T: Send> Send for RwLock<T> {}
unsafe impl<T: Send + Sync> Sync for RwLock<T> {}
unsafe impl<'a, T: Sync> Sync for RwLockReadGuard<'a, T> {}
unsafe impl<'a, T: Sync> Sync for RwLockWriteGuard<'a, T> {}

impl<T> RwLock<T> {
    /// Takes a shared lock, sleeping until `deadline` at the latest.
    pub fn try_read_until(&self, deadline: std::time::Instant) -> Option<RwLockReadGuard<'_, T>> {
        self.try_read_until_deadline(Deadline(Some(deadline)))
    }

    /// Takes a shared lock, sleeping for at most `timeout`.
    pub fn try_read_for(&self, timeout: std::time::Duration) -> Option<RwLockReadGuard<'_, T>> {
        self.try_read_until(std::time::Instant::now() + timeout)
    }

    /// Takes the exclusive lock, sleeping until `deadline` at the latest.
    pub fn try_write_until(&self, deadline: std::time::Instant) -> Option<RwLockWriteGuard<'_, T>> {
        self.try_write_until_deadline(Deadline(Some(deadline)))
    }

    /// Takes the exclusive lock, sleeping for at most `timeout`.
    pub fn try_write_for(&self, timeout: std::time::Duration) -> Option<RwLockWriteGuard<'_, T>> {
        self.try_write_until(std::time::Instant::now() + timeout)
    }
}

impl<T: Default> Default for RwLock<T> {
    fn default() -> Self {
        RwLock::new(T::default())
    }
}

impl<T> From<T> for RwLock<T> {
    fn from(v: T) -> Self {
        RwLock::new(v)
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for RwLock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.try_read() {
            Some(g) => f.debug_struct("RwLock").field("data", &&*g).finish(),
            None => f.debug_struct("RwLock").field("data", &format_args!("<locked>")).finish(),
        }
    }
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for RwLockReadGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for RwLockWriteGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}
