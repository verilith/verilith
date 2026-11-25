//! A verified reader-writer lock with parking_lot's `RwLock` API.
//!
//! One 32-bit word holds the whole lock: bit 0 is the writer, bit 1 says
//! threads may be parked, bit 2 says a writer is waiting (which holds off
//! new readers, so writers do not starve), and the rest counts readers.
//! What is proved: a write guard excludes every other guard, read guards
//! only ever see the data shared, and the data is dropped exactly once. The
//! proof does not depend on the parking code, nor on bits 1 and 2.
#![allow(non_snake_case, non_shorthand_field_patterns, unused_imports)]
use crate::util::{Backoff, Deadline};
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::multiset::*;
use vstd::prelude::*;
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

/// The lock's constants: the ids of its atomic and of its token instance.
pub ghost struct RwConsts {
    /// The id of the state atomic.
    pub state: int,
    /// The id of the `RwToks` instance.
    pub inst: vstd::resource::Loc,
}

/// What the lock's invariant owns.
pub tracked struct RwShared<T> {
    /// The state atomic's permission.
    pub state: PermissionU32,
    /// The token saying whether a writer holds the lock.
    pub exc: RwToks::exc<T>,
    /// The token counting readers.
    pub rc: RwToks::rc<T>,
}

/// The lock's invariant (see its `inv`).
pub struct RwPred;

impl<T> InvariantPredicate<RwConsts, RwShared<T>> for RwPred {
    open spec fn inv(c: RwConsts, s: RwShared<T>) -> bool {
        &&& s.state@.patomic == c.state
        &&& s.exc.instance_id() == c.inst
        &&& s.rc.instance_id() == c.inst
        &&& s.exc.value() == has_writer(s.state@.value)
        &&& s.rc.value() == readers(s.state@.value)
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
}

/// Proof that the holder alone has the data.
pub struct RwLockWriteGuard<'a, T> {
    lock: &'a RwLock<T>,
    /// `Some` until the guard is dropped or downgraded.
    perm: Tracked<Option<PointsTo<T>>>,
    handle: Tracked<Option<RwToks::writer<T>>>,
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
        }
        let ghost c = RwConsts { state: state.id(), inst: inst.id() };
        let tracked s = RwShared { state: sp, exc, rc };
        let tracked inv = AtomicInvariant::<_, _, RwPred>::new(c, s, 0x7277);
        RwLock { state, data, inst: Tracked(inst), inv: Tracked(Some(inv)) }
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

    /// Adds a reader if the word still holds `cur`, which has no writer.
    #[inline(always)]
    fn cas_read(&self, cur: u32) -> (r: (bool, Tracked<Option<RwToks::reader<T>>>))
        requires
            self.wf(),
            cur & 1 == 0,
            cur <= MAX_FOR_READ,
        ensures
            r.0 ==> self.reads(r.1@),
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur + ONE_READER) {
                Ok(_) => true,
                Err(_) => false,
            };
            if ok {
                proof {
                    lemma_add_reader(cur);
                    let tracked (_, Tracked(h)) = self.inst.borrow().acquire_read(&s.exc, &mut s.rc);
                    got = Some(h);
                }
            }
        });
        (ok, Tracked(got))
    }

    /// Sets the writer bit if the word still holds `cur`, which is unlocked.
    #[inline(always)]
    fn cas_write(&self, cur: u32) -> (r: (bool, Tracked<Option<(PointsTo<T>, RwToks::writer<T>)>>))
        requires
            self.wf(),
            cur & 1 == 0,
            cur >> 3 == 0,
        ensures
            r.0 ==> self.writes(r.1@),
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur | WRITER) {
                Ok(_) => true,
                Err(_) => false,
            };
            if ok {
                proof {
                    lemma_set_writer(cur);
                    let tracked (_, Tracked(p), Tracked(h)) = self.inst.borrow().acquire_write(&mut s.exc, &s.rc);
                    got = Some((p, h));
                }
            }
        });
        (ok, Tracked(got))
    }

    /// Sets flag bits (`PARKED`, or that and `WRITER_WAITING`) if the word
    /// still holds `cur`.
    #[inline(always)]
    fn cas_flags(&self, cur: u32, bits: u32) -> bool
        requires
            self.wf(),
            bits == PARKED || bits == FLAGS,
    {
        let ok;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                lemma_flag_bits(cur, bits);
            }
            ok = match self.state.compare_exchange(Tracked(&mut s.state), cur, cur | bits) {
                Ok(_) => true,
                Err(_) => false,
            };
        });
        ok
    }

    /// Clears both flag bits.
    #[inline(always)]
    fn clear_flags(&self)
        requires
            self.wf(),
    {
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                lemma_flag_bits(s.state@.value, 6);
            }
            let _ = self.state.fetch_and(Tracked(&mut s.state), NOT_FLAGS);
        });
    }

    #[verifier::external_body]
    fn unpark_all(&self) {
        crate::parking::unpark(self.key(), usize::MAX);
    }

    /// The parking-lot key: the address of the lock word (see
    /// `Mutex::key` for why not the lock's own address).
    #[verifier::external_body]
    fn key(&self) -> usize {
        &self.state as *const PAtomicU32 as usize
    }

    /// Sleeps while `blocked(state)` holds and the parked bit is set.
    /// Returns false at the deadline.
    #[verifier::external_body]
    fn park(&self, deadline: Deadline, for_write: bool) -> bool {
        let ok = crate::parking::park(self.key(), || {
            let s = self.state_now();
            let blocked = if for_write { s & WRITER != 0 || s >> 3 != 0 } else { s & BLOCKS_READ != 0 };
            blocked && s & PARKED != 0
        }, deadline.0);
        ok || deadline.0.map_or(true, |d| std::time::Instant::now() < d)
    }

    /// The lock word right now, for the parking lot's re-check.
    pub fn state_now(&self) -> u32
        requires
            self.wf(),
    {
        self.load()
    }

    fn read_guard(&self, Tracked(h): Tracked<Option<RwToks::reader<T>>>) -> (g: RwLockReadGuard<'_, T>)
        requires
            self.wf(),
            self.reads(h),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        RwLockReadGuard { lock: self, handle: Tracked(h) }
    }

    fn write_guard(&self, Tracked(w): Tracked<Option<(PointsTo<T>, RwToks::writer<T>)>>) -> (g: RwLockWriteGuard<'_, T>)
        requires
            self.wf(),
            self.writes(w),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        let tracked (p, h) = w.tracked_unwrap();
        RwLockWriteGuard { lock: self, perm: Tracked(Some(p)), handle: Tracked(Some(h)) }
    }

    /// Takes a shared lock if no writer holds or waits for the lock.
    #[inline]
    pub fn try_read(&self) -> (r: Option<RwLockReadGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        let s = self.load();
        proof {
            lemma_flag_bits(s, 2);
        }
        if s & BLOCKS_READ == 0 && s <= MAX_FOR_READ {
            let (ok, h) = self.cas_read(s);
            if ok {
                return Some(self.read_guard(h));
            }
        }
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
        let s = self.load();
        if s & WRITER == 0 && s >> 3 == 0 {
            let (ok, w) = self.cas_write(s);
            if ok {
                return Some(self.write_guard(w));
            }
        }
        None
    }

    /// Takes a shared lock, sleeping while a writer holds or waits for it.
    #[inline]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn read(&self) -> (g: RwLockReadGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        if let Some(g) = self.try_read() {
            return g;
        }
        loop
            invariant
                self.wf(),
        {
            if let Some(g) = self.read_slow(crate::util::no_deadline()) {
                return g;
            }
        }
    }

    /// Takes the exclusive lock, sleeping while others hold it.
    #[inline]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn write(&self) -> (g: RwLockWriteGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.rwlock() == self,
    {
        proof {
            lemma_zero();
        }
        let (ok, w) = self.cas_write(0);
        if ok {
            return self.write_guard(w);
        }
        loop
            invariant
                self.wf(),
        {
            if let Some(g) = self.write_slow(crate::util::no_deadline()) {
                return g;
            }
        }
    }

    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn read_slow(&self, deadline: Deadline) -> (r: Option<RwLockReadGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        let backoff = Backoff::new();
        loop
            invariant
                self.wf(),
        {
            let s = self.load();
            proof {
                lemma_flag_bits(s, 2);
            }
            if s & BLOCKS_READ == 0 {
                if s > MAX_FOR_READ {
                    crate::util::exhausted();
                }
                let (ok, h) = self.cas_read(s);
                if ok {
                    return Some(self.read_guard(h));
                }
                backoff.spin();
            } else if s & PARKED == 0 && !backoff.is_completed() {
                backoff.snooze();
            } else if s & PARKED == 0 {
                let _ = self.cas_flags(s, PARKED);
            } else if !self.park(deadline, false) {
                return None;
            }
        }
    }

    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn write_slow(&self, deadline: Deadline) -> (r: Option<RwLockWriteGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        let backoff = Backoff::new();
        loop
            invariant
                self.wf(),
        {
            let s = self.load();
            if s & WRITER == 0 && s >> 3 == 0 {
                let (ok, w) = self.cas_write(s);
                if ok {
                    return Some(self.write_guard(w));
                }
                backoff.spin();
            } else if s & PARKED == 0 && !backoff.is_completed() {
                backoff.snooze();
            } else if s & FLAGS != FLAGS {
                let _ = self.cas_flags(s, FLAGS);
            } else if !self.park(deadline, true) {
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
        if let Some(g) = self.try_read() {
            return Some(g);
        }
        self.read_slow(deadline)
    }

    fn try_write_until_deadline(&self, deadline: Deadline) -> (r: Option<RwLockWriteGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.rwlock() == self,
    {
        if let Some(g) = self.try_write() {
            return Some(g);
        }
        self.write_slow(deadline)
    }

    fn unlock_read(&self, Tracked(h): Tracked<RwToks::reader<T>>)
        requires
            self.wf(),
            self.reads(Some(h)),
    {
        let old;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().reader_counted(h.element(), &s.rc, &h);
                lemma_sub_reader(s.state@.value);
            }
            old = self.state.fetch_sub(Tracked(&mut s.state), ONE_READER);
            proof {
                self.inst.borrow().release_read(h.element(), &mut s.rc, h);
            }
        });
        if old >> 3 == 1 && old & FLAGS != 0 {
            self.clear_flags();
            self.unpark_all();
        }
    }

    fn unlock_write(&self, Tracked(p): Tracked<PointsTo<T>>, Tracked(h): Tracked<RwToks::writer<T>>)
        requires
            self.wf(),
            self.writes(Some((p, h))),
    {
        let old;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().writer_alone(&s.exc, &s.rc, &h);
                lemma_zero();
            }
            old = self.state.swap(Tracked(&mut s.state), 0);
            proof {
                self.inst.borrow().release_write(p, &mut s.exc, p, h);
            }
        });
        if old & FLAGS != 0 {
            self.unpark_all();
        }
    }

    /// Turns a write lock into a read lock without letting a writer in.
    fn downgrade_lock(&self, Tracked(p): Tracked<PointsTo<T>>, Tracked(h): Tracked<RwToks::writer<T>>) -> (r: Tracked<Option<RwToks::reader<T>>>)
        requires
            self.wf(),
            self.writes(Some((p, h))),
        ensures
            self.reads(r@),
    {
        let old;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                self.inst.borrow().writer_alone(&s.exc, &s.rc, &h);
                lemma_downgrade(s.state@.value);
            }
            old = self.state.fetch_add(Tracked(&mut s.state), ONE_READER - WRITER);
            proof {
                let tracked r = self.inst.borrow().downgrade(p, &mut s.exc, &mut s.rc, p, h);
                got = Some(r);
            }
        });
        if old & PARKED != 0 {
            self.unpark_all();
        }
        Tracked(got)
    }

    /// Takes the value out if the lock is free, leaving it write-locked and
    /// empty for good. `&mut self` means no guard exists, unless one was
    /// leaked with `mem::forget`.
    fn take_inner(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let tracked inv = self.inv.borrow_mut().tracked_take();
        let ghost c = inv.constant();
        let tracked mut s = inv.into_inner();
        let st = self.state.load(Tracked(&s.state));
        let r = if st & WRITER == 0 && st >> 3 == 0 {
            proof {
                lemma_zero();
                lemma_set_writer(st);
            }
            let tracked (_, Tracked(mut p), Tracked(_h)) = self.inst.borrow().acquire_write(&mut s.exc, &s.rc);
            let v = self.data.take(Tracked(&mut p));
            self.state.store(Tracked(&mut s.state), st | WRITER);
            Some(v)
        } else {
            None
        };
        let tracked inv = AtomicInvariant::<_, _, RwPred>::new(c, s, 0x7277);
        self.inv = Tracked(Some(inv));
        r
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
        self.lock.unlock_read(Tracked(h));
    }
}

impl<'a, T> RwLockWriteGuard<'a, T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@ is Some
        &&& self.handle@ is Some
        &&& self.lock.writes(Some((self.perm@->0, self.handle@->0)))
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
        self.lock.unlock_write(Tracked(p), Tracked(h));
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
        let r = self.lock.downgrade_lock(Tracked(p), Tracked(h));
        RwLockReadGuard { lock: self.lock, handle: r }
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
