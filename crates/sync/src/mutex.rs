//! A verified mutual exclusion lock with parking_lot's `Mutex` API.
//!
//! The lock word is Drepper's three-state futex mutex ("Futexes Are
//! Tricky", mutex 3): 0 unlocked, 1 locked, 2 locked and possibly with
//! sleepers. What is proved: the guard is the only way to reach the data,
//! at most one guard exists at a time, and the data is dropped exactly once.
//!
//! And the code follows the progress model of `progress::mutex`, so its
//! deadlock-freedom theorem is about this code: the invariant holds a
//! [`Model`] of the protocol that only a proven step can change, every
//! access to the lock word, to a waiter's flag and to the parking lot's
//! list is made with it open, and each has to come with the model step it
//! is (see `TRUST.md`, "The mutex and the RwLock"). The model's steps,
//! one per access:
//!
//! | Code | Model |
//! | --- | --- |
//! | `cas_lock` in `lock`, `try_lock*` | `Fast` |
//! | `load_spin`, then `cas_lock`, in `lock_slow`'s spin loop | `Spin`, `SpinCas` |
//! | `swap_contended` | `Swap` |
//! | `check`: the bucket's critical section that re-checks the word and lists the thread | `Check` |
//! | `wait_flag`: the load of the waiter's flag | `Asleep` |
//! | `timeout`: the bucket's critical section that takes a late waiter off | `Asleep`, timing out |
//! | `unlock`'s swap to 0 | `Crit` |
//! | `unpark_one`: the bucket's critical section, and the store to the woken waiter's flag inside it | `Unpark`, `Notify` |
use crate::lot::*;
use crate::model::*;
use crate::progress::mutex::{P, Ph, St, Th};
#[cfg(verus_only)]
use crate::progress::mutex::{go, ph, step};
use crate::util::*;
use std::sync::Arc;
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::resource::Loc;

verus! {

broadcast use {vstd::set_lib::range_set_properties};

/// The number of threads in each mutex's model: any number (see
/// `model::Model::pool_nonempty`).
pub uninterp spec fn model_threads() -> nat;

/// How many times `lock_slow` snoozes before it marks the lock contended:
/// what `Backoff::is_completed` allows.
pub const SPINS: u8 = 11;

/// The mutex's constants: the ids of its atomic, its cell and its ghost
/// state.
pub struct MutexConsts {
    /// The id of the state atomic.
    pub state: int,
    /// The id of the data's cell.
    pub data: CellId,
    /// The location of the `locked` ghost variable.
    pub token: Loc,
    /// The progress model's.
    pub model: Loc,
    /// The waiter list's (`lot`'s `list`).
    pub list: Loc,
    /// The waiters' records'.
    pub recs: Loc,
}

/// Everything the lock owns while unlocked, the bookkeeping that tells a
/// releasing thread the lock is held, and the progress model.
pub tracked struct MutexShared<T> {
    /// The state atomic's permission.
    pub state: PermissionU32,
    /// True exactly while the lock is held.
    pub locked: GhostVarAuth<bool>,
    /// The data and the other half of `locked`, while unlocked; a guard
    /// holds them while locked.
    pub held: Option<(PointsTo<T>, GhostVar<bool>)>,
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

/// The mutex's invariant (see its `inv`).
pub struct MutexPred;

impl<T> InvariantPredicate<MutexConsts, MutexShared<T>> for MutexPred {
    open spec fn inv(c: MutexConsts, s: MutexShared<T>) -> bool {
        let m = s.model@;
        &&& s.state@.patomic == c.state
        &&& s.locked.id() == c.token
        &&& s.locked@ == (s.state@.value != 0)
        &&& (s.state@.value == 0) == (s.held is Some)
        &&& s.held matches Some((p, g)) ==> {
            &&& p.id() == c.data
            &&& p.is_init()
            &&& g.id() == c.token
        }
        &&& s.model.wf()
        &&& s.model.loc() == c.model
        &&& s.model.n() == model_threads()
        &&& m.word == s.state@.value as nat
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
        // A waker sets the flag in the same step that takes the waiter
        // off the list, so no model thread is ever between the two.
        &&& forall|t: nat| t < model_threads() ==> !(#[trigger] ph(m, t) is Notify)
    }
}

/// A mutual-exclusion lock, with parking_lot's `Mutex` API.
pub struct Mutex<T> {
    state: PAtomicU32,
    data: PCell<T>,
    /// `None` only while the mutex is being dropped.
    inv: Tracked<Option<AtomicInvariant<MutexConsts, MutexShared<T>, MutexPred>>>,
}

/// Proof that the lock is held, with the data it protects.
pub struct MutexGuard<'a, T> {
    lock: &'a Mutex<T>,
    /// `Some` until the guard is dropped.
    perm: Tracked<Option<PointsTo<T>>>,
    token: Tracked<Option<GhostVar<bool>>>,
    /// The model thread of the call that took the lock, holding it.
    tok: Tracked<Option<Tok<P>>>,
}

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const CONTENDED: u32 = 2;

/// The token is for a thread of the mutex's model, in phase `p`.
pub open spec fn tok_at(tok: Tok<P>, c: MutexConsts, p: Ph) -> bool {
    tok.id() == c.model && tok.value().ph == p
}

impl<T> Mutex<T> {
    pub closed spec fn consts(&self) -> MutexConsts {
        self.inv@->0.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.inv@ is Some
        &&& self.consts().state == self.state.id()
        &&& self.consts().data == self.data.id()
    }

    /// What the parking lot knows of this mutex.
    pub closed spec fn lot(&self) -> LotId {
        LotId { list: self.consts().list, recs: self.consts().recs }
    }

    /// `got` is the data and the lock token: what holding the lock means.
    pub closed spec fn owns(&self, got: Option<(PointsTo<T>, GhostVar<bool>)>) -> bool {
        got matches Some((p, g)) && {
            &&& p.id() == self.data.id()
            &&& p.is_init()
            &&& g.id() == self.consts().token
            &&& g@
        }
    }

    /// A mutex holding `value`, unlocked.
    pub fn new(value: T) -> (m: Self)
        ensures
            m.wf(),
    {
        let (data, Tracked(perm)) = PCell::new(value);
        let (state, Tracked(sp)) = PAtomicU32::new(UNLOCKED);
        let tracked (locked, token) = GhostVarAuth::new(false);
        let ghost n = model_threads();
        let ghost s0 = St {
            word: 0,
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
        let ghost c = MutexConsts {
            state: state.id(),
            data: data.id(),
            token: locked.id(),
            model: model.loc(),
            list: list.id(),
            recs: recs_auth.id(),
        };
        let tracked s = MutexShared {
            state: sp,
            locked,
            held: Some((perm, token)),
            model,
            list,
            recs_auth,
            recs,
            flags: Map::tracked_empty(),
        };
        proof {
            assert(s.list@.dom() =~= Set::<nat>::empty());
            assert forall|t: nat| t < model_threads() implies !(#[trigger] ph(s.model@, t) is Notify) by {
                assert(s.model@.th[t as int].ph == Ph::Idle);
            }
        }
        let tracked inv = AtomicInvariant::<_, _, MutexPred>::new(c, s, 0x6d75);
        Mutex { state, data, inv: Tracked(Some(inv)) }
    }

    /// The parking-lot key: the address of the lock word, not of the
    /// mutex. A lock nested in another's data can share the outer lock's
    /// address (`RwLock<Mutex<T>>` puts the mutex at offset 0), and then an
    /// unlock of one could wake a waiter of the other instead of its own.
    /// Two lock words alive at once never share an address.
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

    /// A call starts: it takes an idle model thread and starts `lock`
    /// (`timed` false) or a `try_lock*` (`timed` true).
    #[inline(always)]
    fn enter(&self, Ghost(timed): Ghost<bool>) -> (r: Tracked<Tok<P>>)
        requires
            self.wf(),
        ensures
            tok_at(r@, self.consts(), Ph::Fast),
            r@.value().timed == timed,
    {
        let tracked mut tok;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                tok = s.model.enter();
                s.model.agree(&tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = St { th: m.th.update(t as int, Th { ph: Ph::Fast, timed }), ..m };
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
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

    /// `cas(UNLOCKED, LOCKED)`, the model's `Fast` or `SpinCas`. Taking the
    /// lock hands over the data; on failure the thread goes to `fail`.
    #[inline(always)]
    fn cas_lock(&self, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(fail): Ghost<Ph>) -> (r: (bool, Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>))
        requires
            self.wf(),
            old(tok).id() == self.consts().model,
            match old(tok).value().ph {
                Ph::Fast => fail is Spin || (old(tok).value().timed && fail is Idle),
                Ph::SpinCas { left } => fail == (Ph::Spin { left: (left - 1) as nat }),
                _ => false,
            },
        ensures
            r.0 ==> self.owns(r.1@),
            tok_at(*final(tok), self.consts(), if r.0 { Ph::Crit } else { fail }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            ok = match self.state.compare_exchange(Tracked(&mut s.state), UNLOCKED, LOCKED) {
                Ok(_) => true,
                Err(_) => false,
            };
            proof {
                if ok {
                    let tracked (p, mut g) = s.held.tracked_take();
                    s.locked.update(&mut g, true);
                    got = Some((p, g));
                }
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = if ok { St { word: 1, ..go(m, t, Ph::Crit) } } else { go(m, t, fail) };
                if !ok {
                    if let Ph::Spin { left } = fail {
                        assert(s2 == go(m, t, Ph::Spin { left }));
                    }
                }
                assert(step(m, t, s2));
                s.model.step(tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        (ok, Tracked(got))
    }

    /// `lock_slow`'s load of the word, the model's `Spin { left }` with
    /// snoozes left.
    #[inline(always)]
    fn load_spin(&self, Tracked(tok): Tracked<&mut Tok<P>>, Ghost(left): Ghost<nat>) -> (v: u32)
        requires
            self.wf(),
            left > 0,
            tok_at(*old(tok), self.consts(), Ph::Spin { left }),
        ensures
            tok_at(*final(tok), self.consts(), if v == UNLOCKED { Ph::SpinCas { left } } else if v == CONTENDED { Ph::Swap } else { Ph::Spin { left: (left - 1) as nat } }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let v;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            v = self.state.load(Tracked(&s.state));
            proof {
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = go(m, t, if v == UNLOCKED { Ph::SpinCas { left } } else if v == CONTENDED { Ph::Swap } else { Ph::Spin { left: (left - 1) as nat } });
                assert(step(m, t, s2));
                s.model.step(tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        v
    }

    /// The model's `Spin { left: 0 }`: the backoff is used up.
    #[inline(always)]
    fn spun_out(&self, Tracked(tok): Tracked<&mut Tok<P>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Spin { left: 0 }),
        ensures
            tok_at(*final(tok), self.consts(), Ph::Swap),
            final(tok).value().timed == old(tok).value().timed,
    {
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = go(m, t, Ph::Swap);
                assert(step(m, t, s2));
                s.model.step(tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
    }

    /// Sets the lock word to contended, returning what it held, the
    /// model's `Swap`. Taking it from unlocked hands over the data.
    #[inline(always)]
    fn swap_contended(&self, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: (u32, Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>))
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Swap),
        ensures
            r.0 == UNLOCKED ==> self.owns(r.1@),
            tok_at(*final(tok), self.consts(), if r.0 == UNLOCKED { Ph::Crit } else { Ph::Check }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let old;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            old = self.state.swap(Tracked(&mut s.state), CONTENDED);
            proof {
                if old == UNLOCKED {
                    let tracked (p, mut g) = s.held.tracked_take();
                    s.locked.update(&mut g, true);
                    got = Some((p, g));
                }
                s.model.agree(tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = St { word: 2, ..go(m, t, if old == UNLOCKED { Ph::Crit } else { Ph::Check }) };
                assert(step(m, t, s2));
                s.model.step(tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        (old, Tracked(got))
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

    /// Whether the lock word is contended right now.
    pub fn is_contended(&self) -> bool
        requires
            self.wf(),
    {
        self.load() == CONTENDED
    }

    /// Whether some thread holds the lock right now.
    pub fn is_locked(&self) -> bool
        requires
            self.wf(),
    {
        self.load() != UNLOCKED
    }

    fn guard(&self, Tracked(got): Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>, Tracked(tok): Tracked<Tok<P>>) -> (g: MutexGuard<'_, T>)
        requires
            self.wf(),
            self.owns(got),
            tok_at(tok, self.consts(), Ph::Crit),
        ensures
            g.wf(),
            g.mutex() == self,
    {
        let tracked (perm, token) = got.tracked_unwrap();
        MutexGuard { lock: self, perm: Tracked(Some(perm)), token: Tracked(Some(token)), tok: Tracked(Some(tok)) }
    }

    /// Takes the lock if it is free.
    #[inline]
    pub fn try_lock(&self) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
    {
        let Tracked(mut tok) = self.enter(Ghost(true));
        let (ok, got) = self.cas_lock(Tracked(&mut tok), Ghost(Ph::Idle));
        if ok {
            Some(self.guard(got, Tracked(tok)))
        } else {
            self.leave(Tracked(tok));
            None
        }
    }

    /// Takes the lock, sleeping while another thread holds it.
    #[inline]
    pub fn lock(&self) -> (g: MutexGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.mutex() == self,
    {
        let Tracked(mut tok) = self.enter(Ghost(false));
        let (ok, got) = self.cas_lock(Tracked(&mut tok), Ghost(Ph::Spin { left: SPINS as nat }));
        if ok {
            return self.guard(got, Tracked(tok));
        }
        // Without a deadline lock_slow only returns with the lock.
        match self.lock_slow(no_deadline(), Tracked(tok)) {
            Some(g) => g,
            None => vstd::pervasive::unreached(),
        }
    }

    /// The contended path: spin briefly, then mark the lock contended and
    /// sleep until the holder wakes us. Returns `None` only at the deadline.
    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn lock_slow(&self, deadline: Deadline, Tracked(tok0): Tracked<Tok<P>>) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
            tok_at(tok0, self.consts(), Ph::Spin { left: SPINS as nat }),
            has_deadline(deadline) ==> tok0.value().timed,
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
            r is None ==> tok0.value().timed,
    {
        let ghost timed = tok0.value().timed;
        let tracked mut tok = tok0;
        // Spin while the holder is likely to finish soon, as parking_lot
        // does, but not once others are already asleep.
        let backoff = Backoff::new();
        let mut left: u8 = SPINS;
        loop
            invariant_except_break
                self.wf(),
                tok_at(tok, self.consts(), Ph::Spin { left: left as nat }),
                tok.value().timed == timed,
                timed == tok0.value().timed,
            ensures
                self.wf(),
                tok_at(tok, self.consts(), Ph::Swap),
                tok.value().timed == timed,
                timed == tok0.value().timed,
            decreases left,
        {
            if left == 0 {
                self.spun_out(Tracked(&mut tok));
                break;
            }
            let st = self.load_spin(Tracked(&mut tok), Ghost(left as nat));
            if st == UNLOCKED {
                let (ok, got) = self.cas_lock(Tracked(&mut tok), Ghost(Ph::Spin { left: (left - 1) as nat }));
                if ok {
                    return Some(self.guard(got, Tracked(tok)));
                }
            } else if st == CONTENDED {
                break;
            }
            backoff.snooze();
            left = left - 1;
        }
        loop
            invariant
                self.wf(),
                tok_at(tok, self.consts(), Ph::Swap),
                tok.value().timed == timed,
                timed == tok0.value().timed,
                has_deadline(deadline) ==> timed,
        {
            let (old, got) = self.swap_contended(Tracked(&mut tok));
            if old == UNLOCKED {
                // Taken as contended: there may be other sleepers, whom our
                // unlock must wake.
                return Some(self.guard(got, Tracked(tok)));
            }
            let (late, _) = time_left(&deadline);
            match self.check(late, Tracked(&mut tok)) {
                None => {
                    if late {
                        assert(timed);
                        self.leave(Tracked(tok));
                        return None;
                    }
                },
                Some(me) => {
                    // Asleep until woken, or until the deadline.
                    loop
                        invariant_except_break
                            self.wf(),
                            me.wf(),
                            me.lot@ == self.lot(),
                            tok_at(tok, self.consts(), Ph::Asleep { tk: me.tk@ }),
                            tok.value().timed == timed,
                timed == tok0.value().timed,
                            has_deadline(deadline) ==> timed,
                        ensures
                            self.wf(),
                            tok_at(tok, self.consts(), Ph::Swap),
                            tok.value().timed == timed,
                timed == tok0.value().timed,
                    {
                        if self.wait_flag(&me, Tracked(&mut tok)) {
                            break;
                        }
                        let (late, left) = time_left(&deadline);
                        if late {
                            if self.timeout(&me, Tracked(&mut tok)) {
                                break;
                            }
                            assert(timed);
                            self.leave(Tracked(tok));
                            return None;
                        }
                        park_for(left);
                    }
                },
            }
        }
    }

    /// The model's `Check`: `parking::park`'s critical section with the
    /// re-check `is_contended`. If the word is still contended the thread
    /// goes on the list and gets its waiter; if not, it loops, or gives up
    /// if it is `late`.
    #[cold]
    fn check(&self, late: bool, Tracked(tok): Tracked<&mut Tok<P>>) -> (r: Option<Arc<Waiter>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Check),
            late ==> old(tok).value().timed,
        ensures
            final(tok).value().timed == old(tok).value().timed,
            r matches Some(me) ==> {
                &&& me.wf()
                &&& me.lot@ == self.lot()
                &&& tok_at(*final(tok), self.consts(), Ph::Asleep { tk: me.tk@ })
            },
            r is None ==> tok_at(*final(tok), self.consts(), if late { Ph::Idle } else { Ph::Swap }),
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
                let m = s.model@;
                let t = tok.key();
                if v == CONTENDED {
                    tk = m.next_tk;
                    let s2 = St {
                        list: m.list.insert(tk),
                        owner: m.owner.insert(tk, t),
                        next_tk: tk + 1,
                        ..go(m, t, Ph::Asleep { tk })
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
                    let s2 = go(m, t, if late { Ph::Idle } else { Ph::Swap });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                }
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        if v == CONTENDED {
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
    /// set, and the thread goes on to retry.
    #[inline]
    fn wait_flag(&self, me: &Arc<Waiter>, Tracked(tok): Tracked<&mut Tok<P>>) -> (flag: bool)
        requires
            self.wf(),
            me.wf(),
            me.lot@ == self.lot(),
            tok_at(*old(tok), self.consts(), Ph::Asleep { tk: me.tk@ }),
        ensures
            tok_at(*final(tok), self.consts(), if flag { Ph::Swap } else { Ph::Asleep { tk: me.tk@ } }),
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
                assert(ph(s.model@, t) == (Ph::Asleep { tk }));
                assert(tk < s.model@.next_tk);
                s.recs.intersection_agrees_points_to(me.rec.borrow());
            }
            flag = me.notified.load(Tracked(s.flags.tracked_borrow(tk)));
            proof {
                if flag {
                    let m = s.model@;
                    let t = tok.key();
                    let s2 = go(m, t, Ph::Swap);
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                        if u != t {
                            assert(ph(s.model@, u) == ph(m, u));
                        }
                    }
                }
            }
        });
        flag
    }

    /// Past the deadline: the bucket's critical section that takes the
    /// waiter off the list, unless a waker already has (then its flag is
    /// set, and the thread retries: true).
    #[cold]
    fn timeout(&self, me: &Arc<Waiter>, Tracked(tok): Tracked<&mut Tok<P>>) -> (woken: bool)
        requires
            self.wf(),
            me.wf(),
            me.lot@ == self.lot(),
            tok_at(*old(tok), self.consts(), Ph::Asleep { tk: me.tk@ }),
            old(tok).value().timed,
        ensures
            tok_at(*final(tok), self.consts(), if woken { Ph::Swap } else { Ph::Idle }),
            final(tok).value().timed == old(tok).value().timed,
    {
        let ghost tk = me.tk@;
        let (key, Tracked(kf)) = self.key();
        let (g, mut l, Tracked(half), Tracked(bids)) = lock_bucket(key, Tracked(&kf));
        let tracked mut half = half;
        let tracked mut bids = bids;
        let ghost q0 = l.q@;
        let ghost half0 = half@;
        let i = find_id(&l, me.id);
        let flag;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.list.agree(&half);
                s.model.agree(tok);
                s.model.lemma_inv();
                let t = tok.key();
                assert(t < model_threads());
                assert(ph(s.model@, t) == (Ph::Asleep { tk }));
                assert(tk < s.model@.next_tk);
                s.recs.intersection_agrees_points_to(me.rec.borrow());
            }
            flag = me.notified.load(Tracked(s.flags.tracked_borrow(tk)));
            proof {
                let m = s.model@;
                let t = tok.key();
                if flag {
                    let s2 = go(m, t, Ph::Swap);
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                } else {
                    // Not woken, so still listed: nobody is between taking
                    // it off and setting its flag.
                    assert(ph(m, t) == (Ph::Asleep { tk }));
                    if !m.list.contains(tk) {
                        let u = choose|u: nat| u < model_threads() && #[trigger] ph(m, u) == (Ph::Notify { tk });
                        assert(ph(m, u) is Notify);
                    }
                    assert(half0.contains_key(tk));
                    let j = choose|j: int| 0 <= j < q0.len() && (#[trigger] q0[j]).key == key && q0[j].tk@ == tk;
                    assert(q0[j].id == half0[tk]);
                    assert(i < q0.len());
                    assert(i == j);
                    let s2 = St { list: m.list.remove(tk), ..go(m, t, Ph::Idle) };
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    s.list.update(&mut half, half0.remove(tk));
                    assert(s.list@.dom() =~= s2.list);
                }
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        if !flag {
            let ghost l0 = l;
            let _ = l.q.remove(i);
            proof {
                lemma_remove(q0, key, self.lot(), half0, i as int);
                lemma_remove_wf(l0, l.q@, i as int);
                lemma_bids_remove(q0, l.next, bids, i as int);
            }
        }
        unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
        flag
    }

    /// Takes the lock, sleeping until `deadline` at the latest.
    fn try_lock_until_deadline(&self, deadline: Deadline) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
    {
        let Tracked(mut tok) = self.enter(Ghost(true));
        let (ok, got) = self.cas_lock(Tracked(&mut tok), Ghost(Ph::Spin { left: SPINS as nat }));
        if ok {
            return Some(self.guard(got, Tracked(tok)));
        }
        self.lock_slow(deadline, Tracked(tok))
    }

    /// Releases the lock held by `g`'s owner, the model's `Crit`. Waking a
    /// sleeper happens after the release, so it never touches the data.
    #[inline]
    fn unlock(&self, Tracked(perm): Tracked<PointsTo<T>>, Tracked(token): Tracked<GhostVar<bool>>, Tracked(tok): Tracked<Tok<P>>)
        requires
            self.wf(),
            perm.id() == self.data.id(),
            perm.is_init(),
            token.id() == self.consts().token,
            token@,
            tok_at(tok, self.consts(), Ph::Crit),
    {
        let tracked mut tok = tok;
        let old;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                s.locked.agree(&token);
            }
            old = self.state.swap(Tracked(&mut s.state), UNLOCKED);
            proof {
                let tracked mut token = token;
                s.locked.update(&mut token, false);
                s.held = Some((perm, token));
                s.model.agree(&tok);
                let m = s.model@;
                let t = tok.key();
                let s2 = St { word: 0, ..go(m, t, if old == CONTENDED { Ph::Unpark } else { Ph::Idle }) };
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                    if u != t {
                        assert(ph(s.model@, u) == ph(m, u));
                    }
                }
            }
        });
        if old == CONTENDED {
            self.unpark_one(Tracked(&mut tok));
        }
        self.leave(Tracked(tok));
    }

    /// The model's `Unpark` and `Notify`: `parking::unpark(key, 1)`'s
    /// critical section, which takes one waiter off the list and sets its
    /// flag, then wakes its thread.
    #[cold]
    fn unpark_one(&self, Tracked(tok): Tracked<&mut Tok<P>>)
        requires
            self.wf(),
            tok_at(*old(tok), self.consts(), Ph::Unpark),
        ensures
            tok_at(*final(tok), self.consts(), Ph::Idle),
    {
        let (key, Tracked(kf)) = self.key();
        let (g, mut l, Tracked(half), Tracked(bids)) = lock_bucket(key, Tracked(&kf));
        let tracked mut half = half;
        let tracked mut bids = bids;
        let ghost q0 = l.q@;
        let ghost half0 = half@;
        let i = find_key(&l, key);
        if i < l.q.len() {
            let ghost l0 = l;
            let w = l.q.remove(i);
            let ghost tk = w.tk@;
            proof {
                lemma_remove(q0, key, self.lot(), half0, i as int);
                lemma_remove_wf(l0, l.q@, i as int);
                lemma_bids_remove(q0, l.next, bids, i as int);
            }
            open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
                proof {
                    s.list.agree(&half);
                    s.model.agree(tok);
                    s.model.lemma_inv();
                    s.recs.intersection_agrees_points_to(w.rec.borrow());
                }
                let ghost flags0 = s.flags;
                let tracked mut fp = s.flags.tracked_remove(tk);
                w.notified.store(Tracked(&mut fp), true);
                proof {
                    s.flags.tracked_insert(tk, fp);
                    let m = s.model@;
                    let t = tok.key();
                    let s1 = St { list: m.list.remove(tk), ..go(m, t, Ph::Notify { tk }) };
                    assert(step(m, t, s1));
                    s.model.step(tok, s1);
                    let s2 = St { notified: s1.notified.insert(tk), ..go(s1, t, Ph::Idle) };
                    assert(step(s1, t, s2));
                    s.model.step(tok, s2);
                    s.list.update(&mut half, half0.remove(tk));
                    assert(s.list@.dom() =~= s2.list);
                    assert(s.flags.dom() =~= Set::range(0, s2.next_tk));
                    assert forall|x: nat| x < s2.next_tk implies {
                        &&& (#[trigger] s.flags[x]).id() == s.recs@[x].0
                        &&& s.flags[x].value() == s2.notified.contains(x)
                    } by {
                        if x != tk {
                            assert(s.flags[x] == flags0[x]);
                        }
                    }
                    assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                        if u != t {
                            assert(ph(s.model@, u) == ph(m, u));
                        }
                    }
                }
            });
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
            w.thread.unpark();
        } else {
            open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
                proof {
                    s.list.agree(&half);
                    s.model.agree(tok);
                    let m = s.model@;
                    let t = tok.key();
                    // Nobody is listed under the key, so nobody is asleep.
                    assert(m.list =~= Set::empty()) by {
                        assert forall|x: nat| !m.list.contains(x) by {
                            if m.list.contains(x) {
                                assert(half0.contains_key(x));
                                let j = choose|j: int| 0 <= j < q0.len() && (#[trigger] q0[j]).key == key && q0[j].tk@ == x;
                            }
                        }
                    }
                    let s2 = go(m, t, Ph::Idle);
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s.model@, u) is Notify) by {
                        if u != t {
                            assert(ph(s.model@, u) == ph(m, u));
                        }
                    }
                }
            });
            unlock_bucket(g, l, Tracked(half), Tracked(bids), Tracked(&kf));
        }
    }

    /// Takes the value out if the mutex is unlocked. `&mut self` means no
    /// guard exists, unless one was leaked with `mem::forget`. The mutex is
    /// not usable afterwards: only `drop` and `into_inner` call this.
    fn take_inner(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
    {
        let tracked inv = self.inv.borrow_mut().tracked_take();
        let tracked mut s = inv.into_inner();
        if self.state.load(Tracked(&s.state)) == UNLOCKED {
            let tracked (mut perm, _token) = s.held.tracked_take();
            let v = self.data.take(Tracked(&mut perm));
            self.state.store(Tracked(&mut s.state), LOCKED);
            Some(v)
        } else {
            None
        }
    }

    /// Consumes the mutex, returning the value.
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
}

impl<'a, T> MutexGuard<'a, T> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@ matches Some(p) && p.id() == self.lock.data.id() && p.is_init()
        &&& self.token@ matches Some(t) && t.id() == self.lock.consts().token && t@
        &&& self.tok@ matches Some(t) && tok_at(t, self.lock.consts(), Ph::Crit)
    }

    pub closed spec fn mutex(&self) -> &'a Mutex<T> {
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
        let tracked perm = self.perm.borrow_mut().tracked_take();
        let tracked token = self.token.borrow_mut().tracked_take();
        let tracked tok = self.tok.borrow_mut().tracked_take();
        self.lock.unlock(Tracked(perm), Tracked(token), Tracked(tok));
    }
}

} // verus!

impl<T> Drop for Mutex<T> {
    fn drop(&mut self) {
        let _ = self.take_inner();
    }
}

impl<'a, T> Drop for MutexGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.release();
    }
}

impl<'a, T> std::ops::Deref for MutexGuard<'a, T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.get()
    }
}

impl<'a, T> std::ops::DerefMut for MutexGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.get_mut()
    }
}

// SAFETY: the proof shows the data is reached only through the one guard
// that exists at a time, so sharing the mutex between threads moves `T`
// between them but never shares it, as for std's Mutex.
unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}
unsafe impl<'a, T: Sync> Sync for MutexGuard<'a, T> {}

impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Mutex::new(T::default())
    }
}

impl<T> From<T> for Mutex<T> {
    fn from(v: T) -> Self {
        Mutex::new(v)
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.try_lock() {
            Some(g) => f.debug_struct("Mutex").field("data", &&*g).finish(),
            None => f.debug_struct("Mutex").field("data", &format_args!("<locked>")).finish(),
        }
    }
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

impl<T> Mutex<T> {
    /// Takes the lock, sleeping until `deadline` at the latest.
    pub fn try_lock_until(&self, deadline: std::time::Instant) -> Option<MutexGuard<'_, T>> {
        self.try_lock_until_deadline(Deadline(Some(deadline)))
    }

    /// Takes the lock, sleeping for at most `timeout`.
    pub fn try_lock_for(&self, timeout: std::time::Duration) -> Option<MutexGuard<'_, T>> {
        self.try_lock_until_deadline(Deadline(Some(std::time::Instant::now() + timeout)))
    }
}
