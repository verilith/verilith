//! A verified mutual exclusion lock with parking_lot's `Mutex` API.
//!
//! The lock word is Drepper's three-state futex mutex ("Futexes Are
//! Tricky", mutex 3): 0 unlocked, 1 locked, 2 locked and possibly with
//! sleepers. What is proved: the guard is the only way to reach the data,
//! at most one guard exists at a time, and the data is dropped exactly once.
//! The proof does not depend on the parking code ([`crate::parking`]),
//! which only decides when a waiting thread sleeps.
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::ghost_var::*;
use vstd::resource::Loc;
use crate::util::Deadline;

verus! {

/// The mutex's constants: the ids of its atomic, its cell and its token.
pub struct MutexConsts {
    /// The id of the state atomic.
    pub state: int,
    /// The id of the data's cell.
    pub data: CellId,
    /// The location of the `locked` ghost variable.
    pub token: Loc,
}

/// Everything the lock owns while unlocked, and the bookkeeping that tells
/// a releasing thread the lock is held.
pub tracked struct MutexShared<T> {
    /// The state atomic's permission.
    pub state: PermissionU32,
    /// True exactly while the lock is held.
    pub locked: GhostVarAuth<bool>,
    /// The data and the other half of `locked`, while unlocked; a guard
    /// holds them while locked.
    pub held: Option<(PointsTo<T>, GhostVar<bool>)>,
}

/// The mutex's invariant (see its `inv`).
pub struct MutexPred;

impl<T> InvariantPredicate<MutexConsts, MutexShared<T>> for MutexPred {
    open spec fn inv(c: MutexConsts, s: MutexShared<T>) -> bool {
        &&& s.state@.patomic == c.state
        &&& s.locked.id() == c.token
        &&& s.locked@ == (s.state@.value != 0)
        &&& (s.state@.value == 0) == (s.held is Some)
        &&& s.held matches Some((p, g)) ==> {
            &&& p.id() == c.data
            &&& p.is_init()
            &&& g.id() == c.token
        }
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
}

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const CONTENDED: u32 = 2;

impl<T> Mutex<T> {
    pub closed spec fn consts(&self) -> MutexConsts {
        self.inv@->0.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.inv@ is Some
        &&& self.consts().state == self.state.id()
        &&& self.consts().data == self.data.id()
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
        let ghost c = MutexConsts { state: state.id(), data: data.id(), token: locked.id() };
        let tracked s = MutexShared { state: sp, locked, held: Some((perm, token)) };
        let tracked inv = AtomicInvariant::<_, _, MutexPred>::new(c, s, 0x6d75);
        Mutex { state, data, inv: Tracked(Some(inv)) }
    }

    /// Moves the lock word from `from` to `to` if it holds `from`. Taking
    /// it from unlocked hands over the data.
    #[inline(always)]
    fn cas(&self, from: u32, to: u32) -> (r: (bool, Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>))
        requires
            self.wf(),
            to != UNLOCKED,
        ensures
            r.0 && from == UNLOCKED ==> self.owns(r.1@),
    {
        let ok;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            ok = match self.state.compare_exchange(Tracked(&mut s.state), from, to) {
                Ok(_) => true,
                Err(_) => false,
            };
            if ok && from == UNLOCKED {
                proof {
                    let tracked (p, mut g) = s.held.tracked_take();
                    s.locked.update(&mut g, true);
                    got = Some((p, g));
                }
            }
        });
        (ok, Tracked(got))
    }

    /// Sets the lock word to contended, returning what it held. Taking it
    /// from unlocked hands over the data.
    #[inline(always)]
    fn swap_contended(&self) -> (r: (u32, Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>))
        requires
            self.wf(),
        ensures
            r.0 == UNLOCKED ==> self.owns(r.1@),
    {
        let old;
        let tracked mut got = None;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            old = self.state.swap(Tracked(&mut s.state), CONTENDED);
            if old == UNLOCKED {
                proof {
                    let tracked (p, mut g) = s.held.tracked_take();
                    s.locked.update(&mut g, true);
                    got = Some((p, g));
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

    /// Whether the lock word is contended right now; the parking lot's
    /// re-check before sleeping.
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

    fn guard(&self, Tracked(got): Tracked<Option<(PointsTo<T>, GhostVar<bool>)>>) -> (g: MutexGuard<'_, T>)
        requires
            self.wf(),
            self.owns(got),
        ensures
            g.wf(),
            g.mutex() == self,
    {
        let tracked (perm, token) = got.tracked_unwrap();
        MutexGuard { lock: self, perm: Tracked(Some(perm)), token: Tracked(Some(token)) }
    }

    /// Takes the lock if it is free.
    #[inline]
    pub fn try_lock(&self) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
    {
        let (ok, got) = self.cas(UNLOCKED, LOCKED);
        if ok {
            Some(self.guard(got))
        } else {
            None
        }
    }

    /// Takes the lock, sleeping while another thread holds it.
    #[inline]
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (g: MutexGuard<'_, T>)
        requires
            self.wf(),
        ensures
            g.wf(),
            g.mutex() == self,
    {
        let (ok, got) = self.cas(UNLOCKED, LOCKED);
        if ok {
            return self.guard(got);
        }
        // Without a deadline lock_slow only returns with the lock.
        loop
            invariant
                self.wf(),
        {
            if let Some(g) = self.lock_slow(crate::util::no_deadline()) {
                return g;
            }
        }
    }

    /// The contended path: spin briefly, then mark the lock contended and
    /// sleep until the holder wakes us. Returns `None` only at the deadline.
    #[cold]
    #[verifier::exec_allows_no_decreases_clause]
    fn lock_slow(&self, deadline: Deadline) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
    {
        // Spin while the holder is likely to finish soon, as parking_lot
        // does, but not once others are already asleep.
        let backoff = crate::util::Backoff::new();
        while !backoff.is_completed()
            invariant
                self.wf(),
        {
            let st = self.load();
            if st == UNLOCKED {
                let (ok, got) = self.cas(UNLOCKED, LOCKED);
                if ok {
                    return Some(self.guard(got));
                }
            } else if st == CONTENDED {
                break;
            }
            backoff.snooze();
        }
        loop
            invariant
                self.wf(),
        {
            let (old, got) = self.swap_contended();
            if old == UNLOCKED {
                // Taken as contended: there may be other sleepers, whom our
                // unlock must wake.
                return Some(self.guard(got));
            }
            if !self.park(deadline) {
                return None;
            }
        }
    }

    /// Sleeps while the lock word is contended. Returns false at the deadline.
    #[verifier::external_body]
    fn park(&self, deadline: Deadline) -> bool {
        let key = self as *const Self as usize;
        let ok = crate::parking::park(key, || self.is_contended(), deadline.0);
        ok || deadline.0.map_or(true, |d| std::time::Instant::now() < d)
    }

    #[verifier::external_body]
    fn unpark_one(&self) {
        crate::parking::unpark(self as *const Self as usize, 1);
    }

    /// Takes the lock, sleeping until `deadline` at the latest.
    fn try_lock_until_deadline(&self, deadline: Deadline) -> (r: Option<MutexGuard<'_, T>>)
        requires
            self.wf(),
        ensures
            r matches Some(g) ==> g.wf() && g.mutex() == self,
    {
        let (ok, got) = self.cas(UNLOCKED, LOCKED);
        if ok {
            return Some(self.guard(got));
        }
        self.lock_slow(deadline)
    }

    /// Releases the lock held by `g`'s owner. Waking a sleeper happens after
    /// the release, so it never touches the data.
    #[inline]
    fn unlock(&self, Tracked(perm): Tracked<PointsTo<T>>, Tracked(token): Tracked<GhostVar<bool>>)
        requires
            self.wf(),
            perm.id() == self.data.id(),
            perm.is_init(),
            token.id() == self.consts().token,
            token@,
    {
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
            }
        });
        if old == CONTENDED {
            self.unpark_one();
        }
    }

    /// Takes the value out if the mutex is unlocked, leaving it locked and
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
        let r = if self.state.load(Tracked(&s.state)) == UNLOCKED {
            let tracked (mut perm, mut token) = s.held.tracked_take();
            let v = self.data.take(Tracked(&mut perm));
            self.state.store(Tracked(&mut s.state), LOCKED);
            proof {
                s.locked.update(&mut token, true);
            }
            Some(v)
        } else {
            None
        };
        let tracked inv = AtomicInvariant::<_, _, MutexPred>::new(c, s, 0x6d75);
        self.inv = Tracked(Some(inv));
        r
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
        self.lock.unlock(Tracked(perm), Tracked(token));
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
