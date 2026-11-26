//! A verified fair lock: a ticket lock, for the short critical sections
//! of the parking lot's buckets and the channel's waiter lists.
//!
//! These used to be `std::sync::Mutex`, trusted for mutual exclusion and,
//! by the progress proofs, assumed fair: that a thread waiting for one
//! gets it. `std`'s mutex does not promise that (it lets threads barge,
//! and on macOS it is `os_unfair_lock`). This lock is proved to give both:
//!
//! - **Mutual exclusion**: the value goes to one guard at a time, and
//!   the invariant `P::inv` holds of it whenever the lock is free.
//! - **Starvation freedom**: the code follows the model of
//!   `progress::ticket` (one model step per atomic access, as for the
//!   other locks), whose theorem says every waiting thread gets the lock
//!   in every fair execution.
//!
//! A thread takes a ticket with a `fetch_add` on `next` and waits until
//! `serving` equals it; `unlock` adds one to `serving`. Both counters wrap
//! around at 2^64. That is safe because fewer than 2^62 tickets are ever
//! outstanding (`progress::ticket::lemma_bound`: each belongs to a
//! different call in progress, and the model has 2^62 threads, so this is
//! `Model::pool_nonempty`'s assumption with that number), so a waiter's
//! ticket and `serving` are equal exactly when they are equal mod 2^64.
//!
//! Waiting spins, then yields, and never parks: the critical sections
//! these locks protect are a few list operations long.
// Some parameters and imports are used only in specifications and proofs.
#![allow(unused_variables, unused_imports, unused_mut)]
use crate::model::*;
use crate::progress::ticket::{Ph, St, Th, P as TP};
#[cfg(verus_only)]
use crate::progress::ticket::{go, lemma_bound, ph, step, ticket};
use crate::util::{wait_turn, Backoff};
use vstd::atomic::*;
use vstd::cell::pcell_maybe_uninit::*;
use vstd::cell::CellId;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::simple_pptr::MemContents;

verus! {

/// What a [`Lock`] protects: `inv(k, v)` holds of its value whenever the
/// lock is free.
pub trait LockInv<K, V> {
    spec fn inv(k: K, v: V) -> bool;
}

/// The number of threads in each lock's model: more calls than could
/// ever be in progress on one lock at once (see the module comment).
pub open spec fn model_threads() -> nat {
    0x4000_0000_0000_0000
}

/// 2^64: what the counters wrap around at.
pub open spec fn wrap() -> int {
    0x1_0000_0000_0000_0000
}

/// The lock's constants: its invariant's constant, and the ids of its
/// atomics, its cell and its model.
pub ghost struct FairConsts<K> {
    pub k: K,
    pub next: int,
    pub serving: int,
    pub cell: CellId,
    pub model: Loc,
}

/// What the lock owns: its counters, the value while it is free, and the
/// progress model.
pub tracked struct FairShared<V> {
    pub next: PermissionU64,
    pub serving: PermissionU64,
    pub held: Option<PointsTo<V>>,
    pub model: Model<TP>,
}

/// The lock's invariant.
pub struct FairPred<P> {
    _p: core::marker::PhantomData<P>,
}

/// Nobody holds the lock in model state `m`.
pub open spec fn free(m: St) -> bool {
    forall|t: nat| t < model_threads() ==> !(#[trigger] ph(m, t) is Crit)
}

impl<K, V, P: LockInv<K, V>> InvariantPredicate<FairConsts<K>, FairShared<V>> for FairPred<P> {
    open spec fn inv(c: FairConsts<K>, s: FairShared<V>) -> bool {
        let m = s.model@;
        &&& s.next@.patomic == c.next
        &&& s.serving@.patomic == c.serving
        &&& s.model.wf()
        &&& s.model.loc() == c.model
        &&& s.model.n() == model_threads()
        &&& s.next@.value as int == m.next as int % wrap()
        &&& s.serving@.value as int == m.serving as int % wrap()
        &&& (s.held is Some) == free(m)
        &&& s.held matches Some(p) ==> {
            &&& p.id() == c.cell
            &&& p.is_init()
            &&& P::inv(c.k, p.value())
        }
    }
}

/// A fair mutual-exclusion lock holding a `V`, with `P::inv` on it.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(P)]
pub struct Lock<K, V, P: LockInv<K, V>> {
    next: PAtomicU64,
    serving: PAtomicU64,
    cell: PCell<V>,
    /// `None` only while the lock is being dropped.
    inv: Tracked<Option<AtomicInvariant<FairConsts<K>, FairShared<V>, FairPred<P>>>>,
}

/// Aborts if dropped: a guard must be given back with
/// [`LockGuard::unlock`], since the lock's value went with it.
#[verifier::external_body]
pub struct Bomb {
    _p: (),
}

#[verifier::external_body]
#[inline(always)]
fn bomb() -> Bomb {
    Bomb { _p: () }
}

#[verifier::external_body]
#[inline(always)]
fn defuse(b: Bomb) {
    core::mem::forget(b)
}

/// Proof that a [`Lock`] is held.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(P)]
pub struct LockGuard<'a, K, V, P: LockInv<K, V>> {
    lock: &'a Lock<K, V, P>,
    perm: Tracked<PointsTo<V>>,
    /// The model thread of the call that holds the lock.
    tok: Tracked<Tok<TP>>,
    bomb: Bomb,
}

/// `a` and `b` are equal mod 2^64 and less than 2^64 apart.
proof fn lemma_mod_eq(a: int, b: int)
    requires
        0 <= a <= b < a + wrap(),
        a % wrap() == b % wrap(),
    ensures
        a == b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, wrap());
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, wrap());
    let qa = a / wrap();
    let qb = b / wrap();
    assert(b - a == wrap() * (qb - qa));
    assert(qb - qa == 0) by (nonlinear_arith)
        requires
            b - a == wrap() * (qb - qa),
            0 <= b - a < wrap(),
            wrap() > 0,
    ;
}

/// Adding one to a counter mod 2^64.
proof fn lemma_wrap_inc(a: nat, v: u64)
    requires
        v as int == a as int % wrap(),
    ensures
        vstd::wrapping::u64_specs::wrapping_add(v, 1) as int == (a + 1) as int % wrap(),
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(a as int, 1, wrap());
    vstd::arithmetic::div_mod::lemma_small_mod(1, wrap() as nat);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(a as int, wrap());
    if v as int + 1 < wrap() {
        vstd::arithmetic::div_mod::lemma_small_mod((v + 1) as nat, wrap() as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_mod_self_0(wrap());
    }
}

impl<K, V, P: LockInv<K, V>> Lock<K, V, P> {
    pub closed spec fn consts(&self) -> FairConsts<K> {
        self.inv@->0.constant()
    }

    /// The constant the invariant is about.
    pub closed spec fn k(&self) -> K {
        self.consts().k
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.inv@ is Some
        &&& self.consts().next == self.next.id()
        &&& self.consts().serving == self.serving.id()
        &&& self.consts().cell == self.cell.id()
    }

    /// A free lock holding `v`.
    pub fn new(v: V, Ghost(k): Ghost<K>) -> (r: Self)
        requires
            P::inv(k, v),
        ensures
            r.k() == k,
            r.wf(),
    {
        let (cell, Tracked(perm)) = PCell::new(v);
        let (next, Tracked(np)) = PAtomicU64::new(0);
        let (serving, Tracked(sp)) = PAtomicU64::new(0);
        let ghost n = model_threads();
        let ghost s0 = St { next: 0, serving: 0, th: Seq::new(n, |i: int| Th { ph: Ph::Idle }) };
        let tracked model = Model::<TP>::new(s0, n);
        let ghost c = FairConsts { k, next: next.id(), serving: serving.id(), cell: cell.id(), model: model.loc() };
        let tracked s = FairShared { next: np, serving: sp, held: Some(perm), model };
        proof {
            assert forall|t: nat| t < model_threads() implies !(#[trigger] ph(s0, t) is Crit) by {
                assert(s0.th[t as int].ph == Ph::Idle);
            }
            vstd::arithmetic::div_mod::lemma_small_mod(0, wrap() as nat);
        }
        let tracked inv = AtomicInvariant::<_, _, FairPred<P>>::new(c, s, 0x6661);
        Lock { next, serving, cell, inv: Tracked(Some(inv)) }
    }

    /// Takes a ticket. Returns it, mod 2^64.
    #[inline(always)]
    fn take_ticket(&self) -> (r: (u64, Tracked<Tok<TP>>, Ghost<nat>))
        requires
            self.wf(),
        ensures
            r.1@.id() == self.consts().model,
            r.1@.value().ph == (Ph::Wait { tk: r.2@ }),
            r.0 as int == r.2@ as int % wrap(),
    {
        let tracked mut tok;
        let ghost mut tkn: nat;
        let tk;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            proof {
                tok = s.model.enter();
                s.model.agree(&tok);
            }
            tk = self.next.fetch_add_wrapping(Tracked(&mut s.next), 1);
            proof {
                let m = s.model@;
                let t = tok.key();
                tkn = m.next;
                lemma_wrap_inc(m.next, tk);
                let s2 = St { next: m.next + 1, ..go(m, t, Ph::Wait { tk: m.next }) };
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
                assert(t < model_threads());
                assert(ph(m, t) == Ph::Idle);
                if free(m) {
                    assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s2, u) is Crit) by {
                        if u != t {
                            assert(ph(s2, u) == ph(m, u));
                        }
                    }
                } else {
                    let u = choose|u: nat| u < model_threads() && (#[trigger] ph(m, u) is Crit);
                    assert(u != t);
                    assert(ph(s2, u) == ph(m, u));
                }
                assert(ph(s2, t) is Wait);
                assert(free(s2) == free(m));
                assert(s.next@.value as int == s2.next as int % wrap());
            }
        });
        (tk, Tracked(tok), Ghost(tkn))
    }

    /// One load of `serving`, waiting with ticket `tk`. On `true` the
    /// lock is ours, with its value's permission.
    #[inline(always)]
    fn poll(&self, tk: u64, Tracked(tok): Tracked<&mut Tok<TP>>, Ghost(tkn): Ghost<nat>) -> (r: (bool, u64, Tracked<Option<PointsTo<V>>>))
        requires
            self.wf(),
            old(tok).id() == self.consts().model,
            old(tok).value().ph == (Ph::Wait { tk: tkn }),
            tk as int == tkn as int % wrap(),
        ensures
            final(tok).id() == self.consts().model,
            final(tok).key() == old(tok).key(),
            r.0 ==> final(tok).value().ph == (Ph::Crit { tk: tkn }),
            r.0 ==> (r.2@ matches Some(p) && p.id() == self.cell.id() && p.is_init() && P::inv(self.k(), p.value())),
            !r.0 ==> final(tok).value() == old(tok).value(),
    {
        let tracked mut got = None;
        let cur;
        open_atomic_invariant!(self.inv.borrow().tracked_borrow() => s => {
            cur = self.serving.load(Tracked(&s.serving));
            proof {
                s.model.agree(tok);
                s.model.lemma_inv();
                let m = s.model@;
                let t = tok.key();
                let n = model_threads();
                lemma_bound(m, n);
                assert(m.serving <= tkn < m.next) by {
                    assert(match ph(m, t) {
                        Ph::Idle => true,
                        Ph::Wait { tk } => m.serving <= tk < m.next,
                        Ph::Crit { tk } => tk == m.serving && tk < m.next,
                    });
                }
                if cur == tk {
                    lemma_mod_eq(m.serving as int, tkn as int);
                    // Nobody is in: whoever were would hold ticket
                    // `serving`, which is `t`'s.
                    assert forall|u: nat| u < n implies !(#[trigger] ph(m, u) is Crit) by {
                        if u != t && ph(m, u) is Crit {
                            assert(ticket(ph(m, u)) != ticket(ph(m, t)));
                        }
                    }
                    let s2 = go(m, t, Ph::Crit { tk: tkn });
                    assert(step(m, t, s2));
                    s.model.step(tok, s2);
                    got = Some(s.held.tracked_take());
                    assert(!free(s2)) by {
                        assert(ph(s2, t) is Crit);
                    }
                } else {
                    assert(m.serving != tkn);
                    assert(step(m, t, m));
                    s.model.step(tok, m);
                }
            }
        });
        (cur == tk, cur, Tracked(got))
    }

    /// Takes the lock and its value.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (r: (LockGuard<'_, K, V, P>, V))
        requires
            self.wf(),
        ensures
            r.0.wf(),
            r.0.k() == self.k(),
            P::inv(self.k(), r.1),
    {
        let (tk, Tracked(tok), Ghost(tkn)) = self.take_ticket();
        let tracked mut tok = tok;
        let backoff = Backoff::new();
        let tracked mut held: Option<PointsTo<V>> = None;
        loop
            invariant_except_break
                tok.value().ph == (Ph::Wait { tk: tkn }),
            invariant
                self.wf(),
                tok.id() == self.consts().model,
                tk as int == tkn as int % wrap(),
            ensures
                tok.value().ph is Crit,
                held matches Some(p) && p.id() == self.cell.id() && p.is_init() && P::inv(self.k(), p.value()),
        {
            let (ok, cur, Tracked(got)) = self.poll(tk, Tracked(&mut tok), Ghost(tkn));
            if ok {
                proof {
                    held = got;
                }
                break;
            }
            wait_turn(tk.wrapping_sub(cur), &backoff);
        }
        let tracked mut perm = held.tracked_unwrap();
        let v = self.cell.take(Tracked(&mut perm));
        (LockGuard { lock: self, perm: Tracked(perm), tok: Tracked(tok), bomb: bomb() }, v)
    }

    /// Takes the value out for good, when the lock is being dropped.
    /// `None` if a guard was leaked, since the value went with it.
    pub fn take_inner(&mut self) -> (r: Option<V>)
        requires
            old(self).wf(),
    {
        let tracked inv = self.inv.borrow_mut().tracked_take();
        let tracked mut s = inv.into_inner();
        let nx = self.next.load(Tracked(&s.next));
        if nx == self.serving.load(Tracked(&s.serving)) {
            proof {
                // No ticket outstanding: nobody holds the lock.
                s.model.lemma_inv();
                let m = s.model@;
                lemma_bound(m, model_threads());
                lemma_mod_eq(m.serving as int, m.next as int);
                assert forall|t: nat| t < model_threads() implies !(#[trigger] ph(m, t) is Crit) by {
                    assert(match ph(m, t) {
                        Ph::Idle => true,
                        Ph::Wait { tk } => m.serving <= tk < m.next,
                        Ph::Crit { tk } => tk == m.serving && tk < m.next,
                    });
                }
            }
            let tracked mut perm = s.held.tracked_take();
            let v = self.cell.take(Tracked(&mut perm));
            // Leave a ticket outstanding, so a second call finds the lock
            // held and leaves the empty cell alone.
            self.next.store(Tracked(&mut s.next), nx.wrapping_add(1));
            Some(v)
        } else {
            None
        }
    }
}

impl<'a, K, V, P: LockInv<K, V>> LockGuard<'a, K, V, P> {
    pub closed spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.perm@.id() == self.lock.cell.id()
        &&& self.perm@.mem_contents() == MemContents::<V>::Uninit
        &&& self.tok@.id() == self.lock.consts().model
        &&& self.tok@.value().ph is Crit
    }

    pub closed spec fn k(&self) -> K {
        self.lock.k()
    }

    /// Puts the value back and releases the lock.
    pub fn unlock(self, v: V)
        requires
            self.wf(),
            P::inv(self.k(), v),
    {
        let lock = self.lock;
        let bomb = self.bomb;
        let tracked mut perm = self.perm.get();
        let tracked mut tok = self.tok.get();
        lock.cell.put(Tracked(&mut perm), v);
        open_atomic_invariant!(lock.inv.borrow().tracked_borrow() => s => {
            proof {
                s.model.agree(&tok);
                s.model.lemma_inv();
            }
            let ghost m = s.model@;
            let ghost t = tok.key();
            proof {
                lemma_bound(m, model_threads());
                assert(ph(m, t) is Crit);
                assert(!free(m));
                assert(ticket(ph(m, t)) == Some(m.serving)) by {
                    assert(match ph(m, t) {
                        Ph::Idle => true,
                        Ph::Wait { tk } => m.serving <= tk < m.next,
                        Ph::Crit { tk } => tk == m.serving && tk < m.next,
                    });
                }
                lemma_wrap_inc(m.serving, s.serving@.value);
            }
            lock.serving.fetch_add_wrapping(Tracked(&mut s.serving), 1);
            proof {
                let s2 = St { serving: m.serving + 1, ..go(m, t, Ph::Idle) };
                assert(step(m, t, s2));
                s.model.step(&mut tok, s2);
                // `t` was the only one in.
                assert forall|u: nat| u < model_threads() implies !(#[trigger] ph(s2, u) is Crit) by {
                    if u != t {
                        assert(ph(s2, u) == ph(m, u));
                        if ph(m, u) is Crit {
                            assert(ticket(ph(m, u)) != ticket(ph(m, t)));
                            assert(match ph(m, u) {
                                Ph::Idle => true,
                                Ph::Wait { tk } => m.serving <= tk < m.next,
                                Ph::Crit { tk } => tk == m.serving && tk < m.next,
                            });
                        }
                    }
                }
                s.held = Some(perm);
                s.model.leave(tok);
            }
        });
        defuse(bomb);
    }
}

} // verus!

impl Drop for Bomb {
    fn drop(&mut self) {
        // A guard dropped without `unlock`: the lock would be left without
        // its value.
        std::process::abort();
    }
}

impl<K, V, P: LockInv<K, V>> Drop for Lock<K, V, P> {
    fn drop(&mut self) {
        let _ = self.take_inner();
    }
}
