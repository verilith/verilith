//! A thread blocked on a channel is never stranded: a receiver waiting
//! next to a message, or a sender waiting next to free space, is woken.
//!
//! The model is the blocking and non-blocking send and receive, the
//! `Waiters` lists and the sender/receiver counting of
//! `src/chan_sync.rs`, one step per access to shared state. The queue
//! appears only through its verified spec: a pop takes one message if
//! there is one, a push adds one if there is room. `chan_sync.rs` is
//! verified to follow this model: it can change the model's state (which
//! it holds as a ghost resource, `chan_model::Model`) only by a [`step`].
//!
//! Three things are looser here than a first reading of the code
//! suggests, because the code's accesses are separate atomic steps:
//! a notifier sets one waiter's flag per step ([`pop_all`]); a load of a
//! list's `empty` flag may still say "not empty" just after the last
//! waiter left ([`load_empty`]); and a waiter's re-check may say "maybe"
//! when there is nothing to take, though it never misses something that
//! is there.
//!
//! The two directions are the same protocol with the roles swapped, so the
//! model covers both at once. A *taker* waits for a resource: a receiver
//! waits for messages, a sender for free slots. A *giver* makes one: a
//! sender's push adds a message, a receiver's pop frees a slot. `c` counts
//! what takers can take (messages, or free slots), `alive` counts the
//! handles on the other side (senders, or receivers), and every give is
//! followed by a `notify_one` on the takers' list, every last-handle drop
//! by a `notify_all`. Any thread may act in either role, which covers a
//! thread that holds both ends.
//!
//! Proved, for every fair execution and every taker `r` waiting with no
//! deadline:
//!
//! - [`theorem_resource_taken`]: if `c > 0` (a message is there, or a slot
//!   is free), some taker takes one, or `r` returns, or the other side
//!   disconnects. So `r` is never left asleep next to a message.
//! - [`theorem_disconnect_seen`]: once the other side has disconnected,
//!   `r` returns.
//!
//! The first rests on a counting invariant. While some taker sleeps on the
//! list and the other side is connected, `c` is at most the number of
//! threads that will still take or wake: notifiers that have not run yet,
//! plus takers that are off the list and not asleep. A give adds one to
//! each side; a notification moves its count to the taker it wakes. The
//! interesting case is a notification that lands on a taker that was
//! registered but had not gone to sleep yet (it was about to re-check the
//! queue): that taker then counts as woken, so the notification is not
//! lost, even though it did not wake a sleeper.
//!
//! What this does not prove is that a particular taker gets a message:
//! other takers can win every time, as in crossbeam.
use super::trace::*;
use vstd::prelude::*;

verus! {

pub enum Ph {
    Idle,
    /// Taker: about to read whether the other side is gone
    /// (`senders_gone()` in `try_recv`, `receivers_gone()` in `try_send`).
    TGone { left: nat },
    /// Taker: about to pop (or push); `gone` is what it just read.
    TTake { gone: bool, left: nat },
    /// Taker in `wait_until`: about to lock the list and add itself.
    TReg,
    /// Taker on the list as `tk`, checking `ready()`: first whether the
    /// other side is gone ...
    TReady1 { tk: nat },
    /// ... then whether `c > 0` (the queue's `len()`).
    TReady2 { tk: nat },
    /// `ready()` held: about to take itself off the list (`remove`).
    TRemove { tk: nat },
    /// Asleep until its `notified` flag is set.
    TPark { tk: nat },
    /// Its deadline passed: about to take itself off the list.
    TTimeout { tk: nat },
    /// Timed out after a notifier had already taken it off the list: about
    /// to pass the notification on (`notify_one`'s load of `empty`) ...
    TPass,
    /// ... and `notify`'s critical section.
    TPassPop,
    /// Giver after a give: `notify_one`'s load of `empty` ...
    GNotify,
    /// ... and `notify`'s critical section.
    GNotifyPop,
    /// Giver after dropping the last handle: `notify_all`'s load ...
    GNotifyAll,
    /// ... and `notify(true)`'s critical section, one step per waiter
    /// and one to leave.
    GNotifyAllPop,
}

pub struct Th {
    pub ph: Ph,
    pub timed: bool,
}

pub struct St {
    /// What takers can take: messages for receivers, free slots for senders.
    pub c: nat,
    pub cap: nat,
    /// Handles on the giving side: senders for receivers, receivers for
    /// senders.
    pub alive: nat,
    pub th: Seq<Th>,
    /// The takers' waiter list. The `empty` flag is not a variable of the
    /// model: see [`load_empty`].
    pub list: Set<nat>,
    pub owner: Map<nat, nat>,
    pub notified: Set<nat>,
    pub next_tk: nat,
}

pub open spec fn init(s: St, n: nat) -> bool {
    &&& s.c <= s.cap
    &&& s.th.len() == n
    &&& forall|t: int| 0 <= t < n ==> (#[trigger] s.th[t]).ph == Ph::Idle
    &&& s.list.is_empty()
    &&& s.notified.is_empty()
    &&& s.next_tk == 0
}

pub open spec fn ph(s: St, t: nat) -> Ph {
    s.th[t as int].ph
}

pub open spec fn timed(s: St, t: nat) -> bool {
    s.th[t as int].timed
}

pub open spec fn go(s: St, t: nat, p: Ph) -> St {
    St { th: s.th.update(t as int, Th { ph: p, timed: s.th[t as int].timed }), ..s }
}

/// Thread `t` takes waiter `tk` off the list and sets its flag (the
/// store to `notified` in `notify`), and goes on to phase `p`.
pub open spec fn pops(s: St, t: nat, tk: nat, p: Ph, s2: St) -> bool {
    s.list.contains(tk) && s2 == (St {
        list: s.list.remove(tk),
        notified: s.notified.insert(tk),
        ..go(s, t, p)
    })
}

/// `notify`'s critical section for one waiter: take some waiter off the
/// list and set its flag (or nothing, if the list is empty).
pub open spec fn pop_one(s: St, t: nat, s2: St) -> bool {
    if s.list.is_empty() {
        s2 == go(s, t, Ph::Idle)
    } else {
        exists|tk: nat| #[trigger] pops(s, t, tk, Ph::Idle, s2)
    }
}

/// `notify(true)`'s critical section, one waiter at a time: the flags are
/// set by separate stores, and a waiter may see its own before the next
/// one is set. The section ends when the list is empty.
pub open spec fn pop_all(s: St, t: nat, s2: St) -> bool {
    if s.list.is_empty() {
        s2 == go(s, t, Ph::Idle)
    } else {
        exists|tk: nat| #[trigger] pops(s, t, tk, Ph::GNotifyAllPop, s2)
    }
}

/// A load of a waiter list's `empty` flag by a thread about to notify.
/// The flag is written inside the list's critical sections, after the
/// list itself, so it can lag: it may still say "not empty" just after
/// the last waiter was taken off. It never says "empty" while a waiter is
/// on the list. So a notifier skips the critical section (`done`) only if
/// the list is empty, and may enter it (`pop`) either way.
pub open spec fn load_empty(s: St, t: nat, done: Ph, pop: Ph, s2: St) -> bool {
    s2 == go(s, t, pop) || (s.list.is_empty() && s2 == go(s, t, done))
}

/// One step of thread `t`.
pub open spec fn step(s: St, t: nat, s2: St) -> bool {
    match ph(s, t) {
        Ph::Idle => {
            ||| s2 == s
            // Start a take (`recv*`/`try_recv`, or `send*`/`try_send`).
            ||| exists|b: bool, left: nat|
                s2 == (St { th: s.th.update(t as int, Th { ph: Ph::TGone { left }, timed: b }), ..s })
            // Give (a push, or a pop), holding a handle.
            ||| (s.alive > 0 && s.c < s.cap && s2 == (St { c: s.c + 1, ..go(s, t, Ph::GNotify) }))
            // Clone a handle.
            ||| (s.alive > 0 && s2 == (St { alive: s.alive + 1, ..s }))
            // Drop a handle; the last one wakes every taker.
            ||| (s.alive > 0 && s2 == (St {
                alive: (s.alive - 1) as nat,
                ..go(s, t, if s.alive == 1 { Ph::GNotifyAll } else { Ph::Idle })
            }))
        },
        // `try_send` returns `Disconnected` at once; `try_recv` still pops.
        Ph::TGone { left } => if s.alive == 0 {
            s2 == go(s, t, Ph::TTake { gone: true, left }) || s2 == go(s, t, Ph::Idle)
        } else {
            s2 == go(s, t, Ph::TTake { gone: false, left })
        },
        Ph::TTake { gone, left } => if s.c > 0 {
            s2 == (St { c: (s.c - 1) as nat, ..go(s, t, Ph::Idle) })
        } else if gone {
            s2 == go(s, t, Ph::Idle)
        } else if timed(s, t) && s2 == go(s, t, Ph::Idle) {
            true
        } else if left > 0 {
            s2 == go(s, t, Ph::TGone { left: (left - 1) as nat })
        } else {
            s2 == go(s, t, Ph::TReg)
        },
        Ph::TReg => s2 == (St {
            list: s.list.insert(s.next_tk),
            owner: s.owner.insert(s.next_tk, t),
            next_tk: s.next_tk + 1,
            ..go(s, t, Ph::TReady1 { tk: s.next_tk })
        }),
        Ph::TReady1 { tk } => if s.alive == 0 {
            s2 == go(s, t, Ph::TRemove { tk })
        } else {
            s2 == go(s, t, Ph::TReady2 { tk })
        },
        // The re-check may say "maybe" when there is nothing (it reads
        // one end of the queue exactly and the other possibly stale), but
        // it never misses something that is there.
        Ph::TReady2 { tk } => if s.c > 0 {
            s2 == go(s, t, Ph::TRemove { tk })
        } else {
            s2 == go(s, t, Ph::TPark { tk }) || s2 == go(s, t, Ph::TRemove { tk })
        },
        Ph::TRemove { tk } => s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::TGone { left: 0 }) }),
        Ph::TPark { tk } => if s.notified.contains(tk) {
            s2 == go(s, t, Ph::TGone { left: 0 })
        } else {
            s2 == s || (timed(s, t) && s2 == go(s, t, Ph::TTimeout { tk }))
        },
        Ph::TTimeout { tk } => if s.list.contains(tk) {
            s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Idle) })
        } else {
            s2 == go(s, t, Ph::TPass)
        },
        Ph::TPass => load_empty(s, t, Ph::Idle, Ph::TPassPop, s2),
        Ph::TPassPop => pop_one(s, t, s2),
        Ph::GNotify => load_empty(s, t, Ph::Idle, Ph::GNotifyPop, s2),
        Ph::GNotifyPop => pop_one(s, t, s2),
        Ph::GNotifyAll => load_empty(s, t, Ph::Idle, Ph::GNotifyAllPop, s2),
        Ph::GNotifyAllPop => pop_all(s, t, s2),
    }
}

/// The phase `t` goes on to if its step takes a waiter off the list.
pub open spec fn after_pop(s: St, t: nat) -> Option<Ph> {
    if s.list.is_empty() {
        None
    } else {
        match ph(s, t) {
            Ph::TPassPop | Ph::GNotifyPop => Some(Ph::Idle),
            Ph::GNotifyAllPop => Some(Ph::GNotifyAllPop),
            _ => None,
        }
    }
}

/// The waiter `t`'s step takes off the list.
pub open spec fn popped(s: St, t: nat, s2: St) -> nat {
    choose|x: nat| #[trigger] pops(s, t, x, after_pop(s, t)->Some_0, s2)
}

pub open spec fn run(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat) -> bool {
    &&& init(ex(0), n)
    &&& forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1))
}

/// Inside a blocking (or timed) take: not finished.
pub open spec fn waiting(p: Ph) -> bool {
    match p {
        Ph::TGone { .. } | Ph::TTake { .. } | Ph::TReg | Ph::TReady1 { .. } | Ph::TReady2 { .. }
        | Ph::TRemove { .. } | Ph::TPark { .. } | Ph::TTimeout { .. } => true,
        _ => false,
    }
}

/// The ticket a taker on (or just off) the list holds.
pub open spec fn ticket(p: Ph) -> Option<nat> {
    match p {
        Ph::TReady1 { tk } | Ph::TReady2 { tk } | Ph::TRemove { tk } | Ph::TPark { tk } | Ph::TTimeout { tk } => Some(tk),
        _ => None,
    }
}

/// A taker asleep on the list.
pub open spec fn sleeping(s: St, t: nat) -> bool {
    ph(s, t) is TPark && s.list.contains(ph(s, t)->TPark_tk)
}

/// A thread that will still take or wake: a pending notifier, or a taker
/// that is off the list and has not given up.
pub open spec fn live(s: St, t: nat) -> bool {
    match ph(s, t) {
        Ph::TGone { .. } | Ph::TTake { .. } => true,
        Ph::TReady1 { tk } | Ph::TReady2 { tk } | Ph::TRemove { tk } | Ph::TPark { tk } | Ph::TTimeout { tk } => !s.list.contains(tk),
        Ph::TPass | Ph::TPassPop | Ph::GNotify | Ph::GNotifyPop => true,
        _ => false,
    }
}

/// How many of the first `k` threads are live.
pub open spec fn nlive(s: St, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        nlive(s, (k - 1) as nat) + if live(s, (k - 1) as nat) { 1nat } else { 0nat }
    }
}

pub open spec fn someone_sleeps(s: St, n: nat) -> bool {
    exists|t: nat| t < n && #[trigger] sleeping(s, t)
}

pub open spec fn waking_all(s: St, u: nat) -> bool {
    ph(s, u) is GNotifyAll || ph(s, u) is GNotifyAllPop
}

pub open spec fn inv(s: St, n: nat) -> bool {
    &&& s.th.len() == n
    &&& s.c <= s.cap
    &&& forall|tk: nat| #[trigger] s.list.contains(tk) ==> {
        &&& tk < s.next_tk
        &&& !s.notified.contains(tk)
        &&& s.owner[tk] < n
        &&& ticket(ph(s, s.owner[tk])) == Some(tk)
    }
    &&& forall|tk: nat| #[trigger] s.notified.contains(tk) ==> tk < s.next_tk
    &&& forall|t: nat| t < n ==> match ticket(#[trigger] ph(s, t)) {
        Some(tk) => tk < s.next_tk && s.owner[tk] == t,
        None => true,
    }
    // A taker off the list was notified (unless it took itself off).
    &&& forall|t: nat| t < n && #[trigger] ticket(ph(s, t)) is Some ==> s.list.contains(ticket(ph(s, t))->Some_0) || s.notified.contains(ticket(ph(s, t))->Some_0)
    // Having seen the other side gone, it stays gone.
    &&& forall|t: nat| t < n && #[trigger] ph(s, t) is TTake && ph(s, t)->TTake_gone ==> s.alive == 0
    // Only calls with a deadline time out.
    &&& forall|t: nat| t < n && #[trigger] ph(s, t) is TTimeout ==> timed(s, t)
    // Counting: while someone sleeps and the other side is connected,
    // every unit of `c` has a live thread to take it or wake a taker.
    &&& s.alive > 0 && someone_sleeps(s, n) ==> s.c <= nlive(s, n)
    // Disconnection: once the other side is gone, a taker on the list
    // that might sleep (it saw the other side connected) has a
    // `notify_all` coming.
    &&& s.alive == 0 ==> forall|tk: nat| #[trigger] s.list.contains(tk)
        && (ph(s, s.owner[tk]) is TReady2 || ph(s, s.owner[tk]) is TPark)
        ==> exists|u: nat| u < n && #[trigger] waking_all(s, u)
}

// ---------------------------------------------------------------------
// Counting.

proof fn lemma_nlive_ge(s: St, s2: St, k: nat, a: nat, b: nat)
    requires
        a != b,
        forall|u: nat| u < k && u != a && u != b && #[trigger] live(s, u) ==> live(s2, u),
    ensures
        nlive(s2, k) as int >= nlive(s, k) as int
            + (if a < k { (if live(s2, a) { 1int } else { 0 }) - (if live(s, a) { 1int } else { 0 }) } else { 0 })
            + (if b < k { (if live(s2, b) { 1int } else { 0 }) - (if live(s, b) { 1int } else { 0 }) } else { 0 }),
    decreases k,
{
    if k > 0 {
        lemma_nlive_ge(s, s2, (k - 1) as nat, a, b);
    }
}

proof fn lemma_nlive_pos(s: St, k: nat) -> (t: nat)
    requires
        nlive(s, k) > 0,
    ensures
        t < k,
        live(s, t),
    decreases k,
{
    if live(s, (k - 1) as nat) {
        (k - 1) as nat
    } else {
        lemma_nlive_pos(s, (k - 1) as nat)
    }
}

// ---------------------------------------------------------------------
// The invariant.

pub proof fn lemma_init(s: St, n: nat)
    requires
        init(s, n),
    ensures
        inv(s, n),
{
    assert forall|t: nat| t < n implies #[trigger] ph(s, t) == Ph::Idle by {
        assert(s.th[t as int].ph == Ph::Idle);
    }
}

pub proof fn lemma_step_frame(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.th.len() == n,
        forall|u: nat| u < n && u != t ==> #[trigger] s2.th[u as int] == s.th[u as int],
        timed(s2, t) == timed(s, t) || ph(s, t) == Ph::Idle,
        forall|tk: nat| s.notified.contains(tk) ==> #[trigger] s2.notified.contains(tk),
        forall|tk: nat| #[trigger] s2.list.contains(tk) ==> s.list.contains(tk) || tk >= s.next_tk,
        forall|tk: nat| #[trigger] s2.notified.contains(tk) ==> s.notified.contains(tk) || s.list.contains(tk),
        s2.next_tk >= s.next_tk,
        s2.alive == 0 ==> s.alive <= 1,
        s.alive == 0 ==> s2.alive == 0,
        s2.cap == s.cap,
{
}

pub proof fn lemma_step(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        inv(s2, n),
{
    lemma_step_frame(s, n, t, s2);
    lemma_step_tickets(s, n, t, s2);
    lemma_step_count(s, n, t, s2);
    lemma_step_gone(s, n, t, s2);
}

proof fn lemma_step_tickets(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        forall|tk: nat| #[trigger] s2.list.contains(tk) ==> {
            &&& tk < s2.next_tk
            &&& !s2.notified.contains(tk)
            &&& s2.owner[tk] < n
            &&& ticket(ph(s2, s2.owner[tk])) == Some(tk)
        },
        forall|tk: nat| #[trigger] s2.notified.contains(tk) ==> tk < s2.next_tk,
        forall|t: nat| t < n ==> match ticket(#[trigger] ph(s2, t)) {
            Some(tk) => tk < s2.next_tk && s2.owner[tk] == t,
            None => true,
        },
        forall|t: nat| t < n && #[trigger] ticket(ph(s2, t)) is Some ==> s2.list.contains(ticket(ph(s2, t))->Some_0) || s2.notified.contains(ticket(ph(s2, t))->Some_0),
        forall|t: nat| t < n && #[trigger] ph(s2, t) is TTake && ph(s2, t)->TTake_gone ==> s2.alive == 0,
        forall|t: nat| t < n && #[trigger] ph(s2, t) is TTimeout ==> timed(s2, t),
{
    lemma_step_frame(s, n, t, s2);
    assert forall|tk: nat| #[trigger] s2.list.contains(tk) implies {
        &&& tk < s2.next_tk
        &&& !s2.notified.contains(tk)
        &&& s2.owner[tk] < n
        &&& ticket(ph(s2, s2.owner[tk])) == Some(tk)
    } by {
        if s.list.contains(tk) {
            let o = s.owner[tk];
            if o == t {
                assert(ticket(ph(s, t)) == Some(tk));
            }
            if after_pop(s, t) is Some {
                let x = popped(s, t, s2);
                assert(pops(s, t, x, after_pop(s, t)->Some_0, s2));
                assert(x != tk);
            }
        }
    }
    assert forall|t1: nat| t1 < n implies match ticket(#[trigger] ph(s2, t1)) {
        Some(tk) => tk < s2.next_tk && s2.owner[tk] == t1,
        None => true,
    } by {
        if t1 != t {
            assert(ph(s2, t1) == ph(s, t1));
            if let Some(tk) = ticket(ph(s, t1)) {
                if ph(s, t) is TReg {
                    assert(tk != s.next_tk);
                }
            }
        }
    }
    assert forall|t1: nat| t1 < n && #[trigger] ph(s2, t1) is TTake && ph(s2, t1)->TTake_gone implies s2.alive == 0 by {
        if t1 != t {
            assert(ph(s2, t1) == ph(s, t1));
        }
    }
    assert forall|t1: nat| t1 < n && #[trigger] ph(s2, t1) is TTimeout implies timed(s2, t1) by {
        if t1 != t {
            assert(ph(s2, t1) == ph(s, t1));
            assert(s2.th[t1 as int] == s.th[t1 as int]);
        }
    }
    assert forall|t1: nat| t1 < n && #[trigger] ticket(ph(s2, t1)) is Some implies s2.list.contains(ticket(ph(s2, t1))->Some_0) || s2.notified.contains(ticket(ph(s2, t1))->Some_0) by {
        let tk = ticket(ph(s2, t1))->Some_0;
        if t1 == t {
            if !(ph(s, t) is TReg) {
                assert(ticket(ph(s, t)) == Some(tk));
            }
        } else {
            assert(ph(s2, t1) == ph(s, t1));
            if s.list.contains(tk) && !s2.list.contains(tk) {
                // Only a notifier or the sleeper itself takes it off.
                if ph(s, t) is TRemove || ph(s, t) is TTimeout {
                    assert(ticket(ph(s, t)) == Some(tk));
                    assert(s.owner[tk] == t);
                    assert(false);
                }
            }
        }
    }
}

proof fn lemma_step_count(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.alive > 0 && someone_sleeps(s2, n) ==> s2.c <= nlive(s2, n),
{
    lemma_step_frame(s, n, t, s2);
    if s2.alive > 0 && someone_sleeps(s2, n) {
        let z = choose|z: nat| z < n && #[trigger] sleeping(s2, z);
        // Did someone sleep before? A new sleeper parks only on c == 0.
        if !sleeping(s, z) {
            if z == t {
                assert(ph(s, t) is TReady2);
                assert(s2.c == 0);
                return;
            } else {
                assert(ph(s2, z) == ph(s, z));
                assert(s.list.contains(ph(s, z)->TPark_tk) || ph(s2, z)->TPark_tk >= s.next_tk);
                assert(false);
            }
        }
        assert(someone_sleeps(s, n));
        assert(s.alive > 0);
        assert(s.c <= nlive(s, n));
        // Every live thread other than `t` and the owner of a ticket that
        // `t` took off the list stays live; those two are accounted for.
        let o: nat = if after_pop(s, t) is Some {
            s.owner[popped(s, t, s2)]
        } else {
            if t == 0 { 1 } else { 0 }
        };
        assert(o != t) by {
            if after_pop(s, t) is Some {
                let x = popped(s, t, s2);
                assert(pops(s, t, x, after_pop(s, t)->Some_0, s2));
                assert(ticket(ph(s, s.owner[x])) == Some(x));
            }
        }
        assert forall|u: nat| u < n && u != t && u != o && #[trigger] live(s, u) implies live(s2, u) by {
            assert(ph(s2, u) == ph(s, u));
            if let Some(tk) = ticket(ph(s, u)) {
                if s2.list.contains(tk) {
                    assert(s.list.contains(tk) || tk >= s.next_tk);
                }
            }
        };
        lemma_nlive_ge(s, s2, n, t, o);
        if after_pop(s, t) is Some {
            let x = popped(s, t, s2);
            assert(pops(s, t, x, after_pop(s, t)->Some_0, s2));
            assert(o == s.owner[x]);
            assert(ticket(ph(s, o)) == Some(x));
            assert(!live(s, o));
            assert(ph(s2, o) == ph(s, o));
            assert(live(s2, o));
        }
        match ph(s, t) {
            Ph::TTake { gone, left } => {
                if s.c == 0 {
                    assert(s2.c == 0);
                }
            },
            Ph::TReady2 { tk } => {},
            Ph::TRemove { tk } => {},
            Ph::TTimeout { tk } => {},
            Ph::GNotify | Ph::TPass => {
                // It skips the critical section only if the list is empty,
                // and `z` is on it.
                let zt = ph(s, z)->TPark_tk;
                assert(s.list.contains(zt));
            },
            _ => {},
        }
    }
}

proof fn lemma_step_gone(s: St, n: nat, t: nat, s2: St)
    requires
        inv(s, n),
        t < n,
        step(s, t, s2),
    ensures
        s2.alive == 0 ==> forall|tk: nat| #[trigger] s2.list.contains(tk)
            && (ph(s2, s2.owner[tk]) is TReady2 || ph(s2, s2.owner[tk]) is TPark)
            ==> exists|u: nat| u < n && #[trigger] waking_all(s2, u),
{
    lemma_step_frame(s, n, t, s2);
    lemma_step_tickets(s, n, t, s2);
    if s2.alive == 0 {
        assert forall|tk: nat| #[trigger] s2.list.contains(tk)
            && (ph(s2, s2.owner[tk]) is TReady2 || ph(s2, s2.owner[tk]) is TPark)
            implies exists|u: nat| u < n && #[trigger] waking_all(s2, u) by {
            if waking_all(s2, t) {
            } else if s.alive == 1 && s2.alive == 0 {
                // The last drop sends the dropper to `notify_all`.
                assert(ph(s, t) is Idle);
                assert(ph(s2, t) is GNotifyAll);
                assert(waking_all(s2, t));
            } else {
                assert(s.alive == 0);
                assert(s.list.contains(tk) || tk >= s.next_tk);
                assert(s.list.contains(tk));
                let o = s2.owner[tk];
                assert(s.owner[tk] == o);
                if o == t {
                    // `t` moved onto `TReady2`/`TPark` from `TReady1`
                    // (impossible with the other side gone) or `TReady2`.
                    assert(ph(s, t) is TReady2 || ph(s, t) is TPark);
                } else {
                    assert(ph(s2, o) == ph(s, o));
                }
                let u = choose|u: nat| u < n && #[trigger] waking_all(s, u);
                if u == t {
                    // It leaves `notify_all` only with the list empty.
                    if after_pop(s, t) is Some {
                        assert(pops(s, t, popped(s, t, s2), Ph::GNotifyAllPop, s2));
                    }
                    assert(waking_all(s2, t));
                } else {
                    assert(ph(s2, u) == ph(s, u));
                    assert(waking_all(s2, u));
                }
            }
        }
    }
}

pub proof fn lemma_inv(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(i), n),
    decreases i,
{
    if i == 0 {
        lemma_init(ex(0), n);
    } else {
        lemma_inv(ex, sched, n, (i - 1) as nat);
        assert(sched((i - 1) as nat) < n && step(ex((i - 1) as nat), sched((i - 1) as nat), ex(i)));
        lemma_step(ex((i - 1) as nat), n, sched((i - 1) as nat), ex(i));
    }
}

proof fn lemma_at(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, m: nat)
    requires
        run(ex, sched, n),
    ensures
        inv(ex(m), n),
        inv(ex(m + 1), n),
        sched(m) < n,
        step(ex(m), sched(m), ex(m + 1)),
        ex(m + 1).th.len() == n,
        forall|u: nat| u < n && u != sched(m) ==> #[trigger] ex(m + 1).th[u as int] == ex(m).th[u as int],
        timed(ex(m + 1), sched(m)) == timed(ex(m), sched(m)) || ph(ex(m), sched(m)) == Ph::Idle,
        forall|tk: nat| ex(m).notified.contains(tk) ==> #[trigger] ex(m + 1).notified.contains(tk),
        forall|tk: nat| #[trigger] ex(m + 1).list.contains(tk) ==> ex(m).list.contains(tk) || tk >= ex(m).next_tk,
        ex(m).alive == 0 ==> ex(m + 1).alive == 0,
{
    lemma_inv(ex, sched, n, m);
    lemma_inv(ex, sched, n, m + 1);
    assert(sched(m) < n && step(ex(m), sched(m), ex(m + 1)));
    lemma_step_frame(ex(m), n, sched(m), ex(m + 1));
}

proof fn lemma_until_step(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, t: nat, j: nat) -> (k: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        t < n,
    ensures
        k >= j,
        sched(k) == t,
        ex(k).th[t as int] == ex(j).th[t as int],
{
    let k = lemma_next_step(sched, n, t, j);
    let f = |m: nat| ex(m).th[t as int];
    assert forall|m: nat| j <= m < k && #[trigger] sched(m) != t implies f(m + 1) == f(m) by {
        lemma_at(ex, sched, n, m);
    }
    lemma_frame(sched, f, t, j, k);
    k
}

proof fn lemma_off_list_stays(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, tk: nat, j: nat, k: nat)
    requires
        run(ex, sched, n),
        j <= k,
        !ex(j).list.contains(tk),
        tk < ex(j).next_tk,
    ensures
        !ex(k).list.contains(tk),
        tk < ex(k).next_tk,
    decreases k - j,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        lemma_step_frame(ex(j), n, sched(j), ex(j + 1));
        lemma_off_list_stays(ex, sched, n, tk, j + 1, k);
    }
}

// ---------------------------------------------------------------------
// Theorem A: a resource next to a waiting taker is taken.

/// A take happens at step `j`.
pub open spec fn took(ex: spec_fn(nat) -> St, j: nat) -> bool {
    ex(j + 1).c < ex(j).c
}

/// The refuted hypothesis: from `i` on, nothing is taken, `r` keeps
/// waiting, and the other side stays connected.
pub open spec fn stuck(ex: spec_fn(nat) -> St, n: nat, i: nat, r: nat) -> bool {
    forall|j: nat| j >= i ==> !took(ex, j) && waiting(#[trigger] ph(ex(j), r)) && ex(j).alive > 0
}

/// The hypotheses every lemma below works under.
pub open spec fn ctx(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat) -> bool {
    &&& run(ex, sched, n)
    &&& fair(sched, n)
    &&& stuck(ex, n, i, r)
    &&& ex(i).c > 0
    &&& r < n
}

proof fn lemma_c_pos(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat)
    requires
        ctx(ex, sched, n, i, r),
        j >= i,
    ensures
        ex(j).c > 0,
        ex(j).alive > 0,
        waiting(ph(ex(j), r)),
    decreases j - i,
{
    assert(!took(ex, j) && waiting(ph(ex(j), r)) && ex(j).alive > 0);
    if j > i {
        lemma_c_pos(ex, sched, n, i, r, (j - 1) as nat);
        assert(!took(ex, (j - 1) as nat) && waiting(ph(ex((j - 1) as nat), r)));
    }
}

/// A taker that is not asleep (or asleep but already notified) and not
/// timing out takes within a few of its own steps: the other side stays
/// connected and `c` stays positive.
pub open spec fn active(s: St, t: nat) -> bool {
    match ph(s, t) {
        Ph::TGone { .. } | Ph::TTake { .. } | Ph::TReg | Ph::TReady1 { .. } | Ph::TReady2 { .. } | Ph::TRemove { .. } => true,
        Ph::TPark { tk } => s.notified.contains(tk),
        _ => false,
    }
}

pub open spec fn self_fuel(p: Ph) -> nat {
    match p {
        Ph::TTake { .. } => 0,
        Ph::TGone { .. } => 1,
        Ph::TRemove { .. } | Ph::TPark { .. } => 2,
        Ph::TReady2 { .. } => 3,
        Ph::TReady1 { .. } => 4,
        _ => 5,
    }
}

proof fn lemma_self(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, t: nat, j: nat)
    requires
        ctx(ex, sched, n, i, r),
        t < n,
        j >= i,
        active(ex(j), t),
    ensures
        false,
    decreases self_fuel(ph(ex(j), t)),
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_at(ex, sched, n, k);
    lemma_c_pos(ex, sched, n, i, r, k);
    lemma_notified_stays(ex, sched, n, j, k);
    let s = ex(k);
    assert(ph(s, t) == ph(ex(j), t));
    assert(!took(ex, k));
    lemma_self(ex, sched, n, i, r, t, k + 1);
}

proof fn lemma_notified_stays(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, j: nat, k: nat)
    requires
        run(ex, sched, n),
        j <= k,
    ensures
        forall|tk: nat| ex(j).notified.contains(tk) ==> #[trigger] ex(k).notified.contains(tk),
    decreases k - j,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        lemma_notified_stays(ex, sched, n, j + 1, k);
    }
}

/// Under `stuck`, `r` asleep on the list stays asleep on it.
proof fn lemma_sleeping_until(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat, k: nat)
    requires
        ctx(ex, sched, n, i, r),
        i <= j <= k,
        sleeping(ex(j), r),
        !timed(ex(j), r),
    ensures
        sleeping(ex(k), r),
        !timed(ex(k), r),
        ph(ex(k), r) == ph(ex(j), r),
    decreases k - j,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        let tk = ph(ex(j), r)->TPark_tk;
        if sched(j) == r {
            assert(!ex(j).notified.contains(tk));
            assert(ex(j + 1) == ex(j));
        }
        assert(ph(ex(j + 1), r) == ph(ex(j), r));
        if !ex(j + 1).list.contains(tk) {
            assert(ex(j + 1).notified.contains(tk));
            assert(active(ex(j + 1), r));
            lemma_self(ex, sched, n, i, r, r, j + 1);
        }
        lemma_sleeping_until(ex, sched, n, i, r, j + 1, k);
    }
}

/// Threads holding a ticket that is on the list.
pub open spec fn listed(s: St) -> spec_fn(nat) -> bool {
    |u: nat| match ticket(ph(s, u)) {
        Some(tk) => s.list.contains(tk),
        None => false,
    }
}

pub open spec fn cnt(f: spec_fn(nat) -> bool, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        0
    } else {
        cnt(f, (k - 1) as nat) + if f((k - 1) as nat) { 1nat } else { 0nat }
    }
}

proof fn lemma_cnt_le(f: spec_fn(nat) -> bool, g: spec_fn(nat) -> bool, k: nat, o: nat)
    requires
        forall|u: nat| u < k && #[trigger] g(u) ==> f(u),
    ensures
        cnt(g, k) <= cnt(f, k),
        o < k && f(o) && !g(o) ==> cnt(g, k) < cnt(f, k),
    decreases k,
{
    if k > 0 {
        lemma_cnt_le(f, g, (k - 1) as nat, o);
    }
}

/// Under `stuck`, nobody joins the list after `i` (a joiner would take).
proof fn lemma_listed_shrinks(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, m: nat)
    requires
        ctx(ex, sched, n, i, r),
        m >= i,
    ensures
        forall|u: nat| u < n && #[trigger] listed(ex(m + 1))(u) ==> listed(ex(m))(u),
{
    lemma_at(ex, sched, n, m);
    let t = sched(m);
    if ph(ex(m), t) is TReg {
        lemma_self(ex, sched, n, i, r, t, m);
    }
    assert forall|u: nat| u < n && #[trigger] listed(ex(m + 1))(u) implies listed(ex(m))(u) by {
        let tk = ticket(ph(ex(m + 1), u))->Some_0;
        assert(ex(m + 1).list.contains(tk));
        assert(ex(m).list.contains(tk) || tk >= ex(m).next_tk);
        if u == t {
            assert(ticket(ph(ex(m), t)) == Some(tk));
        } else {
            assert(ph(ex(m + 1), u) == ph(ex(m), u));
        }
    }
}

proof fn lemma_listed_until(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat, k: nat)
    requires
        ctx(ex, sched, n, i, r),
        i <= j <= k,
    ensures
        cnt(listed(ex(k)), n) <= cnt(listed(ex(j)), n),
    decreases k - j,
{
    if j < k {
        lemma_listed_until(ex, sched, n, i, r, j + 1, k);
        lemma_listed_shrinks(ex, sched, n, i, r, j);
        lemma_cnt_le(listed(ex(j)), listed(ex(j + 1)), n, 0);
    }
}

/// A notifier that has not run yet, or a timed-out taker that will pass a
/// notification on.
pub open spec fn notifier(s: St, t: nat) -> bool {
    match ph(s, t) {
        Ph::TPass | Ph::TPassPop | Ph::GNotify | Ph::GNotifyPop => true,
        Ph::TTimeout { tk } => !s.list.contains(tk),
        _ => false,
    }
}

pub open spec fn notify_fuel(p: Ph) -> nat {
    match p {
        Ph::TPassPop | Ph::GNotifyPop => 0,
        Ph::TPass | Ph::GNotify => 1,
        _ => 2,
    }
}

/// Under `stuck`, a pending notifier wakes a taker that then takes, or
/// hands the notification to a timed-out taker that passes it on; each
/// hand-over takes a ticket off the list, which nobody joins any more.
proof fn lemma_notifier(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, t: nat, j: nat)
    requires
        ctx(ex, sched, n, i, r),
        t < n,
        j >= i,
        notifier(ex(j), t),
        sleeping(ex(j), r),
        !timed(ex(j), r),
    ensures
        false,
    decreases cnt(listed(ex(j)), n), notify_fuel(ph(ex(j), t)),
{
    let k = lemma_until_step(ex, sched, n, t, j);
    lemma_sleeping_until(ex, sched, n, i, r, j, k);
    lemma_listed_until(ex, sched, n, i, r, j, k);
    lemma_at(ex, sched, n, k);
    let s = ex(k);
    let s2 = ex(k + 1);
    assert(ph(s, t) == ph(ex(j), t));
    assert(t != r);
    let rt = ph(s, r)->TPark_tk;
    assert(s.list.contains(rt));
    lemma_inv(ex, sched, n, j);
    if let Ph::TTimeout { tk } = ph(s, t) {
        assert(ticket(ph(ex(j), t)) == Some(tk));
        assert(!ex(j).list.contains(tk));
        assert(tk < ex(j).next_tk);
        lemma_off_list_stays(ex, sched, n, tk, j, k);
    }
    lemma_listed_shrinks(ex, sched, n, i, r, k);
    lemma_cnt_le(listed(s), listed(s2), n, 0);
    if ph(s, t) is TPassPop || ph(s, t) is GNotifyPop {
        let x = popped(s, t, s2);
        assert(pops(s, t, x, Ph::Idle, s2));
        let o = s.owner[x];
        assert(ticket(ph(s, o)) == Some(x));
        assert(o != t);
        assert(ph(s2, o) == ph(s, o));
        assert(listed(s)(o) && !listed(s2)(o));
        lemma_cnt_le(listed(s), listed(s2), n, o);
        lemma_c_pos(ex, sched, n, i, r, k + 1);
        if active(s2, o) {
            lemma_self(ex, sched, n, i, r, o, k + 1);
        }
        assert(ph(s, o) is TTimeout);
        assert(notifier(s2, o));
        if o == r {
            assert(false);
        }
        lemma_sleeping_until(ex, sched, n, i, r, j, k);
        assert(ph(s2, r) == ph(s, r));
        assert(s2.list.contains(rt));
        lemma_notifier(ex, sched, n, i, r, o, k + 1);
    } else {
        assert(ph(s2, r) == ph(s, r));
        assert(s2.list.contains(rt));
        assert(notifier(s2, t));
        lemma_notifier(ex, sched, n, i, r, t, k + 1);
    }
}

/// Under `stuck`, `r` cannot be asleep: the counting invariant gives a
/// live thread, which either takes or is a notifier.
proof fn lemma_sleeper(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat)
    requires
        ctx(ex, sched, n, i, r),
        j >= i,
        sleeping(ex(j), r),
        !timed(ex(j), r),
    ensures
        false,
{
    lemma_at(ex, sched, n, j);
    lemma_c_pos(ex, sched, n, i, r, j);
    let s = ex(j);
    assert(someone_sleeps(s, n));
    let t = lemma_nlive_pos(s, n);
    if active(s, t) {
        lemma_self(ex, sched, n, i, r, t, j);
    }
    if let Ph::TPark { tk } = ph(s, t) {
        assert(s.notified.contains(tk));
    }
    assert(notifier(s, t));
    lemma_notifier(ex, sched, n, i, r, t, j);
}

/// No stranding next to a resource: in a fair execution, if `c > 0` while
/// a taker `r` waits without a deadline, then later some taker takes, or
/// `r` returns, or the other side disconnects.
pub proof fn theorem_resource_taken(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        r < n,
        waiting(ph(ex(i), r)),
        !timed(ex(i), r),
        ex(i).c > 0,
    ensures
        exists|j: nat| j >= i && (took(ex, j) || !waiting(#[trigger] ph(ex(j), r)) || ex(j).alive == 0),
{
    if !exists|j: nat| j >= i && (took(ex, j) || !waiting(#[trigger] ph(ex(j), r)) || ex(j).alive == 0) {
        assert(stuck(ex, n, i, r));
        lemma_at(ex, sched, n, i);
        let s = ex(i);
        if active(s, r) {
            lemma_self(ex, sched, n, i, r, r, i);
        }
        if let Ph::TPark { tk } = ph(s, r) {
            assert(sleeping(s, r));
            lemma_sleeper(ex, sched, n, i, r, i);
        }
        // `TTimeout` needs a deadline.
        assert(ph(s, r) is TTimeout);
        assert(timed(s, r));
    }
}

// ---------------------------------------------------------------------
// Theorem B: a disconnection is seen.

/// The refuted hypothesis: the other side is gone from `i` on (it cannot
/// come back) and `r` keeps waiting.
pub open spec fn ctx_b(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat) -> bool {
    &&& run(ex, sched, n)
    &&& fair(sched, n)
    &&& r < n
    &&& ex(i).alive == 0
    &&& forall|j: nat| j >= i ==> waiting(#[trigger] ph(ex(j), r)) && !timed(ex(j), r)
}

proof fn lemma_b_gone(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat)
    requires
        ctx_b(ex, sched, n, i, r),
        j >= i,
    ensures
        ex(j).alive == 0,
        waiting(ph(ex(j), r)),
        !timed(ex(j), r),
    decreases j - i,
{
    assert(waiting(ph(ex(j), r)) && !timed(ex(j), r));
    if j > i {
        lemma_b_gone(ex, sched, n, i, r, (j - 1) as nat);
        lemma_at(ex, sched, n, (j - 1) as nat);
    }
}

pub open spec fn b_fuel(p: Ph) -> nat {
    match p {
        Ph::TTake { gone, .. } => if gone { 0 } else { 5 },
        Ph::TGone { .. } => 1,
        Ph::TRemove { .. } | Ph::TPark { .. } => 2,
        Ph::TReady1 { .. } => 3,
        Ph::TReady2 { .. } | Ph::TReg => 4,
        _ => 6,
    }
}

/// `r`, not asleep (or already notified), sees the other side gone and
/// returns within a few of its own steps.
proof fn lemma_b_self(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat)
    requires
        ctx_b(ex, sched, n, i, r),
        j >= i,
        active(ex(j), r),
    ensures
        false,
    decreases b_fuel(ph(ex(j), r)), 0nat, 0nat, 0nat,
{
    let k = lemma_until_step(ex, sched, n, r, j);
    lemma_at(ex, sched, n, k);
    lemma_b_gone(ex, sched, n, i, r, k);
    lemma_b_gone(ex, sched, n, i, r, k + 1);
    lemma_notified_stays(ex, sched, n, j, k);
    let s = ex(k);
    let s2 = ex(k + 1);
    assert(ph(s, r) == ph(ex(j), r));
    if let Ph::TReady2 { tk } = ph(s, r) {
        assert(ticket(ph(s, r)) == Some(tk));
        if ph(s2, r) is TPark {
            if s.list.contains(tk) {
                assert(sleeping(s2, r));
                assert(s2.owner[tk] == r);
                let u = choose|u: nat| u < n && #[trigger] waking_all(s2, u);
                lemma_b_wake(ex, sched, n, i, r, u, k + 1);
            }
            assert(s.notified.contains(tk));
        }
    }
    if let Ph::TTake { gone, left } = ph(s, r) {
        if gone {
            assert(!waiting(ph(s2, r)));
        }
    }
    lemma_b_self(ex, sched, n, i, r, k + 1);
}

/// `r` asleep on the list stays asleep on it until `k`, unless it is woken.
proof fn lemma_b_sleeping_until(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat, k: nat)
    requires
        ctx_b(ex, sched, n, i, r),
        i <= j <= k,
        sleeping(ex(j), r),
    ensures
        sleeping(ex(k), r),
        ph(ex(k), r) == ph(ex(j), r),
    decreases 2nat, 1nat, k - j, 0nat,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        lemma_b_gone(ex, sched, n, i, r, j);
        let tk = ph(ex(j), r)->TPark_tk;
        if sched(j) == r {
            assert(!ex(j).notified.contains(tk));
            assert(ex(j + 1) == ex(j));
        }
        assert(ph(ex(j + 1), r) == ph(ex(j), r));
        if !ex(j + 1).list.contains(tk) {
            assert(ticket(ph(ex(j + 1), r)) == Some(tk));
            assert(ex(j + 1).notified.contains(tk));
            assert(active(ex(j + 1), r));
            lemma_b_self(ex, sched, n, i, r, j + 1);
        }
        lemma_b_sleeping_until(ex, sched, n, i, r, j + 1, k);
    }
}

/// With the other side gone, the threads that are on the list or may
/// still join it: a call registers only if it read the other side
/// connected, and no call can read that any more.
pub open spec fn pend(s: St) -> spec_fn(nat) -> bool {
    |u: nat| listed(s)(u) || ph(s, u) is TReg || (ph(s, u) is TTake && !ph(s, u)->TTake_gone)
}

proof fn lemma_pend_shrinks(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, m: nat)
    requires
        run(ex, sched, n),
        ex(m).alive == 0,
    ensures
        forall|u: nat| u < n && #[trigger] pend(ex(m + 1))(u) ==> pend(ex(m))(u),
{
    lemma_at(ex, sched, n, m);
    let t = sched(m);
    let s = ex(m);
    let s2 = ex(m + 1);
    assert forall|u: nat| u < n && #[trigger] pend(s2)(u) implies pend(s)(u) by {
        if u != t {
            assert(ph(s2, u) == ph(s, u));
        }
        if let Some(tk) = ticket(ph(s2, u)) {
            if s2.list.contains(tk) {
                assert(s.list.contains(tk) || tk >= s.next_tk);
                if u == t && !(ph(s, t) is TReg) {
                    assert(ticket(ph(s, t)) == Some(tk));
                }
            }
        }
    }
}

proof fn lemma_pend_until(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, j: nat, k: nat)
    requires
        run(ex, sched, n),
        j <= k,
        ex(j).alive == 0,
    ensures
        cnt(pend(ex(k)), n) <= cnt(pend(ex(j)), n),
        ex(k).alive == 0,
    decreases k - j,
{
    if j < k {
        lemma_at(ex, sched, n, j);
        lemma_pend_until(ex, sched, n, j + 1, k);
        lemma_pend_shrinks(ex, sched, n, j);
        lemma_cnt_le(pend(ex(j)), pend(ex(j + 1)), n, 0);
    }
}

/// The last drop's `notify_all` wakes `r`: each of its steps takes a
/// waiter off the list, and only boundedly many threads can still join.
proof fn lemma_b_wake(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, u: nat, j: nat)
    requires
        ctx_b(ex, sched, n, i, r),
        u < n,
        j >= i,
        sleeping(ex(j), r),
        waking_all(ex(j), u),
    ensures
        false,
    decreases 2nat, 2nat, cnt(pend(ex(j)), n), (if ph(ex(j), u) is GNotifyAll { 1nat } else { 0nat }),
{
    let k = lemma_until_step(ex, sched, n, u, j);
    lemma_b_sleeping_until(ex, sched, n, i, r, j, k);
    lemma_at(ex, sched, n, k);
    lemma_b_gone(ex, sched, n, i, r, j);
    lemma_b_gone(ex, sched, n, i, r, k);
    lemma_b_gone(ex, sched, n, i, r, k + 1);
    lemma_pend_until(ex, sched, n, j, k);
    lemma_pend_shrinks(ex, sched, n, k);
    let s = ex(k);
    let s2 = ex(k + 1);
    lemma_cnt_le(pend(s), pend(s2), n, 0);
    assert(ph(s, u) == ph(ex(j), u));
    assert(u != r);
    let tk = ph(s, r)->TPark_tk;
    assert(s.list.contains(tk));
    assert(ph(s2, r) == ph(s, r));
    if ph(s, u) is GNotifyAll {
        assert(waking_all(s2, u));
        assert(s2.list.contains(tk));
        lemma_b_wake(ex, sched, n, i, r, u, k + 1);
    } else {
        let x = popped(s, u, s2);
        assert(pops(s, u, x, Ph::GNotifyAllPop, s2));
        if x == tk {
            assert(s2.notified.contains(tk));
            assert(active(s2, r));
            lemma_b_self(ex, sched, n, i, r, k + 1);
        } else {
            let o = s.owner[x];
            assert(ticket(ph(s, o)) == Some(x));
            assert(o != u);
            assert(ph(s2, o) == ph(s, o));
            assert(pend(s)(o) && !pend(s2)(o));
            lemma_cnt_le(pend(s), pend(s2), n, o);
            assert(s2.list.contains(tk));
            assert(waking_all(s2, u));
            lemma_b_wake(ex, sched, n, i, r, u, k + 1);
        }
    }
}

/// Disconnection is seen: in a fair execution, once the other side has
/// dropped every handle, a taker `r` waiting without a deadline returns.
pub proof fn theorem_disconnect_seen(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat)
    requires
        run(ex, sched, n),
        fair(sched, n),
        r < n,
        waiting(ph(ex(i), r)),
        !timed(ex(i), r),
        ex(i).alive == 0,
    ensures
        exists|j: nat| j >= i && !waiting(#[trigger] ph(ex(j), r)),
{
    if !exists|j: nat| j >= i && !waiting(#[trigger] ph(ex(j), r)) {
        // Deadlines never change in the middle of a call.
        assert forall|j: nat| j >= i implies waiting(#[trigger] ph(ex(j), r)) && !timed(ex(j), r) by {
            lemma_untimed_stays(ex, sched, n, i, r, j);
        }
        assert(ctx_b(ex, sched, n, i, r));
        lemma_at(ex, sched, n, i);
        let s = ex(i);
        if active(s, r) {
            lemma_b_self(ex, sched, n, i, r, i);
        }
        if let Ph::TPark { tk } = ph(s, r) {
            assert(sleeping(s, r));
            assert(ticket(ph(s, r)) == Some(tk));
            assert(s.owner[tk] == r);
            let u = choose|u: nat| u < n && #[trigger] waking_all(s, u);
            lemma_b_wake(ex, sched, n, i, r, u, i);
        }
        assert(ph(s, r) is TTimeout);
    }
}

proof fn lemma_untimed_stays(ex: spec_fn(nat) -> St, sched: spec_fn(nat) -> nat, n: nat, i: nat, r: nat, j: nat)
    requires
        run(ex, sched, n),
        r < n,
        i <= j,
        !timed(ex(i), r),
        forall|m: nat| m >= i ==> waiting(#[trigger] ph(ex(m), r)),
    ensures
        !timed(ex(j), r),
    decreases j - i,
{
    if j > i {
        lemma_untimed_stays(ex, sched, n, i, r, (j - 1) as nat);
        lemma_at(ex, sched, n, (j - 1) as nat);
        assert(waiting(ph(ex((j - 1) as nat), r)));
    }
}

} // verus!

verus! {

/// The hypotheses are satisfiable: with every thread idle forever under a
/// round-robin schedule, `run` and `fair` both hold.
pub proof fn lemma_nonvacuous(s0: St, n: nat)
    requires
        init(s0, n),
        n > 0,
    ensures
        run(|i: nat| s0, |i: nat| i % n, n),
        fair(|i: nat| i % n, n),
{
    lemma_round_robin_fair(n);
    let ex = |i: nat| s0;
    let sched = |i: nat| i % n;
    assert forall|i: nat| #[trigger] sched(i) < n && step(ex(i), sched(i), ex(i + 1)) by {
        let t = i % n;
        assert(s0.th[t as int].ph == Ph::Idle);
    }
}

} // verus!
