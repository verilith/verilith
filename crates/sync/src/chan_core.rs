//! The channel's blocking protocol as a verified transition function.
//!
//! The progress theorems in `src/progress/channel.rs` are about a model.
//! This module is the control-flow half of the proof that the code in
//! `src/chan_sync.rs` follows that model.
//!
//! A thread in a channel call is at a [`Pc`]: the next access it will make
//! to shared state. `chan_sync.rs` runs a call as a loop that makes the
//! access for its `Pc` and asks [`next`] where to go, with what the access
//! read. [`theorem_next_refines`] proves that every such move is a step of
//! the model, given that the access read and wrote what [`reads`] and
//! [`writes`] say. [`theorem_notify_refines`] proves the same for
//! `notify_one` and `notify_all`, one waiter per step.
//!
//! `chan_sync.rs` is the other half: at each access it proves `reads` and
//! `writes` from the channel's invariant, applies the theorem here, and
//! advances the model's ghost state by the step it yields. It also covers
//! the steps this module does not (a give, and cloning and dropping a
//! handle).
#[allow(unused_imports)]
use crate::progress::channel::*;
use vstd::prelude::*;

verus! {

/// How a call ended.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum End {
    /// It took a message (or a free slot).
    Taken,
    /// The other side is gone (and, for a receiver, the queue is empty).
    Disconnected,
    /// A `try_` call found nothing to take.
    WouldBlock,
    /// The deadline passed.
    TimedOut,
}

/// The next access to shared state a thread in a take will make.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Pc {
    /// Read whether the other side is gone.
    Gone,
    /// Pop (a receiver) or push (a sender); `gone` is what `Gone` read.
    Take { gone: bool },
    /// Lock the waiter list and add this thread.
    Reg,
    /// On the list: re-check whether the other side is gone ...
    Ready1,
    /// ... then whether there is something to take.
    Ready2,
    /// The re-check found something: leave the list.
    Remove,
    /// Read this waiter's `notified` flag; sleep if it is clear.
    Park,
    /// The deadline passed: leave the list, if still on it.
    Timeout,
    /// A notifier had already taken this waiter off the list: pass the
    /// notification on. Read whether the list is empty ...
    Pass,
    /// ... and wake one waiter.
    PassPop,
    /// The call returns.
    Done(End),
}

/// The kind of call.
#[derive(Clone, Copy)]
pub struct Cfg {
    /// A `try_` call: never waits.
    pub nonblocking: bool,
    /// A sender: gives up as soon as it reads that every receiver is gone.
    /// (A receiver still pops, since messages may remain.)
    pub stop_when_gone: bool,
}

/// Where a take goes after the access at `pc`. `flag` is what the access
/// read: at `Gone` and `Ready1`, whether the other side is gone; at `Take`
/// and `Ready2`, whether there was something to take; at `Park`, the
/// `notified` flag; at `Timeout`, whether this waiter was still on the
/// list; at `Pass`, whether the list is empty. `aux` is the thread's own
/// business: at `Take`, whether it will snooze and retry before it
/// registers; at `Park`, whether its deadline has passed.
pub open spec fn next_spec(pc: Pc, cfg: Cfg, flag: bool, aux: bool) -> Pc {
    match pc {
        Pc::Gone => if flag && cfg.stop_when_gone {
            Pc::Done(End::Disconnected)
        } else {
            Pc::Take { gone: flag }
        },
        Pc::Take { gone } => if flag {
            Pc::Done(End::Taken)
        } else if gone {
            Pc::Done(End::Disconnected)
        } else if cfg.nonblocking {
            Pc::Done(End::WouldBlock)
        } else if aux {
            Pc::Gone
        } else {
            Pc::Reg
        },
        Pc::Reg => Pc::Ready1,
        Pc::Ready1 => if flag {
            Pc::Remove
        } else {
            Pc::Ready2
        },
        Pc::Ready2 => if flag {
            Pc::Remove
        } else {
            Pc::Park
        },
        Pc::Remove => Pc::Gone,
        Pc::Park => if flag {
            Pc::Gone
        } else if aux {
            Pc::Timeout
        } else {
            Pc::Park
        },
        Pc::Timeout => if flag {
            Pc::Done(End::TimedOut)
        } else {
            Pc::Pass
        },
        Pc::Pass => if flag {
            Pc::Done(End::TimedOut)
        } else {
            Pc::PassPop
        },
        Pc::PassPop => Pc::Done(End::TimedOut),
        Pc::Done(e) => Pc::Done(e),
    }
}

/// [`next_spec`], for `chan_sync.rs` to run.
#[inline(always)]
pub fn next(pc: Pc, cfg: Cfg, flag: bool, aux: bool) -> (r: Pc)
    ensures
        r == next_spec(pc, cfg, flag, aux),
{
    match pc {
        Pc::Gone => if flag && cfg.stop_when_gone {
            Pc::Done(End::Disconnected)
        } else {
            Pc::Take { gone: flag }
        },
        Pc::Take { gone } => if flag {
            Pc::Done(End::Taken)
        } else if gone {
            Pc::Done(End::Disconnected)
        } else if cfg.nonblocking {
            Pc::Done(End::WouldBlock)
        } else if aux {
            Pc::Gone
        } else {
            Pc::Reg
        },
        Pc::Reg => Pc::Ready1,
        Pc::Ready1 => if flag {
            Pc::Remove
        } else {
            Pc::Ready2
        },
        Pc::Ready2 => if flag {
            Pc::Remove
        } else {
            Pc::Park
        },
        Pc::Remove => Pc::Gone,
        Pc::Park => if flag {
            Pc::Gone
        } else if aux {
            Pc::Timeout
        } else {
            Pc::Park
        },
        Pc::Timeout => if flag {
            Pc::Done(End::TimedOut)
        } else {
            Pc::Pass
        },
        Pc::Pass => if flag {
            Pc::Done(End::TimedOut)
        } else {
            Pc::PassPop
        },
        Pc::PassPop => Pc::Done(End::TimedOut),
        Pc::Done(e) => Pc::Done(e),
    }
}

/// The model's phase for a thread at `pc`, holding waiter ticket `tk`,
/// with `left` snoozes to go before it registers.
pub open spec fn abs(pc: Pc, tk: nat, left: nat) -> Ph {
    match pc {
        Pc::Gone => Ph::TGone { left },
        Pc::Take { gone } => Ph::TTake { gone, left },
        Pc::Reg => Ph::TReg,
        Pc::Ready1 => Ph::TReady1 { tk },
        Pc::Ready2 => Ph::TReady2 { tk },
        Pc::Remove => Ph::TRemove { tk },
        Pc::Park => Ph::TPark { tk },
        Pc::Timeout => Ph::TTimeout { tk },
        Pc::Pass => Ph::TPass,
        Pc::PassPop => Ph::TPassPop,
        Pc::Done(_) => Ph::Idle,
    }
}

/// What the access at `pc` read, as `flag`.
pub open spec fn reads(s: St, pc: Pc, tk: nat, flag: bool) -> bool {
    match pc {
        Pc::Gone | Pc::Ready1 => flag == (s.alive == 0),
        Pc::Take { .. } => flag == (s.c > 0),
        // The re-check never misses something that is there; it may say
        // "maybe" when there is nothing.
        Pc::Ready2 => s.c > 0 ==> flag,
        Pc::Park => flag == s.notified.contains(tk),
        Pc::Timeout => flag == s.list.contains(tk),
        // `empty` may lag behind the list, but never says "empty" while a
        // waiter is on it.
        Pc::Pass => flag ==> s.list.is_empty(),
        Pc::Reg | Pc::Remove | Pc::PassPop | Pc::Done(_) => true,
    }
}

/// What the access at `pc` did to the shared state: `m` is the state
/// after it, before the thread's own phase changes.
pub open spec fn writes(s: St, pc: Pc, tk: nat, flag: bool, m: St) -> bool {
    match pc {
        // A successful pop (push) takes one message (slot).
        Pc::Take { .. } => m == if flag {
            St { c: (s.c - 1) as nat, ..s }
        } else {
            s
        },
        // Registration adds a fresh ticket to the list.
        Pc::Reg => m == (St {
            list: s.list.insert(s.next_tk),
            owner: s.owner.insert(s.next_tk, tk),
            next_tk: s.next_tk + 1,
            ..s
        }),
        // `remove` takes the ticket off the list (if it is there).
        Pc::Remove | Pc::Timeout => m == (St { list: s.list.remove(tk), ..s }),
        // `notify` takes one waiter off the list and sets its flag.
        Pc::PassPop => if s.list.is_empty() {
            m == s
        } else {
            exists|k: nat| took_off(s, k, m)
        },
        // The others only read.
        Pc::Gone | Pc::Ready1 | Pc::Ready2 | Pc::Park | Pc::Pass | Pc::Done(_) => m == s,
    }
}

/// The ticket after the access at `pc`: registration draws a new one.
pub open spec fn tk_next(s: St, pc: Pc, tk: nat) -> nat {
    if pc is Reg {
        s.next_tk
    } else {
        tk
    }
}

/// The snoozes left after the access at `pc`.
pub open spec fn left_next(pc: Pc, flag: bool, aux: bool, left: nat) -> nat {
    match pc {
        Pc::Take { .. } => if !flag && aux {
            (left - 1) as nat
        } else {
            left
        },
        Pc::Remove | Pc::Park => 0,
        _ => left,
    }
}

/// The shared state after a notifier took waiter `k` off the list and set
/// its flag.
pub open spec fn took_off(s: St, k: nat, m: St) -> bool {
    s.list.contains(k) && m == (St { list: s.list.remove(k), notified: s.notified.insert(k), ..s })
}

proof fn lemma_go_same(s: St, t: nat)
    requires
        t < s.th.len(),
    ensures
        go(s, t, ph(s, t)) == s,
{
    assert(s.th.update(t as int, Th { ph: s.th[t as int].ph, timed: s.th[t as int].timed }) =~= s.th);
}

/// Every move `chan_sync.rs` makes in a take is a step of the model.
///
/// Thread `t` is at `pc` (the model has it in phase `abs(pc, tk, left)`).
/// It makes the access for `pc`, which reads `flag` and leaves the shared
/// state as `m`, and moves to `next(pc, cfg, flag, aux)`. The hypotheses
/// on `aux` and `cfg` are what the model assumes of a thread's own
/// choices: a `try_` call and a call that checks a deadline are `timed`,
/// a call snoozes after a failed attempt exactly while its counter of
/// snoozes is positive, and it registers only once that counter is zero.
pub proof fn theorem_next_refines(s: St, t: nat, pc: Pc, cfg: Cfg, flag: bool, aux: bool, tk: nat, left: nat, m: St)
    requires
        t < s.th.len(),
        ph(s, t) == abs(pc, tk, left),
        reads(s, pc, tk, flag),
        writes(s, pc, if pc is Reg { t } else { tk }, flag, m),
        cfg.nonblocking ==> timed(s, t),
        pc is Park && aux ==> timed(s, t),
        pc is Take && !flag ==> (aux <==> left > 0),
        pc is Reg || pc is Ready1 || pc is Ready2 || pc is Remove || pc is Park ==> left == 0,
    ensures
        step(
            s,
            t,
            go(m, t, abs(next_spec(pc, cfg, flag, aux), tk_next(s, pc, tk), left_next(pc, flag, aux, left))),
        ),
{
    let p2 = abs(next_spec(pc, cfg, flag, aux), tk_next(s, pc, tk), left_next(pc, flag, aux, left));
    let s2 = go(m, t, p2);
    lemma_go_same(s, t);
    match pc {
        Pc::Gone => {},
        Pc::Take { gone } => {
            if flag {
                assert(s2 == (St { c: (s.c - 1) as nat, ..go(s, t, Ph::Idle) }));
            }
        },
        Pc::Reg => {
            assert(s2 == (St {
                list: s.list.insert(s.next_tk),
                owner: s.owner.insert(s.next_tk, t),
                next_tk: s.next_tk + 1,
                ..go(s, t, Ph::TReady1 { tk: s.next_tk })
            }));
        },
        Pc::Ready1 => {},
        Pc::Ready2 => {},
        Pc::Remove => {
            assert(s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::TGone { left: 0 }) }));
        },
        Pc::Park => {},
        Pc::Timeout => {
            if flag {
                assert(s2 == (St { list: s.list.remove(tk), ..go(s, t, Ph::Idle) }));
            } else {
                assert(s.list.remove(tk) =~= s.list);
            }
        },
        Pc::Pass => {},
        Pc::PassPop => {
            if !s.list.is_empty() {
                let k = choose|k: nat| took_off(s, k, m);
                assert(pops(s, t, k, Ph::Idle, s2));
            }
        },
        Pc::Done(_) => {},
    }
}

/// The next access of a thread in `notify_one` or `notify_all`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Npc {
    /// Read whether the waiter list is empty.
    Load,
    /// In the list's critical section: wake the next waiter, or leave.
    Pop,
    Done,
}

/// Where a notifier goes after the access at `pc`. `flag` is what the
/// access read: at `Load`, the `empty` flag; at `Pop`, whether the list
/// was empty (so there was nobody to wake). `notify_one` wakes one waiter
/// and leaves; `notify_all` (`all`) stays until the list is empty.
pub open spec fn notify_next_spec(pc: Npc, all: bool, flag: bool) -> Npc {
    match pc {
        Npc::Load => if flag {
            Npc::Done
        } else {
            Npc::Pop
        },
        Npc::Pop => if all && !flag {
            Npc::Pop
        } else {
            Npc::Done
        },
        Npc::Done => Npc::Done,
    }
}

#[inline(always)]
pub fn notify_next(pc: Npc, all: bool, flag: bool) -> (r: Npc)
    ensures
        r == notify_next_spec(pc, all, flag),
{
    match pc {
        Npc::Load => if flag {
            Npc::Done
        } else {
            Npc::Pop
        },
        Npc::Pop => if all && !flag {
            Npc::Pop
        } else {
            Npc::Done
        },
        Npc::Done => Npc::Done,
    }
}

/// The model's phase for a notifier at `pc`; `all` for `notify_all`.
pub open spec fn nabs(pc: Npc, all: bool) -> Ph {
    match pc {
        Npc::Load => if all {
            Ph::GNotifyAll
        } else {
            Ph::GNotify
        },
        Npc::Pop => if all {
            Ph::GNotifyAllPop
        } else {
            Ph::GNotifyPop
        },
        Npc::Done => Ph::Idle,
    }
}

/// What a notifier's access at `pc` read, as `flag`.
pub open spec fn notify_reads(s: St, pc: Npc, flag: bool) -> bool {
    match pc {
        Npc::Load => flag ==> s.list.is_empty(),
        Npc::Pop => flag == s.list.is_empty(),
        Npc::Done => true,
    }
}

/// What a notifier's access at `pc` did to the shared state.
pub open spec fn notify_writes(s: St, pc: Npc, m: St) -> bool {
    match pc {
        Npc::Pop => if s.list.is_empty() {
            m == s
        } else {
            exists|k: nat| took_off(s, k, m)
        },
        Npc::Load | Npc::Done => m == s,
    }
}

/// Every move of `notify_one` and `notify_all` is a step of the model.
pub proof fn theorem_notify_refines(s: St, t: nat, pc: Npc, all: bool, flag: bool, m: St)
    requires
        t < s.th.len(),
        ph(s, t) == nabs(pc, all),
        notify_reads(s, pc, flag),
        notify_writes(s, pc, m),
    ensures
        step(s, t, go(m, t, nabs(notify_next_spec(pc, all, flag), all))),
{
    let p2 = nabs(notify_next_spec(pc, all, flag), all);
    let s2 = go(m, t, p2);
    lemma_go_same(s, t);
    if pc is Pop && !s.list.is_empty() {
        let k = choose|k: nat| took_off(s, k, m);
        assert(pops(s, t, k, p2, s2));
    }
}

} // verus!
