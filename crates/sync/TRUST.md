# What verilith-sync trusts, and why

Verus checks every proof in verilith-sync, but a proof only means something
relative to the specifications and axioms it starts from. This file lists
everything that is assumed rather than proven, and argues for each
assumption. The most important one is the release/acquire memory model in
`src/ra.rs`, which the queues are verified against.

## The short list

- **Tools**: Verus (pinned in CI), Z3, rustc.
- **vstd**: its cells (`PCell`, `PointsTo`), invariants, ghost resources,
  the logically-atomic-triple machinery, and its sequentially consistent
  atomics (`PAtomicU32`, `PAtomicU64`), which the locks use.
- **`src/ra.rs`**: the release/acquire model. Every `axiom fn` and
  `external_body` function in it is an assumption. Most of this file is
  about them.
- **One more axiom**, `Model::pool_nonempty` in `src/chan_model.rs`:
  boundedly many channel calls are in progress at once (see "The
  channel" at the end).
- **`impl Objective`**: a trusted claim per type (see below). There are
  four: `Hist`, `HistLb`, `spsc::Shared`, `array_queue::Shared`.
- **Specifications**: `QueueView` and the `atomically` blocks on the queue
  operations, and the `RwToks` state machine. Read these to check that they
  say what you expect.
- **Unverified code with no access to the data**: `src/util.rs`
  (`CachePadded`, `Backoff`, `arc_clone`, `exhausted`, `leaked_guard`,
  and the wrappers around `std`'s mutex, `park`/`unpark` and `Instant`
  that the channel uses), `src/parking.rs` and the `park`/`unpark`
  wrappers in the locks that call it, the public shell of the channel in
  `src/channel.rs`, and the one-line `Send`, `Sync`, `Deref` and `Drop`
  impls. CI runs the tests under Miri, whose weak-memory emulation
  exercises release/acquire behaviour too.
- **The progress models** in `src/progress/`: each is a hand-written
  transition system for one protocol, and the progress theorems are about
  the model. For the mutex, the RwLock and the queue, that the model
  matches the code is argued in "Progress" below, step by step, not
  proven. For the channel it is proven: `src/chan_sync.rs` is verified
  against the model, and what that proof still assumes is listed under
  "The channel: what is still assumed".

CI greps for `assume` and `admit` and fails if either appears, and for
any `axiom fn` outside `src/ra.rs` other than that one.

## The release/acquire model

### What it says

`src/ra.rs` follows the view-based operational model of ORC11 (Dang,
Jourdan, Kaiser and Dreyer, "RustBelt Meets Relaxed Memory", POPL 2020).

- Each atomic location has a **history** (`Hist`): its messages in
  modification order, each with a value and a **view**.
- A **view** (`RaView`) maps every location to a timestamp, an index into
  that location's history.
- A `Tid` is a **lower bound on the current thread's view**.
- A **load** may read any message at or after the thread's timestamp for
  the location. An acquire load also joins the message's view into the
  thread's view. A relaxed load joins only the message's own timestamp.
- A **release store** appends a message whose view is the thread's view.
- A **read-modify-write** reads the *last* message and appends its result
  right after it. Its new message's view includes the view of the message
  it read, which models release sequences.
- A **failed compare-and-swap** is a relaxed load.
- A resource whose meaning depends on the thread's view (a cell
  permission, or a `Tid`) is **subjective**. Subjective resources cross
  threads only inside `Published`, which records the view they were
  published at and hands them out only to a thread whose view covers it.
- Shared invariants (`ObjInvariant`) may hold only **objective** types.

### Why each axiom holds

**`Tid::new` gives the bottom view.** Every thread's view is at least the
bottom view, so this lower bound is always true.

**`Tid::dup`, `Tid::join`.** A lower bound can be copied, and two lower
bounds on the same thread's view combine into their join.

**A `Tid` stays with its thread.** `Tid` is a tracked value that is not
`Objective`, and it is neither `Send` nor `Sync` (it holds a
`PhantomData<*const ()>`; a `compile_fail` doctest in `src/ra.rs` checks
this). So Rust's type system, not convention, rules out moving it to
another thread through a shared vstd `AtomicInvariant`, a `static`, or any
other path that does not synchronize: the only ways to move it are inside a
`Published`, or inside an exec type that opts back in with an
`unsafe impl Send`. `Producer` and `Consumer` are the only such types, and
they are moved between threads only by synchronizing transfers: spawning,
joining, channels and locks all create happens-before. This is the same
argument RustBelt uses for `Send`. So the receiving thread's view covers
the sender's, and the lower bound stays true. Earlier versions left `Tid`
`Send` by accident (an empty struct is `Send`), which let client code built
on `verilith_sync::ra` move a `Tid` through a plain `AtomicInvariant` without
synchronizing; verilith-sync's own code never did.

**`Published::publish`, `Published::acquire`.** A cell permission is valid
for any thread whose view includes the writes it depends on. Publishing
records the publisher's view. Acquiring requires the acquirer's view to
cover it, so everything the publisher did to the cell happens-before the
acquirer's accesses. This is ORC11's "view-at" modality.

**`Objective`.** An implementing type must contain no `Tid` and no cell
permission outside `Published`. Then its meaning is the same in every
thread, and an invariant can hold it. The four implementations are a
trusted claim: `Hist` and `HistLb` are ghost history data; the two
`Shared` structs hold histories, ghost variables, monotonic counters, ghost
maps and `Published` cells only.

**`Hist::nonempty_lemma`.** Every location is created with an initial
message (`RaU64::new`).

**`Hist::bounded_lemma`.** Views are built only from timestamps of
messages that exist.

**`Hist::lb`, `Hist::lb_prefix`, `HistLb::dup`.** Every operation in the
model only appends to a history, so a snapshot stays a prefix forever.

**`RaU64::load_acquire`, `load_relaxed`.** These are coherence (read at or
after your timestamp) and acquire synchronization, as in ORC11.

**RMWs (`fetch_add_acqrel`, `fetch_sub_acqrel`, successful
`compare_exchange_seqcst`) read the last message.** This is C11's RMW
atomicity: an RMW reads the write immediately before its own in
modification order. `compare_exchange_seqcst` is SeqCst on success and the
model treats it as AcqRel, which SeqCst includes, so this loses nothing;
the SeqCst is there for the channel's wakeup handshake, which the model
does not cover (see "Progress" below).

**`RaU64::sync_exclusive` makes the thread see every write.** A thread
with `&mut` access to an atomic has synchronized with every earlier access
through shared references. Rust guarantees this, since otherwise
`AtomicU64::get_mut`, a safe non-atomic access, would race. The function
does nothing at run time. verilith-sync uses it only when dropping an
`ArrayQueue`.

### The one place the model is stronger than C11

In this model a store **appends** to the history, so modification order
agrees with the order in which the model interleaves writes. ORC11 instead
lets a store insert its message anywhere after the thread's own timestamp.

Appending is the "strong release/acquire" model (SRA) of Lahav,
Giannarakis and Vafeiadis ("Taming Release-Acquire Consistency", POPL
2016). SRA forbids a few outcomes that C11's release/acquire allows, the
classic one being 2+2W. They show that SRA is exactly what x86-TSO, ARMv8
and POWER provide for release/acquire accesses under the standard
compilation mappings. So the proofs hold for the machine code verilith-sync
compiles to on those architectures. They are not proven for every execution
the C11 specification would allow.

For verilith-sync's own code, the gap should not matter. Every location in verilith-sync
has, at any moment, at most one thread that writes it with plain stores:
the SPSC producer owns `tail` and the consumer owns `head`, and an
`ArrayQueue` slot's stamp is written only by the thread holding that
slot's ticket, after an acquire load that read the current stamp. Every
other write to these locations is an RMW. Call the writer's last write (or
the message it read) `m`. Coherence puts the new store after `m`. RMW
atomicity puts each RMW immediately after the message it read, so no store
can land inside the chain of RMWs that follows `m`. The store therefore
goes after every message in the history, which is what appending says.
This is an argument, not a proof. Making the model C11-exact would mean
modelling insertion, and is future work.

### Mixing with the sequentially consistent proofs

`Mutex` and `RwLock` are verified with vstd's SC atomics and use only
`SeqCst` operations on their own lock words. Their invariants mention only
their own lock word and the data it guards, and no resource passes between
them and the release/acquire objects. A SeqCst write that a SeqCst RMW
reads creates synchronizes-with, which is all the data handoff needs. Each
lock is a single-location object whose operations are totally ordered.
These locks could be re-verified against `src/ra.rs`, but that has not
been done.

## Progress

The safety proofs say what an operation does when it returns. The
modules in `src/progress/` prove that operations return: that the locks
never deadlock, that a thread parked on a channel is always woken once it
can make progress, and that the MPMC queue is lock-free. Verus has no
temporal logic, so each theorem quantifies over infinite executions
directly (`ex: spec_fn(nat) -> St`, with step `i` taken by thread
`sched(i)`) under one assumption, `trace::fair`: every thread takes
infinitely many steps. Each model also proves that its hypotheses can
hold (`lemma_nonvacuous`), and each proof was checked to fail when a known
bug is seeded into the model (an unlock that does not wake, a park
without the re-check, a give without a notify, a waiter that skips its
re-check, a last reader that does not wake, a pop that never confirms
"empty").

### What is proved

| Theorem | Says |
| --- | --- |
| `mutex::theorem_deadlock_free` | While a thread waits in `lock()`, some thread holds the lock later |
| `rwlock::theorem_deadlock_free` | While a thread waits in `read()` or `write()`, some thread holds the lock later |
| `channel::theorem_resource_taken` | While a receiver waits and a message is queued (or a sender waits and a slot is free), some receiver (sender) takes one, or the waiter returns, or the other side disconnects |
| `channel::theorem_disconnect_seen` | Once every sender (receiver) is gone, a waiting receiver (sender) returns |
| `queue::theorem_lock_free` | While a thread is in `push`, `pop` or `len`, some call returns |

The key invariants, each checked over every step of every thread:

- **Mutex, no lost wakeups**: while a thread sleeps on the parking-lot
  list, the word is 2, or some thread is about to wake a sleeper, about to
  swap in 2, or was taken off the list and will retry.
- **RwLock**: the reader count is exactly the number of read-lock holders
  and the writer bit is set exactly while a writer holds the lock alone;
  the parking hints are set only while someone holds the lock or the last
  reader out is about to clear them; and while anyone sleeps, "parked" is
  set or some thread is about to wake everyone.
- **Channel, counting**: while a taker sleeps and the other side is
  connected, the number of messages (free slots) is at most the number of
  pending notifiers plus takers that are off the list and still going. A
  notification that lands on a waiter that has registered but not yet
  re-checked is not lost: that waiter counts as woken from then on.
- **Queue**: the usual Vyukov window invariant (each slot is free for, or
  holds, the position in `[head, head + cap)` it maps to, or a claimant is
  in flight on it), on unpacked positions and stamp ranks.

Not proved, because it is false for these algorithms: that every
individual thread eventually succeeds. Drepper's mutex and the RwLock let
newcomers barge, channel receivers can lose every race for a message, and
queue operations can lose every CAS. crossbeam and parking_lot (between
its fairness timeouts) behave the same way. SPSC needs no model: none of
its functions is exempt from Verus's termination check, so each `push`,
`pop`, `push_slice` and `pop_into` returns after a bounded number of its
own steps whatever the other side does, which is wait-freedom. The same
holds for `try_lock`, `try_read`, `try_write`, every unlock and
`downgrade`. `exec_allows_no_decreases_clause`, which turns the
termination check off, appears on eleven looping functions:
`ArrayQueue::{push, pop, len}`, `Mutex::{lock, lock_slow}`,
`RwLock::{read, write, read_slow, write_slow}`, the channel's `Chan::slow`
and `Chan::add_handle` (see "The channel", item 6). The repository's
[trust ledger](../../TRUST-LEDGER.md), which CI keeps up to date, lists
them by name, so a twelfth would show up in review.

### Why the models match the code

**One step per access.** Each model step is one atomic access to shared
state, or one critical section of a mutex that every other access to the
same data also takes (a parking-lot bucket, a channel waiter list). A
critical section touches its protected data plus at most one other
atomic, read once (`park`'s `validate`), so running it as one step changes
no outcome. Purely local work between accesses (computing an index,
backing off) is folded into the neighbouring step. `Backoff` is modeled as
a counter of snoozes left, chosen freely when a call starts: the model
allows every number of snoozes, which covers whatever `Backoff` does.

**Thread-local choices are nondeterministic.** Calls with a deadline may
time out wherever the code checks the deadline; any thread may start any
call at any time; the channel model lets any thread act on either side.
Allowing more behaviour than the code has only makes the theorems
stronger, since they hold for every execution of the model.

**Mapping.** Mutex (`src/progress/mutex.rs`): `Fast` is the `cas(0, 1)`
in `lock`/`try_lock_until_deadline`; `Spin`/`SpinCas` are `lock_slow`'s
spin loop (`load`, then `cas(0, 1)`); `Swap` is `swap_contended`; `Check`
is `parking::park`'s bucket section with `validate = is_contended`;
`Asleep` is the `while !notified` loop, including the deadline branch;
`Crit` to `Unpark` is `unlock`'s swap to 0; `Unpark` is `parking::unpark`'s
bucket section and `Notify` the `notified` store after it. RwLock
(`src/progress/rwlock.rs`): the word is kept as its fields (bit 0 `w`,
bit 1 `pk`, bit 2 `ww`, bits 3 and up `rc`); `Load`/`Cas`/`Flag`/`Check`
are the branches of `read_slow` and `write_slow` (`cas_read`, `cas_write`,
`cas_flags`, `park`), with `write`'s fast-path `cas_write(0)` as a `Cas`
from 0; `RCrit` is `unlock_read` (`fetch_sub`, then `clear_flags` and
`unpark_all` if it was the last reader with a hint set), `WCrit` is
`unlock_write` (swap 0, then `unpark_all` if a hint was set) or
`downgrade` (`fetch_add(ONE_READER - WRITER)`, then `unpark_all` if
parked), and `Unpark`/`Notify` are `unpark_all`'s bucket section and its
loop of `notified` stores. The channel's mapping is not argued here: it
is proven (next section). Queue
(`src/progress/queue.rs`): one phase per atomic access of `push`, `pop`
and `len`, with the stamp comparisons translated to ranks as its module
comment explains.

**Memory model.** The models are sequentially consistent.

- The locks and the parking lot use only SeqCst atomics and mutexes, so
  for them the models are exact.
- The channel is covered in the next section.
- The queue's loads are relaxed or acquire and can return an older value.
  That only adds failed attempts, after which the loop reloads; the model
  shows that once nobody makes progress, nothing changes, so the next
  attempt that reads the final values succeeds. Reading them needs the
  stores to become visible eventually, which C++ only encourages
  ([intro.progress]: "should") but every hardware target provides.

**Scheduling.** Fairness is weak: it does not say how often or in what
order threads run, only that none stops for good. A thread that never
runs again (killed, or blocked on something outside these primitives)
can block others: a lock holder that never unlocks, or a queue claimant
between its CAS and its stamp store. The models build in that every lock
holder unlocks (its next step is the unlock), and that each thread does
one lock operation at a time, so a thread waiting for a lock it already
holds is outside the theorems, as it deadlocks in parking_lot too.

## The channel: what is proven, and what is still assumed

The channel's progress theorems used to be about a model that was matched
to the code by hand. Now Verus checks the match.

**How.** `src/chan_model.rs` wraps a state of the model
(`progress::channel::St`) in a ghost resource, `Model`, that can only be
changed by `Model::step`, and `step` demands a proof that the change is a
`step` of the model by the thread whose token the caller holds. The
resource also carries the whole execution so far and proves it is one
(`Model::lemma_is_run`). `src/chan_sync.rs` keeps two of these, one per
direction, inside the channel's invariant, together with the permissions
for the channel's atomics and the caller's view of the queue. The
invariant (`ChanPred`, `dir_inv`) ties them together: the sender count is
the receivers' `alive` and the receiver count the senders'; the queue's
length is `c` for receivers and capacity minus length is `c` for senders;
a waiter's `notified` flag is set exactly when its ticket is in the
model's `notified`; the list under the lock is the model's `list`; and if
`empty` says the list is empty, it is. Every access the channel code makes
to shared state happens with this invariant open, so each one has to come
with the model steps that keep it true:

| Access in `chan_sync.rs` | Model step |
| --- | --- |
| load of the other side's count (`read_gone`) | `TGone`, `TReady1` |
| the queue's push or pop, at its linearization point (`push_step`, `pop_step`) | `TTake` in one direction and, if it succeeded, the give in the other, at the same instant |
| the store to `empty` in `register` | `TReg` |
| the queue's `confirm_empty` / `confirm_full`, at its linearization point (`recheck`) | `TReady2` |
| the store to `empty` in `remove` | `TRemove`, `TTimeout` |
| load of the waiter's `notified` (`park`) | `TPark` |
| load of `empty` (`load_empty`) | `TPass`, `GNotify`, `GNotifyAll` |
| each store to a waiter's `notified` in `notify`, and its final store to `empty` | `TPassPop`, `GNotifyPop`, `GNotifyAllPop` |
| the compare-and-swap that counts a new handle (`add_handle`) | clone |
| the `fetch_sub` that uncounts one (`drop_handle`) | drop |

A call starts and ends with its model thread idle (`begin`, `enter`,
`leave`), and the loops that run a call are still the interpreter for
`chan_core::next`, now with `theorem_next_refines` applied at each access
instead of cited.

Three things in the model changed so that the code could be proved to
follow it, each making the model allow more, and both theorems were
re-proved:

- `notify`'s critical section is no longer one step. `notify_all` sets
  one waiter's flag per step, and a waiter may see its flag before the
  next one is set.
- A load of `empty` may lag: it can still say "not empty" just after the
  last waiter left, because `empty` is stored after the list changes. It
  never says "empty" while a waiter is listed, because a waiter joins the
  model's list at its store of `false`.
- The re-check may answer "maybe" when there is nothing to take. It never
  misses something that is there.

The re-check itself changed. It used to call `len()`, whose loads are
relaxed, behind a SeqCst fence, with an argument from the C++ standard
that this could not miss a message. It now calls
`ArrayQueue::confirm_empty` (or `confirm_full`), which reads one end of
the queue with a read-modify-write and is verified, in the release/acquire
model, to answer "empty" only if the queue was empty at one instant during
the call. The fence is gone.

**What is still assumed.** Exactly this:

1. **Boundedly many calls at once** (`Model::pool_nonempty`, the one
   axiom outside `src/ra.rs`). The model has `n` threads, and a call acts
   as one of them from start to return, so some model thread must be free
   whenever a call starts. `n` is not a number in the program (it is
   `chan_sync::model_threads()`, uninterpreted) and the theorems hold for
   every `n`, so this says only that the number of calls in progress on
   one channel at once is bounded, which holds for any program whose
   number of threads is.

2. **SeqCst operations, across the two memory models.** The channel's own
   atomics (`empty`, each `notified`, the two counts) are vstd's
   sequentially consistent atomics and every operation on them is SeqCst.
   The queue is verified under `src/ra.rs`. The channel's proof opens its
   invariant at the queue's linearization points, which treats those
   points and the SeqCst operations as steps of one interleaving. Every
   one of those linearization points is a SeqCst read-modify-write of
   `head` or `tail` (the compare-and-swap that claims a position, or the
   `fetch_add(0)` that confirms full or empty), and every write to `head`
   and `tail` is one of these. C++ [atomics.order] gives all SeqCst
   operations a single total order in which each one sees the latest
   SeqCst write to its location, so that order is the interleaving. This
   is the same kind of assumption as "Mixing with the sequentially
   consistent proofs" above, and it is where the old fence argument went:
   the store-buffering handshake (waiter: store `empty`, then read the
   queue; notifier: write the queue, then load `empty`) is now four SeqCst
   operations. `src/ra.rs` gives these read-modify-writes only
   acquire-release meaning, which is all the queue's own proof needs.

3. **`std`, through four wrappers in `src/util.rs`.** `Lock`: that
   `std::sync::Mutex` gives mutual exclusion, so the value `lock` returns
   is the one the last `unlock` stored (a guard dropped without `unlock`
   aborts, so the invariant cannot be skipped). `Unparker::unpark` and
   `park_for` have no specification at all: they only affect when a thread
   runs. `time_left` is trusted to report "late" only when there is a
   deadline. `Backoff` is used only to pause; the number of snoozes before
   a call registers is a verified counter (`chan_sync::SNOOZES`).

4. **Scheduling, for the progress theorems to apply.** They hold for
   executions of the model in which every thread keeps taking steps. For
   the code this means: a thread that is not parked keeps running; a
   thread waiting for a waiter list's mutex gets it (critical sections
   are short and proven to terminate, but `std`'s mutex is not proven
   fair); and a parked thread whose `notified` flag has been set runs
   again. The last depends on `notify` calling `unpark` after it stores
   the flag, and on `std`'s promise that `unpark` wakes a parked thread or
   makes its next `park` return. Verus does not check that the call is
   there, since `unpark` has no specification; nothing but progress
   depends on it. A parked thread whose flag is clear counts as taking
   steps that change nothing, which the model allows.

5. **The shell, `src/channel.rs`.** `Sender` and `Receiver` wrap
   `chan_sync::Handle` and forward to it. The verified functions have
   preconditions the shell is trusted to meet: a handle is well formed
   (it comes from `Handle::pair` or `clone_handle`), `disconnect` is
   called once, from `drop`, and a sender is never used to receive or a
   receiver to send. `len`, `is_empty`, `is_full` and `capacity` read the
   queue directly and are hints, as in crossbeam.

6. **Two loops without a termination proof.** `Chan::slow` is the
   blocking loop the progress theorems are about. `Chan::add_handle`
   (cloning a handle) retries a compare-and-swap, so that the count
   provably cannot overflow; a retry means another clone or drop on the
   same side succeeded, so it is lock-free, but that is not proven.

What the theorems say is unchanged, and so is what they do not say: a
particular receiver can lose every race for a message.
