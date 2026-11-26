# What verilith-sync trusts, and why

Verus checks every proof in verilith-sync, but a proof only means something
relative to the specifications and axioms it starts from. This file lists
everything that is assumed rather than proven, and argues for each
assumption. The most important one is the release/acquire memory model in
`src/ra.rs`, which the queues are verified against. The MPMC queue and
the channel use only its C11 rules, so their proofs hold for C11 itself;
the SPSC queue's hold for x86, ARMv8 and POWER, and "Where writes go"
below shows why no proof could cover C11 for it as written.

## The short list

- **Tools**: Verus (pinned in CI), Z3, rustc.
- **vstd**: its cells (`PCell`, `PointsTo`), invariants, ghost resources,
  the logically-atomic-triple machinery, and its sequentially consistent
  atomics (`PAtomicU32`, `PAtomicU64`), which the locks use.
- **`src/ra.rs`**: the release/acquire model. Every `axiom fn` and
  `external_body` function in it is an assumption. Most of this file is
  about them. Three of them (`store_release_sra`, `fetch_add_acqrel_sra`,
  `fetch_sub_acqrel_sra`) hold only for the hardware model, and only
  `spsc` uses them.
- **One more axiom**, `Model::pool_nonempty` in `src/model.rs`:
  boundedly many calls are in progress at once on one lock, queue or
  channel (see "Progress").
- **The parking lot's hand-over** in `src/lot.rs`: `lock_bucket` and
  `unlock_bucket`, and each lock's `key`, are trusted to give a lock the
  ghost list of its own waiters (see "The parking lot").
- **`impl Objective`**: a trusted claim per type (see below). There are
  four: `Hist`, `HistLb`, `spsc::Shared`, `array_queue::Shared`.
- **Specifications**: `QueueView` and the `atomically` blocks on the queue
  operations, and the `RwToks` state machine. Read these to check that they
  say what you expect.
- **Unverified code with no access to the data**: `src/util.rs`
  (`CachePadded`, `Backoff`, `wait_turn`, `arc_clone`, `exhausted`,
  `leaked_guard`, and the wrappers around `park`/`unpark` and `Instant`
  that the channel and the parking lot use), `fair::Bomb` (it aborts if a
  fair lock's guard is dropped without `unlock`), the public shell of the channel in
  `src/channel.rs`, the one-line `Send`, `Sync`, `Deref` and `Drop`
  impls, and the plain-Rust queue methods (`ArrayQueue::push`, `pop`,
  `confirm_empty`, `confirm_full`; `Producer::push`, `push_slice`;
  `Consumer::pop`, `pop_into`). Each calls its verified `*_atomic` form
  with `Tracked::assume_new()` for the atomic update, a ghost argument
  that is erased at run time and assumes nothing about the data. CI runs the tests under Miri, whose weak-memory emulation
  exercises release/acquire behaviour too.
- **The progress models** in `src/progress/`: each is a hand-written
  transition system for one protocol, and the progress theorems are about
  the model. That the code follows its model is proven for all six (the
  mutex, the RwLock, the MPMC queue, the channel, the channel's handle
  counts and the fair lock), as "Progress" explains. What those proofs
  still assume is the axiom and the hand-over above, fairness of
  scheduling and of the memory system, and for the channel the items
  under "The channel: what is still assumed". They no longer assume
  anything of `std`'s mutex: the parking lot and the channel's waiter
  lists use `src/fair.rs`, a ticket lock proven to give mutual exclusion
  and to be starvation-free.

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
- A **release store** appends a message whose view is the thread's view,
  if the thread has seen the last message.
- A **read-modify-write** reads the *last* message and appends its result
  right after it, if the thread has seen the last message or only RMWs
  have written the location. Its new message's view includes the view of the message
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

**RMWs (`fetch_add_acqrel`, `fetch_add_seqcst`, `fetch_sub_acqrel`,
successful `compare_exchange_seqcst`) read the last message, and
`store_release` appends.** C11's RMW atomicity says an RMW reads the
write immediately before its own in modification order; that this is the
*last* message, and that a store goes at the end, is what the
preconditions `rmw_reads_last` and `seen_last` buy, as "Where writes go"
below explains. The `_sra` forms drop the preconditions and hold only in
the hardware model. `compare_exchange_seqcst` is SeqCst on success and the
model treats it as AcqRel, which SeqCst includes, so this loses nothing;
the SeqCst is there for the channel's wakeup handshake, which the model
does not cover (see "Progress" below).

**`RaU64::sync_exclusive` makes the thread see every write.** A thread
with `&mut` access to an atomic has synchronized with every earlier access
through shared references. Rust guarantees this, since otherwise
`AtomicU64::get_mut`, a safe non-atomic access, would race. The function
does nothing at run time. verilith-sync uses it only when dropping an
`ArrayQueue`.

### Where writes go: C11, and where the hardware model is still assumed

C11 does not order a location's writes by when they happen. In ORC11 a
store may take any place in the modification order after the messages
its thread has seen, except between a read-modify-write and the message
that RMW read (RMW atomicity), and an RMW may read any message the thread
has not seen past, as long as no other RMW has read it. The model here
keeps a history as a list in modification order and appends every
write. That alone is the "strong release/acquire" model (SRA) of Lahav,
Giannarakis and Vafeiadis ("Taming Release-Acquire Consistency", POPL
2016): exactly what x86-TSO, ARMv8 and POWER provide for release/acquire
accesses under the standard mappings, but stronger than C11, which also
allows 2+2W and store buffering through RMWs (see below).

So the C11 rules in `src/ra.rs` append only where C11 leaves no other
place, and their preconditions say when that is:

- **`store_release`** requires `seen_last`: the thread's view is at the
  location's last message. A C11 store goes after everything its thread
  has seen, and nothing comes after the last message, so the end is its
  only place.
- **Read-modify-writes** (`fetch_add_acqrel`, `fetch_add_seqcst`,
  `fetch_sub_acqrel`, a successful `compare_exchange_seqcst`) require
  `rmw_reads_last`: `seen_last`, or `rmw_only`, which says that every
  message but the first was written by an RMW of the one before it. Then
  every message but the last has already been read by an RMW, so C11
  leaves a new RMW only the last message to read. `RaU64::new` starts a
  history with `rmw_only`, every RMW keeps it, and a store ends it.
- Loads, failed CASes and `sync_exclusive` are unchanged: they never
  needed the list to be in time order.

Under these preconditions each step the model takes is one ORC11 allows,
and ORC11's other choices at that step are ruled out, so proofs that use
only these rules hold for C11 itself (as ORC11 formalizes it, which, like
RC11, rules out out-of-thin-air values). Two primitives use only these
rules:

- **The MPMC queue.** `head` and `tail` are written only by RMWs, and
  its invariant now records `rmw_only` for both. A slot's stamp is
  written by a plain store, by the thread holding that slot's ticket,
  after an acquire load of the stamp. The invariant now also says that
  only the last message of a stamp holds its current value, so the
  message that load read, which held the value the ticket is for, is the
  last one, and the storing thread has seen it. Verus checks `seen_last`
  at both stores.
- **The channel**, which is the MPMC queue plus SeqCst atomics (see
  "Mixing" below and "The channel").

This replaces a paper argument (every location has one plain writer, so
its stores land at the end). The argument was right for the MPMC queue,
as the proof now shows. For the SPSC queue it was wrong:

**The SPSC queue is linearizable on the hardware, but not in C11.** Its
producer writes `tail` with plain stores and the consumer writes it
with the `fetch_add(0)` that confirms "empty"; `head` is the mirror
image. Take capacity 2. The producer pushes items 1 and 2 (it stores
`tail = 1`, then `tail = 2`) and tries a third push: its load of `head`
says 0, so the queue looks full, and it confirms with an RMW of `head`.
The consumer pops item 1 (it reads `tail = 1` and stores `head = 1`) and
tries another pop: its load of `tail` says 1, so the queue looks empty,
and it confirms with an RMW of `tail`. C11 lets the producer's RMW read
`head = 0`, placed before the consumer's store, and the consumer's RMW
read `tail = 1`, placed between the producer's two stores: no
happens-before edge forbids either. That is store buffering, with RMWs
as the loads. Then `push` reports "full" and `pop` reports "empty", and
no order of the operations explains both: "full" needs push 2 before
pop 1, and "empty" needs pop 1 before push 2. x86, ARMv8 and POWER
forbid this outcome (there, an RMW is ordered after the thread's earlier
stores, which is what SRA says). So the SPSC proofs use the SRA rules
(`store_release_sra`, `fetch_add_acqrel_sra`, and `fetch_sub_acqrel_sra`
for the reference count), and Verus rejects the C11 rules there, as it
should. Making SPSC correct for C11 would take RMWs for the index stores
(an `xchg` per push on x86, the cost this queue was rebuilt to avoid) or
SeqCst fences before the confirming RMWs, which this model cannot
express yet.

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
| `handles::theorem_lock_free` | While a thread is cloning a channel handle, some clone or drop on the same side takes effect |
| `ticket::theorem_starvation_free` | Every thread waiting for a fair lock (a parking-lot bucket, a channel waiter list) gets it |

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
- **Fair lock**: the tickets from `serving` up to `next` belong to
  distinct threads, each waiting or, for `serving` only, holding the
  lock. So `serving` keeps growing while anyone waits, and reaches every
  waiter. The same fact bounds the outstanding tickets by the number of
  threads, which is why the counters may wrap around at 2^64.
- **Handle count**: the count changes only by a clone or drop that takes
  effect, so a clone's CAS fails only after one did.

Not proved, because it is false for these algorithms: that every
individual thread eventually succeeds. Drepper's mutex and the RwLock let
newcomers barge, channel receivers can lose every race for a message, and
queue operations and handle clones can lose every CAS. (The fair lock is
the exception: it serves waiters in order.) crossbeam and parking_lot (between
its fairness timeouts) behave the same way. SPSC needs no model: none of
its functions is exempt from Verus's termination check, so each `push`,
`pop`, `push_slice` and `pop_into` returns after a bounded number of its
own steps whatever the other side does, which is wait-freedom. The same
holds for `try_lock`, `try_read`, `try_write`, every unlock and
`downgrade`. `exec_allows_no_decreases_clause`, which turns the
termination check off, appears on ten looping functions:
`ArrayQueue::{push_atomic, pop_atomic, len}`, `Mutex::lock_slow`,
`RwLock::{read_slow, write_slow, park}`, the channel's `Chan::slow`
and `Chan::add_handle`, and `fair::Lock::lock`. Each has a progress
theorem: `lock`, `read` and `write` call their slow paths without a
deadline, which are proven to return the lock then; `add_handle` is
lock-free and `fair::Lock::lock` starvation-free. The repository's
[trust ledger](../../TRUST-LEDGER.md), which CI keeps up to date, lists
them by name, so an eleventh would show up in review.

### How the code is checked against the models

Each primitive keeps, inside the invariant that holds its atomics, a
ghost `model::Model` (`src/model.rs`): a state of its protocol's model
and the execution so far. The only way to change it is `Model::step`,
which demands a proof that the change is a step of the model by the
thread whose token (`Tok`) the caller holds. The invariant ties the
model's state to the real one (the lock word, the waiters' flags, the
queue's head, tail and stamps), so every access the code makes to shared
state has to come with the model step it stands for, and a call that
returned has taken a path through the model. A call takes an idle model
thread when it starts and gives it back when it returns, so the axiom
`pool_nonempty` (some model thread is free) says only that boundedly
many calls are in progress on one object at once; the number of model
threads is uninterpreted and the theorems hold for every number.

**One step per access.** Each model step is one atomic access to shared
state, or one critical section of a mutex that every other access to the
same data also takes (a parking-lot bucket, a channel waiter list).
Purely local work between accesses (computing an index, backing off) is
folded into the neighbouring step. Thread-local choices are
nondeterministic in the model: calls with a deadline may time out
wherever the code checks the deadline, and any thread may start any call
at any time. Allowing more behaviour than the code has only makes the
theorems stronger.

**Mutex** (`src/mutex.rs`, model `src/progress/mutex.rs`):

| Code | Model step |
| --- | --- |
| `cas_lock`: the `cas(0, 1)` in `try_lock`, `lock_slow` and its spin loop | `Fast`, `SpinCas` |
| `load_spin`, `spun_out`: the spin loop's load, with its count | `Spin` |
| `swap_contended` | `Swap` |
| `check`: the bucket section that parks if the word is still 2 | `Check` |
| `wait_flag`: load of the waiter's `notified` | `Asleep` |
| `timeout`: the bucket section of a waiter past its deadline | `Asleep` (gives up, or was woken) |
| `unlock`: the swap to 0 | `Crit` |
| `unpark_one`: the bucket section that takes a waiter off and sets its flag | `Unpark`, `Notify` |

**RwLock** (`src/rwlock.rs`, model `src/progress/rwlock.rs`):

| Code | Model step |
| --- | --- |
| `load_at`: a load of the word in `read_slow` or `write_slow`, which decides what comes next: CAS, snooze (counted down as the model's `left`), set a hint, or sleep (`wait`) | `Load` |
| `cas_read`, `cas_write`: the CAS that takes a read or write lock, including the fast paths (`write` starts with a CAS from 0) | `Cas` |
| `cas_flags`: the CAS that sets a parking hint | `Flag` |
| `check`: the bucket section that parks if the word still blocks and the hint is set | `Check` |
| `wait_flag`, `timeout` | `Asleep` |
| `unlock_read`: the `fetch_sub`; `clear_flags` | `RCrit`, `Clear` |
| `unlock_write`: the swap to 0; `downgrade_lock`: the `fetch_add` | `WCrit` |
| `unpark_all`: the bucket section that empties the list, then one `notified` store per waiter | `Unpark`, `Notify` |

**MPMC queue** (`src/array_queue.rs`, model `src/progress/queue.rs`):

| Code | Model step |
| --- | --- |
| `push_atomic`'s load of `tail`, of the slot's stamp, its CAS on `tail`, its load of `head`, the confirming `fetch_add(0)`, and the stamp store | `PLoad`, `PStamp`, `PCas`, `PHead`, `PConfirm`, `PWrite` |
| `pop_atomic`'s, likewise on `head` and `tail` | `QLoad`, `QStamp`, `QCas`, `QTail`, `QConfirm`, `QRead` |
| `len`'s loads of `tail`, `head` and `tail` again | `LTail`, `LHead`, `LTail2` |

The queue's model is kept on unpacked positions and stamp ranks; the
invariant ties the model's slot ranks to the stamps' ghost phases
(`model_ok` in `src/array_queue.rs`).

**Fair lock** (`src/fair.rs`, model `src/progress/ticket.rs`):

| Code | Model step |
| --- | --- |
| `take_ticket`: the `fetch_add` on `next` | `Idle` to `Wait` |
| `poll`: a load of `serving`, which lets the thread in if it equals its ticket | `Wait` |
| `unlock`: the `fetch_add` on `serving` | `Crit` to `Idle` |

This model has 2^62 threads, a concrete number, so that `lemma_bound`
(fewer outstanding tickets than threads) lets the code compare tickets
mod 2^64. Here `pool_nonempty` says that fewer than 2^62 calls are in
progress on one lock at once.

**Handle counts** (`src/chan_sync.rs`, model `src/progress/handles.rs`),
one model per side of a channel, beside the channel's own:

| Code | Model step |
| --- | --- |
| `add_handle`'s load of the count, and each compare-and-swap | `Idle` to `Cas`, `Cas` |
| `drop_handle`'s `fetch_sub` | `Idle` (a drop) |

**Memory model.**

- The locks, the parking lot, the fair lock and the handle counts use
  only SeqCst atomics, so their models are sequentially consistent and
  exact.
- The channel is covered in the last section.
- The queue's loads are relaxed or acquire and can return an older
  value, and so can a failed CAS. The model allows exactly that: a step
  of a thread is either the sequentially consistent one (`sc_step`) or a
  load that read an older value (`stale_step`), which only sends the
  thread round its loop again. Lock-freedom then needs the memory system
  to be fair: once nothing is written any more, each thread's loads
  eventually read the latest values (`mfair`, a hypothesis of
  `theorem_lock_free`, shown satisfiable in `lemma_nonvacuous`). C++
  only encourages this ([intro.progress]: stores "should" become visible
  in a finite period of time); every hardware target provides it.

**Scheduling.** Fairness is weak: it does not say how often or in what
order threads run, only that none stops for good. A thread that never
runs again (killed, or blocked on something outside these primitives)
can block others: a lock holder that never unlocks, or a queue claimant
between its CAS and its stamp store. The models build in that every lock
holder unlocks (its next step is the unlock), and that each thread does
one lock operation at a time, so a thread waiting for a lock it already
holds is outside the theorems, as it deadlocks in parking_lot too.

## The parking lot

`src/lot.rs` is the global parking lot the mutex and the RwLock sleep in,
as parking_lot_core is for parking_lot: 64 buckets, each a list of
waiters behind a verified fair lock (`src/fair.rs`), shared by every lock
whose key hashes to it. Its list operations (search, push, removal) are verified. What the
locks' proofs need from it is the link between a bucket's contents and
their own ghost state, and that link is trusted:

- **`lock_bucket(key, k)`** locks the bucket and returns, besides the
  list, the lot's half of the asking lock's ghost `list` (the tickets of
  its waiters, which the lock's invariant holds the other half of),
  with `listed`: the waiters under `key` are this lock's and their
  tickets are exactly that list. It also returns the bucket's ghost map
  of the ids it has handed out (`bids`), so that a waiter that times out
  and finds an entry with its id knows the entry is its own.
- **`unlock_bucket`** takes both back and requires `listed` and `bids_ok`
  again, plus that waiters under other keys are as they were, so a
  critical section can change only its own lock's waiters, and only in
  step with its list.
- **Each lock's `key()`** returns the address of its lock word with a
  `KeyOf` that names the lock's ghost locations.

Why this is sound: the ghost halves are created out of nothing
(`Tracked::assume_new`) and taken back at unlock, so the claim is that at
most one of them is outstanding per lock (the bucket mutex ensures this)
and that it is the asking lock's. That rests on keys: a lock's waiters
each hold a borrow of the lock, so while any are listed the lock word
cannot move or be freed, and no other live lock word has the same
address. (Keying by the lock's address, as before, broke this: a lock at
offset 0 of another's data shares its address. That was a real bug, now
fixed and covered by `tests/nested_locks.rs`.) The `bids` map is one per
bucket (`bucket_loc`), so keys that share a bucket share it, and a
bucket hands out each id once.

## The channel: what is proven, and what is still assumed

The channel's progress theorems used to be about a model that was matched
to the code by hand. Now Verus checks the match, as it does for the
locks and the queue.

**How.** `src/model.rs` wraps a state of the model
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
   axiom outside `src/ra.rs`, shared with the locks and the queue). The model has `n` threads, and a call acts
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

3. **`std`, through three wrappers in `src/util.rs`.** `Unparker::unpark`
   and `park_for` have no specification at all: they only affect when a
   thread runs. `time_left` is trusted to report "late" only when there
   is a deadline. `Backoff` is used only to pause; the number of snoozes
   before a call registers is a verified counter (`chan_sync::SNOOZES`).
   The waiter lists' lock is no longer `std::sync::Mutex` but
   `fair::Lock`, whose mutual exclusion is proven (a guard dropped
   without `unlock` still aborts, so the invariant cannot be skipped).

4. **Scheduling, for the progress theorems to apply.** They hold for
   executions of the model in which every thread keeps taking steps. For
   the code this means: a thread that is not parked keeps running; a
   thread waiting for a waiter list's lock gets it, which
   `ticket::theorem_starvation_free` derives from the first (the critical
   sections are proven to terminate, and the model builds in that a
   holder unlocks); and a parked thread whose `notified` flag has been
   set runs again. The last depends on `notify` calling `unpark` after it stores
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
   provably cannot overflow. `handles::theorem_lock_free` proves that a
   retry means another clone or drop on the same side took effect, for
   the handle-count model the code is verified to follow.

What the theorems say is unchanged, and so is what they do not say: a
particular receiver can lose every race for a message.
