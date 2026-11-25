# verilith-sync

Concurrency primitives for Rust, formally verified with
[Verus](https://github.com/verus-lang/verus): a single-producer queue, a
multi-producer multi-consumer queue, channels built on it, a mutex and a
reader-writer lock. Each one stands in for the crate people already use:
rtrb (in spirit: the constructor and error types differ), crossbeam-queue's `ArrayQueue`, crossbeam-channel's `bounded`,
and parking_lot's `Mutex` and `RwLock`.

The queues are proven **linearizable** against a plain sequence: each push
and pop takes effect atomically at one instant between its call and its
return, and does to the queue exactly what `Seq::push` and
`Seq::drop_first` say. The locks are proven to give **mutual exclusion**:
a write guard excludes every other guard, and read guards only ever share
the data. Everything is proven **memory safe**: no data races on the
values, no use of a slot before it is written or after it is read, and
every value dropped exactly once.

The queues are verified against a **release/acquire memory model**
(`src/ra.rs`, after ORC11), not just sequential consistency, so they use
the same orderings as the crates they replace: Release stores, Acquire
loads, AcqRel read-modify-writes (the queue's head/tail CAS and the
read-modify-writes that confirm it full or empty are SeqCst, which the
channel's wakeup handshake needs). Verus itself only models sequentially
consistent atomics; [TRUST.md](https://github.com/verilith/verilith/blob/main/crates/sync/TRUST.md) states the model's axioms and
argues they are sound.

With those orderings the queues run about as fast as the originals: the
SPSC queue beats rtrb one item at a time, and the MPMC queue and channel
are within a few percent of crossbeam on a noisy machine. The locks are
faster than parking_lot in every contended configuration measured but one
(two threads on a mutex), and tie uncontended.

## Usage

The proofs hold for 64-bit and for 32-bit targets (wasm32 included):
`scripts/verify.sh sync` checks the first and `crates/sync/scripts/verify-narrow.sh`
the second. Positions stay 64-bit on both, so the no-ABA argument below
is the same. The crate builds for wasm32-unknown-unknown; its tests spawn
threads, which wasm32-wasip1 does not have, so they run natively only.

```rust
// Instead of parking_lot::{Mutex, RwLock}:
use verilith_sync::mutex::Mutex;
use verilith_sync::rwlock::{RwLock, RwLockWriteGuard};

let m = Mutex::new(0);
*m.lock() += 1;
if let Some(mut g) = m.try_lock_for(std::time::Duration::from_millis(10)) {
    *g += 1;
}

let l = RwLock::new(vec![1, 2, 3]);
let total: i32 = l.read().iter().sum();
let mut w = l.write();
w.push(total);
let r = RwLockWriteGuard::downgrade(w); // no writer can get in between
assert_eq!(r.len(), 4);
drop(r);

// Instead of crossbeam_channel::bounded:
let (tx, rx) = verilith_sync::channel::bounded(1024);
std::thread::spawn(move || {
    for i in 0..10 {
        tx.send(i).unwrap();
    }
});
assert_eq!(rx.iter().sum::<i32>(), 45);

// Instead of crossbeam_queue::ArrayQueue:
let q = verilith_sync::array_queue::ArrayQueue::new(64);
q.push(1).unwrap();
assert_eq!(q.pop(), Some(1));

// Like rtrb::RingBuffer (the third value is the ghost queue view, which
// only verified callers use):
let (mut p, mut c, _) = verilith_sync::spsc::new(64);
p.push(1).unwrap();
assert_eq!(c.pop(), Some(1));
```

## What is proven

Checked by Verus: `cargo verus verify` reports 350 items verified, 0
errors, with no `assume` or `admit` anywhere in the crate. The queue rows
hold under the release/acquire model of `src/ra.rs`; the lock rows under
vstd's sequentially consistent atomics. The progress rows at the end are
proved about models of the protocols, as explained below the table; for
the channel, the code is verified to follow its model.

| Property | Where |
| --- | --- |
| **SPSC batches are linearizable**: `push_slice` appends a prefix of the slice and `pop_into` removes a prefix of the queue, each at one atomic step and with one index store; neither comes back empty-handed unless the queue was full (or empty) at that step | `Producer::push_slice`, `Consumer::pop_into` |
| **SPSC queue is linearizable**: `push` and `pop` are *logically atomic* against a ghost `Seq<T>` the caller holds; each one updates it exactly as `Seq::push` / `Seq::drop_first` at a single atomic step (the Release index store, or the read-modify-write that confirms the queue full or empty after an Acquire load suggested it) | `src/spsc.rs` |
| **MPMC queue is linearizable**, with the same spec, for any number of threads. It is crossbeam's `ArrayQueue` algorithm (Vyukov's bounded queue: per-slot stamps, head and tail CAS). The proof gives each slot a ghost phase (free, claimed, full, taken), hands each slot's cell from thread to thread through the Release stamp store and the Acquire stamp load that reads it, and carries "this stamp was at least *s* when I read it" across atomic steps with history snapshots and a monotonic-counter resource | `src/array_queue.rs`, `src/mono.rs` |
| **No data races under release/acquire**: a cell is touched only by a thread whose view covers the store that handed the cell over, so every write to it happens-before the next access | `Published` in `src/ra.rs` |
| **No ABA**: positions are 64-bit and never wrap; a push or pop that would overflow aborts instead, which takes over 2^63 operations on one queue. This is what lets the proof treat a successful CAS as "nothing happened since my load" | `ArrayQueue::push`, `util::exhausted` |
| **Queue memory safety**: a slot's value is written only by the push that claimed it and read only by the pop that claimed it, after the push finished; values left in a queue are dropped exactly once when it is dropped (for SPSC, by whichever side is dropped last, decided by an AcqRel refcount) | `slot_inv`, `ArrayQueue::destroy`, `Producer::leave`, `Consumer::leave` |
| **`len()` is in range**: never more than the capacity, even while racing | `ArrayQueue::len` |
| **Mutex excludes**: the data is reachable only through a guard, and a guard exists only while the lock word is nonzero, which only one thread can change from zero. The lock word is Drepper's three-state futex mutex | `src/mutex.rs` |
| **RwLock excludes**: one 32-bit word holds the writer bit, two parking hints and the reader count. A tokenized state machine (writer token, reader tokens, data in storage) proves a writer holds the data alone and readers borrow it shared, and that the bits always match the tokens. `downgrade` turns a write lock into a read lock in one atomic step | `src/rwlock.rs` |
| **Locks drop the data exactly once**, and `into_inner` returns it | `Mutex::take_inner`, `RwLock::take_inner` |
| **SPSC is wait-free**: every SPSC function passes Verus's termination check, so each call returns after a bounded number of its own steps whatever the other side does. So do `try_lock`, `try_read`, `try_write`, the unlocks and `downgrade` | `src/spsc.rs` (no loop is exempt) |
| **Mutex never deadlocks**: while a thread waits in `lock()`, some thread holds the lock later. No lost wakeups: while anyone sleeps in the parking lot, the word says "contended" or some thread is committed to waking a sleeper or re-marking the word | `progress::mutex` |
| **RwLock never deadlocks**: likewise for `read()` and `write()`. The parking hints are never left set with nobody to clear them, and a sleeper is never left with "parked" clear and nobody to wake it | `progress::rwlock` |
| **Channel waiters are never stranded**: if a message is queued while a receiver waits (or a slot is free while a sender waits), some receiver (sender) takes it, unless the waiter returns or the other side disconnects; and once the other side is gone, every waiter returns | `progress::channel`, and `src/chan_sync.rs` for the code following the model |
| **MPMC queue is lock-free under fair scheduling**: while a thread is in `push`, `pop` or `len`, some call returns | `progress::queue` |

The progress rows hold in every execution in which each thread keeps
getting scheduled; nothing else is assumed about timing. Each blocking
protocol is modeled one step per atomic access. For the locks and the
queue, `TRUST.md` ("Progress") maps the model to the code line by line,
by hand. For the channel the mapping is checked by Verus: the channel's
blocking code (`src/chan_sync.rs`: the handle counts, the waiter lists,
the send and receive loops, clone and drop) holds the model's state as a
ghost resource that can only change by a step of the model, inside an
invariant that ties it to the real atomics and the queue, so every access
the code makes to shared state has to be a step of the model. What that
still assumes is listed in `TRUST.md` ("The channel"): mainly that
SeqCst operations interleave, that `std`'s mutex excludes, and that a
bounded number of calls run at once. These are deadlock-freedom results, not fairness ones: a
particular thread can still lose every race, as with parking_lot and
crossbeam. Writing the channel proof found a real lost-wakeup bug that the
move to release/acquire had introduced (a receiver could park next to a
message, on ARM or under Miri), now fixed and covered by
`tests/lost_wakeup.rs`.

## Trusted computing base

[TRUST.md](https://github.com/verilith/verilith/blob/main/crates/sync/TRUST.md) lists everything assumed rather than proven and
argues for each item. In short:

- Verus, Z3 and the Rust compiler.
- vstd: cells, invariants, ghost resources, logically atomic triples, and
  the SC atomics the locks use.
- The release/acquire model in `src/ra.rs`: its axioms, and the claim that
  each `Objective` type holds no thread-relative resources. The model is
  ORC11's, with one strengthening (stores append to the history), which is
  the "strong release/acquire" model that x86, ARMv8 and POWER implement.
- The specs: read `QueueView`, the `atomically` blocks on the queue
  operations, and the `RwToks` state machine to check that they say what
  you expect.
- Unverified, with no access to the data: `src/util.rs`, `src/parking.rs`
  (which now includes thin wrappers around `std`'s mutex, park/unpark and
  clock for the channel) and the locks' park/unpark wrappers, the
  channel's public shell in `src/channel.rs`, which only forwards to the
  verified `src/chan_sync.rs`, and the one-line `Send`, `Sync`, `Deref`
  and `Drop` impls. The tests run under Miri in CI, with its weak-memory
  emulation.
- The progress models. For the mutex, the RwLock and the queue, their
  match with the code is argued, not proven. For the channel it is
  proven, up to the assumptions `TRUST.md` lists under "The channel": one
  axiom (boundedly many calls in progress at once), sequentially
  consistent interleaving of the SeqCst operations the proof relies on,
  mutual exclusion from `std::sync::Mutex`, and, for progress only, that
  `unpark` wakes a parked thread and the mutex is eventually acquired.

## The memory model

Verus's atomics are sequentially consistent, and a proof against them only
covers SeqCst code. That costs nothing for locks, which do their work with
read-modify-writes (the same instruction either way on x86), so the locks
are verified that way. For queues it is expensive: an SC store is an
`xchg` on x86, and in the first version of verilith-sync the SeqCst index and stamp
stores made the SPSC queue 2.6x slower than rtrb and the MPMC queue up to
1.8x slower than crossbeam.

So the queues are verified against `src/ra.rs`, a release/acquire model
following ORC11 (Dang et al., POPL 2020). Each atomic has a history of
messages carrying views. A Release store publishes the thread's view, an
Acquire load joins the view of the message it read, and an RMW always
reads the latest message. Cell permissions cross threads only inside
`Published`, which hands them only to a thread whose view covers the
publisher's. Shared invariants may hold only objective resources.

Release/acquire loads can read stale values, so "the queue is full" can't
be decided by a load. Where verilith-sync used a load as the linearization point,
it now uses a plain load (Acquire in SPSC, relaxed in MPMC) to suggest full
(or empty), then confirms with
an AcqRel `fetch_add(0)`, which reads the latest value. That only happens
when the queue looks full or empty.

## Performance

4-vCPU Xeon @ 2.8 GHz (a shared cloud VM, so noisy), Rust 1.99.1,
`lto = "fat"`, `codegen-units = 1`. Every implementation runs in its own
process, rounds alternate between implementations, and each figure is the
median over the rounds (`bench/run.py`). Versions are pinned in
`bench/Cargo.toml`: rtrb 0.3.2, crossbeam-queue 0.3.12,
crossbeam-channel 0.5.15, parking_lot 0.12.4. Lower is better.

**Locks** (ns per lock/unlock pair; T threads, each doing W increments
inside the lock):

| Mutex | verilith-sync | parking_lot | std |
| --- | ---: | ---: | ---: |
| 1 thread | 14.4 | 15.4 | 16.1 |
| 2 threads | 39.1 | 33.5 | 75.5 |
| 4 threads | 41.6 | 62.3 | 110.0 |
| 8 threads | 42.6 | 49.8 | 115.0 |
| 4 threads, W=20 | 80.2 | 126.0 | 205.2 |

| RwLock (ns per op) | verilith-sync | parking_lot | std |
| --- | ---: | ---: | ---: |
| 1 thread, reads only | 19.2 | 19.4 | 19.2 |
| 4 threads, reads only | 68.0 | 70.6 | 104.7 |
| 4 threads, 1% writes | 59.5 | 84.9 | 84.9 |
| 4 threads, 10% writes | 63.8 | 95.3 | 79.3 |
| 4 threads, writes only | 42.7 | 61.0 | 81.3 |
| 8 threads, 10% writes | 70.3 | 90.7 | 89.9 |

**SPSC queue** (ns per item, producer and consumer pinned to two cores,
capacity 1024; batches of 64 use `push_slice`/`pop_into` and rtrb's
`write_chunk_uninit`/`read_chunk`):

| | verilith-sync | rtrb |
| --- | ---: | ---: |
| one item at a time | 27.9 | 30.8 |
| batches of 64 | 2.9 | 2.5 |

With SeqCst index stores (the first, SC-only version) verilith-sync took 70.5 ns
per item.

**MPMC queue** (ns per item, P producers and C consumers, capacity 1024):

| | verilith-sync `ArrayQueue` | crossbeam `ArrayQueue` | verilith-sync, SC-only version |
| --- | ---: | ---: | ---: |
| 1p1c | 65.8 | 68.0 | 55.4 |
| 2p2c | 182.3 | 163.9 | 250.2 |
| 3p1c | 226.1 | 218.8 | 366.6 |
| 1p3c | 278.5 | 262.5 | 341.4 |

**Bounded channel** (ns per message, blocking `send`/`recv`, capacity
1024). `xglue` is a control that runs the channel code verilith-sync had before
it was verified over crossbeam's queue:

| | verilith-sync | xglue | crossbeam-channel |
| --- | ---: | ---: | ---: |
| 1p1c | 25.0 | 28.6 | 21.9 |
| 2p2c | 79.3 | 96.3 | 186.4 |
| 3p1c | 163.3 | 202.4 | 245.5 |
| 1p3c | 347.0 | 359.0 | 311.7 |

(This table was re-measured, median of five runs, when the channel's
blocking code was verified; the VM was a different one from the other
tables', so compare within the table only.)

Contended queue numbers move by 10-20% between runs on this VM. Read
differences smaller than that as ties.

## Departures from the crates it replaces

- **parking_lot**: no `const fn new`, no fair unlocking (`unlock_fair`) and
  no eventual fairness: verilith-sync's mutex never hands the lock to a waiter
  directly, which is part of why it is faster under contention. No
  `MutexGuard::map`, no upgradable reads, no `get_mut` on the lock itself
  (use `lock()`, which is one uncontended CAS), and no reentrant mutex.
  `into_inner` panics if a guard was leaked with `mem::forget`, since the
  value went with the guard. The RwLock prefers writers: a waiting writer
  holds off new readers.
- **crossbeam-channel**: `bounded(n)` for `n > 0` only. No `unbounded()`,
  zero-capacity rendezvous channels or `select!` yet.
- **crossbeam-queue**: `ArrayQueue` has no `force_push`.
- **rtrb**: `spsc::new(cap)` returns the producer and consumer (and the
  ghost view); `push` fails with `Err(value)` and `pop` returns an
  `Option`, where rtrb has its own error types. Batches go through
  `push_slice(&[T])` (for `T: Copy`) and `pop_into(&mut Vec<T>, max)`
  instead of rtrb's chunk types. No `slots()` or `is_abandoned()`.

## Related work

Verus ships examples of verified concurrent data structures, including a
spin-based RwLock in vstd (two separate atomics, no parking) and
logically-atomic queue examples. IronSync (OSDI 2022, in Linear Dafny)
verified concurrent systems code with the same tokenized-state-machine
style. verus-mimalloc verified a memory allocator. verilith-sync is, as far as we
know, the first to verify the primitives Rust programs actually depend on,
in the form they use them: the crossbeam ArrayQueue algorithm with
linearizability rather than just safety, single-word parking locks with
parking_lot's API, and channels on top, measured against the crates they
replace. Release/acquire program logics exist (RSL, GPS, iRC11 in Iris);
verilith-sync brings one into Verus's automated setting, as a small trusted
library, and uses it on production queue algorithms.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/sync/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/sync/LICENSE-MIT), at your option.
