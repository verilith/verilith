// For benchmarking only: see the header of bin/chan/main.rs. This is the
// channel glue as it was before it was verified (src/chan_sync.rs).
//! Multi-producer multi-consumer channels with crossbeam-channel's API.
//!
//! The message path is the verified [`ArrayQueue`]: every message is
//! delivered exactly once, in the order of the sends' linearization points.
//! What is *not* verified is the glue in this file: sender and receiver
//! counting for disconnection, and parking threads that wait on a full or
//! empty channel. That glue only decides when to retry a verified operation
//! and when to give up, so a bug in it could lose a wakeup or report a
//! disconnection late, but could not corrupt or duplicate a message.
//!
//! The deciding itself is verified. Every call here is a loop ([`take`])
//! that makes one access to shared state and asks
//! [`crate::chan_core::next`] what to do next, and `chan_core` proves that
//! each such move is a step of the model whose progress theorems are in
//! `src/progress/channel.rs`. What this file adds, unverified, is the
//! accesses themselves: each arm of the loop must be the one access
//! `chan_core::reads` and `chan_core::writes` describe.
//!
//! Supported: `bounded(n)` for `n > 0`, `send`, `try_send`, `send_timeout`,
//! `recv`, `try_recv`, `recv_timeout`, `iter`, `try_iter`, `len`,
//! `is_empty`, `is_full`, `capacity`, cloning, and disconnection.
//! Not yet: `bounded(0)` (rendezvous), `unbounded()`, `select!`.
use super::cbsc::ArrayQueue;
use verilith_sync::chan_core::{next, Cfg, End, Pc};
use crossbeam_utils::Backoff;
use std::fmt;
use std::collections::VecDeque;
use std::sync::atomic::{fence, AtomicBool, AtomicUsize, Ordering::SeqCst};
use std::sync::{Arc, Mutex};
use std::thread::Thread;
use std::time::{Duration, Instant};

/// Threads parked until some condition may have changed.
///
/// A waiter adds itself to the list and clears `empty`, then re-checks its
/// condition, then parks; a notifier changes the state, then reads `empty`.
/// This is the store-buffering pattern, so it needs a single total order
/// over four accesses: the waiter's SeqCst store to `empty` followed by a
/// SeqCst fence before its re-check, and the notifier's SeqCst
/// read-modify-write of the queue (the head or tail CAS that claims a
/// position, or the SeqCst sender/receiver count decrement) followed by its
/// SeqCst load of `empty`. By the C++20 rules for SeqCst fences, either the
/// notifier's load sees the waiter or the waiter's re-check, whose loads
/// come after the fence, sees the change. The re-check's queue loads are
/// relaxed, so without the fence the waiter could miss the change while
/// the notifier misses the waiter (Miri finds this; see
/// `tests/lost_wakeup.rs`). The fence is on the cold path only. A notified
/// waiter is taken off the list at once, so notifiers stop paying for it
/// while it wakes up. `src/progress/channel.rs` proves that this protocol
/// never strands a waiter.
struct Waiters {
    empty: AtomicBool,
    list: Mutex<VecDeque<Arc<Waiter>>>,
}

struct Waiter {
    thread: Thread,
    notified: AtomicBool,
}

impl Waiters {
    fn new() -> Self {
        Waiters { empty: AtomicBool::new(true), list: Mutex::new(VecDeque::new()) }
    }

    #[inline]
    fn notify_one(&self) {
        self.run_notify(false);
    }

    #[inline]
    fn notify_all(&self) {
        self.run_notify(true);
    }

    /// `notify_one` (or `notify_all`): `Npc::Load`, then `Npc::Pop` if
    /// `chan_core::notify_next` says so.
    #[inline]
    fn run_notify(&self, all: bool) {
        if !self.empty.load(SeqCst) {
            self.notify(all);
        }
    }

    /// `Npc::Pop` and `Pc::PassPop`: one critical section that takes the
    /// first waiter (or every waiter) off the list and sets its flag.
    #[cold]
    fn notify(&self, all: bool) {
        let mut list = self.list.lock().unwrap();
        while let Some(w) = list.pop_front() {
            w.notified.store(true, SeqCst);
            w.thread.unpark();
            if !all {
                break;
            }
        }
        self.empty.store(list.is_empty(), SeqCst);
    }

    /// `Pc::Reg`: one critical section that adds this thread to the list.
    #[cold]
    fn register(&self) -> Arc<Waiter> {
        let me = Arc::new(Waiter { thread: std::thread::current(), notified: AtomicBool::new(false) });
        {
            let mut list = self.list.lock().unwrap();
            list.push_back(me.clone());
            self.empty.store(false, SeqCst);
        }
        // Orders the store to `empty` before the re-check's relaxed loads.
        fence(SeqCst);
        me
    }

    /// `Pc::Park`: reads the waiter's flag and, if it is clear, sleeps
    /// until unparked or until the deadline. Returns the flag and whether
    /// the deadline has passed.
    #[cold]
    fn park(me: &Waiter, deadline: Option<Instant>) -> (bool, bool) {
        if me.notified.load(SeqCst) {
            return (true, false);
        }
        match deadline {
            None => std::thread::park(),
            Some(d) => {
                let now = Instant::now();
                if now >= d {
                    return (false, true);
                }
                std::thread::park_timeout(d - now);
            }
        }
        (false, false)
    }

    /// `Pc::Remove` and `Pc::Timeout`: one critical section that takes `me`
    /// off the list. Returns false if a notifier already did.
    fn remove(&self, me: &Arc<Waiter>) -> bool {
        let mut list = self.list.lock().unwrap();
        let found = match list.iter().position(|w| Arc::ptr_eq(w, me)) {
            Some(i) => {
                list.remove(i);
                true
            }
            None => false,
        };
        self.empty.store(list.is_empty(), SeqCst);
        found
    }
}

struct Chan<T> {
    queue: ArrayQueue<T>,
    senders: AtomicUsize,
    receivers: AtomicUsize,
    /// Receivers waiting for a message.
    recv_waiters: Waiters,
    /// Senders waiting for space.
    send_waiters: Waiters,
}

impl<T> Chan<T> {
    #[inline]
    fn senders_gone(&self) -> bool {
        self.senders.load(SeqCst) == 0
    }

    #[inline]
    fn receivers_gone(&self) -> bool {
        self.receivers.load(SeqCst) == 0
    }
}

/// One take: a receive (`take` pops) or a send (`take` pushes).
///
/// The loop is an interpreter for `chan_core::next`. Each arm makes the
/// one access to shared state its `Pc` names and reports what it read;
/// `next` decides everything else, and `chan_core::theorem_next_refines`
/// proves each move is a step of the progress model. `gone` reads the
/// other side's handle count, `take` is the queue operation (followed, on
/// success, by the notification to the other side's waiters), and `avail`
/// is the re-check of the queue's length.
#[inline]
fn take<R>(
    waiters: &Waiters,
    cfg: Cfg,
    deadline: Option<Instant>,
    gone: impl Fn() -> bool,
    mut take: impl FnMut() -> Option<R>,
    avail: impl Fn() -> bool,
) -> Result<R, End> {
    let mut pc = Pc::Gone;
    let mut out = None;
    loop {
        pc = match pc {
            Pc::Gone => next(pc, cfg, gone(), false),
            Pc::Take { .. } => {
                out = take();
                if out.is_some() || cfg.nonblocking {
                    next(pc, cfg, out.is_some(), false)
                } else {
                    return slow(waiters, cfg, deadline, pc, gone, take, avail);
                }
            }
            Pc::Done(End::Taken) => return Ok(out.unwrap()),
            Pc::Done(e) => return Err(e),
            // A waiting call continues in `slow`.
            _ => unreachable!(),
        };
    }
}

/// [`take`] from its first failed attempt on: the part that snoozes,
/// registers, parks and times out. The same interpreter, with every `Pc`.
#[cold]
fn slow<R>(
    waiters: &Waiters,
    cfg: Cfg,
    deadline: Option<Instant>,
    mut pc: Pc,
    gone: impl Fn() -> bool,
    mut take: impl FnMut() -> Option<R>,
    avail: impl Fn() -> bool,
) -> Result<R, End> {
    let backoff = Backoff::new();
    let mut me: Option<Arc<Waiter>> = None;
    let mut out = None;
    loop {
        pc = match pc {
            Pc::Gone => next(pc, cfg, gone(), false),
            Pc::Take { .. } => {
                // On entry this arm stands for the attempt `take` just
                // made, which failed.
                let snooze = out.is_none() && !backoff.is_completed();
                let p = next(pc, cfg, out.is_some(), snooze);
                if p == Pc::Gone {
                    backoff.snooze();
                }
                p
            }
            Pc::Reg => {
                me = Some(waiters.register());
                next(pc, cfg, false, false)
            }
            Pc::Ready1 => next(pc, cfg, gone(), false),
            Pc::Ready2 => next(pc, cfg, avail(), false),
            Pc::Remove => {
                waiters.remove(me.as_ref().unwrap());
                next(pc, cfg, false, false)
            }
            Pc::Park => {
                let (notified, late) = Waiters::park(me.as_ref().unwrap(), deadline);
                next(pc, cfg, notified, late)
            }
            Pc::Timeout => next(pc, cfg, waiters.remove(me.as_ref().unwrap()), false),
            Pc::Pass => next(pc, cfg, waiters.empty.load(SeqCst), false),
            Pc::PassPop => {
                waiters.notify(false);
                next(pc, cfg, false, false)
            }
            Pc::Done(End::Taken) => return Ok(out.unwrap()),
            Pc::Done(e) => return Err(e),
        };
        // The access for `Take` is made here, so that the arm above sees
        // its result.
        if let Pc::Take { .. } = pc {
            out = take();
        }
    }
}

/// Creates a channel that holds up to `cap` messages.
///
/// # Panics
///
/// If `cap` is zero (rendezvous channels are not supported yet) or at least
/// 2^31.
pub fn bounded<T>(cap: usize) -> (Sender<T>, Receiver<T>) {
    assert!(cap > 0, "vsync does not support zero-capacity channels yet");
    let chan = Arc::new(Chan {
        queue: ArrayQueue::new(cap),
        senders: AtomicUsize::new(1),
        receivers: AtomicUsize::new(1),
        recv_waiters: Waiters::new(),
        send_waiters: Waiters::new(),
    });
    (Sender { chan: chan.clone() }, Receiver { chan })
}

/// The sending side of a channel.
pub struct Sender<T> {
    chan: Arc<Chan<T>>,
}

/// The receiving side of a channel.
pub struct Receiver<T> {
    chan: Arc<Chan<T>>,
}

impl<T> Sender<T> {
    /// One send: `try_send` when `nonblocking`.
    #[inline]
    fn send_as(&self, msg: T, nonblocking: bool, deadline: Option<Instant>) -> Result<(), (T, End)> {
        let chan = &*self.chan;
        let mut slot = Some(msg);
        let r = take(
            &chan.send_waiters,
            Cfg { nonblocking, stop_when_gone: true },
            deadline,
            || chan.receivers_gone(),
            || match chan.queue.push(slot.take().unwrap()) {
                Ok(()) => {
                    chan.recv_waiters.notify_one();
                    Some(())
                }
                Err(m) => {
                    slot = Some(m);
                    None
                }
            },
            || chan.queue.len() < chan.queue.capacity(),
        );
        match r {
            Ok(()) => Ok(()),
            Err(e) => Err((slot.unwrap(), e)),
        }
    }

    /// Sends without blocking.
    pub fn try_send(&self, msg: T) -> Result<(), TrySendError<T>> {
        self.send_as(msg, true, None).map_err(|(m, e)| match e {
            End::Disconnected => TrySendError::Disconnected(m),
            _ => TrySendError::Full(m),
        })
    }

    fn send_deadline(&self, msg: T, deadline: Option<Instant>) -> Result<(), SendTimeoutError<T>> {
        self.send_as(msg, false, deadline).map_err(|(m, e)| match e {
            End::Disconnected => SendTimeoutError::Disconnected(m),
            _ => SendTimeoutError::Timeout(m),
        })
    }

    /// Sends, blocking while the channel is full.
    pub fn send(&self, msg: T) -> Result<(), SendError<T>> {
        self.send_deadline(msg, None).map_err(|e| match e {
            SendTimeoutError::Disconnected(m) => SendError(m),
            SendTimeoutError::Timeout(_) => unreachable!(),
        })
    }

    /// Sends, blocking for at most `timeout` while the channel is full.
    pub fn send_timeout(&self, msg: T, timeout: Duration) -> Result<(), SendTimeoutError<T>> {
        self.send_deadline(msg, Some(Instant::now() + timeout))
    }

    /// Sends, blocking until `deadline` at the latest while the channel is full.
    pub fn send_deadline_at(&self, msg: T, deadline: Instant) -> Result<(), SendTimeoutError<T>> {
        self.send_deadline(msg, Some(deadline))
    }

    pub fn is_empty(&self) -> bool {
        self.chan.queue.len() == 0
    }

    pub fn is_full(&self) -> bool {
        self.chan.queue.len() == self.chan.queue.capacity()
    }

    pub fn len(&self) -> usize {
        self.chan.queue.len()
    }

    pub fn capacity(&self) -> Option<usize> {
        Some(self.chan.queue.capacity())
    }

    /// Whether two senders belong to the same channel.
    pub fn same_channel(&self, other: &Sender<T>) -> bool {
        Arc::ptr_eq(&self.chan, &other.chan)
    }
}

impl<T> Receiver<T> {
    /// One receive: `try_recv` when `nonblocking`.
    #[inline]
    fn recv_as(&self, nonblocking: bool, deadline: Option<Instant>) -> Result<T, End> {
        let chan = &*self.chan;
        // The sender count is read before the pop (`Pc::Gone`, then
        // `Pc::Take`): if it is zero, every send has finished, so an empty
        // queue afterwards means no more messages.
        take(
            &chan.recv_waiters,
            Cfg { nonblocking, stop_when_gone: false },
            deadline,
            || chan.senders_gone(),
            || {
                let m = chan.queue.pop();
                if m.is_some() {
                    chan.send_waiters.notify_one();
                }
                m
            },
            || chan.queue.len() > 0,
        )
    }

    /// Receives without blocking.
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        self.recv_as(true, None).map_err(|e| match e {
            End::Disconnected => TryRecvError::Disconnected,
            _ => TryRecvError::Empty,
        })
    }

    fn recv_deadline(&self, deadline: Option<Instant>) -> Result<T, RecvTimeoutError> {
        self.recv_as(false, deadline).map_err(|e| match e {
            End::Disconnected => RecvTimeoutError::Disconnected,
            _ => RecvTimeoutError::Timeout,
        })
    }

    /// Receives, blocking while the channel is empty. Fails once the channel
    /// is empty and every sender has been dropped.
    pub fn recv(&self) -> Result<T, RecvError> {
        self.recv_deadline(None).map_err(|_| RecvError)
    }

    /// Receives, blocking for at most `timeout` while the channel is empty.
    pub fn recv_timeout(&self, timeout: Duration) -> Result<T, RecvTimeoutError> {
        self.recv_deadline(Some(Instant::now() + timeout))
    }

    /// Receives, blocking until `deadline` at the latest while the channel is empty.
    pub fn recv_deadline_at(&self, deadline: Instant) -> Result<T, RecvTimeoutError> {
        self.recv_deadline(Some(deadline))
    }

    /// Blocks for each message until the channel is disconnected.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { rx: self }
    }

    /// The messages available now, without blocking.
    pub fn try_iter(&self) -> TryIter<'_, T> {
        TryIter { rx: self }
    }

    pub fn is_empty(&self) -> bool {
        self.chan.queue.len() == 0
    }

    pub fn is_full(&self) -> bool {
        self.chan.queue.len() == self.chan.queue.capacity()
    }

    pub fn len(&self) -> usize {
        self.chan.queue.len()
    }

    pub fn capacity(&self) -> Option<usize> {
        Some(self.chan.queue.capacity())
    }

    /// Whether two receivers belong to the same channel.
    pub fn same_channel(&self, other: &Receiver<T>) -> bool {
        Arc::ptr_eq(&self.chan, &other.chan)
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.chan.senders.fetch_add(1, SeqCst);
        Sender { chan: self.chan.clone() }
    }
}

impl<T> Clone for Receiver<T> {
    fn clone(&self) -> Self {
        self.chan.receivers.fetch_add(1, SeqCst);
        Receiver { chan: self.chan.clone() }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        if self.chan.senders.fetch_sub(1, SeqCst) == 1 {
            self.chan.recv_waiters.notify_all();
        }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        if self.chan.receivers.fetch_sub(1, SeqCst) == 1 {
            self.chan.send_waiters.notify_all();
        }
    }
}

impl<T> fmt::Debug for Sender<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Sender { .. }")
    }
}

impl<T> fmt::Debug for Receiver<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Receiver { .. }")
    }
}

pub struct Iter<'a, T> {
    rx: &'a Receiver<T>,
}

impl<T> Iterator for Iter<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.rx.recv().ok()
    }
}

pub struct TryIter<'a, T> {
    rx: &'a Receiver<T>,
}

impl<T> Iterator for TryIter<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.rx.try_recv().ok()
    }
}

pub struct IntoIter<T> {
    rx: Receiver<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.rx.recv().ok()
    }
}

impl<T> IntoIterator for Receiver<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { rx: self }
    }
}

impl<'a, T> IntoIterator for &'a Receiver<T> {
    type Item = T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

// Errors, shaped like crossbeam-channel's.

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct SendError<T>(pub T);

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum TrySendError<T> {
    Full(T),
    Disconnected(T),
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum SendTimeoutError<T> {
    Timeout(T),
    Disconnected(T),
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct RecvError;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum TryRecvError {
    Empty,
    Disconnected,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum RecvTimeoutError {
    Timeout,
    Disconnected,
}

impl<T> SendError<T> {
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> TrySendError<T> {
    pub fn into_inner(self) -> T {
        match self {
            TrySendError::Full(v) | TrySendError::Disconnected(v) => v,
        }
    }
    pub fn is_full(&self) -> bool {
        matches!(self, TrySendError::Full(_))
    }
    pub fn is_disconnected(&self) -> bool {
        matches!(self, TrySendError::Disconnected(_))
    }
}

impl<T> SendTimeoutError<T> {
    pub fn into_inner(self) -> T {
        match self {
            SendTimeoutError::Timeout(v) | SendTimeoutError::Disconnected(v) => v,
        }
    }
    pub fn is_timeout(&self) -> bool {
        matches!(self, SendTimeoutError::Timeout(_))
    }
    pub fn is_disconnected(&self) -> bool {
        matches!(self, SendTimeoutError::Disconnected(_))
    }
}

impl TryRecvError {
    pub fn is_empty(&self) -> bool {
        matches!(self, TryRecvError::Empty)
    }
    pub fn is_disconnected(&self) -> bool {
        matches!(self, TryRecvError::Disconnected)
    }
}

impl RecvTimeoutError {
    pub fn is_timeout(&self) -> bool {
        matches!(self, RecvTimeoutError::Timeout)
    }
    pub fn is_disconnected(&self) -> bool {
        matches!(self, RecvTimeoutError::Disconnected)
    }
}

impl<T> fmt::Debug for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("SendError(..)")
    }
}

impl<T> fmt::Debug for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrySendError::Full(_) => f.pad("Full(..)"),
            TrySendError::Disconnected(_) => f.pad("Disconnected(..)"),
        }
    }
}

impl<T> fmt::Debug for SendTimeoutError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SendTimeoutError::Timeout(_) => f.pad("Timeout(..)"),
            SendTimeoutError::Disconnected(_) => f.pad("Disconnected(..)"),
        }
    }
}

impl<T> fmt::Display for SendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "sending on a disconnected channel".fmt(f)
    }
}

impl<T> fmt::Display for TrySendError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrySendError::Full(_) => "sending on a full channel".fmt(f),
            TrySendError::Disconnected(_) => "sending on a disconnected channel".fmt(f),
        }
    }
}

impl<T> fmt::Display for SendTimeoutError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SendTimeoutError::Timeout(_) => "timed out waiting on send operation".fmt(f),
            SendTimeoutError::Disconnected(_) => "sending on a disconnected channel".fmt(f),
        }
    }
}

impl fmt::Display for RecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "receiving on an empty and disconnected channel".fmt(f)
    }
}

impl fmt::Display for TryRecvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TryRecvError::Empty => "receiving on an empty channel".fmt(f),
            TryRecvError::Disconnected => "receiving on an empty and disconnected channel".fmt(f),
        }
    }
}

impl fmt::Display for RecvTimeoutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RecvTimeoutError::Timeout => "timed out waiting on receive operation".fmt(f),
            RecvTimeoutError::Disconnected => "channel is empty and disconnected".fmt(f),
        }
    }
}

impl<T> std::error::Error for SendError<T> {}
impl<T> std::error::Error for TrySendError<T> {}
impl<T> std::error::Error for SendTimeoutError<T> {}
impl std::error::Error for RecvError {}
impl std::error::Error for TryRecvError {}
impl std::error::Error for RecvTimeoutError {}
