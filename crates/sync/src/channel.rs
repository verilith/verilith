//! Multi-producer multi-consumer channels with crossbeam-channel's API.
//!
//! The message path is the verified [`ArrayQueue`](crate::array_queue):
//! every message is delivered exactly once, in the order of the sends'
//! linearization points. The blocking protocol (counting senders and
//! receivers for disconnection, and blocking threads that wait on a full or
//! empty channel) is `src/chan_sync.rs`, which is verified too: every
//! access it makes to shared state is checked to be a step of the model
//! whose progress theorems are in `src/progress/channel.rs`, so a waiter
//! is never left asleep next to a message, a free slot, or a disconnected
//! channel.
//!
//! This file is the part that is not verified: the public types and their
//! trait impls, which only forward to `chan_sync::Handle`. What the proof
//! asks of it is that each handle is cloned with `clone_handle`, given up
//! with `disconnect` exactly once (in `drop`), and that a sender only
//! sends and a receiver only receives.
//!
//! Supported: `bounded(n)` for `n > 0`, `send`, `try_send`, `send_timeout`,
//! `recv`, `try_recv`, `recv_timeout`, `iter`, `try_iter`, `len`,
//! `is_empty`, `is_full`, `capacity`, cloning, and disconnection.
//! Not yet: `bounded(0)` (rendezvous), `unbounded()`, `select!`.
use crate::chan_core::End;
use crate::chan_sync::Handle;
use crate::util::Deadline;
use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Creates a channel that holds up to `cap` messages.
///
/// # Panics
///
/// If `cap` is zero (rendezvous channels are not supported yet) or at least
/// 2^31.
pub fn bounded<T>(cap: usize) -> (Sender<T>, Receiver<T>) {
    assert!(cap > 0, "vsync does not support zero-capacity channels yet");
    assert!(cap < 0x8000_0000, "capacity must be below 2^31");
    let (tx, rx) = Handle::pair(cap);
    (Sender { h: tx }, Receiver { h: rx })
}

/// The sending side of a channel.
pub struct Sender<T> {
    h: Handle<T>,
}

/// The receiving side of a channel.
pub struct Receiver<T> {
    h: Handle<T>,
}

impl<T> Sender<T> {
    /// Sends without blocking.
    pub fn try_send(&self, msg: T) -> Result<(), TrySendError<T>> {
        self.h.send_as(msg, true, Deadline(None)).map_err(|(m, e)| match e {
            End::Disconnected => TrySendError::Disconnected(m),
            _ => TrySendError::Full(m),
        })
    }

    fn send_deadline(&self, msg: T, deadline: Option<Instant>) -> Result<(), SendTimeoutError<T>> {
        self.h.send_as(msg, false, Deadline(deadline)).map_err(|(m, e)| match e {
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
        self.h.chan.queue.len() == 0
    }

    pub fn is_full(&self) -> bool {
        self.h.chan.queue.len() == self.h.chan.queue.capacity()
    }

    pub fn len(&self) -> usize {
        self.h.chan.queue.len()
    }

    pub fn capacity(&self) -> Option<usize> {
        Some(self.h.chan.queue.capacity())
    }

    /// Whether two senders belong to the same channel.
    pub fn same_channel(&self, other: &Sender<T>) -> bool {
        Arc::ptr_eq(&self.h.chan, &other.h.chan)
    }
}

impl<T> Receiver<T> {
    /// Receives without blocking.
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        self.h.recv_as(true, Deadline(None)).map_err(|e| match e {
            End::Disconnected => TryRecvError::Disconnected,
            _ => TryRecvError::Empty,
        })
    }

    fn recv_deadline(&self, deadline: Option<Instant>) -> Result<T, RecvTimeoutError> {
        self.h.recv_as(false, Deadline(deadline)).map_err(|e| match e {
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
        self.h.chan.queue.len() == 0
    }

    pub fn is_full(&self) -> bool {
        self.h.chan.queue.len() == self.h.chan.queue.capacity()
    }

    pub fn len(&self) -> usize {
        self.h.chan.queue.len()
    }

    pub fn capacity(&self) -> Option<usize> {
        Some(self.h.chan.queue.capacity())
    }

    /// Whether two receivers belong to the same channel.
    pub fn same_channel(&self, other: &Receiver<T>) -> bool {
        Arc::ptr_eq(&self.h.chan, &other.h.chan)
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        Sender { h: self.h.clone_handle(false) }
    }
}

impl<T> Clone for Receiver<T> {
    fn clone(&self) -> Self {
        Receiver { h: self.h.clone_handle(true) }
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        self.h.disconnect(false);
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.h.disconnect(true);
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
