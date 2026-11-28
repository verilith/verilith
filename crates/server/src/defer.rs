//! Deferred responses, and the worker's reactor for handlers that do their
//! own I/O (a reverse proxy's upstream connections).
//!
//! A handler that cannot answer at once calls [`Response::defer`] and gets
//! a [`Pending`]: the request stays open (on HTTP/1.1 the connection reads
//! nothing more until it is answered; on HTTP/2 and HTTP/3 the other
//! streams go on), and the response is written when the [`Pending`] is
//! completed, from the worker's own thread or any other. The answer goes
//! through the same [`Response`] calls, so it reaches the verified engines
//! the same way an immediate one does: what is sent, in which order and
//! with which framing is still theirs.
//!
//! [`register`] lets a handler watch its own sockets on the worker's
//! poller; events for them come to [`Handler::on_io`]
//! (crate::Handler::on_io) on the same thread, and
//! [`Handler::poll_timers`](crate::Handler::poll_timers) runs once per loop
//! turn.
//!
//! Plain Rust, trusted (TRUST.md): it moves a completion to its connection
//! and nothing else.
use std::cell::{Cell, RefCell};
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;

use crate::sys;
use crate::Response;

/// Tokens of sockets registered with [`register`] have this bit set in
/// the worker's poller; the handler sees them without it.
pub(crate) const EXT: u64 = 1 << 62;
/// The worker's wake pipe.
pub(crate) const WAKE: u64 = u64::MAX - 14;

/// Which request a completion is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Target {
    /// A TCP connection's slot in its worker, the slot's generation (a
    /// closed connection's completion is dropped), and the HTTP/2 stream
    /// (0 for HTTP/1.1).
    Tcp { slot: u32, era: u32, stream: u32 },
    /// An HTTP/3 connection on the worker's endpoint, its serial number,
    /// and the request stream.
    H3 { ch: u32, serial: u64, stream: u64 },
}

/// A completion: what the handler would have written, had it answered at
/// once.
pub type Finish = Box<dyn FnOnce(&mut Response) + Send + 'static>;

pub(crate) struct Done {
    pub(crate) to: Target,
    pub(crate) head: bool,
    pub(crate) finish: Finish,
}

/// A worker's completions, and how to wake it.
pub(crate) struct Inbox {
    q: Mutex<Vec<Done>>,
    owner: ThreadId,
    wake_w: i32,
    /// A wakeup is in the pipe and not yet read.
    woken: AtomicBool,
}

impl Inbox {
    pub(crate) fn new() -> io::Result<(Arc<Inbox>, i32)> {
        let (r, w) = sys::wake_pipe()?;
        Ok((Arc::new(Inbox { q: Mutex::new(Vec::new()), owner: std::thread::current().id(), wake_w: w, woken: AtomicBool::new(false) }), r))
    }

    fn push(&self, d: Done) {
        self.q.lock().unwrap_or_else(|e| e.into_inner()).push(d);
        // The worker drains its inbox after every batch of events, so a
        // completion made on its own thread needs no wakeup.
        if std::thread::current().id() != self.owner && !self.woken.swap(true, Ordering::AcqRel) {
            sys::wake(self.wake_w);
        }
    }

    /// Takes every completion waiting, into `out` (emptied first).
    pub(crate) fn take(&self, out: &mut Vec<Done>) {
        out.clear();
        self.woken.store(false, Ordering::Release);
        let mut q = self.q.lock().unwrap_or_else(|e| e.into_inner());
        std::mem::swap(&mut *q, out);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.q.lock().unwrap_or_else(|e| e.into_inner()).is_empty()
    }
}

thread_local! {
    /// The worker running on this thread: its inbox and poller. Unset on
    /// threads that are not workers, and on io_uring workers (which do not
    /// support deferral).
    static WORKER: RefCell<Option<(Arc<Inbox>, sys::PollHandle)>> = const { RefCell::new(None) };
    /// The TCP connection being processed: its slot and generation.
    static CURRENT: Cell<Option<(u32, u32)>> = const { Cell::new(None) };
    /// The client of the request being handled: its socket (TCP) or
    /// address (HTTP/3), and whether the connection is encrypted.
    static CLIENT: Cell<Option<Client>> = const { Cell::new(None) };
}

#[derive(Clone, Copy, Debug)]
enum Client {
    Fd { fd: i32, tls: bool },
    Addr(std::net::SocketAddrV4),
}

pub(crate) fn set_client_fd(fd: i32, tls: bool) {
    CLIENT.with(|c| c.set(Some(Client::Fd { fd, tls })));
}

pub(crate) fn set_client_addr(a: std::net::SocketAddrV4) {
    CLIENT.with(|c| c.set(Some(Client::Addr(a))));
}

pub(crate) fn clear_client() {
    CLIENT.with(|c| c.set(None));
}

/// The address of the client whose request is being handled, and whether
/// its connection is encrypted (TLS or QUIC): for `X-Forwarded-For` and
/// `X-Forwarded-Proto`. `None` outside a handler on a worker.
pub fn client() -> Option<(std::net::SocketAddrV4, bool)> {
    match CLIENT.with(|c| c.get())? {
        Client::Fd { fd, tls } => sys::peer_addr(fd).map(|a| (a, tls)),
        Client::Addr(a) => Some((a, true)),
    }
}

pub(crate) fn set_worker(inbox: Arc<Inbox>, poll: sys::PollHandle) {
    WORKER.with(|w| *w.borrow_mut() = Some((inbox, poll)));
}

pub(crate) fn set_current(c: Option<(u32, u32)>) {
    CURRENT.with(|x| x.set(c));
}

pub(crate) fn current_tcp(stream: u32) -> Option<Target> {
    let (slot, era) = CURRENT.with(|x| x.get())?;
    Some(Target::Tcp { slot, era, stream })
}

fn inbox() -> Option<Arc<Inbox>> {
    WORKER.with(|w| w.borrow().as_ref().map(|(i, _)| i.clone()))
}

/// A request answered later. Complete it with [`Pending::complete`];
/// dropped without that, the request is answered 502 (Bad Gateway).
pub struct Pending {
    inbox: Arc<Inbox>,
    to: Target,
    head: bool,
    done: bool,
}

impl std::fmt::Debug for Pending {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Pending({:?})", self.to)
    }
}

impl Pending {
    pub(crate) fn new(to: Target, head: bool) -> Option<Pending> {
        Some(Pending { inbox: inbox()?, to, head, done: false })
    }

    /// Answers the request: `f` writes the response as a handler would
    /// (`send`, `send_shared`, ...), on the worker's thread. A response
    /// `f` does not send is a 502. Does nothing if the connection or
    /// stream is gone by then.
    pub fn complete(mut self, f: impl FnOnce(&mut Response) + Send + 'static) {
        self.done = true;
        self.inbox.push(Done { to: self.to, head: self.head, finish: Box::new(f) });
    }

    /// Whether the request was HEAD (the response's body is not sent).
    pub fn is_head(&self) -> bool {
        self.head
    }
}

impl Drop for Pending {
    fn drop(&mut self) {
        if !self.done {
            self.inbox.push(Done { to: self.to, head: self.head, finish: Box::new(|r: &mut Response| r.error(502)) });
        }
    }
}

/// Watches `fd` on this worker's poller, edge-triggered, for reading and
/// writing: its events come to [`Handler::on_io`](crate::Handler::on_io)
/// with `token` (below 2^62). Fails off a worker thread, or on an
/// io_uring worker.
pub fn register(fd: i32, token: u64) -> io::Result<()> {
    if token >= EXT {
        return Err(io::Error::from(io::ErrorKind::InvalidInput));
    }
    let p = WORKER.with(|w| w.borrow().as_ref().map(|(_, p)| *p)).ok_or_else(|| io::Error::from(io::ErrorKind::Unsupported))?;
    p.add(fd, token | EXT, true)
}

/// Stops watching `fd` (closing it does as much).
pub fn deregister(fd: i32) {
    if let Some(p) = WORKER.with(|w| w.borrow().as_ref().map(|(_, p)| *p)) {
        p.remove(fd);
    }
}

/// Whether this thread is a worker that supports [`Response::defer`] and
/// [`register`].
pub fn on_worker() -> bool {
    WORKER.with(|w| w.borrow().is_some())
}
