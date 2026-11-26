//! The io_uring event loop (Linux, `Config::io_uring`): the same
//! thread-per-core model and the same engines as the epoll loop in
//! `worker.rs`, with every accept, receive and send an entry on one ring
//! per worker, so that a loop turn costs one `io_uring_enter` however many
//! connections it serves (DESIGN.md, "I/O model").
//!
//! Each connection has at most one receive and one send in flight. The
//! receive names the engine's read buffer and the send its pending
//! output, so the engine is only driven (`process`) when neither is in
//! flight: input that arrives while a send is in flight waits for it.
//! A connection's slot is boxed, so nothing a submitted entry names moves,
//! and it is freed only once its last entry has completed.
use std::io;

use super::{Any, Config, Proto};
use crate::h1::{Conn, Ctx, Io, Next};
use crate::h2::Conn2;
use crate::sys::{self, uring, IoResult};
use crate::Handler;

const OP_ACCEPT: u64 = 1;
const OP_RECV: u64 = 2;
const OP_SEND: u64 = 3;
const OP_POLLOUT: u64 = 4;
#[cfg(feature = "h3")]
const OP_UDP: u64 = 5;
const OP_CANCEL: u64 = 6;

/// Receive buffers per worker, and their size: requests are small, and
/// each buffer goes back to the kernel in the turn it arrives.
const BUFS: u16 = 2048;
const BUF_SIZE: usize = 4096;
/// Bytes received that the engine has not taken yet, past which the
/// receive is cancelled until it does (re-armed once they are taken).
const STASH_MAX: usize = 256 * 1024;
const ECANCELED: i32 = 125;

#[inline]
fn ud(op: u64, generation: u32, id: usize) -> u64 {
    op << 56 | ((generation as u64) & 0xff_ffff) << 32 | id as u64
}

struct Slot {
    fd: i32,
    conn: Any,
    generation: u32,
    /// A multishot receive is armed.
    recv: bool,
    /// ... and a cancel for it has been sent.
    recv_cancelled: bool,
    send: bool,
    /// Received bytes the engine had no room for yet.
    stash: Vec<u8>,
    sb: Box<uring::SendBuf>,
    /// Input arrived while a send was in flight and is not yet processed.
    deferred: bool,
    /// The engine asked to write before reading more (`Next::Write`).
    paused: bool,
    eof: bool,
    /// Close once the pending output is written.
    close_after: bool,
    /// Shut down; freed when the last entry completes.
    dying: bool,
}

pub(super) struct UWorker {
    ring: uring::Ring,
    bufs: uring::BufRing,
    /// Connections whose receive ran out of buffers: re-armed next turn.
    rearm: Vec<usize>,
    lfds: Vec<(i32, Proto)>,
    slots: Vec<Option<Box<Slot>>>,
    free: Vec<usize>,
    generations: Vec<u32>,
    spare: Vec<Conn>,
    spare_sb: Vec<Box<uring::SendBuf>>,
    cfg: Config,
    now: i64,
    ctx: Ctx,
    ctx_tls: Ctx,
    alt: Option<Vec<u8>>,
    #[cfg(feature = "h3")]
    pub(super) h3: Option<(i32, crate::h3::H3)>,
}

impl UWorker {
    pub(super) fn new(lfds: Vec<(i32, Proto)>, cfg: Config) -> io::Result<UWorker> {
        let mut ring = uring::Ring::new(4096)?;
        let bufs = uring::BufRing::new(&ring, 0, BUFS, BUF_SIZE)?;
        for (i, (fd, _)) in lfds.iter().enumerate() {
            ring.push(uring::accept_multishot(*fd, ud(OP_ACCEPT, 0, i)));
        }
        let now = sys::unix_time();
        let ctx = Ctx::new(cfg.server, &crate::date::imf_fixdate(now)).ok_or_else(|| io::Error::other("the Server value is not a valid field value"))?;
        #[allow(unused_mut)]
        let mut alt: Option<Vec<u8>> = None;
        #[cfg(feature = "h3")]
        if let Some((p, _)) = &cfg.h3 {
            alt = Some(format!("h3=\":{p}\"; ma=86400").into_bytes());
        }
        let ctx_tls = Ctx::with_alt_svc(cfg.server, &crate::date::imf_fixdate(now), alt.as_deref())
            .ok_or_else(|| io::Error::other("the Server value is not a valid field value"))?;
        Ok(UWorker {
            ring,
            bufs,
            rearm: Vec::new(),
            lfds,
            slots: Vec::new(),
            free: Vec::new(),
            generations: Vec::new(),
            spare: Vec::new(),
            spare_sb: Vec::new(),
            cfg,
            now,
            ctx,
            ctx_tls,
            alt,
            #[cfg(feature = "h3")]
            h3: None,
        })
    }

    #[cfg(feature = "h3")]
    pub(super) fn add_udp(&mut self, fd: i32, q: crate::h3::H3) {
        self.ring.push(uring::poll(fd, uring::POLLIN, true, ud(OP_UDP, 0, 0)));
        self.h3 = Some((fd, q));
    }

    pub(super) fn run<H: Handler + ?Sized>(&mut self, h: &H) -> io::Result<()> {
        let mut cqes: Vec<uring::Cqe> = Vec::with_capacity(4096);
        loop {
            #[allow(unused_mut)]
            let mut timeout = 1000u32;
            #[cfg(feature = "h3")]
            if let Some((_, q)) = self.h3.as_mut() {
                if let Some(t) = q.timeout_ms(std::time::Instant::now()) {
                    timeout = timeout.min(t.max(0) as u32);
                }
            }
            self.bufs.publish();
            // Submits everything queued last turn and waits for one
            // completion: the turn's only system call.
            self.ring.enter(1, Some(timeout))?;
            cqes.clear();
            self.ring.reap(|c| cqes.push(c));
            let t = sys::unix_time();
            if t != self.now {
                self.now = t;
                let d = crate::date::imf_fixdate(t);
                if let Some(c) = Ctx::new(self.cfg.server, &d) {
                    self.ctx = c;
                }
                if let Some(c) = Ctx::with_alt_svc(self.cfg.server, &d, self.alt.as_deref()) {
                    self.ctx_tls = c;
                }
            }
            for c in &cqes {
                self.complete(h, *c);
            }
            #[cfg(feature = "h3")]
            if let Some((_, q)) = self.h3.as_mut() {
                q.on_timers(h, &self.ctx);
            }
            let mut rearm = std::mem::take(&mut self.rearm);
            for id in rearm.drain(..) {
                self.arm_recv(id);
            }
            self.rearm = rearm;
        }
    }

    fn complete<H: Handler + ?Sized>(&mut self, h: &H, c: uring::Cqe) {
        let op = c.user_data >> 56;
        let generation = ((c.user_data >> 32) & 0xff_ffff) as u32;
        let id = (c.user_data & 0xffff_ffff) as usize;
        match op {
            OP_ACCEPT => {
                if c.res >= 0 {
                    self.accepted(id, c.res);
                }
                if c.flags & uring::CQE_F_MORE == 0 {
                    // Disarmed (an error, or the kernel's limit): again.
                    let fd = self.lfds[id].0;
                    self.ring.push(uring::accept_multishot(fd, ud(OP_ACCEPT, 0, id)));
                }
            }
            #[cfg(feature = "h3")]
            OP_UDP => {
                if let Some((fd, q)) = self.h3.as_mut() {
                    q.on_readable(h, &self.ctx);
                    if c.flags & uring::CQE_F_MORE == 0 {
                        let fd = *fd;
                        self.ring.push(uring::poll(fd, uring::POLLIN, true, ud(OP_UDP, 0, 0)));
                    }
                }
            }
            OP_RECV | OP_SEND | OP_POLLOUT => {
                // A buffer goes back to the kernel whatever else happens.
                let buf = if op == OP_RECV && c.flags & uring::CQE_F_BUFFER != 0 { Some((c.flags >> 16) as u16) } else { None };
                let Some(Some(s)) = self.slots.get_mut(id) else {
                    if let Some(b) = buf {
                        self.bufs.put(b);
                    }
                    return;
                };
                if s.generation & 0xff_ffff != generation {
                    if let Some(b) = buf {
                        self.bufs.put(b);
                    }
                    return;
                }
                if op == OP_RECV {
                    if c.flags & uring::CQE_F_MORE == 0 {
                        s.recv = false;
                    }
                    if let Some(b) = buf {
                        if c.res > 0 && !s.dying {
                            deliver(&mut s.conn, &mut s.stash, self.bufs.get(b, c.res as usize));
                        }
                        self.bufs.put(b);
                    }
                    if s.recv && !s.recv_cancelled && s.stash.len() > STASH_MAX {
                        s.recv_cancelled = true;
                        let target = ud(OP_RECV, s.generation, id);
                        self.ring.push(uring::cancel(target, ud(OP_CANCEL, 0, 0)));
                    }
                } else {
                    s.send = false;
                }
                if s.dying {
                    self.maybe_free(id);
                    return;
                }
                match op {
                    OP_RECV => {
                        if c.res == -uring::ENOBUFS {
                            // Out of buffers this turn: armed again next.
                            if !s.recv {
                                self.rearm.push(id);
                            }
                        } else if c.res <= 0 && c.res != -ECANCELED && c.res != -11 && c.res != -4 {
                            // 0: the peer closed; an error (not EAGAIN,
                            // EINTR, or our own cancel): the same to us.
                            s.eof = true;
                        }
                        if s.send {
                            s.deferred = true;
                        } else {
                            self.drive(h, id);
                        }
                    }
                    OP_SEND => {
                        if c.res == -11 {
                            // EAGAIN: the socket is nonblocking (for
                            // sendfile) and full. Again once it has room.
                            let e = uring::poll(s.fd, uring::POLLOUT, false, ud(OP_POLLOUT, s.generation, id));
                            s.send = true;
                            self.ring.push(e);
                            return;
                        }
                        if c.res < 0 {
                            self.close(id);
                            return;
                        }
                        s.conn.wrote(c.res as usize);
                        #[cfg(feature = "tls")]
                        if let Any::Tls(t) = &s.conn {
                            // As in the epoll loop: quick ACKs while the
                            // handshake runs, set after the write.
                            if t.handshaking() {
                                sys::quickack(s.fd);
                            }
                        }
                        self.after_send(h, id);
                    }
                    _ => self.after_send(h, id),
                }
            }
            _ => {}
        }
    }

    fn accepted(&mut self, which: usize, fd: i32) {
        let proto = self.lfds[which].1;
        if !sys::NODELAY_INHERITED {
            sys::set_nodelay(fd);
        }
        let conn = match proto {
            Proto::H1 => Any::H1(self.spare.pop().unwrap_or_else(|| Conn::new(self.cfg.limits))),
            Proto::H2 => Any::H2(Box::new(Conn2::new(self.cfg.limits2))),
            #[cfg(feature = "tls")]
            Proto::Tls => match crate::tls::TlsConn::new(self.cfg.tls.as_ref().unwrap().1.clone(), self.cfg.limits, self.cfg.limits2) {
                Some(t) => Any::Tls(Box::new(t)),
                None => {
                    sys::close_fd(fd);
                    return;
                }
            },
        };
        let id = match self.free.pop() {
            Some(i) => i,
            None => {
                self.slots.push(None);
                self.generations.push(0);
                self.slots.len() - 1
            }
        };
        let generation = self.generations[id];
        let sb = self.spare_sb.pop().unwrap_or_else(uring::SendBuf::new);
        self.slots[id] = Some(Box::new(Slot { fd, conn, generation, recv: false, recv_cancelled: false, send: false, stash: Vec::new(), sb, deferred: false, paused: false, eof: false, close_after: false, dying: false }));
        self.arm_recv(id);
    }

    fn arm_recv(&mut self, id: usize) {
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        if s.recv || s.eof || s.dying || s.stash.len() > STASH_MAX / 2 {
            return;
        }
        let e = uring::recv_multishot(s.fd, self.bufs.group, ud(OP_RECV, s.generation, id));
        s.recv = true;
        s.recv_cancelled = false;
        self.ring.push(e);
    }

    /// Writes what is pending: one `sendmsg` entry, or for a file body,
    /// `sendfile` now (it has no ring operation) and a readiness wait if
    /// the socket is full. Returns false if the connection broke.
    fn start_send(&mut self, id: usize) -> bool {
        let Some(Some(s)) = self.slots.get_mut(id) else { return false };
        loop {
            if s.send || s.conn.pending_len() == 0 {
                return true;
            }
            let mut v: [&[u8]; 8] = [&[]; 8];
            let mut more = false;
            match s.conn.pending_io(&mut v, &mut more) {
                Io::Slices(k, _) => {
                    let flags = if more { sys::MSG_MORE } else { 0 };
                    let e = if k == 1 {
                        uring::send(s.fd, v[0].as_ptr(), v[0].len(), flags, ud(OP_SEND, s.generation, id))
                    } else {
                        let m = s.sb.set(&v[..k]);
                        uring::sendmsg(s.fd, m, flags, ud(OP_SEND, s.generation, id))
                    };
                    s.send = true;
                    self.ring.push(e);
                    return true;
                }
                Io::File { fd, off, len } => match sys::sendfile_nb(s.fd, fd, off, len) {
                    IoResult::Done(n) => s.conn.wrote(n),
                    IoResult::WouldBlock => {
                        let e = uring::poll(s.fd, uring::POLLOUT, false, ud(OP_POLLOUT, s.generation, id));
                        s.send = true;
                        self.ring.push(e);
                        return true;
                    }
                    IoResult::Closed => return false,
                },
            }
        }
    }

    fn after_send<H: Handler + ?Sized>(&mut self, h: &H, id: usize) {
        if !self.start_send(id) {
            self.close(id);
            return;
        }
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        if s.send {
            return;
        }
        // Drained. The engine may hold back output until this one is
        // written (its high-water mark), so it runs again whenever it
        // stopped for that, or is finishing up.
        if s.conn.closing() {
            self.close(id);
            return;
        }
        if s.deferred || s.paused || s.close_after || s.eof {
            self.drive(h, id);
        }
    }

    /// Runs the engine on what has been read, starts the writes, and
    /// arms the next receive: the epoll loop's `read_process_write`, one
    /// read at a time. Only called with nothing in flight.
    fn drive<H: Handler + ?Sized>(&mut self, h: &H, id: usize) {
        let mut stashed = usize::MAX;
        loop {
            let Some(Some(s)) = self.slots.get_mut(id) else { return };
            s.deferred = false;
            feed(&mut s.conn, &mut s.stash);
            if s.stash.len() >= stashed && stashed > 0 && !s.send {
                // The engine took nothing more and has nothing to write.
                break;
            }
            stashed = s.stash.len();
            #[cfg(feature = "tls")]
            let ctx = if matches!(s.conn, Any::Tls(_)) { &self.ctx_tls } else { &self.ctx };
            #[cfg(not(feature = "tls"))]
            let ctx = &self.ctx;
            let next = s.conn.process(h, ctx);
            // The peer's end of stream comes after the bytes still stashed.
            let eof = s.eof && s.stash.is_empty();
            if eof {
                s.conn.eof();
            }
            if !self.start_send(id) {
                self.close(id);
                return;
            }
            let Some(Some(s)) = self.slots.get_mut(id) else { return };
            let pending = s.conn.pending_len();
            if pending == 0 && s.conn.closing() {
                self.close(id);
                return;
            }
            match next {
                Next::Close => {
                    // Unlike the epoll loop, nothing has been written yet:
                    // the output goes first.
                    if pending == 0 {
                        self.close(id);
                    } else {
                        s.close_after = true;
                    }
                    return;
                }
                Next::Write if pending > 0 => {
                    s.paused = true;
                    return;
                }
                _ => {
                    s.paused = false;
                    if eof {
                        if pending == 0 {
                            self.close(id);
                        } else {
                            s.close_after = true;
                        }
                        return;
                    }
                    if s.stash.is_empty() {
                        self.arm_recv(id);
                        return;
                    }
                    // Bytes the engine had no room for: once its output
                    // is written, or now if it made room.
                    if s.send {
                        s.paused = true;
                        self.arm_recv(id);
                        return;
                    }
                }
            }
        }
        // The engine neither reads nor writes: give up on it.
        self.close(id);
    }

    fn close(&mut self, id: usize) {
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        if s.recv || s.send {
            if !s.dying {
                s.dying = true;
                // Ends the in-flight entries; the slot goes when they do.
                let (fd, g) = (s.fd, s.generation);
                let (r, w) = (s.recv, s.send);
                if r {
                    self.ring.push(uring::cancel(ud(OP_RECV, g, id), ud(OP_CANCEL, 0, 0)));
                }
                if w {
                    // A send stuck on a full socket: shut it down.
                    uring::shutdown_rdwr(fd);
                }
            }
            return;
        }
        self.free_slot(id);
    }

    fn maybe_free(&mut self, id: usize) {
        if let Some(Some(s)) = self.slots.get(id) {
            if !s.recv && !s.send {
                self.free_slot(id);
            }
        }
    }

    fn free_slot(&mut self, id: usize) {
        if let Some(s) = self.slots[id].take() {
            let s = *s;
            sys::close_fd(s.fd);
            if let Any::H1(mut c) = s.conn {
                if self.spare.len() < 1024 {
                    c.reset();
                    self.spare.push(c);
                }
            }
            if self.spare_sb.len() < 1024 {
                self.spare_sb.push(s.sb);
            }
            self.generations[id] = self.generations[id].wrapping_add(1);
            self.free.push(id);
        }
    }
}

/// Received bytes into the engine's read buffer, the rest into `stash`
/// (behind anything already there, so the order is kept).
#[inline]
fn deliver(conn: &mut Any, stash: &mut Vec<u8>, mut d: &[u8]) {
    if stash.is_empty() {
        let b = conn.read_buf();
        let n = b.len().min(d.len());
        b[..n].copy_from_slice(&d[..n]);
        if n > 0 {
            conn.filled(n);
        }
        d = &d[n..];
    }
    stash.extend_from_slice(d);
}

/// As much of `stash` as the engine has room for.
#[inline]
fn feed(conn: &mut Any, stash: &mut Vec<u8>) {
    while !stash.is_empty() {
        let b = conn.read_buf();
        let n = b.len().min(stash.len());
        if n == 0 {
            return;
        }
        b[..n].copy_from_slice(&stash[..n]);
        conn.filled(n);
        stash.drain(..n);
    }
}
