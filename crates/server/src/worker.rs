//! The thread-per-core event loop (DESIGN.md, "I/O model").
//!
//! Each worker owns a poller, a listening socket (Linux: its own, with
//! SO_REUSEPORT; macOS: a shared one), and its connections. A connection
//! never leaves its worker. Per readiness event: read until the kernel has
//! nothing more, let the engine handle every complete request, and write
//! all the responses with one call.
use std::io;
use std::sync::Arc;
#[cfg(feature = "tls")]
use std::sync::atomic::{AtomicBool, Ordering};

use crate::h1::{Conn, Ctx, Io, Limits, Next};
use crate::h2::{Conn2, Limits2};
use crate::defer::{Done, Inbox, Target, EXT, WAKE};
use crate::sys::{self, IoResult};
use crate::Handler;

#[cfg(target_os = "linux")]
#[path = "worker_uring.rs"]
mod uring;

/// How to run the server.
#[derive(Clone, Debug)]
pub struct Config {
    pub addr: [u8; 4],
    /// The HTTP/1.1 port.
    pub port: u16,
    /// A port for HTTP/2 with prior knowledge (h2c), if any.
    pub h2c_port: Option<u16>,
    pub limits2: Limits2,
    /// Worker threads. 0: one per CPU this process may use.
    pub threads: usize,
    /// Pin worker `i` to the `i`th allowed CPU (Linux).
    pub pin: bool,
    pub limits: Limits,
    /// A TLS port (h2 and http/1.1 by ALPN), with its configuration.
    #[cfg(feature = "tls")]
    pub tls: Option<(u16, Arc<crate::tls::Config>)>,
    /// Linux, epoll workers: once a TLS handshake is over, hand record
    /// protection of what the server sends to the kernel (kTLS), so that
    /// static files go out with `sendfile`. Connections stay in userspace
    /// where the kernel has no kTLS (no `tls` module) or refuses the keys.
    #[cfg(feature = "tls")]
    pub ktls: bool,
    /// An HTTP/3 port (UDP), with its QUIC configuration.
    #[cfg(feature = "h3")]
    pub h3: Option<(u16, crate::h3::QuicConfig)>,
    #[cfg(feature = "h3")]
    pub limits3: crate::h3::Limits3,
    /// The `Server` field value.
    pub server: &'static [u8],
    /// Empty polls before a worker sleeps. 0 (the default) sleeps at once;
    /// a few hundred trade CPU for lower latency when connections are
    /// short (`h1-close`: +14% requests, twice the CPU).
    pub spin: u32,
    /// Linux: run each worker on io_uring instead of epoll (falls back
    /// to epoll where the kernel has no io_uring).
    pub io_uring: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            addr: [127, 0, 0, 1],
            port: 8080,
            h2c_port: None,
            limits2: Limits2::default(),
            threads: 0,
            pin: true,
            limits: Limits::default(),
            #[cfg(feature = "tls")]
            tls: None,
            #[cfg(feature = "tls")]
            ktls: false,
            #[cfg(feature = "h3")]
            h3: None,
            #[cfg(feature = "h3")]
            limits3: crate::h3::Limits3::default(),
            server: b"verilith",
            spin: 0,
            io_uring: false,
        }
    }
}

/// Listener tokens count down from here; connection tokens are slot indices.
const LISTENER: u64 = u64::MAX;
/// The HTTP/3 UDP socket's token.
#[cfg(feature = "h3")]
const UDP: u64 = LISTENER - 15;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Proto {
    H1,
    H2,
    #[cfg(feature = "tls")]
    Tls,
}

/// Runs the server on the calling thread and `threads - 1` more, until the
/// process exits.
pub fn serve<H: Handler>(cfg: Config, handler: Arc<H>) -> io::Result<()> {
    sys::ignore_sigpipe();
    let cpus = sys::allowed_cpus();
    let n = if cfg.threads == 0 { cpus.len().max(1) } else { cfg.threads };
    let mut ports = vec![(cfg.port, Proto::H1)];
    if let Some(p) = cfg.h2c_port {
        ports.push((p, Proto::H2));
    }
    #[cfg(feature = "tls")]
    if let Some((p, _)) = &cfg.tls {
        ports.push((*p, Proto::Tls));
    }
    // macOS: one listening socket per port for all workers, made up front.
    let shared: Option<Vec<(i32, Proto)>> = if sys::REUSEPORT_BALANCES {
        None
    } else {
        Some(ports.iter().map(|&(p, k)| sys::listen_tcp(cfg.addr, p, false, 65535).map(|fd| (fd, k))).collect::<io::Result<_>>()?)
    };
    let mut joins = Vec::new();
    for i in 0..n {
        let lfd = match &shared {
            Some(v) => v.clone(),
            None => ports.iter().map(|&(p, k)| sys::listen_tcp(cfg.addr, p, true, 65535).map(|fd| (fd, k))).collect::<io::Result<_>>()?,
        };
        // HTTP/3: a UDP socket per worker where the kernel keeps each
        // client on one socket; elsewhere worker 0 serves it alone.
        #[cfg(feature = "h3")]
        let udp = match &cfg.h3 {
            Some((p, _)) if sys::UDP_REUSEPORT_BALANCES || i == 0 => Some(sys::bind_udp(cfg.addr, *p, sys::UDP_REUSEPORT_BALANCES)?),
            _ => None,
        };
        let cfg = cfg.clone();
        let h = handler.clone();
        let cpu = if cpus.is_empty() { i } else { cpus[i % cpus.len()] };
        joins.push(std::thread::Builder::new().name(format!("verilith-w{i}")).spawn(move || {
            if cfg.pin {
                sys::pin_to_cpu(cpu);
            }
            #[cfg(target_os = "linux")]
            if cfg.io_uring {
                match uring::UWorker::new(lfd.clone(), cfg.clone()) {
                    Ok(mut w) => {
                        #[cfg(feature = "h3")]
                        if let (Some(fd), Some((_, qc))) = (udp, &cfg.h3) {
                            w.add_udp(fd, crate::h3::H3::new(fd, qc.clone(), cfg.limits3));
                        }
                        return w.run(&*h);
                    }
                    Err(e) if i == 0 => eprintln!("verilith-server: no io_uring ({e}); using epoll"),
                    Err(_) => {}
                }
            }
            #[allow(unused_mut)]
            let mut w = Worker::new(lfd, cfg)?;
            #[cfg(feature = "h3")]
            if let (Some(fd), Some((_, qc))) = (udp, &w.cfg.h3) {
                w.poll.add(fd, UDP, false)?;
                w.h3 = Some(crate::h3::H3::new(fd, qc.clone(), w.cfg.limits3));
            }
            w.run(&*h)
        })?);
    }
    for j in joins {
        j.join().map_err(|_| io::Error::other("worker panicked"))??;
    }
    Ok(())
}

enum Any {
    H1(Conn),
    H2(Box<Conn2>),
    #[cfg(feature = "tls")]
    Tls(Box<crate::tls::TlsConn>),
}

#[cfg(not(feature = "tls"))]
macro_rules! each {
    ($c:expr, $x:ident => $e:expr) => {
        match $c {
            Any::H1($x) => $e,
            Any::H2($x) => $e,
        }
    };
}

#[cfg(feature = "tls")]
macro_rules! each {
    ($c:expr, $x:ident => $e:expr) => {
        match $c {
            Any::H1($x) => $e,
            Any::H2($x) => $e,
            Any::Tls($x) => $e,
        }
    };
}

impl Any {
    fn read_buf(&mut self) -> &mut [u8] {
        each!(self, c => c.read_buf())
    }
    fn filled(&mut self, n: usize) {
        each!(self, c => c.filled(n))
    }
    fn eof(&mut self) {
        each!(self, c => c.eof())
    }
    fn closing(&self) -> bool {
        each!(self, c => c.closing())
    }
    fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        each!(self, c => c.process(h, ctx))
    }
    fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        each!(self, c => c.pending(out))
    }
    fn pending_io<'a>(&'a self, out: &mut [&'a [u8]], more: &mut bool) -> Io<'a> {
        match self {
            Any::H1(c) => c.pending_io(out, more),
            Any::H2(c) => c.pending_io(out, more),
            #[cfg(feature = "tls")]
            Any::Tls(c) => c.pending_io(out, more),
        }
    }
    fn pending_len(&self) -> usize {
        each!(self, c => c.pending_len())
    }
    fn wrote(&mut self, n: usize) {
        each!(self, c => c.wrote(n))
    }
    fn resume(&mut self, stream: u32, head: bool, f: crate::defer::Finish, ctx: &Ctx) {
        match self {
            Any::H1(c) => c.resume(f, ctx),
            Any::H2(c) => c.resume(stream, head, f, ctx),
            #[cfg(feature = "tls")]
            Any::Tls(c) => c.resume(stream, head, f, ctx),
        }
    }
}

struct Slot {
    fd: i32,
    /// Changes each time the slot is reused: a deferred response for a
    /// closed connection finds another generation and is dropped.
    era: u32,
    conn: Any,
    /// Reading stopped because the write buffer was full.
    read_paused: bool,
}

struct Worker {
    lfds: Vec<(i32, Proto)>,
    poll: sys::Poller,
    slots: Vec<Option<Slot>>,
    free: Vec<usize>,
    /// Connections closed and reusable, buffers and all.
    spare: Vec<Conn>,
    cfg: Config,
    now: i64,
    ctx: Ctx,
    /// For TLS connections: `ctx` with Alt-Svc advertising HTTP/3, when
    /// it is served.
    ctx_tls: Ctx,
    alt: Option<Vec<u8>>,
    #[cfg(feature = "h3")]
    h3: Option<crate::h3::H3>,
    /// Deferred responses completed, waiting to be written.
    inbox: Arc<Inbox>,
    wake_r: i32,
    done: Vec<Done>,
    eras: u32,
    /// The handler's own timers: how long the worker may sleep.
    ext_timeout: Option<u64>,
}

impl Worker {
    fn new(lfds: Vec<(i32, Proto)>, cfg: Config) -> io::Result<Worker> {
        let poll = sys::Poller::new(1024)?;
        for (i, (fd, _)) in lfds.iter().enumerate() {
            poll.add(*fd, LISTENER - i as u64, false)?;
        }
        let (inbox, wake_r) = Inbox::new()?;
        poll.add(wake_r, WAKE, false)?;
        crate::defer::set_worker(inbox.clone(), poll.handle());
        let now = sys::unix_time();
        let ctx = Ctx::new(cfg.server, &crate::date::imf_fixdate(now))
            .ok_or_else(|| io::Error::other("the Server value is not a valid field value"))?;
        #[allow(unused_mut)]
        let mut alt: Option<Vec<u8>> = None;
        #[cfg(feature = "h3")]
        if let Some((p, _)) = &cfg.h3 {
            alt = Some(format!("h3=\":{p}\"; ma=86400").into_bytes());
        }
        let ctx_tls = Ctx::with_alt_svc(cfg.server, &crate::date::imf_fixdate(now), alt.as_deref())
            .ok_or_else(|| io::Error::other("the Server value is not a valid field value"))?;
        Ok(Worker {
            lfds,
            poll,
            slots: Vec::new(),
            free: Vec::new(),
            spare: Vec::new(),
            cfg,
            now,
            ctx,
            ctx_tls,
            alt,
            #[cfg(feature = "h3")]
            h3: None,
            inbox,
            wake_r,
            done: Vec::new(),
            eras: 0,
            ext_timeout: None,
        })
    }

    fn run<H: Handler + ?Sized>(&mut self, h: &H) -> io::Result<()> {
        let mut evs = Vec::with_capacity(1024);
        let spin = self.cfg.spin;
        let mut idle = 0u32;
        loop {
            evs.clear();
            #[allow(unused_mut)]
            let mut timeout_us: u64 = if idle < spin { 0 } else { 1_000_000 };
            if let Some(t) = self.ext_timeout {
                timeout_us = timeout_us.min(t);
            }
            #[cfg(feature = "h3")]
            if let Some(q) = self.h3.as_mut() {
                if let Some(t) = q.timeout_us(std::time::Instant::now()) {
                    timeout_us = timeout_us.min(t);
                }
            }
            let n = self.poll.wait_us(timeout_us, |e| evs.push(e));
            idle = if n == 0 { idle.saturating_add(1) } else { 0 };
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
            for e in &evs {
                if e.token == WAKE {
                    sys::drain(self.wake_r);
                    continue;
                }
                if e.token & EXT != 0 && e.token < LISTENER - 16 {
                    h.on_io(e.token & !EXT, e.readable, e.writable);
                    continue;
                }
                #[cfg(feature = "h3")]
                if e.token == UDP {
                    if let Some(q) = self.h3.as_mut() {
                        q.on_readable(h, &self.ctx);
                    }
                    continue;
                }
                if e.token > LISTENER - 16 {
                    self.accept_all(h, (LISTENER - e.token) as usize);
                } else {
                    self.on_event(h, e.token as usize, e.readable, e.writable);
                }
            }
            #[cfg(feature = "h3")]
            if let Some(q) = self.h3.as_mut() {
                q.on_timers(h, &self.ctx);
            }
            self.ext_timeout = h.poll_timers();
            self.completions(h);
        }
    }

    /// Writes the deferred responses that were completed. Answering one
    /// can run handlers for the requests behind it, which may complete
    /// at once: a few rounds.
    fn completions<H: Handler + ?Sized>(&mut self, h: &H) {
        for _ in 0..16 {
            if self.inbox.is_empty() {
                return;
            }
            let mut done = std::mem::take(&mut self.done);
            self.inbox.take(&mut done);
            for d in done.drain(..) {
                match d.to {
                    Target::Tcp { slot, era, stream } => {
                        let id = slot as usize;
                        let Some(Some(s)) = self.slots.get_mut(id) else { continue };
                        if s.era != era {
                            continue;
                        }
                        #[cfg(feature = "tls")]
                        let ctx = if matches!(s.conn, Any::Tls(_)) { &self.ctx_tls } else { &self.ctx };
                        #[cfg(not(feature = "tls"))]
                        let ctx = &self.ctx;
                        s.conn.resume(stream, d.head, d.finish, ctx);
                        crate::defer::set_current(Some((slot, era)));
                        let close = read_process_write(s, h, ctx);
                        crate::defer::set_current(None);
                        if close {
                            self.close(id);
                        }
                    }
                    #[cfg(feature = "h3")]
                    Target::H3 { ch, serial, stream } => {
                        if let Some(q) = self.h3.as_mut() {
                            q.resume(ch, serial, stream, d.head, d.finish, h, &self.ctx);
                        }
                    }
                    #[cfg(not(feature = "h3"))]
                    Target::H3 { .. } => {}
                }
            }
            self.done = done;
        }
    }

    fn accept_all<H: Handler + ?Sized>(&mut self, h: &H, which: usize) {
        let (lfd, proto) = self.lfds[which];
        while let Some(fd) = sys::accept_nb(lfd) {
            if !sys::NODELAY_INHERITED {
                sys::set_nodelay(fd);
            }
            let conn = match proto {
                Proto::H1 => Any::H1(match self.spare.pop() {
                    Some(c) => c,
                    None => Conn::new(self.cfg.limits),
                }),
                Proto::H2 => Any::H2(Box::new(Conn2::new(self.cfg.limits2))),
                #[cfg(feature = "tls")]
                Proto::Tls => match crate::tls::TlsConn::new(self.cfg.tls.as_ref().unwrap().1.clone(), self.cfg.limits, self.cfg.limits2) {
                    Some(mut t) => {
                        if self.cfg.ktls && sys::HAS_KTLS && !KTLS_MISSING.load(Ordering::Relaxed) {
                            t.want_ktls();
                        }
                        Any::Tls(Box::new(t))
                    }
                    None => {
                        sys::close_fd(fd);
                        continue;
                    }
                },
            };
            let id = match self.free.pop() {
                Some(i) => i,
                None => {
                    self.slots.push(None);
                    self.slots.len() - 1
                }
            };
            self.eras = self.eras.wrapping_add(1);
            self.slots[id] = Some(Slot { fd, era: self.eras, conn, read_paused: false });
            if self.poll.add(fd, id as u64, true).is_err() {
                self.close(id);
                continue;
            }
            // The request often arrives with the connection.
            self.on_event(h, id, true, false);
        }
    }

    fn on_event<H: Handler + ?Sized>(&mut self, h: &H, id: usize, readable: bool, writable: bool) {
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        #[cfg(feature = "tls")]
        let ctx = if matches!(s.conn, Any::Tls(_)) { &self.ctx_tls } else { &self.ctx };
        #[cfg(not(feature = "tls"))]
        let ctx = &self.ctx;
        let mut close = false;
        if writable || s.read_paused {
            close = flush(s);
        }
        if !close && (readable || s.read_paused) {
            crate::defer::set_current(Some((id as u32, s.era)));
            close = read_process_write(s, h, ctx);
            crate::defer::set_current(None);
        }
        if close {
            self.close(id);
        }
    }

    fn close(&mut self, id: usize) {
        if let Some(s) = self.slots[id].take() {
            // Closing the only descriptor of a socket also removes it from
            // epoll and kqueue: no separate system call.
            sys::close_fd(s.fd);
            if let Any::H1(mut c) = s.conn {
                if self.spare.len() < 1024 {
                    c.reset();
                    self.spare.push(c);
                }
            }
            self.free.push(id);
        }
    }
}

/// Reads all that is available, handles it, writes the responses. Returns
/// whether to close the connection.
#[inline]
fn read_process_write<H: Handler + ?Sized>(s: &mut Slot, h: &H, ctx: &Ctx) -> bool {
    loop {
        let mut eof = false;
        let mut drained = false;
        loop {
            let b = s.conn.read_buf();
            if b.is_empty() {
                break;
            }
            let room = b.len();
            match sys::read_into(s.fd, b) {
                IoResult::Done(n) => {
                    s.conn.filled(n);
                    // A short read emptied the socket; edge-triggered readiness
                    // reports the next bytes as a new event.
                    if n < room {
                        drained = true;
                        break;
                    }
                }
                IoResult::WouldBlock => {
                    drained = true;
                    break;
                }
                IoResult::Closed => {
                    eof = true;
                    drained = true;
                    break;
                }
            }
        }
        let next = s.conn.process(h, ctx);
        if eof {
            s.conn.eof();
        }
        let broken = flush(s);
        #[cfg(feature = "tls")]
        if let Any::Tls(c) = &s.conn {
            // A TLS 1.3 client's Finished gets no answer from the server
            // (no session tickets), so a client with Nagle on holds its
            // request until the kernel's delayed ACK, 40 ms. Quick ACKs
            // while handshaking release it at once (after the write, which
            // would otherwise turn delayed ACKs back on).
            if c.handshaking() {
                sys::quickack(s.fd);
            }
        }
        if broken {
            return true;
        }
        match next {
            Next::Close => return s.conn.pending_len() == 0 || eof,
            Next::Write => {
                s.read_paused = s.conn.pending_len() > 0;
                if s.read_paused {
                    return false;
                }
            }
            Next::Read => {
                s.read_paused = false;
                if eof {
                    return true;
                }
                if drained {
                    return false;
                }
            }
            // A deferred response: the connection is resumed when it is
            // completed (`Worker::completions`).
            Next::Wait => {
                s.read_paused = false;
                return false;
            }
        }
    }
}

/// The kernel has no kTLS (found by the first connection that tried):
/// later connections do not ask.
#[cfg(feature = "tls")]
static KTLS_MISSING: AtomicBool = AtomicBool::new(false);

/// kTLS: gives the kernel the connection's sending keys once it wants
/// them, and sends the records that are not application data. Returns
/// whether the connection is broken (`Err`), else whether it has bytes
/// to write now that it did not have before (`Ok(true)`).
#[cfg(feature = "tls")]
fn ktls_step(s: &mut Slot) -> Result<bool, ()> {
    let Any::Tls(c) = &mut s.conn else { return Ok(false) };
    if let Some(k) = c.ktls_keys() {
        let before = c.pending_len();
        match sys::ktls_tx(s.fd, k.suite, &k.key[..k.key_len], &k.iv, k.seq, true) {
            Ok(()) => c.ktls_installed(true),
            Err((attach, e)) => {
                c.ktls_installed(false);
                // The TLS layer would not attach (no `tls` module, or no
                // TLS in the kernel): no connection will get one. Keys
                // refused (a cipher the kernel lacks) concern this one.
                if attach && !KTLS_MISSING.swap(true, Ordering::Relaxed) {
                    eprintln!("verilith-server: no kTLS in this kernel ({e}); TLS stays in userspace");
                }
            }
        }
        return Ok(c.pending_len() > before);
    }
    while let Some((ty, b)) = c.ktls_ctrl() {
        match sys::send_record(s.fd, ty, b) {
            IoResult::Done(n) => {
                if let Some(k) = c.ktls_ctrl_sent(n) {
                    // After a KeyUpdate: the kernel's new keys. A kernel
                    // that cannot change them (before Linux 6.14) ends the
                    // connection.
                    if sys::ktls_tx(s.fd, k.suite, &k.key[..k.key_len], &k.iv, k.seq, false).is_err() {
                        return Err(());
                    }
                }
            }
            IoResult::WouldBlock => return Ok(false),
            IoResult::Closed => return Err(()),
        }
    }
    Ok(false)
}

/// Writes what is pending. Returns whether the connection is broken, or
/// closing with nothing left to write.
#[inline]
fn flush(s: &mut Slot) -> bool {
    loop {
        #[cfg(feature = "tls")]
        if matches!(s.conn, Any::Tls(_)) {
            match ktls_step(s) {
                Err(()) => return true,
                Ok(true) => continue,
                Ok(false) => {}
            }
            if let Any::Tls(c) = &s.conn {
                if c.ktls_ctrl().is_some() {
                    // A record that must go first is waiting for room.
                    return false;
                }
            }
        }
        if s.conn.pending_len() == 0 {
            return s.conn.closing();
        }
        let mut v: [&[u8]; 8] = [&[]; 8];
        let mut more = false;
        let r = match s.conn.pending_io(&mut v, &mut more) {
            Io::Slices(k, _) => sys::write_slices(s.fd, &v[..k], more),
            Io::File { fd, off, len } => sys::sendfile_nb(s.fd, fd, off, len),
        };
        match r {
            IoResult::Done(n) => s.conn.wrote(n),
            IoResult::WouldBlock => return false,
            IoResult::Closed => return true,
        }
    }
}
