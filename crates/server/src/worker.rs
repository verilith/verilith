//! The thread-per-core event loop (DESIGN.md, "I/O model").
//!
//! Each worker owns a poller, a listening socket (Linux: its own, with
//! SO_REUSEPORT; macOS: a shared one), and its connections. A connection
//! never leaves its worker. Per readiness event: read until the kernel has
//! nothing more, let the engine handle every complete request, and write
//! all the responses with one call.
use std::io;
use std::sync::Arc;

use crate::h1::{Conn, Ctx, Io, Limits, Next};
use crate::h2::{Conn2, Limits2};
use crate::sys::{self, IoResult};
use crate::Handler;

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
    pub tls: Option<(u16, Arc<rustls::ServerConfig>)>,
    /// The `Server` field value.
    pub server: &'static [u8],
    /// Empty polls before a worker sleeps. 0 (the default) sleeps at once;
    /// a few hundred trade CPU for lower latency when connections are
    /// short (`h1-close`: +14% requests, twice the CPU).
    pub spin: u32,
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
            server: b"verilith",
            spin: 0,
        }
    }
}

/// Listener tokens count down from here; connection tokens are slot indices.
const LISTENER: u64 = u64::MAX;

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
        let cfg = cfg.clone();
        let h = handler.clone();
        let cpu = if cpus.is_empty() { i } else { cpus[i % cpus.len()] };
        joins.push(std::thread::Builder::new().name(format!("verilith-w{i}")).spawn(move || {
            if cfg.pin {
                sys::pin_to_cpu(cpu);
            }
            Worker::new(lfd, cfg).and_then(|mut w| w.run(&*h))
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
            Any::Tls(c) => Io::Slices(c.pending(out), Default::default()),
        }
    }
    fn pending_len(&self) -> usize {
        each!(self, c => c.pending_len())
    }
    fn wrote(&mut self, n: usize) {
        each!(self, c => c.wrote(n))
    }
}

struct Slot {
    fd: i32,
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
}

impl Worker {
    fn new(lfds: Vec<(i32, Proto)>, cfg: Config) -> io::Result<Worker> {
        let poll = sys::Poller::new(1024)?;
        for (i, (fd, _)) in lfds.iter().enumerate() {
            poll.add(*fd, LISTENER - i as u64, false)?;
        }
        let now = sys::unix_time();
        let ctx = Ctx::new(cfg.server, &crate::date::imf_fixdate(now))
            .ok_or_else(|| io::Error::other("the Server value is not a valid field value"))?;
        Ok(Worker { lfds, poll, slots: Vec::new(), free: Vec::new(), spare: Vec::new(), cfg, now, ctx })
    }

    fn run<H: Handler + ?Sized>(&mut self, h: &H) -> io::Result<()> {
        let mut evs = Vec::with_capacity(1024);
        let spin = self.cfg.spin;
        let mut idle = 0u32;
        loop {
            evs.clear();
            let n = self.poll.wait(if idle < spin { 0 } else { 1000 }, |e| evs.push(e));
            idle = if n == 0 { idle.saturating_add(1) } else { 0 };
            let t = sys::unix_time();
            if t != self.now {
                self.now = t;
                if let Some(c) = Ctx::new(self.cfg.server, &crate::date::imf_fixdate(t)) {
                    self.ctx = c;
                }
            }
            for e in &evs {
                if e.token > LISTENER - 16 {
                    self.accept_all(h, (LISTENER - e.token) as usize);
                } else {
                    self.on_event(h, e.token as usize, e.readable, e.writable);
                }
            }
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
                    Some(t) => Any::Tls(Box::new(t)),
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
            self.slots[id] = Some(Slot { fd, conn, read_paused: false });
            if self.poll.add(fd, id as u64, true).is_err() {
                self.close(id);
                continue;
            }
            // The request often arrives with the connection.
            self.on_event(h, id, true, false);
        }
    }

    fn on_event<H: Handler + ?Sized>(&mut self, h: &H, id: usize, readable: bool, writable: bool) {
        let ctx = &self.ctx;
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        let mut close = false;
        if writable || s.read_paused {
            close = flush(s);
        }
        if !close && (readable || s.read_paused) {
            close = read_process_write(s, h, ctx);
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
        if flush(s) {
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
        }
    }
}

/// Writes what is pending. Returns whether the connection is broken, or
/// closing with nothing left to write.
#[inline]
fn flush(s: &mut Slot) -> bool {
    loop {
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
