//! The thread-per-core event loop (DESIGN.md, "I/O model").
//!
//! Each worker owns a poller, a listening socket (Linux: its own, with
//! SO_REUSEPORT; macOS: a shared one), and its connections. A connection
//! never leaves its worker. Per readiness event: read until the kernel has
//! nothing more, let the engine handle every complete request, and write
//! all the responses with one call.
use std::io;
use std::sync::Arc;

use crate::h1::{Conn, Ctx, Limits, Next};
use crate::sys::{self, IoResult};
use crate::Handler;

/// How to run the server.
#[derive(Clone, Debug)]
pub struct Config {
    pub addr: [u8; 4],
    pub port: u16,
    /// Worker threads. 0: one per CPU this process may use.
    pub threads: usize,
    /// Pin worker `i` to the `i`th allowed CPU (Linux).
    pub pin: bool,
    pub limits: Limits,
    /// The `Server` field value.
    pub server: &'static [u8],
}

impl Default for Config {
    fn default() -> Self {
        Config { addr: [127, 0, 0, 1], port: 8080, threads: 0, pin: true, limits: Limits::default(), server: b"verilith" }
    }
}

const LISTENER: u64 = u64::MAX;

/// Runs the server on the calling thread and `threads - 1` more, until the
/// process exits.
pub fn serve<H: Handler>(cfg: Config, handler: Arc<H>) -> io::Result<()> {
    sys::ignore_sigpipe();
    let cpus = sys::allowed_cpus();
    let n = if cfg.threads == 0 { cpus.len().max(1) } else { cfg.threads };
    // macOS: one listening socket for all, created before the workers start.
    let shared = if sys::REUSEPORT_BALANCES { None } else { Some(sys::listen_tcp(cfg.addr, cfg.port, false, 65535)?) };
    let mut joins = Vec::new();
    for i in 0..n {
        let lfd = match shared {
            Some(fd) => fd,
            None => sys::listen_tcp(cfg.addr, cfg.port, true, 65535)?,
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

struct Slot {
    fd: i32,
    conn: Conn,
    /// Reading stopped because the write buffer was full.
    read_paused: bool,
}

struct Worker {
    lfd: i32,
    poll: sys::Poller,
    slots: Vec<Option<Slot>>,
    free: Vec<usize>,
    /// Connections closed and reusable, buffers and all.
    spare: Vec<Conn>,
    cfg: Config,
    now: i64,
    date: [u8; 29],
}

impl Worker {
    fn new(lfd: i32, cfg: Config) -> io::Result<Worker> {
        let poll = sys::Poller::new(1024)?;
        poll.add(lfd, LISTENER, false)?;
        let now = sys::unix_time();
        Ok(Worker { lfd, poll, slots: Vec::new(), free: Vec::new(), spare: Vec::new(), cfg, now, date: crate::date::imf_fixdate(now) })
    }

    fn run<H: Handler + ?Sized>(&mut self, h: &H) -> io::Result<()> {
        let mut evs = Vec::with_capacity(1024);
        loop {
            evs.clear();
            self.poll.wait(1000, |e| evs.push(e));
            let t = sys::unix_time();
            if t != self.now {
                self.now = t;
                self.date = crate::date::imf_fixdate(t);
            }
            for e in &evs {
                if e.token == LISTENER {
                    self.accept_all(h);
                } else {
                    self.on_event(h, e.token as usize, e.readable, e.writable);
                }
            }
        }
    }

    fn accept_all<H: Handler + ?Sized>(&mut self, h: &H) {
        while let Some(fd) = sys::accept_nb(self.lfd) {
            sys::set_nodelay(fd);
            let conn = match self.spare.pop() {
                Some(c) => c,
                None => Conn::new(self.cfg.limits),
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
        let ctx = Ctx { date: &self.date, server: self.cfg.server };
        let Some(Some(s)) = self.slots.get_mut(id) else { return };
        let mut close = false;
        if writable || s.read_paused {
            close = flush(s);
        }
        if !close && (readable || s.read_paused) {
            close = read_process_write(s, h, &ctx);
        }
        if close {
            self.close(id);
        }
    }

    fn close(&mut self, id: usize) {
        if let Some(s) = self.slots[id].take() {
            self.poll.remove(s.fd);
            sys::close_fd(s.fd);
            if self.spare.len() < 1024 {
                let mut c = s.conn;
                c.reset();
                self.spare.push(c);
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
        let k = s.conn.pending(&mut v);
        match sys::write_slices(s.fd, &v[..k]) {
            IoResult::Done(n) => s.conn.wrote(n),
            IoResult::WouldBlock => return false,
            IoResult::Closed => return true,
        }
    }
}
