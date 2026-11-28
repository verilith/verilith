//! The proxy: a [`Handler`] for verilith-server that routes each request
//! to an upstream, forwards it over a pooled HTTP/1.1 connection, and
//! answers the client with the upstream's response, cached and compressed
//! where that is allowed.
//!
//! Plain Rust, trusted (TRUST.md): the glue between the verified pieces.
//! Every decision about bytes is made by verified code: the request head
//! the upstream reads (`upreq.rs`), which fields cross the proxy
//! (`hop.rs`), how the upstream's response head and framing are read
//! (`upresp.rs` over verilith-http), when a connection is reused
//! (`upresp::reuse_ok`), the route (`route.rs`), the coding
//! (`coding.rs`), whether and how long a response is cached (`rules.rs`),
//! the compressors (verilith-brotli, -zstd, -zlib, each proven to decode
//! back to its input), and what the client is sent (verilith-server's
//! engines). This file moves bytes between sockets and buffers, keeps
//! timers, and picks upstream servers.
//!
//! Each worker thread keeps its own upstream connections, watched on its
//! own poller ([`verilith_server::register`]), so a request is forwarded
//! and answered without leaving the thread that read it.
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use verilith_http::api::{Chunked, ChunkedDecoder};
use verilith_http::parse::Header;
use verilith_http::spec::Body;
use verilith_server::sys::{self, IoResult};
use verilith_server::{Field, Handler, Pending, Request, Response};

use crate::cache::{Cache, Entry};
use crate::coding::{self, Coding};
use crate::route::{self, Route};
use crate::rules::{self, Cc, ReqFacts, RespFacts};
use crate::upresp::{read_head, reuse_ok, Up};
use crate::{fields, hop, upreq};

/// An upstream server: an IPv4 address and port.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Server {
    pub addr: [u8; 4],
    pub port: u16,
}

pub struct Config {
    /// The routes, in order; each names an upstream (an index into
    /// `upstreams`).
    pub routes: Vec<Route>,
    /// Each upstream is a group of servers, used in turn.
    pub upstreams: Vec<Vec<Server>>,
    /// The cache's byte budget (0: no cache), and the largest response
    /// it stores.
    pub cache_bytes: usize,
    pub cache_entry_max: usize,
    /// Compress responses for clients that accept it (Brotli, Zstandard,
    /// gzip). The upstream is then asked for identity bodies.
    pub compress: bool,
    /// The largest response body read from an upstream; longer ones are
    /// answered 502.
    pub max_response: usize,
    pub connect_timeout: Duration,
    /// From the request's last byte written to the response's last byte
    /// read.
    pub response_timeout: Duration,
    /// How long an idle upstream connection is kept, and how many per
    /// server and worker.
    pub idle_timeout: Duration,
    pub idle_max: usize,
    /// How long a server that refused a connection is skipped.
    pub fail_timeout: Duration,
    /// The `Via` pseudonym (RFC 9110 §7.6.3).
    pub via: Vec<u8>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            routes: Vec::new(),
            upstreams: Vec::new(),
            cache_bytes: 64 << 20,
            cache_entry_max: 8 << 20,
            compress: true,
            max_response: 64 << 20,
            connect_timeout: Duration::from_secs(5),
            response_timeout: Duration::from_secs(60),
            idle_timeout: Duration::from_secs(30),
            idle_max: 1024,
            fail_timeout: Duration::from_secs(10),
            via: b"1.1 verilith".to_vec(),
        }
    }
}

/// Field lines in a parsed head, at most.
const MAX_FIELDS: usize = 100;
/// A response head longer than this is refused.
const MAX_HEAD: usize = 64 * 1024;
/// Shortest body worth compressing.
const COMPRESS_MIN: usize = 256;
/// Compression levels: responses compressed once and cached, and
/// responses compressed for one client.
const BR_CACHED: u32 = 6;
const BR_ONCE: u32 = 2;
const ZSTD_LEVEL: i32 = 3;
const GZIP_LEVEL: u32 = 6;

pub struct Proxy {
    cfg: Config,
    cache: Option<Cache>,
    next: Vec<AtomicUsize>,
    /// Per server, the time (ms since `start`) it is used again after a
    /// failure.
    down: Vec<Vec<AtomicU64>>,
    start: Instant,
}

impl Proxy {
    pub fn new(cfg: Config) -> Proxy {
        for r in &cfg.routes {
            assert!(r.upstream < cfg.upstreams.len(), "a route names an upstream that is not configured");
        }
        for u in &cfg.upstreams {
            assert!(!u.is_empty(), "an upstream has no servers");
        }
        let cache = (cfg.cache_bytes > 0).then(|| Cache::new(cfg.cache_bytes, cfg.cache_entry_max));
        let next = cfg.upstreams.iter().map(|_| AtomicUsize::new(0)).collect();
        let down = cfg.upstreams.iter().map(|u| u.iter().map(|_| AtomicU64::new(0)).collect()).collect();
        Proxy { cfg, cache, next, down, start: Instant::now() }
    }

    fn now_ms(&self) -> u64 {
        self.start.elapsed().as_millis() as u64
    }

    /// The next server of upstream `g` not marked down (or the next one,
    /// if all are).
    fn pick(&self, g: usize, avoid: Option<usize>) -> usize {
        let n = self.cfg.upstreams[g].len();
        let first = self.next[g].fetch_add(1, Ordering::Relaxed) % n;
        let now = self.now_ms();
        for k in 0..n {
            let s = (first + k) % n;
            if Some(s) != avoid && self.down[g][s].load(Ordering::Relaxed) <= now {
                return s;
            }
        }
        first
    }

    fn mark_down(&self, g: usize, s: usize) {
        self.down[g][s].store(self.now_ms() + self.cfg.fail_timeout.as_millis() as u64, Ordering::Relaxed);
    }
}

// ---- Requests --------------------------------------------------------------

/// A request on its way to an upstream.
struct Job {
    pending: Pending,
    group: usize,
    /// The request head and body, as written to the upstream.
    req: Vec<u8>,
    /// Safe to send again (RFC 9110 §9.2.2) if a reused connection closes
    /// before answering.
    idempotent: bool,
    tries: u8,
    /// The server the last try went to.
    server: Option<usize>,
    /// What the cache and compression need from the request.
    key: Option<Vec<u8>>,
    facts: ReqFacts,
    accept: Option<Vec<u8>>,
}

fn is_idempotent(m: &[u8]) -> bool {
    matches!(m, b"GET" | b"HEAD" | b"PUT" | b"DELETE" | b"OPTIONS" | b"TRACE")
}

/// The values of every field named `name`, joined by `sep` (RFC 9110
/// §5.3), or `None` if there are none.
fn joined<'a>(fs: impl Iterator<Item = (&'a [u8], &'a [u8])>, name: &[u8], sep: &[u8]) -> Option<Vec<u8>> {
    let mut out: Option<Vec<u8>> = None;
    for (n, v) in fs {
        if n.eq_ignore_ascii_case(name) {
            match &mut out {
                Some(o) => {
                    o.extend_from_slice(sep);
                    o.extend_from_slice(v);
                }
                None => out = Some(v.to_vec()),
            }
        }
    }
    out
}

/// The host of a Host field value, without its port.
fn host_name(h: &[u8]) -> &[u8] {
    if h.first() == Some(&b'[') {
        // An IPv6 literal.
        return match h.iter().position(|&c| c == b']') {
            Some(i) => &h[..=i],
            None => h,
        };
    }
    match h.iter().rposition(|&c| c == b':') {
        Some(i) => &h[..i],
        None => h,
    }
}

fn has_token(v: &[u8], t: &[u8]) -> bool {
    v.split(|&c| c == b',').any(|e| e.trim_ascii().eq_ignore_ascii_case(t))
}

impl Handler for Proxy {
    fn handle(&self, req: &Request, res: &mut Response) {
        let Some(host) = req.header(b"host").or_else(|| req.header(b":authority")) else {
            res.error(400);
            return;
        };
        // The router sees the path as verilith-server's verified
        // resolution reads it; the upstream gets the target as sent.
        let Some((comps, _)) = verilith_server::path::resolve_exec(req.path()) else {
            res.error(400);
            return;
        };
        let name = host_name(host);
        let Some(ri) = route::choose(&self.cfg.routes, name, &comps) else {
            res.error(404);
            return;
        };
        let group = self.cfg.routes[ri].upstream;
        let all = || req.headers().filter(|(n, _)| !n.starts_with(b":"));

        // HEAD is forwarded as GET: the server then writes the length of
        // the body it would send, and the response can be cached.
        let method: &[u8] = if req.method == b"HEAD" { b"GET" } else { req.method };
        let get = method == b"GET";
        let cc = joined(all(), b"cache-control", b", ").map_or_else(no_cc, |v| rules::cc_exec(&v));
        let facts = ReqFacts { get, authorization: req.header(b"authorization").is_some(), cc };
        let accept = joined(all(), b"accept-encoding", b", ");
        let key = match &self.cache {
            Some(_) if get => {
                let mut k = name.to_ascii_lowercase();
                k.push(b' ');
                k.extend_from_slice(req.target);
                Some(k)
            }
            _ => None,
        };
        if let (Some(cache), Some(k)) = (&self.cache, &key) {
            let pragma = joined(all(), b"pragma", b",").is_some_and(|v| has_token(&v, b"no-cache"));
            if req.header(b"range").is_none() && !rules::bypass_exec(&cc, pragma) {
                if let Some(e) = cache.get(k) {
                    let resident = e.stored.elapsed().as_secs();
                    if rules::fresh_exec(e.lifetime, e.age, resident) {
                        self.serve_entry(res, &e, accept.as_deref(), e.age.saturating_add(resident));
                        return;
                    }
                    cache.remove(k);
                }
            }
        }

        // The forwarded fields (verified, `fields::request_fields`): the
        // client's through the hop-by-hop filter, less every field the
        // proxy sets itself, then the proxy's own.
        let fields: Vec<Field> = all().map(|(n, v)| Field { name: n, value: v }).collect();
        let mut own: Vec<Field> = Vec::with_capacity(5);
        let cookie = joined(all(), b"cookie", b"; ");
        let (xff, proto) = match verilith_server::client() {
            Some((a, tls)) => (a.ip().to_string().into_bytes(), if tls { &b"https"[..] } else { b"http" }),
            None => (Vec::new(), &b"http"[..]),
        };
        let mut via = joined(all(), b"via", b", ").map(|mut v| {
            v.extend_from_slice(b", ");
            v
        });
        let via = match via.as_mut() {
            Some(v) => {
                v.extend_from_slice(&self.cfg.via);
                &v[..]
            }
            None => &self.cfg.via[..],
        };
        if let Some(c) = &cookie {
            own.push(Field { name: b"Cookie", value: c });
        }
        if !self.cfg.compress {
            if let Some(a) = &accept {
                own.push(Field { name: b"Accept-Encoding", value: a });
            }
        }
        if !xff.is_empty() {
            own.push(Field { name: b"X-Forwarded-For", value: &xff });
        }
        own.push(Field { name: b"X-Forwarded-Proto", value: proto });
        own.push(Field { name: b"Via", value: via });
        let fwd = fields::request_fields(&fields, &own);
        let body = req.body;
        let cl = (!body.is_empty() || matches!(method, b"POST" | b"PUT" | b"PATCH")).then_some(body.len() as u64);
        let mut buf = Vec::with_capacity(512 + body.len());
        if !upreq::write_request(&mut buf, method, req.target, host, &fwd, cl) {
            res.error(400);
            return;
        }
        buf.extend_from_slice(body);
        let Some(pending) = res.defer() else {
            // Not on an epoll/kqueue worker: nothing to wait on.
            res.error(502);
            return;
        };
        let job = Job { pending, group, req: buf, idempotent: is_idempotent(req.method), tries: 0, server: None, key, facts, accept };
        POOL.with(|p| p.borrow_mut().start(self, job));
    }

    fn on_io(&self, token: u64, readable: bool, writable: bool) {
        POOL.with(|p| p.borrow_mut().event(self, token, readable, writable));
    }

    fn poll_timers(&self) -> Option<u64> {
        POOL.with(|p| p.borrow_mut().timers(self))
    }
}

fn no_cc() -> Cc {
    Cc { no_store: false, no_cache: false, private: false, public: false, must_revalidate: false, max_age: None, s_maxage: None }
}

// ---- Upstream connections --------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum St {
    Connecting,
    Sending,
    Receiving,
    Idle,
}

/// A response being read.
struct Resp {
    status: u16,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    framing: Body,
    persist: bool,
    head_len: usize,
    body: Vec<u8>,
    dec: ChunkedDecoder,
    /// Body bytes received, and those the framing took.
    received: usize,
    used: usize,
    complete: bool,
}

struct Conn {
    fd: i32,
    group: usize,
    server: usize,
    st: St,
    job: Option<Job>,
    off: usize,
    inbuf: Vec<u8>,
    resp: Option<Resp>,
    /// The connection carried an earlier request, and a byte of this
    /// response has arrived.
    reused: bool,
    got: bool,
    deadline: Instant,
}

#[derive(Default)]
struct Pool {
    conns: Vec<Option<Conn>>,
    eras: Vec<u32>,
    free: Vec<usize>,
    idle: HashMap<(usize, usize), Vec<usize>>,
    live: usize,
    scratch: Vec<u8>,
    hs: Vec<Header>,
}

thread_local! {
    static POOL: RefCell<Pool> = RefCell::new(Pool::default());
}

/// How a connection's turn ended.
enum Outcome {
    /// Waiting for the socket.
    Wait,
    /// The response is complete.
    Done,
    /// The connection failed: answer this status (502, 504), or try
    /// again elsewhere if that is safe.
    Fail(u16, bool),
}

impl Pool {
    fn token(&self, i: usize) -> u64 {
        ((self.eras[i] as u64) << 32) | i as u64
    }

    fn alloc(&mut self, c: Conn) -> usize {
        self.live += 1;
        match self.free.pop() {
            Some(i) => {
                self.conns[i] = Some(c);
                i
            }
            None => {
                self.conns.push(Some(c));
                self.eras.push(0);
                self.conns.len() - 1
            }
        }
    }

    fn close(&mut self, i: usize) -> Option<Job> {
        let c = self.conns[i].take()?;
        if c.st == St::Idle {
            if let Some(v) = self.idle.get_mut(&(c.group, c.server)) {
                v.retain(|&j| j != i);
            }
        }
        sys::close_fd(c.fd);
        self.eras[i] = self.eras[i].wrapping_add(1);
        self.free.push(i);
        self.live -= 1;
        c.job
    }

    /// Sends `job` on an idle connection to a server of its upstream, or
    /// a new one.
    fn start(&mut self, p: &Proxy, mut job: Job) {
        let g = job.group;
        let s = p.pick(g, if job.tries > 0 { job.server } else { None });
        job.server = Some(s);
        job.tries += 1;
        if let Some(i) = self.idle.get_mut(&(g, s)).and_then(|v| v.pop()) {
            let c = self.conns[i].as_mut().expect("an idle connection");
            c.st = St::Sending;
            c.job = Some(job);
            c.off = 0;
            c.reused = true;
            c.got = false;
            c.deadline = Instant::now() + p.cfg.response_timeout;
            self.drive(p, i);
            return;
        }
        let srv = p.cfg.upstreams[g][s];
        let fd = match sys::connect_nb(srv.addr, srv.port) {
            Ok(fd) => fd,
            Err(_) => {
                p.mark_down(g, s);
                return self.retry_or(p, job, 502, true);
            }
        };
        let c = Conn {
            fd,
            group: g,
            server: s,
            st: St::Connecting,
            job: Some(job),
            off: 0,
            inbuf: Vec::new(),
            resp: None,
            reused: false,
            got: false,
            deadline: Instant::now() + p.cfg.connect_timeout,
        };
        let i = self.alloc(c);
        if verilith_server::register(fd, self.token(i)).is_err() {
            if let Some(j) = self.close(i) {
                drop(j.pending);
            }
        }
        // The connect completes with a writable event.
    }

    /// Tries `job` once more on another connection if `again` and it has
    /// not been tried twice, else answers `status`.
    fn retry_or(&mut self, p: &Proxy, job: Job, status: u16, again: bool) {
        if again && job.tries < 2 {
            self.start(p, job);
        } else {
            job.pending.complete(move |r: &mut Response| r.error(status));
        }
    }

    fn event(&mut self, p: &Proxy, token: u64, readable: bool, writable: bool) {
        let i = (token & 0xffff_ffff) as usize;
        if i >= self.conns.len() || self.eras[i] != (token >> 32) as u32 || self.conns[i].is_none() {
            return;
        }
        let st = self.conns[i].as_ref().unwrap().st;
        match st {
            St::Idle => {
                // Unasked bytes, or the server closed: never reuse it.
                if readable {
                    self.close(i);
                }
            }
            St::Connecting => {
                if writable || readable {
                    let c = self.conns[i].as_mut().unwrap();
                    if sys::take_error(c.fd).is_some() {
                        let (g, s) = (c.group, c.server);
                        p.mark_down(g, s);
                        if let Some(job) = self.close(i) {
                            self.retry_or(p, job, 502, true);
                        }
                        return;
                    }
                    c.st = St::Sending;
                    c.deadline = Instant::now() + p.cfg.response_timeout;
                    self.drive(p, i);
                }
            }
            St::Sending | St::Receiving => self.drive(p, i),
        }
    }

    /// Writes what is left of the request, then reads what has come of
    /// the response, as far as the socket allows.
    fn drive(&mut self, p: &Proxy, i: usize) {
        let out = self.step(p, i);
        match out {
            Outcome::Wait => {}
            Outcome::Done => self.finish(p, i),
            Outcome::Fail(status, again) => {
                if let Some(job) = self.close(i) {
                    self.retry_or(p, job, status, again);
                }
            }
        }
    }

    fn step(&mut self, p: &Proxy, i: usize) -> Outcome {
        let c = self.conns[i].as_mut().unwrap();
        let job = c.job.as_ref().unwrap();
        // A reused connection the server closed before answering: the
        // request may be sent again if it is idempotent.
        let again = |c: &Conn| c.reused && !c.got && c.job.as_ref().is_some_and(|j| j.idempotent);
        if c.st == St::Sending {
            while c.off < job.req.len() {
                match sys::write_slices(c.fd, &[&job.req[c.off..]], false) {
                    IoResult::Done(n) => c.off += n,
                    IoResult::WouldBlock => return Outcome::Wait,
                    IoResult::Closed => return Outcome::Fail(502, again(c)),
                }
            }
            c.st = St::Receiving;
        }
        if self.scratch.len() < 64 * 1024 {
            self.scratch.resize(64 * 1024, 0);
        }
        loop {
            let c = self.conns[i].as_mut().unwrap();
            match sys::read_into(c.fd, &mut self.scratch) {
                IoResult::Done(0) => continue,
                IoResult::Done(n) => {
                    c.got = true;
                    match feed(c, &mut self.scratch[..n], &mut self.hs, p.cfg.max_response) {
                        Ok(true) => return Outcome::Done,
                        Ok(false) => {}
                        Err(()) => return Outcome::Fail(502, false),
                    }
                }
                IoResult::WouldBlock => return Outcome::Wait,
                IoResult::Closed => {
                    return match &mut c.resp {
                        Some(r) if matches!(r.framing, Body::Close) => {
                            r.complete = true;
                            Outcome::Done
                        }
                        _ => Outcome::Fail(502, again(c)),
                    };
                }
            }
        }
    }

    /// The response is read: the connection goes back to the pool if
    /// [`reuse_ok`] allows it, and the client gets its answer.
    fn finish(&mut self, p: &Proxy, i: usize) {
        let c = self.conns[i].as_mut().unwrap();
        let r = c.resp.take().unwrap();
        let job = c.job.take().unwrap();
        let reuse = reuse_ok(r.persist, r.framing, r.head_len + r.used, r.head_len + r.received);
        let key = (c.group, c.server);
        let pooled = self.idle.get(&key).map_or(0, |v| v.len());
        if reuse && pooled < p.cfg.idle_max {
            c.st = St::Idle;
            c.inbuf.clear();
            c.deadline = Instant::now() + p.cfg.idle_timeout;
            self.idle.entry(key).or_default().push(i);
        } else {
            self.close(i);
        }
        p.deliver(job, r);
    }

    /// Closes connections past their deadline; returns how long until the
    /// next one is due (microseconds).
    fn timers(&mut self, p: &Proxy) -> Option<u64> {
        if self.live == 0 {
            return None;
        }
        let now = Instant::now();
        let mut next: Option<Instant> = None;
        for i in 0..self.conns.len() {
            let Some(c) = &self.conns[i] else { continue };
            if c.deadline > now {
                next = Some(next.map_or(c.deadline, |n| n.min(c.deadline)));
                continue;
            }
            let (st, g, s) = (c.st, c.group, c.server);
            let job = self.close(i);
            match (st, job) {
                (St::Connecting, Some(job)) => {
                    p.mark_down(g, s);
                    self.retry_or(p, job, 504, true);
                }
                (_, Some(job)) => job.pending.complete(|r: &mut Response| r.error(504)),
                _ => {}
            }
        }
        next.map(|n| n.saturating_duration_since(now).as_micros() as u64 + 1000)
    }
}

/// Takes `bytes` read from the upstream: true once the response is
/// complete, an error if it cannot be forwarded.
fn feed(c: &mut Conn, bytes: &mut [u8], hs: &mut Vec<Header>, max: usize) -> Result<bool, ()> {
    if c.resp.is_none() {
        c.inbuf.extend_from_slice(bytes);
        loop {
            hs.clear();
            match read_head(&c.inbuf, MAX_FIELDS, false, hs) {
                Up::Partial => {
                    return if c.inbuf.len() > MAX_HEAD { Err(()) } else { Ok(false) };
                }
                Up::Bad => return Err(()),
                Up::Interim(n) => {
                    c.inbuf.drain(..n);
                }
                Up::Final { status, head_len, body, persist } => {
                    let fields = hs.iter().map(|h| (h.name.of(&c.inbuf).to_vec(), h.value.of(&c.inbuf).to_vec())).collect();
                    let mut rest = c.inbuf.split_off(head_len);
                    c.resp = Some(Resp {
                        status,
                        fields,
                        framing: body,
                        persist,
                        head_len,
                        body: Vec::new(),
                        dec: ChunkedDecoder::new(),
                        received: 0,
                        used: 0,
                        complete: false,
                    });
                    return body_bytes(c.resp.as_mut().unwrap(), &mut rest, max);
                }
            }
        }
    }
    body_bytes(c.resp.as_mut().unwrap(), bytes, max)
}

fn body_bytes(r: &mut Resp, raw: &mut [u8], max: usize) -> Result<bool, ()> {
    r.received += raw.len();
    if !r.complete {
        match r.framing {
            Body::Empty => r.complete = true,
            Body::Length(n) => {
                let want = (n as usize).saturating_sub(r.body.len());
                if n as usize > max {
                    return Err(());
                }
                let take = want.min(raw.len());
                r.body.extend_from_slice(&raw[..take]);
                r.used += take;
                r.complete = r.body.len() as u64 == n;
            }
            Body::Chunked => match r.dec.decode(raw) {
                Ok(Chunked::More { out }) => {
                    r.body.extend_from_slice(&raw[..out]);
                    r.used += raw.len();
                }
                Ok(Chunked::Done { out, rest }) => {
                    r.body.extend_from_slice(&raw[..out]);
                    r.used += raw.len() - rest;
                    r.complete = true;
                }
                Err(_) => return Err(()),
            },
            Body::Close => r.body.extend_from_slice(raw),
        }
    }
    if r.body.len() > max {
        return Err(());
    }
    Ok(r.complete)
}

// ---- Responses -------------------------------------------------------------

/// Whether a response's media type is worth compressing.
fn compressible_type(ct: &[u8]) -> bool {
    let t = ct.split(|&c| c == b';').next().unwrap_or(b"").trim_ascii().to_ascii_lowercase();
    t.starts_with(b"text/")
        || t.ends_with(b"+json")
        || t.ends_with(b"+xml")
        || matches!(
            &t[..],
            b"application/json" | b"application/javascript" | b"application/x-javascript" | b"application/xml"
                | b"application/wasm" | b"image/svg+xml" | b"application/manifest+json"
        )
}

fn find<'a>(fs: &'a [(Vec<u8>, Vec<u8>)], name: &[u8]) -> Option<&'a [u8]> {
    fs.iter().find(|(n, _)| n.eq_ignore_ascii_case(name)).map(|(_, v)| &v[..])
}

fn compress(c: Coding, body: &[u8], cached: bool) -> Option<Vec<u8>> {
    Some(match c {
        Coding::Br => verilith_brotli::compress::compress(body, if cached { BR_CACHED } else { BR_ONCE }, 22),
        Coding::Zstd => {
            if body.len() > verilith_zstd::compress::IN_MAX {
                return None;
            }
            verilith_zstd::compress::compress(body, ZSTD_LEVEL, false)
        }
        Coding::Gzip => verilith_zlib::gzip_compress(body, GZIP_LEVEL),
    })
}

/// The coding to send to a client whose Accept-Encoding is `accept`.
/// Brotli is for bodies compressed once and cached: at quality 2 it takes
/// about twice as long as Zstandard level 3 on a 16 KiB page, for larger
/// output, so a response compressed for one client gets Zstandard or gzip
/// when the client takes either.
fn coding_for(accept: Option<&[u8]>, once: bool) -> Option<Coding> {
    let a = accept?;
    if once {
        coding::choose(a, false, true, true).or_else(|| coding::choose(a, true, false, false))
    } else {
        coding::choose(a, true, true, true)
    }
}

fn coding_name(c: Coding) -> &'static [u8] {
    match c {
        Coding::Br => b"br",
        Coding::Zstd => b"zstd",
        Coding::Gzip => b"gzip",
    }
}

/// What the client is sent.
struct Answer {
    status: u16,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    body: Arc<[u8]>,
}

impl Answer {
    fn send(&self, r: &mut Response) {
        let fs: Vec<Field> = self.fields.iter().map(|(n, v)| Field { name: n, value: v }).collect();
        if r.send_shared(self.status, &fs, &self.body).is_err() {
            r.error(502);
        }
    }
}

/// The response's fields as the client gets them: the verified
/// hop-by-hop filter, without the fields the server writes itself (Date,
/// Server) and Age (the cache sets its own).
fn client_fields(fs: &[(Vec<u8>, Vec<u8>)]) -> Vec<(Vec<u8>, Vec<u8>)> {
    let all: Vec<Field> = fs.iter().map(|(n, v)| Field { name: n, value: v }).collect();
    fields::response_fields(&all).iter().map(|f| (f.name.to_vec(), f.value.to_vec())).collect()
}

/// Adds Content-Encoding and Vary for a compressed body, and weakens a
/// strong ETag (the compressed bytes are a different representation:
/// RFC 9110 §8.8.3).
fn encoded(fields: &mut Vec<(Vec<u8>, Vec<u8>)>, c: Option<Coding>) {
    if !find(fields, b"vary").is_some_and(|v| has_token(v, b"accept-encoding")) {
        fields.push((b"Vary".to_vec(), b"Accept-Encoding".to_vec()));
    }
    let Some(c) = c else { return };
    fields.push((b"Content-Encoding".to_vec(), coding_name(c).to_vec()));
    for (n, v) in fields.iter_mut() {
        if n.eq_ignore_ascii_case(b"etag") && v.first() == Some(&b'"') {
            v.splice(0..0, *b"W/");
        }
    }
}

impl Proxy {
    /// Whether the proxy may compress this response.
    fn may_compress(&self, status: u16, fs: &[(Vec<u8>, Vec<u8>)], len: usize) -> bool {
        self.cfg.compress
            && status == 200
            && len >= COMPRESS_MIN
            && find(fs, b"content-encoding").is_none()
            && find(fs, b"content-range").is_none()
            && find(fs, b"content-type").is_some_and(compressible_type)
            && !find(fs, b"cache-control").is_some_and(|v| has_token(v, b"no-transform"))
    }

    fn serve_entry(&self, res: &mut Response, e: &Entry, accept: Option<&[u8]>, age: u64) {
        let mut fields = e.fields.clone();
        let mut body = e.body.clone();
        if e.compressible {
            let c = coding_for(accept, false).and_then(|c| match e.variant(c) {
                Some(b) => Some((c, b)),
                None => {
                    let b: Arc<[u8]> = compress(c, &e.body, true)?.into();
                    e.set_variant(c, b.clone());
                    Some((c, b))
                }
            });
            encoded(&mut fields, c.as_ref().map(|x| x.0));
            if let Some((_, b)) = c {
                body = b;
            }
        }
        fields.push((b"Age".to_vec(), age.to_string().into_bytes()));
        Answer { status: e.status, fields, body }.send(res);
    }

    /// Answers `job` with the upstream's response `r`, storing it first if
    /// the verified rules allow.
    fn deliver(&self, job: Job, r: Resp) {
        let mut fields = client_fields(&r.fields);
        let body: Arc<[u8]> = r.body.into();
        let compressible = self.may_compress(r.status, &fields, body.len());
        let mut store = None;
        if let (Some(cache), Some(key)) = (&self.cache, job.key) {
            let iter = || r.fields.iter().map(|(n, v)| (&n[..], &v[..]));
            let cc = joined(iter(), b"cache-control", b", ").map_or_else(no_cc, |v| rules::cc_exec(&v));
            let vary_ok = joined(iter(), b"vary", b", ")
                .is_none_or(|v| v.split(|&c| c == b',').all(|e| e.trim_ascii().eq_ignore_ascii_case(b"accept-encoding")));
            let rf = RespFacts { status: r.status, set_cookie: find(&r.fields, b"set-cookie").is_some(), vary_ok, cc };
            // A body the upstream encoded itself depends on an
            // Accept-Encoding the key does not hold.
            let encoded_up = find(&r.fields, b"content-encoding").is_some();
            match rules::decide(&job.facts, &rf) {
                Some(lifetime) if !encoded_up && body.len() <= cache.max_entry => {
                    let age = find(&r.fields, b"age").and_then(rules::delta_exec).unwrap_or(0);
                    store = Some((cache, key, lifetime, age));
                }
                _ => cache.remove(&key),
            }
        }
        let c = if compressible {
            coding_for(job.accept.as_deref(), store.is_none()).and_then(|c| Some((c, Arc::<[u8]>::from(compress(c, &body, store.is_some())?))))
        } else {
            None
        };
        if let Some((cache, key, lifetime, age)) = store {
            let e = Entry {
                status: r.status,
                fields: fields.clone(),
                body: body.clone(),
                stored: Instant::now(),
                lifetime,
                age,
                compressible,
                variants: Default::default(),
            };
            if let Some((k, b)) = &c {
                e.set_variant(*k, b.clone());
            }
            cache.put(key, e);
        }
        if compressible {
            encoded(&mut fields, c.as_ref().map(|x| x.0));
        }
        let out = c.map_or(body, |x| x.1);
        let a = Answer { status: r.status, fields, body: out };
        job.pending.complete(move |res: &mut Response| a.send(res));
    }
}
