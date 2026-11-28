//! The listeners (unverified glue; TRUST.md): DNS over UDP and TCP (RFC
//! 1035 §4.2, RFC 7766), DNS over TLS (RFC 7858) on verilith-tls, and DNS
//! over HTTPS (RFC 8484) on verilith-server. Every message from a client
//! goes to the verified `frontend::serve` and every reply comes from it.
use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use crate::cache::Cache;
use crate::net::{Upstream, ROOTS_V4};
use crate::resolve::{Net, Shared};

/// What a resolver is started with.
#[derive(Clone)]
pub struct Options {
    /// Root server addresses (4 or 16 bytes each).
    pub roots: Vec<Vec<u8>>,
    /// The port to ask servers on (53; another for a test hierarchy).
    pub upstream_port: u16,
    pub timeout: Duration,
    /// Cache shards and sets per shard (each set holds `cache::WAYS`
    /// entries).
    pub shards: usize,
    pub sets: usize,
    /// DNSSEC trust anchors: DS RDATA (key tag, algorithm, digest type,
    /// digest) for the root zone. Empty: no validation. Fixed for the
    /// process (see `trust::set_anchors`).
    pub trust_anchors: Vec<Vec<u8>>,
}

/// The root zone's trust anchors as IANA publishes them
/// (<https://data.iana.org/root-anchors/root-anchors.xml>): KSK-2017 and
/// KSK-2024, as DS RDATA (SHA-256 digests).
pub fn iana_root_anchors() -> Vec<Vec<u8>> {
    [
        (20326u16, "E06D44B80B8F1D39A95C0B0D7C65D08458E880409BBC683457104237C7F8EC8D"),
        (38696u16, "683D2D0ACB8C9B712A1948B27F741219298D0A450D612C483AF444A4C0FB2B16"),
    ]
    .iter()
    .map(|(tag, hex)| {
        let mut d = tag.to_be_bytes().to_vec();
        d.push(8); // RSA/SHA-256
        d.push(2); // SHA-256
        d.extend(parse_hex(hex).unwrap());
        d
    })
    .collect()
}

/// Parses hexadecimal digits (any case; spaces ignored).
pub fn parse_hex(s: &str) -> Option<Vec<u8>> {
    let h: Vec<u8> = s.bytes().filter(|c| !c.is_ascii_whitespace()).collect();
    if h.len() % 2 != 0 {
        return None;
    }
    h.chunks(2)
        .map(|p| u8::from_str_radix(std::str::from_utf8(p).ok()?, 16).ok())
        .collect()
}

/// A DS trust anchor in presentation form, `<tag> <alg> <digest type>
/// <hex digest>` (as in a DS record's RDATA, RFC 4034 §5.3), as RDATA.
pub fn parse_ds(s: &str) -> Option<Vec<u8>> {
    let mut f = s.split_whitespace();
    let tag: u16 = f.next()?.parse().ok()?;
    let alg: u8 = f.next()?.parse().ok()?;
    let dt: u8 = f.next()?.parse().ok()?;
    let digest = parse_hex(&f.collect::<String>())?;
    let mut d = tag.to_be_bytes().to_vec();
    d.push(alg);
    d.push(dt);
    d.extend(digest);
    Some(d)
}

impl Default for Options {
    fn default() -> Self {
        Options {
            roots: ROOTS_V4.iter().map(|a| a.to_vec()).collect(),
            upstream_port: 53,
            timeout: Duration::from_millis(1500),
            shards: 64,
            sets: 4096,
            trust_anchors: iana_root_anchors(),
        }
    }
}

pub struct Resolver {
    roots: Vec<Vec<u8>>,
    net: Net,
    cache: Shared,
}

impl Resolver {
    pub fn new(o: &Options) -> Resolver {
        let roots: Vec<Vec<u8>> = o.roots.iter().filter(|a| a.len() == 4 || a.len() == 16).cloned().collect();
        assert!(!roots.is_empty(), "no root server addresses");
        let sets = o.sets.clamp(1, 0x1000_0000);
        assert!(
            crate::trust::set_anchors(o.trust_anchors.clone()),
            "trust anchors are fixed for the process, and differ from those already in force"
        );
        Resolver {
            roots,
            net: Net { t: Arc::new(Upstream::new(o.upstream_port, o.timeout)) },
            cache: Shared::new(o.shards.max(1), sets),
        }
    }

    /// The reply to a client's message, if it gets one.
    pub fn answer(&self, query: &[u8], udp: bool) -> Option<Vec<u8>> {
        self.answer_with(query, udp, crate::frontend::QUERY_BUDGET)
    }

    /// The reply from the cache alone: `None` if the message gets no
    /// reply, `Some(None)` if answering it needs queries to servers.
    pub fn answer_cached(&self, query: &[u8], udp: bool) -> Option<Option<Vec<u8>>> {
        let r = self.answer_with(query, udp, 0)?;
        // SERVFAIL with a budget of 0: something was not in the cache.
        Some(if r.len() >= 4 && r[3] & 15 == 2 { None } else { Some(r) })
    }

    fn answer_with(&self, query: &[u8], udp: bool, budget: u32) -> Option<Vec<u8>> {
        crate::frontend::serve(&self.roots, &self.net, &self.cache, query, udp, budget).map(|r| r.0)
    }
}

/// Serves UDP on `sock`: one receiving thread per CPU answers from the
/// cache, and hands questions that need servers to a pool of `workers`
/// threads (dropping them when `QUEUE` are already waiting).
pub fn udp(r: Arc<Resolver>, sock: UdpSocket, workers: usize) -> io::Result<Vec<std::thread::JoinHandle<()>>> {
    const QUEUE: usize = 8192;
    let (tx, rx) = std::sync::mpsc::sync_channel::<(Vec<u8>, SocketAddr)>(QUEUE);
    let rx = Arc::new(Mutex::new(rx));
    let mut hs = Vec::new();
    for _ in 0..workers.max(1) {
        let (s, r, rx) = (sock.try_clone()?, r.clone(), rx.clone());
        hs.push(std::thread::spawn(move || loop {
            let job = rx.lock().unwrap_or_else(|e| e.into_inner()).recv();
            let Ok((q, from)) = job else { return };
            if let Some(out) = r.answer(&q, true) {
                let _ = s.send_to(&out, from);
            }
        }));
    }
    let cpus = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    for _ in 0..cpus {
        let (s, r, tx) = (sock.try_clone()?, r.clone(), tx.clone());
        hs.push(std::thread::spawn(move || {
            let mut buf = vec![0u8; 65535];
            loop {
                let (n, from) = match s.recv_from(&mut buf) {
                    Ok(x) => x,
                    Err(_) => continue,
                };
                match r.answer_cached(&buf[..n], true) {
                    Some(Some(out)) => {
                        let _ = s.send_to(&out, from);
                    }
                    Some(None) => {
                        let _ = tx.try_send((buf[..n].to_vec(), from));
                    }
                    None => {}
                }
            }
        }));
    }
    Ok(hs)
}

/// The most TCP, DoT connections served at once.
pub const MAX_CONNS: usize = 4096;
/// How long a TCP or DoT connection may stay idle (RFC 7766 §6.2.3).
pub const IDLE: Duration = Duration::from_secs(10);

static CONNS: AtomicUsize = AtomicUsize::new(0);

struct Slot;
impl Drop for Slot {
    fn drop(&mut self) {
        CONNS.fetch_sub(1, Ordering::Relaxed);
    }
}

fn take_slot() -> Option<Slot> {
    if CONNS.fetch_add(1, Ordering::Relaxed) >= MAX_CONNS {
        CONNS.fetch_sub(1, Ordering::Relaxed);
        return None;
    }
    Some(Slot)
}

/// Takes each two-byte-length-prefixed message from `buf` (RFC 1035
/// §4.2.2), answers it, and appends the framed replies to `out`.
fn frames(r: &Resolver, buf: &mut Vec<u8>, out: &mut Vec<u8>) {
    let mut at = 0;
    while buf.len() - at >= 2 {
        let n = u16::from_be_bytes([buf[at], buf[at + 1]]) as usize;
        if buf.len() - at - 2 < n {
            break;
        }
        if let Some(rep) = r.answer(&buf[at + 2..at + 2 + n], false) {
            out.extend_from_slice(&(rep.len() as u16).to_be_bytes());
            out.extend_from_slice(&rep);
        }
        at += 2 + n;
    }
    buf.drain(..at);
}

/// Serves DNS over TCP on `l`, a thread per connection.
pub fn tcp(r: Arc<Resolver>, l: TcpListener) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        for c in l.incoming() {
            let Ok(mut c) = c else { continue };
            let Some(slot) = take_slot() else { continue };
            let r = r.clone();
            std::thread::spawn(move || {
                let _slot = slot;
                let _ = c.set_read_timeout(Some(IDLE));
                let _ = c.set_nodelay(true);
                let mut buf = Vec::new();
                let mut chunk = vec![0u8; 16384];
                let mut out = Vec::new();
                loop {
                    let n = match c.read(&mut chunk) {
                        Ok(0) | Err(_) => return,
                        Ok(n) => n,
                    };
                    buf.extend_from_slice(&chunk[..n]);
                    if buf.len() > 2 * 65537 {
                        return;
                    }
                    frames(&r, &mut buf, &mut out);
                    if !out.is_empty() {
                        if c.write_all(&out).is_err() {
                            return;
                        }
                        out.clear();
                    }
                }
            });
        }
    })
}

#[cfg(feature = "tls")]
pub mod tls {
    use super::*;
    use verilith_tls::stream::ServerStream;
    use verilith_tls_aws_lc::{AwsLc, SigningKey, TicketKeys, GROUPS, SUITES};

    /// A DoT server's TLS configuration.
    pub struct DotConfig {
        cfg: Arc<verilith_tls::server::Config>,
        key: Arc<SigningKey>,
        tickets: Arc<TicketKeys>,
    }

    fn bad(m: &str) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, m.to_string())
    }

    /// From PEM files: the certificate chain, and a PKCS#8 key. ALPN "dot"
    /// (RFC 7858 §3.2 and the IANA registry).
    pub fn dot_config(cert: &str, key: &str) -> io::Result<DotConfig> {
        let chain = verilith_server::tls::pem_blocks(&std::fs::read(cert)?, "CERTIFICATE");
        let keys = verilith_server::tls::pem_blocks(&std::fs::read(key)?, "PRIVATE KEY");
        let k = keys.first().ok_or_else(|| bad("no PKCS#8 \"PRIVATE KEY\" block in the key file"))?;
        let key = SigningKey::from_pkcs8(k).ok_or_else(|| bad("the key is not PKCS#8 ECDSA, Ed25519 or RSA"))?;
        let mut cfg = verilith_tls::server::Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), b"\x03dot".to_vec(), &chain)
            .ok_or_else(|| bad("the certificate chain is empty or too long"))?;
        cfg.set_tickets(2, 6 * 3600);
        Ok(DotConfig { cfg: Arc::new(cfg), key: Arc::new(key), tickets: Arc::new(TicketKeys::new(6 * 3600)) })
    }

    fn dot_conn(r: &Resolver, d: &DotConfig, mut c: TcpStream) -> Option<()> {
        c.set_read_timeout(Some(IDLE)).ok()?;
        let _ = c.set_nodelay(true);
        let mut tls = ServerStream::new(d.cfg.clone(), AwsLc::shared(d.key.clone()).with_tickets(d.tickets.clone()));
        let mut chunk = vec![0u8; 16384];
        let mut buf = Vec::new();
        let mut out = Vec::new();
        loop {
            let n = c.read(&mut chunk).ok()?;
            if n == 0 {
                return None;
            }
            tls.read_tls(&chunk[..n]);
            let ok = tls.process().is_ok();
            buf.extend_from_slice(tls.plaintext());
            let k = tls.plaintext().len();
            tls.consume_plaintext(k);
            if buf.len() > 2 * 65537 {
                return None;
            }
            frames(r, &mut buf, &mut out);
            if !out.is_empty() {
                tls.write(&out).ok()?;
                out.clear();
            }
            if !tls.pending().is_empty() {
                c.write_all(tls.pending()).ok()?;
                let p = tls.pending().len();
                tls.consume_pending(p);
            }
            if !ok || tls.peer_closed() {
                return None;
            }
        }
    }

    /// Serves DNS over TLS on `l`, a thread per connection.
    pub fn dot(r: Arc<Resolver>, d: Arc<DotConfig>, l: TcpListener) -> std::thread::JoinHandle<()> {
        std::thread::spawn(move || {
            for c in l.incoming() {
                let Ok(c) = c else { continue };
                let Some(slot) = take_slot() else { continue };
                let (r, d) = (r.clone(), d.clone());
                std::thread::spawn(move || {
                    let _slot = slot;
                    let _ = dot_conn(&r, &d, c);
                });
            }
        })
    }

    /// The `dns` parameter of a GET's query string (RFC 8484 §4.1).
    fn dns_param(target: &[u8]) -> Option<&[u8]> {
        let q = &target[target.iter().position(|&c| c == b'?')? + 1..];
        q.split(|&c| c == b'&').find_map(|p| p.strip_prefix(b"dns="))
    }

    fn base64url(s: &[u8]) -> Option<Vec<u8>> {
        use verilith_text::base64::forgiving::{decode_forgiving, max_len_exec};
        let mut out = vec![0u8; max_len_exec(s)];
        let n = decode_forgiving(true, s, &mut out).ok()?;
        out.truncate(n);
        Some(out)
    }

    /// The smallest TTL in a reply's answer and authority sections, for
    /// Cache-Control (RFC 8484 §5.1).
    fn min_ttl(reply: &[u8]) -> u32 {
        use verilith_dns::Section;
        let Some(m) = verilith_dns::parse(reply) else { return 0 };
        let mut t = u32::MAX;
        for s in [Section::Answer, Section::Authority] {
            for i in 0..m.record_count(s) {
                if let Some(r) = m.record(s, i) {
                    t = t.min(r.ttl);
                }
            }
        }
        if t == u32::MAX { 0 } else { t }
    }

    /// DNS over HTTPS (RFC 8484) at `/dns-query`, GET and POST, over
    /// verilith-server's HTTP/1.1 and HTTP/2 (and HTTP/3 with `h3`).
    /// `threads`: worker threads; a handler waits while it resolves, so
    /// more workers than CPUs keep cache hits flowing behind slow misses.
    pub fn doh(r: Arc<Resolver>, addr: [u8; 4], http_port: u16, tls_port: u16, cert: &str, key: &str, threads: usize) -> io::Result<()> {
        use verilith_server::{serve, Config, Field, Request, Response};
        let tls = verilith_server::tls::config(cert, key)?;
        let handler = move |req: &Request, res: &mut Response| {
            if req.path() != b"/dns-query" {
                res.error(404);
                return;
            }
            let q = if req.method == b"GET" {
                match dns_param(req.target).and_then(base64url) {
                    Some(q) => q,
                    None => return res.error(400),
                }
            } else if req.method == b"POST" {
                match req.header(b"content-type") {
                    Some(ct) if ct.eq_ignore_ascii_case(b"application/dns-message") => req.body.to_vec(),
                    _ => return res.error(415),
                }
            } else {
                return res.error(405);
            };
            match r.answer(&q, false) {
                Some(rep) => {
                    let cc = format!("max-age={}", min_ttl(&rep));
                    let _ = res.send(
                        200,
                        &[
                            Field { name: b"Content-Type", value: b"application/dns-message" },
                            Field { name: b"Cache-Control", value: cc.as_bytes() },
                        ],
                        &rep,
                    );
                }
                None => res.error(400),
            }
        };
        let cfg = Config { addr, port: http_port, threads, pin: false, tls: Some((tls_port, tls)), ..Config::default() };
        serve(cfg, Arc::new(handler))
    }
}

/// Binds a UDP socket.
pub fn bind_udp(addr: SocketAddr) -> io::Result<UdpSocket> {
    UdpSocket::bind(addr)
}
