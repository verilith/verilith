//! TLS (DESIGN.md, "TLS"), sans I/O: ciphertext in from the socket,
//! plaintext through the HTTP/1.1 or HTTP/2 engine (chosen by ALPN),
//! ciphertext out.
//!
//! The record layer and handshake are verilith-tls's (TLS 1.3, verified),
//! with aws-lc's cryptography through verilith-tls-aws-lc (trusted). With
//! `--features tls-rustls`, rustls is a second backend behind the same
//! shape, kept to compare against.
use std::sync::Arc;

use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::{AwsLc, SigningKey, TicketKeys, GROUPS, SUITES};

use crate::h1::{Conn, Ctx, Limits, Next};
use crate::h2::{Conn2, Limits2};
use crate::Handler;

/// ALPN, in the server's order of preference.
const ALPN: &[u8] = b"\x02h2\x08http/1.1";

/// A server's TLS configuration: certificate chain and key.
pub enum Config {
    /// `tickets`: the session-ticket keys every worker shares, so a
    /// ticket from one resumes on any.
    Verilith { cfg: Arc<verilith_tls::server::Config>, key: Arc<SigningKey>, tickets: Arc<TicketKeys> },
    #[cfg(feature = "tls-rustls")]
    Rustls(Arc<rustls::ServerConfig>),
}

impl std::fmt::Debug for Config {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Config::Verilith { .. } => "Config::Verilith",
            #[cfg(feature = "tls-rustls")]
            Config::Rustls(_) => "Config::Rustls",
        })
    }
}

fn bad(m: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, m.to_string())
}

/// The DER bodies of the PEM blocks labelled `label` in `pem`.
pub fn pem_blocks(pem: &[u8], label: &str) -> Vec<Vec<u8>> {
    let text = String::from_utf8_lossy(pem);
    let (begin, end) = (format!("-----BEGIN {label}-----"), format!("-----END {label}-----"));
    let mut out = Vec::new();
    let mut rest = &text[..];
    while let Some(i) = rest.find(&begin) {
        let after = &rest[i + begin.len()..];
        let Some(j) = after.find(&end) else { break };
        if let Some(der) = base64(&after[..j]) {
            out.push(der);
        }
        rest = &after[j + end.len()..];
    }
    out
}

fn base64(s: &str) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(s.len() * 3 / 4);
    let (mut acc, mut bits) = (0u32, 0u32);
    for c in s.bytes() {
        let v = match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            b'=' | b' ' | b'\t' | b'\r' | b'\n' => continue,
            _ => return None,
        };
        acc = acc << 6 | v as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    Some(out)
}

/// A configuration from a certificate chain (DER, leaf first) and a
/// PKCS#8 key (DER): ECDSA P-256/P-384, Ed25519 or RSA.
pub fn config_der(chain: Vec<Vec<u8>>, key_pkcs8: &[u8]) -> std::io::Result<Arc<Config>> {
    config_der_early(chain, key_pkcs8, 0)
}

/// [`config_der`], taking up to `max_early` bytes of 0-RTT data on a
/// resumption (0 for none). Requests in early data reach the handler
/// with [`crate::Request::early`] set, and any method but GET, HEAD and
/// OPTIONS is answered 425 (Too Early) without it. Replays are refused
/// by a single-use register in this process (verilith-tls-aws-lc):
/// servers on several machines that share ticket keys must not enable it.
pub fn config_der_early(chain: Vec<Vec<u8>>, key_pkcs8: &[u8], max_early: u32) -> std::io::Result<Arc<Config>> {
    let key = SigningKey::from_pkcs8(key_pkcs8).ok_or_else(|| bad("the key is not PKCS#8 ECDSA, Ed25519 or RSA"))?;
    let mut cfg = verilith_tls::server::Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), ALPN.to_vec(), &chain)
        .ok_or_else(|| bad("the certificate chain is empty or too long"))?;
    // Two tickets per connection, valid as long as the ticket keys rotate
    // (6 h).
    const TICKET_LIFETIME: u32 = 6 * 3600;
    cfg.set_tickets(2, TICKET_LIFETIME);
    cfg.set_early_data(max_early);
    let tickets = Arc::new(TicketKeys::new(TICKET_LIFETIME as u64));
    Ok(Arc::new(Config::Verilith { cfg: Arc::new(cfg), key: Arc::new(key), tickets }))
}

/// A configuration for `cert`/`key` (PEM files; the key "PRIVATE KEY",
/// that is PKCS#8).
pub fn config(cert: &str, key: &str) -> std::io::Result<Arc<Config>> {
    config_early(cert, key, 0)
}

/// [`config`], with 0-RTT data as [`config_der_early`] takes it.
pub fn config_early(cert: &str, key: &str, max_early: u32) -> std::io::Result<Arc<Config>> {
    let chain = pem_blocks(&std::fs::read(cert)?, "CERTIFICATE");
    let keys = pem_blocks(&std::fs::read(key)?, "PRIVATE KEY");
    let key = keys.first().ok_or_else(|| bad("no PKCS#8 \"PRIVATE KEY\" block in the key file"))?;
    config_der_early(chain, key, max_early)
}

/// The same with rustls, with ALPN offering h2 and http/1.1.
#[cfg(feature = "tls-rustls")]
pub fn rustls_config(cert: &str, key: &str) -> std::io::Result<Arc<Config>> {
    use rustls::pki_types::pem::PemObject;
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};
    let e = |e: rustls::pki_types::pem::Error| std::io::Error::other(e.to_string());
    let certs = CertificateDer::pem_file_iter(cert).map_err(e)?.collect::<Result<Vec<_>, _>>().map_err(e)?;
    let key = PrivateKeyDer::from_pem_file(key).map_err(e)?;
    let mut c = rustls::ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .map_err(|e| std::io::Error::other(e.to_string()))?
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    c.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
    // Like verilith-tls: two tickets, resumed on any worker (rustls's
    // default ticketer is process-wide).
    c.send_tls13_tickets = 2;
    c.ticketer = rustls::crypto::aws_lc_rs::Ticketer::new().map_err(|e| std::io::Error::other(e.to_string()))?;
    Ok(Arc::new(Config::Rustls(Arc::new(c))))
}

/// Plaintext decrypted and not yet taken by the engine, past which no
/// more ciphertext is decrypted.
const PLAIN_HIGH: usize = 256 * 1024;

/// One TLS session, of either backend.
enum Session {
    V(Box<ServerStream<AwsLc>>),
    #[cfg(feature = "tls-rustls")]
    R(Box<rustls::ServerConnection>),
}

impl Session {
    /// Takes ciphertext: the bytes taken, or Err on a TLS error (an alert
    /// is queued).
    fn feed(&mut self, data: &[u8]) -> Result<usize, ()> {
        match self {
            Session::V(s) => {
                if s.plaintext().len() >= PLAIN_HIGH || s.peer_closed() {
                    return Ok(0);
                }
                s.read_tls(data);
                s.process().map_err(|_| ())?;
                Ok(data.len())
            }
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => {
                let mut r = data;
                // Err: rustls's plaintext buffer is full.
                let n = s.read_tls(&mut r).unwrap_or(0);
                if n > 0 {
                    s.process_new_packets().map_err(|_| ())?;
                }
                Ok(n)
            }
        }
    }

    /// Plaintext into `buf`: (bytes, whether the peer closed and all its
    /// plaintext has been read).
    fn read(&mut self, buf: &mut [u8]) -> (usize, bool) {
        match self {
            Session::V(s) => {
                let p = s.plaintext();
                let n = p.len().min(buf.len());
                buf[..n].copy_from_slice(&p[..n]);
                s.consume_plaintext(n);
                (n, s.plaintext().is_empty() && s.peer_closed())
            }
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => {
                use std::io::Read;
                match s.reader().read(buf) {
                    Ok(0) => (0, true),
                    Ok(k) => (k, false),
                    Err(_) => (0, false),
                }
            }
        }
    }

    /// Protects `data`: the bytes taken.
    fn write(&mut self, data: &[u8]) -> Result<usize, ()> {
        match self {
            Session::V(s) => s.write(data).map(|_| data.len()).map_err(|_| ()),
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => {
                use std::io::Write;
                Ok(s.writer().write(data).unwrap_or(0))
            }
        }
    }

    /// Ciphertext out, onto `out` (from `pos`, the part already sent).
    fn put(&mut self, out: &mut Vec<u8>, pos: &mut usize) {
        match self {
            Session::V(s) => {
                if s.pending().is_empty() {
                    return;
                }
                if *pos == out.len() {
                    out.clear();
                    *pos = 0;
                    s.swap_pending(out);
                } else {
                    out.extend_from_slice(s.pending());
                    let n = s.pending().len();
                    s.consume_pending(n);
                }
            }
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => {
                while s.wants_write() && out.len() - *pos < COUT_HIGH {
                    if s.write_tls(out).is_err() {
                        break;
                    }
                }
            }
        }
    }

    fn handshaking(&self) -> bool {
        match self {
            Session::V(s) => s.is_handshaking(),
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => s.is_handshaking(),
        }
    }

    /// 0-RTT data was taken and the handshake is not yet confirmed.
    fn early(&self) -> bool {
        match self {
            Session::V(s) => s.in_early_data(),
            #[cfg(feature = "tls-rustls")]
            Session::R(_) => false,
        }
    }

    fn h2(&self) -> bool {
        match self {
            Session::V(s) => s.alpn() == Some(b"h2"),
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => s.alpn_protocol() == Some(b"h2"),
        }
    }

    fn close(&mut self) {
        match self {
            Session::V(s) => s.close(),
            #[cfg(feature = "tls-rustls")]
            Session::R(s) => s.send_close_notify(),
        }
    }
}

/// Writes the gathered plaintext: false if the session took less.
fn flush(tls: &mut Session, gather: &mut Vec<u8>) -> Result<bool, ()> {
    if gather.is_empty() {
        return Ok(true);
    }
    let n = tls.write(gather)?;
    let all = n == gather.len();
    gather.drain(..n);
    Ok(all)
}

enum Inner {
    H1(Conn),
    H2(Box<Conn2>),
}

macro_rules! inner {
    ($c:expr, $x:ident => $e:expr) => {
        match $c {
            Inner::H1($x) => $e,
            Inner::H2($x) => $e,
        }
    };
}

/// Ciphertext kept before the session takes it, and written before the
/// socket takes it, at most.
const CIN: usize = 32 * 1024;
const COUT_HIGH: usize = 1 << 20;
/// Plaintext gathered into one write (one or a few records).
const GATHER: usize = 16 * 1024;

pub struct TlsConn {
    tls: Session,
    inner: Option<Inner>,
    limits: Limits,
    limits2: Limits2,
    cin: Vec<u8>,
    cin_start: usize,
    cin_end: usize,
    cout: Vec<u8>,
    cout_pos: usize,
    /// Small plaintext pieces gathered into one record.
    gather: Vec<u8>,
    closing: bool,
    eof: bool,
    /// Ciphertext is waiting that the session will not take until
    /// plaintext is read out of it.
    blocked: bool,
}

impl TlsConn {
    pub fn new(cfg: Arc<Config>, limits: Limits, limits2: Limits2) -> Option<TlsConn> {
        let tls = match &*cfg {
            Config::Verilith { cfg, key, tickets } => {
                Session::V(Box::new(ServerStream::new(cfg.clone(), AwsLc::shared(key.clone()).with_tickets(tickets.clone()))))
            }
            #[cfg(feature = "tls-rustls")]
            Config::Rustls(c) => Session::R(Box::new(rustls::ServerConnection::new(c.clone()).ok()?)),
        };
        Some(TlsConn {
            tls,
            inner: None,
            limits,
            limits2,
            cin: vec![0; CIN],
            cin_start: 0,
            cin_end: 0,
            cout: Vec::new(),
            cout_pos: 0,
            gather: Vec::new(),
            closing: false,
            eof: false,
            blocked: false,
        })
    }

    pub fn read_buf(&mut self) -> &mut [u8] {
        if self.closing || self.blocked {
            return &mut [];
        }
        if self.cin_start > 0 {
            self.cin.copy_within(self.cin_start..self.cin_end, 0);
            self.cin_end -= self.cin_start;
            self.cin_start = 0;
        }
        &mut self.cin[self.cin_end..]
    }

    pub fn filled(&mut self, n: usize) {
        self.cin_end += n;
    }

    pub fn eof(&mut self) {
        self.eof = true;
        if let Some(i) = self.inner.as_mut() {
            inner!(i, c => c.eof());
        }
    }

    pub fn closing(&self) -> bool {
        self.closing
    }

    /// The handshake is not finished.
    pub fn handshaking(&self) -> bool {
        self.inner.is_none() && !self.closing
    }

    pub fn pending<'a>(&'a self, out: &mut [&'a [u8]]) -> usize {
        if self.cout_pos == self.cout.len() || out.is_empty() {
            return 0;
        }
        out[0] = &self.cout[self.cout_pos..];
        1
    }

    pub fn pending_len(&self) -> usize {
        self.cout.len() - self.cout_pos
    }

    pub fn wrote(&mut self, n: usize) {
        self.cout_pos += n;
        if self.cout_pos == self.cout.len() {
            self.cout.clear();
            self.cout_pos = 0;
        }
    }

    /// Takes in ciphertext; false on a TLS error (an alert is queued).
    fn take_ciphertext(&mut self) -> (bool, bool) {
        let mut moved = false;
        self.blocked = false;
        while self.cin_start < self.cin_end {
            match self.tls.feed(&self.cin[self.cin_start..self.cin_end]) {
                Err(()) => return (false, moved),
                Ok(0) => {
                    self.blocked = true;
                    break;
                }
                Ok(k) => {
                    self.cin_start += k;
                    moved = true;
                }
            }
        }
        if self.cin_start == self.cin_end {
            self.cin_start = 0;
            self.cin_end = 0;
        }
        (true, moved)
    }

    fn put_ciphertext(&mut self) {
        self.tls.put(&mut self.cout, &mut self.cout_pos);
    }


    /// Plaintext out of the engine, as far as the session and `cout`
    /// take it: whether any moved, or Err on a TLS error.
    fn plaintext_out(&mut self) -> Result<bool, ()> {
        let Some(i) = self.inner.as_mut() else { return Ok(false) };
        let mut progress = false;
        // Bytes left in `gather` from a short write go first.
        if !flush(&mut self.tls, &mut self.gather)? {
            return Ok(false);
        }
        while self.cout.len() - self.cout_pos < COUT_HIGH {
            let mut v: [&[u8]; 8] = [&[]; 8];
            let k = inner!(i, c => c.pending(&mut v));
            if k == 0 {
                break;
            }
            // Each piece is gathered (small) or written as it is (big);
            // `taken` counts the bytes the session has, or `gather` holds.
            let mut taken = 0;
            let mut short = false;
            for s in &v[..k] {
                if self.gather.len() + s.len() <= GATHER {
                    self.gather.extend_from_slice(s);
                    taken += s.len();
                    continue;
                }
                let n = self.gather.len();
                let w = self.tls.write(&self.gather)?;
                self.gather.drain(..w);
                if w < n {
                    short = true;
                    break;
                }
                if s.len() >= GATHER {
                    let w = self.tls.write(s)?;
                    taken += w;
                    if w < s.len() {
                        short = true;
                        break;
                    }
                } else {
                    self.gather.extend_from_slice(s);
                    taken += s.len();
                }
            }
            if !short && !flush(&mut self.tls, &mut self.gather)? {
                short = true;
            }
            if taken > 0 {
                inner!(i, c => c.wrote(taken));
                progress = true;
            }
            self.tls.put(&mut self.cout, &mut self.cout_pos);
            if short || taken == 0 {
                break;
            }
        }
        Ok(progress)
    }

    pub fn process<H: Handler + ?Sized>(&mut self, h: &H, ctx: &Ctx) -> Next {
        // Each pass moves bytes one stage on; stop once none moved.
        for _ in 0..64 {
            let (ok, mut progress) = self.take_ciphertext();
            if !ok {
                self.put_ciphertext();
                self.closing = true;
                return Next::Close;
            }
            // With 0-RTT data, HTTP starts before the handshake is done.
            let early = self.tls.early();
            if self.inner.is_none() && (!self.tls.handshaking() || early) {
                self.inner = Some(if self.tls.h2() { Inner::H2(Box::new(Conn2::new(self.limits2))) } else { Inner::H1(Conn::new(self.limits)) });
                if self.eof {
                    inner!(self.inner.as_mut().unwrap(), c => c.eof());
                }
            }
            if let Some(i) = self.inner.as_mut() {
                match i {
                    Inner::H1(c) => c.early = early,
                    Inner::H2(c) => c.early = early,
                }
                // Plaintext in.
                let mut peer_closed = false;
                loop {
                    let b = inner!(i, c => c.read_buf());
                    if b.is_empty() {
                        break;
                    }
                    let (k, closed) = self.tls.read(b);
                    if k > 0 {
                        inner!(i, c => c.filled(k));
                        progress = true;
                    }
                    if closed {
                        peer_closed = true;
                    }
                    if k == 0 {
                        break;
                    }
                }
                let _ = inner!(i, c => c.process(h, ctx));
                if peer_closed {
                    inner!(i, c => c.eof());
                }
                match self.plaintext_out() {
                    Ok(p) => progress |= p,
                    Err(()) => {
                        self.put_ciphertext();
                        self.closing = true;
                        return Next::Close;
                    }
                }
                let i = self.inner.as_mut().unwrap();
                let done = inner!(i, c => c.closing() && c.pending_len() == 0) && self.gather.is_empty();
                if done && !self.closing {
                    self.tls.close();
                    self.closing = true;
                }
            } else if self.eof {
                self.closing = true;
            }
            let before = self.pending_len();
            self.put_ciphertext();
            if self.pending_len() != before {
                progress = true;
            }
            if !progress {
                break;
            }
        }
        if self.closing {
            Next::Close
        } else if self.pending_len() > 0 && (self.blocked || self.pending_len() >= COUT_HIGH) {
            Next::Write
        } else {
            Next::Read
        }
    }
}
