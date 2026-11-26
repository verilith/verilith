//! TLS (DESIGN.md, "TLS"), sans I/O: ciphertext in from the socket,
//! plaintext through the HTTP/1.1 or HTTP/2 engine (chosen by ALPN),
//! ciphertext out. The record layer and handshake are rustls's (trusted,
//! with aws-lc-rs's cryptography); Verilith's own TLS crate is meant to
//! replace it behind this same shape: feed ciphertext, take plaintext,
//! give plaintext, take ciphertext.
use std::io::{Read, Write};
use std::sync::Arc;

use crate::h1::{Conn, Ctx, Limits, Next};
use crate::h2::{Conn2, Limits2};
use crate::Handler;

/// A rustls server configuration for `cert`/`key` (PEM files), with ALPN
/// offering h2 and http/1.1.
pub fn config(cert: &str, key: &str) -> std::io::Result<Arc<rustls::ServerConfig>> {
    use rustls::pki_types::pem::PemObject;
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};
    let bad = |e: rustls::pki_types::pem::Error| std::io::Error::other(e.to_string());
    let certs = CertificateDer::pem_file_iter(cert).map_err(bad)?.collect::<Result<Vec<_>, _>>().map_err(bad)?;
    let key = PrivateKeyDer::from_pem_file(key).map_err(bad)?;
    let mut c = rustls::ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_safe_default_protocol_versions()
        .map_err(|e| std::io::Error::other(e.to_string()))?
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .map_err(|e| std::io::Error::other(e.to_string()))?;
    c.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
    // No session tickets or stateful resumption across workers: each
    // worker would need the same keys; full handshakes for now.
    Ok(Arc::new(c))
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

/// Ciphertext kept before rustls takes it, and written before the socket
/// takes it, at most.
const CIN: usize = 32 * 1024;
const COUT_HIGH: usize = 1 << 20;

pub struct TlsConn {
    tls: rustls::ServerConnection,
    inner: Option<Inner>,
    limits: Limits,
    limits2: Limits2,
    cin: Vec<u8>,
    cin_start: usize,
    cin_end: usize,
    cout: Vec<u8>,
    cout_pos: usize,
    closing: bool,
    eof: bool,
    /// Ciphertext is waiting that rustls will not take until plaintext is
    /// read out of it.
    blocked: bool,
}

impl TlsConn {
    pub fn new(cfg: Arc<rustls::ServerConfig>, limits: Limits, limits2: Limits2) -> Option<TlsConn> {
        let tls = rustls::ServerConnection::new(cfg).ok()?;
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
            let mut r = &self.cin[self.cin_start..self.cin_end];
            match self.tls.read_tls(&mut r) {
                Ok(0) => break,
                Ok(k) => {
                    self.cin_start += k;
                    moved = true;
                }
                Err(_) => {
                    // rustls's plaintext buffer is full: read it out first.
                    self.blocked = true;
                    break;
                }
            }
            if self.tls.process_new_packets().is_err() {
                return (false, moved);
            }
        }
        if self.cin_start == self.cin_end {
            self.cin_start = 0;
            self.cin_end = 0;
        }
        (true, moved)
    }

    fn put_ciphertext(&mut self) {
        while self.tls.wants_write() && self.pending_len() < COUT_HIGH {
            if self.tls.write_tls(&mut self.cout).is_err() {
                break;
            }
        }
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
            if self.inner.is_none() && !self.tls.is_handshaking() {
                self.inner = Some(match self.tls.alpn_protocol() {
                    Some(b"h2") => Inner::H2(Box::new(Conn2::new(self.limits2))),
                    _ => Inner::H1(Conn::new(self.limits)),
                });
                if self.eof {
                    inner!(self.inner.as_mut().unwrap(), c => c.eof());
                }
            }
            if let Some(i) = self.inner.as_mut() {
                // Plaintext in.
                let mut peer_closed = false;
                loop {
                    let b = inner!(i, c => c.read_buf());
                    if b.is_empty() {
                        break;
                    }
                    match self.tls.reader().read(b) {
                        Ok(0) => {
                            peer_closed = true;
                            break;
                        }
                        Ok(k) => {
                            inner!(i, c => c.filled(k));
                            progress = true;
                        }
                        Err(_) => break,
                    }
                }
                let _ = inner!(i, c => c.process(h, ctx));
                if peer_closed {
                    inner!(i, c => c.eof());
                }
                // Plaintext out, as far as rustls will buffer it.
                loop {
                    let mut v: [&[u8]; 8] = [&[]; 8];
                    let k = inner!(i, c => c.pending(&mut v));
                    if k == 0 {
                        break;
                    }
                    let mut n = 0;
                    let mut full = false;
                    for s in &v[..k] {
                        let w = self.tls.writer().write(s).unwrap_or(0);
                        n += w;
                        if w < s.len() {
                            full = true;
                            break;
                        }
                    }
                    if n > 0 {
                        inner!(i, c => c.wrote(n));
                        progress = true;
                    }
                    if full || n == 0 {
                        break;
                    }
                }
                let done = inner!(i, c => c.closing() && c.pending_len() == 0);
                if done && !self.closing {
                    self.tls.send_close_notify();
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
