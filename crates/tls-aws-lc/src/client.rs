//! A blocking TLS 1.3 client over any `Read + Write` transport (a
//! `TcpStream`): the verified `ClientConn` with aws-lc's cryptography.
//! Framing and I/O only; every decision about the bytes is
//! `ClientConn::read_record`'s.
use crate::AwsLc;
use std::io::{self, Read, Write};
use std::sync::Arc;
use verilith_tls::client_hs::ClientConfig;
use verilith_tls::server::Error;
use verilith_tls::stream::ClientStream;

/// The signature schemes this crate checks, for `ClientConfig::sigs`.
pub const SIGS: [u16; 6] = [
    crate::ECDSA_SECP256R1_SHA256,
    crate::ECDSA_SECP384R1_SHA384,
    crate::ED25519,
    crate::RSA_PSS_RSAE_SHA256,
    crate::RSA_PSS_RSAE_SHA384,
    crate::RSA_PSS_RSAE_SHA512,
];

/// A configuration with every suite, group and signature scheme this crate
/// has, shares for X25519MLKEM768 and X25519, and `roots` (DER) as trust
/// anchors.
pub fn config(roots: Vec<Vec<u8>>, alpn: &[&[u8]]) -> ClientConfig {
    ClientConfig {
        suites: crate::SUITES.to_vec(),
        groups: crate::GROUPS.to_vec(),
        shares: 2,
        sigs: SIGS.to_vec(),
        alpn: alpn.iter().map(|p| p.to_vec()).collect(),
        roots,
    }
}

fn tls_err(e: Error) -> io::Error {
    let msg = match e {
        Error::Sent(a) => format!("TLS: sent alert {a}"),
        Error::Received(a) => format!("TLS: received alert {a}"),
        Error::Closed => "TLS: connection closed".to_string(),
        Error::OutputFull => "TLS: output buffer full".to_string(),
    };
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

/// A TLS client connection over `S`.
pub struct TlsStream<S: Read + Write> {
    io: S,
    tls: ClientStream<AwsLc>,
    eof: bool,
}

impl<S: Read + Write> TlsStream<S> {
    /// Connects to `host` (a DNS name) over `io`, and runs the handshake
    /// to the end.
    pub fn connect(cfg: Arc<ClientConfig>, host: &str, io: S) -> io::Result<Self> {
        let tls = ClientStream::new(cfg, host.as_bytes(), AwsLc::new(None))
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "bad TLS configuration or host name"))?;
        let mut s = TlsStream { io, tls, eof: false };
        while s.tls.is_handshaking() {
            s.flush_tls()?;
            if !s.read_more()? {
                return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "TLS: closed during handshake"));
            }
        }
        s.flush_tls()?;
        Ok(s)
    }

    /// Sends what the connection has to send.
    fn flush_tls(&mut self) -> io::Result<()> {
        let out = self.tls.take_pending();
        if !out.is_empty() {
            self.io.write_all(&out)?;
            self.io.flush()?;
        }
        Ok(())
    }

    /// Reads from the transport and processes it; false at end of stream.
    fn read_more(&mut self) -> io::Result<bool> {
        let mut buf = [0u8; 16 * 1024 + 512];
        let n = self.io.read(&mut buf)?;
        if n == 0 {
            return Ok(false);
        }
        self.tls.read_tls(&buf[..n]);
        let r = self.tls.process();
        // An alert we sent goes out before the error does.
        let _ = self.flush_tls();
        r.map_err(tls_err)?;
        Ok(true)
    }

    /// The ALPN protocol the server chose.
    pub fn alpn(&self) -> Option<&[u8]> {
        self.tls.alpn()
    }

    /// The server's certificates, leaf first, as checked.
    pub fn peer_certificates(&self) -> &[Vec<u8>] {
        self.tls.peer_certificates()
    }

    /// Sends close_notify.
    pub fn close(&mut self) -> io::Result<()> {
        self.tls.close();
        self.flush_tls()
    }

    pub fn get_ref(&self) -> &S {
        &self.io
    }

    pub fn into_inner(self) -> S {
        self.io
    }
}

impl<S: Read + Write> Read for TlsStream<S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        loop {
            let p = self.tls.plaintext();
            if !p.is_empty() {
                let n = p.len().min(buf.len());
                buf[..n].copy_from_slice(&p[..n]);
                self.tls.consume_plaintext(n);
                return Ok(n);
            }
            if self.eof || self.tls.peer_closed() {
                return Ok(0);
            }
            if !self.read_more()? {
                // RFC 8446 §6.1: an end of stream without close_notify may
                // be a truncation.
                self.eof = true;
                return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "TLS: closed without close_notify"));
            }
        }
    }
}

impl<S: Read + Write> Write for TlsStream<S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.tls.write(buf).map_err(tls_err)?;
        self.flush_tls()?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_tls()
    }
}
