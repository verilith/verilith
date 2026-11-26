//! A byte-stream face for `ServerConn`, for callers that read and write
//! sockets: feed it ciphertext as it arrives, take plaintext and the
//! bytes to send. This is framing and buffering only, not verified; every
//! decision about the bytes is `ServerConn::read_record`'s.
use crate::crypto::Provider;
use crate::server::{Config, Error, Event, ServerConn};
use alloc::sync::Arc;
use alloc::vec::Vec;

/// A server connection over a byte stream.
pub struct ServerStream<P: Provider> {
    conn: ServerConn<P>,
    /// Ciphertext received, from `start`.
    inbuf: Vec<u8>,
    start: usize,
    /// Bytes to send.
    out: Vec<u8>,
    /// Plaintext received and not yet consumed.
    plain: Vec<u8>,
    plain_start: usize,
    handshake_done: bool,
    peer_closed: bool,
}

impl<P: Provider> ServerStream<P> {
    pub fn new(cfg: Arc<Config>, prov: P) -> Self {
        ServerStream {
            conn: ServerConn::new(cfg, prov),
            inbuf: Vec::new(),
            start: 0,
            out: Vec::new(),
            plain: Vec::new(),
            plain_start: 0,
            handshake_done: false,
            peer_closed: false,
        }
    }

    /// Ciphertext from the peer.
    pub fn read_tls(&mut self, data: &[u8]) {
        if self.start > 0 && self.start == self.inbuf.len() {
            self.inbuf.clear();
            self.start = 0;
        }
        self.inbuf.extend_from_slice(data);
    }

    /// Processes every whole record received so far. Plaintext goes to
    /// `plaintext`, answers to `pending`.
    pub fn process(&mut self) -> Result<(), Error> {
        loop {
            let avail = self.inbuf.len() - self.start;
            if avail < 5 {
                break;
            }
            let s = self.start;
            let hdr: [u8; 5] = self.inbuf[s..s + 5].try_into().unwrap();
            let len = (hdr[3] as usize) << 8 | hdr[4] as usize;
            if avail < 5 + len {
                break;
            }
            let body = &mut self.inbuf[s + 5..s + 5 + len];
            let ev = self.conn.read_record(&hdr, body, &mut self.out);
            self.start = s + 5 + len;
            match ev? {
                Event::Nothing => {}
                Event::HandshakeDone => self.handshake_done = true,
                Event::Data(n) | Event::EarlyData(n) => {
                    if self.plain_start == self.plain.len() {
                        self.plain.clear();
                        self.plain_start = 0;
                    }
                    self.plain.extend_from_slice(&self.inbuf[s + 5..s + 5 + n]);
                }
                Event::Closed => {
                    self.peer_closed = true;
                    break;
                }
            }
        }
        // Keep the buffer from growing without bound.
        if self.start > 0 && self.start >= self.inbuf.len() / 2 {
            self.inbuf.drain(..self.start);
            self.start = 0;
        }
        Ok(())
    }

    /// Plaintext received.
    pub fn plaintext(&self) -> &[u8] {
        &self.plain[self.plain_start..]
    }

    pub fn consume_plaintext(&mut self, n: usize) {
        self.plain_start = (self.plain_start + n).min(self.plain.len());
    }

    /// Protects `data` for sending.
    pub fn write(&mut self, data: &[u8]) -> Result<(), Error> {
        self.conn.write(data, &mut self.out)
    }

    /// Bytes to send.
    pub fn pending(&self) -> &[u8] {
        &self.out
    }

    /// Marks the first `n` bytes of `pending` as sent.
    pub fn consume_pending(&mut self, n: usize) {
        self.out.drain(..n.min(self.out.len()));
    }

    /// Takes everything to send.
    pub fn take_pending(&mut self) -> Vec<u8> {
        core::mem::take(&mut self.out)
    }

    /// Swaps the bytes to send with `v`, which should be empty: the
    /// caller takes them without a copy and lends its buffer back.
    pub fn swap_pending(&mut self, v: &mut Vec<u8>) {
        core::mem::swap(&mut self.out, v)
    }

    /// 0-RTT data was taken and the handshake is not yet confirmed: the
    /// plaintext so far may be a replay (RFC 8446 §8), and whoever acts on
    /// it should do only what is safe to repeat (RFC 8470).
    pub fn in_early_data(&self) -> bool {
        self.conn.early_accepted() && !self.handshake_done
    }

    pub fn is_handshaking(&self) -> bool {
        !self.handshake_done
    }

    pub fn peer_closed(&self) -> bool {
        self.peer_closed
    }

    pub fn alpn(&self) -> Option<&[u8]> {
        self.conn.alpn()
    }

    pub fn close(&mut self) {
        self.conn.close(&mut self.out)
    }

    pub fn conn(&self) -> &ServerConn<P> {
        &self.conn
    }
}
