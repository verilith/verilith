//! Send buffers for CRYPTO and STREAM data: [`SendBuf`] keeps what was
//! written until it is acknowledged. Which offsets to send, resend and free
//! is decided by verilith-quic's verified `sendq::SendState`; this file
//! only stores the bytes. (Received data is put back in order by the
//! verified `reasm::Reassembly`.)
use bytes::{Buf, Bytes, BytesMut};
use std::collections::VecDeque;
use verilith_quic::sendq::SendState;

/// Writes at least this long are kept as the writer's shared buffer
/// ([`SendBuf::write_bytes`]); shorter ones are copied.
pub const SHARE_MIN: usize = 4096;

/// Data written to a stream (or CRYPTO at one level), kept until
/// acknowledged.
pub struct SendBuf {
    /// Bytes from `st.base()` on: buffers shared with the writer (large
    /// writes, kept without copying), then `tail`.
    chunks: VecDeque<Bytes>,
    /// The bytes in `chunks`.
    chunked: usize,
    /// Small writes, copied, after `chunks`.
    tail: BytesMut,
    /// The offsets: verified.
    st: SendState,
}

impl Default for SendBuf {
    fn default() -> Self {
        SendBuf { chunks: VecDeque::new(), chunked: 0, tail: BytesMut::new(), st: SendState::new() }
    }
}

impl SendBuf {
    /// The offset after the last byte written.
    pub fn end(&self) -> u64 {
        self.st.end()
    }

    /// Bytes written and not yet acknowledged.
    pub fn unacked(&self) -> usize {
        self.chunked + self.tail.len()
    }

    /// Whether the stream ends after the data written.
    pub fn fin(&self) -> bool {
        self.st.fin()
    }

    /// The stream ends after the data written.
    pub fn set_fin(&mut self) {
        self.st.set_fin();
    }

    pub fn write(&mut self, b: &[u8]) {
        if self.st.write(b.len() as u64) {
            self.tail.extend_from_slice(b);
        }
    }

    /// Writes `b`, keeping a large buffer as it is (shared, not copied).
    pub fn write_bytes(&mut self, b: Bytes) {
        if b.len() < SHARE_MIN {
            return self.write(&b);
        }
        if !self.st.write(b.len() as u64) {
            return;
        }
        if !self.tail.is_empty() {
            let t = self.tail.split().freeze();
            self.chunked += t.len();
            self.chunks.push_back(t);
        }
        self.chunked += b.len();
        self.chunks.push_back(b);
    }

    /// Drops the first `k` bytes (acknowledged).
    fn drop_front(&mut self, mut k: usize) {
        while k > 0 {
            let Some(c) = self.chunks.front_mut() else { break };
            let m = k.min(c.len());
            self.chunked -= m;
            k -= m;
            if m == c.len() {
                self.chunks.pop_front();
            } else {
                c.advance(m);
            }
        }
        self.tail.advance(k);
    }

    /// Whether anything (data or the FIN) is waiting to be sent.
    pub fn has_pending(&self) -> bool {
        self.st.has_pending()
    }

    /// Bytes written and never sent.
    pub fn new_pending(&self) -> u64 {
        self.st.new_pending()
    }

    /// The next chunk to send, at most `max` bytes: lost data first, then
    /// new data up to `limit` (flow control's end offset). Returns
    /// `(offset, len, fin)`; the caller reads the bytes with `get` and then
    /// calls `sent`.
    pub fn next(&self, max: usize, limit: u64) -> Option<(u64, usize, bool)> {
        self.st.next(max as u64, limit).map(|(o, n, f)| (o, n as usize, f))
    }

    /// Copies `[off, off + n)` into `out`.
    pub fn get(&self, off: u64, mut n: usize, out: &mut Vec<u8>) {
        let mut i = (off - self.st.base()) as usize;
        for c in &self.chunks {
            if n == 0 {
                return;
            }
            if i >= c.len() {
                i -= c.len();
                continue;
            }
            let m = n.min(c.len() - i);
            out.extend_from_slice(&c[i..i + m]);
            n -= m;
            i = 0;
        }
        out.extend_from_slice(&self.tail[i..i + n]);
    }

    /// `[off, off + n)` (and the FIN if `fin`) went out in a packet.
    pub fn sent(&mut self, off: u64, n: usize, fin: bool) {
        self.st.sent(off, n as u64, fin);
    }

    /// `[off, off + n)` was acknowledged.
    pub fn on_ack(&mut self, off: u64, n: usize, fin: bool) {
        let k = self.st.on_ack(off, n as u64, fin);
        self.drop_front(k as usize);
    }

    /// `[off, off + n)` was lost: resend what of it is not acknowledged.
    pub fn on_lost(&mut self, off: u64, n: usize, fin: bool) {
        self.st.on_lost(off, n as u64, fin);
    }

    /// Everything written, and the FIN, is acknowledged.
    pub fn all_acked(&self) -> bool {
        self.st.all_acked()
    }

    /// Drops everything (a reset stream).
    pub fn clear(&mut self) {
        self.st.clear();
        self.chunks.clear();
        self.chunked = 0;
        self.tail.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn send_buf() {
        let mut s = SendBuf::default();
        s.write(b"0123456789");
        s.set_fin();
        let (o, n, f) = s.next(4, u64::MAX).unwrap();
        assert_eq!((o, n, f), (0, 4, false));
        s.sent(o, n, f);
        let (o, n, f) = s.next(100, u64::MAX).unwrap();
        assert_eq!((o, n, f), (4, 6, true));
        s.sent(o, n, f);
        assert!(!s.has_pending());
        s.on_ack(4, 6, true);
        s.on_lost(0, 4, false);
        assert_eq!(s.next(100, u64::MAX), Some((0, 4, false)));
        let mut b = Vec::new();
        s.get(0, 4, &mut b);
        assert_eq!(b, b"0123");
        s.sent(0, 4, false);
        s.on_ack(0, 4, false);
        assert!(s.all_acked());
    }

    /// Shared chunks and copied writes interleaved: every range reads back
    /// the bytes written, across chunk boundaries, as acknowledgments drop
    /// the front.
    #[test]
    fn send_buf_chunks() {
        let mut s = SendBuf::default();
        let mut all = Vec::new();
        for (i, len) in [3usize, 5000, 7, 9000, 4096, 1, 12000].into_iter().enumerate() {
            let b: Vec<u8> = (0..len).map(|j| (j * 7 + i * 13) as u8).collect();
            all.extend_from_slice(&b);
            if i % 2 == 1 {
                s.write_bytes(Bytes::from(b));
            } else {
                s.write(&b);
            }
        }
        assert_eq!(s.end(), all.len() as u64);
        let mut acked = 0u64;
        for step in [1u64, 4999, 3, 2, 9001, 100, 4000] {
            for (off, n) in [(acked, 1usize), (acked, 5003), (acked + 2, 9000), (acked, (all.len() as u64 - acked) as usize)] {
                let n = n.min((all.len() as u64 - off) as usize);
                let mut out = Vec::new();
                s.get(off, n, &mut out);
                assert_eq!(out, &all[off as usize..off as usize + n], "off {off} n {n}");
            }
            s.sent(acked, step as usize, false);
            s.on_ack(acked, step as usize, false);
            acked += step;
            assert_eq!(s.unacked() as u64, all.len() as u64 - acked);
        }
    }
}
