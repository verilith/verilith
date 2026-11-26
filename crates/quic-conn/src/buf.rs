//! Byte-stream buffers for CRYPTO and STREAM data: [`Assembler`] puts
//! received frames back in order, [`SendBuf`] keeps what was written until
//! it is acknowledged and knows what to send or resend next.
use std::collections::{BTreeMap, VecDeque};

/// Disjoint half-open ranges `[start, end)`, keyed by start.
#[derive(Default, Debug, Clone)]
pub struct Ranges {
    m: BTreeMap<u64, u64>,
}

impl Ranges {
    pub fn is_empty(&self) -> bool {
        self.m.is_empty()
    }

    /// Adds `[a, b)`, merging with any range it touches.
    pub fn insert(&mut self, mut a: u64, mut b: u64) {
        if a >= b {
            return;
        }
        // A range starting at or before `a` that reaches it.
        if let Some((&s, &e)) = self.m.range(..=a).next_back() {
            if e >= a {
                if e >= b {
                    return;
                }
                a = s;
                self.m.remove(&s);
            }
        }
        // Ranges starting inside [a, b].
        while let Some((&s, &e)) = self.m.range(a..=b).next() {
            self.m.remove(&s);
            if e > b {
                b = e;
            }
        }
        self.m.insert(a, b);
    }

    /// Removes `[a, b)`.
    pub fn remove(&mut self, a: u64, b: u64) {
        if a >= b {
            return;
        }
        if let Some((&s, &e)) = self.m.range(..a).next_back() {
            if e > a {
                self.m.insert(s, a);
                if e > b {
                    self.m.insert(b, e);
                    return;
                }
            }
        }
        while let Some((&s, &e)) = self.m.range(a..b).next() {
            self.m.remove(&s);
            if e > b {
                self.m.insert(b, e);
                break;
            }
        }
    }

    /// The first range.
    pub fn first(&self) -> Option<(u64, u64)> {
        self.m.iter().next().map(|(&a, &b)| (a, b))
    }

    /// Whether `[a, b)` is covered.
    pub fn contains(&self, a: u64, b: u64) -> bool {
        match self.m.range(..=a).next_back() {
            Some((_, &e)) => e >= b,
            None => false,
        }
    }

    pub fn clear(&mut self) {
        self.m.clear();
    }
}

/// Received data put back in order.
#[derive(Default)]
pub struct Assembler {
    /// Bytes from `read` on, contiguous, not yet read.
    ready: VecDeque<u8>,
    /// The offset of `ready[0]`.
    read: u64,
    /// Out-of-order segments past the contiguous data, by offset.
    pending: BTreeMap<u64, Vec<u8>>,
    /// Bytes buffered in `pending`.
    pending_len: usize,
}

impl Assembler {
    /// The offset up to which data is contiguous.
    pub fn contiguous(&self) -> u64 {
        self.read + self.ready.len() as u64
    }

    /// The offset of the next byte to read.
    pub fn read_offset(&self) -> u64 {
        self.read
    }

    /// Buffers `data` at `offset`; bytes already held are dropped.
    pub fn insert(&mut self, offset: u64, data: &[u8]) {
        let end = offset + data.len() as u64;
        let have = self.contiguous();
        if end <= have {
            return;
        }
        if offset <= have {
            let skip = (have - offset) as usize;
            self.ready.extend(&data[skip..]);
            self.drain_pending();
        } else {
            match self.pending.get(&offset) {
                Some(v) if v.len() >= data.len() => {}
                _ => {
                    if let Some(old) = self.pending.insert(offset, data.to_vec()) {
                        self.pending_len -= old.len();
                    }
                    self.pending_len += data.len();
                }
            }
        }
    }

    fn drain_pending(&mut self) {
        while let Some((&off, _)) = self.pending.iter().next() {
            let have = self.contiguous();
            if off > have {
                break;
            }
            let v = self.pending.remove(&off).unwrap();
            self.pending_len -= v.len();
            let end = off + v.len() as u64;
            if end > have {
                self.ready.extend(&v[(have - off) as usize..]);
            }
        }
    }

    /// The contiguous unread bytes, in up to two slices.
    pub fn peek(&self) -> (&[u8], &[u8]) {
        self.ready.as_slices()
    }

    /// Bytes available to read.
    pub fn available(&self) -> usize {
        self.ready.len()
    }

    /// Consumes `n` bytes.
    pub fn consume(&mut self, n: usize) {
        self.ready.drain(..n);
        self.read += n as u64;
    }

    /// Reads up to `out.len()` bytes.
    pub fn read_into(&mut self, out: &mut Vec<u8>, max: usize) -> usize {
        let n = max.min(self.ready.len());
        let (a, b) = self.ready.as_slices();
        if n <= a.len() {
            out.extend_from_slice(&a[..n]);
        } else {
            out.extend_from_slice(a);
            out.extend_from_slice(&b[..n - a.len()]);
        }
        self.consume(n);
        n
    }

    /// Bytes buffered out of order.
    pub fn buffered(&self) -> usize {
        self.pending_len + self.ready.len()
    }
}

/// Data written to a stream (or CRYPTO at one level), kept until
/// acknowledged.
#[derive(Default)]
pub struct SendBuf {
    /// Bytes from `base` on.
    data: VecDeque<u8>,
    /// The offset of `data[0]`: everything before is acknowledged.
    base: u64,
    /// The offset of the next byte never sent.
    unsent: u64,
    /// Acknowledged ranges past `base`.
    acked: Ranges,
    /// Ranges sent, declared lost, and not yet resent.
    lost: Ranges,
    /// The stream ends after the data written.
    pub fin: bool,
    /// The FIN has been sent (and not declared lost since).
    pub fin_sent: bool,
    /// The FIN has been acknowledged.
    pub fin_acked: bool,
}

impl SendBuf {
    /// The offset after the last byte written.
    pub fn end(&self) -> u64 {
        self.base + self.data.len() as u64
    }

    /// Bytes written and not yet acknowledged.
    pub fn unacked(&self) -> usize {
        self.data.len()
    }

    pub fn write(&mut self, b: &[u8]) {
        self.data.extend(b);
    }

    /// Whether anything (data or the FIN) is waiting to be sent.
    pub fn has_pending(&self) -> bool {
        !self.lost.is_empty() || self.unsent < self.end() || (self.fin && !self.fin_sent)
    }

    /// Whether only new data (not retransmissions) is pending.
    pub fn new_pending(&self) -> u64 {
        self.end() - self.unsent
    }

    /// The next chunk to send, at most `max` bytes: lost data first, then
    /// new data up to `limit` (flow control's end offset). Returns
    /// `(offset, len, fin)`; the caller reads the bytes with `get` and then
    /// calls `sent`.
    pub fn next(&self, max: usize, limit: u64) -> Option<(u64, usize, bool)> {
        if let Some((a, b)) = self.lost.first() {
            let n = ((b - a) as usize).min(max);
            let fin = self.fin && a + n as u64 == self.end() && !self.fin_sent;
            return Some((a, n, fin));
        }
        let lim = limit.min(self.end());
        if self.unsent < lim && max > 0 {
            let n = ((lim - self.unsent) as usize).min(max);
            let fin = self.fin && self.unsent + n as u64 == self.end();
            return Some((self.unsent, n, fin));
        }
        if self.fin && !self.fin_sent && self.unsent == self.end() {
            return Some((self.end(), 0, true));
        }
        None
    }

    /// Copies `[off, off + n)` into `out`.
    pub fn get(&self, off: u64, n: usize, out: &mut Vec<u8>) {
        let i = (off - self.base) as usize;
        let (a, b) = self.data.as_slices();
        if i + n <= a.len() {
            out.extend_from_slice(&a[i..i + n]);
        } else if i >= a.len() {
            out.extend_from_slice(&b[i - a.len()..i - a.len() + n]);
        } else {
            out.extend_from_slice(&a[i..]);
            out.extend_from_slice(&b[..n - (a.len() - i)]);
        }
    }

    /// `[off, off + n)` (and the FIN if `fin`) went out in a packet.
    pub fn sent(&mut self, off: u64, n: usize, fin: bool) {
        let end = off + n as u64;
        self.lost.remove(off, end);
        if end > self.unsent {
            self.unsent = end;
        }
        if fin {
            self.fin_sent = true;
        }
    }

    /// `[off, off + n)` was acknowledged.
    pub fn on_ack(&mut self, off: u64, n: usize, fin: bool) {
        let end = off + n as u64;
        if fin {
            self.fin_acked = true;
        }
        if end <= self.base {
            return;
        }
        let a = off.max(self.base);
        self.acked.insert(a, end);
        self.lost.remove(a, end);
        if let Some((s, e)) = self.acked.first() {
            if s == self.base {
                let k = (e - self.base) as usize;
                self.data.drain(..k);
                self.base = e;
                self.acked.remove(s, e);
            }
        }
    }

    /// `[off, off + n)` was lost: resend what of it is not acknowledged.
    pub fn on_lost(&mut self, off: u64, n: usize, fin: bool) {
        let end = off + n as u64;
        if fin && !self.fin_acked {
            self.fin_sent = false;
        }
        let a = off.max(self.base);
        if a >= end {
            return;
        }
        // Add [a, end) minus the acknowledged parts.
        let mut x = a;
        let start = match self.acked.m.range(..=a).next_back() {
            Some((&s, &e)) if e > a => s,
            _ => a,
        };
        let covered: Vec<(u64, u64)> = self.acked.m.range(start..end).map(|(&s, &e)| (s, e)).collect();
        for (s, e) in covered {
            if s > x {
                self.lost.insert(x, s.min(end));
            }
            if e > x {
                x = e;
            }
            if x >= end {
                return;
            }
        }
        if x < end {
            self.lost.insert(x, end);
        }
    }

    /// Everything written, and the FIN, is acknowledged.
    pub fn all_acked(&self) -> bool {
        self.data.is_empty() && (!self.fin || self.fin_acked)
    }

    /// Drops everything (a reset stream).
    pub fn clear(&mut self) {
        self.base = self.end();
        self.data.clear();
        self.unsent = self.base;
        self.acked.clear();
        self.lost.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ranges() {
        let mut r = Ranges::default();
        r.insert(10, 20);
        r.insert(30, 40);
        r.insert(20, 30);
        assert_eq!(r.first(), Some((10, 40)));
        r.remove(15, 25);
        assert!(r.contains(10, 15) && r.contains(25, 40) && !r.contains(14, 16));
        r.insert(0, 100);
        assert_eq!(r.first(), Some((0, 100)));
    }

    #[test]
    fn assembler() {
        let mut a = Assembler::default();
        a.insert(5, b"fgh");
        a.insert(0, b"abc");
        assert_eq!(a.available(), 3);
        a.insert(2, b"cde");
        assert_eq!(a.available(), 8);
        let mut out = Vec::new();
        a.read_into(&mut out, 100);
        assert_eq!(out, b"abcdefgh");
        a.insert(0, b"zz");
        assert_eq!(a.available(), 0);
    }

    #[test]
    fn send_buf() {
        let mut s = SendBuf::default();
        s.write(b"0123456789");
        s.fin = true;
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
}
