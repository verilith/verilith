//! Stream reassembly (RFC 9000 §2.2): STREAM and CRYPTO data arrive at
//! any offset, out of order and repeated; the application reads them in
//! order.
//!
//! Proven, after any sequence of calls, of [`Reassembly`] and the map
//! [`Reassembly::received`] of every byte received (the first copy of each
//! offset; QUIC requires later copies to be the same, §2.2):
//!
//! - the bytes the application reads are the received bytes from
//!   [`Reassembly::read_offset`] on, in order, each offset once
//!   ([`Reassembly::read_into`], [`Reassembly::peek`]);
//! - [`Reassembly::contiguous`] is exactly where the received bytes stop
//!   being contiguous, so nothing that could be read is held back;
//! - the buffer stays below twice the window plus [`COMPACT`] bytes
//!   ([`Reassembly::lemma_bounds`]), however the peer splits, repeats or
//!   overlaps its frames: data past `read_offset + window` is refused
//!   (flow control, §4.1, keeps an honest peer inside it).
use verilith_core::prims::extend;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Bytes already read are dropped from the buffer's front once there are
/// at least this many of them and at least as many as are still held (so
/// each byte is moved at most once on average).
pub const COMPACT: u64 = 16384;

/// The largest window.
pub const MAX_WINDOW: u64 = 0x1000_0000;

/// Stream offsets are below 2^62 (§4.5).
pub const OFFSET_LIMIT: u64 = 0x4000_0000_0000_0000;

/// `got` with the bytes of `src` at `offset..` added where `got` has none.
pub open spec fn add(got: IMap<int, u8>, offset: int, src: Seq<u8>) -> IMap<int, u8> {
    IMap::new(
        |o: int| got.contains_key(o) || offset <= o < offset + src.len(),
        |o: int| if got.contains_key(o) { got[o] } else { src[o - offset] },
    )
}

/// The `n` bytes of `got` from `from`.
pub open spec fn run(got: IMap<int, u8>, from: int, n: int) -> Seq<u8> {
    Seq::new(n as nat, |k: int| got[from + k])
}

/// One stream's received bytes.
pub struct Reassembly {
    /// The bytes at offsets `base..base + data.len()` (where received).
    data: Vec<u8>,
    /// Which of them were received, for offsets from `contig` on.
    have: Vec<bool>,
    base: u64,
    /// The next offset to read.
    read: u64,
    /// Every offset below this was received.
    contig: u64,
    /// Data must end within `read + window`.
    window: u64,
    received: Ghost<IMap<int, u8>>,
}

impl Reassembly {
    /// Every byte received, by offset.
    pub closed spec fn received(&self) -> IMap<int, u8> {
        self.received@
    }

    pub closed spec fn read_spec(&self) -> int {
        self.read as int
    }

    pub closed spec fn contig_spec(&self) -> int {
        self.contig as int
    }

    pub closed spec fn window_spec(&self) -> int {
        self.window as int
    }

    /// Bytes of memory the buffer holds.
    pub closed spec fn mem(&self) -> int {
        self.data.len() as int
    }

    pub closed spec fn end(&self) -> int {
        self.base + self.data.len()
    }

    pub closed spec fn inv(&self) -> bool {
        let b = self.base as int;
        let e = b + self.data.len();
        let g = self.received@;
        &&& self.have.len() == self.data.len()
        &&& b <= self.read <= self.contig <= e
        &&& e <= self.read + self.window
        &&& e <= OFFSET_LIMIT
        &&& 1 <= self.window <= MAX_WINDOW
        &&& (self.read - b < COMPACT || self.read - b < e - self.read)
        &&& forall|o: int| 0 <= o < self.contig ==> #[trigger] g.contains_key(o)
        &&& forall|o: int| (o < 0 || o >= e) ==> !#[trigger] g.contains_key(o)
        &&& forall|i: int|
            self.read - b <= i < self.contig - b ==> g[b + i] == #[trigger] self.data@[i]
        &&& forall|i: int|
            self.contig - b <= i < self.data.len() ==> (#[trigger] self.have@[i] == g.contains_key(b + i)
                && (self.have@[i] ==> g[b + i] == self.data@[i]))
        &&& (self.contig < e ==> !self.have@[self.contig - b])
    }

    /// What the invariant gives a caller: the bytes from `read_offset` to
    /// `contiguous` were received, the one at `contiguous` was not, and
    /// the buffer's size is bounded by the window.
    pub proof fn lemma_bounds(&self)
        requires
            self.inv(),
        ensures
            0 <= self.read_spec() <= self.contig_spec(),
            forall|o: int| 0 <= o < self.contig_spec() ==> #[trigger] self.received().contains_key(o),
            !self.received().contains_key(self.contig_spec()),
            self.mem() < 2 * self.window_spec() + COMPACT,
            self.window_spec() <= MAX_WINDOW,
    {
        let b = self.base as int;
        let e = self.end();
        if self.contig < e {
            assert(self.have@[self.contig - b] == self.received@.contains_key(b + (self.contig - b)));
        }
    }

    /// Nothing received; data may end up to `window` bytes past what was
    /// read.
    pub fn new(window: u64) -> (r: Reassembly)
        requires
            1 <= window <= MAX_WINDOW,
        ensures
            r.inv(),
            r.received() == IMap::<int, u8>::empty(),
            r.read_spec() == 0,
            r.window_spec() == window,
    {
        Reassembly { data: Vec::new(), have: Vec::new(), base: 0, read: 0, contig: 0, window, received: Ghost(IMap::empty()) }
    }

    /// The offset of the next byte to read.
    pub fn read_offset(&self) -> (r: u64)
        ensures
            r == self.read_spec(),
    {
        self.read
    }

    /// Received bytes are contiguous up to this offset.
    pub fn contiguous(&self) -> (r: u64)
        ensures
            r == self.contig_spec(),
    {
        self.contig
    }

    /// Bytes ready to read.
    pub fn available(&self) -> (r: usize)
        requires
            self.inv(),
        ensures
            r == self.contig_spec() - self.read_spec(),
    {
        (self.contig - self.read) as usize
    }

    /// Bytes the buffer holds.
    pub fn buffered(&self) -> (r: usize)
        ensures
            r == self.mem(),
    {
        self.data.len()
    }

    /// Adds `src` at `offset`. False (and nothing changes) if it ends past
    /// `read_offset + window`; bytes already received are kept.
    pub fn insert(&mut self, offset: u64, src: &[u8]) -> (ok: bool)
        requires
            old(self).inv(),
            offset + src@.len() <= OFFSET_LIMIT,
        ensures
            final(self).inv(),
            ok == (offset + src@.len() <= old(self).contig_spec() || offset + src@.len() <= old(self).read_spec()
                + old(self).window_spec()),
            ok ==> final(self).received() == add(old(self).received(), offset as int, src@),
            !ok ==> final(self).received() == old(self).received(),
            final(self).read_spec() == old(self).read_spec(),
            final(self).window_spec() == old(self).window_spec(),
            final(self).contig_spec() >= old(self).contig_spec(),
    {
        let ghost g0 = self.received@;
        let end = offset + src.len() as u64;
        if end <= self.contig {
            proof {
                assert(add(g0, offset as int, src@) =~= g0);
            }
            return true;
        }
        if end > self.read + self.window {
            return false;
        }
        let e = self.base + self.data.len() as u64;
        if offset <= self.contig && self.contig == e {
            // In order, past everything held: append.
            let from = (self.contig - offset) as usize;
            let s = slice_subrange(src, from, src.len());
            extend(&mut self.data, s);
            let n = (end - self.base) as usize;
            self.have.resize(n, false);
            proof {
                let b = self.base as int;
                let g1 = add(g0, offset as int, src@);
                self.received = Ghost(g1);
                assert forall|o: int| 0 <= o < end implies #[trigger] g1.contains_key(o) by {
                    if o >= offset {
                    } else {
                        assert(g0.contains_key(o));
                    }
                }
                assert forall|o: int| (o < 0 || o >= end) implies !#[trigger] g1.contains_key(o) by {
                    assert(!g0.contains_key(o));
                }
                assert forall|i: int| self.read - b <= i < end - b implies g1[b + i] == #[trigger] self.data@[i] by {
                    if i < e - b {
                        assert(g0.contains_key(b + i));
                    } else {
                        assert(!g0.contains_key(b + i));
                        assert(self.data@[i] == s@[i - (e - b)]);
                    }
                }
            }
            self.contig = end;
            return true;
        }
        if end > e {
            let n = (end - self.base) as usize;
            let old_len = self.data.len();
            self.data.resize(n, 0u8);
            self.have.resize(n, false);
            proof {
                assert forall|i: int| old_len <= i < n implies !#[trigger] self.have@[i] by {
                    assert(cloned::<bool>(false, self.have@[i]));
                }
                assert(self.have@.subrange(0, old_len as int) =~= old(self).have@);
                assert(self.data@.subrange(0, old_len as int) =~= old(self).data@);
                assert forall|i: int| 0 <= i < old_len implies #[trigger] self.have@[i] == old(self).have@[i]
                    && self.data@[i] == old(self).data@[i] by {
                    assert(self.have@.subrange(0, old_len as int)[i] == self.have@[i]);
                    assert(self.data@.subrange(0, old_len as int)[i] == self.data@[i]);
                }
            }
        }
        let ghost b = self.base as int;
        let e1x = self.base + self.data.len() as u64;
        let ghost e1 = e1x as int;
        let start = if offset > self.contig { offset } else { self.contig };
        let mut o = start;
        while o < end
            invariant
                self.have.len() == self.data.len(),
                b == self.base,
                e1 == b + self.data.len(),
                end <= e1,
                e1 <= self.read + self.window,
                e1 == if end > e { end as int } else { e as int },
                start <= o <= end,
                b <= old(self).contig,
                start == if offset > old(self).contig { offset } else { old(self).contig },
                self.read == old(self).read,
                self.contig == old(self).contig,
                self.window == old(self).window,
                self.base == old(self).base,
                offset + src@.len() == end,
                self.contig >= offset || start == offset,
                // Positions held before are unchanged below `contig`.
                forall|i: int| 0 <= i < self.contig - b ==> #[trigger] self.data@[i] == old(self).data@[i],
                forall|p: int|
                    #[trigger] self.received@.contains_key(p) == (g0.contains_key(p) || (start <= p < o)),
                forall|p: int| g0.contains_key(p) ==> #[trigger] self.received@[p] == g0[p],
                forall|p: int|
                    start <= p < o && !g0.contains_key(p) ==> #[trigger] self.received@[p] == src@[p - offset],
                forall|i: int|
                    self.contig - b <= i < self.data.len() ==> (#[trigger] self.have@[i]
                        == self.received@.contains_key(b + i) && (self.have@[i] ==> self.received@[b + i]
                        == self.data@[i])),
                forall|o2: int| (o2 < 0 || o2 >= e1) ==> !#[trigger] self.received@.contains_key(o2),
            decreases end - o,
        {
            let idx = (o - self.base) as usize;
            if !self.have[idx] {
                proof {
                    assert(self.have@[idx as int] == self.received@.contains_key(b + idx));
                    assert(!g0.contains_key(o as int));
                }
                self.data.set(idx, src[(o - offset) as usize]);
                self.have.set(idx, true);
                proof {
                    self.received = Ghost(self.received@.insert(o as int, src@[o - offset]));
                }
            } else {
                proof {
                    assert(self.have@[idx as int] == self.received@.contains_key(b + idx));
                    assert(g0.contains_key(o as int));
                }
            }
            o = o + 1;
        }
        proof {
            assert(self.received@ =~= add(g0, offset as int, src@)) by {
                assert forall|p: int| #[trigger] self.received@.contains_key(p) == add(g0, offset as int, src@).contains_key(p) by {
                    if offset <= p < start {
                        assert(p < old(self).contig);
                        assert(g0.contains_key(p));
                    }
                }
            }
        }
        // Advance over what is now contiguous.
        while self.contig < e1x && self.have[(self.contig - self.base) as usize]
            invariant
                self.have.len() == self.data.len(),
                b == self.base,
                e1 == b + self.data.len(),
                e1 <= self.read + self.window,
                e1 <= OFFSET_LIMIT,
                old(self).contig <= self.contig <= e1,
                b <= old(self).contig,
                e1x == e1,
                self.read == old(self).read,
                self.window == old(self).window,
                self.received@ == add(g0, offset as int, src@),
                forall|i: int| 0 <= i < old(self).contig - b ==> #[trigger] self.data@[i] == old(self).data@[i],
                forall|o2: int| 0 <= o2 < self.contig ==> #[trigger] self.received@.contains_key(o2),
                forall|i: int|
                    self.read - b <= i < self.contig - b ==> self.received@[b + i] == #[trigger] self.data@[i],
                forall|i: int|
                    self.contig - b <= i < self.data.len() ==> (#[trigger] self.have@[i]
                        == self.received@.contains_key(b + i) && (self.have@[i] ==> self.received@[b + i]
                        == self.data@[i])),
            decreases e1 - self.contig,
        {
            proof {
                let i = self.contig - b;
                assert(self.have@[i] == self.received@.contains_key(b + i));
            }
            self.contig = self.contig + 1;
        }
        proof {
            // The old prefix kept its values.
            assert forall|i: int| self.read - b <= i < old(self).contig - b implies self.received@[b + i]
                == #[trigger] self.data@[i] by {
                assert(old(self).data@[i] == g0[b + i]);
                assert(g0.contains_key(b + i));
            }
        }
        true
    }

    /// Drops what was read from the front, when that frees at least as
    /// much as it moves.
    fn compact(&mut self)
        requires
            old(self).have.len() == old(self).data.len(),
            old(self).base <= old(self).read <= old(self).base + old(self).data.len(),
            old(self).base + old(self).data.len() <= OFFSET_LIMIT,
        ensures
            final(self).have.len() == final(self).data.len(),
            final(self).read == old(self).read,
            final(self).contig == old(self).contig,
            final(self).window == old(self).window,
            final(self).received == old(self).received,
            final(self).base + final(self).data.len() == old(self).base + old(self).data.len(),
            final(self).base <= final(self).read,
            (final(self).read - final(self).base < COMPACT || final(self).read - final(self).base < final(self).base
                + final(self).data.len() - final(self).read),
            forall|i: int|
                final(self).read - final(self).base <= i < final(self).data.len() ==> #[trigger] final(self).data@[i]
                    == old(self).data@[i + (final(self).base - old(self).base)] && final(self).have@[i] == old(
                    self,
                ).have@[i + (final(self).base - old(self).base)],
            old(self).base <= final(self).base,
    {
        let k = self.read - self.base;
        let e = self.base + self.data.len() as u64;
        if k >= COMPACT && k >= e - self.read {
            let ku = k as usize;
            let d = self.data.split_off(ku);
            self.data = d;
            let h = self.have.split_off(ku);
            self.have = h;
            self.base = self.read;
        }
    }

    /// Reads up to `max` bytes onto `out`: the received bytes from
    /// `read_offset` on.
    pub fn read_into(&mut self, out: &mut Vec<u8>, max: usize) -> (n: usize)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            n == if max < old(self).contig_spec() - old(self).read_spec() { max as int } else { old(self).contig_spec()
                - old(self).read_spec() },
            final(out)@ == old(out)@ + run(old(self).received(), old(self).read_spec(), n as int),
            final(self).read_spec() == old(self).read_spec() + n,
            final(self).contig_spec() == old(self).contig_spec(),
            final(self).received() == old(self).received(),
            final(self).window_spec() == old(self).window_spec(),
    {
        let avail = (self.contig - self.read) as usize;
        let n = if max < avail { max } else { avail };
        let start = (self.read - self.base) as usize;
        let s = slice_subrange(self.data.as_slice(), start, start + n);
        extend(out, s);
        proof {
            assert(s@ =~= run(self.received@, self.read as int, n as int)) by {
                assert forall|k: int| 0 <= k < n implies s@[k] == run(self.received@, self.read as int, n as int)[k] by {
                    assert(self.data@[start + k] == self.received@[self.base + (start + k)]);
                }
            }
        }
        self.consume(n);
        n
    }

    /// The bytes ready to read.
    pub fn peek(&self) -> (s: &[u8])
        requires
            self.inv(),
        ensures
            s@ == run(self.received(), self.read_spec(), self.contig_spec() - self.read_spec()),
    {
        let start = (self.read - self.base) as usize;
        let n = (self.contig - self.read) as usize;
        let s = slice_subrange(self.data.as_slice(), start, start + n);
        proof {
            assert(s@ =~= run(self.received@, self.read as int, n as int)) by {
                assert forall|k: int| 0 <= k < n implies s@[k] == run(self.received@, self.read as int, n as int)[k] by {
                    assert(self.data@[start + k] == self.received@[self.base + (start + k)]);
                }
            }
        }
        s
    }

    /// Marks `n` ready bytes read.
    pub fn consume(&mut self, n: usize)
        requires
            old(self).inv(),
            n <= old(self).contig_spec() - old(self).read_spec(),
        ensures
            final(self).inv(),
            final(self).read_spec() == old(self).read_spec() + n,
            final(self).contig_spec() == old(self).contig_spec(),
            final(self).received() == old(self).received(),
            final(self).window_spec() == old(self).window_spec(),
    {
        let ghost s0 = *self;
        self.read = self.read + n as u64;
        let ghost s1 = *self;
        self.compact();
        proof {
            let b0 = s0.base as int;
            let b = self.base as int;
            let d = b - b0;
            let g = self.received@;
            assert forall|i: int| self.read - b <= i < self.contig - b implies g[b + i] == #[trigger] self.data@[i] by {
                assert(self.data@[i] == s1.data@[i + d]);
                assert(s0.data@[i + d] == g[b0 + (i + d)]);
            }
            assert forall|i: int| self.contig - b <= i < self.data.len() implies (#[trigger] self.have@[i]
                == g.contains_key(b + i) && (self.have@[i] ==> g[b + i] == self.data@[i])) by {
                assert(self.data@[i] == s1.data@[i + d]);
                assert(self.have@[i] == s1.have@[i + d]);
                assert(s0.have@[i + d] == g.contains_key(b0 + (i + d)));
            }
            if self.contig < self.base + self.data.len() {
                let i = self.contig - b;
                assert(self.have@[i] == s1.have@[i + d]);
            }
        }
    }
}

} // verus!
