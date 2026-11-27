//! The streaming compressor: input arrives in pieces, output can be taken
//! at any time, and a flush makes everything so far decodable. The bytes
//! handed out, in order, are proven to decode to the input.
use crate::compress::*;
use crate::encoder::Enc;
use crate::mblock::shl1;
#[cfg(verus_only)]
use crate::mblock::drs;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Inputs this long (4 GiB) or longer go out as stored meta-blocks: the
/// match finder keeps 32-bit positions.
pub const LIMIT: usize = 0xFFFF_FF00;

pub struct Compressor {
    pub e: Enc,
    pub data: Vec<u8>,
    pub done: usize,
    pub mf: Mf,
    pub dr: [u32; 4],
    pub p: Params,
    pub wb: u32,
    pub last: usize,
}

impl Compressor {
    pub open spec fn ok(&self) -> bool {
        &&& self.e.ok()
        &&& self.e.st@.phase is MetaHeader
        &&& self.done <= self.data@.len()
        &&& self.e.st@.out == self.data@.subrange(0, self.done as int)
        &&& self.e.st@.wbits == self.wb
        &&& self.e.st@.dr == drs(self.dr)
        &&& 16 <= self.wb <= 24
        &&& 1 <= self.p.block <= 0x100_0000
        &&& self.p.ways == 4 || self.p.ways == 8 || self.p.ways == 16 || self.p.ways == 32
        &&& (self.data@.len() < LIMIT ==> self.mf.wf(self.data@.len()))
    }

    /// The input so far.
    pub closed spec fn input(&self) -> Seq<u8> {
        self.data@
    }

    /// The bytes handed out so far.
    pub closed spec fn sent(&self) -> Seq<u8> {
        self.e.bw.sent()
    }

    pub fn new(quality: u32, lgwin: u32) -> (r: Compressor)
        ensures
            r.ok(),
            r.input() == Seq::<u8>::empty(),
            r.sent() == Seq::<u8>::empty(),
    {
        let wb = if lgwin < 16 { 16 } else if lgwin > 24 { 24 } else { lgwin };
        let e = Enc::new(wb, 1 << 16);
        let p = params(quality);
        proof {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(4, wb as nat);
            crate::elemmas::lemma_pow2_small();
        }
        let wmax = (shl1(wb) - 16) as usize;
        let mf = Mf::new(0, p.depth, p.lazy, p.quick, p.ways, p.h7, wmax);
        let r = Compressor { e, data: Vec::new(), done: 0, mf, dr: [4, 11, 15, 16], p, wb, last: 4 };
        proof {
            assert(drs(r.dr) =~= seq![4int, 11, 15, 16]);
            assert(r.data@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        r
    }

    /// Takes in more input.
    pub fn push(&mut self, input: &[u8])
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).input() == old(self).input() + input@,
            final(self).sent() == old(self).sent(),
    {
        let n0 = self.data.len();
        let mut i: usize = 0;
        while i < input.len()
            invariant
                self.ok(),
                self.data@ == old(self).data@ + input@.subrange(0, i as int),
                self.e.bw.sent() == old(self).e.bw.sent(),
                i <= input@.len(),
            decreases input@.len() - i,
        {
            let ghost d0 = self.data@;
            self.data.push(input[i]);
            if self.data.len() < LIMIT {
                self.mf.grow(self.data.len());
            }
            proof {
                assert(self.data@.subrange(0, self.done as int) =~= d0.subrange(0, self.done as int));
                assert(input@.subrange(0, i + 1) =~= input@.subrange(0, i as int).push(input@[i as int]));
            }
            i = i + 1;
        }
        proof {
            assert(input@.subrange(0, input@.len() as int) =~= input@);
        }
    }

    /// Compresses the input not yet written: whole blocks only, unless
    /// `all`.
    pub fn compress_pending(&mut self, all: bool)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent(),
            all ==> final(self).done == final(self).data@.len(),
    {
        let n = self.data.len();
        while self.done < n
            invariant
                self.ok(),
                self.data@ == old(self).data@,
                self.e.bw.sent() == old(self).e.bw.sent(),
                n == self.data@.len(),
            ensures
                self.ok(),
                self.data@ == old(self).data@,
                self.e.bw.sent() == old(self).e.bw.sent(),
                all ==> self.done == n,
            decreases n - self.done,
        {
            let rest = n - self.done;
            if rest < self.p.block && !all {
                break;
            }
            let k = if rest > self.p.block { self.p.block } else { rest };
            let i = self.done;
            if n < LIMIT {
                let lz = parse(&mut self.mf, self.data.as_slice(), i, i + k, self.last);
                put_block(&mut self.e, &mut self.dr, self.wb, self.data.as_slice(), i, i + k, &lz);
                self.last = self.dr[0] as usize;
            } else {
                let piece = vstd::slice::slice_subrange(self.data.as_slice(), i, i + k);
                self.e.put_stored(piece);
                proof {
                    assert(self.data@.subrange(0, i as int) + self.data@.subrange(i as int, i + k) =~= self.data@.subrange(0, i + k));
                }
            }
            self.done = i + k;
        }
    }

    /// The whole bytes written so far.
    pub fn take(&mut self) -> (r: Vec<u8>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent() + r@,
    {
        self.e.bw.take()
    }

    /// Compresses all the input so far and pads to a byte boundary: what
    /// has been handed out then decodes to the input so far.
    pub fn flush(&mut self) -> (r: Vec<u8>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).input() == old(self).input(),
            final(self).sent() == old(self).sent() + r@,
    {
        self.compress_pending(true);
        self.e.flush()
    }

    /// Ends the stream: everything handed out, then `r`, decodes to the
    /// input.
    pub fn finish(mut self) -> (r: Vec<u8>)
        requires
            self.ok(),
        ensures
            decodes(self.sent() + r@, self.input(), (self.sent() + r@).len() as int),
    {
        self.compress_pending(true);
        proof {
            assert(self.data@.subrange(0, self.data@.len() as int) =~= self.data@);
        }
        self.e.finish()
    }
}

} // verus!
