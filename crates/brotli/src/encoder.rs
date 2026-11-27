//! The compressor. Everything it writes is proven to decode, under
//! `spec`, to its input: the encoder carries the spec machine's state as
//! ghost state next to the bits it writes (`elemmas::good`).
use crate::bitwriter::*;
use crate::spec::St;
#[cfg(verus_only)]
use crate::elemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Zeros written by `align` reach the next byte boundary.
proof fn lemma_align_k(old: int, new: int)
    requires
        0 <= old <= new < old + 8,
        new % 8 == 0,
    ensures
        new - old == (8 - old % 8) % 8,
{
}

/// The bits written so far and the spec state they lead to.
pub struct Enc {
    pub bw: BitWriter,
    pub st: Ghost<St>,
}

impl Enc {
    pub open spec fn ok(&self) -> bool {
        &&& self.bw.wf()
        &&& good(self.bw.bits(), self.st@)
    }

    /// A new stream with window `2^wb`.
    pub fn new(wb: u32, cap: usize) -> (r: Enc)
        requires
            16 <= wb <= 24,
        ensures
            r.ok(),
            r.st@.phase is MetaHeader,
            r.st@.out == Seq::<u8>::empty(),
            r.st@.wbits == wb,
            r.st@.dr == seq![4int, 11, 15, 16],
            r.bw.sent() == Seq::<u8>::empty(),
    {
        let mut bw = BitWriter::new(cap);
        let ghost s0 = init();
        let ghost w0 = bw.bits();
        proof {
            lemma_good_init();
            lemma_wbits(w0, s0, wb as int);
            lemma_pow2_small();
        }
        if wb == 16 {
            bw.put(0, 1);
        } else if wb == 17 {
            bw.put(1, 1);
            bw.put(0, 3);
            bw.put(0, 3);
        } else {
            bw.put(1, 1);
            bw.put(wb - 17, 3);
        }
        proof {
            let u = wbits_bits(wb as int);
            assert(bw.bits() =~= w0 + u);
            lemma_good_moves(w0, u, s0, after_wbits(s0, wb as int));
        }
        Enc { bw, st: Ghost(after_wbits(s0, wb as int)) }
    }

    /// Writes `MNIBBLES - 4` and `MLEN - 1`.
    pub fn put_mlen(&mut self, len: usize)
        requires
            old(self).bw.wf(),
            1 <= len <= 0x1000000,
        ensures
            final(self).bw.wf(),
            final(self).bw.bits() == old(self).bw.bits() + mlen_bits(len as int),
            final(self).bw.sent() == old(self).bw.sent(),
            final(self).st == old(self).st,
    {
        proof {
            lemma_pow2_small();
        }
        let v = (len - 1) as u32;
        if v < 0x10000 {
            self.bw.put(0, 2);
            self.bw.put(v, 16);
        } else if v < 0x100000 {
            self.bw.put(1, 2);
            self.bw.put(v, 20);
        } else {
            self.bw.put(2, 2);
            self.bw.put(v, 24);
        }
        proof {
            assert(self.bw.bits() =~= old(self).bw.bits() + mlen_bits(len as int));
        }
    }

    /// Writes `data` as one uncompressed meta-block (not the last).
    pub fn put_stored(&mut self, data: &[u8])
        requires
            old(self).ok(),
            old(self).st@.phase is MetaHeader,
            1 <= data@.len() <= 0x1000000,
        ensures
            final(self).ok(),
            final(self).st@ == (St { phase: Phase::MetaHeader, pos: final(self).st@.pos, out: old(self).st@.out + data@, last: false, mrem: 0, ..old(self).st@ }),
            final(self).bw.sent() == old(self).bw.sent(),
    {
        let ghost w0 = self.bw.bits();
        let ghost s0 = self.st@;
        let len = data.len();
        proof {
            lemma_meta_unc(w0, s0, len as int);
            lemma_pow2_small();
        }
        self.bw.put(0, 1);
        self.put_mlen(len);
        self.bw.put(1, 1);
        let ghost w1 = self.bw.bits();
        proof {
            lemma_bits_of(1, 1);
            lemma_bits_of(0, 1);
            assert(w1 =~= w0 + meta_bits(len as int, true));
        }
        self.bw.align();
        proof {
            lemma_align_k(w1.len() as int, self.bw.bits().len() as int);
            assert(self.bw.bits() =~= w0 + unc_bits(s0.pos, len as int));
            lemma_good_moves(w0, unc_bits(s0.pos, len as int), s0, after_unc(s0, len as int));
        }
        let ghost w2 = self.bw.bits();
        let ghost s2 = after_unc(s0, len as int);
        self.bw.put_bytes(data);
        let ghost s3 = St { phase: Phase::MetaDone, pos: s2.pos + 8 * data@.len(), mrem: 0, out: s2.out + data@, ..s2 };
        proof {
            lemma_unc_bytes(w2, s2, data@);
            lemma_bytes_bits(data@);
            lemma_good_moves(w2, bytes_bits(data@), s2, s3);
            lemma_meta_done(self.bw.bits(), s3);
            assert(self.bw.bits() + Seq::<nat>::empty() =~= self.bw.bits());
            lemma_good_moves(self.bw.bits(), Seq::empty(), s3, St { phase: Phase::MetaHeader, ..s3 });
        }
        self.st = Ghost(St { phase: Phase::MetaHeader, ..s3 });
    }

    /// Ends the stream with an empty last meta-block and returns it.
    pub fn finish(mut self) -> (r: Vec<u8>)
        requires
            self.ok(),
            self.st@.phase is MetaHeader,
            self.bw.sent() == Seq::<u8>::empty(),
        ensures
            decodes(r@, self.st@.out, r@.len() as int),
    {
        let ghost w0 = self.bw.bits();
        let ghost s0 = self.st@;
        proof {
            lemma_meta_end(w0, s0);
            lemma_pow2_small();
        }
        self.bw.put(1, 1);
        self.bw.put(1, 1);
        let ghost w1 = self.bw.bits();
        proof {
            lemma_bits_of(1, 1);
            assert(w1 =~= w0 + fld(1, 1) + fld(1, 1));
        }
        self.bw.align();
        let ghost t = St { phase: Phase::Done, pos: s0.pos + end_bits(s0.pos).len(), last: true, mrem: 0, ..s0 };
        proof {
            lemma_align_k(w1.len() as int, self.bw.bits().len() as int);
            assert(self.bw.bits() =~= w0 + end_bits(s0.pos));
            lemma_good_moves(w0, end_bits(s0.pos), s0, t);
        }
        let ghost wl = self.bw.bits();
        let (out, wf) = self.bw.finish();
        proof {
            assert(Seq::<u8>::empty() + out@ =~= out@);
            assert(wf@ =~= wl);
            lemma_good_decodes(out@, wl, t);
        }
        out
    }
}

/// `data` as a Brotli stream of uncompressed meta-blocks.
pub fn compress_stored(data: &[u8]) -> (r: Vec<u8>)
    ensures
        decodes(r@, data@, r@.len() as int),
{
    let n = data.len();
    let cap = if n <= 0x4000_0000 { n + n / 65536 * 8 + 16 } else { n };
    let mut e = Enc::new(16, cap);
    let mut i: usize = 0;
    while i < n
        invariant
            e.ok(),
            e.st@.phase is MetaHeader,
            e.bw.sent() == Seq::<u8>::empty(),
            i <= n,
            n == data@.len(),
            e.st@.out == data@.subrange(0, i as int),
        decreases n - i,
    {
        let k = if n - i > 0x1000000 { 0x1000000 } else { n - i };
        let piece = vstd::slice::slice_subrange(data, i, i + k);
        e.put_stored(piece);
        proof {
            assert(data@.subrange(0, i as int) + data@.subrange(i as int, i + k) =~= data@.subrange(0, i + k));
        }
        i = i + k;
    }
    proof {
        assert(data@.subrange(0, n as int) =~= data@);
    }
    e.finish()
}

} // verus!
