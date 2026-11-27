//! Flushing the compressor's output: an empty metadata meta-block pads the
//! stream to a byte boundary without adding output, so every byte written
//! so far can be handed out.
use crate::encoder::Enc;
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use crate::elemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// `ISLAST = 0`, `MNIBBLES = 0` (code 3), reserved 0, `MSKIPBYTES = 0`,
/// then zeros to the byte boundary.
pub open spec fn flush_bits(pos: int) -> Seq<nat> {
    fld(0, 1) + (fld(3, 2) + (fld(0, 1) + (fld(0, 2) + fld(0, ((8 - (pos + 6) % 8) % 8) as nat))))
}

#[verifier::spinoff_prover]
proof fn lemma_flush_at(b: Seq<u8>, w: Seq<nat>, s: St, k: nat)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
        k == ((8 - (s.pos + 6) % 8) % 8) as nat,
        ext(b, w + flush_bits(s.pos)),
    ensures
        step(b, s) == Step::Next(St { phase: Phase::Metadata, pos: s.pos + 6 + k, last: false, mrem: 0, ..s }),
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    lemma_bits_of(3, 2);
    lemma_bits_of(0, 2);
    lemma_bits_of(0, k);
    lemma_pow2_pos(k);
    let p = w.len() as int;
    let u = flush_bits(s.pos);
    let w1 = w + fld(0, 1);
    let w2 = w1 + fld(3, 2);
    let w3 = w2 + fld(0, 1);
    let w4 = w3 + fld(0, 2);
    lemma_rd(b, w, 0, 1, fld(3, 2) + (fld(0, 1) + (fld(0, 2) + fld(0, k))));
    assert(w + u =~= w1 + (fld(3, 2) + (fld(0, 1) + (fld(0, 2) + fld(0, k)))));
    lemma_rd(b, w1, 3, 2, fld(0, 1) + (fld(0, 2) + fld(0, k)));
    assert(w + u =~= w2 + (fld(0, 1) + (fld(0, 2) + fld(0, k))));
    lemma_rd(b, w2, 0, 1, fld(0, 2) + fld(0, k));
    assert(w + u =~= w3 + (fld(0, 2) + fld(0, k)));
    lemma_rd(b, w3, 0, 2, fld(0, k));
    assert(w + u =~= w4 + (fld(0, k) + Seq::<nat>::empty()));
    lemma_rd(b, w4, 0, k, Seq::empty());
    let q = p + 6;
    assert(w4.len() == q);
    assert(pad(b, q) == R::<()>::Ok((), q + k));
    let h = MetaHeader { last: false, kind: Kind::Metadata, len: 0 };
    assert(read_meta_len(b, p + 1, false) == pad_then(b, q, h));
    assert(read_meta_header(b, p) == R::Ok(h, q + k));
    crate::decoder::lemma_step_header(b, s);
}

pub proof fn lemma_flush(w: Seq<nat>, s: St)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
    ensures
        moves(w, flush_bits(s.pos), s, St { phase: Phase::MetaHeader, pos: s.pos + flush_bits(s.pos).len(), last: false, mrem: 0, ..s }),
        (s.pos + flush_bits(s.pos).len()) % 8 == 0,
{
    let k = ((8 - (s.pos + 6) % 8) % 8) as nat;
    lemma_bits_of(0, 1);
    lemma_bits_of(3, 2);
    lemma_bits_of(0, 2);
    lemma_bits_of(0, k);
    let u = flush_bits(s.pos);
    let t1 = St { phase: Phase::Metadata, pos: s.pos + 6 + k, last: false, mrem: 0, ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t1) by {
        lemma_flush_at(b, w, s, k);
    }
    lemma_moves_step(w, u, s, t1);
    let w1 = w + u;
    let t2 = St { phase: Phase::MetaDone, ..t1 };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w1 + Seq::empty()) implies step(b, t1) == Step::Next(t2) by {
        crate::decoder::lemma_step_metadata(b, t1);
    }
    lemma_moves_step(w1, Seq::empty(), t1, t2);
    lemma_meta_done(w1 + Seq::empty(), t2);
    let t3 = St { phase: Phase::MetaHeader, ..t2 };
    assert(w1 + Seq::<nat>::empty() =~= w1);
    assert(Seq::<nat>::empty() + Seq::<nat>::empty() =~= Seq::<nat>::empty());
    lemma_moves_trans(w1, Seq::empty(), Seq::empty(), t1, t2, t3);
    assert(u + Seq::<nat>::empty() =~= u);
    lemma_moves_trans(w, u, Seq::empty(), s, t1, t3);
}

impl Enc {
    /// Pads the stream to a byte boundary (with an empty metadata block)
    /// and hands out every byte written so far.
    pub fn flush(&mut self) -> (r: Vec<u8>)
        requires
            old(self).ok(),
            old(self).st@.phase is MetaHeader,
        ensures
            final(self).ok(),
            final(self).st@ == (St { phase: Phase::MetaHeader, pos: final(self).st@.pos, last: false, mrem: 0, ..old(self).st@ }),
            final(self).bw.sent() == old(self).bw.sent() + r@,
    {
        let ghost w0 = self.bw.bits();
        let ghost s0 = self.st@;
        proof {
            lemma_flush(w0, s0);
            lemma_pow2_small();
        }
        self.bw.put(0, 1);
        self.bw.put(3, 2);
        self.bw.put(0, 1);
        self.bw.put(0, 2);
        let ghost w1 = self.bw.bits();
        self.bw.align();
        let ghost t = St { phase: Phase::MetaHeader, pos: s0.pos + flush_bits(s0.pos).len(), last: false, mrem: 0, ..s0 };
        proof {
            crate::encoder::lemma_align_k(w1.len() as int, self.bw.bits().len() as int);
            lemma_bits_of(0, ((8 - (s0.pos + 6) % 8) % 8) as nat);
            assert(self.bw.bits() =~= w0 + flush_bits(s0.pos));
            lemma_good_moves(w0, flush_bits(s0.pos), s0, t);
        }
        self.st = Ghost(t);
        self.bw.take()
    }
}

} // verus!
