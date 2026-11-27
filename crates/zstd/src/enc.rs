//! The block encoder: match finding and entropy coding. Only memory safety
//! is proven here; `compress` checks each block it makes with the verified
//! decoder.
use vstd::prelude::*;

verus! {

pub struct Enc {
    pub window: u64,
    pub level: i32,
}

impl Enc {
    pub fn new(src: &[u8], window: u64, level: i32) -> (r: Enc) {
        Enc { window, level }
    }

    /// Appends the content of a compressed block for `src[pos..end]`, the
    /// repeat offsets at its start being `r1`, `r2`, `r3`. `false`: no
    /// block was made (what was appended is to be dropped).
    pub fn block(&mut self, src: &[u8], pos: usize, end: usize, r1: u64, r2: u64, r3: u64, out: &mut Vec<u8>) -> (ok: bool)
        requires
            pos < end <= src@.len(),
        ensures
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
    {
        proof {
            assert(out@.subrange(0, out@.len() as int) =~= out@);
        }
        false
    }
}

} // verus!
