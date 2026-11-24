//! Data sub-block chains (§15), proven against `spec::sub_blocks`.
use crate::spec::*;
use verilith_core::prims::{extend, get};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Where a chain ends, if it does.
pub open spec fn end_of(r: Option<(Seq<u8>, int)>) -> Option<int> {
    match r {
        Some((_, e)) => Some(e),
        None => None,
    }
}

/// The position after the chain of sub-blocks at `p`.
pub fn skip_blocks(b: &[u8], p: usize) -> (r: Option<usize>)
    ensures
        match sub_blocks(b@, p as int) {
            Some((_, e)) => r == Some(e as usize),
            None => r is None,
        },
{
    proof {
        lemma_sub_blocks_end(b@, p as int);
    }
    if p >= b.len() {
        return None;
    }
    let mut q = p;
    while q < b.len()
        invariant
            q <= b@.len(),
            end_of(sub_blocks(b@, p as int)) == end_of(sub_blocks(b@, q as int)),
        decreases b@.len() - q,
    {
        let n = get(b, q) as usize;
        if n == 0 {
            return Some(q + 1);
        }
        if b.len() - q - 1 < n {
            return None;
        }
        q = q + 1 + n;
    }
    None
}

/// The data of the chain of sub-blocks at `p`, which `skip_blocks` has
/// found to end at `e`.
pub fn gather(b: &[u8], p: usize, e: usize) -> (r: Vec<u8>)
    requires
        sub_blocks(b@, p as int) matches Some((_, x)) && x == e,
    ensures
        sub_blocks(b@, p as int) == Some((r@, e as int)),
{
    proof {
        lemma_sub_blocks_end(b@, p as int);
    }
    let blen = b.len();
    let mut out: Vec<u8> = Vec::with_capacity(e - p);
    let mut q = p;
    loop
        invariant
            q < b@.len(),
            blen == b@.len(),
            sub_blocks(b@, q as int) is Some,
            sub_blocks(b@, p as int) == Some((out@ + sub_blocks(b@, q as int)->Some_0.0, e as int)),
        decreases b@.len() - q,
    {
        let n = get(b, q) as usize;
        if n == 0 {
            proof {
                assert(out@ + Seq::<u8>::empty() =~= out@);
            }
            return out;
        }
        proof {
            reveal_with_fuel(sub_blocks, 1);
            assert(q + 1 + n <= b@.len());
            assert(b@.len() == blen);
        }
        let ghost o = out@;
        let ghost rest = sub_blocks(b@, q + 1 + n)->Some_0.0;
        extend(&mut out, slice_subrange(b, q + 1, q + 1 + n));
        proof {
            assert(o + (b@.subrange(q + 1, q + 1 + n) + rest) =~= out@ + rest);
            lemma_sub_blocks_end(b@, q + 1 + n);
        }
        q = q + 1 + n;
    }
}

} // verus!
