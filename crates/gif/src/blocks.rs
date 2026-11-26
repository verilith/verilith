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

/// The position after the chain of sub-blocks at `p`. Also returns the
/// work done, one step per sub-block: at most the chain's length in bytes,
/// and at most the bytes after `p` if there is no chain.
pub fn skip_blocks(b: &[u8], p: usize) -> (r: (Option<usize>, Ghost<nat>))
    ensures
        match sub_blocks(b@, p as int) {
            Some((_, e)) => r.0 == Some(e as usize),
            None => r.0 is None,
        },
        r.0 matches Some(e) ==> r.1@ <= e - p,
        p <= b@.len() ==> r.1@ <= b@.len() - p,
{
    proof {
        lemma_sub_blocks_end(b@, p as int);
    }
    if p >= b.len() {
        return (None, Ghost(0));
    }
    let mut q = p;
    let ghost mut work: nat = 0;
    while q < b.len()
        invariant
            p <= q <= b@.len(),
            end_of(sub_blocks(b@, p as int)) == end_of(sub_blocks(b@, q as int)),
            work <= q - p,
        decreases b@.len() - q,
    {
        let n = get(b, q) as usize;
        if n == 0 {
            return (Some(q + 1), Ghost(work + 1));
        }
        if b.len() - q - 1 < n {
            return (None, Ghost(work));
        }
        q = q + 1 + n;
        proof {
            work = work + 1;
        }
    }
    (None, Ghost(work))
}

/// The data of the chain of sub-blocks at `p`, which `skip_blocks` has
/// found to end at `e`. Also returns the work done, a step for each
/// sub-block and each byte copied: at most `2 * (e - p)`.
pub fn gather(b: &[u8], p: usize, e: usize) -> (r: (Vec<u8>, Ghost<nat>))
    requires
        sub_blocks(b@, p as int) matches Some((_, x)) && x == e,
    ensures
        sub_blocks(b@, p as int) == Some((r.0@, e as int)),
        r.1@ <= 2 * (e - p),
        r.0@.len() <= e - p,
{
    proof {
        lemma_sub_blocks_end(b@, p as int);
    }
    let blen = b.len();
    let mut out: Vec<u8> = Vec::with_capacity(e - p);
    let mut q = p;
    let ghost mut work: nat = 0;
    loop
        invariant
            p <= q < b@.len(),
            q < e,
            blen == b@.len(),
            sub_blocks(b@, q as int) is Some,
            sub_blocks(b@, q as int)->Some_0.1 == e,
            sub_blocks(b@, p as int) == Some((out@ + sub_blocks(b@, q as int)->Some_0.0, e as int)),
            work <= 2 * (q - p),
            out@.len() <= q - p,
        decreases b@.len() - q,
    {
        let n = get(b, q) as usize;
        if n == 0 {
            proof {
                assert(out@ + Seq::<u8>::empty() =~= out@);
                reveal_with_fuel(sub_blocks, 1);
            }
            return (out, Ghost(work + 1));
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
            reveal_with_fuel(sub_blocks, 1);
            work = (work + 1 + n) as nat;
        }
        q = q + 1 + n;
    }
}

} // verus!
