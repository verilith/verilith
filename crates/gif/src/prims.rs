//! The one memory primitive this crate adds to verilith-core's: a zeroed
//! byte allocation that can fail. It is trusted (`external_body`): Verus
//! has no specification for the allocator.
use vstd::prelude::*;

verus! {

/// A vector of `n` zeros, or `None` if the allocation fails. Large
/// allocations come from `calloc`, which maps zeroed pages lazily.
#[verifier::external_body]
pub fn alloc_zeroed(n: usize) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(v) ==> v@ == Seq::new(n as nat, |i: int| 0u8),
{
    if n == 0 {
        return Some(Vec::new());
    }
    let layout = match std::alloc::Layout::array::<u8>(n) {
        Ok(l) => l,
        Err(_) => return None,
    };
    // SAFETY: `layout` has non-zero size. On success the block holds `n`
    // initialised (zero) bytes allocated by the global allocator with the
    // layout `Vec<u8>` uses for capacity `n`.
    unsafe {
        let p = std::alloc::alloc_zeroed(layout);
        if p.is_null() {
            return None;
        }
        Some(Vec::from_raw_parts(p, n, n))
    }
}

} // verus!
