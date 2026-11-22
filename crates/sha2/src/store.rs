//! Big-endian stores of a word into a byte slice (part of the trusted
//! base): one line each, with the bytes they write as their `ensures`.
//! LLVM does not merge the eight byte stores the verified form takes into
//! one, so these are what the digests and the length field are written
//! with. `tests/vectors.rs` and the other tests check every digest byte.
use vstd::prelude::*;

verus! {

/// Writes `x` most significant byte first into `b[i..i + 4]`.
#[verifier::external_body]
#[inline(always)]
pub fn put_u32_be(b: &mut [u8], i: usize, x: u32)
    requires
        i + 4 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        forall|k: int| 0 <= k < old(b)@.len() && !(i <= k < i + 4) ==> final(b)@[k] == old(b)@[k],
        forall|k: int|
            0 <= k < 4 ==> #[trigger] final(b)@[i + k] == ((x >> ((24 - 8 * k) as u32)) & 0xff) as u8,
{
    b[i..i + 4].copy_from_slice(&x.to_be_bytes());
}

/// Writes `x` most significant byte first into `b[i..i + 8]`.
#[verifier::external_body]
#[inline(always)]
pub fn put_u64_be(b: &mut [u8], i: usize, x: u64)
    requires
        i + 8 <= old(b)@.len(),
    ensures
        final(b)@.len() == old(b)@.len(),
        forall|k: int| 0 <= k < old(b)@.len() && !(i <= k < i + 8) ==> final(b)@[k] == old(b)@[k],
        forall|k: int| 0 <= k < 8 ==> #[trigger] final(b)@[i + k] == crate::spec::be64(x)[k],
{
    b[i..i + 8].copy_from_slice(&x.to_be_bytes());
}

} // verus!
