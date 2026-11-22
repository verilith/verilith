//! The static dictionary (RFC 7932 Appendix A). Trusted: `dict_bytes`
//! returns the bytes of `src/dictionary.bin`, which `spec::dict` names and
//! `tests/tables.rs` checks against the RFC's SHA-256.
use crate::spec::*;
use vstd::prelude::*;

static DICT: [u8; 122784] = *include_bytes!("dictionary.bin");

verus! {

/// The `n` dictionary bytes at `off`.
#[verifier::external_body]
#[inline(always)]
pub fn dict_bytes(off: usize, n: usize) -> (r: &'static [u8])
    requires
        off + n <= 122784,
    ensures
        r@ == Seq::new(n as nat, |i: int| dict(off + i)),
{
    &DICT[off..off + n]
}

} // verus!

/// The whole dictionary, for tests.
pub fn dictionary() -> &'static [u8] {
    &DICT
}
