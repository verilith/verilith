//! Declassification: the one point where verilith-aes lets a value computed
//! from secrets decide anything.
//!
//! `open` decides once, on whether the tag matched (SP 800-38D §7.2 step 8),
//! which its caller learns from the result anyway. It goes through
//! [`declassify`], a function the compiler keeps as a call, so that the
//! static check of the compiled code (`tools/ctcheck.py`) sees exactly where
//! a secret becomes public and treats only that value as public. Nothing
//! else in the crate may branch on, or index memory with, a secret.
use vstd::prelude::*;

verus! {

/// `b`, made public. Trusted to return `b`; kept out of line (and opaque to
/// the optimizer, through `black_box`) so that the decision on it is a
/// decision on the call's result, where the binary check can see it.
#[verifier::external_body]
#[inline(never)]
pub fn declassify(b: bool) -> (r: bool)
    ensures
        r == b,
{
    core::hint::black_box(b)
}

} // verus!
