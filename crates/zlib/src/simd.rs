//! CPU-specific code paths (part of the trusted base).
//!
//! - `run` is the verified `Inflater::run`, compiled a second time with
//!   BMI2 enabled when the CPU has it.
//!
//! The checksum kernels (AVX2 Adler-32, PCLMULQDQ CRC-32) moved to
//! `verilith_core::checksum::cpu`.
use crate::inflate::{Inflater, Status};
#[cfg(verus_only)]
use crate::inflate::{body_cost, bit_cost, credit, fail_cost, header_cost, past, prefix, MODE_DONE};
#[cfg(verus_only)]
use crate::spec::nbits;
use vstd::prelude::*;

verus! {

/// `Inflater::run`, compiled with BMI2 (faster variable shifts) when the CPU
/// has it.
#[verifier::external_body]
pub fn run(inf: &mut Inflater, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (st: Status)
    requires
        prefix(input@, b),
        old(inf).in_pos <= input@.len(),
        old(inf).inv(b),
        old(inf).out_pos <= old(out)@.len(),
    ensures
        final(inf).in_pos <= input@.len(),
        final(inf).fixed_ok(),
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, old(inf).out_pos as int) == old(out)@.subrange(
            0,
            old(inf).out_pos as int,
        ),
        old(inf).out_pos <= final(inf).out_pos <= final(out)@.len(),
        st == Status::Done ==> final(inf).inv(b) && final(inf).mode == MODE_DONE && old(inf).rest(b, old(out)@.subrange(0, old(inf).out_pos as int)) == Some(
            (final(inf).pos(), final(out)@.subrange(0, final(inf).out_pos as int)),
        ),
        st == Status::NeedOutput ==> final(inf).inv(b) && final(inf).out_pos == final(out)@.len() && final(inf).rest(b, final(out)@.subrange(0, final(inf).out_pos as int))
            == old(inf).rest(b, old(out)@.subrange(0, old(inf).out_pos as int)),
        st == Status::BadData ==> old(inf).rest(
            b,
            old(out)@.subrange(0, old(inf).out_pos as int),
        ) is None,
        st == Status::Truncated ==> final(inf).inv(b) && final(inf).rest(
            b,
            final(out)@.subrange(0, final(inf).out_pos as int),
        ) == old(inf).rest(b, old(out)@.subrange(0, old(inf).out_pos as int)) && (input@ == b
            ==> old(inf).rest(b, old(out)@.subrange(0, old(inf).out_pos as int)) is None),
        st == Status::Truncated ==> past(old(inf).rest(b, old(out)@.subrange(0, old(inf).out_pos as int)), nbits(input@)),
        st == Status::Truncated ==> final(inf).pos() >= old(inf).pos() && final(inf).work@ + credit(final(inf).fixed, final(inf).mode)
            <= old(inf).work@ + credit(old(inf).fixed, old(inf).mode) + bit_cost() * (final(inf).pos() - old(inf).pos())
            + (final(inf).out_pos - old(inf).out_pos) + fail_cost(),
        st == Status::Done || st == Status::NeedOutput ==> final(inf).pos() >= old(inf).pos()
            && final(inf).work@ + credit(final(inf).fixed, final(inf).mode) <= old(inf).work@
            + credit(old(inf).fixed, old(inf).mode) + bit_cost() * (final(inf).pos() - old(inf).pos()) + (final(inf).out_pos - old(inf).out_pos) + body_cost(),
        final(inf).work@ <= old(inf).work@ + credit(old(inf).fixed, old(inf).mode)
            + bit_cost() * (nbits(input@) - old(inf).pos()) + (final(inf).out_pos - old(inf).out_pos) + header_cost() + body_cost(),
{
    #[cfg(target_arch = "x86_64")]
    {
        if std::is_x86_feature_detected!("bmi2") {
            // SAFETY: the CPU supports BMI2.
            return unsafe { run_bmi2(inf, input, Ghost(b), out) };
        }
    }
    inf.run(input, Ghost(b), out)
}

} // verus!

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
unsafe fn run_bmi2(inf: &mut Inflater, input: &[u8], b: Ghost<Seq<u8>>, out: &mut [u8]) -> Status {
    inf.run(input, b, out)
}
