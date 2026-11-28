//! The insert and copy length codes of an insert-and-copy symbol, for the
//! meta-block writer (`mbw`) and the compressor.
use crate::spec::CELL;
#[cfg(verus_only)]
use crate::cmeta::*;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The insert and copy length codes of symbol `sym`.
#[inline(always)]
pub fn sym_codes(sym: u16) -> (r: (usize, usize))
    requires
        sym < 704,
    ensures
        r.0 == ins_code(sym as int),
        r.1 == cpy_code(sym as int),
        r.0 < 24,
        r.1 < 24,
{
    proof {
        lemma_codes_range(sym as int);
    }
    let cell = CELL[(sym / 64) as usize] as usize;
    let s = sym as usize;
    ((cell / 8) * 8 + (s / 8) % 8, (cell % 4) * 8 + s % 8)
}

/// The insert and copy length codes of any symbol (0 past the alphabet).
pub fn sym_codes_safe(sym: u16) -> (r: (usize, usize))
    ensures
        r.0 < 24,
        r.1 < 24,
{
    if sym < 704 { sym_codes(sym) } else { (0, 0) }
}



} // verus!
