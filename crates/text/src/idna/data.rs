//! The UTS #46 data the IDNA spec is defined over: the generated tables
//! seen as uninterpreted functions, the per-character properties read from
//! them, and the facts about the data that the proofs rely on.
//!
//! Trusted here: each `*_at` accessor returns its table's entry (each is
//! one array read), and the `axiom_*` facts, which tests/idna_data.rs checks
//! for every code point.
#[cfg(verus_only)]
use super::super::unicode::data::is_scalar;
use super::tables::*;
use vstd::prelude::*;

verus! {

pub uninterp spec fn idna_l1(i: int) -> u16;

pub uninterp spec fn idna_l2(i: int) -> u16;

pub uninterp spec fn idna_data(i: int) -> u32;

pub uninterp spec fn idna_pool(i: int) -> u32;

macro_rules! accessor {
    ($name:ident, $table:ident, $len:ident, $spec:ident, $ty:ty) => {
        verus! {
            #[doc = concat!("Entry `i` of `", stringify!($table), "`.")]
            #[verifier::external_body]
            #[inline(always)]
            pub fn $name(i: usize) -> (r: $ty)
                requires
                    i < $len,
                ensures
                    r == $spec(i as int),
            {
                // SAFETY: `i < $len`, the length of the table, is a precondition.
                unsafe { *$table.get_unchecked(i) }
            }
        }
    };
}

accessor!(idna_l1_at, IDNA_L1, IDNA_L1_LEN, idna_l1, u16);
accessor!(idna_l2_at, IDNA_L2, IDNA_L2_LEN, idna_l2, u16);
accessor!(idna_data_at, IDNA_DATA, IDNA_DATA_LEN, idna_data, u32);
accessor!(idna_pool_at, IDNA_POOL, IDNA_POOL_LEN, idna_pool, u32);

/// The word of a code point above U+10FFFF: disallowed, with no other
/// properties.
pub const OUT_OF_RANGE_WORD: u32 = 4 | (11 << 4);

/// The word of `c` (see tools/gen_idna.py).
pub open spec fn iword(c: u32) -> u32 {
    if c <= 0x10FFFF {
        let j = idna_l1((c >> 12u32) as int) as int + ((c >> 6u32) & 63) as int;
        let i = idna_l2(j) as int + (c & 63) as int;
        if j < IDNA_L2_LEN && i < IDNA_DATA_LEN {
            idna_data(i)
        } else {
            OUT_OF_RANGE_WORD
        }
    } else {
        OUT_OF_RANGE_WORD
    }
}

pub open spec fn status(c: u32) -> u32 {
    iword(c) & 7
}

pub open spec fn is_mark(c: u32) -> bool {
    iword(c) & 8 != 0
}

pub open spec fn bidi(c: u32) -> u32 {
    (iword(c) >> 4u32) & 15
}

pub open spec fn joining(c: u32) -> u32 {
    (iword(c) >> 8u32) & 7
}

pub open spec fn map_len(c: u32) -> int {
    ((iword(c) >> 11u32) & 31) as int
}

pub open spec fn map_off(c: u32) -> int {
    (iword(c) >> 16u32) as int
}

/// The mapping of a mapped or deviation code point.
pub open spec fn mapping(c: u32) -> Seq<u32> {
    Seq::new(map_len(c) as nat, |k: int| idna_pool(map_off(c) + k))
}

// ---------------------------------------------------------------------------
// Axioms
// ---------------------------------------------------------------------------

/// The trie's blocks are in bounds.
pub axiom fn axiom_idna_trie(i: int, j: int)
    requires
        0 <= i < IDNA_L1_LEN,
        0 <= j < IDNA_L2_LEN,
    ensures
        idna_l1(i) + 64 <= IDNA_L2_LEN,
        idna_l2(j) + 64 <= IDNA_DATA_LEN;

/// Mappings are in the pool, and are scalars.
pub axiom fn axiom_idna_mapping(c: u32)
    ensures
        map_off(c) + map_len(c) <= IDNA_POOL_LEN,
        forall|k: int| 0 <= k < map_len(c) ==> is_scalar(#[trigger] idna_pool(map_off(c) + k));

/// ASCII: capital letters map to small ones, everything else is valid, and
/// nothing is a mark or right-to-left.
pub axiom fn axiom_idna_ascii(c: u32)
    requires
        c < 0x80,
    ensures
        0x41 <= c <= 0x5A ==> status(c) == STATUS_MAPPED && mapping(c) == seq![(c + 0x20) as u32],
        !(0x41 <= c <= 0x5A) ==> status(c) == STATUS_VALID,
        !is_mark(c),
        bidi(c) != BIDI_R && bidi(c) != BIDI_AL && bidi(c) != BIDI_AN,
        joining(c) == JT_U;

// ---------------------------------------------------------------------------
// Implementation
// ---------------------------------------------------------------------------

/// The trie word of `c` (see `tables`).
///
/// ```text
/// ensures  r == iword(c)
/// ```
pub fn iword_of(c: u32) -> (r: u32)
    ensures
        r == iword(c),
{
    if c <= 0x10FFFF {
        assert(c <= 0x10FFFF ==> (c >> 12u32) < 272) by (bit_vector);
        assert(((c >> 6u32) & 63) < 64 && (c & 63) < 64) by (bit_vector);
        let a = (c >> 12) as usize;
        let b = ((c >> 6) & 63) as usize;
        proof {
            axiom_idna_trie(a as int, 0);
        }
        let j = idna_l1_at(a) as usize + b;
        proof {
            axiom_idna_trie(a as int, j as int);
        }
        idna_data_at(idna_l2_at(j) as usize + (c & 63) as usize)
    } else {
        OUT_OF_RANGE_WORD
    }
}

/// Appends `mapping(c)`, `w` being `c`'s word.
pub fn push_mapping(out: &mut Vec<u32>, c: u32, w: u32)
    requires
        w == iword(c),
    ensures
        final(out)@ == old(out)@ + mapping(c),
{
    proof {
        axiom_idna_mapping(c);
    }
    let off = (w >> 16) as usize;
    let len = ((w >> 11) & 31) as usize;
    let mut k = 0;
    while k < len
        invariant
            k <= len == map_len(c),
            off == map_off(c),
            off + len <= IDNA_POOL_LEN,
            out@ == old(out)@ + mapping(c).take(k as int),
        decreases len - k,
    {
        out.push(idna_pool_at(off + k));
        proof {
            assert(out@ =~= old(out)@ + mapping(c).take(k + 1));
        }
        k += 1;
    }
    proof {
        assert(mapping(c).take(len as int) =~= mapping(c));
    }
}

} // verus!
