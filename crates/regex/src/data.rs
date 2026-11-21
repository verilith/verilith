//! The Unicode data the syntax is defined over: the generated tables seen
//! as uninterpreted functions, and the sets of code points built from them.
//!
//! Trusted here: each `*_at` accessor returns its table's entry (each is
//! one bounds-checked array read).
use crate::tables::{FOLD_A, FOLD_B, GROUP_HI, GROUP_LO, GROUP_NAMES, GROUP_NAME_OFF, GROUP_OFF};
use vstd::prelude::*;

const _: () = assert!(GROUP_LO.len() == NRANGES && GROUP_HI.len() == NRANGES);
const _: () = assert!(FOLD_A.len() == NFOLD && FOLD_B.len() == NFOLD);
const _: () = assert!(GROUP_NAMES.len() == NNAMEBYTES);
const _: () = assert!(GROUP_OFF.len() == NOFF && GROUP_NAME_OFF.len() == NOFF && NGROUPS + 1 == NOFF);
const _: () = assert!(NGROUPS == crate::tables::NGROUPS);

verus! {

/// Unicode groups in the tables.
pub const NGROUPS: usize = 199;

/// The largest code point.
pub const MAXCP: u32 = 0x10FFFF;

/// Ranges in `GROUP_LO`/`GROUP_HI`.
pub const NRANGES: usize = 5820;

/// Pairs in `FOLD_A`/`FOLD_B`.
pub const NFOLD: usize = 2980;

/// Bytes in `GROUP_NAMES`.
pub const NNAMEBYTES: usize = 1450;

/// Entries in `GROUP_OFF` and `GROUP_NAME_OFF`: one more than `NGROUPS`.
pub const NOFF: usize = 200;

pub uninterp spec fn group_off(g: int) -> u32;

pub uninterp spec fn group_lo(i: int) -> u32;

pub uninterp spec fn group_hi(i: int) -> u32;

pub uninterp spec fn fold_a(k: int) -> u32;

pub uninterp spec fn fold_b(k: int) -> u32;

pub uninterp spec fn name_off(g: int) -> u32;

pub uninterp spec fn name_byte(i: int) -> u8;

macro_rules! accessor {
    ($name:ident, $table:ident, $len:ident, $spec:ident, $ty:ty) => {
        verus! {
            #[verifier::external_body]
            #[inline(always)]
            pub fn $name(i: usize) -> (r: $ty)
                requires
                    i < $len,
                ensures
                    r == $spec(i as int),
            {
                $table[i]
            }
        }
    };
}

accessor!(group_off_at, GROUP_OFF, NOFF, group_off, u32);
accessor!(group_lo_at, GROUP_LO, NRANGES, group_lo, u32);
accessor!(group_hi_at, GROUP_HI, NRANGES, group_hi, u32);
accessor!(fold_a_at, FOLD_A, NFOLD, fold_a, u32);
accessor!(fold_b_at, FOLD_B, NFOLD, fold_b, u32);
accessor!(name_off_at, GROUP_NAME_OFF, NOFF, name_off, u32);
accessor!(name_byte_at, GROUP_NAMES, NNAMEBYTES, name_byte, u8);

// ---------------------------------------------------------------------------
// Sets of code points
// ---------------------------------------------------------------------------

/// The code points `lo..=hi`.
pub open spec fn cs_range(lo: u32, hi: u32) -> ISet<u32> {
    ISet::new(|c: u32| lo <= c <= hi)
}

/// The code points in any of the ranges `rs`.
pub open spec fn cs_ranges(rs: Seq<(u32, u32)>) -> ISet<u32> {
    ISet::new(|c: u32| exists|k: int| 0 <= k < rs.len() && (#[trigger] rs[k]).0 <= c <= rs[k].1)
}

pub open spec fn cs_union(a: ISet<u32>, b: ISet<u32>) -> ISet<u32> {
    ISet::new(|c: u32| a.contains(c) || b.contains(c))
}

/// The code points not in `a`.
pub open spec fn cs_neg(a: ISet<u32>) -> ISet<u32> {
    ISet::new(|c: u32| c <= MAXCP && !a.contains(c))
}

/// Whether pair `k` of the folding table adds `c` to a set holding the
/// pair's first code point.
pub open spec fn folds_to(a: ISet<u32>, k: int, c: u32) -> bool {
    0 <= k < NFOLD && a.contains(fold_a(k)) && fold_b(k) == c
}

/// `a` with every code point that has the same simple case folding as one
/// of its members. (The table holds every ordered pair of distinct code
/// points with the same folding.)
pub open spec fn cs_fold(a: ISet<u32>) -> ISet<u32> {
    ISet::new(|c: u32| a.contains(c) || (c <= MAXCP && exists|k: int| #[trigger] folds_to(a, k, c)))
}

/// Whether range `i` of the group table belongs to group `g` and holds `c`.
pub open spec fn in_group_range(g: int, i: int, c: u32) -> bool {
    group_off(g) <= i < group_off(g + 1) && i < NRANGES && group_lo(i) <= c <= group_hi(i) && group_hi(i) <= MAXCP
}

/// Unicode group `g` of the table: a general category or a script.
pub open spec fn cs_group(g: int) -> ISet<u32> {
    ISet::new(|c: u32| exists|i: int| #[trigger] in_group_range(g, i, c))
}

/// The name of group `g`.
pub open spec fn group_name(g: int) -> Seq<u8> {
    Seq::new((name_off(g + 1) - name_off(g)) as nat, |k: int| name_byte(name_off(g) + k))
}

/// Whether group `g` exists and is named `name`.
pub open spec fn group_is(g: int, name: Seq<u8>) -> bool {
    0 <= g < NGROUPS && name_off(g) <= name_off(g + 1) <= NNAMEBYTES && group_name(g) == name
}

/// The first group at or after `g` named `name`.
pub open spec fn find_group_from(name: Seq<u8>, g: int) -> Option<int>
    decreases NGROUPS - g,
{
    if g < 0 || g >= NGROUPS {
        None
    } else if group_is(g, name) {
        Some(g)
    } else {
        find_group_from(name, g + 1)
    }
}

} // verus!
