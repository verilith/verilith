//! The sequences section and compressed blocks (RFC 8878 §3.1.1.3.2,
//! §3.1.1.4).
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
use crate::fse::*;
use crate::huf::*;
use crate::prims::{at, row};
use crate::work::Meter;
use verilith_core::tail::Tail;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The most output a decode may be asked to produce, and the input sizes
/// the decoders are proven for: 256 TiB on 64-bit targets, and on 32-bit
/// ones 2 GiB, above the largest slice there (`isize::MAX` bytes), so that
/// a length plus a block or a window still fits a `usize`.
#[cfg(target_pointer_width = "64")]
pub const MAX_LIMIT: usize = 0x1_0000_0000_0000;

#[cfg(target_pointer_width = "32")]
pub const MAX_LIMIT: usize = 0x8000_0000;

// ---------------------------------------------------------------------------
// Code tables
// ---------------------------------------------------------------------------

/// Literals length baselines.
exec static LL_BASE: [u32; 36]
    ensures
        forall|k: int| 0 <= k < 36 ==> (#[trigger] LL_BASE@[k]) as nat == ll_base(k as nat) && LL_BASE@[k] <= 65536,
{
    let r: [u32; 36] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536];
    proof {
        assert(ll_base(0) == 0nat) by (compute_only);
        assert(ll_base(1) == 1nat) by (compute_only);
        assert(ll_base(2) == 2nat) by (compute_only);
        assert(ll_base(3) == 3nat) by (compute_only);
        assert(ll_base(4) == 4nat) by (compute_only);
        assert(ll_base(5) == 5nat) by (compute_only);
        assert(ll_base(6) == 6nat) by (compute_only);
        assert(ll_base(7) == 7nat) by (compute_only);
        assert(ll_base(8) == 8nat) by (compute_only);
        assert(ll_base(9) == 9nat) by (compute_only);
        assert(ll_base(10) == 10nat) by (compute_only);
        assert(ll_base(11) == 11nat) by (compute_only);
        assert(ll_base(12) == 12nat) by (compute_only);
        assert(ll_base(13) == 13nat) by (compute_only);
        assert(ll_base(14) == 14nat) by (compute_only);
        assert(ll_base(15) == 15nat) by (compute_only);
        assert(ll_base(16) == 16nat) by (compute_only);
        assert(ll_base(17) == 18nat) by (compute_only);
        assert(ll_base(18) == 20nat) by (compute_only);
        assert(ll_base(19) == 22nat) by (compute_only);
        assert(ll_base(20) == 24nat) by (compute_only);
        assert(ll_base(21) == 28nat) by (compute_only);
        assert(ll_base(22) == 32nat) by (compute_only);
        assert(ll_base(23) == 40nat) by (compute_only);
        assert(ll_base(24) == 48nat) by (compute_only);
        assert(ll_base(25) == 64nat) by (compute_only);
        assert(ll_base(26) == 128nat) by (compute_only);
        assert(ll_base(27) == 256nat) by (compute_only);
        assert(ll_base(28) == 512nat) by (compute_only);
        assert(ll_base(29) == 1024nat) by (compute_only);
        assert(ll_base(30) == 2048nat) by (compute_only);
        assert(ll_base(31) == 4096nat) by (compute_only);
        assert(ll_base(32) == 8192nat) by (compute_only);
        assert(ll_base(33) == 16384nat) by (compute_only);
        assert(ll_base(34) == 32768nat) by (compute_only);
        assert(ll_base(35) == 65536nat) by (compute_only);
        assert(forall|k: int| 0 <= k < 36 ==> r@[k] as nat == ll_base(k as nat) && r@[k] <= 65536) by {
            assert forall|k: int| 0 <= k < 36 implies r@[k] as nat == ll_base(k as nat) && r@[k] <= 65536 by {
                if k == 0 { assert(r@[0] == 0u32); }
                if k == 1 { assert(r@[1] == 1u32); }
                if k == 2 { assert(r@[2] == 2u32); }
                if k == 3 { assert(r@[3] == 3u32); }
                if k == 4 { assert(r@[4] == 4u32); }
                if k == 5 { assert(r@[5] == 5u32); }
                if k == 6 { assert(r@[6] == 6u32); }
                if k == 7 { assert(r@[7] == 7u32); }
                if k == 8 { assert(r@[8] == 8u32); }
                if k == 9 { assert(r@[9] == 9u32); }
                if k == 10 { assert(r@[10] == 10u32); }
                if k == 11 { assert(r@[11] == 11u32); }
                if k == 12 { assert(r@[12] == 12u32); }
                if k == 13 { assert(r@[13] == 13u32); }
                if k == 14 { assert(r@[14] == 14u32); }
                if k == 15 { assert(r@[15] == 15u32); }
                if k == 16 { assert(r@[16] == 16u32); }
                if k == 17 { assert(r@[17] == 18u32); }
                if k == 18 { assert(r@[18] == 20u32); }
                if k == 19 { assert(r@[19] == 22u32); }
                if k == 20 { assert(r@[20] == 24u32); }
                if k == 21 { assert(r@[21] == 28u32); }
                if k == 22 { assert(r@[22] == 32u32); }
                if k == 23 { assert(r@[23] == 40u32); }
                if k == 24 { assert(r@[24] == 48u32); }
                if k == 25 { assert(r@[25] == 64u32); }
                if k == 26 { assert(r@[26] == 128u32); }
                if k == 27 { assert(r@[27] == 256u32); }
                if k == 28 { assert(r@[28] == 512u32); }
                if k == 29 { assert(r@[29] == 1024u32); }
                if k == 30 { assert(r@[30] == 2048u32); }
                if k == 31 { assert(r@[31] == 4096u32); }
                if k == 32 { assert(r@[32] == 8192u32); }
                if k == 33 { assert(r@[33] == 16384u32); }
                if k == 34 { assert(r@[34] == 32768u32); }
                if k == 35 { assert(r@[35] == 65536u32); }
            }
        }
    }
    r
}

/// Literals length extra bits.
exec static LL_BITS: [u32; 36]
    ensures
        forall|k: int| 0 <= k < 36 ==> (#[trigger] LL_BITS@[k]) as nat == ll_bits(k as nat) && LL_BITS@[k] <= 16,
{
    let r: [u32; 36] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    proof {
        assert(ll_bits(0) == 0nat) by (compute_only);
        assert(ll_bits(1) == 0nat) by (compute_only);
        assert(ll_bits(2) == 0nat) by (compute_only);
        assert(ll_bits(3) == 0nat) by (compute_only);
        assert(ll_bits(4) == 0nat) by (compute_only);
        assert(ll_bits(5) == 0nat) by (compute_only);
        assert(ll_bits(6) == 0nat) by (compute_only);
        assert(ll_bits(7) == 0nat) by (compute_only);
        assert(ll_bits(8) == 0nat) by (compute_only);
        assert(ll_bits(9) == 0nat) by (compute_only);
        assert(ll_bits(10) == 0nat) by (compute_only);
        assert(ll_bits(11) == 0nat) by (compute_only);
        assert(ll_bits(12) == 0nat) by (compute_only);
        assert(ll_bits(13) == 0nat) by (compute_only);
        assert(ll_bits(14) == 0nat) by (compute_only);
        assert(ll_bits(15) == 0nat) by (compute_only);
        assert(ll_bits(16) == 1nat) by (compute_only);
        assert(ll_bits(17) == 1nat) by (compute_only);
        assert(ll_bits(18) == 1nat) by (compute_only);
        assert(ll_bits(19) == 1nat) by (compute_only);
        assert(ll_bits(20) == 2nat) by (compute_only);
        assert(ll_bits(21) == 2nat) by (compute_only);
        assert(ll_bits(22) == 3nat) by (compute_only);
        assert(ll_bits(23) == 3nat) by (compute_only);
        assert(ll_bits(24) == 4nat) by (compute_only);
        assert(ll_bits(25) == 6nat) by (compute_only);
        assert(ll_bits(26) == 7nat) by (compute_only);
        assert(ll_bits(27) == 8nat) by (compute_only);
        assert(ll_bits(28) == 9nat) by (compute_only);
        assert(ll_bits(29) == 10nat) by (compute_only);
        assert(ll_bits(30) == 11nat) by (compute_only);
        assert(ll_bits(31) == 12nat) by (compute_only);
        assert(ll_bits(32) == 13nat) by (compute_only);
        assert(ll_bits(33) == 14nat) by (compute_only);
        assert(ll_bits(34) == 15nat) by (compute_only);
        assert(ll_bits(35) == 16nat) by (compute_only);
        assert(forall|k: int| 0 <= k < 36 ==> r@[k] as nat == ll_bits(k as nat) && r@[k] <= 16) by {
            assert forall|k: int| 0 <= k < 36 implies r@[k] as nat == ll_bits(k as nat) && r@[k] <= 16 by {
                if k == 0 { assert(r@[0] == 0u32); }
                if k == 1 { assert(r@[1] == 0u32); }
                if k == 2 { assert(r@[2] == 0u32); }
                if k == 3 { assert(r@[3] == 0u32); }
                if k == 4 { assert(r@[4] == 0u32); }
                if k == 5 { assert(r@[5] == 0u32); }
                if k == 6 { assert(r@[6] == 0u32); }
                if k == 7 { assert(r@[7] == 0u32); }
                if k == 8 { assert(r@[8] == 0u32); }
                if k == 9 { assert(r@[9] == 0u32); }
                if k == 10 { assert(r@[10] == 0u32); }
                if k == 11 { assert(r@[11] == 0u32); }
                if k == 12 { assert(r@[12] == 0u32); }
                if k == 13 { assert(r@[13] == 0u32); }
                if k == 14 { assert(r@[14] == 0u32); }
                if k == 15 { assert(r@[15] == 0u32); }
                if k == 16 { assert(r@[16] == 1u32); }
                if k == 17 { assert(r@[17] == 1u32); }
                if k == 18 { assert(r@[18] == 1u32); }
                if k == 19 { assert(r@[19] == 1u32); }
                if k == 20 { assert(r@[20] == 2u32); }
                if k == 21 { assert(r@[21] == 2u32); }
                if k == 22 { assert(r@[22] == 3u32); }
                if k == 23 { assert(r@[23] == 3u32); }
                if k == 24 { assert(r@[24] == 4u32); }
                if k == 25 { assert(r@[25] == 6u32); }
                if k == 26 { assert(r@[26] == 7u32); }
                if k == 27 { assert(r@[27] == 8u32); }
                if k == 28 { assert(r@[28] == 9u32); }
                if k == 29 { assert(r@[29] == 10u32); }
                if k == 30 { assert(r@[30] == 11u32); }
                if k == 31 { assert(r@[31] == 12u32); }
                if k == 32 { assert(r@[32] == 13u32); }
                if k == 33 { assert(r@[33] == 14u32); }
                if k == 34 { assert(r@[34] == 15u32); }
                if k == 35 { assert(r@[35] == 16u32); }
            }
        }
    }
    r
}

/// Every match is at least three bytes long.
pub proof fn lemma_ml_base_min(c: nat)
    requires
        c < 53,
    ensures
        ml_base(c) >= 3,
{
    if c >= 32 {
        if c == 32 {
            assert(ml_base(32) == 35nat) by (compute_only);
        } else if c == 33 {
            assert(ml_base(33) == 37nat) by (compute_only);
        } else if c == 34 {
            assert(ml_base(34) == 39nat) by (compute_only);
        } else if c == 35 {
            assert(ml_base(35) == 41nat) by (compute_only);
        } else if c == 36 {
            assert(ml_base(36) == 43nat) by (compute_only);
        } else if c == 37 {
            assert(ml_base(37) == 47nat) by (compute_only);
        } else if c == 38 {
            assert(ml_base(38) == 51nat) by (compute_only);
        } else if c == 39 {
            assert(ml_base(39) == 59nat) by (compute_only);
        } else if c == 40 {
            assert(ml_base(40) == 67nat) by (compute_only);
        } else if c == 41 {
            assert(ml_base(41) == 83nat) by (compute_only);
        } else if c == 42 {
            assert(ml_base(42) == 99nat) by (compute_only);
        } else if c == 43 {
            assert(ml_base(43) == 131nat) by (compute_only);
        } else if c == 44 {
            assert(ml_base(44) == 259nat) by (compute_only);
        } else if c == 45 {
            assert(ml_base(45) == 515nat) by (compute_only);
        } else if c == 46 {
            assert(ml_base(46) == 1027nat) by (compute_only);
        } else if c == 47 {
            assert(ml_base(47) == 2051nat) by (compute_only);
        } else if c == 48 {
            assert(ml_base(48) == 4099nat) by (compute_only);
        } else if c == 49 {
            assert(ml_base(49) == 8195nat) by (compute_only);
        } else if c == 50 {
            assert(ml_base(50) == 16387nat) by (compute_only);
        } else if c == 51 {
            assert(ml_base(51) == 32771nat) by (compute_only);
        } else if c == 52 {
            assert(ml_base(52) == 65539nat) by (compute_only);
        }
    }
}

/// Match length baselines.
exec static ML_BASE: [u32; 53]
    ensures
        forall|k: int| 0 <= k < 53 ==> (#[trigger] ML_BASE@[k]) as nat == ml_base(k as nat) && ML_BASE@[k] <= 65539,
{
    let r: [u32; 53] = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099, 8195, 16387, 32771, 65539];
    proof {
        assert(ml_base(0) == 3nat) by (compute_only);
        assert(ml_base(1) == 4nat) by (compute_only);
        assert(ml_base(2) == 5nat) by (compute_only);
        assert(ml_base(3) == 6nat) by (compute_only);
        assert(ml_base(4) == 7nat) by (compute_only);
        assert(ml_base(5) == 8nat) by (compute_only);
        assert(ml_base(6) == 9nat) by (compute_only);
        assert(ml_base(7) == 10nat) by (compute_only);
        assert(ml_base(8) == 11nat) by (compute_only);
        assert(ml_base(9) == 12nat) by (compute_only);
        assert(ml_base(10) == 13nat) by (compute_only);
        assert(ml_base(11) == 14nat) by (compute_only);
        assert(ml_base(12) == 15nat) by (compute_only);
        assert(ml_base(13) == 16nat) by (compute_only);
        assert(ml_base(14) == 17nat) by (compute_only);
        assert(ml_base(15) == 18nat) by (compute_only);
        assert(ml_base(16) == 19nat) by (compute_only);
        assert(ml_base(17) == 20nat) by (compute_only);
        assert(ml_base(18) == 21nat) by (compute_only);
        assert(ml_base(19) == 22nat) by (compute_only);
        assert(ml_base(20) == 23nat) by (compute_only);
        assert(ml_base(21) == 24nat) by (compute_only);
        assert(ml_base(22) == 25nat) by (compute_only);
        assert(ml_base(23) == 26nat) by (compute_only);
        assert(ml_base(24) == 27nat) by (compute_only);
        assert(ml_base(25) == 28nat) by (compute_only);
        assert(ml_base(26) == 29nat) by (compute_only);
        assert(ml_base(27) == 30nat) by (compute_only);
        assert(ml_base(28) == 31nat) by (compute_only);
        assert(ml_base(29) == 32nat) by (compute_only);
        assert(ml_base(30) == 33nat) by (compute_only);
        assert(ml_base(31) == 34nat) by (compute_only);
        assert(ml_base(32) == 35nat) by (compute_only);
        assert(ml_base(33) == 37nat) by (compute_only);
        assert(ml_base(34) == 39nat) by (compute_only);
        assert(ml_base(35) == 41nat) by (compute_only);
        assert(ml_base(36) == 43nat) by (compute_only);
        assert(ml_base(37) == 47nat) by (compute_only);
        assert(ml_base(38) == 51nat) by (compute_only);
        assert(ml_base(39) == 59nat) by (compute_only);
        assert(ml_base(40) == 67nat) by (compute_only);
        assert(ml_base(41) == 83nat) by (compute_only);
        assert(ml_base(42) == 99nat) by (compute_only);
        assert(ml_base(43) == 131nat) by (compute_only);
        assert(ml_base(44) == 259nat) by (compute_only);
        assert(ml_base(45) == 515nat) by (compute_only);
        assert(ml_base(46) == 1027nat) by (compute_only);
        assert(ml_base(47) == 2051nat) by (compute_only);
        assert(ml_base(48) == 4099nat) by (compute_only);
        assert(ml_base(49) == 8195nat) by (compute_only);
        assert(ml_base(50) == 16387nat) by (compute_only);
        assert(ml_base(51) == 32771nat) by (compute_only);
        assert(ml_base(52) == 65539nat) by (compute_only);
        assert(forall|k: int| 0 <= k < 53 ==> r@[k] as nat == ml_base(k as nat) && r@[k] <= 65539) by {
            assert forall|k: int| 0 <= k < 53 implies r@[k] as nat == ml_base(k as nat) && r@[k] <= 65539 by {
                if k == 0 { assert(r@[0] == 3u32); }
                if k == 1 { assert(r@[1] == 4u32); }
                if k == 2 { assert(r@[2] == 5u32); }
                if k == 3 { assert(r@[3] == 6u32); }
                if k == 4 { assert(r@[4] == 7u32); }
                if k == 5 { assert(r@[5] == 8u32); }
                if k == 6 { assert(r@[6] == 9u32); }
                if k == 7 { assert(r@[7] == 10u32); }
                if k == 8 { assert(r@[8] == 11u32); }
                if k == 9 { assert(r@[9] == 12u32); }
                if k == 10 { assert(r@[10] == 13u32); }
                if k == 11 { assert(r@[11] == 14u32); }
                if k == 12 { assert(r@[12] == 15u32); }
                if k == 13 { assert(r@[13] == 16u32); }
                if k == 14 { assert(r@[14] == 17u32); }
                if k == 15 { assert(r@[15] == 18u32); }
                if k == 16 { assert(r@[16] == 19u32); }
                if k == 17 { assert(r@[17] == 20u32); }
                if k == 18 { assert(r@[18] == 21u32); }
                if k == 19 { assert(r@[19] == 22u32); }
                if k == 20 { assert(r@[20] == 23u32); }
                if k == 21 { assert(r@[21] == 24u32); }
                if k == 22 { assert(r@[22] == 25u32); }
                if k == 23 { assert(r@[23] == 26u32); }
                if k == 24 { assert(r@[24] == 27u32); }
                if k == 25 { assert(r@[25] == 28u32); }
                if k == 26 { assert(r@[26] == 29u32); }
                if k == 27 { assert(r@[27] == 30u32); }
                if k == 28 { assert(r@[28] == 31u32); }
                if k == 29 { assert(r@[29] == 32u32); }
                if k == 30 { assert(r@[30] == 33u32); }
                if k == 31 { assert(r@[31] == 34u32); }
                if k == 32 { assert(r@[32] == 35u32); }
                if k == 33 { assert(r@[33] == 37u32); }
                if k == 34 { assert(r@[34] == 39u32); }
                if k == 35 { assert(r@[35] == 41u32); }
                if k == 36 { assert(r@[36] == 43u32); }
                if k == 37 { assert(r@[37] == 47u32); }
                if k == 38 { assert(r@[38] == 51u32); }
                if k == 39 { assert(r@[39] == 59u32); }
                if k == 40 { assert(r@[40] == 67u32); }
                if k == 41 { assert(r@[41] == 83u32); }
                if k == 42 { assert(r@[42] == 99u32); }
                if k == 43 { assert(r@[43] == 131u32); }
                if k == 44 { assert(r@[44] == 259u32); }
                if k == 45 { assert(r@[45] == 515u32); }
                if k == 46 { assert(r@[46] == 1027u32); }
                if k == 47 { assert(r@[47] == 2051u32); }
                if k == 48 { assert(r@[48] == 4099u32); }
                if k == 49 { assert(r@[49] == 8195u32); }
                if k == 50 { assert(r@[50] == 16387u32); }
                if k == 51 { assert(r@[51] == 32771u32); }
                if k == 52 { assert(r@[52] == 65539u32); }
            }
        }
    }
    r
}

/// Match length extra bits.
exec static ML_BITS: [u32; 53]
    ensures
        forall|k: int| 0 <= k < 53 ==> (#[trigger] ML_BITS@[k]) as nat == ml_bits(k as nat) && ML_BITS@[k] <= 16,
{
    let r: [u32; 53] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    proof {
        assert(ml_bits(0) == 0nat) by (compute_only);
        assert(ml_bits(1) == 0nat) by (compute_only);
        assert(ml_bits(2) == 0nat) by (compute_only);
        assert(ml_bits(3) == 0nat) by (compute_only);
        assert(ml_bits(4) == 0nat) by (compute_only);
        assert(ml_bits(5) == 0nat) by (compute_only);
        assert(ml_bits(6) == 0nat) by (compute_only);
        assert(ml_bits(7) == 0nat) by (compute_only);
        assert(ml_bits(8) == 0nat) by (compute_only);
        assert(ml_bits(9) == 0nat) by (compute_only);
        assert(ml_bits(10) == 0nat) by (compute_only);
        assert(ml_bits(11) == 0nat) by (compute_only);
        assert(ml_bits(12) == 0nat) by (compute_only);
        assert(ml_bits(13) == 0nat) by (compute_only);
        assert(ml_bits(14) == 0nat) by (compute_only);
        assert(ml_bits(15) == 0nat) by (compute_only);
        assert(ml_bits(16) == 0nat) by (compute_only);
        assert(ml_bits(17) == 0nat) by (compute_only);
        assert(ml_bits(18) == 0nat) by (compute_only);
        assert(ml_bits(19) == 0nat) by (compute_only);
        assert(ml_bits(20) == 0nat) by (compute_only);
        assert(ml_bits(21) == 0nat) by (compute_only);
        assert(ml_bits(22) == 0nat) by (compute_only);
        assert(ml_bits(23) == 0nat) by (compute_only);
        assert(ml_bits(24) == 0nat) by (compute_only);
        assert(ml_bits(25) == 0nat) by (compute_only);
        assert(ml_bits(26) == 0nat) by (compute_only);
        assert(ml_bits(27) == 0nat) by (compute_only);
        assert(ml_bits(28) == 0nat) by (compute_only);
        assert(ml_bits(29) == 0nat) by (compute_only);
        assert(ml_bits(30) == 0nat) by (compute_only);
        assert(ml_bits(31) == 0nat) by (compute_only);
        assert(ml_bits(32) == 1nat) by (compute_only);
        assert(ml_bits(33) == 1nat) by (compute_only);
        assert(ml_bits(34) == 1nat) by (compute_only);
        assert(ml_bits(35) == 1nat) by (compute_only);
        assert(ml_bits(36) == 2nat) by (compute_only);
        assert(ml_bits(37) == 2nat) by (compute_only);
        assert(ml_bits(38) == 3nat) by (compute_only);
        assert(ml_bits(39) == 3nat) by (compute_only);
        assert(ml_bits(40) == 4nat) by (compute_only);
        assert(ml_bits(41) == 4nat) by (compute_only);
        assert(ml_bits(42) == 5nat) by (compute_only);
        assert(ml_bits(43) == 7nat) by (compute_only);
        assert(ml_bits(44) == 8nat) by (compute_only);
        assert(ml_bits(45) == 9nat) by (compute_only);
        assert(ml_bits(46) == 10nat) by (compute_only);
        assert(ml_bits(47) == 11nat) by (compute_only);
        assert(ml_bits(48) == 12nat) by (compute_only);
        assert(ml_bits(49) == 13nat) by (compute_only);
        assert(ml_bits(50) == 14nat) by (compute_only);
        assert(ml_bits(51) == 15nat) by (compute_only);
        assert(ml_bits(52) == 16nat) by (compute_only);
        assert(forall|k: int| 0 <= k < 53 ==> r@[k] as nat == ml_bits(k as nat) && r@[k] <= 16) by {
            assert forall|k: int| 0 <= k < 53 implies r@[k] as nat == ml_bits(k as nat) && r@[k] <= 16 by {
                if k == 0 { assert(r@[0] == 0u32); }
                if k == 1 { assert(r@[1] == 0u32); }
                if k == 2 { assert(r@[2] == 0u32); }
                if k == 3 { assert(r@[3] == 0u32); }
                if k == 4 { assert(r@[4] == 0u32); }
                if k == 5 { assert(r@[5] == 0u32); }
                if k == 6 { assert(r@[6] == 0u32); }
                if k == 7 { assert(r@[7] == 0u32); }
                if k == 8 { assert(r@[8] == 0u32); }
                if k == 9 { assert(r@[9] == 0u32); }
                if k == 10 { assert(r@[10] == 0u32); }
                if k == 11 { assert(r@[11] == 0u32); }
                if k == 12 { assert(r@[12] == 0u32); }
                if k == 13 { assert(r@[13] == 0u32); }
                if k == 14 { assert(r@[14] == 0u32); }
                if k == 15 { assert(r@[15] == 0u32); }
                if k == 16 { assert(r@[16] == 0u32); }
                if k == 17 { assert(r@[17] == 0u32); }
                if k == 18 { assert(r@[18] == 0u32); }
                if k == 19 { assert(r@[19] == 0u32); }
                if k == 20 { assert(r@[20] == 0u32); }
                if k == 21 { assert(r@[21] == 0u32); }
                if k == 22 { assert(r@[22] == 0u32); }
                if k == 23 { assert(r@[23] == 0u32); }
                if k == 24 { assert(r@[24] == 0u32); }
                if k == 25 { assert(r@[25] == 0u32); }
                if k == 26 { assert(r@[26] == 0u32); }
                if k == 27 { assert(r@[27] == 0u32); }
                if k == 28 { assert(r@[28] == 0u32); }
                if k == 29 { assert(r@[29] == 0u32); }
                if k == 30 { assert(r@[30] == 0u32); }
                if k == 31 { assert(r@[31] == 0u32); }
                if k == 32 { assert(r@[32] == 1u32); }
                if k == 33 { assert(r@[33] == 1u32); }
                if k == 34 { assert(r@[34] == 1u32); }
                if k == 35 { assert(r@[35] == 1u32); }
                if k == 36 { assert(r@[36] == 2u32); }
                if k == 37 { assert(r@[37] == 2u32); }
                if k == 38 { assert(r@[38] == 3u32); }
                if k == 39 { assert(r@[39] == 3u32); }
                if k == 40 { assert(r@[40] == 4u32); }
                if k == 41 { assert(r@[41] == 4u32); }
                if k == 42 { assert(r@[42] == 5u32); }
                if k == 43 { assert(r@[43] == 7u32); }
                if k == 44 { assert(r@[44] == 8u32); }
                if k == 45 { assert(r@[45] == 9u32); }
                if k == 46 { assert(r@[46] == 10u32); }
                if k == 47 { assert(r@[47] == 11u32); }
                if k == 48 { assert(r@[48] == 12u32); }
                if k == 49 { assert(r@[49] == 13u32); }
                if k == 50 { assert(r@[50] == 14u32); }
                if k == 51 { assert(r@[51] == 15u32); }
                if k == 52 { assert(r@[52] == 16u32); }
            }
        }
    }
    r
}

/// Baseline and extra bits of a literals length code.
#[inline(always)]
pub fn ll_code(c: u8) -> (r: (u32, u32))
    requires
        c <= 35,
    ensures
        r.0 as nat == ll_base(c as nat),
        r.1 as nat == ll_bits(c as nat),
        r.0 <= 65536,
        r.1 <= 16,
{
    (at(&LL_BASE, c as usize), at(&LL_BITS, c as usize))
}

/// Baseline and extra bits of a match length code.
#[inline(always)]
pub fn ml_code(c: u8) -> (r: (u32, u32))
    requires
        c <= 52,
    ensures
        r.0 as nat == ml_base(c as nat),
        r.1 as nat == ml_bits(c as nat),
        r.0 <= 65539,
        r.1 <= 16,
{
    (at(&ML_BASE, c as usize), at(&ML_BITS, c as usize))
}

/// A table row with its code's baseline and number of extra bits looked
/// up: what the fast sequence loop reads.
#[derive(Clone, Copy)]
pub struct SeqE {
    pub base: u32,
    pub xb: u8,
    pub nb: u8,
    pub next: u16,
}

/// The baseline of code `c` of kind `k` (0: literals length, 1: offset,
/// 2: match length).
pub open spec fn kind_base(k: nat, c: nat) -> nat {
    if k == 0 {
        ll_base(c)
    } else if k == 1 {
        pow2(c)
    } else {
        ml_base(c)
    }
}

/// The number of extra bits of code `c` of kind `k`.
pub open spec fn kind_bits(k: nat, c: nat) -> nat {
    if k == 0 {
        ll_bits(c)
    } else if k == 1 {
        c
    } else {
        ml_bits(c)
    }
}

/// `d` is `rows` with each symbol's baseline and extra bits looked up.
pub open spec fn baked(d: Seq<SeqE>, rows: Seq<FseRow>, k: nat) -> bool {
    &&& d.len() == rows.len()
    &&& forall|u: int|
        #![trigger d[u]]
        0 <= u < d.len() ==> {
            &&& d[u].base as nat == kind_base(k, rows[u].sym as nat)
            &&& d[u].xb as nat == kind_bits(k, rows[u].sym as nat)
            &&& d[u].nb == rows[u].nb
            &&& d[u].next == rows[u].base
            &&& d[u].xb <= (if k == 1 { 31u8 } else { 16u8 })
            &&& k != 1 ==> d[u].base <= 65539
        }
}

/// Looks up each row's baseline and extra bits (`baked`).
pub fn bake(t: &FseTab, k: u8, Tracked(m): Tracked<&mut Meter>) -> (d: Vec<SeqE>)
    requires
        k <= 2,
        tab_wf(t, kind_nsym(k as nat)),
    ensures
        baked(d@, t.rows@, k as nat),
        final(m).n == old(m).n + t.rows@.len(),
{
    // One copy of the loop per kind, so the kind is not tested per row.
    if k == 0 {
        bake_kind(t, 0, Tracked(m))
    } else if k == 1 {
        bake_kind(t, 1, Tracked(m))
    } else {
        bake_kind(t, 2, Tracked(m))
    }
}

#[inline(always)]
fn bake_kind(t: &FseTab, k: u8, Tracked(m): Tracked<&mut Meter>) -> (d: Vec<SeqE>)
    requires
        k <= 2,
        tab_wf(t, kind_nsym(k as nat)),
    ensures
        baked(d@, t.rows@, k as nat),
        final(m).n == old(m).n + t.rows@.len(),
{
    let n = t.rows.len();
    let mut d: Vec<SeqE> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            k <= 2,
            tab_wf(t, kind_nsym(k as nat)),
            n == t.rows@.len(),
            i <= n,
            d@.len() == i,
            forall|u: int|
                #![trigger d@[u]]
                0 <= u < i ==> {
                    &&& d@[u].base as nat == kind_base(k as nat, t.rows@[u].sym as nat)
                    &&& d@[u].xb as nat == kind_bits(k as nat, t.rows@[u].sym as nat)
                    &&& d@[u].nb == t.rows@[u].nb
                    &&& d@[u].next == t.rows@[u].base
                    &&& d@[u].xb <= (if k == 1 { 31u8 } else { 16u8 })
                    &&& k != 1 ==> d@[u].base <= 65539
                },
            m.n == old(m).n + i,
        decreases n - i,
    {
        proof {
            m.n = m.n + 1;
        }
        let r = t.rows[i];
        proof {
            assert((t.rows@[i as int].sym as nat) < kind_nsym(k as nat));
        }
        let e = if k == 0 {
            let (b, x) = ll_code(r.sym);
            SeqE { base: b, xb: x as u8, nb: r.nb, next: r.base }
        } else if k == 1 {
            proof {
                lemma_u64_pow2_no_overflow(r.sym as nat);
                lemma_u64_shl_is_mul(1, r.sym as u64);
                lemma_pow2_le(r.sym as nat, 31);
                assert(pow2(31) == 0x8000_0000) by {
                    lemma2_to64();
                }
            }
            SeqE { base: (1u64 << r.sym as u64) as u32, xb: r.sym, nb: r.nb, next: r.base }
        } else {
            let (b, x) = ml_code(r.sym);
            SeqE { base: b, xb: x as u8, nb: r.nb, next: r.base }
        };
        d.push(e);
        i = i + 1;
    }
    d
}

/// The three tables of a block, and the same with baselines and extra
/// bits looked up.
pub struct SeqTabs {
    pub ll: FseTab,
    pub of: FseTab,
    pub ml: FseTab,
    pub dl: Vec<SeqE>,
    pub dof: Vec<SeqE>,
    pub dml: Vec<SeqE>,
}

pub open spec fn seqtabs_is(t: &SeqTabs, s: SeqTables) -> bool {
    &&& tab_is(&t.ll, s.ll)
    &&& tab_is(&t.of, s.of)
    &&& tab_is(&t.ml, s.ml)
    &&& tab_wf(&t.ll, 36)
    &&& tab_wf(&t.of, 32)
    &&& tab_wf(&t.ml, 53)
    &&& baked(t.dl@, t.ll.rows@, 0)
    &&& baked(t.dof@, t.of.rows@, 1)
    &&& baked(t.dml@, t.ml.rows@, 2)
}

pub open spec fn kind_nsym(k: nat) -> nat {
    kind_maxsv(k) + 1
}

/// A predefined table.
pub fn default_tab(k: u8, Tracked(wm): Tracked<&mut Meter>) -> (r: FseTab)
    requires
        k <= 2,
    ensures
        tab_is(&r, kind_default(k as nat)),
        tab_wf(&r, kind_nsym(k as nat)),
        final(wm).n <= old(wm).n + 351,
{
    proof {
        lemma2_to64();
    }
    if k == 0 {
        let a: [i16; 36] = [
            4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
            -1, -1, -1, -1,
        ];
        proof {
            assert(iseq(a@) =~= ll_default());
            assert(psum(ll_default(), 36) == 64) by (compute_only);
        }
        build_table(&a, 6, Tracked(wm))
    } else if k == 1 {
        let a: [i16; 29] = [
            1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1,
        ];
        proof {
            assert(iseq(a@) =~= of_default());
            assert(psum(of_default(), 29) == 32) by (compute_only);
        }
        let t = build_table(&a, 5, Tracked(wm));
        t
    } else {
        let a: [i16; 53] = [
            1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
            1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1,
        ];
        proof {
            assert(iseq(a@) =~= ml_default());
            assert(psum(ml_default(), 53) == 64) by (compute_only);
        }
        build_table(&a, 6, Tracked(wm))
    }
}

/// One table of the sequences header (`seq_table`).
pub fn seq_table_exec(b: &[u8], k: u8, mode: u8, prev: Option<&FseTab>, Ghost(gprev): Ghost<Option<FseTable>>, Tracked(m): Tracked<&mut Meter>) -> (r:
    Option<(FseTab, usize)>)
    requires
        k <= 2,
        mode <= 3,
        b@.len() < BITS_MAX,
        match prev {
            None => gprev is None,
            Some(t) => gprev is Some && tab_is(t, gprev.unwrap()) && tab_wf(t, kind_nsym(k as nat)),
        },
    ensures
        match seq_table(b@, k as nat, mode as nat, gprev) {
            None => r is None,
            Some((t, used)) => {
                &&& r is Some
                &&& tab_is(&r.unwrap().0, t)
                &&& tab_wf(&r.unwrap().0, kind_nsym(k as nat))
                &&& r.unwrap().1 as int == used
                &&& used <= b@.len()
            },
        },
        final(m).n <= old(m).n + 8 * b@.len() + 1870,
{
    proof {
        lemma2_to64();
    }
    let maxsv: u32 = if k == 0 {
        35
    } else if k == 1 {
        31
    } else {
        52
    };
    if mode == 0 {
        Some((default_tab(k, Tracked(m)), 0))
    } else if mode == 1 {
        if b.len() < 1 || b[0] as u32 > maxsv {
            return None;
        }
        Some((rle_tab(b[0]), 1))
    } else if mode == 2 {
        let maxlog: u32 = if k == 1 {
            8
        } else {
            9
        };
        match read_ncount(b, maxsv, maxlog, Tracked(m)) {
            None => None,
            Some((log, norm, used)) => {
                proof {
                    lemma_pow2_le(log as nat, 9);
                }
                Some((build_table(norm.as_slice(), log, Tracked(m)), used))
            },
        }
    } else {
        match prev {
            None => None,
            Some(t) => {
                proof {
                    lemma_pow2_le(t.log as nat, 9);
                }
                Some((t.clone_tab(Tracked(m)), 0))
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Decoding and executing sequences
// ---------------------------------------------------------------------------

/// The repeat offsets resolved for one sequence (`resolve_offset`).
#[inline(always)]
pub fn resolve_offset_exec(ov: u64, ll0: bool, r1: u64, r2: u64, r3: u64) -> (r: Option<(u64, u64, u64, u64)>)
    requires
        ov < 0x1_0000_0000,
    ensures
        match resolve_offset(ov as nat, ll0, Reps { r1: r1 as nat, r2: r2 as nat, r3: r3 as nat }) {
            None => r is None,
            Some((off, reps)) => {
                &&& r is Some
                &&& r.unwrap().0 as nat == off
                &&& r.unwrap().1 as nat == reps.r1
                &&& r.unwrap().2 as nat == reps.r2
                &&& r.unwrap().3 as nat == reps.r3
            },
        },
{
    if ov > 3 {
        let off = ov - 3;
        Some((off, off, r1, r2))
    } else {
        let idx = if ll0 {
            ov + 1
        } else {
            ov
        };
        if idx == 1 {
            Some((r1, r1, r2, r3))
        } else if idx == 2 {
            Some((r2, r2, r1, r3))
        } else if idx == 3 {
            Some((r3, r3, r1, r2))
        } else if r1 <= 1 {
            None
        } else {
            let off = r1 - 1;
            Some((off, off, r1, r2))
        }
    }
}

/// `copy_match` makes the output `len` bytes longer.
pub proof fn lemma_copy_match_len(out: Seq<u8>, dist: nat, len: nat)
    ensures
        copy_match(out, dist, len).len() == out.len() + len,
    decreases len,
{
    if len > 0 {
        lemma_copy_match_len(out.push(out[out.len() - dist]), dist, (len - 1) as nat);
    }
}

/// `copy_match` only appends.
pub proof fn lemma_copy_match_prefix(out: Seq<u8>, dist: nat, len: nat)
    ensures
        copy_match(out, dist, len).subrange(0, out.len() as int) == out,
    decreases len,
{
    if len > 0 {
        let o1 = out.push(out[out.len() - dist]);
        lemma_copy_match_prefix(o1, dist, (len - 1) as nat);
        lemma_copy_match_len(o1, dist, (len - 1) as nat);
        assert(copy_match(out, dist, len).subrange(0, out.len() as int) =~= copy_match(o1, dist, (len - 1) as nat).subrange(
            0,
            o1.len() as int,
        ).subrange(0, out.len() as int));
        assert(o1.subrange(0, out.len() as int) =~= out);
    } else {
        assert(out.subrange(0, out.len() as int) =~= out);
    }
}

/// `copy_match` repeats the last `dist` bytes.
pub proof fn lemma_copy_match_periodic(o: Seq<u8>, dist: nat, len: nat)
    requires
        1 <= dist <= o.len(),
    ensures
        copy_match(o, dist, len) == o + Seq::new(len, |j: int| o[o.len() - dist + j % (dist as int)]),
    decreases len,
{
    let p = |k: nat| Seq::new(k, |j: int| o[o.len() - dist + j % (dist as int)]);
    if len == 0 {
        assert(o + p(0) =~= o);
    } else {
        // copy_match(o, d, len) = copy_match(o, d, len - 1) pushed with one more byte.
        lemma_copy_match_snoc(o, dist, (len - 1) as nat);
        lemma_copy_match_periodic(o, dist, (len - 1) as nat);
        let q = o + p((len - 1) as nat);
        let k = (len - 1) as int;
        let d = dist as int;
        // q[q.len() - d] is the periodic byte number k.
        assert(q[q.len() - d] == o[o.len() - d + k % d]) by {
            if k >= d {
                vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(k, d);
                assert((k - d) % d == k % d) by {
                    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(k - d, d);
                }
                assert(q[q.len() - d] == p((len - 1) as nat)[k - d]);
            } else {
                vstd::arithmetic::div_mod::lemma_small_mod(k as nat, d as nat);
                assert(q[q.len() - d] == o[o.len() - d + k]);
            }
        }
        assert(q.push(q[q.len() - d]) =~= o + p(len));
    }
}

/// `copy_match` one byte further.
pub proof fn lemma_copy_match_snoc(o: Seq<u8>, dist: nat, len: nat)
    requires
        1 <= dist <= o.len(),
    ensures
        copy_match(o, dist, len + 1) == copy_match(o, dist, len).push(
            copy_match(o, dist, len)[copy_match(o, dist, len).len() - dist],
        ),
    decreases len,
{
    if len > 0 {
        lemma_copy_match_snoc(o.push(o[o.len() - dist]), dist, (len - 1) as nat);
    } else {
        reveal_with_fuel(copy_match, 2);
    }
}

proof fn lemma_mod_period(x: int, y: int, k: int, d: int)
    requires
        d > 0,
        x == y + k * d,
    ensures
        x % d == y % d,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(k, y, d);
    vstd::arithmetic::mul::lemma_mul_is_commutative(k, d);
}

/// The first `k` bytes of repeating the last `d` bytes of `o`.
pub open spec fn per_seq(o: Seq<u8>, d: int, k: nat) -> Seq<u8> {
    Seq::new(k, |j: int| o[o.len() - d + j % d])
}

/// Appends a match of `len` bytes from `off` back (`copy_match`): one
/// copy when it does not overlap what it copies.
#[inline(always)]
fn copy_match_exec(out: &mut Tail, fstart: usize, off: usize, len: usize, Tracked(m): Tracked<&mut Meter>)
    requires
        fstart <= old(out)@.len(),
        1 <= off <= old(out)@.len() - fstart,
        old(out)@.len() + len + 32 <= old(out).cap(),
    ensures
        final(out).cap() == old(out).cap(),
        final(m).n <= old(m).n + 2 * len,
        final(out)@ == old(out)@.subrange(0, fstart as int) + copy_match(
            old(out)@.subrange(fstart as int, old(out)@.len() as int),
            off as nat,
            len as nat,
        ),
{
    if len <= off {
        let ghost pre = out@.subrange(0, fstart as int);
        let ghost o0 = out@.subrange(fstart as int, out@.len() as int);
        let ghost all0 = out@;
        let ghost d = off as int;
        proof {
            lemma_copy_match_periodic(o0, off as nat, len as nat);
        }
        let start = out.len() - off;
        out.append_within(start, len);
        proof {
            assert forall|j: int| 0 <= j < len implies #[trigger] per_seq(o0, d, len as nat)[j] == all0[start + j] by {
                vstd::arithmetic::div_mod::lemma_small_mod(j as nat, d as nat);
            }
            assert(out@ =~= all0 + per_seq(o0, d, len as nat));
            assert(out@ =~= pre + copy_match(o0, off as nat, len as nat));
            m.n = (m.n + len) as nat;
        }
    } else {
        copy_match_loop(out, fstart, off, len, Tracked(m));
    }
}

/// `copy_match_exec` for overlapping matches: in chunks that double, each
/// one a copy of bytes already written. Out of line, as it is rare.
#[inline(never)]
fn copy_match_loop(out: &mut Tail, fstart: usize, off: usize, len: usize, Tracked(mt): Tracked<&mut Meter>)
    requires
        fstart <= old(out)@.len(),
        1 <= off <= old(out)@.len() - fstart,
        old(out)@.len() + len + 32 <= old(out).cap(),
    ensures
        final(out).cap() == old(out).cap(),
        final(mt).n <= old(mt).n + 2 * len,
        final(out)@ == old(out)@.subrange(0, fstart as int) + copy_match(
            old(out)@.subrange(fstart as int, old(out)@.len() as int),
            off as nat,
            len as nat,
        ),
{
    let ghost pre = out@.subrange(0, fstart as int);
    let ghost o0 = out@.subrange(fstart as int, out@.len() as int);
    let ghost all0 = out@;
    let ghost d = off as int;
    proof {
        lemma_copy_match_periodic(o0, off as nat, len as nat);
        assert(out@ =~= all0 + per_seq(o0, d, 0));
    }
    let start = out.len() - off;
    if len <= off {
        // No overlap: one copy.
        out.append_within(start, len);
        proof {
            mt.n = (mt.n + len) as nat;
            assert forall|j: int| 0 <= j < len implies #[trigger] per_seq(o0, d, len as nat)[j] == all0[start + j] by {
                vstd::arithmetic::div_mod::lemma_small_mod(j as nat, d as nat);
            }
            assert(out@ =~= all0 + per_seq(o0, d, len as nat));
            assert(out@ =~= pre + copy_match(o0, off as nat, len as nat));
        }
        return;
    }
    let ghost cap0 = out.cap();
    let mut done: usize = 0;
    let ghost mut m: int = 0;
    while done < len
        invariant
            done <= len,
            start == all0.len() - d,
            1 <= d <= o0.len(),
            all0.len() + len + 32 <= out.cap(),
            out.cap() == cap0,
            all0 == pre + o0,
            o0.len() == all0.len() - pre.len(),
            pre.len() == fstart,
            m >= 0,
            done < len ==> done as int == m * d,
            out@ == all0 + per_seq(o0, d, done as nat),
            mt.n <= old(mt).n + 2 * done,
        decreases len - done,
    {
        let avail = out.len() - start;
        let n = if len - done < avail { len - done } else { avail };
        proof {
            // The turn, and the bytes copied (at least one).
            mt.n = (mt.n + 1 + n) as nat;
        }
        let ghost before = out@;
        proof {
            vstd::arithmetic::mul::lemma_mul_nonnegative(m, d);
        }
        out.append_within(start, n);
        proof {
            assert forall|j: int| 0 <= j < n implies #[trigger] out@[before.len() + j] == per_seq(o0, d, (done + n) as nat)[done + j] by {
                let v = o0[o0.len() - d + (done + j) % d];
                assert(per_seq(o0, d, (done + n) as nat)[done + j] == v);
                assert(out@[before.len() + j] == before[start + j]);
                if j < d {
                    assert(before[start + j] == all0[start + j]);
                    assert(all0[start + j] == o0[start + j - fstart]);
                    vstd::arithmetic::div_mod::lemma_small_mod(j as nat, d as nat);
                    lemma_mod_period(done + j, j, m, d);
                } else {
                    assert(before[start + j] == per_seq(o0, d, done as nat)[j - d]);
                    assert(per_seq(o0, d, done as nat)[j - d] == o0[o0.len() - d + (j - d) % d]);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(d, m, 1);
                    lemma_mod_period(done + j, j - d, m + 1, d);
                }
            }
            assert forall|i: int| 0 <= i < before.len() implies #[trigger] out@[i] == (all0 + per_seq(o0, d, (done + n) as nat))[i] by {
                assert(out@[i] == before[i]);
                if i >= all0.len() {
                    assert(per_seq(o0, d, done as nat)[i - all0.len()] == per_seq(o0, d, (done + n) as nat)[i - all0.len()]);
                }
            }
            assert forall|i: int| before.len() <= i < out@.len() implies #[trigger] out@[i] == (all0 + per_seq(o0, d, (done + n) as nat))[i] by {
                assert(out@[before.len() + (i - before.len())] == per_seq(o0, d, (done + n) as nat)[done + (i - before.len())]);
            }
            assert(out@ =~= all0 + per_seq(o0, d, (done + n) as nat));
            if done + n < len {
                assert((done + n) as int == (2 * m + 1) * d) by {
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(d, 2 * m, 1);
                    vstd::arithmetic::mul::lemma_mul_is_associative(2, m, d);
                }
            }
        }
        proof {
            m = 2 * m + 1;
        }
        done = done + n;
    }
    proof {
        assert(out@ =~= pre + copy_match(o0, off as nat, len as nat));
    }
}

/// `copy_match_exec` for a match of at most 32 bytes from at least 16
/// back that does not overlap what it copies: two 16-byte copies.
#[inline(always)]
fn copy_match_short(out: &mut Tail, fstart: usize, off: usize, len: usize, Tracked(m): Tracked<&mut Meter>)
    requires
        fstart <= old(out)@.len(),
        16 <= off <= old(out)@.len() - fstart,
        len <= off,
        len <= 32,
        old(out)@.len() + 32 <= old(out).cap(),
    ensures
        final(out).cap() == old(out).cap(),
        final(m).n == old(m).n + len,
        final(out)@ == old(out)@.subrange(0, fstart as int) + copy_match(
            old(out)@.subrange(fstart as int, old(out)@.len() as int),
            off as nat,
            len as nat,
        ),
{
    let ghost pre = out@.subrange(0, fstart as int);
    let ghost o0 = out@.subrange(fstart as int, out@.len() as int);
    let ghost all0 = out@;
    let ghost d = off as int;
    proof {
        lemma_copy_match_periodic(o0, off as nat, len as nat);
    }
    let start = out.len() - off;
    out.append_within32(start, len);
    proof {
        m.n = (m.n + len) as nat;
        assert forall|j: int| 0 <= j < len implies #[trigger] per_seq(o0, d, len as nat)[j] == all0[start + j] by {
            vstd::arithmetic::div_mod::lemma_small_mod(j as nat, d as nat);
        }
        assert(out@ =~= all0 + per_seq(o0, d, len as nat));
        assert(out@ =~= pre + copy_match(o0, off as nat, len as nat));
    }
}

/// The frame's output in `out`.
pub open spec fn fout(out: Seq<u8>, fstart: int) -> Seq<u8> {
    out.subrange(fstart, out.len() as int)
}

/// The decoder's state as the spec sees it.
pub open spec fn sstate(p: usize, sll: u32, sof: u32, sml: u32, r1: u64, r2: u64, r3: u64, li: usize, out: Seq<u8>, fstart: int) -> SeqState {
    SeqState {
        p: p as int,
        sll: sll as nat,
        sof: sof as nat,
        sml: sml as nat,
        reps: Reps { r1: r1 as nat, r2: r2 as nat, r3: r3 as nat },
        li: li as int,
        out: fout(out, fstart),
    }
}

/// `seq_run` only appends to the output.
pub proof fn lemma_seq_run_grows(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, window: nat, n: nat, st: SeqState)
    ensures
        seq_run(t, s, lits, window, n, st) is Some ==> seq_run(t, s, lits, window, n, st).unwrap().out.len() >= st.out.len(),
        seq_run(t, s, lits, window, n, st) is Some && 0 <= st.li <= lits.len() ==> 0 <= seq_run(t, s, lits, window, n, st).unwrap().li <= lits.len(),
    decreases n,
{
    reveal(seq_run);
    if n > 0 && seq_run(t, s, lits, window, n, st) is Some {
        let ell = t.ll.rows[st.sll as int];
        let eof = t.of.rows[st.sof as int];
        let eml = t.ml.rows[st.sml as int];
        let oc = eof.sym;
        let mlb = ml_bits(eml.sym);
        let llb = ll_bits(ell.sym);
        let p0 = st.p;
        let ov = pow2(oc) + bits(s, p0 - oc, oc);
        let p1 = p0 - oc;
        let ml = ml_base(eml.sym) + bits(s, p1 - mlb, mlb);
        let p2 = p1 - mlb;
        let ll = ll_base(ell.sym) + bits(s, p2 - llb, llb);
        let p3 = p2 - llb;
        let (off, reps) = resolve_offset(ov, ll == 0, st.reps).unwrap();
        let out1 = st.out + lits.subrange(st.li, st.li + ll);
        let out2 = copy_match(out1, off, ml);
        lemma_copy_match_len(out1, off, ml);
        let li = st.li + ll;
        if n > 1 {
            let sll = ell.base + bits(s, p3 - ell.nb, ell.nb);
            let p4 = p3 - ell.nb;
            let sml = eml.base + bits(s, p4 - eml.nb, eml.nb);
            let p5 = p4 - eml.nb;
            let sof = eof.base + bits(s, p5 - eof.nb, eof.nb);
            let p6 = p5 - eof.nb;
            lemma_seq_run_grows(
                t,
                s,
                lits,
                window,
                (n - 1) as nat,
                SeqState { p: p6, sll: sll, sof: sof, sml: sml, reps: reps, li: li, out: out2 },
            );
        }
    }
}

/// The result of decoding sequences: stream position, repeat offsets,
/// literals used.
pub struct SeqOut {
    pub p: usize,
    pub r1: u64,
    pub r2: u64,
    pub r3: u64,
    pub li: usize,
}

/// One sequence of `seq_run`, decoded and executed, keeping the states.
pub open spec fn seq_step(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, window: nat, st: SeqState) -> Option<SeqState> {
    if st.sll >= t.ll.rows.len() || st.sof >= t.of.rows.len() || st.sml >= t.ml.rows.len() {
        None
    } else {
        let ell = t.ll.rows[st.sll as int];
        let eof = t.of.rows[st.sof as int];
        let eml = t.ml.rows[st.sml as int];
        let oc = eof.sym;
        let mlb = ml_bits(eml.sym);
        let llb = ll_bits(ell.sym);
        let p0 = st.p;
        if oc + mlb + llb > p0 {
            None
        } else {
            let ov = pow2(oc) + bits(s, p0 - oc, oc);
            let p1 = p0 - oc;
            let ml = ml_base(eml.sym) + bits(s, p1 - mlb, mlb);
            let p2 = p1 - mlb;
            let ll = ll_base(ell.sym) + bits(s, p2 - llb, llb);
            let p3 = p2 - llb;
            match resolve_offset(ov, ll == 0, st.reps) {
                None => None,
                Some((off, reps)) => {
                    if st.li + ll > lits.len() {
                        None
                    } else {
                        let out1 = st.out + lits.subrange(st.li, st.li + ll);
                        if off > out1.len() || off > window || off == 0 {
                            None
                        } else {
                            Some(
                                SeqState {
                                    p: p3,
                                    sll: st.sll,
                                    sof: st.sof,
                                    sml: st.sml,
                                    reps: reps,
                                    li: st.li + ll,
                                    out: copy_match(out1, off, ml),
                                },
                            )
                        }
                    }
                },
            }
        }
    }
}

/// The state update after a sequence: new position and states.
pub open spec fn seq_next(t: SeqTables, s: Seq<u8>, p3: int, sll: nat, sof: nat, sml: nat) -> Option<(int, nat, nat, nat)> {
    if sll >= t.ll.rows.len() || sof >= t.of.rows.len() || sml >= t.ml.rows.len() {
        None
    } else {
        let ell = t.ll.rows[sll as int];
        let eof = t.of.rows[sof as int];
        let eml = t.ml.rows[sml as int];
        if ell.nb + eml.nb + eof.nb > p3 {
            None
        } else {
            let sll2 = ell.base + bits(s, p3 - ell.nb, ell.nb);
            let p4 = p3 - ell.nb;
            let sml2 = eml.base + bits(s, p4 - eml.nb, eml.nb);
            let p5 = p4 - eml.nb;
            let sof2 = eof.base + bits(s, p5 - eof.nb, eof.nb);
            Some((p5 - eof.nb, sll2, sof2, sml2))
        }
    }
}

/// `seq_run` as `seq_step` then `seq_next`.
pub proof fn lemma_seq_run_unfold(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, window: nat, n: nat, st: SeqState)
    requires
        n > 0,
    ensures
        seq_run(t, s, lits, window, n, st) == match seq_step(t, s, lits, window, st) {
            None => None,
            Some(a) => if n == 1 {
                Some(a)
            } else {
                match seq_next(t, s, a.p, a.sll, a.sof, a.sml) {
                    None => None,
                    Some((p6, x, y, z)) => seq_run(
                        t,
                        s,
                        lits,
                        window,
                        (n - 1) as nat,
                        SeqState { p: p6, sll: x, sof: y, sml: z, reps: a.reps, li: a.li, out: a.out },
                    ),
                }
            },
        },
{
    reveal(seq_run);
}

/// One sequence (`seq_step`). `None` also when the output would pass `olimit`.
#[verifier::rlimit(40)]
#[inline(always)]
pub fn seq_step_exec(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    p: usize,
    sll: u32,
    sof: u32,
    sml: u32,
    r1: u64,
    r2: u64,
    r3: u64,
    li: usize,
    out: &mut Tail,
    fstart: usize,
    olimit: usize,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Result<SeqOut, bool>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p <= 8 * s@.len(),
        li <= lits@.len(),
        (sll as int) < t.ll.rows@.len(),
        (sof as int) < t.of.rows@.len(),
        (sml as int) < t.ml.rows@.len(),
        fstart <= old(out)@.len() <= olimit,
        olimit <= MAX_LIMIT,
        old(out).cap() >= olimit + 64,
    ensures
        final(out).cap() == old(out).cap(),
        // Work: two steps a byte at most, and every sequence writes three.
        final(out)@.len() >= old(out)@.len(),
        final(m).n <= old(m).n + 2 * (final(out)@.len() - old(out)@.len()),
        final(out)@.len() <= olimit,
        r is Ok ==> final(out)@.len() >= old(out)@.len() + 3,
        r is Ok ==> final(out)@.len() - old(out)@.len() >= r.unwrap().li - li,
        ({
            let cur = sstate(p, sll, sof, sml, r1, r2, r3, li, old(out)@, fstart as int);
            match seq_step(ts, s@, lits@, window as nat, cur) {
                None => r is Err,
                Some(a) => match r {
                    Err(lim) => lim && fstart + a.out.len() > olimit,
                    Ok(o) => {
                        &&& a.p == o.p as int
                        &&& a.reps == (Reps { r1: o.r1 as nat, r2: o.r2 as nat, r3: o.r3 as nat })
                        &&& a.li == o.li as int
                        &&& a.sll == sll as nat && a.sof == sof as nat && a.sml == sml as nat
                        &&& fstart <= final(out)@.len() <= olimit
                        &&& final(out)@.subrange(0, fstart as int) == old(out)@.subrange(0, fstart as int)
                        &&& fout(final(out)@, fstart as int) == a.out
                        &&& o.li <= lits@.len()
                        &&& o.p <= p
                    },
                },
            }
        }),
{
    let ghost pre = out@.subrange(0, fstart as int);
    let ell = row(t.ll.rows.as_slice(), sll as usize);
    let eof = row(t.of.rows.as_slice(), sof as usize);
    let eml = row(t.ml.rows.as_slice(), sml as usize);
    proof {
        assert(t.ll.rows@[sll as int] == ell);
        assert(t.of.rows@[sof as int] == eof);
        assert(t.ml.rows@[sml as int] == eml);
    }
    let oc = eof.sym as u32;
    proof {
        assert((eml.sym as int) < 53);
    }
    let (mlbase, mlb) = ml_code(eml.sym);
    proof {
        lemma_ml_base_min(eml.sym as nat);
    }
    let (llbase, llb) = ll_code(ell.sym);
    if (oc + mlb + llb) as usize > p {
        return Err(false);
    }
    proof {
        lemma_u64_pow2_no_overflow(oc as nat);
        lemma_u64_shl_is_mul(1, oc as u64);
        lemma_pow2_le(oc as nat, 31);
        lemma_pow2_le(mlb as nat, 16);
        lemma_pow2_le(llb as nat, 16);
        assert(pow2(31) == 0x8000_0000 && pow2(16) == 65536) by {
            lemma2_to64();
        }
    }
    let p1 = p - oc as usize;
    let p2 = p1 - mlb as usize;
    let p3 = p2 - llb as usize;
    // The three fields with one read when they fit in 56 bits.
    let tot = oc + mlb + llb;
    let (xo, xm, xl) = if tot <= 56 {
        let w = bits_at(s, p3, tot);
        (
            field_top(w, llb + mlb, Ghost(s@), Ghost(p3 as int), Ghost(tot as nat)),
            field(w, llb, mlb, Ghost(s@), Ghost(p3 as int), Ghost(tot as nat)),
            field(w, 0, llb, Ghost(s@), Ghost(p3 as int), Ghost(tot as nat)),
        )
    } else {
        (rd(s, p, oc), rd(s, p1, mlb), rd(s, p2, llb))
    };
    let ov: u64 = (1u64 << oc as u64) + xo;
    let ml: u64 = mlbase as u64 + xm;
    let ll: u64 = llbase as u64 + xl;
    let (off, n1, n2, n3) = match resolve_offset_exec(ov, ll == 0, r1, r2, r3) {
        None => {
            return Err(false);
        },
        Some(x) => x,
    };
    if li as u64 + ll > lits.len() as u64 {
        return Err(false);
    }
    let lend = li + ll as usize;
    let ghost out1 = fout(out@, fstart as int) + lits@.subrange(li as int, lend as int);
    proof {
        lemma_copy_match_len(out1, off as nat, ml as nat);
    }
    if out.len() + (ll as usize) + (ml as usize) > olimit {
        return Err(true);
    }
    out.append_from(lits, li, ll as usize);
    proof {
        assert(out@.subrange(0, fstart as int) =~= pre);
        assert(fout(out@, fstart as int) =~= out1);
        m.n = (m.n + ll) as nat;
    }
    if off > (out.len() - fstart) as u64 || off > window || off == 0 {
        return Err(false);
    }
    copy_match_exec(out, fstart, off as usize, ml as usize, Tracked(m));
    proof {
        assert(out@.subrange(0, fstart as int) =~= pre);
        assert(fout(out@, fstart as int) =~= copy_match(out1, off as nat, ml as nat));
    }
    Ok(SeqOut { p: p3, r1: n1, r2: n2, r3: n3, li: lend })
}

/// The state update (`seq_next`).
#[inline(always)]
pub fn seq_next_exec(t: &SeqTabs, s: &[u8], p3: usize, sll: u32, sof: u32, sml: u32, Ghost(ts): Ghost<SeqTables>) -> (r: Option<(usize, u32, u32, u32)>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        p3 <= 8 * s@.len(),
        (sll as int) < t.ll.rows@.len(),
        (sof as int) < t.of.rows@.len(),
        (sml as int) < t.ml.rows@.len(),
    ensures
        match seq_next(ts, s@, p3 as int, sll as nat, sof as nat, sml as nat) {
            None => r is None,
            Some((p6, x, y, z)) => r is Some && r.unwrap().0 as int == p6 && r.unwrap().1 as nat == x
                && r.unwrap().2 as nat == y && r.unwrap().3 as nat == z && p6 <= p3
                && (r.unwrap().1 as int) < t.ll.rows@.len() && (r.unwrap().2 as int) < t.of.rows@.len()
                && (r.unwrap().3 as int) < t.ml.rows@.len(),
        },
{
    let ell = row(t.ll.rows.as_slice(), sll as usize);
    let eof = row(t.of.rows.as_slice(), sof as usize);
    let eml = row(t.ml.rows.as_slice(), sml as usize);
    proof {
        assert(t.ll.rows@[sll as int] == ell);
        assert(t.of.rows@[sof as int] == eof);
        assert(t.ml.rows@[sml as int] == eml);
    }
    if (ell.nb as usize + eml.nb as usize + eof.nb as usize) > p3 {
        return None;
    }
    proof {
        lemma_pow2_le(ell.nb as nat, 9);
        lemma_pow2_le(eml.nb as nat, 9);
        lemma_pow2_le(eof.nb as nat, 9);
        assert(pow2(9) == 512) by {
            lemma2_to64();
        }
    }
    let p4 = p3 - ell.nb as usize;
    let p5 = p4 - eml.nb as usize;
    let p6 = p5 - eof.nb as usize;
    let tot = ell.nb as u32 + eml.nb as u32 + eof.nb as u32;
    let w = bits_at(s, p6, tot);
    let a = ell.base as u32 + field_top(w, eof.nb as u32 + eml.nb as u32, Ghost(s@), Ghost(p6 as int), Ghost(tot as nat)) as u32;
    let c = eml.base as u32 + field(w, eof.nb as u32, eml.nb as u32, Ghost(s@), Ghost(p6 as int), Ghost(tot as nat)) as u32;
    let b = eof.base as u32 + field(w, 0, eof.nb as u32, Ghost(s@), Ghost(p6 as int), Ghost(tot as nat)) as u32;
    Some((p6, a, b, c))
}

/// One sequence decoded by `seq_dec`: offset value, match length,
/// literals length, the next three states and the bits used.
pub struct Dec {
    pub ov: u64,
    pub ml: u64,
    pub ll: u64,
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub tot: u32,
}

/// What `seq_dec` returns for the stream `s` at `p` in states `sll`, `sof`
/// and `sml`: the fields of `seq_step` and `seq_next`.
pub open spec fn seq_dec_is(d: Dec, t: SeqTables, s: Seq<u8>, p: int, sll: int, sof: int, sml: int) -> bool {
    let ell = t.ll.rows[sll];
    let eof = t.of.rows[sof];
    let eml = t.ml.rows[sml];
    let oc = eof.sym;
    let mlb = ml_bits(eml.sym);
    let llb = ll_bits(ell.sym);
    let p3 = p - oc - mlb - llb;
    &&& d.tot as nat == oc + mlb + llb + ell.nb + eml.nb + eof.nb
    &&& d.tot <= 56
    &&& d.ov as nat == pow2(oc) + bits(s, p - oc, oc)
    &&& d.ml as nat == ml_base(eml.sym) + bits(s, p - oc - mlb, mlb)
    &&& d.ll as nat == ll_base(ell.sym) + bits(s, p3, llb)
    &&& d.a as nat == ell.base + bits(s, p3 - ell.nb, ell.nb)
    &&& d.c as nat == eml.base + bits(s, p3 - ell.nb - eml.nb, eml.nb)
    &&& d.b as nat == eof.base + bits(s, p3 - ell.nb - eml.nb - eof.nb, eof.nb)
    &&& d.ov < 0x1_0000_0000
    &&& d.ml <= 131074
    &&& d.ll <= 131071
}

/// Decodes one sequence and the next states from a single 56-bit read
/// below `p`. `None` when the sequence needs more than 56 bits.
#[verifier::rlimit(120)]
#[inline(always)]
pub fn seq_dec(t: &SeqTabs, s: &[u8], p: usize, sll: u32, sof: u32, sml: u32, Ghost(ts): Ghost<SeqTables>) -> (r: Option<Dec>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        64 <= p < 8 * s@.len(),
        (sll as int) < t.ll.rows@.len(),
        (sof as int) < t.of.rows@.len(),
        (sml as int) < t.ml.rows@.len(),
    ensures
        r matches Some(d) ==> {
            &&& seq_dec_is(d, ts, s@, p as int, sll as int, sof as int, sml as int)
            &&& (d.a as int) < t.ll.rows@.len()
            &&& (d.b as int) < t.of.rows@.len()
            &&& (d.c as int) < t.ml.rows@.len()
        },
{
    let el = row(t.dl.as_slice(), sll as usize);
    let eo = row(t.dof.as_slice(), sof as usize);
    let em = row(t.dml.as_slice(), sml as usize);
    let ghost ell = t.ll.rows@[sll as int];
    let ghost eof = t.of.rows@[sof as int];
    let ghost eml = t.ml.rows@[sml as int];
    proof {
        assert(t.dl@[sll as int] == el);
        assert(t.dof@[sof as int] == eo);
        assert(t.dml@[sml as int] == em);
        lemma_pow2_le(ell.nb as nat, 9);
        lemma_pow2_le(eml.nb as nat, 9);
        lemma_pow2_le(eof.nb as nat, 9);
        lemma_pow2_le(el.xb as nat, 16);
        lemma_pow2_le(em.xb as nat, 16);
        lemma_pow2_le(eo.xb as nat, 31);
        assert(pow2(9) == 512 && pow2(16) == 65536 && pow2(31) == 0x8000_0000) by {
            lemma2_to64();
        }
    }
    let oxb = eo.xb as u32;
    let mxb = em.xb as u32;
    let lxb = el.xb as u32;
    let c1 = oxb + mxb;
    let c2 = c1 + lxb;
    let c3 = c2 + el.nb as u32;
    let c4 = c3 + em.nb as u32;
    let tot = c4 + eo.nb as u32;
    if tot > 56 {
        return None;
    }
    let w = word56(s, p);
    let ghost lo = p - 56;
    let ov = eo.base as u64 + fld(w, 56 - oxb, oxb, Ghost(s@), Ghost(lo));
    // Most literals and match lengths have no extra bits.
    let ml = if mxb == 0 {
        em.base as u64
    } else {
        em.base as u64 + fld(w, 56 - c1, mxb, Ghost(s@), Ghost(lo))
    };
    let ll = if lxb == 0 {
        el.base as u64
    } else {
        el.base as u64 + fld(w, 56 - c2, lxb, Ghost(s@), Ghost(lo))
    };
    let a = el.next as u32 + fld(w, 56 - c3, el.nb as u32, Ghost(s@), Ghost(lo)) as u32;
    let c = em.next as u32 + fld(w, 56 - c4, em.nb as u32, Ghost(s@), Ghost(lo)) as u32;
    let b = eo.next as u32 + fld(w, 56 - tot, eo.nb as u32, Ghost(s@), Ghost(lo)) as u32;
    proof {
        assert(bits(s@, p - c1, 0) == 0);
        assert(bits(s@, p - c2, 0) == 0);
    }
    Some(Dec { ov, ml, ll, a, b, c, tot })
}

/// Where the fast loop stopped. `res` is 0 when it stopped between two
/// sequences (the rest is the state there), 1 when the sequences are
/// invalid, and 2 when the output would pass the limit.
pub struct Fast {
    pub res: u8,
    pub p: usize,
    pub sll: u32,
    pub sof: u32,
    pub sml: u32,
    pub r1: u64,
    pub r2: u64,
    pub r3: u64,
    pub li: usize,
    pub left: usize,
}

/// Decodes and executes sequences while each one, with its state update,
/// fits in one 56-bit read (`seq_dec`), stopping before the last one.
/// The caller decodes the next sequence with `seq_step_exec`.
#[verifier::rlimit(80)]
#[inline(always)]
pub fn seq_fast(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    left0: usize,
    p0: usize,
    sll0: u32,
    sof0: u32,
    sml0: u32,
    r10: u64,
    r20: u64,
    r30: u64,
    li0: usize,
    out: &mut Tail,
    fstart: usize,
    olimit: usize,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Fast)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p0 <= 8 * s@.len(),
        li0 <= lits@.len(),
        (sll0 as int) < t.ll.rows@.len(),
        (sof0 as int) < t.of.rows@.len(),
        (sml0 as int) < t.ml.rows@.len(),
        fstart <= old(out)@.len() <= olimit,
        olimit <= MAX_LIMIT,
        old(out).cap() >= olimit + 64,
    ensures
        final(out).cap() == old(out).cap(),
        final(out)@.len() >= old(out)@.len(),
        final(m).n <= old(m).n + 3 * (final(out)@.len() - old(out)@.len()) + 2,
        final(out)@.len() <= olimit,
        r.res == 0 ==> final(out)@.len() - old(out)@.len() >= r.li - li0,
        ({
            let st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, li0, old(out)@, fstart as int);
            let full = seq_run(ts, s@, lits@, window as nat, left0 as nat, st0);
            if r.res == 0 {
                &&& r.left <= left0
                &&& seq_run(
                    ts,
                    s@,
                    lits@,
                    window as nat,
                    r.left as nat,
                    sstate(r.p, r.sll, r.sof, r.sml, r.r1, r.r2, r.r3, r.li, final(out)@, fstart as int),
                ) == full
                &&& r.p <= 8 * s@.len()
                &&& r.li <= lits@.len()
                &&& (r.sll as int) < t.ll.rows@.len()
                &&& (r.sof as int) < t.of.rows@.len()
                &&& (r.sml as int) < t.ml.rows@.len()
                &&& fstart <= final(out)@.len() <= olimit
                &&& final(out)@.subrange(0, fstart as int) == old(out)@.subrange(0, fstart as int)
            } else {
                match full {
                    None => true,
                    Some(fin) => r.res == 2 && fstart + fin.out.len() > olimit,
                }
            }
        }),
{
    let ghost pre = out@.subrange(0, fstart as int);
    let ghost st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, li0, out@, fstart as int);
    let ghost full = seq_run(ts, s@, lits@, window as nat, left0 as nat, st0);
    let mut p = p0;
    let mut sll = sll0;
    let mut sof = sof0;
    let mut sml = sml0;
    let mut r1 = r10;
    let mut r2 = r20;
    let mut r3 = r30;
    let mut li = li0;
    let mut left = left0;
    // `p` only falls, so it stays below the end of the stream and
    // `seq_dec` can load without a test.
    if p >= 8 * s.len() {
        return Fast { res: 0, p, sll, sof, sml, r1, r2, r3, li, left };
    }
    // How far back a match may reach, as of the last time it was worked
    // out: the output only grows, so this stays a safe bound, and the
    // short case tests the offset against it alone.
    let mut wlim: u64 = if (out.len() - fstart) as u64 > window {
        window
    } else {
        (out.len() - fstart) as u64
    };
    loop
        invariant_except_break
            m.n <= old(m).n + 3 * (out@.len() - old(out)@.len()) + 1,
        invariant
            left <= left0,
            seqtabs_is(t, ts),
            s@.len() < BITS_MAX,
            lits@.len() <= 131072,
            p < 8 * s@.len(),
            li <= lits@.len(),
            (sll as int) < t.ll.rows@.len(),
            (sof as int) < t.of.rows@.len(),
            (sml as int) < t.ml.rows@.len(),
            fstart <= out@.len() <= olimit,
            olimit <= MAX_LIMIT,
            out.cap() == old(out).cap(),
            out.cap() >= olimit + 64,
            wlim <= window,
            wlim <= out@.len() - fstart,
            out@.subrange(0, fstart as int) == pre,
            pre == old(out)@.subrange(0, fstart as int),
            st0 == sstate(p0, sll0, sof0, sml0, r10, r20, r30, li0, old(out)@, fstart as int),
            full == seq_run(ts, s@, lits@, window as nat, left0 as nat, st0),
            seq_run(ts, s@, lits@, window as nat, left as nat, sstate(p, sll, sof, sml, r1, r2, r3, li, out@, fstart as int))
                == full,
            out@.len() >= old(out)@.len(),
            li >= li0,
            out@.len() - old(out)@.len() >= li - li0,
        ensures
            m.n <= old(m).n + 3 * (out@.len() - old(out)@.len()) + 2,
        decreases left,
    {
        proof {
            m.n = m.n + 1;
        }
        if left <= 1 || p < 64 {
            break;
        }
        let ghost cur = sstate(p, sll, sof, sml, r1, r2, r3, li, out@, fstart as int);
        proof {
            lemma_seq_run_unfold(ts, s@, lits@, window as nat, left as nat, cur);
        }
        let d = match seq_dec(t, s, p, sll, sof, sml, Ghost(ts)) {
            None => {
                break;
            },
            Some(d) => d,
        };
        let ghost step = seq_step(ts, s@, lits@, window as nat, cur);
        let ghost ell = ts.ll.rows[sll as int];
        let ghost eof = ts.of.rows[sof as int];
        let ghost eml = ts.ml.rows[sml as int];
        let ghost oc = eof.sym;
        let ghost mlb = ml_bits(eml.sym);
        let ghost llb = ll_bits(ell.sym);
        let ghost sres = resolve_offset(d.ov as nat, d.ll == 0, cur.reps);
        proof {
            assert(oc + mlb + llb <= p);
            assert(d.ov as nat == pow2(oc) + bits(s@, p - oc, oc));
            assert(d.ml as nat == ml_base(eml.sym) + bits(s@, (p - oc) - mlb, mlb));
            assert(d.ll as nat == ll_base(ell.sym) + bits(s@, ((p - oc) - mlb) - llb, llb));
            assert(sres is None ==> step is None);
            // The next state, if the step succeeds, is the one decoded.
            if let Some(a) = step {
                assert(seq_next(ts, s@, a.p, a.sll, a.sof, a.sml) == Some(
                    ((p - d.tot) as int, d.a as nat, d.b as nat, d.c as nat),
                ));
                lemma_seq_run_grows(
                    ts,
                    s@,
                    lits@,
                    window as nat,
                    (left - 1) as nat,
                    SeqState {
                        p: (p - d.tot) as int,
                        sll: d.a as nat,
                        sof: d.b as nat,
                        sml: d.c as nat,
                        reps: a.reps,
                        li: a.li,
                        out: a.out,
                    },
                );
            }
        }
        let ll = d.ll;
        let ml = d.ml;
        proof {
            assert(eml.sym == t.ml.rows@[sml as int].sym as nat);
            lemma_ml_base_min(eml.sym);
            assert(ml >= 3);
        }
        let (off, n1, n2, n3) = match resolve_offset_exec(d.ov, ll == 0, r1, r2, r3) {
            None => {
                proof {
                    assert(step is None);
                }
                return Fast { res: 1, p, sll, sof, sml, r1, r2, r3, li, left };
            },
            Some(x) => x,
        };
        let ghost out1 = fout(out@, fstart as int) + lits@.subrange(li as int, li + ll);
        proof {
            lemma_copy_match_len(out1, off as nat, ml as nat);
        }
        // Most sequences are short: one test for everything, then four
        // 16-byte copies with nothing to decide.
        if ll <= 32 && ml <= 32 && off >= 16 && ml <= off && li as u64 + ll + 32 <= lits.len() as u64 && out.len() as u64
            + ll + ml <= olimit as u64 && off <= wlim {
            out.append_from32(lits, li, ll as usize);
            proof {
                assert(out@.subrange(0, fstart as int) =~= pre);
                assert(fout(out@, fstart as int) =~= out1);
                m.n = (m.n + ll) as nat;
            }
            copy_match_short(out, fstart, off as usize, ml as usize, Tracked(m));
            proof {
                assert(out@.subrange(0, fstart as int) =~= pre);
                assert(fout(out@, fstart as int) =~= copy_match(out1, off as nat, ml as nat));
                assert(step is Some);
                assert(step.unwrap().out == fout(out@, fstart as int));
                assert(step.unwrap().reps == (Reps { r1: n1 as nat, r2: n2 as nat, r3: n3 as nat }));
                assert(step.unwrap().li == li + ll);
            }
            // The step ends here rather than joining the general case
            // below: measured, that is the faster arrangement.
            p = p - d.tot as usize;
            sll = d.a;
            sof = d.b;
            sml = d.c;
            r1 = n1;
            r2 = n2;
            r3 = n3;
            li = li + ll as usize;
            left = left - 1;
            continue;
        } else {
            wlim = if (out.len() - fstart) as u64 > window {
                window
            } else {
                (out.len() - fstart) as u64
            };
            if li as u64 + ll > lits.len() as u64 {
                proof {
                    assert(step is None);
                }
                return Fast { res: 1, p, sll, sof, sml, r1, r2, r3, li, left };
            }
            if out.len() + (ll as usize) + (ml as usize) > olimit {
                proof {
                    if let Some(a) = step {
                        assert(a.out == copy_match(out1, off as nat, ml as nat));
                        assert(fstart + a.out.len() > olimit);
                    }
                }
                return Fast { res: 2, p, sll, sof, sml, r1, r2, r3, li, left };
            }
            out.append_from(lits, li, ll as usize);
            proof {
                assert(out@.subrange(0, fstart as int) =~= pre);
                assert(fout(out@, fstart as int) =~= out1);
                m.n = (m.n + ll) as nat;
            }
            if off > (out.len() - fstart) as u64 || off > window || off == 0 {
                proof {
                    assert(step is None);
                }
                return Fast { res: 1, p, sll, sof, sml, r1, r2, r3, li, left };
            }
            copy_match_exec(out, fstart, off as usize, ml as usize, Tracked(m));
        }
        let lend = li + ll as usize;
        proof {
            assert(out@.subrange(0, fstart as int) =~= pre);
            assert(fout(out@, fstart as int) =~= copy_match(out1, off as nat, ml as nat));
            assert(step is Some);
            assert(step.unwrap().out == fout(out@, fstart as int));
            assert(step.unwrap().reps == (Reps { r1: n1 as nat, r2: n2 as nat, r3: n3 as nat }));
            assert(step.unwrap().li == lend as int);
        }
        p = p - d.tot as usize;
        sll = d.a;
        sof = d.b;
        sml = d.c;
        r1 = n1;
        r2 = n2;
        r3 = n3;
        li = lend;
        left = left - 1;
    }
    Fast { res: 0, p, sll, sof, sml, r1, r2, r3, li, left }
}

/// Decodes and executes `n` sequences (`seq_run`), appending to `out`.
/// Stops early (`None`) once the output passes `olimit` bytes: the block is
/// then too large whatever follows.
#[inline(always)]
pub fn seq_run_exec(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    n: usize,
    p0: usize,
    sll0: u32,
    sof0: u32,
    sml0: u32,
    r10: u64,
    r20: u64,
    r30: u64,
    out: &mut Vec<u8>,
    fstart: usize,
    olimit: usize,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Result<SeqOut, bool>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p0 <= 8 * s@.len(),
        (sll0 as int) < t.ll.rows@.len(),
        (sof0 as int) < t.of.rows@.len(),
        (sml0 as int) < t.ml.rows@.len(),
        fstart <= old(out)@.len() <= olimit,
        olimit <= MAX_LIMIT,
        olimit - old(out)@.len() <= 131072,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(m).n <= old(m).n + 3 * (final(out)@.len() - old(out)@.len()) + 3,
        final(out)@.len() <= olimit,
        r is Ok ==> final(out)@.len() - old(out)@.len() >= r.unwrap().li,
        ({
            let st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, 0, old(out)@, fstart as int);
            match seq_run(ts, s@, lits@, window as nat, n as nat, st0) {
                None => r is Err,
                Some(fin) => match r {
                    Err(lim) => lim && fstart + fin.out.len() > olimit,
                    Ok(o) => {
                        &&& fin.p == o.p as int
                        &&& fin.reps == (Reps { r1: o.r1 as nat, r2: o.r2 as nat, r3: o.r3 as nat })
                        &&& fin.li == o.li as int
                        &&& final(out)@ == old(out)@.subrange(0, fstart as int) + fin.out
                        &&& o.li <= lits@.len()
                        &&& final(out)@.len() <= olimit
                    },
                },
            }
        }),
{
    // Room for the whole block is reserved here, once, so that no append
    // in the loop has to test for it.
    let extra = olimit - out.len() + 64;
    let mut w = Tail::take(out, extra);
    let r = seq_run_tail(t, s, lits, window, n, p0, sll0, sof0, sml0, r10, r20, r30, &mut w, fstart, olimit, Ghost(ts), Tracked(m));
    w.put_back(out);
    r
}

/// `seq_run_exec` on a vector with room reserved up to `olimit` and 64
/// bytes more.
#[inline(always)]
#[verifier::rlimit(40)]
fn seq_run_tail(
    t: &SeqTabs,
    s: &[u8],
    lits: &[u8],
    window: u64,
    n: usize,
    p0: usize,
    sll0: u32,
    sof0: u32,
    sml0: u32,
    r10: u64,
    r20: u64,
    r30: u64,
    out: &mut Tail,
    fstart: usize,
    olimit: usize,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: Result<SeqOut, bool>)
    requires
        seqtabs_is(t, ts),
        s@.len() < BITS_MAX,
        lits@.len() <= 131072,
        p0 <= 8 * s@.len(),
        (sll0 as int) < t.ll.rows@.len(),
        (sof0 as int) < t.of.rows@.len(),
        (sml0 as int) < t.ml.rows@.len(),
        fstart <= old(out)@.len() <= olimit,
        olimit <= MAX_LIMIT,
        old(out).cap() >= olimit + 64,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(m).n <= old(m).n + 3 * (final(out)@.len() - old(out)@.len()) + 3,
        final(out)@.len() <= olimit,
        r is Ok ==> final(out)@.len() - old(out)@.len() >= r.unwrap().li,
        ({
            let st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, 0, old(out)@, fstart as int);
            match seq_run(ts, s@, lits@, window as nat, n as nat, st0) {
                None => r is Err,
                Some(fin) => match r {
                    Err(lim) => lim && fstart + fin.out.len() > olimit,
                    Ok(o) => {
                        &&& fin.p == o.p as int
                        &&& fin.reps == (Reps { r1: o.r1 as nat, r2: o.r2 as nat, r3: o.r3 as nat })
                        &&& fin.li == o.li as int
                        &&& final(out)@ == old(out)@.subrange(0, fstart as int) + fin.out
                        &&& o.li <= lits@.len()
                        &&& final(out)@.len() <= olimit
                    },
                },
            }
        }),
{
    let ghost pre = out@.subrange(0, fstart as int);
    let ghost st0 = sstate(p0, sll0, sof0, sml0, r10, r20, r30, 0, out@, fstart as int);
    let ghost full = seq_run(ts, s@, lits@, window as nat, n as nat, st0);
    let mut p = p0;
    let mut sll = sll0;
    let mut sof = sof0;
    let mut sml = sml0;
    let mut r1 = r10;
    let mut r2 = r20;
    let mut r3 = r30;
    let mut li: usize = 0;
    let mut i: usize = 0;
    loop
        invariant
            i <= n,
            seqtabs_is(t, ts),
            s@.len() < BITS_MAX,
            lits@.len() <= 131072,
            p <= 8 * s@.len(),
            li <= lits@.len(),
            (sll as int) < t.ll.rows@.len(),
            (sof as int) < t.of.rows@.len(),
            (sml as int) < t.ml.rows@.len(),
            fstart <= out@.len() <= olimit,
            olimit <= MAX_LIMIT,
            out.cap() >= olimit + 64,
            out@.subrange(0, fstart as int) == pre,
            pre == old(out)@.subrange(0, fstart as int),
            st0 == sstate(p0, sll0, sof0, sml0, r10, r20, r30, 0, old(out)@, fstart as int),
            full == seq_run(ts, s@, lits@, window as nat, n as nat, st0),
            seq_run(ts, s@, lits@, window as nat, (n - i) as nat, sstate(p, sll, sof, sml, r1, r2, r3, li, out@, fstart as int))
                == full,
            out@.len() >= old(out)@.len(),
            m.n <= old(m).n + 3 * (out@.len() - old(out)@.len()),
            out@.len() - old(out)@.len() >= li,
        decreases n - i,
    {
        proof {
            m.n = m.n + 1;
        }
        let ghost cur = sstate(p, sll, sof, sml, r1, r2, r3, li, out@, fstart as int);
        if i == n {
            proof {
                reveal(seq_run);
                assert(seq_run(ts, s@, lits@, window as nat, 0, cur) == Some(cur));
                assert(out@ =~= pre + fout(out@, fstart as int));
            }
            return Ok(SeqOut { p, r1, r2, r3, li });
        }
        // As many sequences as the fast loop takes, then one the slow way.
        let f = seq_fast(t, s, lits, window, n - i, p, sll, sof, sml, r1, r2, r3, li, out, fstart, olimit, Ghost(ts), Tracked(m));
        if f.res != 0 {
            return Err(f.res == 2);
        }
        p = f.p;
        sll = f.sll;
        sof = f.sof;
        sml = f.sml;
        r1 = f.r1;
        r2 = f.r2;
        r3 = f.r3;
        li = f.li;
        i = n - f.left;
        let ghost cur = sstate(p, sll, sof, sml, r1, r2, r3, li, out@, fstart as int);
        if i == n {
            proof {
                reveal(seq_run);
                assert(seq_run(ts, s@, lits@, window as nat, 0, cur) == Some(cur));
                assert(out@ =~= pre + fout(out@, fstart as int));
            }
            return Ok(SeqOut { p, r1, r2, r3, li });
        }
        proof {
            lemma_seq_run_unfold(ts, s@, lits@, window as nat, (n - i) as nat, cur);
        }
        let o = match seq_step_exec(t, s, lits, window, p, sll, sof, sml, r1, r2, r3, li, out, fstart, olimit, Ghost(ts), Tracked(m)) {
            Err(lim) => {
                proof {
                    if let Some(a) = seq_step(ts, s@, lits@, window as nat, cur) {
                        if n - i > 1 {
                            if let Some((p6, x, y, z)) = seq_next(ts, s@, a.p, a.sll, a.sof, a.sml) {
                                lemma_seq_run_grows(
                                    ts,
                                    s@,
                                    lits@,
                                    window as nat,
                                    (n - i - 1) as nat,
                                    SeqState { p: p6, sll: x, sof: y, sml: z, reps: a.reps, li: a.li, out: a.out },
                                );
                            }
                        }
                    }
                }
                return Err(lim);
            },
            Ok(o) => o,
        };
        li = o.li;
        r1 = o.r1;
        r2 = o.r2;
        r3 = o.r3;
        if i + 1 == n {
            proof {
                assert(out@ =~= pre + fout(out@, fstart as int));
            }
            return Ok(SeqOut { p: o.p, r1, r2, r3, li });
        }
        match seq_next_exec(t, s, o.p, sll, sof, sml, Ghost(ts)) {
            None => {
                return Err(false);
            },
            Some((p6, x, y, z)) => {
                p = p6;
                sll = x;
                sof = y;
                sml = z;
            },
        }
        i = i + 1;
    }
}

// ---------------------------------------------------------------------------
// Frame state and compressed blocks
// ---------------------------------------------------------------------------

/// How a block went: decoded, invalid, or stopped at the output limit.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Step {
    Done,
    Bad,
    Limit,
}

/// What the decoder carries from block to block.
pub struct FrameDec {
    pub out: Vec<u8>,
    pub fstart: usize,
    pub r1: u64,
    pub r2: u64,
    pub r3: u64,
    pub huf: Option<HufTab>,
    pub seqt: Option<SeqTabs>,
    pub lits: Vec<u8>,
}

pub open spec fn seqt_opt_is(t: Option<SeqTabs>, s: Option<SeqTables>) -> bool {
    match t {
        None => s is None,
        Some(tt) => s is Some && seqtabs_is(&tt, s.unwrap()),
    }
}

/// `d` is in the spec's state `st`.
pub open spec fn dec_is(d: &FrameDec, st: FrameState) -> bool {
    &&& d.fstart <= d.out@.len()
    &&& fout(d.out@, d.fstart as int) == st.out
    &&& st.reps == (Reps { r1: d.r1 as nat, r2: d.r2 as nat, r3: d.r3 as nat })
    &&& huf_opt_is(d.huf, st.huf)
    &&& seqt_opt_is(d.seqt, st.seqt)
}

/// The number of sequences (`nb_seq`).
pub fn nb_seq_exec(b: &[u8]) -> (r: Option<(usize, usize)>)
    ensures
        match nb_seq(b@) {
            None => r is None,
            Some((n, h)) => r is Some && r.unwrap().0 as nat == n && r.unwrap().1 as int == h && h <= b@.len()
                && n < 0x20000,
        },
{
    if b.len() < 1 {
        None
    } else if b[0] < 128 {
        Some((b[0] as usize, 1))
    } else if b[0] < 255 {
        if b.len() < 2 {
            None
        } else {
            Some(((b[0] as usize - 128) * 256 + b[1] as usize, 2))
        }
    } else if b.len() < 3 {
        None
    } else {
        Some((b[1] as usize + 256 * b[2] as usize + 0x7f00, 3))
    }
}

/// The three tables of a sequences header whose modes byte is at `h`.
pub open spec fn seq_hdr(b: Seq<u8>, h: int, st: FrameState) -> Option<(SeqTables, int)> {
    let modes = b[h];
    let prev_ll = match st.seqt {
        None => None,
        Some(t) => Some(t.ll),
    };
    let prev_of = match st.seqt {
        None => None,
        Some(t) => Some(t.of),
    };
    let prev_ml = match st.seqt {
        None => None,
        Some(t) => Some(t.ml),
    };
    let a0 = h + 1;
    match seq_table(b.subrange(a0, b.len() as int), 0, (modes / 64) as nat, prev_ll) {
        None => None,
        Some((ll, u0)) => {
            let a1 = a0 + u0;
            match seq_table(b.subrange(a1, b.len() as int), 1, ((modes / 16) % 4) as nat, prev_of) {
                None => None,
                Some((of, u1)) => {
                    let a2 = a1 + u1;
                    match seq_table(b.subrange(a2, b.len() as int), 2, ((modes / 4) % 4) as nat, prev_ml) {
                        None => None,
                        Some((ml, u2)) => Some((SeqTables { ll: ll, of: of, ml: ml }, a2 + u2)),
                    }
                },
            }
        },
    }
}

/// The bitstream part of a sequences section, after the tables.
pub open spec fn seq_body(b: Seq<u8>, lits: Seq<u8>, window: nat, st: FrameState, t: SeqTables, a3: int, n: nat) -> Option<
    FrameState,
> {
    let s = b.subrange(a3, b.len() as int);
    let ll = t.ll;
    let of = t.of;
    let ml = t.ml;
    match bstart(s) {
        None => None,
        Some(p) => if ll.log + of.log + ml.log > p {
            None
        } else {
            let sll = bits(s, p - ll.log, ll.log);
            let sof = bits(s, p - ll.log - of.log, of.log);
            let sml = bits(s, p - ll.log - of.log - ml.log, ml.log);
            let st0 = SeqState {
                p: p - ll.log - of.log - ml.log,
                sll: sll,
                sof: sof,
                sml: sml,
                reps: st.reps,
                li: 0,
                out: st.out,
            };
            match seq_run(t, s, lits, window, n, st0) {
                None => None,
                Some(fin) => if fin.p != 0 {
                    None
                } else {
                    Some(
                        FrameState {
                            out: fin.out + lits.subrange(fin.li, lits.len() as int),
                            reps: fin.reps,
                            huf: st.huf,
                            seqt: Some(t),
                        },
                    )
                },
            }
        },
    }
}

/// `seq_section` in three parts.
pub proof fn lemma_seq_section(b: Seq<u8>, lits: Seq<u8>, window: nat, st: FrameState)
    ensures
        seq_section(b, lits, window, st) == match nb_seq(b) {
            None => None,
            Some((n, h)) => if n == 0 {
                if h != b.len() {
                    None
                } else {
                    Some(FrameState { out: st.out + lits, ..st })
                }
            } else if h + 1 > b.len() || b[h] % 4 != 0 {
                None
            } else {
                match seq_hdr(b, h, st) {
                    None => None,
                    Some((t, a3)) => seq_body(b, lits, window, st, t, a3, n),
                }
            },
        },
{
    reveal(seq_section);
}

/// The most steps the three tables of a sequences header take, besides
/// 24 per byte of the block: each is read (`read_ncount`, at most 162),
/// built (`build_table`, at most 1695) and baked (at most 512).
pub spec const SEQ_HDR_WORK: nat = 7200;

/// Parses the three tables (`seq_hdr`).
pub fn seq_hdr_exec(b: &[u8], h: usize, seqt: &Option<SeqTabs>, Ghost(st): Ghost<FrameState>, Tracked(m): Tracked<&mut Meter>) -> (r: Option<(SeqTabs, usize)>)
    requires
        b@.len() < BITS_MAX,
        h < b@.len(),
        seqt_opt_is(*seqt, st.seqt),
    ensures
        final(m).n <= old(m).n + SEQ_HDR_WORK + 24 * b@.len(),
        match seq_hdr(b@, h as int, st) {
            None => r is None,
            Some((t, a3)) => r is Some && seqtabs_is(&r.unwrap().0, t) && r.unwrap().1 as int == a3 && a3 <= b@.len(),
        },
{
    let modes = b[h];
    let a0 = h + 1;
    let ghost gprev_ll: Option<FseTable> = match st.seqt {
        None => None,
        Some(t) => Some(t.ll),
    };
    let ghost gprev_of: Option<FseTable> = match st.seqt {
        None => None,
        Some(t) => Some(t.of),
    };
    let ghost gprev_ml: Option<FseTable> = match st.seqt {
        None => None,
        Some(t) => Some(t.ml),
    };
    let (prev_ll, prev_of, prev_ml) = match seqt {
        None => (None, None, None),
        Some(t) => (Some(&t.ll), Some(&t.of), Some(&t.ml)),
    };
    let (ll, u0) = match seq_table_exec(slice_subrange(b, a0, b.len()), 0, modes / 64, prev_ll, Ghost(gprev_ll), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let a1 = a0 + u0;
    let (of, u1) = match seq_table_exec(slice_subrange(b, a1, b.len()), 1, (modes / 16) % 4, prev_of, Ghost(gprev_of), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let a2 = a1 + u1;
    let (ml, u2) = match seq_table_exec(slice_subrange(b, a2, b.len()), 2, (modes / 4) % 4, prev_ml, Ghost(gprev_ml), Tracked(m)) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    proof {
        lemma_pow2_le(ll.log as nat, 9);
        lemma_pow2_le(of.log as nat, 9);
        lemma_pow2_le(ml.log as nat, 9);
        lemma2_to64();
    }
    let dl = bake(&ll, 0, Tracked(m));
    let dof = bake(&of, 1, Tracked(m));
    let dml = bake(&ml, 2, Tracked(m));
    Some((SeqTabs { ll, of, ml, dl, dof, dml }, a2 + u2))
}

/// The bitstream part (`seq_body`).
#[verifier::rlimit(40)]
pub fn seq_body_exec(
    b: &[u8],
    window: u64,
    d: &mut FrameDec,
    olimit: usize,
    tabs: SeqTabs,
    a3: usize,
    n: usize,
    Ghost(st): Ghost<FrameState>,
    Ghost(ts): Ghost<SeqTables>,
    Tracked(m): Tracked<&mut Meter>,
) -> (ok: Step)
    requires
        b@.len() < BITS_MAX,
        a3 <= b@.len(),
        seqtabs_is(&tabs, ts),
        dec_is(old(d), st),
        old(d).lits@.len() <= 131072,
        old(d).out@.len() <= olimit <= MAX_LIMIT,
        olimit - old(d).out@.len() <= 131072,
    ensures
        final(d).out@.len() >= old(d).out@.len(),
        final(m).n <= old(m).n + 3 * (final(d).out@.len() - old(d).out@.len()) + 3,
        final(d).out@.len() <= olimit,
        ok is Done ==> final(d).out@.len() - old(d).out@.len() >= old(d).lits@.len(),
        match seq_body(b@, old(d).lits@, window as nat, st, ts, a3 as int, n as nat) {
            None => !(ok is Done),
            Some(st2) => match ok {
                Step::Done => {
                &&& dec_is(final(d), st2)
                &&& final(d).fstart == old(d).fstart
                &&& final(d).out@.subrange(0, old(d).fstart as int) == old(d).out@.subrange(0, old(d).fstart as int)
                &&& final(d).lits@ == old(d).lits@
                &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => old(d).fstart + st2.out.len() > olimit,
            },
        },
{
    let ghost lits = d.lits@;
    let ghost pre = d.out@.subrange(0, d.fstart as int);
    let s = slice_subrange(b, a3, b.len());
    let p = match bstart_exec(s) {
        None => {
            return Step::Bad;
        },
        Some(p) => p,
    };
    let l1 = tabs.ll.log as usize;
    let l2 = tabs.of.log as usize;
    let l3 = tabs.ml.log as usize;
    if l1 + l2 + l3 > p {
        return Step::Bad;
    }
    proof {
        lemma_pow2_le(l1 as nat, 9);
        lemma_pow2_le(l2 as nat, 9);
        lemma_pow2_le(l3 as nat, 9);
        assert(pow2(9) == 512) by {
            lemma2_to64();
        }
    }
    let sll = rd(s, p, l1 as u32) as u32;
    let sof = rd(s, p - l1, l2 as u32) as u32;
    let sml = rd(s, p - l1 - l2, l3 as u32) as u32;
    let fstart = d.fstart;
    let ghost st0 = SeqState {
        p: p - l1 - l2 - l3,
        sll: sll as nat,
        sof: sof as nat,
        sml: sml as nat,
        reps: st.reps,
        li: 0,
        out: st.out,
    };
    proof {
        assert(sstate((p - l1 - l2 - l3) as usize, sll, sof, sml, d.r1, d.r2, d.r3, 0, d.out@, fstart as int) == st0);
    }
    let res = crate::cpu::run_seqs(
        &tabs,
        s,
        d.lits.as_slice(),
        window,
        n,
        p - l1 - l2 - l3,
        sll,
        sof,
        sml,
        d.r1,
        d.r2,
        d.r3,
        &mut d.out,
        fstart,
        olimit,
        Ghost(ts),
        Tracked(m),
    );
    proof {
        lemma_seq_run_grows(ts, s@, lits, window as nat, n as nat, st0);
        assert(s@ == b@.subrange(a3 as int, b@.len() as int));
        assert(st0.sll == bits(s@, p - ts.ll.log, ts.ll.log));
        assert(st0.sof == bits(s@, p - ts.ll.log - ts.of.log, ts.of.log));
        assert(st0.sml == bits(s@, p - ts.ll.log - ts.of.log - ts.ml.log, ts.ml.log));
    }
    match res {
        Err(lim) => {
            proof {
                if let Some(fin) = seq_run(ts, s@, lits, window as nat, n as nat, st0) {
                    if fin.p == 0 {
                        let st2 = seq_body(b@, lits, window as nat, st, ts, a3 as int, n as nat).unwrap();
                        assert(st2.out.len() >= fin.out.len());
                    }
                }
            }
            if lim {
                Step::Limit
            } else {
                Step::Bad
            }
        },
        Ok(o) => {
            if o.p != 0 {
                return Step::Bad;
            }
            let rest = slice_subrange(d.lits.as_slice(), o.li, d.lits.len());
            if d.out.len() + rest.len() > olimit {
                return Step::Limit;
            }
            let ghost o1 = d.out@;
            d.out.extend_from_slice(rest);
            proof {
                m.n = m.n + rest@.len();
            }
            d.r1 = o.r1;
            d.r2 = o.r2;
            d.r3 = o.r3;
            d.seqt = Some(tabs);
            proof {
                let fin = seq_run(ts, s@, lits, window as nat, n as nat, st0).unwrap();
                assert(fout(o1, fstart as int) =~= fin.out);
                assert(d.out@ =~= o1 + rest@);
                assert(d.out@.subrange(0, fstart as int) =~= pre);
                assert(fout(d.out@, fstart as int) =~= fout(o1, fstart as int) + lits.subrange(o.li as int, lits.len() as int));
            }
            Step::Done
        },
    }
}

/// The sequences section `b` of a block whose literals are in `d.lits`
/// (`seq_section`). Fails early, with the spec's result too large, once
/// the output passes `olimit`.
fn seq_section_exec(b: &[u8], window: u64, d: &mut FrameDec, olimit: usize, Ghost(st): Ghost<FrameState>, Tracked(m): Tracked<&mut Meter>) -> (ok: Step)
    requires
        b@.len() < BITS_MAX,
        dec_is(old(d), st),
        old(d).lits@.len() <= 131072,
        old(d).out@.len() <= olimit <= MAX_LIMIT,
        olimit - old(d).out@.len() <= 131072,
    ensures
        final(d).out@.len() >= old(d).out@.len(),
        final(m).n <= old(m).n + SEQ_HDR_WORK + 24 * b@.len() + 3 * (final(d).out@.len() - old(d).out@.len()) + 3,
        final(d).out@.len() <= olimit,
        ok is Done ==> final(d).out@.len() - old(d).out@.len() >= old(d).lits@.len(),
        match seq_section(b@, old(d).lits@, window as nat, st) {
            None => !(ok is Done),
            Some(st2) => match ok {
                Step::Done => {
                &&& dec_is(final(d), st2)
                &&& final(d).fstart == old(d).fstart
                &&& final(d).out@.subrange(0, old(d).fstart as int) == old(d).out@.subrange(0, old(d).fstart as int)
                &&& final(d).lits@ == old(d).lits@
                &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => old(d).fstart + st2.out.len() > olimit,
            },
        },
{
    let ghost lits = d.lits@;
    let ghost pre = d.out@.subrange(0, d.fstart as int);
    proof {
        lemma_seq_section(b@, lits, window as nat, st);
    }
    let (n, h) = match nb_seq_exec(b) {
        None => {
            return Step::Bad;
        },
        Some(x) => x,
    };
    if n == 0 {
        if h != b.len() {
            return Step::Bad;
        }
        if d.out.len() + d.lits.len() > olimit {
            return Step::Limit;
        }
        d.out.extend_from_slice(d.lits.as_slice());
        proof {
            m.n = m.n + lits.len();
            assert(d.out@.subrange(0, d.fstart as int) =~= pre);
            assert(fout(d.out@, d.fstart as int) =~= st.out + lits);
        }
        return Step::Done;
    }
    if h + 1 > b.len() || b[h] % 4 != 0 {
        return Step::Bad;
    }
    let (tabs, a3) = match seq_hdr_exec(b, h, &d.seqt, Ghost(st), Tracked(m)) {
        None => {
            return Step::Bad;
        },
        Some(x) => x,
    };
    let ghost ts = seq_hdr(b@, h as int, st).unwrap().0;
    seq_body_exec(b, window, d, olimit, tabs, a3, n, Ghost(st), Ghost(ts), Tracked(m))
}

/// The most steps a compressed block takes besides those linear in its
/// size and output: a Huffman tree and three sequence tables.
pub spec const CBLOCK_WORK: nat = 19603;

/// A compressed block (`compressed_block`).
#[verifier::rlimit(40)]
pub fn compressed_block_exec(b: &[u8], window: u64, bmax: usize, d: &mut FrameDec, olimit: usize, Ghost(st): Ghost<FrameState>, Tracked(m): Tracked<&mut Meter>) -> (ok: Step)
    requires
        b@.len() < BITS_MAX,
        bmax <= 131072,
        dec_is(old(d), st),
        old(d).out@.len() <= olimit <= MAX_LIMIT,
    ensures
        // Work: linear in the block and in the output it adds (or, if it
        // fails, the literals it may have decoded).
        final(d).out@.len() >= old(d).out@.len(),
        final(m).n <= old(m).n + CBLOCK_WORK + 24 * b@.len() + 6 * bmax + 3 * (final(d).out@.len() - old(d).out@.len()),
        final(d).out@.len() <= olimit,
        final(d).out@.len() <= old(d).out@.len() + bmax,
        ok is Done ==> final(m).n <= old(m).n + CBLOCK_WORK + 24 * b@.len() + 9 * (final(d).out@.len() - old(d).out@.len()),
        match compressed_block(b@, window as nat, bmax as nat, st) {
            None => !(ok is Done),
            Some(st2) => match ok {
                Step::Done => {
                &&& dec_is(final(d), st2)
                &&& final(d).fstart == old(d).fstart
                &&& final(d).out@.subrange(0, old(d).fstart as int) == old(d).out@.subrange(0, old(d).fstart as int)
                &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => old(d).fstart + st2.out.len() > olimit,
            },
        },
{
    let ghost hc = old_huf_code(&d.huf);
    let used = match lit_section_exec(b, bmax, &mut d.huf, &mut d.lits, Tracked(m)) {
        None => {
            return Step::Bad;
        },
        Some(u) => u,
    };
    let ghost l = lit_section(b@, bmax as nat, hc).unwrap();
    let ghost st1 = FrameState { huf: l.huf, ..st };
    // The block may not grow the output by more than `bmax`.
    let blim = if olimit - d.out.len() > bmax { d.out.len() + bmax } else { olimit };
    let ok = seq_section_exec(slice_subrange(b, used, b.len()), window, d, blim, Ghost(st1), Tracked(m));
    proof {
        let r = seq_section(b@.subrange(used as int, b@.len() as int), l.lits, window as nat, st1);
        if r is Some {
            let st2 = r.unwrap();
            if ok is Limit {
                assert(old(d).fstart + st2.out.len() > blim);
            }
        }
    }
    ok
}

} // verus!
