//! A byte mask's `movemask`, bit by bit.
use crate::ops::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Bit `k` of `m`.
pub open spec fn bit64(m: u64, k: int) -> bool {
    (m >> (k as u64)) & 1u64 == 1u64
}

pub proof fn lemma_movemask_bound(a: Seq<u8>)
    ensures
        movemask(a) < pow2(a.len()),
    decreases a.len(),
{
    reveal(pow2);
    if a.len() == 0 {
        lemma2_to64();
    } else {
        lemma_movemask_bound(a.drop_first());
        lemma_pow2_unfold(a.len());
    }
}

/// Bit `k` of `movemask(a)` is the top bit of lane `k`, and the bits past
/// the last lane are zero.
pub proof fn lemma_movemask_bits(a: Seq<u8>, r: u64)
    requires
        a.len() <= 64,
        r as nat == movemask(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> #[trigger] bit64(r, k) == (a[k] >= 128),
        forall|k: int| a.len() <= k < 64 ==> !#[trigger] bit64(r, k),
    decreases a.len(),
{
    if a.len() == 0 {
        assert forall|k: int| 0 <= k < 64 implies !#[trigger] bit64(r, k) by {
            let kk = k as u64;
            assert((0u64 >> kk) & 1u64 == 0u64) by (bit_vector);
        }
    } else {
        let t = a.drop_first();
        lemma_movemask_bound(t);
        lemma2_to64();
        lemma2_to64_rest();
        assert(pow2(t.len()) <= pow2(63)) by {
            if t.len() < 63 {
                lemma_pow2_strictly_increases(t.len(), 63);
            }
        }
        let r2 = movemask(t) as u64;
        let b0: u64 = if a[0] >= 128 { 1 } else { 0 };
        assert(r == b0 + 2 * r2);
        lemma_movemask_bits(t, r2);
        assert forall|k: int| 0 <= k < 64 implies (if k < a.len() {
            #[trigger] bit64(r, k) == (a[k] >= 128)
        } else {
            !bit64(r, k)
        }) by {
            if k == 0 {
                assert((r >> 0u64) & 1u64 == b0) by (bit_vector)
                    requires
                        r == b0 + 2 * r2,
                        b0 <= 1,
                        r2 < 0x8000_0000_0000_0000u64,
                ;
            } else {
                let kk = k as u64;
                let k1 = (k - 1) as u64;
                assert((r >> kk) & 1u64 == (r2 >> k1) & 1u64) by (bit_vector)
                    requires
                        r == b0 + 2 * r2,
                        b0 <= 1,
                        r2 < 0x8000_0000_0000_0000u64,
                        1 <= kk < 64,
                        k1 == kk - 1,
                ;
                assert(bit64(r2, k - 1) == bit64(r, k));
                if k < a.len() {
                    assert(t[k - 1] == a[k]);
                }
            }
        }
    }
}

/// `movemask(a)` is zero exactly when no lane has its top bit set.
pub proof fn lemma_movemask_zero(a: Seq<u8>)
    ensures
        movemask(a) == 0 <==> (forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] < 128),
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.drop_first();
        lemma_movemask_zero(t);
        if movemask(a) == 0 {
            assert forall|k: int| 0 <= k < a.len() implies #[trigger] a[k] < 128 by {
                if k > 0 {
                    assert(t[k - 1] == a[k]);
                }
            }
        }
        if forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] < 128 {
            assert forall|k: int| 0 <= k < t.len() implies #[trigger] t[k] < 128 by {
                assert(t[k] == a[k + 1]);
            }
        }
    }
}

} // verus!
