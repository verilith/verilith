//! Common shapes of operands, with lemmas that evaluate the intrinsics on
//! them.
use crate::lanes::*;
use crate::ops::*;
use vstd::prelude::*;

verus! {

/// Entry `k` (0..4) of a 4-entry pattern.
pub open spec fn pick4(c0: int, c1: int, c2: int, c3: int, k: int) -> int {
    if k == 0 {
        c0
    } else if k == 1 {
        c1
    } else if k == 2 {
        c2
    } else {
        c3
    }
}

/// A `pshufb` mask, `n` bytes long, under which byte `i` takes byte
/// `pick4(.., i % 4)` of its own 4-byte group, or zero where that is
/// negative.
pub open spec fn group4_mask(c0: int, c1: int, c2: int, c3: int, n: nat) -> Seq<u8> {
    Seq::new(
        n,
        |i: int|
            if pick4(c0, c1, c2, c3, i % 4) < 0 {
                128u8
            } else {
                (i % 16 - i % 4 + pick4(c0, c1, c2, c3, i % 4)) as u8
            },
    )
}

pub proof fn lemma_group4_shuffle(a: Seq<u8>, c0: int, c1: int, c2: int, c3: int)
    requires
        a.len() % 16 == 0,
        -1 <= c0 < 4,
        -1 <= c1 < 4,
        -1 <= c2 < 4,
        -1 <= c3 < 4,
    ensures
        shuffle8_lanes(a, group4_mask(c0, c1, c2, c3, a.len())).len() == a.len(),
        forall|i: int|
            0 <= i < a.len() ==> #[trigger] shuffle8_lanes(a, group4_mask(c0, c1, c2, c3, a.len()))[i] == if pick4(
                c0,
                c1,
                c2,
                c3,
                i % 4,
            ) < 0 {
                0u8
            } else {
                a[i - i % 4 + pick4(c0, c1, c2, c3, i % 4)]
            },
{
    let m = group4_mask(c0, c1, c2, c3, a.len());
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] shuffle8_lanes(a, m)[i] == if pick4(
        c0,
        c1,
        c2,
        c3,
        i % 4,
    ) < 0 {
        0u8
    } else {
        a[i - i % 4 + pick4(c0, c1, c2, c3, i % 4)]
    } by {
        let c = pick4(c0, c1, c2, c3, i % 4);
        if c >= 0 {
            assert(0 <= i % 16 - i % 4 + c < 16);
            assert((i / 16) * 16 + (i % 16 - i % 4 + c) == i - i % 4 + c);
        }
    }
}

/// Byte shifts by whole 32-bit lanes move the lanes.
pub proof fn lemma_bslli_u32s(b: Seq<u8>, s: int)
    requires
        b.len() % 16 == 0,
        0 <= s <= 4,
    ensures
        u32s(bslli_lanes(b, 4 * s)).len() == u32s(b).len(),
        forall|k: int|
            0 <= k < u32s(b).len() ==> #[trigger] u32s(bslli_lanes(b, 4 * s))[k] == if k % 4 >= s {
                u32s(b)[k - s]
            } else {
                0u32
            },
{
    let r = bslli_lanes(b, 4 * s);
    assert forall|k: int| 0 <= k < u32s(b).len() implies #[trigger] u32s(r)[k] == if k % 4 >= s {
        u32s(b)[k - s]
    } else {
        0u32
    } by {
        assert((4 * k) % 16 == 4 * (k % 4));
        assert((4 * k + 1) % 16 == 4 * (k % 4) + 1);
        assert((4 * k + 2) % 16 == 4 * (k % 4) + 2);
        assert((4 * k + 3) % 16 == 4 * (k % 4) + 3);
        if k % 4 >= s {
            assert(r[4 * k] == b[4 * (k - s)]);
            assert(r[4 * k + 1] == b[4 * (k - s) + 1]);
            assert(r[4 * k + 2] == b[4 * (k - s) + 2]);
            assert(r[4 * k + 3] == b[4 * (k - s) + 3]);
        } else {
            assert(le32(0u8, 0u8, 0u8, 0u8) == 0u32) by (compute);
        }
    }
}

/// `shuffle_epi32::<0xff>` copies lane 3 of each 4-lane group to the group.
pub proof fn lemma_shuffle32_splat3(a: Seq<u32>)
    requires
        a.len() % 4 == 0,
    ensures
        shuffle32_lanes(a, 0xff).len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] shuffle32_lanes(a, 0xff)[i] == a[(i / 4) * 4 + 3],
{
    reveal_with_fuel(pow2_spec, 7);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] shuffle32_lanes(a, 0xff)[i] == a[(i / 4) * 4 + 3] by {
        let k = i % 4;
        assert(pow2_spec(0) == 1 && pow2_spec(2) == 4 && pow2_spec(4) == 16 && pow2_spec(6) == 64);
        if k == 0 {
            assert((255int / pow2_spec(0) as int) % 4 == 3);
        } else if k == 1 {
            assert((255int / pow2_spec(2) as int) % 4 == 3);
        } else if k == 2 {
            assert((255int / pow2_spec(4) as int) % 4 == 3);
        } else {
            assert((255int / pow2_spec(6) as int) % 4 == 3);
        }
    }
}

/// The 32-bit lanes of a zero vector.
pub proof fn lemma_u32s_splat0(n: nat)
    requires
        n % 4 == 0,
    ensures
        u32s(splat8(0u8, n)) == splat32(0u32, n / 4),
{
    assert(le32(0u8, 0u8, 0u8, 0u8) == 0u32) by (compute);
    assert(u32s(splat8(0u8, n)) =~= splat32(0u32, n / 4));
}

} // verus!
