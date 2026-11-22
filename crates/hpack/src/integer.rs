//! The verified integer decoder (RFC 7541 §5.1).
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub enum IntE {
    Short,
    Bad,
    Ok(u32, usize),
}

pub open spec fn int_matches(r: IntE, s: IntR) -> bool {
    match (r, s) {
        (IntE::Short, IntR::Short) => true,
        (IntE::Bad, IntR::Bad) => true,
        (IntE::Ok(v, e), IntR::Ok(sv, se)) => v as nat == sv && e as int == se,
        _ => false,
    }
}

const P128: [u64; 5] = [1, 128, 16384, 2097152, 268435456];

const P2: [u32; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

proof fn lemma_p128()
    ensures
        forall|i: int| 0 <= i < 5 ==> #[trigger] P128@[i] as nat == pow128(i as nat),
        forall|i: int| 0 <= i < 8 ==> #[trigger] P2@[i] as nat == pow2_8(i as nat),
        forall|i: int| 0 <= i < 5 ==> #[trigger] P128@[i] <= 268435456,
{
    assert(pow128(0) == 1);
    assert(pow128(1) == 128) by (compute);
    assert(pow128(2) == 16384) by (compute);
    assert(pow128(3) == 2097152) by (compute);
    assert(pow128(4) == 268435456) by (compute);
    assert(P128@[0] == 1 && P128@[1] == 128 && P128@[2] == 16384 && P128@[3] == 2097152 && P128@[4] == 268435456);
}

/// Decodes the integer with an `n`-bit prefix at `b[pos]`.
#[inline(always)]
pub fn decode(b: &[u8], pos: usize, n: u8) -> (r: IntE)
    requires
        4 <= n <= 7,
    ensures
        int_matches(r, int_dec(b@, pos as int, n as nat)),
        r matches IntE::Ok(_, e) ==> e <= b@.len(),
{
    proof {
        lemma_p128();
    }
    if pos >= b.len() {
        return IntE::Short;
    }
    let k = P2[n as usize] - 1;
    let first = (b[pos] as u32) % P2[n as usize];
    if first < k {
        return IntE::Ok(first, pos + 1);
    }
    let mut acc: u64 = k as u64;
    let mut p = pos + 1;
    let mut i: usize = 0;
    while p < b.len()
        invariant
            pos < p <= b@.len(),
            i <= 5,
            acc <= 0xFFFF_FFFF,
            int_dec(b@, pos as int, n as nat) == int_tail(b@, p as int, i as nat, acc as nat),
            forall|j: int| 0 <= j < 5 ==> #[trigger] P128@[j] as nat == pow128(j as nat),
            forall|j: int| 0 <= j < 5 ==> #[trigger] P128@[j] <= 268435456,
        decreases b@.len() - p,
    {
        if i >= 5 {
            return IntE::Bad;
        }
        let x = b[p];
        let m = P128[i];
        let lo = (x % 128) as u64;
        assert(lo * m <= 127 * 268435456) by (nonlinear_arith)
            requires
                lo <= 127,
                m <= 268435456,
        ;
        let add = lo * m;
        if acc + add > 0xFFFF_FFFF {
            return IntE::Bad;
        }
        acc = acc + add;
        if x < 128 {
            return IntE::Ok(acc as u32, p + 1);
        }
        p = p + 1;
        i = i + 1;
    }
    IntE::Short
}

} // verus!
