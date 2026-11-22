//! Kraft sums: when a prefix code the spec accepts is a valid canonical
//! code (`huffman::valid_code`), so that the Huffman table builder accepts
//! it too.
use crate::huffman::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// The code space a code length takes, out of 2^15.
pub open spec fn term(v: u8) -> nat {
    if v == 0 || v > 15 {
        0
    } else {
        pow2((15 - v) as nat)
    }
}

/// The code space the first `n` code lengths take.
pub open spec fn kr(s: Seq<u8>, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        kr(s, n - 1) + term(s[n - 1])
    }
}

pub open spec fn kraft(s: Seq<u8>) -> nat {
    kr(s, s.len() as int)
}

/// All lengths at most 15.
pub open spec fn short(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 15
}

/// The code space lengths `1..=l` take among the first `n` symbols.
pub open spec fn kb(s: Seq<u8>, l: nat, n: int) -> nat
    decreases l,
{
    if l == 0 {
        0
    } else {
        kb(s, (l - 1) as nat, n) + count_below(s, l, n) * pow2((15 - l) as nat)
    }
}

pub proof fn lemma_term_bound(v: u8)
    ensures
        term(v) <= 16384,
        v != 0 && v <= 15 ==> term(v) >= 1,
{
    if v != 0 && v <= 15 {
        lemma_pow2_pos((15 - v) as nat);
        if v > 1 {
            lemma_pow2_strictly_increases((15 - v) as nat, 14);
        }
        lemma2_to64();
    }
}

proof fn lemma_kb_step(s: Seq<u8>, l: nat, n: int)
    requires
        1 <= n <= s.len(),
        l <= 15,
    ensures
        kb(s, l, n) == kb(s, l, n - 1) + if 1 <= s[n - 1] <= l {
            pow2((15 - s[n - 1]) as nat)
        } else {
            0
        },
    decreases l,
{
    if l > 0 {
        lemma_kb_step(s, (l - 1) as nat, n);
        let v = s[n - 1];
        let a = count_below(s, l, n - 1);
        let p = pow2((15 - l) as nat);
        if v as nat == l {
            assert(count_below(s, l, n) == a + 1);
            assert((a + 1) * p == a * p + p) by (nonlinear_arith);
            assert((15 - l) as nat == (15 - v) as nat);
        } else {
            assert(count_below(s, l, n) == a);
        }
    }
}

/// The Kraft sum, by length.
proof fn lemma_kr_kb(s: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
        short(s),
    ensures
        kr(s, n) == kb(s, 15, n),
    decreases n,
{
    if n == 0 {
        lemma_kb_zero(s, 15);
    } else {
        lemma_kr_kb(s, n - 1);
        lemma_kb_step(s, 15, n);
        assert(s[n - 1] <= 15);
    }
}

proof fn lemma_kb_zero(s: Seq<u8>, l: nat)
    ensures
        kb(s, l, 0) == 0,
    decreases l,
{
    if l > 0 {
        lemma_kb_zero(s, (l - 1) as nat);
        assert(count_below(s, l, 0) == 0);
        assert(0 * pow2((15 - l) as nat) == 0);
    }
}

proof fn lemma_kb_mono(s: Seq<u8>, l: nat, m: nat, n: int)
    requires
        l <= m,
    ensures
        kb(s, l, n) <= kb(s, m, n),
    decreases m,
{
    if l < m {
        lemma_kb_mono(s, l, (m - 1) as nat, n);
    }
}

/// `left(l)`, scaled to 2^15: the code space not taken by lengths `<= l`.
proof fn lemma_left_kb(s: Seq<u8>, l: nat)
    requires
        l <= 15,
    ensures
        left(s, l) * pow2((15 - l) as nat) == 32768 - kb(s, l, s.len() as int),
    decreases l,
{
    lemma2_to64();
    if l == 0 {
        assert(left(s, 0) == 1);
    } else {
        lemma_left_kb(s, (l - 1) as nat);
        let p = pow2((15 - l) as nat);
        lemma_pow2_adds(1, (15 - l) as nat);
        assert(pow2((15 - (l - 1)) as nat) == 2 * p);
        let a = left(s, (l - 1) as nat);
        let c = count(s, l) as int;
        assert(left(s, l) == 2 * a - c);
        assert((2 * a - c) * p == a * (2 * p) - c * p) by (nonlinear_arith);
    }
}

/// No code length at all: nothing is taken.
proof fn lemma_kr_zero(s: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
        count_below(s, 0, n) == n,
    ensures
        kr(s, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_count_below_le_n(s, 0, n - 1);
        if s[n - 1] != 0 {
            assert(count_below(s, 0, n) == count_below(s, 0, n - 1));
        }
        lemma_kr_zero(s, n - 1);
    }
}

proof fn lemma_count_below_le_n(s: Seq<u8>, l: nat, n: int)
    requires
        0 <= n,
    ensures
        count_below(s, l, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_below_le_n(s, l, n - 1);
    }
}

/// Kraft's equality makes a valid code.
pub proof fn lemma_kraft_valid(s: Seq<u8>)
    requires
        short(s),
        kraft(s) == 32768,
    ensures
        valid_code(s),
{
    let n = s.len() as int;
    lemma_kr_kb(s, n);
    assert forall|l: nat| 1 <= l <= MAX_BITS implies #[trigger] left(s, l) >= 0 by {
        lemma_left_kb(s, l);
        lemma_kb_mono(s, l, 15, n);
        lemma_pow2_pos((15 - l) as nat);
        let p = pow2((15 - l) as nat) as int;
        if left(s, l) < 0 {
            assert(left(s, l) * p < 0) by (nonlinear_arith)
                requires
                    left(s, l) < 0,
                    p > 0,
            ;
        }
    }
    lemma_left_kb(s, 15);
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(((15 - 15nat) as nat) == 0nat);
    assert(left(s, 15) * pow2(0) == 32768 - kb(s, 15, n));
    assert(left(s, 15) == 0) by (nonlinear_arith)
        requires
            left(s, 15) * pow2(0) == 32768 - kb(s, 15, n),
            pow2(0) == 1,
            kb(s, 15, n) == 32768,
    ;
    if used(s) == 0 {
        lemma_count_below_le_n(s, 0, n);
        lemma_kr_zero(s, n);
    }
    if used(s) == 1 {
    } else {
        assert(used(s) >= 2);
    }
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] as nat <= MAX_BITS by {
        assert(s[i] <= 15);
    }
}

// ---------------------------------------------------------------------------
// Sums of sequences built a piece at a time
// ---------------------------------------------------------------------------

proof fn lemma_kr_prefix(s: Seq<u8>, t: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
        n <= t.len(),
        forall|i: int| 0 <= i < n ==> s[i] == t[i],
    ensures
        kr(s, n) == kr(t, n),
    decreases n,
{
    if n > 0 {
        lemma_kr_prefix(s, t, n - 1);
    }
}

pub proof fn lemma_kraft_push(s: Seq<u8>, v: u8)
    ensures
        kraft(s.push(v)) == kraft(s) + term(v),
{
    lemma_kr_prefix(s, s.push(v), s.len() as int);
}

/// Zeros take no code space.
pub proof fn lemma_kraft_zeros(s: Seq<u8>, k: nat)
    ensures
        kraft(s + Seq::new(k, |i: int| 0u8)) == kraft(s),
    decreases k,
{
    let z = Seq::new(k, |i: int| 0u8);
    if k == 0 {
        assert(s + z == s);
    } else {
        let z1 = Seq::new((k - 1) as nat, |i: int| 0u8);
        lemma_kraft_zeros(s, (k - 1) as nat);
        assert(s + z == (s + z1).push(0u8));
        lemma_kraft_push(s + z1, 0u8);
    }
}

/// `k` copies of `v`.
pub proof fn lemma_kraft_rep(s: Seq<u8>, v: u8, k: nat)
    ensures
        kraft(s + Seq::new(k, |i: int| v)) == kraft(s) + k * term(v),
    decreases k,
{
    let z = Seq::new(k, |i: int| v);
    if k == 0 {
        assert(s + z == s);
    } else {
        let z1 = Seq::new((k - 1) as nat, |i: int| v);
        lemma_kraft_rep(s, v, (k - 1) as nat);
        assert(s + z == (s + z1).push(v));
        lemma_kraft_push(s + z1, v);
        assert((k - 1) * term(v) + term(v) == k * term(v)) by (nonlinear_arith);
    }
}

proof fn lemma_kr_update(s: Seq<u8>, j: int, v: u8, n: int)
    requires
        0 <= j < s.len(),
        0 <= n <= s.len(),
    ensures
        kr(s.update(j, v), n) + (if j < n {
            term(s[j])
        } else {
            0
        }) == kr(s, n) + (if j < n {
            term(v)
        } else {
            0
        }),
    decreases n,
{
    if n > 0 {
        lemma_kr_update(s, j, v, n - 1);
    }
}

/// Setting one length.
pub proof fn lemma_kraft_update(s: Seq<u8>, j: int, v: u8)
    requires
        0 <= j < s.len(),
    ensures
        kraft(s.update(j, v)) + term(s[j]) == kraft(s) + term(v),
{
    lemma_kr_update(s, j, v, s.len() as int);
}

proof fn lemma_kr_bound(s: Seq<u8>, n: int)
    requires
        0 <= n,
    ensures
        kr(s, n) <= 16384 * n,
    decreases n,
{
    if n > 0 {
        lemma_kr_bound(s, n - 1);
        lemma_term_bound(s[n - 1]);
    }
}

pub proof fn lemma_kraft_bound(s: Seq<u8>)
    ensures
        kraft(s) <= 16384 * s.len(),
{
    lemma_kr_bound(s, s.len() as int);
}

/// The number of nonzero lengths among the first `n`.
pub open spec fn nz(s: Seq<u8>, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        nz(s, n - 1) + if s[n - 1] != 0 {
            1nat
        } else {
            0
        }
    }
}

proof fn lemma_nz_count(s: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        nz(s, n) + count_below(s, 0, n) == n,
    decreases n,
{
    if n > 0 {
        lemma_nz_count(s, n - 1);
    }
}

pub proof fn lemma_used_nz(s: Seq<u8>)
    ensures
        used(s) == nz(s, s.len() as int),
{
    lemma_nz_count(s, s.len() as int);
}

proof fn lemma_nz_update(s: Seq<u8>, j: int, v: u8, n: int)
    requires
        0 <= j < s.len(),
        0 <= n <= s.len(),
    ensures
        nz(s.update(j, v), n) + (if j < n && s[j] != 0 {
            1nat
        } else {
            0
        }) == nz(s, n) + (if j < n && v != 0 {
            1nat
        } else {
            0
        }),
    decreases n,
{
    if n > 0 {
        lemma_nz_update(s, j, v, n - 1);
    }
}

pub proof fn lemma_used_update(s: Seq<u8>, j: int, v: u8)
    requires
        0 <= j < s.len(),
    ensures
        used(s.update(j, v)) + (if s[j] != 0 {
            1nat
        } else {
            0
        }) == used(s) + (if v != 0 {
            1nat
        } else {
            0
        }),
{
    lemma_used_nz(s);
    lemma_used_nz(s.update(j, v));
    lemma_nz_update(s, j, v, s.len() as int);
}

proof fn lemma_nz_zeros(n: nat, k: int)
    requires
        0 <= k <= n,
    ensures
        nz(Seq::new(n, |i: int| 0u8), k) == 0,
        kr(Seq::new(n, |i: int| 0u8), k) == 0,
    decreases k,
{
    if k > 0 {
        lemma_nz_zeros(n, k - 1);
    }
}

pub proof fn lemma_zeros(n: nat)
    ensures
        used(Seq::new(n, |i: int| 0u8)) == 0,
        kraft(Seq::new(n, |i: int| 0u8)) == 0,
{
    lemma_nz_zeros(n, n as int);
    lemma_used_nz(Seq::new(n, |i: int| 0u8));
}

/// One nonzero length below 16 is a valid (zero-bit) code.
pub proof fn lemma_single_valid(s: Seq<u8>)
    requires
        short(s),
        used(s) == 1,
    ensures
        valid_code(s),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] as nat <= MAX_BITS by {
        assert(s[i] <= 15);
    }
}

} // verus!
