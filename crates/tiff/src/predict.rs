//! Horizontal differencing undone (§14), proven against `spec::unpredict`.
use crate::spec::*;
use verilith_core::prims::{get, set};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_le_val_bound(d: Seq<u8>, i: int, k: nat)
    ensures
        le_val(d, i, k) < pow2(8 * k),
    decreases k,
{
    if k == 0 {
        lemma2_to64();
    } else {
        lemma_le_val_bound(d, i + 1, (k - 1) as nat);
        lemma_pow2_adds(8, (8 * (k - 1)) as nat);
        assert(8 + 8 * (k - 1) == 8 * k);
        lemma2_to64();
        let r = le_val(d, i + 1, (k - 1) as nat);
        let p = pow2((8 * (k - 1)) as nat);
        assert(d[i] as nat + 256 * r < 256 * p);
    }
}

/// `x / 2^(8 (j + 1)) == (x / 256) / 2^(8 j)`.
proof fn lemma_byte_shift(x: nat, j: nat)
    ensures
        x / pow2(8 * (j + 1)) == (x / 256) / pow2(8 * j),
{
    lemma2_to64();
    lemma_pow2_adds(8, 8 * j);
    assert(8 + 8 * j == 8 * (j + 1));
    lemma_pow2_pos(8 * j);
    lemma_div_denominator(x as int, 256, pow2(8 * j) as int);
}

/// Bytes that are `x`'s, least significant first, read back as `x`.
pub proof fn lemma_le_val_of(d: Seq<u8>, i: int, k: nat, x: nat)
    requires
        x < pow2(8 * k),
        forall|j: int| 0 <= j < k ==> #[trigger] d[i + j] == byte_of(x, j as nat),
    ensures
        le_val(d, i, k) == x,
    decreases k,
{
    lemma2_to64();
    if k == 0 {
        assert(pow2(0) == 1);
    } else {
        let y = x / 256;
        assert forall|j: int| 0 <= j < k - 1 implies #[trigger] d[(i + 1) + j] == byte_of(y, j as nat) by {
            assert(d[i + (j + 1)] == byte_of(x, (j + 1) as nat));
            lemma_byte_shift(x, j as nat);
            assert(i + (j + 1) == (i + 1) + j);
        }
        lemma_pow2_adds(8, (8 * (k - 1)) as nat);
        assert(8 + 8 * (k - 1) == 8 * k);
        lemma_multiply_divide_lt(x as int, 256, pow2((8 * (k - 1)) as nat) as int);
        lemma_mul_is_commutative(256, pow2((8 * (k - 1)) as nat) as int);
        lemma_le_val_of(d, i + 1, (k - 1) as nat, y);
        assert(d[i + 0] == byte_of(x, 0));
        assert(x / pow2(0) == x);
        lemma_fundamental_div_mod(x as int, 256);
    }
}

/// The bytes of a value read from bytes are those bytes.
pub proof fn lemma_bytes_of(d: Seq<u8>, i: int, k: nat, j: nat)
    requires
        j < k,
    ensures
        byte_of(le_val(d, i, k), j) == d[i + j],
    decreases k,
{
    lemma2_to64();
    let v = le_val(d, i, k);
    let r = le_val(d, i + 1, (k - 1) as nat);
    assert(v == d[i] as nat + 256 * r);
    if j == 0 {
        assert(v / pow2(0) == v);
        lemma_mod_multiples_vanish(r as int, d[i] as int, 256);
        lemma_mul_is_commutative(256, r as int);
        lemma_small_mod(d[i] as nat, 256);
    } else {
        lemma_bytes_of(d, i + 1, (k - 1) as nat, (j - 1) as nat);
        lemma_byte_shift(v, (j - 1) as nat);
        assert(v / 256 == r) by {
            lemma_fundamental_div_mod_converse(v as int, 256, r as int, d[i] as int);
        }
        assert(i + 1 + (j - 1) == i + j);
        assert((j - 1) as nat + 1 == j);
    }
}

/// `le_val` of a subrange is `le_val` of the whole, shifted.
pub proof fn lemma_le_val_sub(d: Seq<u8>, a: int, b: int, i: int, k: nat)
    requires
        0 <= a <= b <= d.len(),
        0 <= i,
        i + k <= b - a,
    ensures
        le_val(d.subrange(a, b), i, k) == le_val(d, a + i, k),
    decreases k,
{
    if k > 0 {
        lemma_le_val_sub(d, a, b, i + 1, (k - 1) as nat);
        assert(a + (i + 1) == a + i + 1);
    }
}

/// The `k` bytes at `i` as a little-endian number (`spec::le_val`).
fn read_le(v: &[u8], i: usize, k: usize) -> (r: u64)
    requires
        1 <= k <= 4,
        i + k <= v@.len(),
    ensures
        r as nat == le_val(v@, i as int, k as nat),
{
    let l = v.len();
    let mut acc: u64 = 0;
    let mut j: usize = k;
    while j > 0
        invariant
            l == v@.len(),
            1 <= k <= 4,
            i + k <= v@.len(),
            j <= k,
            acc as nat == le_val(v@, i + j, (k - j) as nat),
        decreases j,
    {
        proof {
            lemma_le_val_bound(v@, i + j, (k - j) as nat);
            if 8 * (k - j) < 24 { lemma_pow2_strictly_increases(8 * (k - j) as nat, 24); }
            lemma2_to64();
            assert(pow2(24) == 0x100_0000);
            assert((k - (j - 1)) as nat == (k - j) as nat + 1);
            assert(i + (j - 1) + 1 == i + j);
        }
        j = j - 1;
        acc = acc * 256 + get(v, i + j) as u64;
    }
    acc
}

/// Writes the `k` bytes of `x` at `i`, least significant first.
fn write_le(v: &mut [u8], i: usize, k: usize, x: u64)
    requires
        1 <= k <= 4,
        i + k <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|j: int| 0 <= j < final(v)@.len() ==> #[trigger] final(v)@[j] == if i <= j < i + k {
            byte_of(x as nat, (j - i) as nat)
        } else {
            old(v)@[j]
        },
{
    let ghost o = v@;
    let l = v.len();
    let mut j: usize = 0;
    while j < k
        invariant
            l == v@.len(),
            1 <= k <= 4,
            i + k <= o.len(),
            v@.len() == o.len(),
            j <= k,
            forall|t: int| 0 <= t < v@.len() ==> #[trigger] v@[t] == if i <= t < i + j {
                byte_of(x as nat, (t - i) as nat)
            } else {
                o[t]
            },
        decreases k - j,
    {
        let sh = (8 * j) as u64;
        let b = (x >> sh) as u8;
        proof {
            lemma_u64_shr_is_div(x, sh);
            let y = x >> sh;
            assert(y as u8 == (y % 256) as u8) by (bit_vector);
        }
        set(v, i + j, b);
        j = j + 1;
    }
}

/// Undoes horizontal differencing in each row of `rb` bytes of `v`:
/// samples of `k` bytes, `stride` per pixel (`spec::unpredict`).
pub fn unpredict_exec(v: &mut [u8], rb: usize, k: usize, stride: usize)
    requires
        k == 1 || k == 2 || k == 4,
        1 <= stride,
        1 <= rb,
        rb % k == 0,
        old(v)@.len() % (rb as nat) == 0,
    ensures
        final(v)@ == unpredict(old(v)@, rb as nat, k as nat, stride as nat),
{
    let ghost o = v@;
    let ghost want = unpredict(o, rb as nat, k as nat, stride as nat);
    let n = v.len();
    let ns = rb / k;
    proof {
        lemma_fundamental_div_mod(rb as int, k as int);
        lemma2_to64();
    }
    let modulus: u64 = if k == 1 { 0x100 } else if k == 2 { 0x1_0000 } else { 0x1_0000_0000 };
    proof {
        assert(modulus as nat == pow2(8 * k as nat));
    }
    let mut base: usize = 0;
    while base < n
        invariant
            k == 1 || k == 2 || k == 4,
            1 <= stride,
            1 <= rb,
            rb % k == 0,
            ns * k == rb,
            n == v@.len(),
            n == o.len(),
            n % rb == 0,
            base % rb == 0,
            base <= n,
            modulus as nat == pow2(8 * k as nat),
            want == unpredict(o, rb as nat, k as nat, stride as nat),
            forall|i: int| 0 <= i < base ==> #[trigger] v@[i] == want[i],
            forall|i: int| base <= i < n ==> #[trigger] v@[i] == o[i],
        decreases n - base,
    {
        proof {
            crate::chunk::lemma_multiples(base as int, n as int, rb as int);
        }
        let ghost row = o.subrange(base as int, base + rb);
        let mut s: usize = 0;
        while s < ns
            invariant
                k == 1 || k == 2 || k == 4,
                1 <= stride,
                ns * k == rb,
                base + rb <= n,
                n == v@.len(),
                n == o.len(),
                s <= ns,
                modulus as nat == pow2(8 * k as nat),
                row == o.subrange(base as int, base + rb),
                forall|i: int| 0 <= i < base ==> #[trigger] v@[i] == want[i],
                forall|i: int| base + s * k <= i < n ==> #[trigger] v@[i] == o[i],
                forall|t: int, j: int|
                    #![trigger v@[base + t * k + j]]
                    0 <= t < s && 0 <= j < k ==> v@[base + t * k + j] == byte_of(
                        undiff(row, t as nat, stride as nat, k as nat),
                        j as nat,
                    ),
            decreases ns - s,
        {
            proof {
                lemma_mul_inequality(s as int + 1, ns as int, k as int);
                lemma_mul_is_distributive_add_other_way(k as int, s as int, 1);
            }
            let at = base + s * k;
            let cur = read_le(v, at, k);
            proof {
                assert(v@.subrange(at as int, at + k) =~= o.subrange(at as int, at + k));
                assert forall|j: int| 0 <= j < k implies #[trigger] v@[at + j] == o[at + j] by {}
                lemma_le_val_eq(v@, o, at as int, k as nat);
                lemma_le_val_sub(o, base as int, base + rb, (s * k) as int, k as nat);
            }
            if s >= stride {
                let pt = base + (s - stride) * k;
                let prev = read_le(v, pt, k);
                proof {
                    let t = (s - stride) as int;
                    let u = undiff(row, t as nat, stride as nat, k as nat);
                    assert forall|j: int| 0 <= j < k implies #[trigger] v@[pt + j] == byte_of(u, j as nat) by {
                        assert(pt + j == base + t * k + j);
                    }
                    reveal_with_fuel(undiff, 2);
                    lemma_pow2_pos(8 * k as nat);
                    assert(u < pow2(8 * k as nat)) by {
                        if t >= stride {
                            lemma_mod_bound(
                                (undiff(row, (t - stride) as nat, stride as nat, k as nat) + le_val(row, (t * k) as int, k as nat)) as int,
                                pow2(8 * k as nat) as int,
                            );
                        } else {
                            lemma_le_val_bound(row, (t * k) as int, k as nat);
                        }
                    }
                    lemma_le_val_of(v@, pt as int, k as nat, u);
                    lemma_le_val_bound(o, at as int, k as nat);
                    if 8 * k < 32 { lemma_pow2_strictly_increases(8 * k as nat, 32); }
                    lemma2_to64();
                    assert(pow2(32) == 0x1_0000_0000);
                }
                let x = (prev + cur) % modulus;
                write_le(v, at, k, x);
            } else {
                // The first pixel of the row is stored as it is.
                proof {
                    assert forall|j: int| 0 <= j < k implies #[trigger] v@[at + j] == byte_of(cur as nat, j as nat) by {
                        lemma_bytes_of(v@, at as int, k as nat, j as nat);
                    }
                }
            }
            proof {
                reveal_with_fuel(undiff, 2);
                assert forall|t: int, j: int|
                    #![trigger v@[base + t * k + j]]
                    0 <= t < s + 1 && 0 <= j < k implies v@[base + t * k + j] == byte_of(
                        undiff(row, t as nat, stride as nat, k as nat),
                        j as nat,
                    ) by {
                    if t < s {
                        lemma_mul_inequality(t + 1, s as int, k as int);
                        lemma_mul_is_distributive_add_other_way(k as int, t, 1);
                    } else {
                        assert(base + t * k + j == at + j);
                    }
                }
                assert forall|i: int| base + (s + 1) * k <= i < n implies #[trigger] v@[i] == o[i] by {
                    lemma_mul_is_distributive_add_other_way(k as int, s as int, 1);
                }
            }
            s = s + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < base + rb implies #[trigger] v@[i] == want[i] by {
                if i >= base {
                    let x = i - base;
                    lemma_fundamental_div_mod(x, k as int);
                    let t = x / k as int;
                    let j = x % k as int;
                    lemma_fundamental_div_mod(base as int, rb as int);
                    lemma_mul_is_commutative(rb as int, base as int / rb as int);
                    lemma_fundamental_div_mod_converse(i, rb as int, base as int / rb as int, x);
                    assert(i / rb as int * rb as int == base);
                    assert(o.subrange(i / rb as int * rb as int, i / rb as int * rb as int + rb) == row);
                    assert(0 <= t < ns) by {
                        lemma_multiply_divide_lt(x, k as int, ns as int);
                        lemma_mul_is_commutative(k as int, ns as int);
                    }
                    assert(i == base + t * k + j) by {
                        lemma_mul_is_commutative(k as int, t);
                    }
                }
            }
            lemma_mod_add_multiples_vanish(base as int, rb as int);
        }
        base = base + rb;
    }
    proof {
        assert(v@ =~= want);
    }
}

/// Equal bytes, equal values.
proof fn lemma_le_val_eq(a: Seq<u8>, b: Seq<u8>, i: int, k: nat)
    requires
        forall|j: int| 0 <= j < k ==> #[trigger] a[i + j] == b[i + j],
    ensures
        le_val(a, i, k) == le_val(b, i, k),
    decreases k,
{
    if k > 0 {
        assert forall|j: int| 0 <= j < k - 1 implies #[trigger] a[(i + 1) + j] == b[(i + 1) + j] by {
            assert(a[i + (j + 1)] == b[i + (j + 1)]);
            assert(i + (j + 1) == (i + 1) + j);
        }
        lemma_le_val_eq(a, b, i + 1, (k - 1) as nat);
        assert(a[i + 0] == b[i + 0]);
    }
}

} // verus!
