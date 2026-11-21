//! Facts about `spec::code` (bits read first bit most significant).
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

pub proof fn lemma_pow2_8(n: nat)
    requires
        n < 8,
    ensures
        pow2_8(n) == pow2(n),
{
    lemma2_to64();
}

pub proof fn lemma_code_bound(b: Seq<u8>, p: int, n: nat)
    ensures
        code(b, p, n) < pow2(n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_code_bound(b, p, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(bit(b, p + n - 1) <= 1);
    }
}

/// Reading `m + n` bits is reading `m` bits, then `n`.
pub proof fn lemma_code_split(b: Seq<u8>, p: int, m: nat, n: nat)
    ensures
        code(b, p, m + n) == code(b, p, m) * pow2(n) + code(b, p + m, n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_code_split(b, p, m, (n - 1) as nat);
        lemma_pow2_unfold(n);
        assert(code(b, p, m + n) == 2 * code(b, p, (m + n - 1) as nat) + bit(b, p + m + n - 1));
        assert(code(b, p + m, n) == 2 * code(b, p + m, (n - 1) as nat) + bit(b, p + m + n - 1));
        lemma_mul_is_associative(code(b, p, m) as int, pow2((n - 1) as nat) as int, 2);
        lemma_mul_is_commutative(pow2((n - 1) as nat) as int, 2);
    }
}

/// The top `l` of `n` bits.
pub proof fn lemma_code_top(b: Seq<u8>, p: int, n: nat, l: nat)
    requires
        l <= n,
    ensures
        code(b, p, n) / pow2((n - l) as nat) == code(b, p, l),
        code(b, p, n) % pow2((n - l) as nat) == code(b, p + l, (n - l) as nat),
{
    lemma_code_split(b, p, l, (n - l) as nat);
    lemma_code_bound(b, p + l, (n - l) as nat);
    lemma_pow2_pos((n - l) as nat);
    lemma_fundamental_div_mod_converse(
        code(b, p, n) as int,
        pow2((n - l) as nat) as int,
        code(b, p, l) as int,
        code(b, p + l, (n - l) as nat) as int,
    );
}

/// The 8 bits of byte `i` are the byte.
pub proof fn lemma_code_byte(b: Seq<u8>, i: int)
    requires
        0 <= i < b.len(),
    ensures
        code(b, 8 * i, 8) == b[i] as nat,
{
    let x = b[i];
    assert(forall|k: int| 0 <= k < 8 ==> #[trigger] ((8 * i + k) / 8) == i && (8 * i + k) % 8 == k)
        by {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] ((8 * i + k) / 8) == i && (8 * i + k)
            % 8 == k by {
            lemma_fundamental_div_mod_converse(8 * i + k, 8, i, k);
        }
    }
    assert(bit(b, 8 * i + 0) == (x as nat / 128) % 2);
    assert(bit(b, 8 * i + 1) == (x as nat / 64) % 2);
    assert(bit(b, 8 * i + 2) == (x as nat / 32) % 2);
    assert(bit(b, 8 * i + 3) == (x as nat / 16) % 2);
    assert(bit(b, 8 * i + 4) == (x as nat / 8) % 2);
    assert(bit(b, 8 * i + 5) == (x as nat / 4) % 2);
    assert(bit(b, 8 * i + 6) == (x as nat / 2) % 2);
    assert(bit(b, 8 * i + 7) == (x as nat / 1) % 2);
    assert(code(b, 8 * i, 8) == 2 * (2 * (2 * (2 * (2 * (2 * (2 * bit(b, 8 * i) + bit(b, 8 * i + 1))
        + bit(b, 8 * i + 2)) + bit(b, 8 * i + 3)) + bit(b, 8 * i + 4)) + bit(b, 8 * i + 5)) + bit(
        b,
        8 * i + 6,
    )) + bit(b, 8 * i + 7)) by {
        reveal_with_fuel(code, 9);
    }
    assert(x as nat == 2 * (2 * (2 * (2 * (2 * (2 * (2 * ((x as nat / 128) % 2) + (x as nat / 64)
        % 2) + (x as nat / 32) % 2) + (x as nat / 16) % 2) + (x as nat / 8) % 2) + (x as nat / 4)
        % 2) + (x as nat / 2) % 2) + (x as nat / 1) % 2) by (nonlinear_arith)
        requires
            x < 256,
    ;
}

/// Appending byte `i` to the `n` bits before it.
pub proof fn lemma_code_push(b: Seq<u8>, p: int, n: nat, i: int)
    requires
        0 <= i < b.len(),
        p + n == 8 * i,
    ensures
        code(b, p, n + 8) == code(b, p, n) * 256 + b[i] as nat,
{
    lemma_code_split(b, p, n, 8);
    lemma_code_byte(b, i);
    lemma2_to64();
}

/// `code` only reads the bits it covers.
pub proof fn lemma_code_prefix(a: Seq<u8>, b: Seq<u8>, p: int, n: nat)
    requires
        0 <= p,
        p + n <= 8 * a.len(),
        a.len() <= b.len(),
        a == b.subrange(0, a.len() as int),
    ensures
        code(a, p, n) == code(b, p, n),
    decreases n,
{
    if n > 0 {
        lemma_code_prefix(a, b, p, (n - 1) as nat);
        let k = p + n - 1;
        assert(0 <= k / 8 < a.len()) by {
            lemma_div_pos_is_pos(k, 8);
            lemma_div_by_multiple_is_strongly_ordered(k, 8 * a.len() as int, a.len() as int, 8);
        }
    }
}

} // verus!
