//! Decimal digits and numbers: what a run of ASCII digits is worth, where it
//! ends, and how a number is written.
use vstd::prelude::*;
use alloc::vec::Vec;

verus! {

/// An ASCII digit, `0`-`9`.
pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// The position after the run of digits at `i` (`i` itself if there is
/// none).
pub open spec fn digits_end(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if 0 <= i < s.len() && is_digit(s[i]) {
        digits_end(s, i + 1)
    } else {
        i
    }
}

/// The value of the digits `d`, read as a decimal number. Bytes that are not
/// digits are not given a meaning here: callers require `all_digits`.
pub open spec fn dec_value(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        dec_value(d.drop_last()) * 10 + (d.last() - 0x30) as nat
    }
}

pub open spec fn all_digits(d: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < d.len() ==> is_digit(#[trigger] d[k])
}

/// The shortest decimal representation of `n`.
pub open spec fn decimal(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u8]
    } else {
        decimal(n / 10) + seq![(0x30 + n % 10) as u8]
    }
}

/// The digit run from `a` to `b` ends where the one from `b` does.
pub proof fn lemma_digits_run(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
        forall|m: int| a <= m < b ==> is_digit(#[trigger] s[m]),
    ensures
        digits_end(s, a) == digits_end(s, b),
    decreases b - a,
{
    if a < b {
        lemma_digits_run(s, a + 1, b);
    }
}

/// What `digits_end` says about the run.
pub proof fn lemma_digits_end(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= digits_end(s, i) <= s.len(),
        forall|m: int| i <= m < digits_end(s, i) ==> is_digit(#[trigger] s[m]),
        digits_end(s, i) < s.len() ==> !is_digit(s[digits_end(s, i)]),
    decreases s.len() - i,
{
    if i < s.len() && is_digit(s[i]) {
        lemma_digits_end(s, i + 1);
    }
}

/// `dec_value` grows by at least a factor of ten per digit.
pub proof fn lemma_dec_value_append(d: Seq<u8>, c: u8)
    requires
        is_digit(c),
    ensures
        dec_value(d.push(c)) == dec_value(d) * 10 + (c - 0x30) as nat,
{
    assert(d.push(c).drop_last() =~= d);
}

/// Whether `c` is an ASCII digit.
///
/// ```text
/// ensures  r == is_digit(c)
/// ```
#[inline(always)]
pub fn ex_is_digit(c: u8) -> (r: bool)
    ensures
        r == is_digit(c),
{
    c.wrapping_sub(0x30) < 10
}

/// `digits_end`, one byte at a time.
#[inline(always)]
pub fn ex_digits_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        r as int == digits_end(s@, i as int),
        i <= r <= s@.len(),
{
    let mut j = i;
    while j < s.len() && ex_is_digit(s[j])
        invariant
            i <= j <= s@.len(),
            digits_end(s@, i as int) == digits_end(s@, j as int),
        decreases s@.len() - j,
    {
        j = j + 1;
    }
    proof {
        lemma_digits_end(s@, j as int);
    }
    j
}

/// The value of the digits `s[a..b]`, or `None` if one of them is not a
/// digit or the value does not fit in a `u64`. An empty range is 0.
pub fn parse_u64_dec(s: &[u8], a: usize, b: usize) -> (r: Option<u64>)
    requires
        a <= b <= s@.len(),
    ensures
        r is Some <==> all_digits(s@.subrange(a as int, b as int)) && dec_value(
            s@.subrange(a as int, b as int),
        ) <= u64::MAX,
        r matches Some(v) ==> v as nat == dec_value(s@.subrange(a as int, b as int)),
{
    let mut v: u64 = 0;
    let mut j = a;
    while j < b
        invariant
            a <= j <= b <= s@.len(),
            all_digits(s@.subrange(a as int, j as int)),
            v as nat == dec_value(s@.subrange(a as int, j as int)),
        decreases b - j,
    {
        let c = s[j];
        proof {
            assert(s@.subrange(a as int, j + 1) =~= s@.subrange(a as int, j as int).push(c));
        }
        if !ex_is_digit(c) {
            proof {
                assert(!is_digit(s@.subrange(a as int, b as int)[j - a]));
            }
            return None;
        }
        let dv = (c - 0x30) as u64;
        proof {
            lemma_dec_value_append(s@.subrange(a as int, j as int), c);
        }
        if v > (u64::MAX - dv) / 10 {
            proof {
                // The prefix through `j` is already too big, and the value
                // only grows from there (if the rest are digits at all).
                if all_digits(s@.subrange(a as int, b as int)) {
                    lemma_dec_value_prefix(s@.subrange(a as int, b as int), j + 1 - a);
                    assert(s@.subrange(a as int, b as int).subrange(0, j + 1 - a) =~= s@.subrange(
                        a as int,
                        j + 1,
                    ));
                }
            }
            return None;
        }
        v = v * 10 + dv;
        j = j + 1;
    }
    Some(v)
}

/// A prefix is worth no more than the whole.
pub proof fn lemma_dec_value_prefix(d: Seq<u8>, n: int)
    requires
        0 <= n <= d.len(),
        all_digits(d),
    ensures
        dec_value(d.subrange(0, n)) <= dec_value(d),
    decreases d.len() - n,
{
    if n < d.len() {
        lemma_dec_value_prefix(d, n + 1);
        let p = d.subrange(0, n + 1);
        assert(p.drop_last() =~= d.subrange(0, n));
        assert(is_digit(d[n]));
    } else {
        assert(d.subrange(0, n) =~= d);
    }
}

/// Appends `decimal(n)`.
pub fn push_decimal(out: &mut Vec<u8>, n: u32)
    ensures
        final(out)@ == old(out)@ + decimal(n as nat),
        n < 100000 ==> final(out)@.len() <= old(out)@.len() + 5,
        n < 10000 ==> final(out)@.len() <= old(out)@.len() + 4,
        n < 1000 ==> final(out)@.len() <= old(out)@.len() + 3,
        n < 256 ==> final(out)@.len() <= old(out)@.len() + 3,
        n < 100 ==> final(out)@.len() <= old(out)@.len() + 2,
        n < 10 ==> final(out)@.len() <= old(out)@.len() + 1,
    decreases n,
{
    if n >= 10 {
        push_decimal(out, n / 10);
    }
    out.push(0x30 + (n % 10) as u8);
    proof {
        assert(final(out)@ =~= old(out)@ + decimal(n as nat));
    }
}

} // verus!
