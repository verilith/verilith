//! `Range: bytes=…` for one range (RFC 9110 §14.1.2), verified.
//!
//! `range_of` is the specification. The theorem (`lemma_part_ok`): a
//! range that is served is non-empty and lies inside the file, so the
//! bytes sent are exactly bytes `start .. start + len` of it.
//! [`parse_range`] computes exactly `range_of`. Several ranges, another
//! unit, an invalid range or a number over 18 digits are ignored (the
//! whole file is served, as §14.2 allows); a valid range that starts past
//! the end is a 416.
use vstd::prelude::*;

verus! {

pub enum Rng {
    /// Serve the whole file (200).
    Whole,
    /// Serve `len` bytes from `start` (206).
    Part(u64, u64),
    /// 416 Range Not Satisfiable.
    Unsat,
}

pub open spec fn is_digit(b: u8) -> bool {
    0x30 <= b <= 0x39
}

pub open spec fn digits(s: Seq<u8>) -> bool {
    1 <= s.len() <= 18 && forall|k: int| 0 <= k < s.len() ==> is_digit(#[trigger] s[k])
}

pub open spec fn num(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { num(s.drop_last()) * 10 + (s.last() - 0x30) as nat }
}

/// The first `-` from `i`, or the end.
pub open spec fn dash(r: Seq<u8>, i: int) -> int
    decreases r.len() - i,
{
    if i >= r.len() || r[i] == 0x2d { i } else { dash(r, i + 1) }
}

pub open spec fn min(a: nat, b: nat) -> nat {
    if a < b { a } else { b }
}

pub open spec fn prefix() -> Seq<u8> {
    seq![0x62u8, 0x79, 0x74, 0x65, 0x73, 0x3d]
}

/// What a Range field value asks of a file of `size` bytes.
pub open spec fn range_of(v: Seq<u8>, size: nat) -> (nat, nat, int) {
    // (start, len, kind): kind 0 whole, 1 part, 2 unsatisfiable.
    if !(v.len() >= 6 && v.subrange(0, 6) == prefix()) {
        (0, 0, 0)
    } else {
        let r = v.subrange(6, v.len() as int);
        let i = dash(r, 0);
        if i >= r.len() {
            (0, 0, 0)
        } else {
            let a = r.subrange(0, i);
            let b = r.subrange(i + 1, r.len() as int);
            if a.len() == 0 && digits(b) {
                let n = num(b);
                if n == 0 || size == 0 { (0, 0, 2) } else { ((size - min(n, size)) as nat, min(n, size), 1) }
            } else if digits(a) && b.len() == 0 {
                let f = num(a);
                if f < size { (f, (size - f) as nat, 1) } else { (0, 0, 2) }
            } else if digits(a) && digits(b) {
                let f = num(a);
                let l = num(b);
                if f > l { (0, 0, 0) } else if f < size { (f, (min(l, (size - 1) as nat) - f + 1) as nat, 1) } else { (0, 0, 2) }
            } else {
                (0, 0, 0)
            }
        }
    }
}

pub open spec fn rng_view(r: Rng) -> (nat, nat, int) {
    match r {
        Rng::Whole => (0, 0, 0),
        Rng::Part(s, n) => (s as nat, n as nat, 1),
        Rng::Unsat => (0, 0, 2),
    }
}

/// The theorem: a served range is non-empty and inside the file.
pub proof fn lemma_part_ok(v: Seq<u8>, size: nat)
    ensures
        range_of(v, size).2 == 1 ==> range_of(v, size).1 > 0 && range_of(v, size).0 + range_of(v, size).1 <= size,
{
}

proof fn lemma_dash(r: Seq<u8>, i: int)
    requires 0 <= i <= r.len(),
    ensures
        i <= dash(r, i) <= r.len(),
        dash(r, i) < r.len() ==> r[dash(r, i)] == 0x2d,
    decreases r.len() - i,
{
    if i < r.len() && r[i] != 0x2d {
        lemma_dash(r, i + 1);
    }
}

proof fn lemma_num_bound(s: Seq<u8>)
    requires forall|k: int| 0 <= k < s.len() ==> is_digit(#[trigger] s[k]),
    ensures num(s) < pow10(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|k: int| 0 <= k < t.len() implies is_digit(#[trigger] t[k]) by {
            assert(t[k] == s[k]);
        }
        lemma_num_bound(t);
        assert(is_digit(s[s.len() - 1]));
    }
}

pub open spec fn pow10(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 10 * pow10((n - 1) as nat) }
}

proof fn lemma_pow10_18(n: nat)
    requires n <= 18,
    ensures pow10(n) <= 1_000_000_000_000_000_000,
    decreases n,
{
    if n > 0 {
        lemma_pow10_18((n - 1) as nat);
        assert(pow10((n - 1) as nat) <= 100_000_000_000_000_000) by {
            lemma_pow10_mono((n - 1) as nat, 17);
            reveal_with_fuel(pow10, 18);
        }
    }
}

proof fn lemma_pow10_mono(a: nat, b: nat)
    requires a <= b,
    ensures pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_mono(a, (b - 1) as nat);
    }
}

/// The digits of `s[i..j]` as a number: Some exactly when they are
/// [`digits`].
fn number(s: &[u8], i: usize, j: usize) -> (r: Option<u64>)
    requires i <= j <= s@.len(),
    ensures
        r matches Some(x) ==> digits(s@.subrange(i as int, j as int)) && x as nat == num(s@.subrange(i as int, j as int)),
        r is None ==> !digits(s@.subrange(i as int, j as int)),
{
    if j - i == 0 || j - i > 18 {
        return None;
    }
    let mut x: u64 = 0;
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= s@.len(),
            j - i <= 18,
            forall|m: int| i <= m < k ==> is_digit(#[trigger] s@[m]),
            x as nat == num(s@.subrange(i as int, k as int)),
            x < pow10((k - i) as nat),
        decreases j - k,
    {
        let b = s[k];
        if b < 0x30 || b > 0x39 {
            assert(!is_digit(s@.subrange(i as int, j as int)[(k - i) as int]));
            return None;
        }
        proof {
            let t = s@.subrange(i as int, k as int + 1);
            assert(t.drop_last() =~= s@.subrange(i as int, k as int));
            lemma_pow10_18((k - i) as nat);
            assert(pow10((k + 1 - i) as nat) == 10 * pow10((k - i) as nat));
        }
        x = x * 10 + (b - 0x30) as u64;
        k += 1;
    }
    proof {
        let t = s@.subrange(i as int, j as int);
        assert forall|m: int| 0 <= m < t.len() implies is_digit(#[trigger] t[m]) by {
            assert(t[m] == s@[i + m]);
        }
    }
    Some(x)
}

/// The range a Range field value `v` asks of a file of `size` bytes:
/// exactly `range_of`.
pub fn parse_range(v: &[u8], size: u64) -> (r: Rng)
    ensures rng_view(r) == range_of(v@, size as nat),
{
    if v.len() < 6 || v[0] != 0x62 || v[1] != 0x79 || v[2] != 0x74 || v[3] != 0x65 || v[4] != 0x73 || v[5] != 0x3d {
        proof {
            if v@.len() >= 6 {
                if v@.subrange(0, 6) == prefix() {
                    assert(v@.subrange(0, 6)[0] == v@[0]);
                    assert(v@.subrange(0, 6)[1] == v@[1]);
                    assert(v@.subrange(0, 6)[2] == v@[2]);
                    assert(v@.subrange(0, 6)[3] == v@[3]);
                    assert(v@.subrange(0, 6)[4] == v@[4]);
                    assert(v@.subrange(0, 6)[5] == v@[5]);
                }
            }
        }
        return Rng::Whole;
    }
    assert(v@.subrange(0, 6) =~= prefix());
    let ghost r = v@.subrange(6, v@.len() as int);
    let n = v.len();
    let mut i: usize = 6;
    proof {
        lemma_dash(r, 0);
    }
    while i < n && v[i] != 0x2d
        invariant
            6 <= i <= n == v@.len(),
            r == v@.subrange(6, n as int),
            dash(r, 0) == dash(r, i - 6),
        decreases n - i,
    {
        i += 1;
    }
    assert(dash(r, i - 6) == i - 6);
    if i >= n {
        return Rng::Whole;
    }
    let ghost a = r.subrange(0, i - 6);
    let ghost b = r.subrange(i - 6 + 1, r.len() as int);
    assert(a =~= v@.subrange(6, i as int));
    assert(b =~= v@.subrange(i + 1, n as int));
    let fa = number(v, 6, i);
    let lb = number(v, i + 1, n);
    if i == 6 {
        assert(a.len() == 0);
        match lb {
            Some(k) => {
                if k == 0 || size == 0 {
                    Rng::Unsat
                } else {
                    let m = if k < size { k } else { size };
                    Rng::Part(size - m, m)
                }
            }
            None => {
                Rng::Whole
            }
        }
    } else {
        match (fa, lb) {
            (Some(f), None) => {
                if i + 1 == n {
                    assert(b.len() == 0);
                    if f < size { Rng::Part(f, size - f) } else { Rng::Unsat }
                } else {
                    assert(b.len() != 0);
                    Rng::Whole
                }
            }
            (Some(f), Some(l)) => {
                if f > l {
                    Rng::Whole
                } else if f < size {
                    let e = if l < size - 1 { l } else { size - 1 };
                    Rng::Part(f, e - f + 1)
                } else {
                    Rng::Unsat
                }
            }
            (None, _) => {
                assert(a.len() != 0);
                Rng::Whole
            }
        }
    }
}

} // verus!
