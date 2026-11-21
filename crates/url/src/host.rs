//! The host parser and serializer, proven to compute exactly
//! `spec::host_parse` and `spec::host_serialize`.
use crate::encode::*;
use crate::idna;
use crate::spec::*;
use crate::tables::*;
pub use verilith_core::num::push_decimal;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Characters
// ---------------------------------------------------------------------------

pub fn is_hex_digit(c: u8) -> (r: bool)
    ensures
        r == is_ascii_hex_digit(c),
{
    (b'0' <= c && c <= b'9') || (b'A' <= c && c <= b'F') || (b'a' <= c && c <= b'f')
}

pub fn hex_val(c: u8) -> (r: u8)
    requires
        is_ascii_hex_digit(c),
    ensures
        r as nat == hex_value(c),
        r < 16,
{
    if c <= b'9' {
        c - b'0'
    } else if c <= b'F' {
        c - b'A' + 10
    } else {
        c - b'a' + 10
    }
}

pub fn is_digit(c: u8) -> (r: bool)
    ensures
        r == is_ascii_digit(c),
{
    b'0' <= c && c <= b'9'
}

pub fn is_alpha(c: u8) -> (r: bool)
    ensures
        r == is_ascii_alpha(c),
{
    (b'A' <= c && c <= b'Z') || (b'a' <= c && c <= b'z')
}

pub fn to_lower(c: u8) -> (r: u8)
    ensures
        r == ascii_lowercase(c),
{
    if b'A' <= c && c <= b'Z' {
        c + 32
    } else {
        c
    }
}

pub fn is_forbidden_host(c: u8) -> (r: bool)
    ensures
        r == is_forbidden_host_code_point(c),
{
    c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == b' ' || c == b'#' || c == b'/' || c
        == b':' || c == b'<' || c == b'>' || c == b'?' || c == b'@' || c == b'[' || c == b'\\'
        || c == b']' || c == b'^' || c == b'|'
}

pub fn is_forbidden_domain(c: u8) -> (r: bool)
    ensures
        r == is_forbidden_domain_code_point(c),
{
    c <= 0x20 || c == b'#' || c == b'/' || c == b':' || c == b'<' || c == b'>' || c == b'?' || c
        == b'@' || c == b'[' || c == b'\\' || c == b']' || c == b'^' || c == b'|' || c == b'%' || c
        == 0x7F
}

// ---------------------------------------------------------------------------
// Percent-decoding
// ---------------------------------------------------------------------------

/// Scratch storage for the host parser, kept across parses so that a
/// percent-encoded or non-ASCII host needs no allocation of its own. What
/// it holds does not matter.
pub struct Scratch {
    pub dec: Vec<u8>,
    pub map: Vec<u32>,
    /// A spare href buffer, which the parser takes when it has room.
    pub href: Vec<u8>,
}

impl Scratch {
    pub fn new() -> Scratch {
        Scratch { dec: Vec::new(), map: Vec::new(), href: Vec::new() }
    }
}

/// The capacity of `v`. Nothing is assumed about it.
#[verifier::external_body]
pub fn capacity<T>(v: &Vec<T>) -> usize {
    v.capacity()
}

pub fn percent_decode_exec(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: Vec<u8>)
    ensures
        r@ == percent_decode(s@),
        r.len() <= s.len(),
        final(cost).n <= old(cost).n + s.len(),
{
    let mut out: Vec<u8> = Vec::with_capacity(s.len());
    percent_decode_into(s, &mut out, Tracked(cost));
    out
}

/// Percent-decodes `s` into `out`, replacing what it held.
pub fn percent_decode_into(s: &[u8], out: &mut Vec<u8>, Tracked(cost): Tracked<&mut Meter>)
    ensures
        final(out)@ == percent_decode(s@),
        final(out)@.len() <= s.len(),
        final(cost).n <= old(cost).n + s.len(),
{
    out.clear();
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
        assert(out@ + percent_decode(s@.skip(0)) =~= percent_decode(s@));
    }
    while i < s.len()
        invariant
            i <= s.len(),
            percent_decode(s@) == out@ + percent_decode(s@.skip(i as int)),
            out.len() <= i,
            cost.n <= old(cost).n + i,
        decreases s.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let ghost rest = s@.skip(i as int);
        let c = s[i];
        if c == b'%' && s.len() - i >= 3 && is_hex_digit(s[i + 1]) && is_hex_digit(s[i + 2]) {
            let b = hex_val(s[i + 1]) * 16 + hex_val(s[i + 2]);
            proof {
                assert(rest[0] == c && rest[1] == s[i + 1 as int] && rest[2] == s[i + 2 as int]);
                assert(rest.skip(3) =~= s@.skip(i + 3));
                assert(percent_decode(rest) == seq![b] + percent_decode(s@.skip(i + 3)));
            }
            out.push(b);
            i = i + 3;
            proof {
                assert(percent_decode(s@) =~= out@ + percent_decode(s@.skip(i as int)));
            }
        } else {
            proof {
                assert(rest[0] == c);
                if rest.len() >= 3 {
                    assert(rest[1] == s[i + 1 as int] && rest[2] == s[i + 2 as int]);
                }
                assert(rest.skip(1) =~= s@.skip(i + 1));
                assert(percent_decode(rest) == seq![c] + percent_decode(s@.skip(i + 1)));
            }
            out.push(c);
            i = i + 1;
            proof {
                assert(percent_decode(s@) =~= out@ + percent_decode(s@.skip(i as int)));
            }
        }
    }
    proof {
        assert(s@.skip(i as int) =~= Seq::<u8>::empty());
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
}

// ---------------------------------------------------------------------------
// Splitting on a delimiter
// ---------------------------------------------------------------------------

pub open spec fn no_byte(s: Seq<u8>, d: u8) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != d
}

pub proof fn lemma_split_len(s: Seq<u8>, d: u8)
    ensures
        split(s, d).len() >= 1,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_split_len(s.skip(1), d);
    }
}

/// A string without the delimiter is a single part.
pub proof fn lemma_split_none(s: Seq<u8>, d: u8)
    requires
        no_byte(s, d),
    ensures
        split(s, d) == seq![s],
    decreases s.len(),
{
    if s.len() > 0 {
        assert(no_byte(s.skip(1), d)) by {
            assert forall|i: int| 0 <= i < s.skip(1).len() implies #[trigger] s.skip(1)[i] != d by {
                assert(s.skip(1)[i] == s[i + 1]);
            }
        }
        lemma_split_none(s.skip(1), d);
        assert(seq![s[0]] + s.skip(1) =~= s);
        assert(split(s, d) =~= seq![s]);
    } else {
        assert(s =~= Seq::<u8>::empty());
    }
}

/// Splitting at the first delimiter.
pub proof fn lemma_split_first(s: Seq<u8>, d: u8, k: int)
    requires
        0 <= k < s.len(),
        s[k] == d,
        no_byte(s.take(k), d),
    ensures
        split(s, d) == seq![s.take(k)] + split(s.skip(k + 1), d),
    decreases k,
{
    if k == 0 {
        assert(s.take(0) =~= Seq::<u8>::empty());
        assert(s.skip(1) =~= s.skip(k + 1));
    } else {
        let t = s.skip(1);
        assert(t[k - 1] == d);
        assert(no_byte(t.take(k - 1), d)) by {
            assert forall|i: int| 0 <= i < t.take(k - 1).len() implies #[trigger] t.take(k - 1)[i] != d by {
                assert(t.take(k - 1)[i] == s.take(k)[i + 1]);
            }
        }
        assert(s[0] != d) by {
            assert(s.take(k)[0] == s[0]);
        }
        lemma_split_first(t, d, k - 1);
        assert(t.skip(k) =~= s.skip(k + 1));
        assert(seq![s[0]] + t.take(k - 1) =~= s.take(k));
        lemma_split_len(t, d);
        assert(split(s, d) =~= seq![s.take(k)] + split(s.skip(k + 1), d));
    }
}

/// Splitting at the last delimiter.
pub proof fn lemma_split_back(t: Seq<u8>, u: Seq<u8>, d: u8)
    requires
        no_byte(u, d),
    ensures
        split(t + seq![d] + u, d) == split(t, d).push(u),
    decreases t.len(),
{
    let s = t + seq![d] + u;
    if t.len() == 0 {
        assert(s[0] == d);
        assert(s.skip(1) =~= u);
        lemma_split_none(u, d);
        assert(split(s, d) =~= split(t, d).push(u));
    } else {
        assert(s.skip(1) =~= t.skip(1) + seq![d] + u);
        lemma_split_back(t.skip(1), u, d);
        lemma_split_len(t.skip(1), d);
        assert(s[0] == t[0]);
        assert(split(s, d) =~= split(t, d).push(u));
    }
}

/// The index of the last `d` in `s[..end]`, or `None`.
pub fn last_index_of(s: &[u8], end: usize, d: u8, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<usize>)
    requires
        end <= s.len(),
    ensures
        final(cost).n <= old(cost).n + end - (match r {
            Some(k) => k as int,
            None => 0,
        }) + 1,
        r matches Some(k) ==> k < end && s@[k as int] == d && no_byte(
            s@.subrange(k + 1, end as int),
            d,
        ),
        r is None ==> no_byte(s@.subrange(0, end as int), d),
{
    let mut j = end;
    while j > 0
        invariant
            j <= end <= s.len(),
            no_byte(s@.subrange(j as int, end as int), d),
            cost.n <= old(cost).n + end - j,
        decreases j,
    {
        proof {
            cost.n = cost.n + 1;
        }
        if s[j - 1] == d {
            return Some(j - 1);
        }
        proof {
            assert forall|i: int| 0 <= i < s@.subrange(j - 1, end as int).len() implies #[trigger] s@.subrange(
                j - 1,
                end as int,
            )[i] != d by {
                if i > 0 {
                    assert(s@.subrange(j - 1, end as int)[i] == s@.subrange(j as int, end as int)[i
                        - 1]);
                }
            }
        }
        j = j - 1;
    }
    proof {
        cost.n = cost.n + 1;
    }
    None
}

/// The index of the first `d` in `s[start..end]`, or `end`.
pub fn index_of_from(s: &[u8], start: usize, end: usize, d: u8, Tracked(cost): Tracked<&mut Meter>) -> (r: usize)
    requires
        start <= end <= s.len(),
    ensures
        start <= r <= end,
        final(cost).n <= old(cost).n + (r - start) + 1,
        r < end ==> s@[r as int] == d,
        no_byte(s@.subrange(start as int, r as int), d),
{
    let mut j = start;
    while j < end
        invariant
            start <= j <= end <= s.len(),
            no_byte(s@.subrange(start as int, j as int), d),
            cost.n <= old(cost).n + (j - start),
        decreases end - j,
    {
        if s[j] == d {
            proof {
                cost.n = cost.n + 1;
            }
            return j;
        }
        proof {
            cost.n = cost.n + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < s@.subrange(start as int, j + 1).len() implies #[trigger] s@.subrange(
                start as int,
                j + 1,
            )[i] != d by {
                if i < j - start {
                    assert(s@.subrange(start as int, j + 1)[i] == s@.subrange(start as int, j as int)[i]);
                }
            }
        }
        j = j + 1;
    }
    proof {
        cost.n = cost.n + 1;
    }
    j
}

// ---------------------------------------------------------------------------
// IPv4
// ---------------------------------------------------------------------------

/// Numbers are tracked saturated at 2^32: every IPv4 check compares with a
/// bound of at most 2^32, so saturation never changes an outcome.
pub open spec fn cap() -> nat {
    0x1_0000_0000
}

pub open spec fn sat(v: nat) -> nat {
    if v > cap() {
        cap()
    } else {
        v
    }
}

proof fn lemma_radix_value_step(t: Seq<u8>, i: int, r: nat)
    requires
        0 <= i < t.len(),
    ensures
        radix_value(t.take(i + 1), r) == radix_value(t.take(i), r) * r + hex_value(t[i]),
{
    assert(t.take(i + 1).drop_last() =~= t.take(i));
}

/// The IPv4 number parser on `s[start..end]`, with the number saturated.
pub fn ipv4_number_exec(s: &[u8], start: usize, end: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<(u64, bool)>)
    requires
        start <= end <= s.len(),
    ensures
        final(cost).n <= old(cost).n + (end - start),
        r matches Some((v, ve)) ==> ipv4_number(s@.subrange(start as int, end as int)) matches Some(
            (n, ve2),
        ) && v as nat == sat(n) && ve == ve2,
        r is None ==> ipv4_number(s@.subrange(start as int, end as int)) is None,
{
    let ghost sub = s@.subrange(start as int, end as int);
    if start == end {
        return None;
    }
    let len = end - start;
    let (r, a, ve): (u64, usize, bool) = if len >= 2 && s[start] == b'0' && (s[start + 1] == b'x'
        || s[start + 1] == b'X') {
        (16, start + 2, true)
    } else if len >= 2 && s[start] == b'0' {
        (8, start + 1, true)
    } else {
        (10, start, false)
    };
    let ghost t = s@.subrange(a as int, end as int);
    proof {
        assert(sub[0] == s@[start as int]);
        if len >= 2 {
            assert(sub[1] == s@[start + 1]);
        }
        assert(t =~= sub.skip(a - start));
    }
    if a == end {
        return Some((0, true));
    }
    let mut v: u64 = 0;
    let mut i: usize = a;
    proof {
        assert(t.take(0) =~= Seq::<u8>::empty());
    }
    while i < end
        invariant
            a <= i <= end <= s.len(),
            r == 16 || r == 10 || r == 8,
            t == s@.subrange(a as int, end as int),
            sub == s@.subrange(start as int, end as int),
            start <= a <= start + 2,
            len == end - start,
            t == sub.skip(a - start),
            len >= 2 ==> sub[1] == s@[start + 1],
            sub[0] == s@[start as int],
            r == 16 ==> len >= 2 && s@[start as int] == b'0' && (s@[start + 1] == b'x' || s@[start
                + 1] == b'X') && a == start + 2 && ve,
            r == 8 ==> len >= 2 && s@[start as int] == b'0' && !(s@[start + 1] == b'x' || s@[start
                + 1] == b'X') && a == start + 1 && ve,
            r == 10 ==> !(len >= 2 && s@[start as int] == b'0') && a == start && !ve,
            forall|j: int| 0 <= j < i - a ==> is_radix_digit(#[trigger] t[j], r as nat),
            v as nat == sat(radix_value(t.take(i - a), r as nat)),
            cost.n <= old(cost).n + (i - start),
        decreases end - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let c = s[i];
        let ok = if r == 16 {
            is_hex_digit(c)
        } else if r == 10 {
            is_digit(c)
        } else {
            b'0' <= c && c <= b'7'
        };
        proof {
            assert(t[i - a] == c);
        }
        if !ok {
            proof {
                assert(!is_radix_digit(t[i - a], r as nat));
                assert(t == ipv4_digits(sub) && r as nat == ipv4_radix(sub));
            }
            return None;
        }
        let d = hex_val(c) as u64;
        let ghost old_rv = radix_value(t.take(i - a), r as nat);
        proof {
            lemma_radix_value_step(t, i - a, r as nat);
        }
        if v == 0x1_0000_0000 {
            proof {
                assert(old_rv >= cap());
                assert(old_rv * r >= cap()) by (nonlinear_arith)
                    requires
                        old_rv >= cap(),
                        r >= 1,
                ;
            }
        } else {
            proof {
                assert(v as nat == old_rv);
                assert(v * r + d <= 0x1_0000_0000 * 16 + 16) by (nonlinear_arith)
                    requires
                        v <= 0x1_0000_0000,
                        r <= 16,
                        d < 16,
                ;
            }
            let nv = v * r + d;
            v = if nv > 0x1_0000_0000 {
                0x1_0000_0000
            } else {
                nv
            };
        }
        i = i + 1;
    }
    proof {
        assert(t.take(i - a) =~= t);
        assert(!(exists|j: int| 0 <= j < t.len() && !is_radix_digit(#[trigger] t[j], r as nat)));
    }
    Some((v, ve))
}

proof fn lemma_split_trailing(s: Seq<u8>)
    requires
        s.len() > 0,
        s.last() == b'.',
    ensures
        split(s, b'.') == split(s.drop_last(), b'.').push(Seq::empty()),
        split(s, b'.').len() > 1,
        split(s, b'.').last().len() == 0,
{
    lemma_split_back(s.drop_last(), Seq::empty(), b'.');
    assert(s.drop_last() + seq![b'.'] + Seq::<u8>::empty() =~= s);
    lemma_split_len(s.drop_last(), b'.');
}

/// For non-empty `s`, the parts the IPv4 parser and the ends-in-a-number
/// checker work on: split `s[..e]`, where `e` drops one trailing ".".
proof fn lemma_parts(s: Seq<u8>, e: int)
    requires
        s.len() > 0,
        e == (if s.last() == b'.' { s.len() - 1 } else { s.len() as int }),
    ensures
        ({
            let parts0 = split(s, b'.');
            let parts = if parts0.last().len() == 0 {
                parts0.drop_last()
            } else {
                parts0
            };
            parts == split(s.take(e), b'.')
        }),
        ({
            let parts0 = split(s, b'.');
            let parts = if parts0.last().len() == 0 && parts0.len() > 1 {
                parts0.drop_last()
            } else {
                parts0
            };
            parts == split(s.take(e), b'.')
        }),
{
    if s.last() == b'.' {
        lemma_split_trailing(s);
        assert(s.drop_last() =~= s.take(e));
        assert(split(s.take(e), b'.').push(Seq::empty()).drop_last() =~= split(s.take(e), b'.'));
    } else {
        assert(s.take(e) =~= s);
        lemma_split_last_nonempty(s, b'.');
    }
}

proof fn lemma_split_last_nonempty(s: Seq<u8>, d: u8)
    requires
        s.len() > 0,
        s.last() != d,
    ensures
        split(s, d).last().len() > 0,
    decreases s.len(),
{
    let rest = split(s.skip(1), d);
    lemma_split_len(s.skip(1), d);
    if s.len() == 1 {
        assert(s.skip(1) =~= Seq::<u8>::empty());
        assert(s[0] == s.last());
    } else {
        assert(s.skip(1).last() == s.last());
        lemma_split_last_nonempty(s.skip(1), d);
    }
}

/// The last part of `s` split on `d` ends with the last byte of `s` when
/// that byte is not `d`.
proof fn lemma_split_last_char(s: Seq<u8>, d: u8)
    requires
        s.len() > 0,
        s.last() != d,
    ensures
        split(s, d).last().len() > 0,
        split(s, d).last().last() == s.last(),
    decreases s.len(),
{
    let rest = split(s.skip(1), d);
    lemma_split_len(s.skip(1), d);
    if s.len() == 1 {
        assert(s.skip(1) =~= Seq::<u8>::empty());
        assert(s[0] == s.last());
        assert(rest =~= seq![Seq::<u8>::empty()]);
        assert(split(s, d) == rest.update(0, seq![s[0]] + rest[0]));
        assert(seq![s[0]] + rest[0] =~= seq![s[0]]);
    } else {
        assert(s.skip(1).last() == s.last());
        lemma_split_last_char(s.skip(1), d);
        if s[0] != d && rest.len() == 1 {
            let f = seq![s[0]] + rest[0];
            assert(split(s, d) == rest.update(0, f));
            assert(f.last() == rest[0].last());
        }
    }
}

/// The last part of `s[..e]` split on "." is `s[ls..e]`.
fn last_part(s: &[u8], e: usize, Tracked(cost): Tracked<&mut Meter>) -> (ls: usize)
    requires
        e <= s.len(),
    ensures
        ls <= e,
        final(cost).n <= old(cost).n + e + 1,
        split(s@.take(e as int), b'.').last() == s@.subrange(ls as int, e as int),
{
    let ghost t = s@.take(e as int);
    match last_index_of(s, e, b'.', Tracked(cost)) {
        Some(k) => {
            proof {
                let u = s@.subrange(k + 1, e as int);
                assert(t =~= t.take(k as int) + seq![b'.'] + u);
                lemma_split_back(t.take(k as int), u, b'.');
            }
            k + 1
        },
        None => {
            proof {
                assert(t =~= s@.subrange(0, e as int));
                lemma_split_none(t, b'.');
            }
            0
        },
    }
}

pub fn all_digits(s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    requires
        a <= b <= s.len(),
    ensures
        final(cost).n <= old(cost).n + (b - a),
        r == all_ascii_digits(s@.subrange(a as int, b as int)),
{
    let ghost sub = s@.subrange(a as int, b as int);
    let mut j = a;
    while j < b
        invariant
            a <= j <= b <= s.len(),
            sub == s@.subrange(a as int, b as int),
            forall|i: int| 0 <= i < j - a ==> is_ascii_digit(#[trigger] sub[i]),
            cost.n <= old(cost).n + (j - a),
        decreases b - j,
    {
        proof {
            cost.n = cost.n + 1;
        }
        if !is_digit(s[j]) {
            proof {
                assert(sub[j - a] == s@[j as int]);
            }
            return false;
        }
        proof {
            assert(sub[j - a] == s@[j as int]);
        }
        j = j + 1;
    }
    true
}

/// The ends in a number checker.
pub fn ends_in_a_number_exec(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    requires
        s.len() > 0,
    ensures
        r == ends_in_a_number(s@),
        final(cost).n <= old(cost).n + 3 * s.len() + 1,
{
    let e = if s[s.len() - 1] == b'.' {
        s.len() - 1
    } else {
        s.len()
    };
    proof {
        lemma_parts(s@, e as int);
        lemma_split_len(s@.take(e as int), b'.');
    }
    // A last part ending in a byte that no number can end in.
    if e > 0 && s[e - 1] != b'.' && !(is_hex_digit(s[e - 1]) || s[e - 1] == b'x' || s[e - 1] == b'X') {
        proof {
            let t = s@.take(e as int);
            let c = s@[e - 1];
            assert(t.last() == c);
            lemma_split_last_char(t, b'.');
            let last = split(t, b'.').last();
            assert(last[last.len() - 1] == c);
            assert(!is_ascii_digit(c));
            assert(!all_ascii_digits(last));
            let d = ipv4_digits(last);
            if d.len() > 0 {
                assert(d[d.len() - 1] == c);
                assert(!is_radix_digit(d[d.len() - 1], ipv4_radix(last)));
            }
            assert(ipv4_number(last) is None);
        }
        return false;
    }
    let ls = last_part(s, e, Tracked(cost));
    let ghost last = s@.subrange(ls as int, e as int);
    if ls < e {
        let c = s[e - 1];
        if !(is_hex_digit(c) || c == b'x' || c == b'X') {
            proof {
                assert(last[last.len() - 1] == c);
                assert(!is_ascii_digit(c));
                assert(!all_ascii_digits(last));
                let t = ipv4_digits(last);
                if t.len() > 0 {
                    assert(t[t.len() - 1] == c);
                    assert(!is_radix_digit(t[t.len() - 1], ipv4_radix(last)));
                }
                assert(ipv4_number(last) is None);
            }
            return false;
        }
    }
    if ls < e && all_digits(s, ls, e, Tracked(cost)) {
        return true;
    }
    ipv4_number_exec(s, ls, e, Tracked(cost)).is_some()
}

proof fn lemma_ipv4_numbers_append(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures
        ipv4_numbers(a + b) == match (ipv4_numbers(a), ipv4_numbers(b)) {
            (Some(x), Some(y)) => Some(x + y),
            _ => None,
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        if let Some(y) = ipv4_numbers(b) {
            assert(Seq::<nat>::empty() + y =~= y);
        }
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_ipv4_numbers_append(a.skip(1), b);
        if let (Some(x), Some(y)) = (ipv4_numbers(a), ipv4_numbers(b)) {
            let n = (ipv4_number(a[0])->0).0;
            let x1 = ipv4_numbers(a.skip(1))->0;
            assert(seq![n] + (x1 + y) =~= (seq![n] + x1) + y);
        }
    }
}

proof fn lemma_ipv4_numbers_one(part: Seq<u8>)
    ensures
        ipv4_numbers(seq![part]) == match ipv4_number(part) {
            Some((n, _)) => Some(seq![n]),
            None => None,
        },
{
    assert(seq![part][0] == part);
    assert(seq![part].skip(1) =~= Seq::<Seq<u8>>::empty());
    assert(ipv4_numbers(Seq::<Seq<u8>>::empty()) == Some(Seq::<nat>::empty()));
    if let Some((n, _)) = ipv4_number(part) {
        assert(seq![n] + Seq::<nat>::empty() =~= seq![n]);
    }
}

proof fn lemma_pow256_small()
    ensures
        pow256(0) == 1,
        pow256(1) == 0x100,
        pow256(2) == 0x1_0000,
        pow256(3) == 0x100_0000,
        pow256(4) == 0x1_0000_0000,
{
    reveal_with_fuel(pow256, 5);
}

/// The IPv4 parser, for a non-empty ASCII `s`.
pub fn ipv4_parse_exec(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: Option<u32>)
    requires
        s.len() > 0,
    ensures
        final(cost).n <= old(cost).n + 3 * s.len() + 3,
        r matches Some(a) ==> ipv4_parse(s@) == Some(a),
        r is None ==> ipv4_parse(s@) is None,
{
    let e = if s[s.len() - 1] == b'.' {
        s.len() - 1
    } else {
        s.len()
    };
    let ghost t = s@.take(e as int);
    proof {
        lemma_parts(s@, e as int);
        assert(ipv4_parse(s@) == ipv4_parse_parts(split(t, b'.')));
        assert(t.skip(0) =~= t);
        assert(Seq::<Seq<u8>>::empty() + split(t, b'.') =~= split(t, b'.'));
    }
    let mut nums: [u64; 4] = [0;4];
    let mut count: usize = 0;
    let mut pos: usize = 0;
    let ghost mut done: Seq<Seq<u8>> = Seq::empty();
    let ghost mut dn: Seq<nat> = Seq::empty();
    loop
        invariant_except_break
            pos <= e,
            split(t, b'.') == done + split(t.skip(pos as int), b'.'),
            cost.n <= old(cost).n + 3 * pos,
        invariant
            e <= s.len(),
            t == s@.take(e as int),
            ipv4_parse(s@) == ipv4_parse_parts(split(t, b'.')),
            count <= 4,
            done.len() == count,
            dn.len() == count,
            ipv4_numbers(done) == Some(dn),
            forall|j: int| 0 <= j < count ==> nums[j] as nat == sat(#[trigger] dn[j]),
        ensures
            count >= 1,
            split(t, b'.') == done,
            cost.n <= old(cost).n + 3 * e + 3,
        decreases e - pos,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let k = index_of_from(s, pos, e, b'.', Tracked(cost));
        let ghost rest = t.skip(pos as int);
        let ghost part = s@.subrange(pos as int, k as int);
        proof {
            assert(rest =~= s@.subrange(pos as int, e as int));
            if k < e {
                assert(part =~= rest.take(k - pos));
                assert(rest[k - pos] == b'.');
                lemma_split_first(rest, b'.', k - pos);
                assert(rest.skip(k - pos + 1) =~= t.skip(k + 1));
            } else {
                assert(part =~= rest);
                lemma_split_none(rest, b'.');
            }
        }
        if count == 4 {
            proof {
                lemma_split_len(rest, b'.');
                assert(split(t, b'.').len() > 4);
            }
            return None;
        }
        match ipv4_number_exec(s, pos, k, Tracked(cost)) {
            None => {
                proof {
                    lemma_ipv4_numbers_one(part);
                    if k < e {
                        lemma_ipv4_numbers_append(seq![part], split(t.skip(k + 1), b'.'));
                        assert(split(rest, b'.') =~= seq![part] + split(t.skip(k + 1), b'.'));
                    }
                    lemma_ipv4_numbers_append(done, split(rest, b'.'));
                }
                return None;
            },
            Some((v, _)) => {
                proof {
                    lemma_ipv4_numbers_one(part);
                    lemma_ipv4_numbers_append(done, seq![part]);
                }
                nums[count] = v;
                proof {
                    let n = (ipv4_number(part)->0).0;
                    assert(dn.push(n) =~= dn + seq![n]);
                    assert(done.push(part) =~= done + seq![part]);
                    dn = dn.push(n);
                    done = done.push(part);
                }
                count = count + 1;
                if k == e {
                    proof {
                        assert(split(t, b'.') =~= done);
                    }
                    break;
                }
                proof {
                    assert(split(t, b'.') =~= done + split(t.skip(k + 1), b'.'));
                }
                pos = k + 1;
            },
        }
    }
    // numbers == dn, parts == done.
    proof {
        assert(ipv4_parse(s@) == ipv4_from_numbers(dn));
    }
    let n = count;
    let mut j: usize = 0;
    while j + 1 < n
        invariant
            ipv4_parse(s@) == ipv4_from_numbers(dn),
            1 <= n <= 4,
            n == dn.len(),
            j < n,
            cost.n <= old(cost).n + 3 * s.len() + 3,
            forall|i: int| 0 <= i < n ==> nums[i] as nat == sat(#[trigger] dn[i]),
            forall|i: int| 0 <= i < j ==> #[trigger] dn[i] <= 255,
        decreases n - j,
    {
        if nums[j] > 255 {
            proof {
                assert(dn[j as int] > 255);
                assert(some_non_last_over_255(dn));
            }
            return None;
        }
        j = j + 1;
    }
    proof {
        assert(!some_non_last_over_255(dn));
        lemma_pow256_small();
    }
    let last = nums[n - 1];
    let limit: u64 = if n == 1 {
        0x1_0000_0000
    } else if n == 2 {
        0x100_0000
    } else if n == 3 {
        0x1_0000
    } else {
        0x100
    };
    proof {
        assert(limit as nat == pow256((5 - n) as nat));
    }
    if last >= limit {
        proof {
            assert(dn.last() >= pow256((5 - dn.len()) as nat));
        }
        return None;
    }
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(dn.take(0) =~= Seq::<nat>::empty());
    }
    while i + 1 < n
        invariant
            ipv4_parse(s@) == ipv4_from_numbers(dn),
            !some_non_last_over_255(dn),
            last as nat == sat(dn.last()),
            (last as nat) < pow256((5 - n) as nat),
            1 <= n <= 4,
            n == dn.len(),
            i < n,
            cost.n <= old(cost).n + 3 * s.len() + 3,
            forall|k: int| 0 <= k < n ==> nums[k] as nat == sat(#[trigger] dn[k]),
            forall|k: int| 0 <= k < n - 1 ==> #[trigger] dn[k] <= 255,
            acc as nat == ipv4_prefix_sum(dn.take(i as int)),
            acc + pow256((4 - i) as nat) <= 0x1_0000_0000,
        decreases n - i,
    {
        let m: u64 = if i == 0 {
            0x100_0000
        } else if i == 1 {
            0x1_0000
        } else {
            0x100
        };
        proof {
            lemma_pow256_small();
            assert(m as nat == pow256((3 - i) as nat));
            assert(dn.take(i + 1).drop_last() =~= dn.take(i as int));
            assert(dn.take(i + 1).last() == dn[i as int]);
            assert(nums[i as int] <= 255);
            assert(pow256((4 - i) as nat) == 256 * m);
            let x = nums[i as int];
            assert(x * m + m <= 256 * m) by (nonlinear_arith)
                requires
                    x <= 255,
            ;
            assert(x * m <= 255 * 0x100_0000) by (nonlinear_arith)
                requires
                    x <= 255,
                    m <= 0x100_0000,
            ;
        }
        acc = acc + nums[i] * m;
        i = i + 1;
    }
    proof {
        assert(dn.take(n - 1) =~= dn.drop_last());
        lemma_pow256_small();
    }
    Some((acc + last) as u32)
}

// ---------------------------------------------------------------------------
// IPv6
// ---------------------------------------------------------------------------

pub open spec fn nat_view(a: [u16; 8]) -> Seq<nat> {
    Seq::new(8, |i: int| a@[i] as nat)
}

pub open spec fn opt_int(o: Option<usize>) -> Option<int> {
    match o {
        Some(c) => Some(c as int),
        None => None,
    }
}

proof fn lemma_nat_view_update(a: [u16; 8], i: int, v: u16)
    requires
        0 <= i < 8,
    ensures
        nat_view(a).update(i, v as nat) == Seq::new(8, |j: int| a@.update(i, v)[j] as nat),
{
    assert(nat_view(a).update(i, v as nat) =~= Seq::new(8, |j: int| a@.update(i, v)[j] as nat));
}

fn ipv6_hex_run_exec(s: &[u8], p: usize) -> (r: (u16, usize))
    requires
        p <= s.len(),
    ensures
        ipv6_hex_run(s@, p as int, 0, 0) == (r.0 as nat, r.1 as nat),
        r.1 <= 4,
        p + r.1 <= s.len(),
{
    let mut value: u32 = 0;
    let mut length: usize = 0;
    while length < 4 && p + length < s.len() && is_hex_digit(s[p + length])
        invariant
            p <= s.len(),
            length <= 4,
            p + length <= s.len(),
            value < 0x10000,
            length == 0 ==> value == 0,
            length == 1 ==> value < 0x10,
            length == 2 ==> value < 0x100,
            length == 3 ==> value < 0x1000,
            ipv6_hex_run(s@, p as int, 0, 0) == ipv6_hex_run(s@, p as int, value as nat, length as nat),
        decreases 4 - length,
    {
        value = value * 16 + hex_val(s[p + length]) as u32;
        length = length + 1;
    }
    (value as u16, length)
}

fn ipv6_v4_digits_exec(s: &[u8], p: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<(u16, usize)>)
    requires
        p <= s.len(),
    ensures
        final(cost).n <= old(cost).n + (match r {
            Some((_, q)) => q - p,
            None => s.len() - p,
        }),
        r matches Some((v, q)) ==> ipv6_v4_digits(s@, p as int, None) == Some((v as nat, q as int))
            && v <= 255 && p < q <= s.len(),
        r is None ==> ipv6_v4_digits(s@, p as int, None) is None,
{
    let mut q = p;
    let mut piece: Option<u16> = None;
    while q < s.len() && is_digit(s[q])
        invariant
            p <= q <= s.len(),
            piece is None <==> q == p,
            piece matches Some(v) ==> v <= 255,
            ipv6_v4_digits(s@, p as int, None) == ipv6_v4_digits(
                s@,
                q as int,
                match piece {
                    Some(v) => Some(v as nat),
                    None => None,
                },
            ),
            cost.n <= old(cost).n + (q - p),
        decreases s.len() - q,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let number = hex_val(s[q]) as u16;
        match piece {
            None => {
                piece = Some(number);
            },
            Some(v) => {
                if v == 0 {
                    return None;
                }
                if v * 10 + number > 255 {
                    return None;
                }
                piece = Some(v * 10 + number);
            },
        }
        q = q + 1;
    }
    match piece {
        None => None,
        Some(v) => Some((v, q)),
    }
}

/// The IPv4-in-IPv6 loop, starting at piece `pi` with `a[pi..]` all zero.
fn ipv6_v4_exec(s: &[u8], p: usize, pi: usize, a: &mut [u16; 8], Tracked(cost): Tracked<&mut Meter>) -> (r: Option<usize>)
    requires
        p <= s.len(),
        pi <= 6,
        forall|j: int| pi <= j < 8 ==> old(a)@[j] == 0,
    ensures
        final(cost).n <= old(cost).n + 3 * (s.len() - p),
        r matches Some(pi2) ==> ipv6_v4(s@, p as int, 0, pi as int, nat_view(*old(a))) == Some(
            (nat_view(*final(a)), pi2 as int),
        ) && pi <= pi2 <= 8,
        r is None ==> ipv6_v4(s@, p as int, 0, pi as int, nat_view(*old(a))) is None,
{
    let mut q = p;
    let mut ns: usize = 0;
    let mut idx = pi;
    while q < s.len()
        invariant
            p <= q <= s.len(),
            pi <= 6,
            ns <= 4,
            idx == pi + ns / 2,
            forall|j: int| idx < j < 8 ==> a@[j] == 0,
            ns % 2 == 0 && idx < 8 ==> a@[idx as int] == 0,
            ns % 2 == 1 ==> a@[idx as int] <= 255,
            ipv6_v4(s@, p as int, 0, pi as int, nat_view(*old(a))) == ipv6_v4(
                s@,
                q as int,
                ns as nat,
                idx as int,
                nat_view(*a),
            ),
            cost.n <= old(cost).n + 3 * (q - p),
        decreases s.len() - q,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let mut q1 = q;
        if ns > 0 {
            if s[q] == b'.' && ns < 4 {
                q1 = q + 1;
            } else {
                return None;
            }
        }
        match ipv6_v4_digits_exec(s, q1, Tracked(cost)) {
            None => {
                return None;
            },
            Some((piece, q2)) => {
                let cur = a[idx];
                let nv = cur * 0x100 + piece;
                proof {
                    lemma_nat_view_update(*a, idx as int, nv);
                    assert(nat_view(*a)[idx as int] == cur as nat);
                }
                a[idx] = nv;
                proof {
                    assert(nat_view(*a) =~= Seq::new(8, |j: int| a@[j] as nat));
                }
                ns = ns + 1;
                if ns == 2 || ns == 4 {
                    idx = idx + 1;
                }
                q = q2;
            },
        }
    }
    if ns != 4 {
        return None;
    }
    Some(idx)
}

/// The IPv6 parser.
pub fn ipv6_parse_exec(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: Option<[u16; 8]>)
    ensures
        final(cost).n <= old(cost).n + 4 * s.len(),
        r matches Some(a) ==> ipv6_parse(s@) == Some(a@),
        r is None ==> ipv6_parse(s@) is None,
{
    let mut a: [u16; 8] = [0;8];
    let ghost zero = Seq::new(8, |i: int| 0nat);
    proof {
        assert(nat_view(a) =~= zero);
    }
    let mut p: usize = 0;
    let mut pi: usize = 0;
    let mut compress: Option<usize> = None;
    if s.len() > 0 && s[0] == b':' {
        if s.len() < 2 || s[1] != b':' {
            return None;
        }
        p = 2;
        pi = 1;
        compress = Some(1);
    }
    let ghost p0 = p as int;
    let ghost pi0 = pi as int;
    let ghost c0 = opt_int(compress);
    proof {
        assert(ipv6_main(s@, p0, pi0, c0, zero) is None ==> ipv6_parse(s@) is None);
    }
    loop
        invariant_except_break
            forall|j: int| pi <= j < 8 ==> a@[j] == 0,
            ipv6_main(s@, p0, pi0, c0, zero) == ipv6_main(s@, p as int, pi as int, opt_int(compress), nat_view(a)),
            cost.n <= old(cost).n + p,
        invariant
            ipv6_main(s@, p0, pi0, c0, zero) is None ==> ipv6_parse(s@) is None,
            p <= s.len(),
            pi <= 8,
            compress matches Some(c) ==> c <= pi,
        ensures
            pi <= 8,
            compress matches Some(c) ==> c <= pi,
            ipv6_main(s@, p0, pi0, c0, zero) == Some((nat_view(a), pi as int, opt_int(compress))),
            cost.n <= old(cost).n + 4 * s.len(),
        decreases s.len() - p,
    {
        if p >= s.len() {
            break;
        }
        proof {
            cost.n = cost.n + 1;
        }
        if pi == 8 {
            return None;
        }
        if s[p] == b':' {
            if compress.is_some() {
                return None;
            }
            p = p + 1;
            pi = pi + 1;
            compress = Some(pi);
            continue;
        }
        let (value, length) = ipv6_hex_run_exec(s, p);
        let q = p + length;
        if q < s.len() && s[q] == b'.' {
            if length == 0 {
                return None;
            }
            if pi > 6 {
                return None;
            }
            match ipv6_v4_exec(s, p, pi, &mut a, Tracked(cost)) {
                None => {
                    return None;
                },
                Some(pi2) => {
                    pi = pi2;
                    break;
                },
            }
        } else if q < s.len() && s[q] == b':' {
            if q + 1 >= s.len() {
                return None;
            }
            proof {
                lemma_nat_view_update(a, pi as int, value);
            }
            a[pi] = value;
            proof {
                assert(nat_view(a) =~= Seq::new(8, |j: int| a@[j] as nat));
            }
            pi = pi + 1;
            p = q + 1;
        } else if q < s.len() {
            return None;
        } else {
            proof {
                lemma_nat_view_update(a, pi as int, value);
            }
            a[pi] = value;
            proof {
                assert(nat_view(a) =~= Seq::new(8, |j: int| a@[j] as nat));
            }
            pi = pi + 1;
            p = q;
            break;
        }
    }
    match compress {
        Some(c) => {
            let mut swaps = pi - c;
            let mut i: usize = 7;
            let ghost a0 = nat_view(a);
            while i != 0 && swaps > 0
                invariant
                    i <= 7,
                    c + swaps <= 8,
                    cost.n <= old(cost).n + 4 * s.len(),
                    ipv6_swap(a0, 7, (pi - c) as int, c as int) == ipv6_swap(nat_view(a), i as int, swaps as int, c as int),
                decreases swaps,
            {
                let j = c + swaps - 1;
                let x = a[i];
                let y = a[j];
                proof {
                    let na = nat_view(a);
                    assert(na.update(i as int, na[j as int]).update(j as int, na[i as int]) =~= Seq::new(8, |k: int| a@.update(i as int, y).update(j as int, x)[k] as nat));
                }
                a[i] = y;
                a[j] = x;
                proof {
                    assert(nat_view(a) =~= Seq::new(8, |k: int| a@[k] as nat));
                }
                i = i - 1;
                swaps = swaps - 1;
            }
            proof {
                let r = ipv6_swap(nat_view(a), i as int, swaps as int, c as int);
                assert(r == nat_view(a));
                assert(Seq::new(8, |k: int| r[k] as u16) =~= a@);
            }
            Some(a)
        },
        None => {
            if pi != 8 {
                return None;
            }
            proof {
                assert(Seq::new(8, |k: int| nat_view(a)[k] as u16) =~= a@);
            }
            Some(a)
        },
    }
}

// ---------------------------------------------------------------------------
// Host serializing
// ---------------------------------------------------------------------------

pub fn push_lower_hex(out: &mut Vec<u8>, n: u16)
    ensures
        final(out)@ == old(out)@ + lower_hex(n as nat),
        final(out)@.len() <= old(out)@.len() + 4,
        n < 0x1000 ==> final(out)@.len() <= old(out)@.len() + 3,
        n < 0x100 ==> final(out)@.len() <= old(out)@.len() + 2,
        n < 0x10 ==> final(out)@.len() <= old(out)@.len() + 1,
    decreases n,
{
    if n >= 16 {
        push_lower_hex(out, n / 16);
    }
    let d = (n % 16) as u8;
    out.push(if d < 10 {
        b'0' + d
    } else {
        b'a' + d - 10
    });
    proof {
        assert(final(out)@ =~= old(out)@ + lower_hex(n as nat));
    }
}

pub fn ipv4_serialize_exec(out: &mut Vec<u8>, a: u32)
    ensures
        final(out)@ == old(out)@ + ipv4_serialize(a),
        final(out)@.len() <= old(out)@.len() + 15,
{
    push_decimal(out, a / 0x100_0000);
    out.push(b'.');
    push_decimal(out, (a / 0x1_0000) % 256);
    out.push(b'.');
    push_decimal(out, (a / 0x100) % 256);
    out.push(b'.');
    push_decimal(out, a % 256);
    proof {
        assert(final(out)@ =~= old(out)@ + ipv4_serialize(a));
    }
}

fn ipv6_compress_exec(a: &[u16; 8]) -> (r: Option<usize>)
    ensures
        opt_int(r) == ipv6_compress(a@),
        r matches Some(c) ==> c < 8,
{
    let mut li: Option<usize> = None;
    let mut ls: usize = 1;
    let mut fi: Option<usize> = None;
    let mut fs: usize = 0;
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            fs <= i,
            ls <= 8,
            li matches Some(x) ==> x < 8,
            fi matches Some(x) ==> x < 8,
            ipv6_compress(a@) == ipv6_compress_from(a@, i as int, opt_int(li), ls as int, opt_int(fi), fs as int),
        decreases 8 - i,
    {
        if a[i] != 0 {
            if fs > ls {
                li = fi;
                ls = fs;
            }
            fi = None;
            fs = 0;
        } else {
            if fi.is_none() {
                fi = Some(i);
            }
            fs = fs + 1;
        }
        i = i + 1;
    }
    if fs > ls {
        fi
    } else {
        li
    }
}

pub fn ipv6_serialize_exec(out: &mut Vec<u8>, a: &[u16; 8])
    ensures
        final(out)@ == old(out)@ + ipv6_serialize(a@),
        final(out)@.len() <= old(out)@.len() + 40,
{
    let compress = ipv6_compress_exec(a);
    let mut ignore0 = false;
    let mut i: usize = 0;
    proof {
        assert(old(out)@ + ipv6_serialize(a@) =~= out@ + ipv6_serialize_from(a@, 0, opt_int(compress), false));
    }
    while i < 8
        invariant
            i <= 8,
            old(out)@ + ipv6_serialize(a@) == out@ + ipv6_serialize_from(a@, i as int, opt_int(compress), ignore0),
            out@.len() <= old(out)@.len() + 5 * i,
        decreases 8 - i,
    {
        let x = a[i];
        if ignore0 && x == 0 {
            i = i + 1;
            continue;
        }
        let ghost before = out@;
        let ghost ign0 = ignore0;
        if compress == Some(i) {
            if i == 0 {
                out.push(b':');
                out.push(b':');
            } else {
                out.push(b':');
            }
            ignore0 = true;
            proof {
                let sep = if i == 0 { seq![b':', b':'] } else { seq![b':'] };
                assert(out@ =~= before + sep);
                assert(before + ipv6_serialize_from(a@, i as int, opt_int(compress), ign0) =~= out@ + ipv6_serialize_from(a@, i + 1, opt_int(compress), true));
            }
            i = i + 1;
            continue;
        }
        push_lower_hex(out, x);
        if i != 7 {
            out.push(b':');
        }
        proof {
            let tail = if i != 7 { seq![b':'] } else { Seq::<u8>::empty() };
            assert(out@ =~= before + lower_hex(x as nat) + tail);
            assert(opt_int(compress) != Some(i as int));
        }
        ignore0 = false;
        i = i + 1;
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
}

// ---------------------------------------------------------------------------
// Host parsing
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HostKind {
    Domain,
    Ipv4,
    Ipv6,
    Opaque,
    Empty,
}

pub open spec fn kind_of(h: Host) -> HostKind {
    match h {
        Host::Domain(_) => HostKind::Domain,
        Host::Ipv4(_) => HostKind::Ipv4,
        Host::Ipv6(_) => HostKind::Ipv6,
        Host::Opaque(_) => HostKind::Opaque,
        Host::Empty => HostKind::Empty,
    }
}

/// The opaque-host parser; appends the host to `out`.
pub fn opaque_host_exec(s: &[u8], out: &mut Vec<u8>, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<(HostKind, Ghost<Host>)>)
    ensures
        final(cost).n <= old(cost).n + 4 * s.len(),
        final(out)@.len() <= old(out)@.len() + 3 * s.len(),
        r matches Some((k, h)) ==> opaque_host_parse(s@) == Some(h@) && k == kind_of(h@)
            && final(out)@ == old(out)@ + host_serialize(h@),
        r is None ==> opaque_host_parse(s@) is None,
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> !is_forbidden_host_code_point(#[trigger] s@[j]),
            cost.n <= old(cost).n + i,
        decreases s.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        if is_forbidden_host(s[i]) {
            return None;
        }
        i = i + 1;
    }
    let start = out.len();
    append_pe(out, s, 0, s.len(), EncodeSet::C0Control, Tracked(cost));
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
        lemma_pe_seq_len(s@, EncodeSet::C0Control);
    }
    if out.len() == start {
        proof {
            assert(pe_seq(s@, EncodeSet::C0Control).len() == 0);
            assert(final(out)@ =~= old(out)@ + host_serialize(Host::Empty));
        }
        Some((HostKind::Empty, Ghost(Host::Empty)))
    } else {
        Some((HostKind::Opaque, Ghost(Host::Opaque(pe_seq(s@, EncodeSet::C0Control)))))
    }
}

pub proof fn lemma_percent_decode_identity(s: Seq<u8>)
    requires
        no_byte(s, b'%'),
    ensures
        percent_decode(s) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s[0] != b'%');
        assert(no_byte(s.skip(1), b'%')) by {
            assert forall|i: int| 0 <= i < s.skip(1).len() implies #[trigger] s.skip(1)[i] != b'%' by {
                assert(s.skip(1)[i] == s[i + 1]);
            }
        }
        lemma_percent_decode_identity(s.skip(1));
        assert(seq![s[0]] + s.skip(1) =~= s);
    } else {
        assert(s =~= Seq::<u8>::empty());
    }
}

pub fn is_ascii_exec(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    ensures
        r == is_ascii(s@),
        final(cost).n <= old(cost).n + s.len(),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] < 0x80,
            cost.n <= old(cost).n + i,
        decreases s.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        if s[i] >= 0x80 {
            return false;
        }
        i = i + 1;
    }
    true
}

/// The rest of the host parser for a percent-decoded domain `d`: the domain
/// parser, then the IPv4 parser if the result ends in a number.
pub open spec fn domain_host(d: Seq<u8>) -> Option<Host> {
    match domain_parse(d) {
        None => None,
        Some(ascii) => if ends_in_a_number(ascii) {
            match ipv4_parse(ascii) {
                None => None,
                Some(a) => Some(Host::Ipv4(a)),
            }
        } else {
            Some(Host::Domain(ascii))
        },
    }
}

fn domain_host_exec(d: &[u8], fast: bool, out: &mut Vec<u8>, map: &mut Vec<u32>, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<(HostKind, Ghost<Host>)>)
    requires
        fast == (d.len() > 0 && forall|j: int| 0 <= j < d.len() ==> !cls_has(#[trigger] d@[j], DOMAIN_SLOW)),
    ensures
        final(cost).n <= old(cost).n + 80 * d.len() + 4,
        final(out)@.len() <= old(out)@.len() + 8 * d.len() + 15,
        r matches Some((k, h)) ==> domain_host(d@) == Some(h@) && k == kind_of(h@)
            && final(out)@ == old(out)@ + host_serialize(h@),
        r is None ==> domain_host(d@) is None,
{
    let start = out.len();
    if fast {
        // Already lowercase ASCII without forbidden code points: copy it.
        append(out, d, Tracked(cost));
        proof {
            lemma_cls();
            let v = d@;
            assert forall|j: int| 0 <= j < v.len() implies !(v[j] >= 0x80 || is_ascii_upper_alpha(v[j])
                || is_forbidden_domain_code_point(v[j])) by {
                assert(!cls_has(v[j], DOMAIN_SLOW));
                assert(cls_has(v[j], DOMAIN_SLOW) == cls_pred(DOMAIN_SLOW, v[j]));
            }
            assert(is_ascii(v));
            assert(ascii_lowercase_seq(v) =~= v);
            assert(!contains_forbidden_domain_code_point(v));
            assert(domain_parse(v) == Some(v));
        }
    } else if is_ascii_exec(d, Tracked(cost)) {
        let mut i: usize = 0;
        proof {
            assert(ascii_lowercase_seq(d@.take(0)) =~= Seq::<u8>::empty());
            assert(out@ =~= old(out)@ + ascii_lowercase_seq(d@.take(0)));
        }
        while i < d.len()
            invariant
                is_ascii(d@),
                i <= d.len(),
                start == old(out)@.len(),
                out@ == old(out)@ + ascii_lowercase_seq(d@.take(i as int)),
                forall|j: int| 0 <= j < i ==> !is_forbidden_domain_code_point(#[trigger] ascii_lowercase(d@[j])),
                cost.n <= old(cost).n + d.len() + i,
            decreases d.len() - i,
        {
            proof {
                cost.n = cost.n + 1;
            }
            let c = to_lower(d[i]);
            if is_forbidden_domain(c) {
                proof {
                    let r = ascii_lowercase_seq(d@);
                    assert(r[i as int] == c);
                    assert(contains_forbidden_domain_code_point(r));
                    assert(r.len() > 0);
                    assert(is_ascii(d@));
                    assert(domain_parse_result(d@) == Some(r));
                    assert(domain_check(r) is None);
                    assert(domain_parse(d@) is None);
                }
                return None;
            }
            out.push(c);
            proof {
                assert(ascii_lowercase_seq(d@.take(i + 1)) =~= ascii_lowercase_seq(d@.take(i as int)).push(c));
            }
            i = i + 1;
        }
        proof {
            assert(d@.take(i as int) =~= d@);
            let r = ascii_lowercase_seq(d@);
            assert(!contains_forbidden_domain_code_point(r)) by {
                assert forall|j: int| 0 <= j < r.len() implies !is_forbidden_domain_code_point(#[trigger] r[j]) by {
                    assert(r[j] == ascii_lowercase(d@[j]));
                }
            }
        }
    } else {
        // ToASCII appends straight to `out`; on failure that is undone.
        let ok = idna::domain_to_ascii_into(d, map, out, Tracked(cost));
        if capacity(map) > 4096 {
            *map = Vec::new();
        }
        if !ok {
            out.truncate(start);
            return None;
        }
        let ghost v = out@.subrange(start as int, out@.len() as int);
        proof {
            assert(out@ =~= old(out)@ + v);
        }
        let n = out.len();
        if !is_ascii_exec(vstd::slice::slice_subrange(out.as_slice(), start, n), Tracked(cost)) {
            out.truncate(start);
            return None;
        }
        let mut i: usize = start;
        while i < n
            invariant
                !is_ascii(d@),
                crate::spec::domain_to_ascii(d@) == Some(v),
                is_ascii(v),
                n == out.len(),
                start <= i <= n,
                start == old(out)@.len(),
                out@ == old(out)@ + v,
                v.len() == n - start,
                forall|j: int| 0 <= j < i - start ==> !is_forbidden_domain_code_point(#[trigger] v[j]),
                v.len() <= 8 * d.len(),
                cost.n <= old(cost).n + 2 * d.len() + v.len() + (i - start),
            decreases n - i,
        {
            proof {
                cost.n = cost.n + 1;
            }
            if is_forbidden_domain(out[i]) {
                proof {
                    assert(out@[i as int] == v[i - start]);
                    assert(is_forbidden_domain_code_point(v[i - start]));
                    assert(contains_forbidden_domain_code_point(v));
                    assert(domain_parse(d@) is None);
                }
                out.truncate(start);
                return None;
            }
            i = i + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < v.len() implies !is_forbidden_domain_code_point(#[trigger] v[j]) by {}
        }
    }
    let end = out.len();
    proof {
        assert(cost.n <= old(cost).n + 74 * d.len());
        assert(end <= start + 8 * d.len());
    }
    if end == start {
        return None;
    }
    let ghost ascii = out@.subrange(start as int, end as int);
    proof {
        assert(ascii =~= out@.subrange(old(out)@.len() as int, out@.len() as int));
        assert(out@ =~= old(out)@ + ascii);
        assert(domain_parse(d@) == Some(ascii));
    }
    let ends = ends_in_a_number_exec(vstd::slice::slice_subrange(out.as_slice(), start, end), Tracked(cost));
    if ends {
        let v4 = ipv4_parse_exec(vstd::slice::slice_subrange(out.as_slice(), start, end), Tracked(cost));
        match v4 {
            None => None,
            Some(a) => {
                out.truncate(start);
                proof {
                    assert(out@ =~= old(out)@);
                }
                ipv4_serialize_exec(out, a);
                Some((HostKind::Ipv4, Ghost(Host::Ipv4(a))))
            },
        }
    } else {
        Some((HostKind::Domain, Ghost(Host::Domain(ascii))))
    }
}

/// Bounds on the host parser's work and output for an `n`-byte host.
pub open spec fn host_cost(n: nat) -> nat {
    96 * n + 8
}

pub open spec fn host_growth(n: nat) -> nat {
    8 * n + 42
}

/// The host parser; appends the serialized host to `out`.
pub fn host_parse_exec(s: &[u8], is_opaque: bool, out: &mut Vec<u8>, sc: &mut Scratch, clean: bool, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<(HostKind, Ghost<Host>)>)
    requires
        clean ==> forall|j: int| 0 <= j < s.len() ==> !cls_has(#[trigger] s@[j], DOMAIN_SLOW),
    ensures
        final(cost).n <= old(cost).n + host_cost(s.len() as nat),
        final(out)@.len() <= old(out)@.len() + host_growth(s.len() as nat),
        r matches Some((k, h)) ==> host_parse(s@, is_opaque) == Some(h@) && k == kind_of(h@)
            && final(out)@ == old(out)@ + host_serialize(h@),
        r is None ==> host_parse(s@, is_opaque) is None,
{
    if s.len() > 0 && s[0] == b'[' {
        if s[s.len() - 1] != b']' {
            return None;
        }
        let inner = vstd::slice::slice_subrange(s, 1, s.len() - 1);
        match ipv6_parse_exec(inner, Tracked(cost)) {
            None => {
                return None;
            },
            Some(a) => {
                out.push(b'[');
                ipv6_serialize_exec(out, &a);
                out.push(b']');
                proof {
                    assert(final(out)@ =~= old(out)@ + host_serialize(Host::Ipv6(a@)));
                }
                return Some((HostKind::Ipv6, Ghost(Host::Ipv6(a@))));
            },
        }
    }
    if is_opaque {
        return opaque_host_exec(s, out, Tracked(cost));
    }
    let k = if clean {
        s.len()
    } else {
        proof {
            crate::swar::lemma_plain_free_masks();
        }
        crate::swar::find_cls_plain(s, 0, s.len(), DOMAIN_SLOW, Tracked(cost))
    };
    if k == s.len() && k > 0 {
        // No '%' either, since it is a forbidden domain code point.
        proof {
            lemma_cls();
            assert forall|j: int| 0 <= j < s.len() implies s@[j] != b'%' by {
                assert(cls_has(s@[j], DOMAIN_SLOW) == cls_pred(DOMAIN_SLOW, s@[j]));
            }
            lemma_percent_decode_identity(s@);
        }
        domain_host_exec(s, true, out, &mut sc.map, Tracked(cost))
    } else if index_of_from(s, 0, s.len(), b'%', Tracked(cost)) == s.len() {
        proof {
            assert(s@.subrange(0, s.len() as int) =~= s@);
            lemma_percent_decode_identity(s@);
            if s.len() > 0 {
                assert(cls_has(s@[k as int], DOMAIN_SLOW));
            }
        }
        domain_host_exec(s, false, out, &mut sc.map, Tracked(cost))
    } else {
        let mut d: Vec<u8> = Vec::new();
        core::mem::swap(&mut d, &mut sc.dec);
        percent_decode_into(s, &mut d, Tracked(cost));
        proof {
            crate::swar::lemma_plain_free_masks();
        }
        let fast = d.len() > 0 && crate::swar::find_cls_plain(d.as_slice(), 0, d.len(), DOMAIN_SLOW, Tracked(cost)) == d.len();
        let r = domain_host_exec(d.as_slice(), fast, out, &mut sc.map, Tracked(cost));
        // Keep small buffers only.
        if capacity(&d) <= 4096 {
            sc.dec = d;
        }
        if capacity(&sc.map) > 4096 {
            sc.map = Vec::new();
        }
        r
    }
}

} // verus!
