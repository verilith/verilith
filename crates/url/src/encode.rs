//! Byte-buffer helpers and percent-encoding, proven against `spec::pe_seq`.
use crate::spec::*;
use crate::tables::*;
use vstd::prelude::*;

verus! {

/// Appends `s` to `out` with a single `memcpy`.
pub fn append(out: &mut Vec<u8>, s: &[u8], Tracked(cost): Tracked<&mut Meter>)
    ensures
        final(out)@ == old(out)@ + s@,
        final(cost).n == old(cost).n + s.len(),
{
    out.extend_from_slice(s);
    proof {
        cost.n = (cost.n + s.len()) as nat;
        assert forall|i: int| 0 <= i < final(out)@.len() implies #[trigger] final(out)@[i] == (old(
            out,
        )@ + s@)[i] by {
            if i >= old(out)@.len() {
                assert(cloned::<u8>(s@[i - old(out)@.len()], final(out)@[i]));
            }
        }
        assert(final(out)@ =~= old(out)@ + s@);
    }
}

/// Appends `s[a..b]` to `out`.
pub fn append_range(out: &mut Vec<u8>, s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>)
    requires
        a <= b <= s.len(),
    ensures
        final(out)@ == old(out)@ + s@.subrange(a as int, b as int),
        final(cost).n == old(cost).n + (b - a),
{
    append(out, vstd::slice::slice_subrange(s, a, b), Tracked(cost));
}

/// The class bit of an encode set.
pub open spec fn set_bit_spec(set: EncodeSet) -> u16 {
    match set {
        EncodeSet::C0Control => C0,
        EncodeSet::Fragment => FRAGMENT,
        EncodeSet::Query => QUERY,
        EncodeSet::SpecialQuery => SPECIAL_QUERY,
        EncodeSet::Path => PATH,
        EncodeSet::Userinfo => USERINFO,
    }
}

pub fn set_bit(set: EncodeSet) -> (r: u16)
    ensures
        r == set_bit_spec(set),
        forall|c: u8| #[trigger] cls_has(c, r) == in_encode_set(set, c),
{
    proof {
        lemma_cls();
    }
    match set {
        EncodeSet::C0Control => C0,
        EncodeSet::Fragment => FRAGMENT,
        EncodeSet::Query => QUERY,
        EncodeSet::SpecialQuery => SPECIAL_QUERY,
        EncodeSet::Path => PATH,
        EncodeSet::Userinfo => USERINFO,
    }
}

pub proof fn lemma_and_or(x: u16, a: u16, b: u16)
    ensures
        (x & (a | b) != 0) == (x & a != 0 || x & b != 0),
{
    assert((x & (a | b) != 0) == (x & a != 0 || x & b != 0)) by (bit_vector);
}

pub fn in_set(set: EncodeSet, c: u8) -> (r: bool)
    ensures
        r == in_encode_set(set, c),
{
    let m = set_bit(set);
    proof {
        assert(cls_has(c, m) == in_encode_set(set, c));
    }
    cls(c) & m != 0
}

pub fn upper_hex(n: u8) -> (r: u8)
    requires
        n < 16,
    ensures
        r == upper_hex_digit(n as nat),
{
    if n < 10 {
        b'0' + n
    } else {
        b'A' + n - 10
    }
}

/// Appends `pe(c, set)` to `out`.
pub fn push_pe(out: &mut Vec<u8>, c: u8, set: EncodeSet)
    ensures
        final(out)@ == old(out)@ + pe(c, set),
{
    if in_set(set, c) {
        out.push(b'%');
        out.push(upper_hex(c / 16));
        out.push(upper_hex(c % 16));
        proof {
            assert(final(out)@ =~= old(out)@ + pe(c, set));
        }
    } else {
        out.push(c);
        proof {
            assert(final(out)@ =~= old(out)@ + pe(c, set));
        }
    }
}

pub proof fn lemma_pe_seq_push(s: Seq<u8>, c: u8, set: EncodeSet)
    ensures
        pe_seq(s.push(c), set) == pe_seq(s, set) + pe(c, set),
{
    assert(s.push(c).drop_last() =~= s);
}

pub proof fn lemma_pe_seq_append(a: Seq<u8>, b: Seq<u8>, set: EncodeSet)
    ensures
        pe_seq(a + b, set) == pe_seq(a, set) + pe_seq(b, set),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(pe_seq(b, set) =~= Seq::<u8>::empty());
        assert(pe_seq(a, set) + pe_seq(b, set) =~= pe_seq(a, set));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_pe_seq_append(a, b.drop_last(), set);
        assert(pe_seq(a + b, set) =~= pe_seq(a, set) + pe_seq(b, set));
    }
}

/// `pe_seq` leaves strings without bytes in the set unchanged.
pub proof fn lemma_pe_seq_identity(s: Seq<u8>, set: EncodeSet)
    requires
        forall|i: int| 0 <= i < s.len() ==> !in_encode_set(set, #[trigger] s[i]),
    ensures
        pe_seq(s, set) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_pe_seq_identity(s.drop_last(), set);
        assert(!in_encode_set(set, s[s.len() - 1]));
        assert(s.drop_last().push(s.last()) =~= s);
    } else {
        assert(s =~= Seq::<u8>::empty());
    }
}

pub proof fn lemma_pe_len(c: u8, set: EncodeSet)
    ensures
        1 <= pe(c, set).len() <= 3,
{
}

/// Percent-encoding at most triples the length.
pub proof fn lemma_pe_seq_len(s: Seq<u8>, set: EncodeSet)
    ensures
        s.len() <= pe_seq(s, set).len() <= 3 * s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_pe_seq_len(s.drop_last(), set);
        lemma_pe_len(s.last(), set);
    }
}

/// Skips 16-byte blocks of `s[i..b]` with no `maybe(kind, _)` byte, with
/// one SIMD test each.
#[inline(always)]
fn skip_clean(s: &[u8], i: usize, b: usize, kind: u8, Tracked(cost): Tracked<&mut Meter>) -> (j: usize)
    requires
        i <= b <= s.len(),
        kind == K_FRAG || kind == K_QUERY,
    ensures
        i <= j <= b,
        forall|k: int| i <= k < j ==> !maybe(kind, #[trigger] s@[k]),
        final(cost).n == old(cost).n + (j - i),
{
    let mut j = i;
    while b - j >= 16 && crate::simd::clean16(s, j, kind)
        invariant
            i <= j <= b <= s.len(),
            kind == K_FRAG || kind == K_QUERY,
            forall|k: int| i <= k < j ==> !maybe(kind, #[trigger] s@[k]),
            cost.n == old(cost).n + (j - i),
        decreases b - j,
    {
        proof {
            cost.n = cost.n + 16;
            assert forall|k: int| i <= k < j + 16 implies !maybe(kind, #[trigger] s@[k]) by {
            }
        }
        j = j + 16;
    }
    j
}

/// Appends `pe_seq(s[a..b], set)` to `out`: runs of bytes outside the set
/// are copied with one `memcpy` each.
#[verifier::rlimit(40)]
pub fn append_pe(out: &mut Vec<u8>, s: &[u8], a: usize, b: usize, set: EncodeSet, Tracked(cost): Tracked<&mut Meter>)
    requires
        a <= b <= s.len(),
    ensures
        final(out)@ == old(out)@ + pe_seq(s@.subrange(a as int, b as int), set),
        final(cost).n <= old(cost).n + 3 * (b - a),
{
    let mut i = a;
    let m = set_bit(set);
    proof {
        assert(s@.subrange(a as int, a as int) =~= Seq::<u8>::empty());
        assert(old(out)@ + pe_seq(Seq::<u8>::empty(), set) =~= old(out)@);
    }
    while i < b
        invariant
            a <= i <= b <= s.len(),
            forall|c: u8| #[trigger] cls_has(c, m) == in_encode_set(set, c),
            out@ == old(out)@ + pe_seq(s@.subrange(a as int, i as int), set),
            cost.n <= old(cost).n + 3 * (i - a),
        decreases b - i,
    {
        // The run s[i..j] needs no encoding. A fragment skips clean
        // 16-byte windows first.
        let mut j = i;
        if let EncodeSet::Fragment = set {
            let ghost c0 = cost.n;
            j = skip_clean(s, i, b, K_FRAG, Tracked(cost));
            proof {
                assert(cost.n == c0 + (j - i));
                assert forall|k: int| i <= k < j implies !in_encode_set(set, #[trigger] s@[k]) by {
                    assert(!maybe(K_FRAG, s@[k]));
                }
            }
        }
        while j < b && cls(s[j]) & m == 0
            invariant
                i <= j <= b <= s.len(),
                forall|c: u8| #[trigger] cls_has(c, m) == in_encode_set(set, c),
                forall|k: int| i <= k < j ==> !in_encode_set(set, #[trigger] s@[k]),
                cost.n <= old(cost).n + 3 * (i - a) + (j - i),
            decreases b - j,
        {
            proof {
                cost.n = cost.n + 1;
            }
            proof {
                assert(cls_has(s@[j as int], m) == in_encode_set(set, s@[j as int]));
            }
            j = j + 1;
        }
        proof {
            let run = s@.subrange(i as int, j as int);
            assert forall|k: int| 0 <= k < run.len() implies !in_encode_set(set, #[trigger] run[k]) by {
                assert(run[k] == s@[i + k]);
            }
            lemma_pe_seq_identity(run, set);
            lemma_pe_seq_append(s@.subrange(a as int, i as int), run, set);
            assert(s@.subrange(a as int, i as int) + run =~= s@.subrange(a as int, j as int));
        }
        append_range(out, s, i, j, Tracked(cost));
        i = j;
        if i < b {
            proof {
                cost.n = cost.n + 1;
                lemma_pe_seq_push(s@.subrange(a as int, i as int), s@[i as int], set);
                assert(s@.subrange(a as int, i as int).push(s@[i as int]) =~= s@.subrange(
                    a as int,
                    i + 1,
                ));
            }
            push_pe(out, s[i], set);
            i = i + 1;
        }
    }
}


/// Appends `pe_seq(s[a..k], set)` to `out`, where `k` is the first index in
/// `a..b` whose byte has a class bit in `stop` (or `b`).
pub fn append_pe_until(out: &mut Vec<u8>, s: &[u8], a: usize, b: usize, set: EncodeSet, stop: u16, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
    ensures
        a <= k <= b,
        final(cost).n <= old(cost).n + 22 * (k - a) + 21,
        final(out)@ == old(out)@ + pe_seq(s@.subrange(a as int, k as int), set),
        forall|j: int| a <= j < k ==> !cls_has(#[trigger] s@[j], stop),
        k < b ==> cls_has(s@[k as int], stop),
{
    let mut i = a;
    let m = set_bit(set);
    let any = m | stop;
    proof {
        assert(s@.subrange(a as int, a as int) =~= Seq::<u8>::empty());
        assert(old(out)@ + pe_seq(Seq::<u8>::empty(), set) =~= old(out)@);
        assert forall|c: u8| #[trigger] cls_has(c, any) implies in_encode_set(set, c) || cls_has(c, stop) by {
            lemma_and_or(CLS@[c as int], m, stop);
            assert(cls_has(c, m) == in_encode_set(set, c));
        }
    }
    loop
        invariant
            a <= i <= b <= s.len(),
            any == m | stop,
            forall|c: u8| #[trigger] cls_has(c, m) == in_encode_set(set, c),
            forall|c: u8| #[trigger] cls_has(c, any) ==> in_encode_set(set, c) || cls_has(c, stop),
            out@ == old(out)@ + pe_seq(s@.subrange(a as int, i as int), set),
            forall|j: int| a <= j < i ==> !cls_has(#[trigger] s@[j], stop),
            cost.n <= old(cost).n + 22 * (i - a),
        decreases b - i,
    {
        let j = find_any(s, i, b, set, stop, any, Tracked(cost));
        proof {
            assert forall|k: int| i <= k < j implies !in_encode_set(set, #[trigger] s@[k]) && !cls_has(s@[k], stop) by {
                lemma_and_or(CLS@[s@[k] as int], m, stop);
                assert(!cls_has(s@[k], any));
                assert(cls_has(s@[k], m) == in_encode_set(set, s@[k]));
            }
            if j < b {
                lemma_and_or(CLS@[s@[j as int] as int], m, stop);
            }
        }
        proof {
            let run = s@.subrange(i as int, j as int);
            assert forall|k: int| 0 <= k < run.len() implies !in_encode_set(set, #[trigger] run[k]) by {
                assert(run[k] == s@[i + k]);
            }
            lemma_pe_seq_identity(run, set);
            lemma_pe_seq_append(s@.subrange(a as int, i as int), run, set);
            assert(s@.subrange(a as int, i as int) + run =~= s@.subrange(a as int, j as int));
        }
        append_range(out, s, i, j, Tracked(cost));
        i = j;
        if i >= b {
            return i;
        }
        let c = s[i];
        if cls(c) & stop != 0 {
            return i;
        }
        proof {
            lemma_pe_seq_push(s@.subrange(a as int, i as int), c, set);
            assert(s@.subrange(a as int, i as int).push(c) =~= s@.subrange(a as int, i + 1));
        }
        push_pe(out, c, set);
        i = i + 1;
    }
}


/// Byte kinds the block scans test for with plain comparisons, which the
/// compiler vectorizes; each is a superset of the bytes a table scan stops at.
pub const K_QUERY: u8 = 0;

pub const K_PATH: u8 = 1;

pub const K_FRAG: u8 = 2;

pub open spec fn maybe(kind: u8, c: u8) -> bool {
    if kind == K_QUERY {
        // The query and special-query percent-encode sets.
        c <= 0x20 || c >= 0x7F || c == 0x22 || c == 0x23 || c == 0x27 || c == 0x3C || c == 0x3E
    } else if kind == K_PATH {
        // The path percent-encode set, ".", "%" and "\\".
        c <= 0x20 || c >= 0x7F || c == 0x22 || c == 0x23 || c == 0x25 || c == 0x2E || c == 0x3C
            || c == 0x3E || c == 0x3F || c == 0x5C || c == 0x5E || c == 0x60 || c == 0x7B || c
            == 0x7D
    } else if kind == K_FRAG {
        // The fragment percent-encode set.
        c <= 0x20 || c >= 0x7F || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x60
    } else {
        false
    }
}

#[inline(always)]
fn maybe_exec(kind: u8, c: u8) -> (r: bool)
    ensures
        r == maybe(kind, c),
{
    if kind == K_QUERY {
        (c <= 0x20) | (c >= 0x7F) | (c == 0x22) | (c == 0x23) | (c == 0x27) | (c == 0x3C) | (c
            == 0x3E)
    } else if kind == K_PATH {
        (c <= 0x20) | (c >= 0x7F) | (c == 0x22) | (c == 0x23) | (c == 0x25) | (c == 0x2E) | (c
            == 0x3C) | (c == 0x3E) | (c == 0x3F) | (c == 0x5C) | (c == 0x5E) | (c == 0x60) | (c
            == 0x7B) | (c == 0x7D)
    } else if kind == K_FRAG {
        (c <= 0x20) | (c >= 0x7F) | (c == 0x22) | (c == 0x3C) | (c == 0x3E) | (c == 0x60)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// 16-byte masks: bit i says whether byte i stops a scan, so the first
// stopping byte is the mask's trailing zero count (one vector compare and
// a `tzcnt` in place of a byte loop).
// ---------------------------------------------------------------------------

pub proof fn lemma_mask_bit(m: u32, x: u32, i: u32, j: u32)
    requires
        i < 16,
        x <= 1,
        m < (1u32 << i),
        j < 16,
    ensures
        (m | (x << i)) < (1u32 << (i + 1) as u32),
        j == i ==> ((m | (x << i)) >> j) & 1 == x,
        j < i ==> ((m | (x << i)) >> j) & 1 == (m >> j) & 1,
{
    let i1 = (i + 1) as u32;
    assert((m | (x << i)) < (1u32 << i1)) by (bit_vector)
        requires
            i < 16,
            x <= 1,
            m < (1u32 << i),
            i1 == i + 1,
    ;
    assert(j == i ==> ((m | (x << i)) >> j) & 1 == x) by (bit_vector)
        requires
            i < 16,
            x <= 1,
            m < (1u32 << i),
            j < 16,
    ;
    assert(j < i ==> ((m | (x << i)) >> j) & 1 == (m >> j) & 1) by (bit_vector)
        requires
            i < 16,
            x <= 1,
            m < (1u32 << i),
            j < 16,
    ;
}

pub proof fn lemma_mask_clear(m: u32, d: u32, j: u32)
    requires
        1 <= d <= 16,
        j < 16,
    ensures
        ((m & !(((1u32 << d) - 1) as u32)) >> j) & 1 == (if j < d { 0 } else { (m >> j) & 1 }),
{
    assert(((m & !(((1u32 << d) - 1) as u32)) >> j) & 1 == (if j < d { 0 } else { (m >> j) & 1 }))
        by (bit_vector)
        requires
            1 <= d <= 16,
            j < 16,
    ;
}

/// For a nonzero mask below 2^16: its trailing zero count `t` is below 16,
/// bit `t` is set and the bits below it are clear.
pub proof fn lemma_mask_tz(m: u32)
    requires
        m != 0,
        m < 0x10000,
    ensures
        m.trailing_zeros() < 16,
        (m >> m.trailing_zeros()) & 1 == 1,
        forall|j: u32| j < m.trailing_zeros() ==> (m >> j) & 1 == 0,
{
    broadcast use vstd::std_specs::bits::axiom_u32_trailing_zeros;

    let t = m.trailing_zeros();
    assert(t < 32);
    assert((m >> t) & 1 == 1);
    assert(m < 0x10000 && t < 32 && (m >> t) & 1 == 1 ==> t < 16) by (bit_vector);
    assert forall|j: u32| j < t implies (m >> j) & 1 == 0 by {
        assert((m >> j) & 1u32 == 0u32);
    }
}

/// Bit `i` is set exactly when `maybe(kind, w[i])`.
#[inline(always)]
pub fn maybe_mask16(w: &[u8], kind: u8) -> (m: u32)
    requires
        w.len() == 16,
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> (((m >> j) & 1) == 1) == maybe(kind, #[trigger] w@[j as int]),
{
    if (kind == K_FRAG || kind == K_QUERY) && verilith_simd::neon::has_neon() {
        return crate::simd::maybe_mask16_neon(w, kind);
    }
    let mut m: u32 = 0;
    let mut i: u32 = 0;
    proof {
        assert((1u32 << 0u32) == 1u32) by (bit_vector);
    }
    while i < 16
        invariant
            i <= 16,
            w.len() == 16,
            m < (1u32 << i),
            forall|j: u32| j < i ==> (((m >> j) & 1) == 1) == maybe(kind, #[trigger] w@[j as int]),
        decreases 16 - i,
    {
        // A cast, not an `if`, so the compiler vectorizes the loop.
        let x = maybe_exec(kind, w[i as usize]) as u32;
        proof {
            assert forall|j: u32| j < i + 1 implies (((m | (x << i)) >> j) & 1 == 1) == maybe(
                kind,
                #[trigger] w@[j as int],
            ) by {
                lemma_mask_bit(m, x, i, j);
            }
            lemma_mask_bit(m, x, i, 0);
        }
        m = m | (x << i);
        i = i + 1;
    }
    proof {
        assert((1u32 << 16u32) == 0x10000u32) by (bit_vector);
    }
    m
}

/// From `w`, skips bytes that are not `maybe(kind, _)` by looking at one
/// 16-byte window: the one at `w`, or the last one of `s[..b]` if fewer
/// than 16 bytes remain.
#[inline(always)]
pub fn skip_window(s: &[u8], w: usize, b: usize, kind: u8) -> (k: usize)
    requires
        w <= b <= s.len(),
    ensures
        w <= k <= b,
        forall|j: int| w <= j < k ==> !maybe(kind, #[trigger] s@[j]),
{
    if b - w >= 16 {
        let win = vstd::slice::slice_subrange(s, w, w + 16);
        let m = maybe_mask16(win, kind);
        if m != 0 {
            let t = m.trailing_zeros();
            proof {
                lemma_mask_tz(m);
                assert forall|j: int| w <= j < w + t implies !maybe(kind, #[trigger] s@[j]) by {
                    assert(s@[j] == win@[(j - w) as u32 as int]);
                    assert((m >> ((j - w) as u32)) & 1 == 0);
                }
            }
            w + t as usize
        } else {
            proof {
                assert forall|j: int| w <= j < w + 16 implies !maybe(kind, #[trigger] s@[j]) by {
                    assert(s@[j] == win@[(j - w) as u32 as int]);
                    assert((m >> ((j - w) as u32)) & 1 == 0) by {
                        let jj = (j - w) as u32;
                        assert(m == 0 ==> (m >> jj) & 1 == 0) by (bit_vector);
                    }
                }
            }
            w + 16
        }
    } else if b >= 16 && w < b {
        let st = b - 16;
        let win = vstd::slice::slice_subrange(s, st, b);
        let d = (w - st) as u32;
        let m0 = maybe_mask16(win, kind);
        proof {
            assert(1 <= d <= 16 ==> (1u32 << d) >= 1) by (bit_vector);
        }
        let m = m0 & !((1u32 << d) - 1);
        proof {
            assert(m <= m0) by (bit_vector)
                requires
                    m == m0 & !(((1u32 << d) - 1) as u32),
            ;
        }
        if m == 0 {
            proof {
                assert forall|j: int| w <= j < b implies !maybe(kind, #[trigger] s@[j]) by {
                    let jj = (j - st) as u32;
                    assert(s@[j] == win@[jj as int]);
                    lemma_mask_clear(m0, d, jj);
                    assert(m == 0 ==> (m >> jj) & 1 == 0) by (bit_vector);
                }
            }
            b
        } else {
            let t = m.trailing_zeros();
            proof {
                lemma_mask_tz(m);
                lemma_mask_clear(m0, d, t);
                assert forall|j: int| w <= j < st + t implies !maybe(kind, #[trigger] s@[j]) by {
                    let jj = (j - st) as u32;
                    assert(s@[j] == win@[jj as int]);
                    lemma_mask_clear(m0, d, jj);
                    assert((m >> jj) & 1 == 0);
                }
            }
            st + t as usize
        }
    } else {
        w
    }
}

/// Whether some byte of `w` is `maybe(kind, _)`, without early exits.
#[inline(always)]
fn any_maybe(w: &[u8], kind: u8, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    ensures
        !r ==> forall|j: int| 0 <= j < w.len() ==> !maybe(kind, #[trigger] w@[j]),
        final(cost).n == old(cost).n + w.len(),
{
    let mut acc = false;
    let mut i = 0;
    while i < w.len()
        invariant
            i <= w.len(),
            !acc ==> forall|j: int| 0 <= j < i ==> !maybe(kind, #[trigger] w@[j]),
            cost.n == old(cost).n + i,
        decreases w.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        acc = acc | maybe_exec(kind, w[i]);
        i = i + 1;
    }
    acc
}

/// Skips `n`-byte blocks of `s[a..b]` with no `maybe(kind, _)` byte.
#[inline(always)]
pub fn skip_blocks(s: &[u8], a: usize, b: usize, kind: u8, n: usize, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
        n > 0,
    ensures
        a <= k <= b,
        forall|j: int| a <= j < k ==> !maybe(kind, #[trigger] s@[j]),
        final(cost).n <= old(cost).n + 2 * (k - a) + n + 1,
{
    let t = vstd::slice::slice_subrange(s, 0, b);
    let mut k = a;
    while b - k >= n
        invariant_except_break
            cost.n <= old(cost).n + 2 * (k - a),
        invariant
            a <= k <= b <= s.len(),
            n > 0,
            t@ == s@.subrange(0, b as int),
            forall|j: int| a <= j < k ==> !maybe(kind, #[trigger] s@[j]),
        ensures
            cost.n <= old(cost).n + 2 * (k - a) + n + 1,
        decreases b - k,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let w = vstd::slice::slice_subrange(t, k, k + n);
        if any_maybe(w, kind, Tracked(cost)) {
            break;
        }
        proof {
            assert forall|j: int| a <= j < k + n implies !maybe(kind, #[trigger] s@[j]) by {
                if j >= k {
                    assert(s@[j] == w@[j - k]);
                }
            }
        }
        k = k + n;
    }
    k
}

/// `find_cls(s, a, b, any)`, skipping clean 16-byte blocks of a query first.
#[inline(always)]
fn find_any(s: &[u8], a: usize, b: usize, set: EncodeSet, stop: u16, any: u16, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
        forall|c: u8| #[trigger] cls_has(c, any) ==> in_encode_set(set, c) || cls_has(c, stop),
    ensures
        a <= k <= b,
        final(cost).n <= old(cost).n + 2 * (k - a) + 18,
        forall|j: int| a <= j < k ==> !cls_has(#[trigger] s@[j], any),
        k < b ==> cls_has(s@[k as int], any),
{
    let query = match set {
        EncodeSet::Query | EncodeSet::SpecialQuery => stop == HASH,
        _ => false,
    };
    let w = if query {
        let w0 = skip_clean(s, a, b, K_QUERY, Tracked(cost));
        // The block that stopped the scan, or the short tail: a mask finds
        // the first byte to look at instead of a byte loop.
        let w1 = skip_window(s, w0, b, K_QUERY);
        proof {
            assert forall|j: int| a <= j < w1 implies !maybe(K_QUERY, #[trigger] s@[j]) by {
                if j >= w0 {
                }
            }
        }
        w1
    } else {
        a
    };
    proof {
        if w > a {
            lemma_cls();
            assert forall|k: int| a <= k < w implies !cls_has(#[trigger] s@[k], any) by {
                assert(cls_has(s@[k], HASH) == cls_pred(HASH, s@[k]));
            }
        }
    }
    let j = find_cls(s, w, b, any, Tracked(cost));
    proof {
        assert forall|k: int| a <= k < j implies !cls_has(#[trigger] s@[k], any) by {
            if k >= w {
            }
        }
    }
    j
}

/// The first index in `a..b` whose byte is in the special-query
/// percent-encode set (which holds "#"), or `b`: clean 16-byte blocks are
/// skipped with one SIMD test each.
pub fn scan_special_query(s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
    ensures
        a <= k <= b,
        final(cost).n <= old(cost).n + 2 * (k - a) + 18,
        forall|j: int| a <= j < k ==> !in_special_query_set(#[trigger] s@[j]),
        k < b ==> in_special_query_set(s@[k as int]),
{
    let any = SPECIAL_QUERY | HASH;
    proof {
        lemma_cls();
        assert forall|c: u8| #[trigger] cls_has(c, any) implies in_encode_set(EncodeSet::SpecialQuery, c)
            || cls_has(c, HASH) by {
            lemma_and_or(CLS@[c as int], SPECIAL_QUERY, HASH);
            assert(cls_has(c, SPECIAL_QUERY) == cls_pred(SPECIAL_QUERY, c));
        }
    }
    let k = find_any(s, a, b, EncodeSet::SpecialQuery, HASH, any, Tracked(cost));
    proof {
        assert forall|j: int| a <= j < k implies !in_special_query_set(#[trigger] s@[j]) by {
            lemma_and_or(CLS@[s@[j] as int], SPECIAL_QUERY, HASH);
            assert(cls_has(s@[j], SPECIAL_QUERY) == cls_pred(SPECIAL_QUERY, s@[j]));
        }
        if k < b {
            let c = s@[k as int];
            lemma_and_or(CLS@[c as int], SPECIAL_QUERY, HASH);
            assert(cls_has(c, SPECIAL_QUERY) == cls_pred(SPECIAL_QUERY, c));
            assert(cls_has(c, HASH) == cls_pred(HASH, c));
        }
    }
    k
}

/// The first index in `a..b` whose byte is in the fragment percent-encode
/// set, or `b`: clean 16-byte blocks are skipped with one SIMD test each.
pub fn scan_fragment(s: &[u8], a: usize, b: usize, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
    ensures
        a <= k <= b,
        final(cost).n <= old(cost).n + (k - a) + 1,
        forall|j: int| a <= j < k ==> !in_fragment_set(#[trigger] s@[j]),
        k < b ==> in_fragment_set(s@[k as int]),
{
    let w = skip_clean(s, a, b, K_FRAG, Tracked(cost));
    let k = find_cls(s, w, b, FRAGMENT, Tracked(cost));
    proof {
        lemma_cls();
        assert forall|j: int| a <= j < k implies !in_fragment_set(#[trigger] s@[j]) by {
            if j >= w {
                assert(cls_has(s@[j], FRAGMENT) == cls_pred(FRAGMENT, s@[j]));
            } else {
                assert(!maybe(K_FRAG, s@[j]));
            }
        }
        if k < b {
            assert(cls_has(s@[k as int], FRAGMENT) == cls_pred(FRAGMENT, s@[k as int]));
        }
    }
    k
}

pub proof fn lemma_or_and(a: u16, b: u16, m: u16)
    ensures
        ((a | b) & m == 0) == (a & m == 0 && b & m == 0),
{
    assert(((a | b) & m == 0) == (a & m == 0 && b & m == 0)) by (bit_vector);
}

/// The first index in `a..b` whose byte has a class bit in `m`, or `b`.
#[inline(always)]
pub fn find_cls(s: &[u8], a: usize, b: usize, m: u16, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        a <= b <= s.len(),
    ensures
        a <= k <= b,
        final(cost).n == old(cost).n + (k - a) + 1,
        forall|j: int| a <= j < k ==> !cls_has(#[trigger] s@[j], m),
        k < b ==> cls_has(s@[k as int], m),
{
    // Working on s[..b] lets the compiler drop the bounds checks.
    let t = vstd::slice::slice_subrange(s, 0, b);
    let n = t.len();
    let mut k = a;
    while k < n && cls(t[k]) & m == 0
        invariant
            a <= k <= n == b <= s.len(),
            t@ == s@.subrange(0, b as int),
            forall|j: int| a <= j < k ==> !cls_has(#[trigger] s@[j], m),
            cost.n == old(cost).n + (k - a),
        decreases n - k,
    {
        proof {
            cost.n = cost.n + 1;
        }
        k = k + 1;
    }
    proof {
        cost.n = cost.n + 1;
    }
    k
}

} // verus!
