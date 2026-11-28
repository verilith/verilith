//! The byte scans of the libxml2 layer's second pass over the tape (runs
//! of libxml2's "plain" character data, attribute values passed as they
//! are, and the line ends and UTF-8 continuation bytes that line and
//! column tracking counts), proven to compute what their spec functions
//! say. On x86-64 they read 16 bytes at a time with SSE2, through
//! verilith-simd's verified `sse2` wrappers (`crate::lanes`); nothing here
//! is trusted. Other targets keep the eight-bytes-at-a-time code in
//! `api::libxml2::scan`.
#[allow(unused_imports)]
use crate::lanes::*;
use vstd::prelude::*;

verus! {

/// Not in libxml2's fast path for character data (`xmlParseCharData`):
/// anything but tab and 0x20 to 0x7F, and `<`, `&` and `]`.
pub open spec fn plain_stop(c: u8) -> bool {
    !(c == 0x09 || (0x20 <= c < 0x80 && c != 0x3C && c != 0x26 && c != 0x5D))
}

/// Stops an attribute value from being passed as it is: `&` or a byte
/// below 0x20.
pub open spec fn att_bad(c: u8) -> bool {
    c < 0x20 || c == 0x26
}

/// Not tab, line feed or 0x20 to 0x7F.
pub open spec fn text_bad(c: u8) -> bool {
    !(c == 0x09 || c == 0x0A || (0x20 <= c < 0x80))
}

/// Space or line feed.
pub open spec fn blank(c: u8) -> bool {
    c == 0x20 || c == 0x0A
}

/// A UTF-8 continuation byte, `10xxxxxx`.
pub open spec fn cont(c: u8) -> bool {
    0x80 <= c < 0xC0
}

pub open spec fn is_nl(c: u8) -> bool {
    c == 0x0A
}

/// What a count counts.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Line feeds (`is_nl`).
    Nl,
    /// UTF-8 continuation bytes (`cont`).
    Cont,
}

pub open spec fn is_kind(f: Kind, c: u8) -> bool {
    match f {
        Kind::Nl => is_nl(c),
        Kind::Cont => cont(c),
    }
}

/// How many of `s[0..j]` are of kind `f`.
pub open spec fn cnt(s: Seq<u8>, f: Kind, j: int) -> nat
    decreases j,
{
    if j <= 0 {
        0
    } else {
        cnt(s, f, j - 1) + if is_kind(f, s[j - 1]) { 1nat } else { 0nat }
    }
}

/// The positions of the line feeds in `s[0..j]`, in order.
pub open spec fn nl_pos(s: Seq<u8>, j: int) -> Seq<int>
    decreases j,
{
    if j <= 0 {
        Seq::empty()
    } else if s[j - 1] == 0x0A {
        nl_pos(s, j - 1).push(j - 1)
    } else {
        nl_pos(s, j - 1)
    }
}

/// Positions without a line feed add none.
pub proof fn lemma_nl_skip(s: Seq<u8>, p: int, q: int)
    requires
        0 <= p <= q <= s.len(),
        forall|j: int| p <= j < q ==> #[trigger] s[j] != 0x0A,
    ensures
        nl_pos(s, q) == nl_pos(s, p),
    decreases q - p,
{
    if p < q {
        lemma_nl_skip(s, p, q - 1);
    }
}

} // verus!

#[cfg(target_arch = "x86_64")]
verus! {

use verilith_simd::arch::__m128i;
#[cfg(verus_only)]
use verilith_simd::ops::{popcount64, set_bits};
use verilith_simd::scalar::popcnt64;

/// Lanes equal to `c` have their top bit set, the others not.
#[inline(always)]
fn eqc(v: __m128i, c: u8) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(v)[k] == c),
{
    eq16(v, splat16(c))
}

/// Lanes at most `c` have their top bit set, the others not.
#[inline(always)]
fn lec(v: __m128i, c: u8) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(v)[k] <= c),
{
    eq16(min16(v, splat16(c)), v)
}

/// Top bits of `a | b`, lane by lane.
#[inline(always)]
fn or2(a: __m128i, b: __m128i) -> (r: __m128i)
    ensures
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(r)[k] >= 0x80) == (b16(a)[k] >= 0x80 || b16(b)[k] >= 0x80),
{
    let r = or16(a, b);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(r)[k] >= 0x80) == (b16(a)[k] >= 0x80 || b16(b)[k]
            >= 0x80) by {
            lemma_top_or(b16(a)[k], b16(b)[k]);
        }
    }
    r
}

/// The movemask of `x`, whose lane `k` has its top bit set exactly where
/// `f(s[i + k])`.
#[inline(always)]
#[allow(unused_variables)]
fn mask_of(x: __m128i, s: &[u8], i: usize, Ghost(f): Ghost<spec_fn(u8) -> bool>) -> (m: u32)
    requires
        i + 16 <= s@.len(),
        forall|k: int| 0 <= k < 16 ==> (#[trigger] b16(x)[k] >= 0x80) == f(s@[i + k]),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == f(s@[i + k]),
{
    let m = movemask16(x);
    proof {
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == f(s@[i + k]) by {
            assert((b16(x)[k as int] >= 0x80) == f(s@[i + k as int]));
        }
    }
    m
}

/// The bytes of `v` are `s[i..i + 16]`.
proof fn lemma_lanes(v: __m128i, s: Seq<u8>, i: int)
    requires
        0 <= i,
        i + 16 <= s.len(),
        b16(v) == s.subrange(i, i + 16),
    ensures
        forall|k: int| 0 <= k < 16 ==> #[trigger] b16(v)[k] == s[i + k],
{
    assert forall|k: int| 0 <= k < 16 implies #[trigger] b16(v)[k] == s[i + k] by {
        assert(s.subrange(i, i + 16)[k] == s[i + k]);
    }
}

#[verifier::bit_vector]
proof fn lemma_zero_bit(m: u32, k: u32)
    requires
        m == 0u32,
    ensures
        !((m >> k) & 1u32 == 1u32),
{
}

/// Bit `k` of `m`: as `bit`, and as `set_bits` reads it.
#[verifier::bit_vector]
proof fn lemma_bit64(m: u32, k: u32)
    requires
        k < 32,
    ensures
        ((m >> k) & 1u32 == 1u32) == (((m as u64) >> (k as u64)) & 1u64 == 1u64),
{
}

#[verifier::bit_vector]
proof fn lemma_high_clear(m: u32, k: u64)
    requires
        m < 0x10000,
        16 <= k < 64,
    ensures
        ((m as u64) >> k) & 1u64 == 0u64,
{
}

/// The set bits of a 16-bit mask are its set bits below 16.
proof fn lemma_set_bits16(m: u32, n: nat)
    requires
        m < 0x10000,
        16 <= n <= 64,
    ensures
        set_bits(m as u64, n) == set_bits(m as u64, 16),
    decreases n,
{
    if n > 16 {
        lemma_set_bits16(m, (n - 1) as nat);
        lemma_high_clear(m, (n - 1) as u64);
    }
}

/// Counting 16 bytes by their mask.
proof fn lemma_cnt_block(s: Seq<u8>, f: Kind, i: int, m: u32, t: nat)
    requires
        0 <= i,
        i + 16 <= s.len(),
        t <= 16,
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == is_kind(f, s[i + k]),
    ensures
        cnt(s, f, i + t) == cnt(s, f, i) + set_bits(m as u64, t).len(),
    decreases t,
{
    if t > 0 {
        lemma_cnt_block(s, f, i, m, (t - 1) as nat);
        let k = (t - 1) as u32;
        lemma_bit64(m, k);
        assert(bit(m, k) == is_kind(f, s[i + k]));
        assert(i + t - 1 == i + k);
    }
}

/// `popcnt` of a mask is the count of its 16 bytes.
proof fn lemma_cnt16(s: Seq<u8>, f: Kind, i: int, m: u32)
    requires
        0 <= i,
        i + 16 <= s.len(),
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == is_kind(f, s[i + k]),
    ensures
        cnt(s, f, i + 16) == cnt(s, f, i) + popcount64(m as u64),
{
    lemma_cnt_block(s, f, i, m, 16);
    lemma_set_bits16(m, 64);
}

proof fn lemma_cnt_bound(s: Seq<u8>, f: Kind, j: int)
    requires
        0 <= j,
    ensures
        cnt(s, f, j) <= j,
    decreases j,
{
    if j > 0 {
        lemma_cnt_bound(s, f, j - 1);
    }
}

/// Bit `k` of `a | b | c` and of `a & !b`.
#[verifier::bit_vector]
proof fn lemma_bits3(a: u32, b: u32, c: u32, k: u32)
    requires
        k < 32,
    ensures
        (((a | (b & !c)) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) || (((b >> k) & 1u32 == 1u32)
            && !((c >> k) & 1u32 == 1u32))),
        (((a | b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) || ((b >> k) & 1u32 == 1u32)),
        (((a & b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) && ((b >> k) & 1u32 == 1u32)),
        (((a & !b) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) && !((b >> k) & 1u32 == 1u32)),
{
}

#[verifier::bit_vector]
proof fn lemma_bounds16(a: u32, b: u32, c: u32)
    requires
        a < 0x10000,
        b < 0x10000,
        c < 0x10000,
    ensures
        a | (b & !c) < 0x10000,
        a | b < 0x10000,
        a & b < 0x10000,
        a & !b < 0x10000,
        (!a) & 0xFFFFu32 < 0x10000,
{
}

#[verifier::bit_vector]
proof fn lemma_not16(a: u32, k: u32)
    requires
        k < 16,
    ensures
        ((((!a) & 0xFFFFu32) >> k) & 1u32 == 1u32) == !((a >> k) & 1u32 == 1u32),
{
}

/// A nonzero 16-bit mask has a set bit below 16.
proof fn lemma_some_bit(m: u32)
    requires
        m < 0x10000,
    ensures
        m != 0 ==> exists|k: u32| k < 16 && #[trigger] bit(m, k),
{
    lemma_zero16(m);
    if m != 0 {
        if bit(m, 0) { assert(bit(m, 0u32)); }
        else if bit(m, 1) { assert(bit(m, 1u32)); }
        else if bit(m, 2) { assert(bit(m, 2u32)); }
        else if bit(m, 3) { assert(bit(m, 3u32)); }
        else if bit(m, 4) { assert(bit(m, 4u32)); }
        else if bit(m, 5) { assert(bit(m, 5u32)); }
        else if bit(m, 6) { assert(bit(m, 6u32)); }
        else if bit(m, 7) { assert(bit(m, 7u32)); }
        else if bit(m, 8) { assert(bit(m, 8u32)); }
        else if bit(m, 9) { assert(bit(m, 9u32)); }
        else if bit(m, 10) { assert(bit(m, 10u32)); }
        else if bit(m, 11) { assert(bit(m, 11u32)); }
        else if bit(m, 12) { assert(bit(m, 12u32)); }
        else if bit(m, 13) { assert(bit(m, 13u32)); }
        else if bit(m, 14) { assert(bit(m, 14u32)); }
        else { assert(bit(m, 15u32)); }
    }
}

#[verifier::bit_vector]
proof fn lemma_zero16(m: u32)
    requires
        m < 0x10000,
    ensures
        (!((m >> 0u32) & 1u32 == 1u32) && !((m >> 1u32) & 1u32 == 1u32) && !((m >> 2u32) & 1u32 == 1u32)
            && !((m >> 3u32) & 1u32 == 1u32) && !((m >> 4u32) & 1u32 == 1u32) && !((m >> 5u32) & 1u32 == 1u32)
            && !((m >> 6u32) & 1u32 == 1u32) && !((m >> 7u32) & 1u32 == 1u32) && !((m >> 8u32) & 1u32 == 1u32)
            && !((m >> 9u32) & 1u32 == 1u32) && !((m >> 10u32) & 1u32 == 1u32) && !((m >> 11u32) & 1u32 == 1u32)
            && !((m >> 12u32) & 1u32 == 1u32) && !((m >> 13u32) & 1u32 == 1u32) && !((m >> 14u32) & 1u32 == 1u32)
            && !((m >> 15u32) & 1u32 == 1u32)) ==> m == 0u32,
{
}

/// Bit `k` of the mask is `plain_stop(s[i + k])`.
#[inline(always)]
fn plain_mask(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == plain_stop(s@[i + k]),
{
    let v = load16(s, i);
    proof {
        lemma_lanes(v, s@, i as int);
    }
    // The top bit of the byte itself is set from 0x80 up.
    let any = mask_of(
        or2(v, or2(lec(v, 0x1F), or2(or2(eqc(v, 0x3C), eqc(v, 0x26)), eqc(v, 0x5D)))),
        s,
        i,
        Ghost(|c: u8| c >= 0x80 || c <= 0x1F || c == 0x3C || c == 0x26 || c == 0x5D),
    );
    let tab = mask_of(eqc(v, 0x09), s, i, Ghost(|c: u8| c == 0x09));
    let m = any & !tab;
    proof {
        lemma_bounds16(any, tab, 0);
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == plain_stop(s@[i + k]) by {
            let c = s@[i + k];
            assert(bit(any, k) == (c >= 0x80 || c <= 0x1F || c == 0x3C || c == 0x26 || c == 0x5D));
            assert(bit(tab, k) == (c == 0x09));
            lemma_bits3(any, tab, 0, k);
        }
    }
    m
}

/// Bit `k` of the mask is `att_bad(s[i + k])`.
#[inline(always)]
fn att_mask(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == att_bad(s@[i + k]),
{
    let v = load16(s, i);
    proof {
        lemma_lanes(v, s@, i as int);
    }
    mask_of(or2(lec(v, 0x1F), eqc(v, 0x26)), s, i, Ghost(|c: u8| att_bad(c)))
}

/// Bit `k` of the mask is `s[i + k] == c`.
#[inline(always)]
fn eq_mask(s: &[u8], i: usize, c: u8) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == (s@[i + k] == c),
{
    let v = load16(s, i);
    proof {
        lemma_lanes(v, s@, i as int);
    }
    mask_of(eqc(v, c), s, i, Ghost(|b: u8| b == c))
}

/// Bit `k` of the mask is `cont(s[i + k])`.
#[inline(always)]
fn cont_mask(s: &[u8], i: usize) -> (m: u32)
    requires
        i + 16 <= s@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == cont(s@[i + k]),
{
    let v = load16(s, i);
    proof {
        lemma_lanes(v, s@, i as int);
    }
    // 0x80 to 0xBF are the bytes below -64 as signed bytes.
    let c0 = splat16(0xC0);
    let x = verilith_simd::arch::_mm_cmpgt_epi8(c0, v);
    proof {
        assert forall|k: int| 0 <= k < 16 implies (#[trigger] b16(x)[k] >= 0x80) == cont(s@[i + k]) by {
            assert(b16(c0)[k] == 0xC0u8);
        }
    }
    mask_of(x, s, i, Ghost(|c: u8| cont(c)))
}

/// The first `j >= i` with `plain_stop(s[j])`, or `s.len()`.
#[inline]
pub fn plain_run(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s@.len(),
    ensures
        i <= r <= s@.len(),
        forall|q: int| i <= q < r ==> !plain_stop(#[trigger] s@[q]),
        r < s@.len() ==> plain_stop(s@[r as int]),
{
    let len = s.len();
    let mut p = i;
    while len - p >= 16
        invariant
            i <= p <= len == s@.len(),
            forall|q: int| i <= q < p ==> !plain_stop(#[trigger] s@[q]),
        decreases len - p,
    {
        let m = plain_mask(s, p);
        if m != 0 {
            let t = first_set16(m);
            proof {
                lemma_some_bit(m);
                assert forall|q: int| i <= q < p + t implies !plain_stop(#[trigger] s@[q]) by {
                    if q >= p {
                        assert(!bit(m, (q - p) as u32));
                        assert(s@[p + (q - p) as u32] == s@[q]);
                    }
                }
                assert(bit(m, t as u32));
            }
            return p + t;
        }
        proof {
            assert forall|q: int| i <= q < p + 16 implies !plain_stop(#[trigger] s@[q]) by {
                if q >= p {
                    lemma_zero_bit(m, (q - p) as u32);
                    assert(!bit(m, (q - p) as u32));
                    assert(s@[p + (q - p) as u32] == s@[q]);
                }
            }
        }
        p = p + 16;
    }
    while p < len && !plain_byte(s[p])
        invariant
            i <= p <= len == s@.len(),
            forall|q: int| i <= q < p ==> !plain_stop(#[trigger] s@[q]),
        decreases len - p,
    {
        p = p + 1;
    }
    p
}

/// The first `j` in `i..n` with `plain_stop(buf[j])`, or `n`; reads 16
/// bytes at a time while they are in `buf`, past `n` as well.
#[inline]
pub fn plain_run_in(buf: &[u8], i: usize, n: usize) -> (r: usize)
    requires
        i <= n <= buf@.len(),
    ensures
        i <= r <= n,
        forall|q: int| i <= q < r ==> !plain_stop(#[trigger] buf@[q]),
        r < n ==> plain_stop(buf@[r as int]),
{
    let len = buf.len();
    let mut p = i;
    while p < n && len - p >= 16
        invariant
            i <= p <= len,
            n <= len == buf@.len(),
            p < n || p >= n,
            forall|q: int| i <= q < p && q < n ==> !plain_stop(#[trigger] buf@[q]),
        decreases len - p,
    {
        let m = plain_mask(buf, p);
        let t = first_set16(m);
        if t < 16 {
            let e = p + t;
            proof {
                assert forall|q: int| i <= q < e && q < n implies !plain_stop(#[trigger] buf@[q]) by {
                    if q >= p {
                        assert(!bit(m, (q - p) as u32));
                        assert(buf@[p + (q - p) as u32] == buf@[q]);
                    }
                }
                assert(bit(m, t as u32));
            }
            return if e < n { e } else { n };
        }
        proof {
            assert forall|q: int| i <= q < p + 16 && q < n implies !plain_stop(#[trigger] buf@[q]) by {
                if q >= p {
                    assert(!bit(m, (q - p) as u32));
                    assert(buf@[p + (q - p) as u32] == buf@[q]);
                }
            }
        }
        p = p + 16;
    }
    if p >= n {
        return n;
    }
    while p < n && !plain_byte(buf[p])
        invariant
            i <= p <= n <= buf@.len(),
            forall|q: int| i <= q < p ==> !plain_stop(#[trigger] buf@[q]),
        decreases n - p,
    {
        p = p + 1;
    }
    p
}

/// `plain_stop(c)`.
#[inline(always)]
fn plain_byte(c: u8) -> (r: bool)
    ensures
        r == plain_stop(c),
{
    !(c == 0x09 || (0x20 <= c && c < 0x80 && c != 0x3C && c != 0x26 && c != 0x5D))
}

/// No byte of `s` is `att_bad`.
#[inline]
pub fn att_plain(s: &[u8]) -> (r: bool)
    ensures
        r == forall|q: int| 0 <= q < s@.len() ==> !att_bad(#[trigger] s@[q]),
{
    let len = s.len();
    let mut p: usize = 0;
    while len - p >= 16
        invariant
            p <= len == s@.len(),
            forall|q: int| 0 <= q < p ==> !att_bad(#[trigger] s@[q]),
        decreases len - p,
    {
        let m = att_mask(s, p);
        if m != 0 {
            let t = first_set16(m);
            proof {
                assert(t < 16) by {
                    lemma_some_bit(m);
                }
                assert(bit(m, t as u32));
                assert(att_bad(s@[p + t as u32]));
            }
            return false;
        }
        proof {
            assert forall|q: int| 0 <= q < p + 16 implies !att_bad(#[trigger] s@[q]) by {
                if q >= p {
                    lemma_zero_bit(m, (q - p) as u32);
                    assert(!bit(m, (q - p) as u32));
                    assert(s@[p + (q - p) as u32] == s@[q]);
                }
            }
        }
        p = p + 16;
    }
    while p < len
        invariant
            p <= len == s@.len(),
            forall|q: int| 0 <= q < p ==> !att_bad(#[trigger] s@[q]),
        decreases len - p,
    {
        let c = s[p];
        if c < 0x20 || c == 0x26 {
            return false;
        }
        p = p + 1;
    }
    true
}

/// How many bytes of `s` are line feeds.
#[inline]
pub fn count_newlines(s: &[u8]) -> (r: usize)
    ensures
        r == cnt(s@, Kind::Nl, s@.len() as int),
{
    let len = s.len();
    let mut p: usize = 0;
    let mut n: usize = 0;
    while len - p >= 16
        invariant
            p <= len == s@.len(),
            n == cnt(s@, Kind::Nl, p as int),
        decreases len - p,
    {
        let m = eq_mask(s, p, 0x0A);
        let c = popcnt64(m as u64);
        proof {
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == is_kind(Kind::Nl, s@[p + k]) by {
                assert(bit(m, k) == (s@[p + k] == 0x0Au8));
                assert(is_kind(Kind::Nl, s@[p + k]) == (s@[p + k] == 0x0Au8));
            }
            lemma_cnt_bound(s@, Kind::Nl, p as int);
            lemma_cnt16(s@, Kind::Nl, p as int, m);
            lemma_cnt_bound(s@, Kind::Nl, p + 16);
        }
        n = n + c as usize;
        p = p + 16;
    }
    while p < len
        invariant
            p <= len == s@.len(),
            n == cnt(s@, Kind::Nl, p as int),
        decreases len - p,
    {
        proof {
            lemma_cnt_bound(s@, Kind::Nl, p as int);
            assert(cnt(s@, Kind::Nl, p + 1) == cnt(s@, Kind::Nl, p as int) + if is_kind(Kind::Nl, s@[p as int]) { 1nat } else { 0nat });
        }
        if s[p] == 0x0A {
            n = n + 1;
        }
        p = p + 1;
    }
    n
}

/// How many bytes of `s` are UTF-8 continuation bytes.
#[inline]
pub fn count_continuations(s: &[u8]) -> (r: usize)
    ensures
        r == cnt(s@, Kind::Cont, s@.len() as int),
{
    let len = s.len();
    let mut p: usize = 0;
    let mut n: usize = 0;
    while len - p >= 16
        invariant
            p <= len == s@.len(),
            n == cnt(s@, Kind::Cont, p as int),
        decreases len - p,
    {
        let m = cont_mask(s, p);
        let c = popcnt64(m as u64);
        proof {
            assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == is_kind(Kind::Cont, s@[p + k]) by {
                assert(bit(m, k) == cont(s@[p + k]));
                assert(is_kind(Kind::Cont, s@[p + k]) == cont(s@[p + k]));
            }
            lemma_cnt_bound(s@, Kind::Cont, p as int);
            lemma_cnt16(s@, Kind::Cont, p as int, m);
            lemma_cnt_bound(s@, Kind::Cont, p + 16);
        }
        n = n + c as usize;
        p = p + 16;
    }
    while p < len
        invariant
            p <= len == s@.len(),
            n == cnt(s@, Kind::Cont, p as int),
        decreases len - p,
    {
        proof {
            lemma_cnt_bound(s@, Kind::Cont, p as int);
            assert(cnt(s@, Kind::Cont, p + 1) == cnt(s@, Kind::Cont, p as int) + if is_kind(Kind::Cont, s@[p as int]) { 1nat } else { 0nat });
        }
        let c = s[p];
        if 0x80 <= c && c < 0xC0 {
            n = n + 1;
        }
        p = p + 1;
    }
    n
}

/// Clearing bit `t` keeps the others, and makes the mask smaller when it
/// was set.
#[verifier::bit_vector]
proof fn lemma_clear_bit(m: u32, t: u32, k: u32)
    requires
        t < 32,
        k < 32,
        (m >> t) & 1u32 == 1u32,
    ensures
        (((m & !(1u32 << t)) >> k) & 1u32 == 1u32) == (((m >> k) & 1u32 == 1u32) && k != t),
        m & !(1u32 << t) < m,
{
}

/// The positions of the line feeds in `s`, and whether `s` is all ASCII.
#[inline]
pub fn line_index(s: &[u8]) -> (r: (Vec<usize>, bool))
    ensures
        r.0@.map_values(|x: usize| x as int) == nl_pos(s@, s@.len() as int),
        r.1 == forall|q: int| 0 <= q < s@.len() ==> #[trigger] s@[q] < 0x80,
{
    let len = s.len();
    let mut v: Vec<usize> = Vec::with_capacity(len / 32);
    let mut ascii = true;
    let mut p: usize = 0;
    proof {
        assert(v@.map_values(|x: usize| x as int) =~= nl_pos(s@, 0));
    }
    while len - p >= 16
        invariant
            p <= len == s@.len(),
            v@.map_values(|x: usize| x as int) == nl_pos(s@, p as int),
            ascii == forall|q: int| 0 <= q < p ==> #[trigger] s@[q] < 0x80,
        decreases len - p,
    {
        let x = load16(s, p);
        proof {
            lemma_lanes(x, s@, p as int);
        }
        let hi = mask_of(x, s, p, Ghost(|c: u8| c >= 0x80));
        let mut m = mask_of(eqc(x, 0x0A), s, p, Ghost(|c: u8| c == 0x0A));
        let ghost mut d: int = p as int;
        while m != 0
            invariant
                p <= d <= p + 16,
                p + 16 <= len == s@.len(),
                m < 0x10000,
                forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == (p + k >= d && s@[p + k] == 0x0A),
                v@.map_values(|x: usize| x as int) == nl_pos(s@, d),
            decreases m,
        {
            let t = first_set16(m);
            proof {
                assert(t < 16) by {
                    lemma_some_bit(m);
                }
                let e = p + t;
                assert(bit(m, t as u32));
                assert(e >= d);
                assert forall|q: int| d <= q < e implies #[trigger] s@[q] != 0x0A by {
                    assert(!bit(m, (q - p) as u32));
                    assert(s@[p + (q - p) as u32] == s@[q]);
                }
                lemma_nl_skip(s@, d, e);
                assert(s@[e] == 0x0A);
                assert(nl_pos(s@, e + 1) == nl_pos(s@, e).push(e));
            }
            v.push(p + t);
            proof {
                assert(v@.map_values(|x: usize| x as int) =~= nl_pos(s@, d).push(p + t));
                assert forall|k: u32| k < 16 implies #[trigger] bit(m & !(1u32 << (t as u32)), k) == (p + k >= p + t
                    + 1 && s@[p + k] == 0x0A) by {
                    lemma_clear_bit(m, t as u32, k);
                    assert(bit(m, k) == (p + k >= d && s@[p + k] == 0x0A));
                    if k < t as u32 {
                        assert(!bit(m, k));
                    }
                }
                lemma_clear_bit(m, t as u32, 0);
                assert(m & !(1u32 << (t as u32)) < 0x10000) by (bit_vector)
                    requires m < 0x10000;
                d = p + t + 1;
            }
            m = m & !(1u32 << (t as u32));
        }
        proof {
            assert forall|q: int| d <= q < p + 16 implies #[trigger] s@[q] != 0x0A by {
                lemma_zero_bit(m, (q - p) as u32);
                    assert(!bit(m, (q - p) as u32));
                assert(s@[p + (q - p) as u32] == s@[q]);
            }
            lemma_nl_skip(s@, d, p + 16);
        }
        if hi != 0 {
            proof {
                lemma_some_bit(hi);
                let t = choose|t: u32| t < 16 && #[trigger] bit(hi, t);
                assert(s@[p + t] >= 0x80);
            }
            ascii = false;
        } else {
            proof {
                assert forall|q: int| p <= q < p + 16 implies #[trigger] s@[q] < 0x80 by {
                    lemma_zero_bit(hi, (q - p) as u32);
                    assert(!bit(hi, (q - p) as u32));
                    assert(s@[p + (q - p) as u32] == s@[q]);
                }
            }
        }
        p = p + 16;
    }
    while p < len
        invariant
            p <= len == s@.len(),
            v@.map_values(|x: usize| x as int) == nl_pos(s@, p as int),
            ascii == forall|q: int| 0 <= q < p ==> #[trigger] s@[q] < 0x80,
        decreases len - p,
    {
        let c = s[p];
        if c >= 0x80 {
            ascii = false;
        }
        if c == 0x0A {
            v.push(p);
            proof {
                assert(v@.map_values(|x: usize| x as int) =~= nl_pos(s@, p as int).push(p as int));
            }
        }
        p = p + 1;
    }
    (v, ascii)
}

/// The keep mask for the lanes from `sh` up: bits `sh` to 15.
#[verifier::bit_vector]
proof fn lemma_keep(sh: u32, k: u32)
    requires
        0 < sh < 16,
        k < 16,
    ensures
        ((((0xFFFFu32 << sh) & 0xFFFFu32) >> k) & 1u32 == 1u32) == (k >= sh),
        (0xFFFFu32 << sh) & 0xFFFFu32 < 0x10000,
{
}

/// Bits of a block of `buf` at `i`: `text_bad` and not `blank`.
#[inline(always)]
fn class_masks(buf: &[u8], i: usize) -> (r: (u32, u32))
    requires
        i + 16 <= buf@.len(),
    ensures
        r.0 < 0x10000,
        r.1 < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(r.0, k) == text_bad(buf@[i + k]),
        forall|k: u32| k < 16 ==> #[trigger] bit(r.1, k) == !blank(buf@[i + k]),
{
    let v = load16(buf, i);
    proof {
        lemma_lanes(v, buf@, i as int);
    }
    let hi = mask_of(v, buf, i, Ghost(|c: u8| c >= 0x80));
    let low = mask_of(lec(v, 0x1F), buf, i, Ghost(|c: u8| c <= 0x1F));
    let tl = mask_of(or2(eqc(v, 0x09), eqc(v, 0x0A)), buf, i, Ghost(|c: u8| c == 0x09 || c == 0x0A));
    let bl = mask_of(or2(eqc(v, 0x20), eqc(v, 0x0A)), buf, i, Ghost(|c: u8| blank(c)));
    let bad = hi | (low & !tl);
    let other = !bl & 0xFFFF;
    proof {
        lemma_bounds16(hi, low, tl);
        lemma_bounds16(bl, 0, 0);
        assert forall|k: u32| k < 16 implies #[trigger] bit(bad, k) == text_bad(buf@[i + k]) by {
            let c = buf@[i + k];
            assert(bit(hi, k) == (c >= 0x80));
            assert(bit(low, k) == (c <= 0x1F));
            assert(bit(tl, k) == (c == 0x09 || c == 0x0A));
            lemma_bits3(hi, low, tl, k);
        }
        assert forall|k: u32| k < 16 implies #[trigger] bit(other, k) == !blank(buf@[i + k]) by {
            assert(bit(bl, k) == blank(buf@[i + k]));
            lemma_not16(bl, k);
        }
    }
    (bad, other)
}

/// Whether no byte of `buf[a..b]` is `text_bad`, and if so whether every
/// one is `blank` (else `false`). The bytes after the last whole block
/// are read as the 16 bytes that end at `b`, the ones before masked out.
#[inline]
pub fn text_class_in(buf: &[u8], a: usize, b: usize) -> (r: (bool, bool))
    requires
        a <= b <= buf@.len(),
    ensures
        r.0 == forall|q: int| a <= q < b ==> !text_bad(#[trigger] buf@[q]),
        r.1 == (r.0 && forall|q: int| a <= q < b ==> blank(#[trigger] buf@[q])),
{
    let mut ws = true;
    let mut p = a;
    while b - p >= 16
        invariant
            a <= p <= b <= buf@.len(),
            forall|q: int| a <= q < p ==> !text_bad(#[trigger] buf@[q]),
            ws == forall|q: int| a <= q < p ==> blank(#[trigger] buf@[q]),
        decreases b - p,
    {
        let (bad, other) = class_masks(buf, p);
        if bad != 0 {
            proof {
                lemma_some_bit(bad);
                let t = choose|t: u32| t < 16 && #[trigger] bit(bad, t);
                assert(text_bad(buf@[p + t]));
            }
            return (false, false);
        }
        proof {
            assert forall|q: int| p <= q < p + 16 implies !text_bad(#[trigger] buf@[q]) by {
                lemma_zero_bit(bad, (q - p) as u32);
                    assert(!bit(bad, (q - p) as u32));
                assert(buf@[p + (q - p) as u32] == buf@[q]);
            }
        }
        if other != 0 {
            proof {
                lemma_some_bit(other);
                let t = choose|t: u32| t < 16 && #[trigger] bit(other, t);
                assert(!blank(buf@[p + t]));
            }
            ws = false;
        } else {
            proof {
                assert forall|q: int| p <= q < p + 16 implies blank(#[trigger] buf@[q]) by {
                    lemma_zero_bit(other, (q - p) as u32);
                    assert(!bit(other, (q - p) as u32));
                    assert(buf@[p + (q - p) as u32] == buf@[q]);
                }
            }
        }
        p = p + 16;
    }
    let r = b - p;
    if r > 0 && b >= 16 {
        let q0 = b - 16;
        let (bad, other) = class_masks(buf, q0);
        let sh = (16 - r) as u32;
        let keep = (0xFFFFu32 << sh) & 0xFFFF;
        let kb = bad & keep;
        let ko = other & keep;
        proof {
            lemma_keep(sh, 0);
            lemma_bounds16(bad, keep, 0);
            lemma_bounds16(other, keep, 0);
            assert forall|k: u32| k < 16 implies #[trigger] bit(kb, k) == (k >= sh && text_bad(buf@[q0 + k])) by {
                lemma_keep(sh, k);
                assert(bit(keep, k) == (k >= sh));
                assert(bit(bad, k) == text_bad(buf@[q0 + k]));
                lemma_bits3(bad, keep, 0, k);
            }
            assert forall|k: u32| k < 16 implies #[trigger] bit(ko, k) == (k >= sh && !blank(buf@[q0 + k])) by {
                lemma_keep(sh, k);
                assert(bit(keep, k) == (k >= sh));
                assert(bit(other, k) == !blank(buf@[q0 + k]));
                lemma_bits3(other, keep, 0, k);
            }
        }
        if kb != 0 {
            proof {
                lemma_some_bit(kb);
                let t = choose|t: u32| t < 16 && #[trigger] bit(kb, t);
                assert(text_bad(buf@[q0 + t]));
                assert(q0 + t >= p);
            }
            return (false, false);
        }
        proof {
            assert forall|q: int| p <= q < b implies !text_bad(#[trigger] buf@[q]) by {
                lemma_zero_bit(kb, (q - q0) as u32);
                    assert(!bit(kb, (q - q0) as u32));
                assert(buf@[q0 + (q - q0) as u32] == buf@[q]);
            }
        }
        if ko != 0 {
            proof {
                lemma_some_bit(ko);
                let t = choose|t: u32| t < 16 && #[trigger] bit(ko, t);
                assert(!blank(buf@[q0 + t]));
                assert(q0 + t >= p);
            }
            return (true, false);
        }
        proof {
            assert forall|q: int| p <= q < b implies blank(#[trigger] buf@[q]) by {
                lemma_zero_bit(ko, (q - q0) as u32);
                    assert(!bit(ko, (q - q0) as u32));
                assert(buf@[q0 + (q - q0) as u32] == buf@[q]);
            }
        }
        return (true, ws);
    }
    while p < b
        invariant
            a <= p <= b <= buf@.len(),
            forall|q: int| a <= q < p ==> !text_bad(#[trigger] buf@[q]),
            ws == forall|q: int| a <= q < p ==> blank(#[trigger] buf@[q]),
        decreases b - p,
    {
        let c = buf[p];
        if !(c == 0x09 || c == 0x0A || (0x20 <= c && c < 0x80)) {
            return (false, false);
        }
        if !(c == 0x20 || c == 0x0A) {
            ws = false;
        }
        p = p + 1;
    }
    (true, ws)
}

} // verus!
