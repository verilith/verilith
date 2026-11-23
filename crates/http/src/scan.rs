//! SIMD scanners for the long runs in a head: request targets, field values
//! and reason phrases. Each finds the first byte outside its class 16 bytes
//! at a time (SSE2 on x86-64, NEON on AArch64) and is proven to return
//! exactly `spec::run_end`.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
use crate::lanes::*;
use crate::parse::{get8, scan_target, scan_token, scan_value, tchar};
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A run that is all in class `k` can be skipped.
pub proof fn lemma_run_skip(b: Seq<u8>, p: int, q: int, k: Cls)
    requires
        0 <= p <= q <= b.len(),
        forall|j: int| p <= j < q ==> in_cls(k, #[trigger] b[j]),
    ensures
        run_end(b, p, k) == run_end(b, q, k),
    decreases q - p,
{
    if p < q {
        lemma_run_skip(b, p + 1, q, k);
    }
}

} // verus!

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
verus! {

/// The lowest set bit of a nonzero 16-bit mask.
proof fn lemma_lowest(m: u32)
    requires
        m != 0,
        m < 0x10000,
    ensures
        ({
            let t = m.trailing_zeros();
            &&& t < 16
            &&& bit(m, t)
            &&& forall|q: u32| q < t ==> !#[trigger] bit(m, q)
        }),
{
    vstd::std_specs::bits::axiom_u32_trailing_zeros(m);
    let t = m.trailing_zeros();
    assert forall|q: u32| q < t implies !#[trigger] bit(m, q) by {
        assert((m >> q) & 1u32 == 0u32);
    }
    if t >= 16 {
        assert(m < 0x10000 && (m >> t) & 1u32 == 1u32 && t < 32 ==> t < 16) by (bit_vector);
    }
}

/// Shifting a 16-bit mask right by `s` moves bit `k + s` to bit `k` and
/// clears the top `s` bits.
proof fn lemma_shr(m: u32, s: u32, k: u32)
    requires
        m < 0x10000,
        s < 16,
        k < 32,
    ensures
        m >> s < 0x10000,
        k + s < 16 ==> bit(m >> s, k) == bit(m, (k + s) as u32),
        k + s >= 16 ==> !bit(m >> s, k),
{
    assert(m < 0x10000 && s < 16 ==> m >> s < 0x10000) by (bit_vector);
    assert(m < 0x10000 && s < 16 && k < 32 ==> (k + s < 16 ==> (((m >> s) >> k) & 1u32 == 1u32)
        == ((m >> (k + s)) & 1u32 == 1u32))) by (bit_vector);
    assert(m < 0x10000 && s < 16 && k < 32 ==> (k + s >= 16 ==> !(((m >> s) >> k) & 1u32
        == 1u32))) by (bit_vector);
}

/// Lane facts: `x | y` of two compare results is set where either is.
proof fn lemma_or_lane(x: u8, y: u8)
    requires
        x == 0xFF || x == 0,
        y == 0xFF || y == 0,
    ensures
        ((x | y) >= 0x80) == (x == 0xFF || y == 0xFF),
{
    assert((x == 0xFF || x == 0) && (y == 0xFF || y == 0) ==> (((x | y) >= 0x80) == (x == 0xFF
        || y == 0xFF))) by (bit_vector);
}

proof fn lemma_andnot_bit(a: u32, t: u32, k: u32)
    requires
        k < 32,
    ensures
        bit(a & !t, k) == (bit(a, k) && !bit(t, k)),
{
    assert(k < 32 ==> ((((a & !t) >> k) & 1u32 == 1u32) == (((a >> k) & 1u32 == 1u32) && !((t
        >> k) & 1u32 == 1u32)))) by (bit_vector);
}

/// Bit `k` is set iff `b[p + k]` is not a field-value byte.
#[inline(always)]
fn value_bad16(b: &[u8], p: usize) -> (m: u32)
    requires
        p + 16 <= b@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == !is_value_char(b@[p + k]),
{
    let x = load16(b, p);
    let lo = eq16(min16(x, splat16(0x1F)), x);
    let del = eq16(x, splat16(0x7F));
    let tab = eq16(x, splat16(HTAB));
    let a = movemask16(or16(lo, del));
    let t = movemask16(tab);
    let m = a & !t;
    proof {
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == !is_value_char(
            b@[p + k],
        ) by {
            let c = b@[p + k];
            assert(b16(x)[k as int] == b@.subrange(p as int, p + 16)[k as int]);
            lemma_or_lane(b16(lo)[k as int], b16(del)[k as int]);
            lemma_andnot_bit(a, t, k);
            assert(bit(a, k) == (c <= 0x1F || c == 0x7F));
            assert(bit(t, k) == (c == HTAB));
        }
        assert(m <= a) by (bit_vector)
            requires
                m == a & !t,
        ;
    }
    m
}

/// Bit `k` is set iff `b[p + k]` is not a request-target byte.
#[inline(always)]
fn target_bad16(b: &[u8], p: usize) -> (m: u32)
    requires
        p + 16 <= b@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 ==> #[trigger] bit(m, k) == !is_target_char(b@[p + k]),
{
    let x = load16(b, p);
    let lo = eq16(min16(x, splat16(0x20)), x);
    let del = eq16(x, splat16(0x7F));
    let m = movemask16(or16(lo, del));
    proof {
        assert forall|k: u32| k < 16 implies #[trigger] bit(m, k) == !is_target_char(
            b@[p + k],
        ) by {
            assert(b16(x)[k as int] == b@.subrange(p as int, p + 16)[k as int]);
            lemma_or_lane(b16(lo)[k as int], b16(del)[k as int]);
        }
    }
    m
}

/// Lane facts for the token fast class: a letter (after case folding), a
/// digit or `-` is a tchar.
proof fn lemma_alnum_dash(c: u8)
    requires
        ((c | 0x20u8) <= 0x7A && !((c | 0x20u8) <= 0x60)) || (c <= 0x39 && !(c <= 0x2F)) || c
            == 0x2D,
    ensures
        is_tchar(c),
{
    assert(((c | 0x20u8) <= 0x7A && !((c | 0x20u8) <= 0x60)) ==> ((0x41 <= c && c <= 0x5A) || (
    0x61 <= c && c <= 0x7A))) by (bit_vector);
}

proof fn lemma_good_bit(a1: u32, a2: u32, d1: u32, d2: u32, ds: u32, k: u32)
    requires
        k < 16,
    ensures
        ({
            let g = (a1 & !a2) | (d1 & !d2) | ds;
            let m = !g & 0xFFFFu32;
            &&& m < 0x10000
            &&& !bit(m, k) ==> ((bit(a1, k) && !bit(a2, k)) || (bit(d1, k) && !bit(d2, k)) || bit(
                ds,
                k,
            ))
        }),
{
    let g = (a1 & !a2) | (d1 & !d2) | ds;
    let m = !g & 0xFFFFu32;
    assert(m < 0x10000) by (bit_vector)
        requires
            m == !g & 0xFFFFu32,
    ;
    assert(k < 16 && m == !((a1 & !a2) | (d1 & !d2) | ds) & 0xFFFFu32 ==> (!((m >> k) & 1u32
        == 1u32) ==> ((((a1 >> k) & 1u32 == 1u32) && !((a2 >> k) & 1u32 == 1u32)) || (((d1 >> k)
        & 1u32 == 1u32) && !((d2 >> k) & 1u32 == 1u32)) || ((ds >> k) & 1u32 == 1u32))))
        by (bit_vector);
}

/// A 16-bit mask whose clear bits are all tchars: bit `k` is clear when
/// `b[p + k]` is a letter, a digit or `-`, the bytes field names are made
/// of. Set bits are only candidates; the scalar step decides them.
#[inline(always)]
fn token_bad16(b: &[u8], p: usize) -> (m: u32)
    requires
        p + 16 <= b@.len(),
    ensures
        m < 0x10000,
        forall|k: u32| k < 16 && !#[trigger] bit(m, k) ==> is_tchar(b@[p + k]),
{
    let x = load16(b, p);
    let y = or16(x, splat16(0x20));
    let a1 = movemask16(eq16(min16(y, splat16(0x7A)), y));
    let a2 = movemask16(eq16(min16(y, splat16(0x60)), y));
    let d1 = movemask16(eq16(min16(x, splat16(0x39)), x));
    let d2 = movemask16(eq16(min16(x, splat16(0x2F)), x));
    let ds = movemask16(eq16(x, splat16(0x2D)));
    let m = !((a1 & !a2) | (d1 & !d2) | ds) & 0xFFFF;
    proof {
        assert forall|k: u32| k < 16 && !#[trigger] bit(m, k) implies is_tchar(b@[p + k]) by {
            let c = b@[p + k];
            assert(b16(x)[k as int] == b@.subrange(p as int, p + 16)[k as int]);
            lemma_good_bit(a1, a2, d1, d2, ds, k);
            lemma_alnum_dash(c);
        }
        lemma_good_bit(a1, a2, d1, d2, ds, 0);
    }
    m
}

/// The first set bit of `m` at or after `sh`, counted from `sh`, or
/// `16 - sh` if there is none.
#[inline(always)]
fn mask_first(m: u32, sh: u32) -> (d: u32)
    requires
        m < 0x10000,
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|k: u32| k < d ==> !#[trigger] bit(m, (k + sh) as u32),
        d < 16 - sh ==> bit(m, (d + sh) as u32),
{
    let s = m >> sh;
    let t = s.trailing_zeros();
    let d = if t > 16 - sh { 16 - sh } else { t };
    proof {
        vstd::std_specs::bits::axiom_u32_trailing_zeros(s);
        assert forall|k: u32| k < d implies !#[trigger] bit(m, (k + sh) as u32) by {
            lemma_shr(m, sh, k);
            assert((s >> k) & 1u32 == 0u32);
        }
        if d < 16 - sh {
            lemma_shr(m, sh, t);
        }
    }
    d
}

/// The first byte from `q + sh` on in `b[q..q + 16]` that is not a field
/// value byte, counted from `q + sh`, or `16 - sh` if there is none.
#[inline(always)]
fn value_from<const NEON: bool>(b: &[u8], q: usize, sh: u32) -> (d: u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 16 <= b@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> in_cls(Cls::Value, #[trigger] b@[j]),
        d < 16 - sh ==> !in_cls(Cls::Value, b@[q + sh + d]),
{
    if NEON {
        let v = crate::scan_neon::value_badv(b, q);
        let d = crate::scan_neon::nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Value, #[trigger] b@[j]) by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let m = value_bad16(b, q);
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Value, #[trigger] b@[j]) by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
        }
        d
    }
}

/// As `value_from`, for request-target bytes.
#[inline(always)]
fn target_from<const NEON: bool>(b: &[u8], q: usize, sh: u32) -> (d: u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 16 <= b@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> in_cls(Cls::Target, #[trigger] b@[j]),
        d < 16 - sh ==> !in_cls(Cls::Target, b@[q + sh + d]),
{
    if NEON {
        let v = crate::scan_neon::target_badv(b, q);
        let d = crate::scan_neon::nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Target, #[trigger] b@[j]) by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let m = target_bad16(b, q);
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Target, #[trigger] b@[j]) by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
        }
        d
    }
}

/// As `value_from`, for the bytes field names are made of (letters,
/// digits and `-`); the byte it stops at is only a candidate.
#[inline(always)]
fn token_from<const NEON: bool>(b: &[u8], q: usize, sh: u32) -> (d: u32)
    requires
        NEON ==> verilith_simd::neon::neon(),
        q + 16 <= b@.len(),
        sh < 16,
    ensures
        d <= 16 - sh,
        forall|j: int| q + sh <= j < q + sh + d ==> in_cls(Cls::Token, #[trigger] b@[j]),
{
    if NEON {
        let v = crate::scan_neon::token_badv(b, q);
        let d = crate::scan_neon::nib_first(v, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Token, #[trigger] b@[j]) by {
                assert(verilith_simd::neon::n8(v)[(((j - q - sh) as u32) + sh) as int] != 0xFF);
            }
        }
        d
    } else {
        let m = token_bad16(b, q);
        let d = mask_first(m, sh);
        proof {
            assert forall|j: int| q + sh <= j < q + sh + d implies in_cls(Cls::Token, #[trigger] b@[j]) by {
                assert(!bit(m, (((j - q - sh) as u32) + sh) as u32));
            }
        }
        d
    }
}

/// `run_end(b, i, Token)`: whole letter, digit and dash blocks are skipped
/// 16 bytes at a time and any other byte is decided by the table. The
/// second result counts loop iterations.
fn scan_token_impl<const NEON: bool>(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        NEON ==> verilith_simd::neon::neon(),
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Token),
        r.1@ <= r.0 - i,
{
    let mut p = i;
    let ghost mut steps: nat = 0;
    while b.len() - p >= 16
        invariant
            NEON ==> verilith_simd::neon::neon(),
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Token) == run_end(b@, p as int, Cls::Token),
            steps <= p - i,
        decreases b@.len() - p,
    {
        let d = token_from::<NEON>(b, p, 0);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Token);
            steps = steps + 1;
        }
        p += d as usize;
        if d < 16 {
            if !tchar(get8(b, p)) {
                return (p, Ghost((steps - 1) as nat));
            }
            p += 1;
        }
    }
    // The last bytes: one block ending at the end of the input, with
    // the lanes before `p` skipped.
    if b.len() >= 16 && p < b.len() {
        let q = b.len() - 16;
        let sh = (p - q) as u32;
        let d = token_from::<NEON>(b, q, sh);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Token);
        }
        p += d as usize;
        if p < b.len() {
            if !tchar(get8(b, p)) {
                return (p, Ghost(steps));
            }
            p += 1;
            proof {
                steps = steps + 1;
            }
        }
    }
    let (e, g) = scan_token(b, p);
    (e, Ghost(steps + g@))
}

/// `run_end(b, i, Value)`; the second result counts loop iterations.
fn scan_value_impl<const NEON: bool>(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        NEON ==> verilith_simd::neon::neon(),
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Value),
        r.1@ <= r.0 - i + 1,
{
    let mut p = i;
    let ghost mut steps: nat = 0;
    while b.len() - p >= 16
        invariant
            NEON ==> verilith_simd::neon::neon(),
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Value) == run_end(b@, p as int, Cls::Value),
            steps <= p - i,
        decreases b@.len() - p,
    {
        let d = value_from::<NEON>(b, p, 0);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Value);
        }
        if d < 16 {
            return (p + d as usize, Ghost(steps + 1));
        }
        proof {
            steps = steps + 1;
        }
        p += 16;
    }
    // The last bytes: one block ending at the end of the input, with
    // the lanes before `p` skipped.
    if b.len() >= 16 && p < b.len() {
        let q = b.len() - 16;
        let sh = (p - q) as u32;
        let d = value_from::<NEON>(b, q, sh);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Value);
        }
        return (p + d as usize, Ghost(steps + 1));
    }
    let (e, g) = scan_value(b, p);
    (e, Ghost(steps + g@))
}

/// `run_end(b, i, Target)`; the second result counts loop iterations.
fn scan_target_impl<const NEON: bool>(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        NEON ==> verilith_simd::neon::neon(),
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Target),
        r.1@ <= r.0 - i + 1,
{
    let mut p = i;
    let ghost mut steps: nat = 0;
    while b.len() - p >= 16
        invariant
            NEON ==> verilith_simd::neon::neon(),
            i <= p <= b@.len(),
            run_end(b@, i as int, Cls::Target) == run_end(b@, p as int, Cls::Target),
            steps <= p - i,
        decreases b@.len() - p,
    {
        let d = target_from::<NEON>(b, p, 0);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Target);
        }
        if d < 16 {
            return (p + d as usize, Ghost(steps + 1));
        }
        proof {
            steps = steps + 1;
        }
        p += 16;
    }
    // The last bytes: one block ending at the end of the input, with
    // the lanes before `p` skipped.
    if b.len() >= 16 && p < b.len() {
        let q = b.len() - 16;
        let sh = (p - q) as u32;
        let d = target_from::<NEON>(b, q, sh);
        proof {
            lemma_run_skip(b@, p as int, p + d, Cls::Target);
        }
        return (p + d as usize, Ghost(steps + 1));
    }
    let (e, g) = scan_target(b, p);
    (e, Ghost(steps + g@))
}

pub fn scan_token_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Token),
        r.1@ <= r.0 - i,
{
    if verilith_simd::neon::has_neon() {
        scan_token_impl::<true>(b, i)
    } else {
        scan_token_impl::<false>(b, i)
    }
}

pub fn scan_value_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Value),
        r.1@ <= r.0 - i + 1,
{
    if verilith_simd::neon::has_neon() {
        scan_value_impl::<true>(b, i)
    } else {
        scan_value_impl::<false>(b, i)
    }
}

pub fn scan_target_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Target),
        r.1@ <= r.0 - i + 1,
{
    if verilith_simd::neon::has_neon() {
        scan_target_impl::<true>(b, i)
    } else {
        scan_target_impl::<false>(b, i)
    }
}

} // verus!

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
verus! {

pub fn scan_token_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Token),
        r.1@ <= r.0 - i,
{
    scan_token(b, i)
}

pub fn scan_value_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Value),
        r.1@ <= r.0 - i + 1,
{
    scan_value(b, i)
}

pub fn scan_target_fast(b: &[u8], i: usize) -> (r: (usize, Ghost<nat>))
    requires
        i <= b@.len(),
    ensures
        r.0 == run_end(b@, i as int, Cls::Target),
        r.1@ <= r.0 - i + 1,
{
    scan_target(b, i)
}

} // verus!

#[cfg(all(test, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
mod tests {
    use super::*;

    /// The NEON and SSE2 scanners agree with the scalar ones on every
    /// start offset of buffers with a single odd byte anywhere.
    #[test]
    fn neon_and_sse2_agree_with_scalar() {
        let fills = [b'a', b'Z', b'7', b'-', b' ', b'/', 0x80];
        for len in 0..70usize {
            for &fill in &fills {
                for pos in 0..=len {
                    for c in 0..=255u8 {
                        let mut d = vec![fill; len];
                        if pos < len {
                            d[pos] = c;
                        }
                        for i in [0, 1, 5, 17].into_iter().filter(|&i| i <= len) {
                            let t = scan_token(&d, i).0;
                            assert_eq!(scan_token_impl::<true>(&d, i).0, t);
                            assert_eq!(scan_token_impl::<false>(&d, i).0, t);
                            let v = scan_value(&d, i).0;
                            assert_eq!(scan_value_impl::<true>(&d, i).0, v);
                            assert_eq!(scan_value_impl::<false>(&d, i).0, v);
                            let g = scan_target(&d, i).0;
                            assert_eq!(scan_target_impl::<true>(&d, i).0, g);
                            assert_eq!(scan_target_impl::<false>(&d, i).0, g);
                        }
                        if pos == len {
                            break;
                        }
                    }
                }
            }
        }
    }
}
