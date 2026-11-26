//! Forgiving base64, as simdutf decodes it for Node.js: the WHATWG Infra
//! Standard's "forgiving-base64 decode", with simdutf's conventions where
//! the standard leaves room.
//!
//! * ASCII whitespace (space, tab, LF, FF, CR) is ignored anywhere.
//! * Padding is optional. Up to two `=` may end the text (with whitespace
//!   around them); if there are any, they must complete the last group.
//! * Bits that a final partial group drops need not be zero.
//! * A last group of one character is an error (`Remainder`); any other
//!   character, and padding that does not fit, is `Invalid`. A bad
//!   character is reported before a bad length.
//!
//! `forgiving` is that definition as a spec; `decode_forgiving` is proven
//! to compute it. It reuses the strict decoder's group loops (and their
//! AVX2 kernel) on the text when it has no whitespace, and on a compacted
//! copy when it does.
use super::scalar::*;
use super::spec::*;
use super::tables::*;
use verilith_core::prims::{get, set};
use vstd::prelude::*;

verus! {

/// Why a text is not forgiving base64, or does not fit.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum B64Error {
    /// A character outside the alphabet and whitespace, or padding that does
    /// not complete the last group.
    Invalid,
    /// A last group of one character.
    Remainder,
    /// The output buffer is too small (only from `decode_forgiving`).
    TooSmall,
}

/// ASCII whitespace, as the Infra Standard defines it.
pub open spec fn ws(c: u8) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D
}

/// `s[..n]` without its trailing whitespace: the new length.
pub open spec fn trim(s: Seq<u8>, n: int) -> int
    decreases n,
{
    if n > 0 && ws(s[n - 1]) {
        trim(s, n - 1)
    } else {
        n
    }
}

/// The length of the body (what is left after trailing whitespace and up to
/// two `=`, as simdutf strips them) and the number of `=`.
pub open spec fn strip(s: Seq<u8>) -> (int, int) {
    let t0 = trim(s, s.len() as int);
    if t0 > 0 && s[t0 - 1] == PAD {
        let t1 = trim(s, t0 - 1);
        if t1 > 0 && s[t1 - 1] == PAD {
            (t1 - 1, 2)
        } else {
            (t1, 1)
        }
    } else {
        (t0, 0)
    }
}

/// The non-whitespace characters of `s[..t]`.
pub open spec fn compact(s: Seq<u8>, t: int) -> Seq<u8>
    decreases t,
{
    if t <= 0 {
        seq![]
    } else if ws(s[t - 1]) {
        compact(s, t - 1)
    } else {
        compact(s, t - 1).push(s[t - 1])
    }
}

/// Every character of `s[..t]` is whitespace or in the alphabet.
pub open spec fn body_ok(url: bool, s: Seq<u8>, t: int) -> bool {
    forall|j: int| 0 <= j < t ==> ws(#[trigger] s[j]) || val(url, s[j]) is Some
}

/// The forgiving decoding of `s`.
pub open spec fn forgiving(url: bool, s: Seq<u8>) -> Result<Seq<u8>, B64Error> {
    let (t, eq) = strip(s);
    if !body_ok(url, s, t) {
        Err(B64Error::Invalid)
    } else {
        let c = compact(s, t);
        let n = c.len();
        if n % 4 == 1 {
            Err(B64Error::Remainder)
        } else if eq > 0 && (n % 4 == 0 || n % 4 + eq != 4) {
            Err(B64Error::Invalid)
        } else {
            Ok(Seq::new(decoded_len(n), |i: int| dec_byte(url, c, n as int, i)))
        }
    }
}

/// simdutf's `maximal_binary_length_from_base64`: the decoded size of a
/// text of this length, less the `=` it literally ends with.
pub open spec fn max_len(s: Seq<u8>) -> nat {
    let n = s.len();
    let p: nat = if n >= 1 && s[n - 1] == PAD {
        if n >= 2 && s[n - 2] == PAD {
            2
        } else {
            1
        }
    } else {
        0
    };
    decoded_len((n - p) as nat)
}

// ---------------------------------------------------------------------------
// Facts
// ---------------------------------------------------------------------------

proof fn lemma_trim(s: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        0 <= trim(s, n) <= n,
        trim(s, n) > 0 ==> !ws(s[trim(s, n) - 1]),
        forall|j: int| trim(s, n) <= j < n ==> ws(#[trigger] s[j]),
    decreases n,
{
    if n > 0 && ws(s[n - 1]) {
        lemma_trim(s, n - 1);
    }
}

proof fn lemma_strip(s: Seq<u8>)
    ensures
        ({
            let (t, eq) = strip(s);
            &&& 0 <= t <= s.len()
            &&& 0 <= eq <= 2
            &&& t + eq <= s.len()
        }),
{
    lemma_trim(s, s.len() as int);
    let t0 = trim(s, s.len() as int);
    if t0 > 0 && s[t0 - 1] == PAD {
        lemma_trim(s, t0 - 1);
    }
}

proof fn lemma_compact_len(s: Seq<u8>, t: int)
    ensures
        compact(s, t).len() <= if t > 0 { t } else { 0 },
    decreases t,
{
    if t > 0 {
        lemma_compact_len(s, t - 1);
    }
}

/// With no whitespace in `s[..t]`, compacting changes nothing.
proof fn lemma_compact_none(s: Seq<u8>, t: int)
    requires
        0 <= t <= s.len(),
        forall|j: int| 0 <= j < t ==> !ws(#[trigger] s[j]),
    ensures
        compact(s, t) == s.subrange(0, t),
    decreases t,
{
    if t > 0 {
        lemma_compact_none(s, t - 1);
        assert(s.subrange(0, t - 1).push(s[t - 1]) =~= s.subrange(0, t));
    } else {
        assert(s.subrange(0, 0) =~= Seq::<u8>::empty());
    }
}

/// `dec_byte` reads only the body.
proof fn lemma_dec_byte_prefix(url: bool, s: Seq<u8>, m: int, i: int)
    requires
        0 <= m <= s.len(),
        0 <= i,
    ensures
        dec_byte(url, s.subrange(0, m), m, i) == dec_byte(url, s, m, i),
{
    let g = i / 3;
    assert forall|j: int| 4 * g <= j < 4 * g + 4 implies #[trigger] vb(url, s.subrange(0, m), m, j) == vb(url, s, m, j) by {
        if j < m {
            assert(s.subrange(0, m)[j] == s[j]);
        }
    }
}

/// The decoded size never exceeds `max_len`, so a buffer of that size is
/// never too small.
proof fn lemma_fits(url: bool, s: Seq<u8>)
    ensures
        forgiving(url, s) matches Ok(x) ==> x.len() <= max_len(s),
{
    let (t, eq) = strip(s);
    lemma_strip(s);
    lemma_compact_len(s, t);
    let n = s.len() as int;
    let p: int = if n >= 1 && s[n - 1] == PAD {
        if n >= 2 && s[n - 2] == PAD {
            2
        } else {
            1
        }
    } else {
        0
    };
    // The `=` the text ends with are among the ones strip removes.
    lemma_trim(s, n);
    let t0 = trim(s, n);
    if p >= 1 {
        assert(t0 == n);
        if p == 2 {
            lemma_trim(s, n - 1);
            assert(trim(s, n - 1) == n - 1);
        }
    }
    assert(t <= n - p);
    let m = compact(s, t).len() as int;
    assert(m <= n - p);
    // `decoded_len` is monotone.
    assert(decoded_len(m as nat) <= decoded_len((n - p) as nat)) by {
        let a = m;
        let b = n - p;
        assert(3 * (a / 4) + (if a % 4 == 0 { 0 } else { a % 4 - 1 }) <= 3 * (b / 4) + (if b % 4 == 0 { 0 } else { b % 4
            - 1 })) by (nonlinear_arith)
            requires
                0 <= a <= b,
        ;
    }
}

// ---------------------------------------------------------------------------
// The decoder
// ---------------------------------------------------------------------------

#[inline(always)]
fn ws_exec(c: u8) -> (r: bool)
    ensures
        r == ws(c),
{
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D
}

fn trim_exec(s: &[u8], n: usize) -> (r: usize)
    requires
        n <= s.len(),
    ensures
        r == trim(s@, n as int),
        r <= n,
{
    proof {
        lemma_trim(s@, n as int);
    }
    let mut k = n;
    while k > 0 && ws_exec(get(s, k - 1))
        invariant
            k <= n <= s.len(),
            trim(s@, k as int) == trim(s@, n as int),
        decreases k,
    {
        k = k - 1;
    }
    k
}

fn strip_exec(s: &[u8]) -> (r: (usize, usize))
    ensures
        r.0 as int == strip(s@).0,
        r.1 as int == strip(s@).1,
{
    proof {
        lemma_trim(s@, s.len() as int);
    }
    let t0 = trim_exec(s, s.len());
    if t0 > 0 && get(s, t0 - 1) == PAD {
        let t1 = trim_exec(s, t0 - 1);
        if t1 > 0 && get(s, t1 - 1) == PAD {
            (t1 - 1, 2)
        } else {
            (t1, 1)
        }
    } else {
        (t0, 0)
    }
}

/// `maximal_binary_length_from_base64`.
pub fn max_len_exec(s: &[u8]) -> (r: usize)
    ensures
        r == max_len(s@),
{
    let n = s.len();
    let p: usize = if n >= 1 && get(s, n - 1) == PAD {
        if n >= 2 && get(s, n - 2) == PAD {
            2
        } else {
            1
        }
    } else {
        0
    };
    dec_len(n - p)
}

/// Decodes the body `c[..m]`, every character of which is in the alphabet
/// and whose length is not 1 mod 4, into the front of `out`.
fn decode_body(url: bool, c: &[u8], m: usize, out: &mut [u8])
    requires
        m <= c.len(),
        m % 4 != 1,
        forall|j: int| 0 <= j < m ==> (#[trigger] val(url, c@[j])) is Some,
        old(out).len() >= decoded_len(m as nat),
    ensures
        final(out).len() == old(out).len(),
        final(out)@.subrange(0, decoded_len(m as nat) as int) == Seq::new(
            decoded_len(m as nat),
            |i: int| dec_byte(url, c@, m as int, i),
        ),
{
    proof {
        assert(3 * (m / 4) <= decoded_len(m as nat));
    }
    let (g, ok) = if verilith_simd::cpu::has_avx2() {
        // The CPU has AVX2.
        super::avx2::decode_bulk(url, c, m, out)
    } else {
        (0, true)
    };
    proof {
        assert(ok) by {
            assert(forall|k: int| 0 <= k < 4 * g ==> (#[trigger] val(url, c@[k])) is Some) by {
                assert forall|k: int| 0 <= k < 4 * g implies (#[trigger] val(url, c@[k])) is Some by {
                    assert(k < m);
                }
            }
        }
    }
    let ok2 = decode_groups(url, c, m, out, g);
    proof {
        assert(ok2) by {
            assert forall|j: int| 4 * g <= j < 4 * (m / 4) implies (#[trigger] val(url, c@[j])) is Some by {
                assert(j < m);
            }
        }
    }
    let tab = dec_tab(url);
    let full = m / 4;
    let rem = m % 4;
    let j = 4 * full;
    let o = 3 * full;
    if rem >= 2 {
        let p = tab[get(c, j) as usize];
        let q = tab[get(c, j + 1) as usize];
        set(out, o, (p << 2) | (q >> 4));
        proof {
            lemma_byte_index(full as int, 0);
            assert(p == vb(url, c@, m as int, 4 * full));
            assert(q == vb(url, c@, m as int, 4 * full + 1));
            assert(vb(url, c@, m as int, 4 * full + 2) == if rem == 3 { v(url, c@, j + 2) } else { 0 });
        }
        if rem == 3 {
            let r = tab[get(c, j + 2) as usize];
            set(out, o + 1, (q << 4) | (r >> 2));
            proof {
                lemma_byte_index(full as int, 1);
                assert(r == vb(url, c@, m as int, 4 * full + 2));
            }
        }
    }
    proof {
        let d = decoded_len(m as nat) as int;
        assert(d == o + if rem == 0 { 0 } else { rem - 1 });
        assert forall|i: int| 0 <= i < d implies #[trigger] out@[i] == dec_byte(url, c@, m as int, i) by {
            if i >= o {
                lemma_byte_index(full as int, i - o);
            }
        }
        assert(out@.subrange(0, d) =~= Seq::new(decoded_len(m as nat), |i: int| dec_byte(url, c@, m as int, i)));
    }
}

/// The forgiving decoding of `s` into the front of `out`. On success,
/// returns its length; with a buffer of `max_len(s)` bytes, `TooSmall`
/// never happens.
pub fn decode_forgiving(url: bool, s: &[u8], out: &mut [u8]) -> (r: Result<usize, B64Error>)
    ensures
        final(out).len() == old(out).len(),
        match forgiving(url, s@) {
            Err(e) => r == Err::<usize, B64Error>(e),
            Ok(x) => if x.len() <= old(out).len() {
                r == Ok::<usize, B64Error>(x.len() as usize) && final(out)@.subrange(0, x.len() as int) == x
            } else {
                r == Err::<usize, B64Error>(B64Error::TooSmall)
            },
        },
        old(out).len() >= max_len(s@) ==> r != Err::<usize, B64Error>(B64Error::TooSmall),
{
    proof {
        lemma_strip(s@);
        lemma_fits(url, s@);
    }
    let (t, eq) = strip_exec(s);
    let tab = dec_tab(url);
    // Fast path: no whitespace in the body, so it is its own compaction.
    let mut j: usize = 0;
    while j < t && tab[get(s, j) as usize] < 64
        invariant
            t <= s.len(),
            j <= t,
            t as int == strip(s@).0,
            eq as int == strip(s@).1,
            out@ == old(out)@,
            forall|c: u8| #[trigger] tab@[c as int] == dec_entry(url, c),
            forall|k: int| 0 <= k < j ==> (#[trigger] val(url, s@[k])) is Some,
        decreases t - j,
    {
        j = j + 1;
    }
    if j == t {
        proof {
            assert forall|k: int| 0 <= k < t implies !ws(#[trigger] s@[k]) by {
                assert(val(url, s@[k]) is Some);
            }
            lemma_compact_none(s@, t as int);
            assert(body_ok(url, s@, t as int));
        }
        let r = finish(url, s, t, t, eq, out);
        proof {
            let d = decoded_len(t as nat);
            assert(Seq::new(d, |i: int| dec_byte(url, s@, t as int, i)) =~= Seq::new(d, |i: int| dec_byte(url, s@.subrange(0, t as int), t as int, i))) by {
                assert forall|i: int| 0 <= i < d implies dec_byte(url, s@, t as int, i) == #[trigger] dec_byte(url, s@.subrange(0, t as int), t as int, i) by {
                    lemma_dec_byte_prefix(url, s@, t as int, i);
                }
            }
        }
        return r;
    }
    // Slow path: compact the body.
    let mut c: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < t
        invariant
            t <= s.len(),
            k <= t,
            t as int == strip(s@).0,
            eq as int == strip(s@).1,
            out@ == old(out)@,
            forall|x: u8| #[trigger] tab@[x as int] == dec_entry(url, x),
            c@ == compact(s@, k as int),
            body_ok(url, s@, k as int),
            forall|i: int| 0 <= i < c@.len() ==> (#[trigger] val(url, c@[i])) is Some,
        decreases t - k,
    {
        let x = get(s, k);
        if !ws_exec(x) {
            if tab[x as usize] >= 64 {
                proof {
                    assert(!body_ok(url, s@, t as int)) by {
                        assert(!(ws(s@[k as int]) || val(url, s@[k as int]) is Some));
                    }
                }
                return Err(B64Error::Invalid);
            }
            c.push(x);
        }
        proof {
            assert(body_ok(url, s@, k + 1)) by {
                assert forall|i: int| 0 <= i < k + 1 implies ws(#[trigger] s@[i]) || val(url, s@[i]) is Some by {
                    if i < k {
                    }
                }
            }
        }
        k = k + 1;
    }
    let m = c.len();
    proof {
        assert(c@.subrange(0, m as int) =~= c@);
    }
    finish(url, c.as_slice(), m, t, eq, out)
}

/// The length and padding checks and the decoding, given the compacted body
/// `c[..m]` of `s` (which strips to `t`, `eq`).
fn finish(url: bool, c: &[u8], m: usize, t: usize, eq: usize, out: &mut [u8]) -> (r: Result<usize, B64Error>)
    requires
        m <= c.len(),
        eq <= 2,
        forall|j: int| 0 <= j < m ==> (#[trigger] val(url, c@[j])) is Some,
    ensures
        final(out).len() == old(out).len(),
        ({
            let n = m as int;
            if n % 4 == 1 {
                r == Err::<usize, B64Error>(B64Error::Remainder)
            } else if eq > 0 && (n % 4 == 0 || n % 4 + eq != 4) {
                r == Err::<usize, B64Error>(B64Error::Invalid)
            } else if decoded_len(m as nat) <= old(out).len() {
                r == Ok::<usize, B64Error>(decoded_len(m as nat) as usize) && final(out)@.subrange(
                    0,
                    decoded_len(m as nat) as int,
                ) == Seq::new(decoded_len(m as nat), |i: int| dec_byte(url, c@, m as int, i))
            } else {
                r == Err::<usize, B64Error>(B64Error::TooSmall)
            }
        }),
{
    let rem = m % 4;
    if rem == 1 {
        return Err(B64Error::Remainder);
    }
    if eq > 0 && (rem == 0 || rem + eq != 4) {
        return Err(B64Error::Invalid);
    }
    let d = dec_len(m);
    if d > out.len() {
        return Err(B64Error::TooSmall);
    }
    decode_body(url, c, m, out);
    Ok(d)
}

} // verus!
