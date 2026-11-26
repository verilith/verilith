//! UTS #46 processing for non-ASCII domains, through vtext's verified
//! implementation (`verilith_text::idna::uts46::url_domain_to_ascii_exec`, proven
//! equal to its transliteration of UTS #46).
//!
//! What is still assumed here is cost, not correctness: vtext's ToASCII is
//! not metered, so it is charged `domain.len()` steps. Its output length is
//! checked: a result over 8 bytes per input byte fails, as
//! `spec::domain_to_ascii` says (the largest ratio over every code point
//! is under 6: U+337F, 3 bytes, becomes "xn--" and 13 more).
use crate::spec::*;
use verilith_core::utf8::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_text::unicode::data::{is_scalar, scalars};
#[cfg(verus_only)]
use verilith_text::unicode::spec::{enc, lemma_enc_append, lemma_enc_one};
#[cfg(verus_only)]
use verilith_text::utf::spec::dec8_at;

verus! {

/// `utf8_decode` is made of scalars, and on well-formed UTF-8 its
/// encoding is the input.
pub proof fn lemma_utf8_decode(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        utf8_from(s, i) ==> enc(utf8_decode(s, i)) == s.subrange(i, s.len() as int),
        scalars(utf8_decode(s, i)),
    decreases s.len() - i,
{
    if i < s.len() {
        let d = utf8_decode(s, i);
        match utf8_len(s, i) {
            Some(l) => {
                verilith_text::utf::spec::lemma_dec8_roundtrip(s, i);
                let c = dec8_at(s, i, l);
                lemma_utf8_decode(s, i + l);
                let rest = utf8_decode(s, i + l);
                lemma_enc_append(seq![c], rest);
                lemma_enc_one(c);
                assert(s.subrange(i, s.len() as int) =~= s.subrange(i, i + l) + s.subrange(i + l, s.len() as int));
                assert(d == seq![c] + rest);
                assert forall|k: int| 0 <= k < d.len() implies is_scalar(#[trigger] d[k]) by {
                    if k > 0 {
                        assert(d[k] == rest[k - 1]);
                    }
                }
            },
            None => {
                let j = i + utf8_subpart(s, i);
                lemma_utf8_decode(s, j);
                let rest = utf8_decode(s, j);
                assert(d == seq![0xFFFDu32] + rest);
                assert forall|k: int| 0 <= k < d.len() implies is_scalar(#[trigger] d[k]) by {
                    if k > 0 {
                        assert(d[k] == rest[k - 1]);
                    }
                }
            },
        }
    } else {
        assert(utf8_decode(s, i) =~= Seq::<u32>::empty());
        assert(enc(Seq::<u32>::empty()) =~= Seq::<u8>::empty());
        assert(s.subrange(i, s.len() as int) =~= Seq::<u8>::empty());
    }
}

/// The length of the well-formed UTF-8 sequence at `i`, or 0.
fn utf8_len_exec(s: &[u8], i: usize) -> (r: usize)
    requires
        i < s.len(),
    ensures
        r == match utf8_len(s@, i as int) {
            Some(l) => l,
            None => 0,
        },
        r <= 4,
{
    let n = s.len();
    let b = s[i];
    if b <= 0x7F {
        1
    } else if 0xC2 <= b && b <= 0xDF {
        if n - i > 1 && 0x80 <= s[i + 1] && s[i + 1] <= 0xBF { 2 } else { 0 }
    } else if 0xE0 <= b && b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if n - i > 2 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF { 3 } else { 0 }
    } else if 0xF0 <= b && b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if n - i > 3 && lo <= s[i + 1] && s[i + 1] <= hi && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF && 0x80 <= s[i + 3] && s[i + 3] <= 0xBF {
            4
        } else {
            0
        }
    } else {
        0
    }
}

/// The length of the maximal subpart of the ill-formed UTF-8 at `i`.
fn utf8_subpart_exec(s: &[u8], i: usize) -> (r: usize)
    requires
        i < s.len(),
        utf8_len(s@, i as int) is None,
    ensures
        r == utf8_subpart(s@, i as int),
        1 <= r <= s.len() - i,
{
    let n = s.len();
    let b = s[i];
    if 0xE0 <= b && b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if n - i > 1 && lo <= s[i + 1] && s[i + 1] <= hi { 2 } else { 1 }
    } else if 0xF0 <= b && b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if n - i > 1 && lo <= s[i + 1] && s[i + 1] <= hi {
            if n - i > 2 && 0x80 <= s[i + 2] && s[i + 2] <= 0xBF { 3 } else { 2 }
        } else {
            1
        }
    } else {
        1
    }
}

/// The UTF-8 encoding of `utf8_decode(s, 0)`: `s` with each maximal
/// subpart of ill-formed UTF-8 replaced by U+FFFD's three bytes.
fn utf8_lossy(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == enc(utf8_decode(s@, 0)),
{
    let n = s.len();
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(enc(Seq::<u32>::empty()) =~= Seq::<u8>::empty());
        assert(v@ + enc(utf8_decode(s@, 0)) =~= enc(utf8_decode(s@, 0)));
    }
    while i < n
        invariant
            i <= n == s@.len(),
            enc(utf8_decode(s@, 0)) == v@ + enc(utf8_decode(s@, i as int)),
        decreases n - i,
    {
        let ghost v0 = v@;
        let l = utf8_len_exec(s, i);
        if l == 0 {
            let j = utf8_subpart_exec(s, i);
            v.push(0xEF);
            v.push(0xBF);
            v.push(0xBD);
            proof {
                let rest = utf8_decode(s@, (i + j) as int);
                assert(utf8_decode(s@, i as int) == seq![0xFFFDu32] + rest);
                lemma_enc_append(seq![0xFFFDu32], rest);
                lemma_enc_one(0xFFFDu32);
                assert(utf8_encode(0xFFFDu32) =~= seq![0xEFu8, 0xBF, 0xBD]);
                assert(v@ =~= v0 + seq![0xEFu8, 0xBF, 0xBD]);
                assert(v0 + (seq![0xEFu8, 0xBF, 0xBD] + enc(rest)) =~= v@ + enc(rest));
            }
            i += j;
        } else {
            proof {
                verilith_text::utf::spec::lemma_dec8_roundtrip(s@, i as int);
            }
            let mut k: usize = 0;
            while k < l
                invariant
                    i + l <= n == s@.len(),
                    k <= l,
                    v@ == v0 + s@.subrange(i as int, (i + k) as int),
                decreases l - k,
            {
                v.push(s[i + k]);
                proof {
                    assert(v@ =~= v0 + s@.subrange(i as int, (i + k + 1) as int));
                }
                k += 1;
            }
            proof {
                let c = dec8_at(s@, i as int, l as int);
                let rest = utf8_decode(s@, (i + l) as int);
                assert(utf8_decode(s@, i as int) == seq![c] + rest);
                lemma_enc_append(seq![c], rest);
                lemma_enc_one(c);
                assert(v0 + (s@.subrange(i as int, (i + l) as int) + enc(rest)) =~= v@ + enc(rest));
            }
            i += l;
        }
    }
    proof {
        assert(utf8_decode(s@, n as int) =~= Seq::<u32>::empty());
        assert(enc(Seq::<u32>::empty()) =~= Seq::<u8>::empty());
        assert(v@ + Seq::<u8>::empty() =~= v@);
    }
    v
}

/// Whether `s` is well-formed UTF-8, one sequence at a time.
fn utf8_ok(s: &[u8]) -> (r: bool)
    ensures
        r == utf8_from(s@, 0),
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == s@.len(),
            utf8_from(s@, 0) == utf8_from(s@, i as int),
        decreases n - i,
    {
        let l = utf8_len_exec(s, i);
        if l == 0 {
            return false;
        }
        i += l;
    }
    true
}

/// UTS #46 ToASCII of the UTF-8 decoding of `domain`, as the URL Standard's
/// host parser runs it (see `spec::domain_to_ascii`), appended to `out`;
/// `map` is scratch storage. It is charged `domain.len()` steps (assumed
/// linear); a result more than 8 times longer fails. On failure `out` may
/// hold part of the result.
pub fn domain_to_ascii_into(domain: &[u8], map: &mut Vec<u32>, out: &mut Vec<u8>, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    ensures
        r == crate::spec::domain_to_ascii(domain@) is Some,
        r ==> final(out)@ == old(out)@ + crate::spec::domain_to_ascii(domain@)->0,
        r ==> crate::spec::domain_to_ascii(domain@)->0.len() <= 8 * domain.len(),
        final(cost).n == old(cost).n + domain.len(),
{
    proof {
        cost.n = (cost.n + domain.len()) as nat;
        reveal(crate::spec::domain_to_ascii);
    }
    let ghost cs = utf8_decode(domain@, 0);
    proof {
        lemma_utf8_decode(domain@, 0);
        assert(domain@.subrange(0, domain@.len() as int) =~= domain@);
    }
    // Ill-formed UTF-8 goes to UTS #46 with U+FFFD in place of each maximal
    // subpart, as the Standard says. (U+FFFD is disallowed, so it fails.)
    let fixed: Vec<u8>;
    let text: &[u8] = if utf8_ok(domain) {
        domain
    } else {
        fixed = utf8_lossy(domain);
        fixed.as_slice()
    };
    let o = verilith_text::idna::spec::Options {
        check_hyphens: false,
        check_bidi: true,
        check_joiners: true,
        use_std3_ascii_rules: false,
        transitional: false,
        verify_dns_length: false,
    };
    let before = out.len();
    if !verilith_text::idna::uts46::url_domain_to_ascii_into(text, o, Ghost(cs), map, out) {
        return false;
    }
    // At most 8 bytes per input byte: `v <= 8 n` exactly when
    // `ceil(v / 8) <= n`, which cannot overflow.
    let v = out.len() - before;
    v / 8 + (if v % 8 == 0 { 0 } else { 1 }) <= domain.len()
}

} // verus!
