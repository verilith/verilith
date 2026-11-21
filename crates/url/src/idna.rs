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

/// `utf8_scalars` is the decoding of well-formed UTF-8: its encoding is the
/// input, and it is made of scalars.
pub proof fn lemma_utf8_scalars(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
        utf8_from(s, i),
    ensures
        enc(utf8_scalars(s, i)) == s.subrange(i, s.len() as int),
        scalars(utf8_scalars(s, i)),
    decreases s.len() - i,
{
    if i < s.len() {
        let l = utf8_len(s, i)->0;
        verilith_text::utf::spec::lemma_dec8_roundtrip(s, i);
        let c = dec8_at(s, i, l);
        lemma_utf8_scalars(s, i + l);
        let rest = utf8_scalars(s, i + l);
        lemma_enc_append(seq![c], rest);
        lemma_enc_one(c);
        assert(s.subrange(i, s.len() as int) =~= s.subrange(i, i + l) + s.subrange(i + l, s.len() as int));
        assert(utf8_scalars(s, i) == seq![c] + rest);
        assert forall|k: int| 0 <= k < utf8_scalars(s, i).len() implies is_scalar(#[trigger] utf8_scalars(s, i)[k]) by {
            if k > 0 {
                assert(utf8_scalars(s, i)[k] == rest[k - 1]);
            }
        }
    } else {
        assert(utf8_scalars(s, i) =~= Seq::<u32>::empty());
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
    if !utf8_ok(domain) {
        return false;
    }
    let ghost cs = utf8_scalars(domain@, 0);
    proof {
        lemma_utf8_scalars(domain@, 0);
        assert(domain@.subrange(0, domain@.len() as int) =~= domain@);
    }
    let o = verilith_text::idna::spec::Options {
        check_hyphens: false,
        check_bidi: true,
        check_joiners: true,
        use_std3_ascii_rules: false,
        transitional: false,
        verify_dns_length: false,
    };
    let before = out.len();
    if !verilith_text::idna::uts46::url_domain_to_ascii_into(domain, o, Ghost(cs), map, out) {
        return false;
    }
    // At most 8 bytes per input byte: `v <= 8 n` exactly when
    // `ceil(v / 8) <= n`, which cannot overflow.
    let v = out.len() - before;
    v / 8 + (if v % 8 == 0 { 0 } else { 1 }) <= domain.len()
}

} // verus!
