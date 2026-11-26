//! The bridge from a `&str` to the verified normalizer: vstd's model of
//! a `str` is its characters `s@`, and of its bytes (`as_bytes`) their
//! UTF-8 encoding, so the bytes of a `&str` are proven to be `enc` of its
//! scalars. The functions here are the normalizer's entry points on a
//! `&str`, with no precondition left for the unverified glue in
//! `unicode/mod.rs` and `idna/mod.rs` to meet.
use super::norm;
#[cfg(verus_only)]
use super::data::*;
#[cfg(verus_only)]
use super::spec::*;
#[cfg(verus_only)]
use verilith_core::utf8::{lemma_char_scalar, lemma_utf8_encode_vstd};
use vstd::prelude::*;

verus! {

/// The scalars of `s`.
pub open spec fn str_cs(s: &str) -> Seq<u32> {
    s@.map_values(|c: char| c as u32)
}

/// The scalars of a sequence of characters.
pub open spec fn chars_cs(cs: Seq<char>) -> Seq<u32> {
    cs.map_values(|c: char| c as u32)
}

/// `enc` of the scalars of some characters is vstd's `encode_utf8` of
/// them, and they are scalars.
pub proof fn lemma_chars_enc(cs: Seq<char>)
    ensures
        scalars(chars_cs(cs)),
        enc(chars_cs(cs)) == vstd::utf8::encode_utf8(cs),
    decreases cs.len(),
{
    broadcast use vstd::utf8::encode_utf8_concat;

    assert forall|i: int| 0 <= i < chars_cs(cs).len() implies is_scalar(#[trigger] chars_cs(cs)[i]) by {
        lemma_char_scalar(cs[i]);
    }
    if cs.len() > 0 {
        let a = cs.drop_last();
        let c = cs.last();
        lemma_chars_enc(a);
        assert(chars_cs(cs).drop_last() =~= chars_cs(a));
        assert(chars_cs(cs).last() == c as u32);
        assert(cs =~= a + seq![c]);
        lemma_char_scalar(c);
        lemma_utf8_encode_vstd(c as u32);
        assert(seq![c].drop_first() =~= Seq::<char>::empty());
        assert(seq![c][0] == c);
        assert(vstd::utf8::encode_utf8(Seq::<char>::empty()) == Seq::<u8>::empty());
        assert(vstd::utf8::encode_utf8(seq![c]) == vstd::utf8::encode_scalar(c as u32) + vstd::utf8::encode_utf8(
            Seq::<char>::empty(),
        ));
        assert(vstd::utf8::encode_utf8(seq![c]) =~= vstd::utf8::encode_scalar(c as u32));
        assert(vstd::utf8::encode_utf8(a + seq![c]) == vstd::utf8::encode_utf8(a) + vstd::utf8::encode_utf8(seq![c]));
    } else {
        assert(chars_cs(cs) =~= Seq::<u32>::empty());
    }
}

/// The bytes of `s`, which encode its scalars.
#[inline(always)]
pub fn str_bytes(s: &str) -> (b: &[u8])
    ensures
        scalars(str_cs(s)),
        b@ == enc(str_cs(s)),
{
    let b = s.as_bytes();
    proof {
        lemma_chars_enc(s@);
        assert(str_cs(s) == chars_cs(s@));
    }
    b
}

/// [`norm::normalize_into`] on the bytes of `s`.
pub fn normalize_into_str(s: &str, compose: bool, compat: bool, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + enc(nf(str_cs(s), compose, compat)),
{
    let b = str_bytes(s);
    norm::normalize_into(b, compose, compat, out, Ghost(str_cs(s)))
}

/// [`norm::quick_check`] on the bytes of `s`.
pub fn quick_check_str(s: &str, compose: bool, compat: bool) -> (r: bool)
    ensures
        r ==> nf(str_cs(s), compose, compat) == str_cs(s),
{
    let b = str_bytes(s);
    norm::quick_check(b, compose, compat, Ghost(str_cs(s)))
}

/// [`norm::normalize_slow`] on the bytes of `s`.
pub fn normalize_slow_str(s: &str, compose: bool, compat: bool, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + enc(nf(str_cs(s), compose, compat)),
{
    let b = str_bytes(s);
    norm::normalize_slow(b, compose, compat, out, Ghost(str_cs(s)))
}

} // verus!
