//! UTS #46's entry points on a `&str`: each passes the bytes of `s`, which
//! [`str_bytes`] proves encode its scalars, to the verified function of
//! the same name in `uts46`, so the unverified glue in `idna/mod.rs` has
//! no precondition left to meet.
#[cfg(verus_only)]
use super::spec::*;
#[cfg(verus_only)]
use super::uts46::{lower, url_domain_to_ascii};
use super::uts46;
use super::spec::Options;
use crate::unicode::strs::str_bytes;
#[cfg(verus_only)]
use crate::unicode::strs::str_cs;
#[cfg(verus_only)]
use crate::unicode::spec::enc;
#[cfg(verus_only)]
use crate::unicode::data::scalars;
#[cfg(verus_only)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

/// [`uts46::ascii_unchanged`] on `s`.
pub fn ascii_unchanged_str(s: &str, o: Options) -> (r: bool)
    ensures
        r ==> to_ascii(str_cs(s), o) == Some(enc(str_cs(s))) && process(str_cs(s), o) == (widen(enc(str_cs(s))), false),
{
    let b = str_bytes(s);
    uts46::ascii_unchanged(b, o, Ghost(str_cs(s)))
}

/// [`uts46::to_ascii_fast`] on `s`.
pub fn to_ascii_fast_str(s: &str, o: Options) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(b) ==> to_ascii(str_cs(s), o) == Some(b@) && process(str_cs(s), o) == (widen(b@), false),
{
    let b = str_bytes(s);
    uts46::to_ascii_fast(b, o, Ghost(str_cs(s)))
}

/// [`uts46::to_ascii_exec`] on `s`.
pub fn to_ascii_str(s: &str, o: Options) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(b) ==> to_ascii(str_cs(s), o) == Some(b@),
        r is None ==> to_ascii(str_cs(s), o) is None,
{
    let b = str_bytes(s);
    uts46::to_ascii_exec(b, o, Ghost(str_cs(s)))
}

/// [`uts46::process_exec`] on `s`.
pub fn process_str(s: &str, o: Options) -> (r: (Vec<u32>, bool))
    ensures
        (r.0@, r.1) == process(str_cs(s), o),
{
    let b = str_bytes(s);
    uts46::process_exec(b, o, Ghost(str_cs(s)))
}

/// [`uts46::url_domain_to_ascii_exec`] on `s`.
pub fn url_domain_to_ascii_str(s: &str, o: Options) -> (r: Option<Vec<u8>>)
    ensures
        r matches Some(b) ==> url_domain_to_ascii(str_cs(s), o) == Some(b@),
        r is None ==> url_domain_to_ascii(str_cs(s), o) is None,
{
    let b = str_bytes(s);
    uts46::url_domain_to_ascii_exec(b, o, Ghost(str_cs(s)))
}

/// The bytes of ASCII text are `enc` of themselves, widened.
proof fn lemma_enc_widen_ascii(b: Seq<u8>)
    requires
        forall|j: int| 0 <= j < b.len() ==> #[trigger] b[j] < 0x80,
    ensures
        enc(widen(b)) == b,
        scalars(widen(b)),
    decreases b.len(),
{
    if b.len() > 0 {
        let a = b.drop_last();
        lemma_enc_widen_ascii(a);
        assert(widen(b).drop_last() =~= widen(a));
        assert(widen(b).last() == b.last() as u32);
        assert(utf8_encode(b.last() as u32) =~= seq![b.last()]);
        assert(a + seq![b.last()] =~= b);
    } else {
        assert(widen(b) =~= Seq::<u32>::empty());
    }
}

/// [`uts46::ascii_checked`] on bytes from outside Rust, which need not be
/// UTF-8: false unless they are ASCII, which is.
pub fn ascii_checked_bytes(s: &[u8], o: Options) -> (r: bool)
    ensures
        r ==> (forall|j: int| 0 <= j < s@.len() ==> #[trigger] s@[j] < 0x80) && to_ascii(widen(s@), o) == Some(
            narrow(lower(widen(s@))),
        ) && process(widen(s@), o) == (lower(widen(s@)), false),
{
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(),
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] < 0x80,
        decreases n - i,
    {
        if s[i] >= 0x80 {
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_enc_widen_ascii(s@);
    }
    uts46::ascii_checked(s, o, Ghost(widen(s@)))
}

} // verus!
