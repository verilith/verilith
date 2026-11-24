//! `URLSearchParams`: the application/x-www-form-urlencoded list of
//! name-value pairs (URL Standard §5).
//!
//! Names and values are kept as the decoded bytes (as ada does), so a
//! percent-encoded byte sequence that is not UTF-8 round-trips unchanged.
//!
//! Proven against the Standard's parser and serializer (`form_parse`,
//! `form_serialize` below): parsing (`UrlSearchParams::parse`, `reset`)
//! and serializing (`to_bytes`), and that a list serializes to bytes that
//! parse back to the same list (`theorem_serialize_parse`). The list edits
//! (`append`, `set`, `remove`, ...) and the UTF-16 `sort` are plain Rust.
#[cfg(verus_only)]
use crate::spec::*;
use crate::host::{hex_val, is_hex_digit};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification (URL Standard §5.1 and §5.2)
// ---------------------------------------------------------------------------

/// The application/x-www-form-urlencoded percent-encode set: the component
/// percent-encode set and !, ' to ), and ~.
pub open spec fn in_component_set(c: u8) -> bool {
    in_userinfo_set(c) || (b'$' <= c <= b'&') || c == b'+' || c == b','
}

pub open spec fn in_form_set(c: u8) -> bool {
    in_component_set(c) || c == b'!' || (b'\'' <= c <= b')') || c == b'~'
}

/// One byte, percent-encoded with the form set and a space as "+"
/// (percent-encode after encoding, with spaceAsPlus).
pub open spec fn form_pe(c: u8) -> Seq<u8> {
    if c == b' ' {
        seq![b'+']
    } else if in_form_set(c) {
        percent_encode_byte(c)
    } else {
        seq![c]
    }
}

pub open spec fn spec_form_encode(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        form_pe(s[0]) + spec_form_encode(s.skip(1))
    }
}

/// Replace each "+" with a space.
pub open spec fn plus_to_space(s: Seq<u8>) -> Seq<u8> {
    s.map_values(|c: u8| if c == b'+' { b' ' } else { c })
}

/// A name or value: "+" as space, then percent-decoded.
pub open spec fn spec_form_decode(s: Seq<u8>) -> Seq<u8> {
    percent_decode(plus_to_space(s))
}

/// The first index at or after `i` where `s` has byte `c`, or `s.len()`.
pub open spec fn find(s: Seq<u8>, c: u8, i: int) -> int
    decreases s.len() - i,
{
    if i >= s.len() {
        s.len() as int
    } else if s[i] == c {
        i
    } else {
        find(s, c, i + 1)
    }
}

/// One non-empty sequence between "&"s: the name up to the first "=", and
/// the value after it (empty if there is no "=").
pub open spec fn form_pair(b: Seq<u8>) -> (Seq<u8>, Seq<u8>) {
    let q = find(b, b'=', 0);
    if q < b.len() {
        (spec_form_decode(b.subrange(0, q)), spec_form_decode(b.subrange(q + 1, b.len() as int)))
    } else {
        (spec_form_decode(b), Seq::empty())
    }
}

/// The application/x-www-form-urlencoded parser: split on "&", skip empty
/// sequences, split each at its first "=".
pub open spec fn form_parse(s: Seq<u8>) -> Seq<(Seq<u8>, Seq<u8>)>
    decreases s.len() via form_parse_decreases
{
    let e = find(s, b'&', 0);
    let part = s.subrange(0, e);
    let rest = if e < s.len() {
        form_parse(s.subrange(e + 1, s.len() as int))
    } else {
        Seq::empty()
    };
    if part.len() == 0 {
        rest
    } else {
        seq![form_pair(part)] + rest
    }
}

#[via_fn]
proof fn form_parse_decreases(s: Seq<u8>) {
    lemma_find_bound(s, b'&', 0);
}

pub open spec fn form_tuple(p: (Seq<u8>, Seq<u8>)) -> Seq<u8> {
    spec_form_encode(p.0) + seq![b'='] + spec_form_encode(p.1)
}

/// The application/x-www-form-urlencoded serializer: each pair as
/// name=value, joined with "&".
pub open spec fn form_serialize(l: Seq<(Seq<u8>, Seq<u8>)>) -> Seq<u8>
    decreases l.len(),
{
    if l.len() == 0 {
        Seq::empty()
    } else if l.len() == 1 {
        form_tuple(l[0])
    } else {
        form_tuple(l[0]) + seq![b'&'] + form_serialize(l.skip(1))
    }
}

/// What `new URLSearchParams(init)` holds for a string `init`: a leading
/// "?" is dropped, then the rest is parsed.
pub open spec fn params_init(s: Seq<u8>) -> Seq<(Seq<u8>, Seq<u8>)> {
    if s.len() > 0 && s[0] == b'?' {
        form_parse(s.skip(1))
    } else {
        form_parse(s)
    }
}

pub open spec fn list_view(l: Seq<(Vec<u8>, Vec<u8>)>) -> Seq<(Seq<u8>, Seq<u8>)> {
    l.map_values(|p: (Vec<u8>, Vec<u8>)| (p.0@, p.1@))
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

proof fn lemma_find(s: Seq<u8>, c: u8, i: int, e: int)
    requires
        0 <= i <= e <= s.len(),
        forall|k: int| i <= k < e ==> s[k] != c,
        e == s.len() || s[e] == c,
    ensures
        find(s, c, i) == e,
    decreases e - i,
{
    if i < e {
        lemma_find(s, c, i + 1, e);
    }
}

proof fn lemma_find_bound(s: Seq<u8>, c: u8, i: int)
    requires
        0 <= i,
    ensures
        i <= find(s, c, i) <= s.len() || (i > s.len() && find(s, c, i) == s.len()),
        find(s, c, i) < s.len() ==> s[find(s, c, i)] == c,
        forall|k: int| i <= k < find(s, c, i) ==> s[k] != c,
    decreases s.len() - i,
{
    if i < s.len() && s[i] != c {
        lemma_find_bound(s, c, i + 1);
    }
}

/// The form set, as the encoder tests it: everything but ASCII
/// alphanumerics, "*", "-", "." and "_".
proof fn lemma_form_set(c: u8)
    ensures
        in_form_set(c) <==> !(is_ascii_alphanumeric(c) || c == b'*' || c == b'-' || c == b'.' || c == b'_'),
{
}

proof fn lemma_upper_hex(n: nat)
    requires
        n < 16,
    ensures
        is_ascii_hex_digit(upper_hex_digit(n)),
        hex_value(upper_hex_digit(n)) == n,
        upper_hex_digit(n) != b'+',
        upper_hex_digit(n) != b'&',
        upper_hex_digit(n) != b'=',
        upper_hex_digit(n) != b'%',
{
}

proof fn lemma_form_pe(c: u8)
    ensures
        forall|j: int| 0 <= j < form_pe(c).len() ==> #[trigger] form_pe(c)[j] != b'&' && form_pe(c)[j] != b'=',
        form_pe(c).len() >= 1,
{
    if c != b' ' && in_form_set(c) {
        lemma_upper_hex((c / 16) as nat);
        lemma_upper_hex((c % 16) as nat);
    }
}

proof fn lemma_encode_len(s: Seq<u8>)
    ensures
        spec_form_encode(s).len() >= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_form_pe(s[0]);
        lemma_encode_len(s.skip(1));
    }
}

/// Encoded bytes hold no "&" and no "=".
proof fn lemma_encode_clean(s: Seq<u8>)
    ensures
        forall|j: int| 0 <= j < spec_form_encode(s).len() ==> #[trigger] spec_form_encode(s)[j] != b'&' && spec_form_encode(s)[j] != b'=',
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_form_pe(s[0]);
        lemma_encode_clean(s.skip(1));
        let a = form_pe(s[0]);
        let b = spec_form_encode(s.skip(1));
        assert forall|j: int| 0 <= j < (a + b).len() implies #[trigger] (a + b)[j] != b'&' && (a + b)[j] != b'=' by {
            if j < a.len() {
                assert((a + b)[j] == a[j]);
            } else {
                assert((a + b)[j] == b[j - a.len()]);
            }
        }
    }
}

proof fn lemma_plus_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        plus_to_space(a + b) == plus_to_space(a) + plus_to_space(b),
{
    assert(plus_to_space(a + b) =~= plus_to_space(a) + plus_to_space(b));
}

/// Decoding undoes encoding.
proof fn lemma_decode_encode(s: Seq<u8>)
    ensures
        spec_form_decode(spec_form_encode(s)) == s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(plus_to_space(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
    } else {
        let c = s[0];
        let a = form_pe(c);
        let b = spec_form_encode(s.skip(1));
        lemma_decode_encode(s.skip(1));
        lemma_plus_concat(a, b);
        let pa = plus_to_space(a);
        let pb = plus_to_space(b);
        let t = pa + pb;
        if c == b' ' {
            assert(pa =~= seq![b' ']);
            assert(t[0] == b' ');
            assert(t.skip(1) =~= pb);
        } else if in_form_set(c) {
            let h = upper_hex_digit((c / 16) as nat);
            let l = upper_hex_digit((c % 16) as nat);
            lemma_upper_hex((c / 16) as nat);
            lemma_upper_hex((c % 16) as nat);
            assert(pa =~= seq![b'%', h, l]);
            assert(t[0] == b'%' && t[1] == h && t[2] == l);
            assert(t.skip(3) =~= pb);
            assert((hex_value(h) * 16 + hex_value(l)) as u8 == c);
        } else {
            lemma_form_set(c);
            assert(pa =~= seq![c]);
            assert(t[0] == c);
            assert(t.skip(1) =~= pb);
        }
        assert(seq![c] + s.skip(1) =~= s);
    }
}

/// Bytes with no "&" and no "=" around one "=".
proof fn lemma_pair_back(k: Seq<u8>, v: Seq<u8>)
    ensures
        form_pair(form_tuple((k, v))) == (k, v),
        form_tuple((k, v)).len() >= 1,
        forall|j: int| 0 <= j < form_tuple((k, v)).len() ==> #[trigger] form_tuple((k, v))[j] != b'&',
{
    let ek = spec_form_encode(k);
    let ev = spec_form_encode(v);
    let t = form_tuple((k, v));
    lemma_encode_clean(k);
    lemma_encode_clean(v);
    assert(t == ek + seq![b'='] + ev);
    assert forall|j: int| 0 <= j < ek.len() implies t[j] != b'=' by {
        assert(t[j] == ek[j]);
    }
    assert(t[ek.len() as int] == b'=');
    lemma_find(t, b'=', 0, ek.len() as int);
    assert(t.subrange(0, ek.len() as int) =~= ek);
    assert(t.subrange((ek.len() + 1) as int, t.len() as int) =~= ev);
    lemma_decode_encode(k);
    lemma_decode_encode(v);
    assert forall|j: int| 0 <= j < t.len() implies #[trigger] t[j] != b'&' by {
        if j < ek.len() {
            assert(t[j] == ek[j]);
        } else if j > ek.len() {
            assert(t[j] == ev[j - ek.len() - 1]);
        }
    }
}

/// The serializer's output parses back to the list it serialized.
pub proof fn theorem_serialize_parse(l: Seq<(Seq<u8>, Seq<u8>)>)
    ensures
        form_parse(form_serialize(l)) == l,
    decreases l.len(),
{
    if l.len() == 0 {
        assert(form_serialize(l) =~= Seq::<u8>::empty());
        assert(Seq::<u8>::empty().subrange(0, 0) =~= Seq::<u8>::empty());
        lemma_find(Seq::<u8>::empty(), b'&', 0, 0);
    } else {
        let p = l[0];
        let t = form_tuple(p);
        lemma_pair_back(p.0, p.1);
        let s = form_serialize(l);
        if l.len() == 1 {
            assert(s == t);
            lemma_find(s, b'&', 0, s.len() as int);
            assert(s.subrange(0, s.len() as int) =~= s);
            assert(l =~= seq![p]);
            assert(seq![form_pair(t)] + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= l);
        } else {
            let r = form_serialize(l.skip(1));
            theorem_serialize_parse(l.skip(1));
            assert(s == t + seq![b'&'] + r);
            assert forall|k: int| 0 <= k < t.len() implies s[k] != b'&' by {
                assert(s[k] == t[k]);
            }
            assert(s[t.len() as int] == b'&');
            lemma_find(s, b'&', 0, t.len() as int);
            assert(s.subrange(0, t.len() as int) =~= t);
            assert(s.subrange((t.len() + 1) as int, s.len() as int) =~= r);
            assert(seq![p] + l.skip(1) =~= l);
        }
    }
}

proof fn lemma_encode_push(s: Seq<u8>, c: u8)
    ensures
        spec_form_encode(s.push(c)) == spec_form_encode(s) + form_pe(c),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(c).skip(1) =~= Seq::<u8>::empty());
        assert(spec_form_encode(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        assert(form_pe(c) + Seq::<u8>::empty() =~= form_pe(c));
        assert(Seq::<u8>::empty() + form_pe(c) =~= form_pe(c));
    } else {
        lemma_encode_push(s.skip(1), c);
        assert(s.push(c).skip(1) =~= s.skip(1).push(c));
        assert(s.push(c)[0] == s[0]);
        assert(form_pe(s[0]) + (spec_form_encode(s.skip(1)) + form_pe(c)) =~= (form_pe(s[0]) + spec_form_encode(s.skip(1))) + form_pe(c));
    }
}

proof fn lemma_serialize_push(l: Seq<(Seq<u8>, Seq<u8>)>, p: (Seq<u8>, Seq<u8>))
    ensures
        form_serialize(l.push(p)) == if l.len() == 0 {
            form_tuple(p)
        } else {
            form_serialize(l) + seq![b'&'] + form_tuple(p)
        },
    decreases l.len(),
{
    if l.len() == 0 {
        assert(l.push(p).len() == 1);
        assert(l.push(p)[0] == p);
    } else if l.len() == 1 {
        assert(l.push(p).skip(1) =~= seq![p]);
        assert(l.push(p)[0] == l[0]);
        assert(seq![p].len() == 1 && seq![p][0] == p);
        assert(form_serialize(seq![p]) == form_tuple(p));
    } else {
        lemma_serialize_push(l.skip(1), p);
        assert(l.push(p).skip(1) =~= l.skip(1).push(p));
        assert(l.push(p)[0] == l[0]);
        let a = form_tuple(l[0]);
        let b = form_serialize(l.skip(1));
        assert(a + seq![b'&'] + (b + seq![b'&'] + form_tuple(p)) =~= (a + seq![b'&'] + b) + seq![b'&'] + form_tuple(p));
    }
}

// ---------------------------------------------------------------------------
// Executable code
// ---------------------------------------------------------------------------

/// Replaces "+" with a space, then percent-decodes (`spec_form_decode`).
pub fn form_decode_exec(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == spec_form_decode(s@),
{
    let ghost t = plus_to_space(s@);
    let mut out: Vec<u8> = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    proof {
        assert(t.skip(0) =~= t);
        assert(out@ + percent_decode(t.skip(0)) =~= percent_decode(t));
    }
    while i < s.len()
        invariant
            i <= s.len(),
            t == plus_to_space(s@),
            t.len() == s@.len(),
            percent_decode(t) == out@ + percent_decode(t.skip(i as int)),
        decreases s.len() - i,
    {
        let ghost rest = t.skip(i as int);
        let c = s[i];
        if c == b'%' && s.len() - i >= 3 && is_hex_digit(s[i + 1]) && is_hex_digit(s[i + 2]) {
            let b = hex_val(s[i + 1]) * 16 + hex_val(s[i + 2]);
            proof {
                assert(rest[0] == b'%' && rest[1] == s[i + 1 as int] && rest[2] == s[i + 2 as int]);
                assert(rest.skip(3) =~= t.skip(i + 3));
            }
            out.push(b);
            i = i + 3;
            proof {
                assert(percent_decode(t) =~= out@ + percent_decode(t.skip(i as int)));
            }
        } else {
            let d = if c == b'+' { b' ' } else { c };
            proof {
                assert(rest[0] == d);
                if rest.len() >= 3 {
                    assert(rest[1] == t[i + 1 as int] && rest[2] == t[i + 2 as int]);
                }
                assert(rest.skip(1) =~= t.skip(i + 1));
            }
            out.push(d);
            i = i + 1;
            proof {
                assert(percent_decode(t) =~= out@ + percent_decode(t.skip(i as int)));
            }
        }
    }
    proof {
        assert(t.skip(i as int) =~= Seq::<u8>::empty());
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

fn upper_hex(n: u8) -> (r: u8)
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

/// Appends `spec_form_encode(s)` to `out`.
pub fn form_encode_exec(s: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + spec_form_encode(s@),
{
    let mut i: usize = 0;
    proof {
        assert(s@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(spec_form_encode(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        assert(old(out)@ + Seq::<u8>::empty() =~= old(out)@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == old(out)@ + spec_form_encode(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let c = s[i];
        let ghost o0 = out@;
        proof {
            lemma_form_set(c);
            lemma_encode_push(s@.subrange(0, i as int), c);
            assert(s@.subrange(0, i as int).push(c) =~= s@.subrange(0, i + 1));
        }
        if (b'0' <= c && c <= b'9') || (b'A' <= c && c <= b'Z') || (b'a' <= c && c <= b'z') || c == b'*' || c == b'-'
            || c == b'.' || c == b'_' {
            out.push(c);
            proof {
                assert(out@ =~= o0 + form_pe(c));
            }
        } else if c == b' ' {
            out.push(b'+');
            proof {
                assert(out@ =~= o0 + form_pe(c));
            }
        } else {
            out.push(b'%');
            out.push(upper_hex(c / 16));
            out.push(upper_hex(c % 16));
            proof {
                assert(out@ =~= o0 + form_pe(c));
            }
        }
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, i as int) =~= s@);
    }
}

/// Parses `s` (`form_parse`), appending the pairs to `list`.
pub fn form_parse_into(s: &[u8], list: &mut Vec<(Vec<u8>, Vec<u8>)>)
    ensures
        list_view(final(list)@) == list_view(old(list)@) + form_parse(s@),
{
    let n = s.len();
    let mut i: usize = 0;
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
        assert(list_view(list@) + form_parse(s@) =~= list_view(old(list)@) + form_parse(s@.subrange(0, n as int)));
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            list_view(old(list)@) + form_parse(s@) == list_view(list@) + form_parse(s@.subrange(i as int, n as int)),
        decreases n - i,
    {
        let ghost r = s@.subrange(i as int, n as int);
        let mut e = i;
        while e < n && s[e] != b'&'
            invariant
                i <= e <= n,
                n == s@.len(),
                forall|k: int| i <= k < e ==> s@[k] != b'&',
            decreases n - e,
        {
            e = e + 1;
        }
        // The pair from s[i..e].
        let mut q = i;
        while q < e && s[q] != b'='
            invariant
                i <= q <= e,
                e <= n,
                n == s@.len(),
                forall|k: int| i <= k < q ==> s@[k] != b'=',
            decreases e - q,
        {
            q = q + 1;
        }
        let ghost part = s@.subrange(i as int, e as int);
        let ghost before = list_view(list@);
        proof {
            lemma_find(r, b'&', 0, e - i);
            assert(r.subrange(0, e - i) =~= part);
            if e < n {
                assert(r.subrange(e - i + 1, r.len() as int) =~= s@.subrange(e + 1, n as int));
            }
        }
        if e > i {
            let (k, v) = if q < e {
                proof {
                    lemma_find(part, b'=', 0, q - i);
                    assert(part.subrange(0, q - i) =~= s@.subrange(i as int, q as int));
                    assert(part.subrange(q - i + 1, part.len() as int) =~= s@.subrange(q + 1, e as int));
                }
                (form_decode_exec(vstd::slice::slice_subrange(s, i, q)), form_decode_exec(vstd::slice::slice_subrange(s, q + 1, e)))
            } else {
                proof {
                    lemma_find(part, b'=', 0, part.len() as int);
                }
                (form_decode_exec(vstd::slice::slice_subrange(s, i, e)), Vec::new())
            };
            proof {
                assert((k@, v@) == form_pair(part));
            }
            list.push((k, v));
            proof {
                assert(list_view(list@) =~= before.push(form_pair(part)));
            }
        }
        if e == n {
            proof {
                assert(s@.subrange(n as int, n as int) =~= Seq::<u8>::empty());
                lemma_find(Seq::<u8>::empty(), b'&', 0, 0);
                assert(form_parse(Seq::<u8>::empty()) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
                assert(list_view(list@) + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= list_view(list@));
                if e > i {
                    assert(before + (seq![form_pair(part)] + Seq::<(Seq<u8>, Seq<u8>)>::empty()) =~= list_view(list@));
                } else {
                    assert(before + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= list_view(list@));
                }
            }
            i = n;
        } else {
            proof {
                if e > i {
                    assert(before + (seq![form_pair(part)] + form_parse(s@.subrange(e + 1, n as int))) =~= list_view(list@)
                        + form_parse(s@.subrange(e + 1, n as int)));
                }
            }
            i = e + 1;
        }
    }
    proof {
        assert(s@.subrange(n as int, n as int) =~= Seq::<u8>::empty());
        lemma_find(Seq::<u8>::empty(), b'&', 0, 0);
        assert(form_parse(Seq::<u8>::empty()) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        assert(list_view(list@) + Seq::<(Seq<u8>, Seq<u8>)>::empty() =~= list_view(list@));
    }
}

/// `params_init`: replaces `list` with the pairs of `input`.
pub fn params_reset(input: &[u8], list: &mut Vec<(Vec<u8>, Vec<u8>)>)
    ensures
        list_view(final(list)@) == params_init(input@),
{
    list.clear();
    proof {
        assert(list_view(list@) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
    }
    if input.len() > 0 && input[0] == b'?' {
        let rest = vstd::slice::slice_subrange(input, 1, input.len());
        proof {
            assert(rest@ =~= input@.skip(1));
        }
        form_parse_into(rest, list);
    } else {
        form_parse_into(input, list);
    }
    proof {
        assert(list_view(final(list)@) =~= params_init(input@));
    }
}

/// Serializes `list` (`form_serialize`).
pub fn form_serialize_exec(list: &Vec<(Vec<u8>, Vec<u8>)>) -> (r: Vec<u8>)
    ensures
        r@ == form_serialize(list_view(list@)),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost l = list_view(list@);
    proof {
        assert(l.subrange(0, 0) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
    }
    while i < list.len()
        invariant
            i <= list@.len(),
            l == list_view(list@),
            out@ == form_serialize(l.subrange(0, i as int)),
        decreases list@.len() - i,
    {
        let ghost o0 = out@;
        if i > 0 {
            out.push(b'&');
        }
        let ghost o1 = out@;
        form_encode_exec(list[i].0.as_slice(), &mut out);
        out.push(b'=');
        form_encode_exec(list[i].1.as_slice(), &mut out);
        proof {
            let p = l[i as int];
            assert(p == (list@[i as int].0@, list@[i as int].1@));
            lemma_serialize_push(l.subrange(0, i as int), p);
            assert(l.subrange(0, i as int).push(p) =~= l.subrange(0, i + 1));
            assert(out@ =~= o1 + form_tuple(p));
            if i > 0 {
                assert(o1 =~= o0 + seq![b'&']);
            } else {
                assert(o0 =~= Seq::<u8>::empty());
                assert(o1 =~= Seq::<u8>::empty());
            }
        }
        i = i + 1;
    }
    proof {
        assert(l.subrange(0, i as int) =~= l);
    }
    out
}

} // verus!

/// A query's name-value pairs, the URL Standard's `URLSearchParams`: names and values are bytes, decoded.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct UrlSearchParams {
    /// The pairs, in order.
    pub list: Vec<(Vec<u8>, Vec<u8>)>,
}

/// Replaces "+" with a space, then percent-decodes. Verified
/// (`form_decode_exec` against `form_decode`).
pub fn form_decode(s: &[u8]) -> Vec<u8> {
    form_decode_exec(s)
}

/// The application/x-www-form-urlencoded percent-encode, with a space
/// written as "+". Verified (`form_encode_exec` against `form_encode`).
pub fn form_encode(s: &[u8], out: &mut Vec<u8>) {
    form_encode_exec(s, out)
}

/// Decodes the next UTF-16 code unit of `s` from byte `*i`, as ada's sort
/// does: bytes that do not start a complete UTF-8 sequence stand for
/// themselves.
fn next_unit(s: &[u8], i: &mut usize, low: &mut u32) -> u32 {
    if *low != 0 {
        let u = *low;
        *low = 0;
        return u;
    }
    let c = s[*i] as u32;
    let at = |k: usize| (s[*i + k] & 0x3F) as u32;
    if c > 0x7F && c <= 0xDF && *i + 1 < s.len() {
        let u = ((c & 0x1F) << 6) | at(1);
        *i += 2;
        u
    } else if c > 0xDF && c <= 0xEF && *i + 2 < s.len() {
        let u = ((c & 0x0F) << 12) | (at(1) << 6) | at(2);
        *i += 3;
        u
    } else if c > 0xEF && c <= 0xF7 && *i + 3 < s.len() {
        let cp = (((c & 0x07) << 18) | (at(1) << 12) | (at(2) << 6) | at(3)).wrapping_sub(0x10000);
        *i += 4;
        *low = 0xDC00 + (cp & 0x3FF);
        (0xD800 + (cp >> 10)) & 0xFFFF
    } else {
        *i += 1;
        c
    }
}

/// Compares two names by UTF-16 code units.
fn utf16_less(a: &[u8], b: &[u8]) -> bool {
    let (mut i, mut j, mut la, mut lb) = (0, 0, 0, 0);
    while (i < a.len() || la != 0) && (j < b.len() || lb != 0) {
        let x = next_unit(a, &mut i, &mut la);
        let y = next_unit(b, &mut j, &mut lb);
        if x != y {
            return x < y;
        }
    }
    j < b.len() || lb != 0
}

impl UrlSearchParams {
    /// Parses a query string; a leading "?" is skipped. Verified
    /// (`params_reset` against `params_init`).
    pub fn parse(input: &[u8]) -> UrlSearchParams {
        let mut p = UrlSearchParams::default();
        p.reset(input);
        p
    }

    /// Replaces the pairs with those parsed from `input` (a leading "?" is skipped).
    pub fn reset(&mut self, input: &[u8]) {
        params_reset(input, &mut self.list);
    }

    /// The number of pairs.
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Whether there are no pairs.
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Appends the pair `(k, v)`.
    pub fn append(&mut self, k: &[u8], v: &[u8]) {
        self.list.push((k.to_vec(), v.to_vec()));
    }

    /// Sets the first pair named `k` to `v` and removes the others, or
    /// appends the pair if there is none.
    pub fn set(&mut self, k: &[u8], v: &[u8]) {
        match self.list.iter().position(|(n, _)| n == k) {
            Some(i) => {
                self.list[i].1 = v.to_vec();
                let mut j = 0;
                self.list.retain(|(n, _)| {
                    j += 1;
                    j <= i + 1 || n != k
                });
            }
            None => self.append(k, v),
        }
    }

    /// Removes every pair named `k`.
    pub fn remove(&mut self, k: &[u8]) {
        self.list.retain(|(n, _)| n != k);
    }

    /// Removes every pair `(k, v)`.
    pub fn remove_value(&mut self, k: &[u8], v: &[u8]) {
        self.list.retain(|(n, x)| n != k || x != v);
    }

    /// Whether some pair is named `k`.
    pub fn has(&self, k: &[u8]) -> bool {
        self.list.iter().any(|(n, _)| n == k)
    }

    /// Whether some pair is `(k, v)`.
    pub fn has_value(&self, k: &[u8], v: &[u8]) -> bool {
        self.list.iter().any(|(n, x)| n == k && x == v)
    }

    /// The value of the first pair named `k`.
    pub fn get(&self, k: &[u8]) -> Option<&[u8]> {
        self.list.iter().find(|(n, _)| n == k).map(|(_, v)| &v[..])
    }

    /// The values of the pairs named `k`, in order.
    pub fn get_all(&self, k: &[u8]) -> Vec<Vec<u8>> {
        self.list.iter().filter(|(n, _)| n == k).map(|(_, v)| v.clone()).collect()
    }

    /// Stable sort by name, comparing UTF-16 code units.
    pub fn sort(&mut self) {
        self.list.sort_by(|a, b| {
            if utf16_less(&a.0, &b.0) {
                core::cmp::Ordering::Less
            } else if utf16_less(&b.0, &a.0) {
                core::cmp::Ordering::Greater
            } else {
                core::cmp::Ordering::Equal
            }
        });
    }

    /// Serializes the list. Verified (`form_serialize_exec` against
    /// `form_serialize`).
    pub fn to_bytes(&self) -> Vec<u8> {
        form_serialize_exec(&self.list)
    }
}
