//! The uniqueness theorems: a message vhttp accepts has one framing under
//! every reading RFC 9112 allows.
//!
//! `rfc.rs` models every RFC 9112 recipient, with a parameter for each
//! choice the RFC leaves open. The theorems say that whenever vhttp
//! accepts a head, every recipient in the model finds the same end of the
//! head and the same body framing (or, for a request with leading empty
//! lines, rejects it if it skips fewer of them). Two compliant parsers can
//! therefore never disagree about where a message vhttp accepts ends,
//! which is what request smuggling needs.
use crate::framing::*;
use crate::rfc::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The model's name for a vhttp framing.
pub open spec fn as_framing(x: Body) -> Framing {
    match x {
        Body::Empty => Framing::Length(0),
        Body::Length(n) => Framing::Length(n as nat),
        Body::Chunked => Framing::Chunked,
        Body::Close => Framing::Close,
    }
}

pub open spec fn field_of(b: Seq<u8>, h: SpecHeader) -> Field {
    Field { name: span_bytes(b, h.name), value: span_bytes(b, h.value) }
}

pub open spec fn fields_view(b: Seq<u8>, hs: Seq<SpecHeader>) -> Seq<Field> {
    hs.map_values(|h: SpecHeader| field_of(b, h))
}

// ---------------------------------------------------------------------------
// Scanning
// ---------------------------------------------------------------------------

proof fn lemma_run(b: Seq<u8>, i: int, k: Cls)
    requires
        0 <= i <= b.len(),
    ensures
        i <= run_end(b, i, k) <= b.len(),
        forall|j: int| i <= j < run_end(b, i, k) ==> in_cls(k, #[trigger] b[j]),
        run_end(b, i, k) < b.len() ==> !in_cls(k, b[run_end(b, i, k)]),
    decreases b.len() - i,
{
    if i < b.len() && in_cls(k, b[i]) {
        lemma_run(b, i + 1, k);
    }
}

pub proof fn lemma_trim_end(b: Seq<u8>, s: int, e: int)
    requires
        0 <= s <= e <= b.len(),
    ensures
        s <= trim_end(b, s, e) <= e,
        forall|j: int| trim_end(b, s, e) <= j < e ==> is_ows(#[trigger] b[j]),
        trim_end(b, s, e) > s ==> !is_ows(b[trim_end(b, s, e) - 1]),
    decreases e - s,
{
    if e > s && is_ows(b[e - 1]) {
        lemma_trim_end(b, s, e - 1);
    }
}

pub proof fn lemma_find(s: Seq<u8>, i: int, j: int, x: u8)
    requires
        0 <= i <= j <= s.len(),
        forall|k: int| i <= k < j ==> #[trigger] s[k] != x,
        j < s.len() ==> s[j] == x,
    ensures
        find(s, i, x) == j,
    decreases j - i,
{
    if i < j {
        lemma_find(s, i + 1, j, x);
    }
}

pub proof fn lemma_ltrim(s: Seq<u8>, a: int)
    requires
        0 <= a <= s.len(),
        forall|k: int| 0 <= k < a ==> is_ows(#[trigger] s[k]),
        a < s.len() ==> !is_ows(s[a]),
    ensures
        ltrim(s) == s.subrange(a, s.len() as int),
    decreases a,
{
    if a == 0 {
        assert(s.subrange(0, s.len() as int) =~= s);
    } else {
        let t = s.drop_first();
        assert forall|k: int| 0 <= k < a - 1 implies is_ows(#[trigger] t[k]) by {
            assert(t[k] == s[k + 1]);
        }
        lemma_ltrim(t, a - 1);
        assert(t.subrange(a - 1, t.len() as int) =~= s.subrange(a, s.len() as int));
    }
}

pub proof fn lemma_rtrim(s: Seq<u8>, e: int)
    requires
        0 <= e <= s.len(),
        forall|k: int| e <= k < s.len() ==> is_ows(#[trigger] s[k]),
        e > 0 ==> !is_ows(s[e - 1]),
    ensures
        rtrim(s) == s.subrange(0, e),
    decreases s.len() - e,
{
    if e == s.len() {
        assert(s.subrange(0, e) =~= s);
    } else {
        let t = s.drop_last();
        assert forall|k: int| e <= k < t.len() implies is_ows(#[trigger] t[k]) by {
            assert(t[k] == s[k]);
        }
        lemma_rtrim(t, e);
        assert(t.subrange(0, e) =~= s.subrange(0, e));
    }
}

/// `trim(s) == s[a..e]` when everything outside `a..e` is OWS and the
/// ends of `a..e` are not.
pub proof fn lemma_trim(s: Seq<u8>, a: int, e: int)
    requires
        0 <= a <= e <= s.len(),
        forall|k: int| 0 <= k < a ==> is_ows(#[trigger] s[k]),
        forall|k: int| e <= k < s.len() ==> is_ows(#[trigger] s[k]),
        a < e ==> !is_ows(s[a]) && !is_ows(s[e - 1]),
        a == e ==> e == s.len(),
    ensures
        trim(s) == s.subrange(a, e),
{
    lemma_ltrim(s, a);
    let t = s.subrange(a, s.len() as int);
    assert forall|k: int| e - a <= k < t.len() implies is_ows(#[trigger] t[k]) by {
        assert(t[k] == s[k + a]);
    }
    lemma_rtrim(t, e - a);
    assert(t.subrange(0, e - a) =~= s.subrange(a, e));
}

// ---------------------------------------------------------------------------
// Lines
// ---------------------------------------------------------------------------

pub proof fn lemma_find_eol(b: Seq<u8>, i: int, e: int, c: Recipient)
    requires
        0 <= i <= e,
        e + 1 < b.len(),
        b[e] == CR,
        b[e + 1] == LF,
        clean(b, i, e),
    ensures
        find_eol(b, i, c) == e + 1,
    decreases e + 1 - i,
{
    if i < e {
        lemma_find_eol(b, i + 1, e, c);
    } else {
        assert(!is_eol(b, e, c));
        assert(is_eol(b, e + 1, c));
        assert(find_eol(b, e + 1, c) == e + 1);
    }
}

/// No CR or LF in `b[i..e]`.
pub open spec fn clean(b: Seq<u8>, i: int, e: int) -> bool {
    forall|k: int| i <= k < e ==> #[trigger] b[k] != LF && b[k] != CR
}

/// A line `b[i..e]` without CR or LF, ended by CRLF, reads as itself under
/// every choice.
pub proof fn lemma_read_clean(b: Seq<u8>, i: int, e: int, c: Recipient)
    requires
        0 <= i <= e,
        e + 1 < b.len(),
        b[e] == CR,
        b[e + 1] == LF,
        clean(b, i, e),
    ensures
        read_line(b, i, c) == Parsed::Done(b.subrange(i, e), e + 2),
{
    lemma_find_eol(b, i, e, c);
    let l = b.subrange(i, e);
    assert(!has_byte(l, CR)) by {
        if has_byte(l, CR) {
            let k = choose|k: int| 0 <= k < l.len() && l[k] == CR;
            assert(b[i + k] == CR);
        }
    }
}

proof fn lemma_crlf(b: Seq<u8>, i: int)
    requires
        0 <= i,
        lit(b, i, crlf()) matches Parsed::Done(_, _),
    ensures
        i + 1 < b.len(),
        b[i] == CR,
        b[i + 1] == LF,
        lit(b, i, crlf()) == Parsed::<()>::Done((), i + 2),
{
    assert(b.subrange(i, i + 2) == crlf().subrange(0, 2));
    assert(b.subrange(i, i + 2)[0] == b[i]);
    assert(b.subrange(i, i + 2)[1] == b[i + 1]);
}

/// A field line vhttp accepts reads as the same field under every choice.
proof fn lemma_header_line(b: Seq<u8>, i: int, c: Recipient)
    requires
        0 <= i <= b.len(),
        parse_header(b, i) matches Parsed::Done(_, _),
    ensures
        ({
            let (h, n) = (parse_header(b, i)->Done_0, parse_header(b, i)->Done_1);
            read_line(b, i, c) matches Parsed::Done(l, n2) && n2 == n && l.len() > 0 && !is_ows(
                l[0],
            ) && field(l, c) == Some(field_of(b, h))
        }),
        parse_header(b, i)->Done_1 > i,
{
    let ne = run_end(b, i, Cls::Token);
    lemma_run(b, i, Cls::Token);
    let v0 = ne + 1;
    let vs = run_end(b, v0, Cls::Ows);
    lemma_run(b, v0, Cls::Ows);
    let e = run_end(b, vs, Cls::Value);
    lemma_run(b, vs, Cls::Value);
    lemma_crlf(b, e);
    let h = parse_header(b, i)->Done_0;
    assert(h.name == SpecSpan { start: i, end: ne });
    assert(h.value == SpecSpan { start: vs, end: trim_end(b, vs, e) });
    assert(b[ne] == COLON);
    assert(clean(b, i, e)) by {
        assert forall|k: int| i <= k < e implies #[trigger] b[k] != LF && b[k] != CR by {
            if k < ne {
                assert(is_tchar(b[k]));
            } else if k == ne {
            } else if k < vs {
                assert(is_ows(b[k]));
            } else {
                assert(is_value_char(b[k]));
            }
        }
    }
    lemma_read_clean(b, i, e, c);
    let l = b.subrange(i, e);
    assert(l[0] == b[i]);
    assert(is_tchar(b[i]));
    // The first colon is the one after the name.
    assert forall|k: int| 0 <= k < ne - i implies #[trigger] l[k] != COLON by {
        assert(l[k] == b[i + k]);
        assert(is_tchar(b[i + k]));
    }
    lemma_find(l, 0, ne - i, COLON);
    assert(l[ne - i - 1] == b[ne - 1]);
    assert(is_tchar(b[ne - 1]));
    let nm = l.subrange(0, ne - i);
    assert(nm.last() == b[ne - 1]);
    lemma_rtrim(nm, nm.len() as int);
    assert(nm.subrange(0, nm.len() as int) =~= nm);
    // The value, trimmed.
    let raw = l.subrange(ne - i + 1, l.len() as int);
    assert(raw =~= b.subrange(v0, e));
    assert forall|k: int| 0 <= k < raw.len() implies #[trigger] raw[k] != 0 by {
        assert(raw[k] == b[v0 + k]);
        if v0 + k < vs {
            assert(is_ows(b[v0 + k]));
        } else {
            assert(is_value_char(b[v0 + k]));
        }
    }
    lemma_find(raw, 0, raw.len() as int, 0);
    assert(raw.subrange(0, raw.len() as int) =~= raw);
    let te = trim_end(b, vs, e);
    lemma_trim_end(b, vs, e);
    assert forall|k: int| 0 <= k < vs - v0 implies is_ows(#[trigger] raw[k]) by {
        assert(raw[k] == b[v0 + k]);
    }
    assert forall|k: int| te - v0 <= k < raw.len() implies is_ows(#[trigger] raw[k]) by {
        assert(raw[k] == b[v0 + k]);
    }
    if vs < te {
        assert(raw[vs - v0] == b[vs]);
        assert(raw[te - v0 - 1] == b[te - 1]);
    } else {
        // All OWS: then the value run is empty.
        if vs < e {
            assert(is_value_char(b[vs]));
            assert(is_ows(b[vs]));
            assert(b[vs] == SP || b[vs] == HTAB);
            assert(false);
        }
    }
    lemma_trim(raw, vs - v0, te - v0);
    let v = trim(raw);
    assert(v =~= b.subrange(vs, te));
    assert(!has_byte(v, 0)) by {
        if has_byte(v, 0) {
            let k = choose|k: int| 0 <= k < v.len() && v[k] == 0;
            assert(v[k] == b[vs + k]);
            assert(is_value_char(b[vs + k]));
        }
    }
    assert(l.subrange(0, ne - i) =~= b.subrange(i, ne));
}

/// The field lines vhttp accepts read as the same lines under every
/// choice, and the head ends at the same place.
proof fn lemma_lines(b: Seq<u8>, i: int, max: nat, c: Recipient)
    requires
        0 <= i <= b.len(),
        parse_headers(b, i, max) matches Parsed::Done(_, _),
    ensures
        ({
            let (hs, end) = (parse_headers(b, i, max)->Done_0, parse_headers(b, i, max)->Done_1);
            read_lines(b, i, c) matches Parsed::Done(ls, e2) && e2 == end && ls.len() == hs.len()
                && forall|k: int|
                0 <= k < ls.len() ==> (#[trigger] ls[k]).len() > 0 && !is_ows(ls[k][0]) && field(
                    ls[k],
                    c,
                ) == Some(field_of(b, hs[k]))
        }),
    decreases b.len() - i,
{
    if b[i] == CR {
        lemma_crlf(b, i);
        lemma_read_clean(b, i, i, c);
        assert(b.subrange(i, i).len() == 0);
    } else {
        lemma_header_line(b, i, c);
        let (h, n) = (parse_header(b, i)->Done_0, parse_header(b, i)->Done_1);
        lemma_lines(b, n, (max - 1) as nat, c);
        let l = read_line(b, i, c)->Done_0;
        let ls2 = read_lines(b, n, c)->Done_0;
        let hs2 = parse_headers(b, n, (max - 1) as nat)->Done_0;
        let ls = seq![l] + ls2;
        let hs = seq![h] + hs2;
        assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] ls[k]).len() > 0 && !is_ows(
            ls[k][0],
        ) && field(ls[k], c) == Some(field_of(b, hs[k])) by {
            if k > 0 {
                assert(ls[k] == ls2[k - 1]);
                assert(hs[k] == hs2[k - 1]);
            }
        }
    }
}

/// Lines that do not start with whitespace unfold to themselves.
proof fn lemma_unfold(ls: Seq<Seq<u8>>, i: int, c: Recipient, acc: Seq<Seq<u8>>)
    requires
        0 <= i <= ls.len(),
        forall|k: int| i <= k < ls.len() ==> (#[trigger] ls[k]).len() > 0 && !is_ows(ls[k][0]),
    ensures
        unfold(ls, i, c, acc) == Some(acc + ls.subrange(i, ls.len() as int)),
    decreases ls.len() - i,
{
    if i == ls.len() {
        assert(acc + ls.subrange(i, i) =~= acc);
    } else {
        assert(ls[i].len() > 0 && !is_ows(ls[i][0]));
        lemma_unfold(ls, i + 1, c, acc.push(ls[i]));
        assert(acc.push(ls[i]) + ls.subrange(i + 1, ls.len() as int) =~= acc + ls.subrange(
            i,
            ls.len() as int,
        ));
    }
}

proof fn lemma_fields(us: Seq<Seq<u8>>, fs: Seq<Field>, c: Recipient)
    requires
        us.len() == fs.len(),
        forall|k: int| 0 <= k < us.len() ==> field(#[trigger] us[k], c) == Some(fs[k]),
    ensures
        fields(us, c) == Some(fs),
    decreases us.len(),
{
    if us.len() > 0 {
        let (u2, f2) = (us.drop_last(), fs.drop_last());
        assert forall|k: int| 0 <= k < u2.len() implies field(#[trigger] u2[k], c) == Some(f2[k]) by {
            assert(u2[k] == us[k]);
        }
        lemma_fields(u2, f2, c);
        assert(field(us.last(), c) == Some(fs[us.len() - 1]));
        assert(f2.push(fs.last()) =~= fs);
    }
}

// ---------------------------------------------------------------------------
// Start lines
// ---------------------------------------------------------------------------

pub proof fn lemma_last_sep(s: Seq<u8>, k: int, j: int, c: Recipient)
    requires
        0 <= j < k <= s.len(),
        is_sep(c, s[j]),
        forall|m: int| j < m < k ==> !is_sep(c, #[trigger] s[m]),
    ensures
        last_sep(s, k, c) == j,
    decreases k,
{
    if k - 1 > j {
        lemma_last_sep(s, k - 1, j, c);
    }
}

proof fn lemma_version(b: Seq<u8>, v: int)
    requires
        0 <= v,
        parse_version(b, v) matches Parsed::Done(_, _),
    ensures
        parse_version(b, v)->Done_1 == v + 8,
        v + 8 <= b.len(),
        version_word(b.subrange(v, v + 8)) == Some(parse_version(b, v)->Done_0),
        forall|k: int| v <= k < v + 8 ==> #[trigger] b[k] != LF && b[k] != CR && b[k] != SP && b[k]
            != HTAB && b[k] != 0x0B && b[k] != 0x0C,
{
    let p = http1_prefix();
    assert(b.subrange(v, v + 7) == p.subrange(0, 7));
    assert(p.subrange(0, 7) =~= p);
    let w = b.subrange(v, v + 8);
    assert(w.subrange(0, 7) =~= b.subrange(v, v + 7));
    assert forall|k: int| v <= k < v + 8 implies #[trigger] b[k] != LF && b[k] != CR && b[k] != SP
        && b[k] != HTAB && b[k] != 0x0B && b[k] != 0x0C by {
        if k < v + 7 {
            assert(b[k] == b.subrange(v, v + 7)[k - v]);
        }
    }
}

/// The request line vhttp accepts: the model reads it as one line with
/// the same version.
proof fn lemma_request_line(b: Seq<u8>, max: nat, c: Recipient)
    requires
        parse_request(b, max) matches Parsed::Done(_, _),
    ensures
        ({
            let s = skip_empty_lines(b, 0)->Done_1;
            let r = parse_request(b, max)->Done_0;
            &&& 0 <= s < b.len()
            &&& read_line(b, s, c) is Done
            &&& read_line(b, s, c)->Done_0.len() > 0
            &&& request_version(read_line(b, s, c)->Done_0, c) == Some(r.minor)
            &&& s < read_line(b, s, c)->Done_1 <= b.len()
            &&& parse_headers(b, read_line(b, s, c)->Done_1, max) == Parsed::Done(
                r.headers,
                parse_request(b, max)->Done_1,
            )
        }),
{
    let s = skip_empty_lines(b, 0)->Done_1;
    lemma_skip_bounds(b, 0);
    let (me, t) = (run_then(b, s, Cls::Token, SP)->Done_0, run_then(b, s, Cls::Token, SP)->Done_1);
    lemma_run(b, s, Cls::Token);
    let (te, v) = (run_then(b, t, Cls::Target, SP)->Done_0, run_then(b, t, Cls::Target, SP)->Done_1);
    lemma_run(b, t, Cls::Target);
    lemma_version(b, v);
    let h = v + 8;
    lemma_crlf(b, h);
    assert(clean(b, s, h)) by {
        assert forall|k: int| s <= k < h implies #[trigger] b[k] != LF && b[k] != CR by {
            if k < me {
                assert(is_tchar(b[k]));
            } else if k == me {
            } else if k < te {
                assert(is_target_char(b[k]));
            } else if k == te {
            }
        }
    }
    lemma_read_clean(b, s, h, c);
    let l = b.subrange(s, h);
    assert(l[0] == b[s]);
    // The version is the last word.
    assert(l.last() == b[h - 1]);
    let tt = if c.ws_start_line {
        rtrim_sep(l, c)
    } else {
        l
    };
    assert(tt == l);
    assert forall|m: int| te - s < m < l.len() implies !is_sep(c, #[trigger] l[m]) by {
        assert(l[m] == b[s + m]);
    }
    assert(l[te - s] == b[te]);
    lemma_last_sep(l, l.len() as int, te - s, c);
    let before = l.subrange(0, te - s);
    assert(before.last() == b[te - 1]);
    assert(is_target_char(b[te - 1]));
    assert(rtrim_sep(before, c) == before);
    assert(l.subrange(te - s + 1, l.len() as int) =~= b.subrange(v, v + 8));
}

pub proof fn lemma_skip_bounds(b: Seq<u8>, i: int)
    requires
        0 <= i,
        skip_empty_lines(b, i) matches Parsed::Done(_, _),
    ensures
        i <= skip_empty_lines(b, i)->Done_1 < b.len(),
        b[skip_empty_lines(b, i)->Done_1] != CR,
    decreases b.len() - i,
{
    if b[i] == CR {
        lemma_skip_bounds(b, i + 2);
    }
}

/// The model skips the same empty lines, or fewer; if fewer, it is left
/// at an empty line.
pub proof fn lemma_skip(b: Seq<u8>, i: int, c: Recipient, k: nat, l: Seq<u8>, n: int)
    requires
        0 <= i,
        skip_empty_lines(b, i) matches Parsed::Done(_, _),
        read_line(b, skip_empty_lines(b, i)->Done_1, c) == Parsed::Done(l, n),
        l.len() > 0,
    ensures
        skip_empty(b, i, c, k) matches Parsed::Done(_, p) && i <= p <= skip_empty_lines(b, i)->Done_1
            && (p < skip_empty_lines(b, i)->Done_1 ==> read_line(b, p, c) == Parsed::Done(
            Seq::<u8>::empty(),
            p + 2,
        )),
    decreases k,
{
    let s = skip_empty_lines(b, i)->Done_1;
    if b[i] == CR {
        lemma_skip_bounds(b, i + 2);
        lemma_read_clean(b, i, i, c);
        assert(b.subrange(i, i) =~= Seq::<u8>::empty());
        if k > 0 {
            lemma_skip(b, i + 2, c, (k - 1) as nat, l, n);
        }
    } else {
        assert(s == i);
    }
}

/// The status line vhttp accepts: the model reads it as one line with the
/// same version and status code.
proof fn lemma_status_line(b: Seq<u8>, max: nat, c: Recipient)
    requires
        parse_response(b, max) matches Parsed::Done(_, _),
    ensures
        ({
            let r = parse_response(b, max)->Done_0;
            let h = parse_status_line(b, 0)->Done_1;
            &&& b.len() > 0 && b[0] != CR
            &&& read_line(b, 0, c) == Parsed::Done(b.subrange(0, h - 2), h)
            &&& h >= 14
            &&& status_line(b.subrange(0, h - 2), c) == Some((r.minor, r.status as nat))
            &&& 0 <= h <= b.len()
            &&& parse_headers(b, h, max) == Parsed::Done(r.headers, parse_response(b, max)->Done_1)
        }),
{
    lemma_version(b, 0);
    let minor = parse_version(b, 0)->Done_0;
    let j = 8int;
    let code = parse_status(b, 9)->Done_0;
    let k = 12int;
    let rs = if k < b.len() && b[k] == SP {
        k + 1
    } else {
        k
    };
    let re = if rs > k {
        run_end(b, rs, Cls::Value)
    } else {
        k
    };
    if rs > k {
        lemma_run(b, rs, Cls::Value);
    }
    lemma_crlf(b, re);
    assert(clean(b, 0, re)) by {
        assert forall|m: int| 0 <= m < re implies #[trigger] b[m] != LF && b[m] != CR by {
            if m >= 13 {
                assert(is_value_char(b[m]));
            } else if m >= 9 && m < 12 {
                assert(is_digit(b[m]));
            }
        }
    }
    lemma_read_clean(b, 0, re, c);
    let l = b.subrange(0, re);
    assert(l[8] == b[8]);
    assert(l.subrange(0, 8) =~= b.subrange(0, 8));
    if c.ws_start_line {
        assert(l[9] == b[9]);
        assert(!is_sep(c, l[9]));
    }
    assert(l[9] == b[9] && l[10] == b[10] && l[11] == b[11]);
    if re > 12 {
        assert(l[12] == b[12]);
    }
    let d = l.subrange(9, 12);
    assert(d.drop_last().drop_last().drop_last() =~= Seq::<u8>::empty());
    assert(d.drop_last().drop_last().last() == b[9]);
    assert(d.drop_last().last() == b[10]);
    assert(d.last() == b[11]);
    let (d1, d2) = (d.drop_last(), d.drop_last().drop_last());
    assert(decimal(d2.drop_last()) == 0);
    assert(decimal(d2) == (b[9] - 0x30) as nat);
    assert(decimal(d1) == decimal(d2) * 10 + (b[10] - 0x30) as nat);
    assert(decimal(d) == decimal(d1) * 10 + (b[11] - 0x30) as nat);
    assert(is_digit(b[9]) && is_digit(b[10]) && is_digit(b[11]));
    assert(code as nat == decimal(d));
}

// ---------------------------------------------------------------------------
// Framing
// ---------------------------------------------------------------------------

proof fn lemma_digits_elements(v: Seq<u8>)
    requires
        all_digits(v),
    ensures
        elements(v, 0) == seq![v],
{
    assert forall|k: int| 0 <= k < v.len() implies #[trigger] v[k] != COMMA by {
        assert(is_digit(v[k]));
    }
    lemma_find(v, 0, v.len() as int, COMMA);
    lemma_trim(v, 0, v.len() as int);
    assert(v.subrange(0, v.len() as int) =~= v);
    assert(seq![v] + Seq::<Seq<u8>>::empty() =~= seq![v]);
}

pub proof fn lemma_decimal_bound(s: Seq<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> is_digit(#[trigger] s[i]),
    ensures
        decimal(s) < pow10(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies is_digit(#[trigger] t[i]) by {
            assert(t[i] == s[i]);
        }
        lemma_decimal_bound(t);
        assert(is_digit(s.last()));
        let d = (s.last() - 0x30) as nat;
        let p = pow10(t.len());
        assert(decimal(t) * 10 + d < p * 10) by (nonlinear_arith)
            requires
                decimal(t) < p,
                d <= 9,
        ;
    }
}

/// The transfer codings vhttp accepts: tokens only, and the last one
/// decides `chunked_last`.
proof fn lemma_te_list(v: Seq<u8>, i: int, st: TeState)
    requires
        0 <= i <= v.len(),
        st.present,
        te_list(v, i, st) matches Some(_),
    ensures
        ({
            let st2 = te_list(v, i, st)->Some_0;
            let es = elements(v, i);
            &&& st2.present
            &&& es.len() == 0 ==> st2.chunked_last == st.chunked_last
            &&& es.len() > 0 ==> st2.chunked_last == ci_eq(es.last(), coding_chunked())
            &&& forall|k: int| i <= k < v.len() ==> #[trigger] v[k] != 0x3B && v[k] != 0x22
        }),
    decreases v.len() - i,
{
    let a = run_end(v, i, Cls::Ows);
    lemma_run(v, i, Cls::Ows);
    if a >= v.len() {
        assert forall|k: int| i <= k < v.len() implies #[trigger] v[k] != COMMA by {
            assert(is_ows(v[k]));
        }
        lemma_find(v, i, v.len() as int, COMMA);
        let s = v.subrange(i, v.len() as int);
        assert forall|k: int| 0 <= k < s.len() implies is_ows(#[trigger] s[k]) by {
            assert(s[k] == v[i + k]);
        }
        lemma_trim(s, s.len() as int, s.len() as int);
        assert forall|k: int| i <= k < v.len() implies #[trigger] v[k] != 0x3B && v[k] != 0x22 by {
            assert(is_ows(v[k]));
        }
    } else if v[a] == COMMA {
        lemma_te_list(v, a + 1, st);
        assert forall|k: int| i <= k < a implies #[trigger] v[k] != COMMA by {
            assert(is_ows(v[k]));
        }
        lemma_find(v, i, a, COMMA);
        let s = v.subrange(i, a);
        assert forall|k: int| 0 <= k < s.len() implies is_ows(#[trigger] s[k]) by {
            assert(s[k] == v[i + k]);
        }
        lemma_trim(s, s.len() as int, s.len() as int);
        assert forall|k: int| i <= k < v.len() implies #[trigger] v[k] != 0x3B && v[k] != 0x22 by {
            if k < a {
                assert(is_ows(v[k]));
            } else if k > a {
                assert(v[k] == v[k]);
            }
        }
    } else {
        let e = run_end(v, a, Cls::Token);
        lemma_run(v, a, Cls::Token);
        let st2 = te_add(st, v.subrange(a, e))->Some_0;
        let f = run_end(v, e, Cls::Ows);
        lemma_run(v, e, Cls::Ows);
        let k = if f >= v.len() {
            v.len() as int
        } else {
            f
        };
        assert forall|m: int| i <= m < k implies #[trigger] v[m] != COMMA by {
            if m < a {
                assert(is_ows(v[m]));
            } else if m < e {
                assert(is_tchar(v[m]));
            } else {
                assert(is_ows(v[m]));
            }
        }
        lemma_find(v, i, k, COMMA);
        let s = v.subrange(i, k);
        assert forall|m: int| 0 <= m < a - i implies is_ows(#[trigger] s[m]) by {
            assert(s[m] == v[i + m]);
        }
        assert forall|m: int| e - i <= m < s.len() implies is_ows(#[trigger] s[m]) by {
            assert(s[m] == v[i + m]);
        }
        assert(s[a - i] == v[a]);
        assert(s[e - i - 1] == v[e - 1]);
        assert(is_tchar(v[a]));
        assert(is_tchar(v[e - 1]));
        lemma_trim(s, a - i, e - i);
        assert(s.subrange(a - i, e - i) =~= v.subrange(a, e));
        if f >= v.len() {
            assert(seq![v.subrange(a, e)] + Seq::<Seq<u8>>::empty() =~= seq![v.subrange(a, e)]);
            assert forall|m: int| i <= m < v.len() implies #[trigger] v[m] != 0x3B && v[m] != 0x22 by {
                if m < a {
                    assert(is_ows(v[m]));
                } else if m < e {
                    assert(is_tchar(v[m]));
                } else {
                    assert(is_ows(v[m]));
                }
            }
        } else {
            lemma_te_list(v, f + 1, st2);
            let rest = elements(v, f + 1);
            let es = seq![v.subrange(a, e)] + rest;
            assert(elements(v, i) == es);
            if rest.len() > 0 {
                assert(es.last() == rest.last());
            } else {
                assert(es.last() == v.subrange(a, e));
            }
            assert forall|m: int| i <= m < v.len() implies #[trigger] v[m] != 0x3B && v[m] != 0x22 by {
                if m < a {
                    assert(is_ows(v[m]));
                } else if m < e {
                    assert(is_tchar(v[m]));
                } else if m < f {
                    assert(is_ows(v[m]));
                }
            }
        }
    }
}

/// Names vhttp accepts compare the same with and without `_` read as `-`.
proof fn lemma_named(b: Seq<u8>, f: Fields, h: SpecHeader, lit: Seq<u8>, c: Recipient)
    requires
        fields_step(b, f, h) is Some,
        lit == name_content_length() || lit == name_transfer_encoding(),
    ensures
        named(field_of(b, h), lit, c) == ci_eq(span_bytes(b, h.name), lit),
{
    let name = span_bytes(b, h.name);
    if ci_eq(name, lit) {
        assert(ci_eq_dash(name, lit));
    }
}

/// What the model sees in the fields of a head vhttp accepts: Content-Length
/// lines that all carry the number vhttp read, and at most one
/// Transfer-Encoding line, with the value vhttp checked.
pub open spec fn agree(fs: Seq<Field>, f: Fields, c: Recipient) -> bool {
    &&& match f.cl {
        None => cl_values(fs, c).len() == 0,
        Some(n) => cl_values(fs, c).len() > 0 && forall|k: int|
            0 <= k < cl_values(fs, c).len() ==> content_length_value(#[trigger] cl_values(fs, c)[k])
                == Some(n),
    }
    &&& if f.te.present {
        te_values(fs, c).len() == 1 && te_list(
            te_values(fs, c)[0],
            0,
            TeState { present: true, chunked_last: false },
        ) == Some(f.te)
    } else {
        te_values(fs, c).len() == 0 && !f.te.chunked_last
    }
}

proof fn lemma_agree(b: Seq<u8>, hs: Seq<SpecHeader>, c: Recipient)
    requires
        fields_of(b, hs) matches Some(_),
    ensures
        agree(fields_view(b, hs), fields_of(b, hs)->Some_0, c),
    decreases hs.len(),
{
    let fs = fields_view(b, hs);
    if hs.len() > 0 {
        let hp = hs.drop_last();
        let fp = fields_view(b, hp);
        assert(fs.drop_last() =~= fp);
        assert(fields_of(b, hp) is Some);
        lemma_agree(b, hp, c);
        let f0 = fields_of(b, hp)->Some_0;
        let x = fs.last();
        assert(x == field_of(b, hs.last()));
        lemma_named(b, f0, hs.last(), name_content_length(), c);
        lemma_named(b, f0, hs.last(), name_transfer_encoding(), c);
        let name = span_bytes(b, hs.last().name);
        let v = x.value;
        let (cp, tp) = (cl_values(fp, c), te_values(fp, c));
        let f1 = fields_of(b, hs)->Some_0;
        assert(fields_of(b, hs) == fields_step(b, f0, hs.last()));
        if ci_eq(name, name_content_length()) {
            assert(!ci_eq(name, name_transfer_encoding()));
            assert(cl_values(fs, c) == cp.push(v));
            assert(te_values(fs, c) == tp);
            assert(f1.te == f0.te);
            assert(f1.cl == content_length_value(v));
            let vs = cp.push(v);
            assert forall|k: int| 0 <= k < vs.len() implies content_length_value(#[trigger] vs[k])
                == f1.cl by {
                if k < cp.len() {
                    assert(vs[k] == cp[k]);
                }
            }
        } else if ci_eq(name, name_transfer_encoding()) {
            assert(te_values(fs, c) == tp.push(v));
            assert(tp.push(v) =~= seq![v]);
            assert(cl_values(fs, c) == cp);
            assert(f1.cl == f0.cl);
            assert(f1.te == te_list(v, 0, TeState { present: true, chunked_last: false })->Some_0);
            assert(f1.te.present) by {
                lemma_te_list(v, 0, TeState { present: true, chunked_last: false });
            }
        } else {
            assert(cl_values(fs, c) == cp);
            assert(te_values(fs, c) == tp);
            assert(f1.cl == f0.cl && f1.te == f0.te);
        }
    }
}

/// A Content-Length value vhttp accepts is the same number to every
/// recipient.
proof fn lemma_cl_number(v: Seq<u8>, n: u64, c: Recipient)
    requires
        content_length_value(v) == Some(n),
    ensures
        all_digits(v),
        cl_number(v, c) == Some(n as nat),
{
    assert(all_digits(v));
    lemma_decimal_bound(v);
    lemma_pow10_mono(v.len(), 19);
    assert(pow10(19) == 10000000000000000000nat) by (compute_only);
}

/// Values that are all digits are lists of one element each.
proof fn lemma_list_digits(vs: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < vs.len() ==> all_digits(#[trigger] vs[k]),
    ensures
        list_all(vs) == vs,
    decreases vs.len(),
{
    if vs.len() > 0 {
        let p = vs.drop_last();
        assert forall|k: int| 0 <= k < p.len() implies all_digits(#[trigger] p[k]) by {
            assert(p[k] == vs[k]);
        }
        lemma_list_digits(p);
        lemma_digits_elements(vs.last());
        assert(p + seq![vs.last()] =~= vs);
    }
}

/// Content-Length lines that all carry `n`: every recipient reads `n`,
/// except one that rejects repeated lines outright.
proof fn lemma_content_length(n: u64, fs: Seq<Field>, c: Recipient)
    requires
        cl_values(fs, c).len() > 0,
        forall|k: int|
            0 <= k < cl_values(fs, c).len() ==> content_length_value(#[trigger] cl_values(fs, c)[k])
                == Some(n),
    ensures
        content_length(fs, c) == if cl_values(fs, c).len() > 1 && !c.cl_list && c.cl_pick == 0 {
            None
        } else {
            Some(Framing::Length(n as nat))
        },
{
    let vs = cl_values(fs, c);
    assert forall|k: int| 0 <= k < vs.len() implies all_digits(#[trigger] vs[k]) && cl_number(
        vs[k],
        c,
    ) == Some(n as nat) by {
        lemma_cl_number(vs[k], n, c);
    }
    lemma_list_digits(vs);
    assert(!exists|i: int| 0 <= i < vs.len() && cl_number(#[trigger] vs[i], c) is None);
}

/// A start line at `s` that the model reads as `l`, then field lines
/// vhttp accepts: the model reads the same head.
proof fn lemma_head_at(b: Seq<u8>, s: int, n: int, max: nat, c: Recipient)
    requires
        0 <= s < n <= b.len(),
        read_line(b, s, c) matches Parsed::Done(l, n2) && n2 == n && l.len() > 0,
        parse_headers(b, n, max) matches Parsed::Done(_, _),
    ensures
        head_at(b, s, c) == Parsed::Done(
            (read_line(b, s, c)->Done_0, fields_view(b, parse_headers(b, n, max)->Done_0)),
            parse_headers(b, n, max)->Done_1,
        ),
{
    let l = read_line(b, s, c)->Done_0;
    let hs = parse_headers(b, n, max)->Done_0;
    lemma_lines(b, n, max, c);
    let ls2 = read_lines(b, n, c)->Done_0;
    let ls = seq![l] + ls2;
    assert(read_lines(b, s, c) == Parsed::Done(ls, parse_headers(b, n, max)->Done_1));
    assert forall|k: int| 1 <= k < ls.len() implies (#[trigger] ls[k]).len() > 0 && !is_ows(
        ls[k][0],
    ) by {
        assert(ls[k] == ls2[k - 1]);
    }
    lemma_unfold(ls, 1, c, Seq::empty());
    assert(Seq::<Seq<u8>>::empty() + ls.subrange(1, ls.len() as int) =~= ls2);
    let fs = fields_view(b, hs);
    assert forall|k: int| 0 <= k < ls2.len() implies field(#[trigger] ls2[k], c) == Some(fs[k]) by {}
    lemma_fields(ls2, fs, c);
}

/// The recipient rejects every repeated Content-Length line (RFC 9112
/// §6.3 allows that), and `fs` has more than one.
pub open spec fn repeated_cl_rejected(fs: Seq<Field>, c: Recipient) -> bool {
    cl_values(fs, c).len() > 1 && !c.cl_list && c.cl_pick == 0
}

/// The model's framing of the fields of a head vhttp accepts.
proof fn lemma_framing(b: Seq<u8>, hs: Seq<SpecHeader>, c: Recipient)
    requires
        fields_of(b, hs) matches Some(_),
    ensures
        ({
            let fs = fields_view(b, hs);
            let f = fields_of(b, hs)->Some_0;
            &&& (te_values(fs, c).len() > 0) == f.te.present
            &&& (cl_values(fs, c).len() > 0) == f.cl is Some
            &&& !te_params(fs, c)
            &&& f.te.chunked_last == (codings(fs, c).len() > 0 && ci_eq(codings(fs, c).last(), coding_chunked()))
            &&& match f.cl {
                Some(n) => content_length(fs, c) == if repeated_cl_rejected(fs, c) {
                    None
                } else {
                    Some(Framing::Length(n as nat))
                },
                None => true,
            }
        }),
{
    let fs = fields_view(b, hs);
    lemma_agree(b, hs, c);
    let f = fields_of(b, hs)->Some_0;
    if let Some(n) = f.cl {
        lemma_content_length(n, fs, c);
    }
    if f.te.present {
        let v = te_values(fs, c)[0];
        let vs = te_values(fs, c);
        assert(vs =~= seq![v]);
        assert(seq![vs[0]] =~= vs);
        assert(seq![vs.last()] =~= vs);
        assert(vs.drop_last() =~= Seq::<Seq<u8>>::empty());
        assert(list_all(vs) == list_all(vs.drop_last()) + elements(v, 0));
        assert(list_all(vs.drop_last()) == Seq::<Seq<u8>>::empty());
        assert(Seq::<Seq<u8>>::empty() + elements(v, 0) =~= elements(v, 0));
        assert(codings(fs, c) == elements(v, 0));
        lemma_te_list(v, 0, TeState { present: true, chunked_last: false });
        assert(!te_params(fs, c)) by {
            if te_params(fs, c) {
                let k = choose|k: int|
                    0 <= k < te_values(fs, c).len() && (has_byte(te_values(fs, c)[k], 0x3B) || has_byte(
                        te_values(fs, c)[k],
                        0x22,
                    ));
                assert(k == 0);
                if has_byte(v, 0x3B) {
                    let m = choose|m: int| 0 <= m < v.len() && v[m] == 0x3B;
                }
                if has_byte(v, 0x22) {
                    let m = choose|m: int| 0 <= m < v.len() && v[m] == 0x22;
                }
            }
        }
        assert(f.te.chunked_last == (codings(fs, c).len() > 0 && ci_eq(codings(fs, c).last(), coding_chunked())));
    } else {
        assert(codings(fs, c) =~= Seq::<Seq<u8>>::empty());
        assert(!te_params(fs, c));
        assert(!f.te.chunked_last);
    }
}

/// **Uniqueness for requests.** If vhttp accepts `b` as a request whose
/// head ends at `end` with body framing `body`, then every recipient the
/// RFC allows reads the same head end and the same framing, or rejects
/// it: a recipient that skips fewer leading empty lines than `b` has, or
/// one that rejects repeated Content-Length lines when `b` repeats one.
pub proof fn theorem_request_unique(b: Seq<u8>, max: nat, c: Recipient)
    requires
        parse_request(b, max) matches Parsed::Done(r, _) && request_body(b, r) is Some,
    ensures
        ({
            let end = parse_request(b, max)->Done_1;
            let body = request_body(b, parse_request(b, max)->Done_0)->Some_0;
            ||| read_request(b, c) == Reading::Accept { head: end, framing: as_framing(body) }
            ||| (read_request(b, c) is Reject && b[0] == CR)
            ||| (read_request(b, c) is Reject && repeated_cl_rejected(
                fields_view(b, parse_request(b, max)->Done_0.headers),
                c,
            ))
        }),
{
    let r = parse_request(b, max)->Done_0;
    lemma_request_line(b, max, c);
    lemma_skip_bounds(b, 0);
    let s = skip_empty_lines(b, 0)->Done_1;
    let (l, n) = (read_line(b, s, c)->Done_0, read_line(b, s, c)->Done_1);
    lemma_skip(b, 0, c, c.empty_lines, l, n);
    let p = skip_empty(b, 0, c, c.empty_lines)->Done_1;
    if p == s {
        lemma_head_at(b, s, n, max, c);
        lemma_framing(b, r.headers, c);
    } else {
        // A recipient that stopped skipping empty lines early.
        assert(read_lines(b, p, c) == Parsed::Done(Seq::<Seq<u8>>::empty(), p + 2));
        assert(b[0] == CR);
    }
}

/// **Uniqueness for requests, without the Host rule.** The same as
/// `theorem_request_unique` for a caller that checks Host itself (Node.js
/// does): the Host rule decides whether a request is accepted, never how
/// it is framed.
pub proof fn theorem_request_unique_framing(b: Seq<u8>, max: nat, c: Recipient)
    requires
        parse_request(b, max) matches Parsed::Done(r, _) && (fields_of(b, r.headers) matches Some(g)
            && request_framing(g, r.minor) is Some),
    ensures
        ({
            let end = parse_request(b, max)->Done_1;
            let r = parse_request(b, max)->Done_0;
            let body = request_framing(fields_of(b, r.headers)->Some_0, r.minor)->Some_0;
            ||| read_request(b, c) == Reading::Accept { head: end, framing: as_framing(body) }
            ||| (read_request(b, c) is Reject && b[0] == CR)
            ||| (read_request(b, c) is Reject && repeated_cl_rejected(fields_view(b, r.headers), c))
        }),
{
    let r = parse_request(b, max)->Done_0;
    lemma_request_line(b, max, c);
    lemma_skip_bounds(b, 0);
    let s = skip_empty_lines(b, 0)->Done_1;
    let (l, n) = (read_line(b, s, c)->Done_0, read_line(b, s, c)->Done_1);
    lemma_skip(b, 0, c, c.empty_lines, l, n);
    let p = skip_empty(b, 0, c, c.empty_lines)->Done_1;
    if p == s {
        lemma_head_at(b, s, n, max, c);
        lemma_framing(b, r.headers, c);
    } else {
        assert(read_lines(b, p, c) == Parsed::Done(Seq::<Seq<u8>>::empty(), p + 2));
        assert(b[0] == CR);
    }
}

/// **Uniqueness for responses.** If vhttp accepts `b` as a response
/// (to a HEAD request if `head_req`, to CONNECT if `connect`), every
/// recipient the RFC allows reads the same head end and the same framing,
/// or rejects it for repeating Content-Length.
pub proof fn theorem_response_unique(b: Seq<u8>, max: nat, head_req: bool, connect: bool, c: Recipient)
    requires
        parse_response(b, max) matches Parsed::Done(r, _) && response_body(b, r, head_req, connect) is Some,
    ensures
        ({
            let r = parse_response(b, max)->Done_0;
            ||| read_response(b, head_req, connect, c) == (Reading::Accept {
                head: parse_response(b, max)->Done_1,
                framing: as_framing(response_body(b, r, head_req, connect)->Some_0),
            })
            ||| (read_response(b, head_req, connect, c) is Reject && repeated_cl_rejected(
                fields_view(b, r.headers),
                c,
            ))
        }),
{
    let r = parse_response(b, max)->Done_0;
    lemma_status_line(b, max, c);
    let h = read_line(b, 0, c)->Done_1;
    // No empty lines to skip.
    assert(skip_empty(b, 0, c, c.empty_lines) == Parsed::Done((), 0));
    lemma_head_at(b, 0, h, max, c);
    lemma_framing(b, r.headers, c);
}

} // verus!
