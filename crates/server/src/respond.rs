//! Verified HTTP/1.1 response heads.
//!
//! [`write_head`] appends a status line, the handler's field lines and the
//! framing field line the server chooses, then the empty line. The theorem
//! [`theorem_head_parses`] says what those bytes mean to a client: parsed by
//! verilith-http's specification of a response head (`spec::parse_response`,
//! the same rules its uniqueness theorems are stated over), they give back
//! exactly the status, reason, and field lines that were written, in order,
//! and the framing the server chose. Since a field name must be a token and
//! a value must not contain CR, LF or NUL ([`name_ok`], [`value_ok`]), no
//! handler can add a field line, end the head early, or change the framing
//! (response splitting): [`check_name`] and [`check_value`] refuse such
//! input, and only checked input reaches [`write_head`].
use vstd::prelude::*;
use verilith_http::spec as hs;
#[cfg(verus_only)]
use verilith_core::num::is_digit;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// A field name a handler may send: a token, and not Content-Length or
/// Transfer-Encoding under any spelling a recipient might read as one
/// (the server writes the framing itself).
pub open spec fn name_ok(n: Seq<u8>) -> bool {
    &&& n.len() > 0
    &&& forall|i: int| 0 <= i < n.len() ==> hs::is_tchar(#[trigger] n[i])
    &&& !hs::ci_eq_dash(n, hs::name_content_length())
    &&& !hs::ci_eq_dash(n, hs::name_transfer_encoding())
}

/// A field value a handler may send: `field-value` (RFC 9110 §5.5) without
/// leading or trailing whitespace. HTAB, SP, VCHAR and obs-text; never CR,
/// LF, NUL or DEL.
pub open spec fn value_ok(v: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> hs::is_value_char(#[trigger] v[i])
    &&& v.len() > 0 ==> !hs::is_ows(v[0]) && !hs::is_ows(v.last())
}

/// A reason phrase: `*( HTAB / SP / VCHAR / obs-text )`.
pub open spec fn reason_ok(r: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < r.len() ==> hs::is_value_char(#[trigger] r[i])
}

pub open spec fn status_ok(s: u16) -> bool {
    100 <= s <= 999
}

/// Field lines as byte strings.
pub type SField = (Seq<u8>, Seq<u8>);

pub open spec fn fields_ok(fs: Seq<SField>) -> bool {
    forall|i: int| 0 <= i < fs.len() ==> name_ok(#[trigger] fs[i].0) && value_ok(fs[i].1)
}

/// How the body of a response is delimited, as the server writes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framing {
    /// `Content-Length: n`.
    Length(u64),
    /// `Transfer-Encoding: chunked`.
    Chunked,
    /// No framing field: a response with no body (1xx, 204), or one
    /// delimited by closing the connection.
    Neither,
}

/// Largest Content-Length that `spec::content_length_value` reads (19
/// digits).
pub const MAX_LENGTH: u64 = 9_999_999_999_999_999_999;

pub open spec fn framing_ok(f: Framing) -> bool {
    match f {
        Framing::Length(n) => n <= MAX_LENGTH,
        _ => true,
    }
}

/// The decimal digits of `n`, most significant first, no leading zeros.
pub open spec fn dec(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u8]
    } else {
        dec(n / 10).push((0x30 + n % 10) as u8)
    }
}

pub open spec fn crlf() -> Seq<u8> {
    seq![hs::CR, hs::LF]
}

/// `name ": " value CRLF`
pub open spec fn line(f: SField) -> Seq<u8> {
    f.0 + seq![hs::COLON, hs::SP] + f.1 + crlf()
}

pub open spec fn lines(fs: Seq<SField>) -> Seq<u8>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        line(fs[0]) + lines(fs.drop_first())
    }
}

/// "Content-Length" as the server writes it.
pub open spec fn cl_name() -> Seq<u8> {
    seq![0x43u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x4c, 0x65, 0x6e, 0x67, 0x74, 0x68]
}

/// "Transfer-Encoding" as the server writes it.
pub open spec fn te_name() -> Seq<u8> {
    seq![
        0x54u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x45, 0x6e, 0x63, 0x6f, 0x64, 0x69,
        0x6e, 0x67,
    ]
}

/// The field lines on the wire: the handler's, then the framing field.
pub open spec fn all_fields(fs: Seq<SField>, f: Framing) -> Seq<SField> {
    match f {
        Framing::Length(n) => fs.push((cl_name(), dec(n as nat))),
        Framing::Chunked => fs.push((te_name(), hs::coding_chunked())),
        Framing::Neither => fs,
    }
}

/// `"HTTP/1.1 "`
pub open spec fn version_sp() -> Seq<u8> {
    hs::http1_prefix() + seq![0x31u8, hs::SP]
}

pub open spec fn status3(s: u16) -> Seq<u8> {
    seq![(0x30 + s / 100) as u8, (0x30 + (s / 10) % 10) as u8, (0x30 + s % 10) as u8]
}

/// The response head [`write_head`] writes.
pub open spec fn head(status: u16, reason: Seq<u8>, fs: Seq<SField>, f: Framing) -> Seq<u8> {
    status_line(status, reason) + lines(all_fields(fs, f)) + crlf()
}

/// What a recipient's framing fields say, per framing.
pub open spec fn cl_of(f: Framing) -> Option<u64> {
    match f {
        Framing::Length(n) => Some(n),
        _ => None,
    }
}

pub open spec fn te_of(f: Framing) -> hs::TeState {
    match f {
        Framing::Chunked => hs::TeState { present: true, chunked_last: true },
        _ => hs::TeState { present: false, chunked_last: false },
    }
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

/// A response head written by [`write_head`], followed by anything at all
/// (the body, the next response), parses under verilith-http's spec to
/// exactly what was written, and its framing fields say exactly `f`.
pub proof fn theorem_head_parses(
    status: u16,
    reason: Seq<u8>,
    fs: Seq<SField>,
    f: Framing,
    rest: Seq<u8>,
    max: nat,
)
    requires
        status_ok(status),
        reason_ok(reason),
        fields_ok(fs),
        framing_ok(f),
        all_fields(fs, f).len() <= max,
    ensures
        ({
            let h = head(status, reason, fs, f);
            let b = h + rest;
            let all = all_fields(fs, f);
            match hs::parse_response(b, max) {
                hs::Parsed::Done(r, end) => {
                    &&& end == h.len()
                    &&& r.minor == 1
                    &&& r.status == status
                    &&& hs::span_bytes(b, r.reason) == reason
                    &&& r.headers.len() == all.len()
                    &&& forall|i: int|
                        0 <= i < all.len() ==> hs::span_bytes(b, #[trigger] r.headers[i].name)
                            == all[i].0 && hs::span_bytes(b, r.headers[i].value) == all[i].1
                    &&& hs::fields_of(b, r.headers) matches Some(fl) && fl.cl == cl_of(f) && fl.te
                        == te_of(f)
                },
                _ => false,
            }
        }),
{
    let h = head(status, reason, fs, f);
    let b = h + rest;
    let all = all_fields(fs, f);
    lemma_all_fields_ok(fs, f);
    let pre = status_line(status, reason);
    assert(h =~= pre + lines(all) + crlf());
    assert(b =~= pre + (lines(all) + crlf() + rest));
    lemma_status_line(status, reason, lines(all) + crlf() + rest);
    assert(b.subrange(pre.len() as int, b.len() as int) =~= lines(all) + (crlf() + rest));
    lemma_parse_lines(b, pre.len() as int, all, crlf() + rest, max);
    match hs::parse_headers(b, pre.len() as int, max) {
        hs::Parsed::Done(hdrs, end) => {
            assert(end == h.len());
            lemma_fields_of(b, hdrs, fs, f);
        },
        _ => {},
    }
}

/// `"HTTP/1.1 " status " " reason CRLF`
pub open spec fn status_line(status: u16, reason: Seq<u8>) -> Seq<u8> {
    version_sp() + status3(status) + seq![hs::SP] + reason + crlf()
}

proof fn lemma_status_line(status: u16, reason: Seq<u8>, rest: Seq<u8>)
    requires
        status_ok(status),
        reason_ok(reason),
    ensures
        ({
            let pre = status_line(status, reason);
            let b = pre + rest;
            hs::parse_status_line(b, 0) == hs::Parsed::Done(
                (1u8, status, hs::SpecSpan { start: 13, end: 13 + reason.len() as int }),
                pre.len() as int,
            ) && hs::span_bytes(b, hs::SpecSpan { start: 13, end: 13 + reason.len() as int }) == reason
        }),
{
    let pre = status_line(status, reason);
    let b = pre + rest;
    let p7 = hs::http1_prefix();
    assert(b.subrange(0, 7) =~= p7) by {
        assert forall|i: int| 0 <= i < 7 implies b[i] == p7[i] by {
            assert(b[i] == pre[i]);
        }
    }
    lemma_lit_done(b, 0, p7);
    assert(b[7] == 0x31u8);
    assert(hs::parse_version(b, 0) == hs::Parsed::Done(1u8, 8));
    assert(b[8] == hs::SP);
    let st = status3(status);
    assert(b[9] == st[0] && b[10] == st[1] && b[11] == st[2]);
    assert(b[9] == (0x30 + status / 100) as u8);
    assert(b[10] == (0x30 + (status / 10) % 10) as u8);
    assert(b[11] == (0x30 + status % 10) as u8);
    assert(is_digit(b[9]) && is_digit(b[10]) && is_digit(b[11]));
    let (d0, d1, d2) = (b[9], b[10], b[11]);
    assert(((d0 - 0x30) * 100 + (d1 - 0x30) * 10 + (d2 - 0x30)) == status) by (nonlinear_arith)
        requires
            d0 == (0x30 + status / 100) as u8,
            d1 == (0x30 + (status / 10) % 10) as u8,
            d2 == (0x30 + status % 10) as u8,
            100 <= status <= 999,
    ;
    assert(hs::parse_status(b, 9) == hs::Parsed::Done(status, 12));
    assert(b[12] == hs::SP);
    let rs: int = 13;
    let re: int = 13 + reason.len() as int;
    assert forall|i: int| rs <= i < re implies hs::in_cls(hs::Cls::Value, #[trigger] b[i]) by {
        assert(b[i] == reason[i - 13]);
    }
    assert(b[re] == hs::CR);
    assert(b[re + 1] == hs::LF);
    lemma_run_end_exact(b, rs, re, hs::Cls::Value);
    assert(b.subrange(re, re + 2) =~= crlf());
    lemma_lit_done(b, re, crlf());
    assert(hs::span_bytes(b, hs::SpecSpan { start: rs, end: re }) =~= reason) by {
        assert forall|i: int| 0 <= i < reason.len() implies #[trigger] b.subrange(rs, re)[i]
            == reason[i] by {
            assert(b[rs + i] == pre[rs + i]);
        }
    }
}

/// The framing field line is a well-formed field line too.
proof fn lemma_all_fields_ok(fs: Seq<SField>, f: Framing)
    requires
        fields_ok(fs),
        framing_ok(f),
    ensures
        forall|i: int|
            0 <= i < all_fields(fs, f).len() ==> line_ok(#[trigger] all_fields(fs, f)[i]),
{
    let all = all_fields(fs, f);
    assert forall|i: int| 0 <= i < all.len() implies line_ok(#[trigger] all[i]) by {
        if i < fs.len() {
            assert(all[i] == fs[i]);
            assert(name_ok(fs[i].0));
        } else {
            match f {
                Framing::Length(n) => {
                    lemma_dec_digits(n as nat);
                    let d = dec(n as nat);
                    assert(cl_name()[0] == 0x43u8);
                    assert forall|j: int| 0 <= j < cl_name().len() implies hs::is_tchar(
                        #[trigger] cl_name()[j],
                    ) by {}
                    assert forall|j: int| 0 <= j < d.len() implies hs::is_value_char(
                        #[trigger] d[j],
                    ) by {
                        assert(is_digit(d[j]));
                    }
                    assert(!hs::is_ows(d[0]) && !hs::is_ows(d.last())) by {
                        assert(is_digit(d[0]));
                        assert(is_digit(d[d.len() - 1]));
                    }
                },
                Framing::Chunked => {
                    assert forall|j: int| 0 <= j < te_name().len() implies hs::is_tchar(
                        #[trigger] te_name()[j],
                    ) by {}
                    let c = hs::coding_chunked();
                    assert forall|j: int| 0 <= j < c.len() implies hs::is_value_char(
                        #[trigger] c[j],
                    ) by {}
                },
                Framing::Neither => {},
            }
        }
    }
}

/// What the parse lemma needs of a line: a token name, and a value of value
/// characters with no whitespace at either end.
pub open spec fn line_ok(f: SField) -> bool {
    &&& f.0.len() > 0
    &&& forall|i: int| 0 <= i < f.0.len() ==> hs::is_tchar(#[trigger] f.0[i])
    &&& value_ok(f.1)
}

/// `dec(n)` is all digits, nonempty, and at most 19 long below 10^19, and
/// reads back as `n`.
pub proof fn lemma_dec_digits(n: nat)
    ensures
        dec(n).len() >= 1,
        forall|i: int| 0 <= i < dec(n).len() ==> is_digit(#[trigger] dec(n)[i]),
        hs::decimal(dec(n)) == n,
        n <= MAX_LENGTH ==> dec(n).len() <= 19,
    decreases n,
{
    if n < 10 {
        assert(dec(n).drop_last() =~= Seq::<u8>::empty());
        assert(hs::decimal(Seq::<u8>::empty()) == 0);
    } else {
        lemma_dec_digits(n / 10);
        let d = dec(n / 10);
        assert(dec(n).drop_last() =~= d);
        assert forall|i: int| 0 <= i < dec(n).len() implies is_digit(#[trigger] dec(n)[i]) by {
            if i < d.len() {
                assert(dec(n)[i] == d[i]);
            }
        }
        assert(hs::decimal(dec(n)) == hs::decimal(d) * 10 + n % 10);
        assert(n == (n / 10) * 10 + n % 10);
        if n <= MAX_LENGTH {
            lemma_dec_len(n);
        }
    }
}

proof fn lemma_dec_len_k(n: nat, k: nat)
    requires
        n < pow10(k),
        k >= 1,
    ensures
        dec(n).len() <= k,
    decreases n,
{
    if n >= 10 {
        if k == 1 {
            assert(pow10(1) == 10 * pow10(0));
            assert(false);
        } else {
            let k1 = (k - 1) as nat;
            assert(pow10(k) == 10 * pow10(k1));
            assert(n / 10 < pow10(k1)) by (nonlinear_arith)
                requires
                    n < 10 * pow10(k1),
            ;
            lemma_dec_len_k(n / 10, k1);
        }
    }
}

proof fn lemma_dec_len(n: nat)
    requires
        n <= MAX_LENGTH,
    ensures
        dec(n).len() <= 19,
{
    assert(pow10(19) == 10_000_000_000_000_000_000) by (compute);
    lemma_dec_len_k(n, 19);
}

pub open spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        10 * pow10((k - 1) as nat)
    }
}

/// A run of class `k` from `i` to just before `j`, ended by a byte not in
/// `k`, has `run_end` at `j`.
pub proof fn lemma_run_end_exact(b: Seq<u8>, i: int, j: int, k: hs::Cls)
    requires
        0 <= i <= j < b.len(),
        forall|m: int| i <= m < j ==> hs::in_cls(k, #[trigger] b[m]),
        !hs::in_cls(k, b[j]),
    ensures
        hs::run_end(b, i, k) == j,
    decreases j - i,
{
    if i < j {
        lemma_run_end_exact(b, i + 1, j, k);
    }
}

pub proof fn lemma_lit_done(b: Seq<u8>, i: int, s: Seq<u8>)
    requires
        0 <= i,
        i + s.len() <= b.len(),
        b.subrange(i, i + s.len()) == s,
    ensures
        hs::lit(b, i, s) == hs::Parsed::<()>::Done((), i + s.len()),
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

/// One field line at `i` parses to its name and value.
proof fn lemma_parse_line(b: Seq<u8>, i: int, fl: SField, rest: Seq<u8>)
    requires
        0 <= i <= b.len(),
        line_ok(fl),
        b.subrange(i, b.len() as int) == line(fl) + rest,
    ensures
        hs::parse_header(b, i) == hs::Parsed::Done(
            hs::SpecHeader {
                name: hs::SpecSpan { start: i, end: i + fl.0.len() },
                value: hs::SpecSpan {
                    start: i + fl.0.len() + 2,
                    end: i + fl.0.len() + 2 + fl.1.len(),
                },
            },
            i + line(fl).len(),
        ),
{
    let (n, v) = fl;
    let ln = line(fl);
    let ne = i + n.len();
    let vs = ne + 2;
    let ve = vs + v.len();
    assert(ln.len() == n.len() + 2 + v.len() + 2);
    assert(b.subrange(i, b.len() as int).len() == b.len() - i);
    assert(b.len() == i + ln.len() + rest.len());
    assert forall|m: int| 0 <= m < ln.len() implies #[trigger] b[i + m] == ln[m] by {
        assert(b.subrange(i, b.len() as int)[m] == b[i + m]);
        assert((ln + rest)[m] == ln[m]);
    }
    assert forall|m: int| i <= m < ne implies hs::in_cls(hs::Cls::Token, #[trigger] b[m]) by {
        assert(b[i + (m - i)] == ln[m - i]);
        assert(ln[m - i] == n[m - i]);
    }
    assert(b[i + n.len()] == ln[n.len() as int]);
    assert(b[ne] == hs::COLON);
    lemma_run_end_exact(b, i, ne, hs::Cls::Token);
    assert(hs::run_then(b, i, hs::Cls::Token, hs::COLON) == hs::Parsed::Done(ne, ne + 1));
    assert(b[i + (n.len() + 1)] == ln[n.len() + 1 as int]);
    assert(b[ne + 1] == hs::SP);
    // The value starts right after ": ": its first byte (or the CR) is not OWS.
    assert(b[vs] == (if v.len() > 0 { v[0] } else { hs::CR })) by {
        assert(b[i + (n.len() + 2)] == ln[n.len() + 2 as int]);
    }
    assert forall|m: int| ne + 1 <= m < vs implies hs::in_cls(hs::Cls::Ows, #[trigger] b[m]) by {
        assert(m == ne + 1);
    }
    lemma_run_end_exact(b, ne + 1, vs, hs::Cls::Ows);
    assert forall|m: int| vs <= m < ve implies hs::in_cls(hs::Cls::Value, #[trigger] b[m]) by {
        assert(b[i + (m - i)] == ln[m - i]);
        assert(ln[m - i] == v[m - vs]);
    }
    assert(b[ve] == hs::CR) by {
        assert(b[i + (ve - i)] == ln[ve - i]);
    }
    assert(b[ve + 1] == hs::LF) by {
        assert(b[i + (ve + 1 - i)] == ln[ve + 1 - i]);
    }
    lemma_run_end_exact(b, vs, ve, hs::Cls::Value);
    if v.len() > 0 {
        assert(b[ve - 1] == v.last()) by {
            assert(b[i + (ve - 1 - i)] == ln[ve - 1 - i]);
        }
    }
    assert(hs::trim_end(b, vs, ve) == ve);
    assert(b.subrange(ve, ve + 2) =~= crlf());
    lemma_lit_done(b, ve, crlf());
}

/// The field lines, then CRLF, parse to their spans, in order.
proof fn lemma_parse_lines(b: Seq<u8>, i: int, fs: Seq<SField>, rest: Seq<u8>, max: nat)
    requires
        0 <= i <= b.len(),
        forall|k: int| 0 <= k < fs.len() ==> line_ok(#[trigger] fs[k]),
        b.subrange(i, b.len() as int) == lines(fs) + rest,
        rest.len() >= 2,
        rest[0] == hs::CR,
        rest[1] == hs::LF,
        fs.len() <= max,
    ensures
        match hs::parse_headers(b, i, max) {
            hs::Parsed::Done(hdrs, end) => {
                &&& end == i + lines(fs).len() + 2
                &&& hdrs.len() == fs.len()
                &&& forall|k: int|
                    0 <= k < fs.len() ==> hs::span_bytes(b, #[trigger] hdrs[k].name) == fs[k].0
                        && hs::span_bytes(b, hdrs[k].value) == fs[k].1
            },
            _ => false,
        },
    decreases fs.len(),
{
    assert(b.subrange(i, b.len() as int).len() == b.len() - i);
    assert(b.len() == i + lines(fs).len() + rest.len());
    if fs.len() == 0 {
        assert(lines(fs) =~= Seq::<u8>::empty());
        assert(b[i] == rest[0]) by {
            assert(b.subrange(i, b.len() as int)[0] == b[i]);
        }
        assert(b[i + 1] == rest[1]) by {
            assert(b.subrange(i, b.len() as int)[1] == b[i + 1]);
        }
        assert(b.subrange(i, i + 2) =~= crlf());
        lemma_lit_done(b, i, crlf());
    } else {
        let fl = fs[0];
        let tail = fs.drop_first();
        let ln = line(fl);
        assert(lines(fs) == ln + lines(tail));
        assert(b.subrange(i, b.len() as int) =~= ln + (lines(tail) + rest));
        lemma_parse_line(b, i, fl, lines(tail) + rest);
        let n = i + ln.len();
        assert(b.subrange(n, b.len() as int) =~= lines(tail) + rest) by {
            assert forall|m: int| 0 <= m < b.len() - n implies b.subrange(n, b.len() as int)[m] == (
            lines(tail) + rest)[m] by {
                assert(b.subrange(i, b.len() as int)[ln.len() + m] == b[n + m]);
            }
        }
        // The first byte of a line is a name byte, not CR.
        assert(b[i] == fl.0[0]) by {
            assert(b.subrange(i, b.len() as int)[0] == b[i]);
        }
        assert(hs::is_tchar(fl.0[0]));
        assert forall|k: int| 0 <= k < tail.len() implies line_ok(#[trigger] tail[k]) by {
            assert(tail[k] == fs[k + 1]);
        }
        lemma_parse_lines(b, n, tail, rest, (max - 1) as nat);
        let h = hs::SpecHeader {
            name: hs::SpecSpan { start: i, end: i + fl.0.len() },
            value: hs::SpecSpan { start: i + fl.0.len() + 2, end: i + fl.0.len() + 2 + fl.1.len() },
        };
        assert(hs::span_bytes(b, h.name) =~= fl.0) by {
            assert forall|m: int| 0 <= m < fl.0.len() implies b.subrange(i, i + fl.0.len())[m]
                == fl.0[m] by {
                assert(b.subrange(i, b.len() as int)[m] == b[i + m]);
                assert(ln[m] == fl.0[m]);
            }
        }
        assert(hs::span_bytes(b, h.value) =~= fl.1) by {
            let vs = i + fl.0.len() + 2;
            assert forall|m: int| 0 <= m < fl.1.len() implies b.subrange(
                vs,
                vs + fl.1.len(),
            )[m] == fl.1[m] by {
                assert(b.subrange(i, b.len() as int)[fl.0.len() + 2 + m] == b[vs + m]);
                assert(ln[fl.0.len() + 2 + m] == fl.1[m]);
            }
        }
        match hs::parse_headers(b, n, (max - 1) as nat) {
            hs::Parsed::Done(hd, e) => {
                let all = seq![h] + hd;
                assert forall|k: int| 0 <= k < fs.len() implies hs::span_bytes(
                    b,
                    #[trigger] all[k].name,
                ) == fs[k].0 && hs::span_bytes(b, all[k].value) == fs[k].1 by {
                    if k > 0 {
                        assert(all[k] == hd[k - 1]);
                        assert(fs[k] == tail[k - 1]);
                    }
                }
            },
            _ => {},
        }
    }
}

/// The framing analysis of the parsed field lines: the handler's lines
/// change neither Content-Length nor Transfer-Encoding, and the server's
/// last line sets exactly the one it means.
proof fn lemma_fields_of(b: Seq<u8>, hdrs: Seq<hs::SpecHeader>, fs: Seq<SField>, f: Framing)
    requires
        fields_ok(fs),
        framing_ok(f),
        hdrs.len() == all_fields(fs, f).len(),
        forall|k: int|
            0 <= k < hdrs.len() ==> hs::span_bytes(b, #[trigger] hdrs[k].name) == all_fields(
                fs,
                f,
            )[k].0 && hs::span_bytes(b, hdrs[k].value) == all_fields(fs, f)[k].1,
    ensures
        hs::fields_of(b, hdrs) matches Some(fl) && fl.cl == cl_of(f) && fl.te == te_of(f),
{
    let nf = fs.len() as int;
    // The handler's lines.
    assert forall|k: int| 0 <= k <= nf implies (hs::fields_of(b, #[trigger] hdrs.take(k)) matches Some(
        fl,
    ) && fl.cl is None && fl.te == te_of(Framing::Neither)) by {
        lemma_fields_prefix(b, hdrs, fs, f, k);
    }
    match f {
        Framing::Neither => {
            assert(hdrs.take(nf) =~= hdrs);
        },
        Framing::Length(n) => {
            assert(hdrs.take(nf + 1) =~= hdrs);
            assert(hdrs.drop_last() =~= hdrs.take(nf));
            let h = hdrs.last();
            assert(hs::span_bytes(b, h.name) == cl_name());
            assert(hs::span_bytes(b, h.value) == dec(n as nat));
            assert(hs::ci_eq(cl_name(), hs::name_content_length()));
            lemma_dec_digits(n as nat);
            assert(hs::content_length_value(dec(n as nat)) == Some(n));
        },
        Framing::Chunked => {
            assert(hdrs.take(nf + 1) =~= hdrs);
            assert(hdrs.drop_last() =~= hdrs.take(nf));
            let h = hdrs.last();
            assert(hs::span_bytes(b, h.name) == te_name());
            let c = hs::coding_chunked();
            assert(hs::span_bytes(b, h.value) == c);
            assert(!hs::ci_eq(te_name(), hs::name_content_length()));
            assert(hs::ci_eq(te_name(), hs::name_transfer_encoding()));
            lemma_te_chunked();
        },
    }
}

proof fn lemma_te_chunked()
    ensures
        hs::te_list(
            hs::coding_chunked(),
            0,
            hs::TeState { present: true, chunked_last: false },
        ) == Some(hs::TeState { present: true, chunked_last: true }),
{
    let c = hs::coding_chunked();
    let st = hs::TeState { present: true, chunked_last: false };
    assert(!hs::is_ows(c[0]));
    assert(hs::run_end(c, 0, hs::Cls::Ows) == 0);
    assert forall|m: int| 0 <= m < 7 implies hs::in_cls(hs::Cls::Token, #[trigger] c[m]) by {}
    lemma_run_end_tail(c, 0, hs::Cls::Token);
    assert(hs::run_end(c, 0, hs::Cls::Token) == 7);
    assert(c.subrange(0, 7) =~= c);
    assert(hs::ci_eq(c, c));
    assert(hs::run_end(c, 7, hs::Cls::Ows) == 7);
}

/// A run of class `k` from `i` to the end of `b`.
proof fn lemma_run_end_tail(b: Seq<u8>, i: int, k: hs::Cls)
    requires
        0 <= i <= b.len(),
        forall|m: int| i <= m < b.len() ==> hs::in_cls(k, #[trigger] b[m]),
    ensures
        hs::run_end(b, i, k) == b.len(),
    decreases b.len() - i,
{
    if i < b.len() {
        lemma_run_end_tail(b, i + 1, k);
    }
}

proof fn lemma_fields_prefix(
    b: Seq<u8>,
    hdrs: Seq<hs::SpecHeader>,
    fs: Seq<SField>,
    f: Framing,
    k: int,
)
    requires
        fields_ok(fs),
        0 <= k <= fs.len(),
        hdrs.len() == all_fields(fs, f).len(),
        forall|j: int|
            0 <= j < hdrs.len() ==> hs::span_bytes(b, #[trigger] hdrs[j].name) == all_fields(
                fs,
                f,
            )[j].0,
    ensures
        hs::fields_of(b, hdrs.take(k)) matches Some(fl) && fl.cl is None && fl.te == te_of(
            Framing::Neither,
        ),
    decreases k,
{
    let p = hdrs.take(k);
    if k > 0 {
        lemma_fields_prefix(b, hdrs, fs, f, k - 1);
        assert(p.drop_last() =~= hdrs.take(k - 1));
        let h = p.last();
        assert(h == hdrs[k - 1]);
        assert(all_fields(fs, f)[k - 1] == fs[k - 1]);
        let name = hs::span_bytes(b, h.name);
        assert(name == fs[k - 1].0);
        assert(name_ok(fs[k - 1].0));
        lemma_ci_eq_dash(name, hs::name_content_length());
        lemma_ci_eq_dash(name, hs::name_transfer_encoding());
    } else {
        assert(p =~= Seq::<hs::SpecHeader>::empty());
    }
}

proof fn lemma_ci_eq_dash(s: Seq<u8>, lit: Seq<u8>)
    ensures
        hs::ci_eq(s, lit) ==> hs::ci_eq_dash(s, lit),
{
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

/// A field line, as the handler gives it.
#[derive(Clone, Copy, Debug)]
pub struct Field<'a> {
    pub name: &'a [u8],
    pub value: &'a [u8],
}

pub open spec fn field_view(f: Field) -> SField {
    (f.name@, f.value@)
}

pub open spec fn fields_view(fs: Seq<Field>) -> Seq<SField> {
    fs.map_values(|f: Field| field_view(f))
}

#[inline]
pub fn tchar(c: u8) -> (r: bool)
    ensures
        r == hs::is_tchar(c),
{
    (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x5A) || (c >= 0x61 && c <= 0x7A) || c == 0x21
        || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27 || c == 0x2A || c == 0x2B
        || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F || c == 0x60 || c == 0x7C || c == 0x7E
}

#[inline]
fn lower(c: u8) -> (r: u8)
    ensures
        r == hs::lower(c),
{
    if c >= 0x41 && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

/// `ci_eq_dash(n, lit)`, for `lit` given as a slice.
fn eq_dash(n: &[u8], lit: &[u8]) -> (r: bool)
    ensures
        r == hs::ci_eq_dash(n@, lit@),
{
    if n.len() != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < n.len()
        invariant
            n.len() == lit.len(),
            0 <= i <= n.len(),
            forall|j: int|
                0 <= j < i ==> hs::lower(#[trigger] n@[j]) == lit@[j] || (n@[j] == 0x5F && lit@[j]
                    == 0x2D),
        decreases n.len() - i,
    {
        let c = n[i];
        if !(lower(c) == lit[i] || (c == 0x5F && lit[i] == 0x2D)) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether a handler may send a field with this name ([`name_ok`]).
pub fn check_name(n: &[u8]) -> (r: bool)
    ensures
        r == name_ok(n@),
{
    if n.len() == 0 {
        return false;
    }
    let mut i = 0;
    while i < n.len()
        invariant
            0 <= i <= n.len(),
            forall|j: int| 0 <= j < i ==> hs::is_tchar(#[trigger] n@[j]),
        decreases n.len() - i,
    {
        if !tchar(n[i]) {
            return false;
        }
        i += 1;
    }
    // Only the two framing names, 14 and 17 bytes long, need the slow check.
    if n.len() == 14 {
        let cl: [u8; 14] = [
            0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68,
        ];
        assert(cl@ =~= hs::name_content_length());
        if eq_dash(n, &cl) {
            return false;
        }
    }
    if n.len() == 17 {
        let te: [u8; 17] = [
            0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64,
            0x69, 0x6e, 0x67,
        ];
        assert(te@ =~= hs::name_transfer_encoding());
        if eq_dash(n, &te) {
            return false;
        }
    }
    true
}

#[inline]
fn value_char(c: u8) -> (r: bool)
    ensures
        r == hs::is_value_char(c),
{
    c == 0x09 || (c >= 0x20 && c != 0x7F)
}

/// Whether a handler may send this field value ([`value_ok`]).
pub fn check_value(v: &[u8]) -> (r: bool)
    ensures
        r == value_ok(v@),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> hs::is_value_char(#[trigger] v@[j]),
        decreases v.len() - i,
    {
        if !value_char(v[i]) {
            return false;
        }
        i += 1;
    }
    if v.len() > 0 {
        let a = v[0];
        let z = v[v.len() - 1];
        if a == 0x20 || a == 0x09 || z == 0x20 || z == 0x09 {
            return false;
        }
    }
    true
}

/// Whether this is a reason phrase ([`reason_ok`]).
pub fn check_reason(r: &[u8]) -> (ok: bool)
    ensures
        ok == reason_ok(r@),
{
    let mut i = 0;
    while i < r.len()
        invariant
            0 <= i <= r.len(),
            forall|j: int| 0 <= j < i ==> hs::is_value_char(#[trigger] r@[j]),
        decreases r.len() - i,
    {
        if !value_char(r[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// Appends `dec(n)`.
pub fn push_dec(out: &mut Vec<u8>, n: u64)
    ensures
        final(out)@ == old(out)@ + dec(n as nat),
    decreases n,
{
    if n < 10 {
        out.push((0x30 + n) as u8);
        assert(final(out)@ =~= old(out)@ + dec(n as nat));
    } else {
        push_dec(out, n / 10);
        out.push((0x30 + n % 10) as u8);
        assert(final(out)@ =~= old(out)@ + dec(n as nat));
    }
}

fn push_line(out: &mut Vec<u8>, name: &[u8], value: &[u8])
    ensures
        final(out)@ == old(out)@ + line((name@, value@)),
{
    verilith_core::prims::extend(out, name);
    out.push(hs::COLON);
    out.push(hs::SP);
    verilith_core::prims::extend(out, value);
    out.push(hs::CR);
    out.push(hs::LF);
    assert(final(out)@ =~= old(out)@ + line((name@, value@)));
}

proof fn lemma_lines_push(fs: Seq<SField>, x: SField)
    ensures
        lines(fs.push(x)) == lines(fs) + line(x),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(fs.push(x).drop_first() =~= Seq::<SField>::empty());
        assert(lines(Seq::<SField>::empty()) =~= Seq::<u8>::empty());
        assert(lines(fs.push(x)) =~= line(x) + Seq::<u8>::empty());
    } else {
        assert(fs.push(x).drop_first() =~= fs.drop_first().push(x));
        lemma_lines_push(fs.drop_first(), x);
        assert(lines(fs.push(x)) =~= lines(fs) + line(x));
    }
}

/// Appends the framing field line, if any.
fn push_framing(out: &mut Vec<u8>, framing: Framing, Ghost(fv): Ghost<Seq<SField>>)
    ensures
        lines(fv) + (final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == lines(
            all_fields(fv, framing),
        ),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        final(out)@.len() >= old(out)@.len(),
{
    let ghost o = out@;
    match framing {
        Framing::Length(n) => {
            let name: [u8; 14] = [
                0x43u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x4c, 0x65, 0x6e, 0x67, 0x74, 0x68,
            ];
            assert(name@ =~= cl_name());
            verilith_core::prims::extend(out, &name);
            out.push(hs::COLON);
            out.push(hs::SP);
            push_dec(out, n);
            out.push(hs::CR);
            out.push(hs::LF);
            proof {
                assert(out@ =~= o + line((cl_name(), dec(n as nat))));
                lemma_lines_push(fv, (cl_name(), dec(n as nat)));
                assert(out@.subrange(o.len() as int, out@.len() as int) =~= line(
                    (cl_name(), dec(n as nat)),
                ));
                assert(out@.subrange(0, o.len() as int) =~= o);
            }
        },
        Framing::Chunked => {
            let name: [u8; 26] = [
                0x54u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x45, 0x6e, 0x63, 0x6f, 0x64,
                0x69, 0x6e, 0x67, 0x3a, 0x20, 0x63, 0x68, 0x75, 0x6e, 0x6b, 0x65, 0x64,
            ];
            assert(name@ =~= te_name() + seq![hs::COLON, hs::SP] + hs::coding_chunked());
            verilith_core::prims::extend(out, &name);
            out.push(hs::CR);
            out.push(hs::LF);
            proof {
                assert(out@ =~= o + line((te_name(), hs::coding_chunked())));
                lemma_lines_push(fv, (te_name(), hs::coding_chunked()));
                assert(out@.subrange(o.len() as int, out@.len() as int) =~= line(
                    (te_name(), hs::coding_chunked()),
                ));
                assert(out@.subrange(0, o.len() as int) =~= o);
            }
        },
        Framing::Neither => {
            assert(out@.subrange(o.len() as int, out@.len() as int) =~= Seq::<u8>::empty());
            assert(lines(fv) + Seq::<u8>::empty() =~= lines(fv));
            assert(out@.subrange(0, o.len() as int) =~= o);
        },
    }
}

proof fn lemma_lines_concat(x: Seq<SField>, y: Seq<SField>)
    ensures
        lines(x + y) == lines(x) + lines(y),
    decreases y.len(),
{
    if y.len() == 0 {
        assert(x + y =~= x);
        assert(lines(y) =~= Seq::<u8>::empty());
        assert(lines(x) + lines(y) =~= lines(x));
    } else {
        let y1 = y.drop_last();
        lemma_lines_concat(x, y1);
        assert(x + y =~= (x + y1).push(y.last()));
        assert(y =~= y1.push(y.last()));
        lemma_lines_push(x + y1, y.last());
        lemma_lines_push(y1, y.last());
        assert(lines(x + y) =~= lines(x) + lines(y));
    }
}

/// Appends the field lines of `fields`.
fn push_lines(out: &mut Vec<u8>, fields: &[Field])
    ensures
        final(out)@ == old(out)@ + lines(fields_view(fields@)),
{
    let ghost pre = out@;
    let mut i = 0;
    while i < fields.len()
        invariant
            0 <= i <= fields.len(),
            out@ == pre + lines(fields_view(fields@).take(i as int)),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        push_line(out, f.name, f.value);
        proof {
            let fv = fields_view(fields@);
            assert(fv.take(i + 1) =~= fv.take(i as int).push(fv[i as int]));
            lemma_lines_push(fv.take(i as int), fv[i as int]);
        }
        i += 1;
    }
    assert(fields_view(fields@).take(fields.len() as int) =~= fields_view(fields@));
}

/// Appends a response head: `HTTP/1.1 <status> <reason>`, the field lines
/// of `a` then of `b`, the framing field line, and the empty line.
/// (Two lists, so that the server's own fields and a handler's need not be
/// copied into one.)
pub fn write_head(
    out: &mut Vec<u8>,
    status: u16,
    reason: &[u8],
    a: &[Field],
    b: &[Field],
    framing: Framing,
)
    requires
        status_ok(status),
    ensures
        final(out)@ == old(out)@ + head(
            status,
            reason@,
            fields_view(a@) + fields_view(b@),
            framing,
        ),
{
    let start: [u8; 9] = [0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20];
    assert(start@ =~= version_sp());
    verilith_core::prims::extend(out, &start);
    out.push((0x30 + status / 100) as u8);
    out.push((0x30 + (status / 10) % 10) as u8);
    out.push((0x30 + status % 10) as u8);
    out.push(hs::SP);
    verilith_core::prims::extend(out, reason);
    out.push(hs::CR);
    out.push(hs::LF);
    let ghost pre = old(out)@ + status_line(status, reason@);
    assert(out@ =~= pre);
    push_lines(out, a);
    push_lines(out, b);
    let ghost fv = fields_view(a@) + fields_view(b@);
    proof {
        lemma_lines_concat(fields_view(a@), fields_view(b@));
        assert(out@ =~= pre + lines(fv));
    }
    let ghost mid = out@;
    push_framing(out, framing, Ghost(fv));
    proof {
        let added = out@.subrange(mid.len() as int, out@.len() as int);
        assert(out@ =~= mid + added);
        assert(mid + added =~= pre + (lines(fv) + added));
    }
    out.push(hs::CR);
    out.push(hs::LF);
    assert(final(out)@ =~= old(out)@ + head(status, reason@, fv, framing));
}

/// All of `fields` pass [`check_name`] and [`check_value`].
pub fn check_fields(fields: &[Field]) -> (r: bool)
    ensures
        r == fields_ok(fields_view(fields@)),
{
    let mut i = 0;
    while i < fields.len()
        invariant
            0 <= i <= fields.len(),
            fields_ok(fields_view(fields@).take(i as int)),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        if !check_name(f.name) || !check_value(f.value) {
            assert(!fields_ok(fields_view(fields@))) by {
                let fv = fields_view(fields@);
                assert(fv[i as int] == field_view(fields@[i as int]));
                assert(fv[i as int].0 == f.name@ && fv[i as int].1 == f.value@);
                assert(!(name_ok(fv[i as int].0) && value_ok(fv[i as int].1)));
            }
            return false;
        }
        proof {
            let fv = fields_view(fields@);
            assert forall|k: int| 0 <= k < i + 1 implies name_ok(#[trigger] fv.take(i + 1)[k].0)
                && value_ok(fv.take(i + 1)[k].1) by {
                if k < i {
                    assert(fv.take(i + 1)[k] == fv.take(i as int)[k]);
                }
            }
        }
        i += 1;
    }
    assert(fields_view(fields@).take(fields.len() as int) =~= fields_view(fields@));
    true
}

/// Checks everything [`theorem_head_parses`] needs, then writes the head.
/// On `true`, the bytes appended are `head(...)` for inputs that satisfy
/// the theorem's preconditions, so they parse back exactly; on `false`,
/// nothing is written.
pub fn write_head_checked(
    out: &mut Vec<u8>,
    status: u16,
    reason: &[u8],
    a: &[Field],
    b: &[Field],
    framing: Framing,
) -> (r: bool)
    ensures
        r ==> {
            &&& status_ok(status)
            &&& reason_ok(reason@)
            &&& fields_ok(fields_view(a@) + fields_view(b@))
            &&& framing_ok(framing)
            &&& final(out)@ == old(out)@ + head(
                status,
                reason@,
                fields_view(a@) + fields_view(b@),
                framing,
            )
        },
        !r ==> final(out)@ == old(out)@,
{
    if status < 100 || status > 999 || !check_reason(reason) || !check_fields(a) || !check_fields(b) {
        return false;
    }
    match framing {
        Framing::Length(n) => {
            if n > MAX_LENGTH {
                return false;
            }
        },
        _ => {},
    }
    proof {
        let x = fields_view(a@);
        let y = fields_view(b@);
        assert forall|i: int| 0 <= i < (x + y).len() implies name_ok(#[trigger] (x + y)[i].0)
            && value_ok((x + y)[i].1) by {
            if i < x.len() {
                assert((x + y)[i] == x[i]);
            } else {
                assert((x + y)[i] == y[i - x.len()]);
            }
        }
    }
    write_head(out, status, reason, a, b, framing);
    true
}

/// Field lines checked once and kept as the bytes they are written as:
/// the server's own fields (Server, Date, rebuilt once a second) and a
/// route's fixed fields (Content-Type, Cache-Control, ...), so the hot path
/// copies them instead of checking them again. The fields are private and
/// the type invariant says they are checked: a `Prepared` can only be made
/// by [`Prepared::new`], [`Prepared::empty`] or [`Prepared::with_close`].
pub struct Prepared {
    bytes: Vec<u8>,
    fs: Ghost<Seq<SField>>,
    /// Whether the fields may list `Connection: close`; false only if
    /// they do not.
    closes: bool,
}

/// `Connection: close`
pub open spec fn conn_close() -> SField {
    (
        seq![0x43u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e],
        seq![0x63u8, 0x6c, 0x6f, 0x73, 0x65],
    )
}

impl Prepared {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& fields_ok(self.fs@)
        &&& self.bytes@ == lines(self.fs@)
        &&& !self.closes ==> !crate::persist::fields_close(self.fs@)
    }

    /// `false` only if the fields do not list the option `close`.
    pub fn may_close(&self) -> (r: bool)
        ensures
            !r ==> !crate::persist::fields_close(self.fields()),
    {
        proof { use_type_invariant(self); }
        self.closes
    }

    /// The field lines.
    pub closed spec fn fields(&self) -> Seq<SField> {
        self.fs@
    }

    /// Checks `fields` and keeps their lines, or `None` if one is not allowed.
    pub fn new(fields: &[Field]) -> (r: Option<Prepared>)
        ensures
            r matches Some(p) ==> p.fields() == fields_view(fields@),
            r is None ==> !fields_ok(fields_view(fields@)),
    {
        if !check_fields(fields) {
            return None;
        }
        let mut bytes = Vec::new();
        push_lines(&mut bytes, fields);
        assert(bytes@ =~= lines(fields_view(fields@)));
        let closes = crate::persist::fields_close_exec(fields);
        Some(Prepared { bytes, fs: Ghost(fields_view(fields@)), closes })
    }

    /// No fields.
    pub fn empty() -> (r: Prepared)
        ensures
            r.fields() == Seq::<SField>::empty(),
    {
        let bytes = Vec::new();
        assert(bytes@ =~= lines(Seq::<SField>::empty()));
        Prepared { bytes, fs: Ghost(Seq::empty()), closes: false }
    }

    /// The same fields followed by `Connection: close`.
    pub fn with_close(&self) -> (r: Prepared)
        ensures
            r.fields() == self.fields().push(conn_close()),
    {
        proof { use_type_invariant(self); }
        let mut bytes = self.bytes.clone();
        let name: [u8; 10] = [0x43u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
        let value: [u8; 5] = [0x63u8, 0x6c, 0x6f, 0x73, 0x65];
        push_line(&mut bytes, &name, &value);
        let ghost fs = self.fs@.push(conn_close());
        proof {
            assert(name@ =~= conn_close().0);
            assert(value@ =~= conn_close().1);
            lemma_lines_push(self.fs@, conn_close());
            assert forall|i: int| 0 <= i < fs.len() implies name_ok(#[trigger] fs[i].0) && value_ok(fs[i].1) by {
                if i < self.fs@.len() {
                    assert(fs[i] == self.fs@[i]);
                } else {
                    assert(fs[i] == conn_close());
                    lemma_conn_close_ok();
                }
            }
        }
        Prepared { bytes, fs: Ghost(fs), closes: true }
    }
}

proof fn lemma_conn_close_ok()
    ensures
        name_ok(conn_close().0),
        value_ok(conn_close().1),
{
    let n = conn_close().0;
    let v = conn_close().1;
    assert(hs::is_tchar(n[0]) && hs::is_tchar(n[1]) && hs::is_tchar(n[2]) && hs::is_tchar(n[3]) && hs::is_tchar(n[4]));
    assert(hs::is_tchar(n[5]) && hs::is_tchar(n[6]) && hs::is_tchar(n[7]) && hs::is_tchar(n[8]) && hs::is_tchar(n[9]));
    assert(!hs::ci_eq_dash(n, hs::name_content_length()));
    assert(!hs::ci_eq_dash(n, hs::name_transfer_encoding()));
    assert(forall|i: int| 0 <= i < v.len() ==> hs::is_value_char(#[trigger] v[i]));
}

/// [`write_head_checked`] with two prepared field lists before the
/// unchecked ones: the head written is `head(status, reason, a ++ b ++ c,
/// framing)`, and the theorem's preconditions hold for it.
pub fn write_head_prepared(
    out: &mut Vec<u8>,
    status: u16,
    reason: &[u8],
    a: &Prepared,
    b: &Prepared,
    c: &[Field],
    framing: Framing,
) -> (r: bool)
    ensures
        r ==> {
            &&& status_ok(status)
            &&& reason_ok(reason@)
            &&& fields_ok(a.fields() + b.fields() + fields_view(c@))
            &&& framing_ok(framing)
            &&& final(out)@ == old(out)@ + head(
                status,
                reason@,
                a.fields() + b.fields() + fields_view(c@),
                framing,
            )
        },
        !r ==> final(out)@ == old(out)@,
{
    proof {
        use_type_invariant(a);
        use_type_invariant(b);
    }
    if status < 100 || status > 999 || !check_reason(reason) || !check_fields(c) {
        return false;
    }
    match framing {
        Framing::Length(n) => {
            if n > MAX_LENGTH {
                return false;
            }
        },
        _ => {},
    }
    let ghost all = a.fs@ + b.fs@ + fields_view(c@);
    proof {
        let x = a.fs@;
        let y = b.fs@;
        let z = fields_view(c@);
        assert forall|i: int| 0 <= i < all.len() implies name_ok(#[trigger] all[i].0) && value_ok(
            all[i].1,
        ) by {
            if i < x.len() {
                assert(all[i] == x[i]);
            } else if i < x.len() + y.len() {
                assert(all[i] == y[i - x.len()]);
            } else {
                assert(all[i] == z[i - x.len() - y.len()]);
            }
        }
    }
    let start: [u8; 9] = [0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20];
    assert(start@ =~= version_sp());
    verilith_core::prims::extend(out, &start);
    out.push((0x30 + status / 100) as u8);
    out.push((0x30 + (status / 10) % 10) as u8);
    out.push((0x30 + status % 10) as u8);
    out.push(hs::SP);
    verilith_core::prims::extend(out, reason);
    out.push(hs::CR);
    out.push(hs::LF);
    let ghost pre = old(out)@ + status_line(status, reason@);
    assert(out@ =~= pre);
    verilith_core::prims::extend(out, &a.bytes);
    verilith_core::prims::extend(out, &b.bytes);
    push_lines(out, c);
    proof {
        lemma_lines_concat(a.fs@, b.fs@);
        lemma_lines_concat(a.fs@ + b.fs@, fields_view(c@));
        assert(out@ =~= pre + lines(all));
    }
    let ghost mid = out@;
    push_framing(out, framing, Ghost(all));
    proof {
        let added = out@.subrange(mid.len() as int, out@.len() as int);
        assert(out@ =~= mid + added);
        assert(mid + added =~= pre + (lines(all) + added));
    }
    out.push(hs::CR);
    out.push(hs::LF);
    assert(final(out)@ =~= old(out)@ + head(status, reason@, all, framing));
    true
}

} // verus!
