//! Verified upstream request heads.
//!
//! The proxy forwards a request by writing a fresh HTTP/1.1 request head
//! to the backend: the method and target it was given, `Host`, the
//! forwarded field lines, and `Content-Length` when there is a body.
//! [`theorem_request_parses`] says what the backend makes of those bytes,
//! read with verilith-http's specification of a request
//! (`spec::parse_request`, the definition its smuggling theorems use):
//! exactly that method and target, exactly those field lines in that
//! order, a single Host, and a body of exactly the length written, after
//! which the next request begins. So whatever the client sent, and in
//! whichever protocol, the backend reads one request per forwarded
//! request, with the body the proxy meant: front-to-back request
//! smuggling (the CL.TE family, a second request hidden in a body, a
//! header injected through a CR or LF in a value) is ruled out by the
//! theorem. [`check_request`] decides its preconditions exactly, and
//! [`write_request`] writes nothing unless they hold.
use vstd::prelude::*;
use verilith_http::spec as hs;
use verilith_server::respond::{Field, SField, MAX_LENGTH};
#[cfg(verus_keep_ghost)]
use verilith_server::respond::{cl_name, crlf, dec, fields_ok, fields_view, line, lines, name_ok, value_ok};
#[cfg(verus_keep_ghost)]
use verilith_server::respond::{
    lemma_ci_eq_dash, lemma_dec_digits, lemma_lines_concat, lemma_lines_push, lemma_lit_done,
    lemma_parse_lines, lemma_run_end_exact, line_ok,
};
#[cfg(verus_only)]
use verilith_core::num::is_digit;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// A method: a token (RFC 9110 §9.1).
pub open spec fn method_ok(m: Seq<u8>) -> bool {
    m.len() > 0 && forall|i: int| 0 <= i < m.len() ==> hs::is_tchar(#[trigger] m[i])
}

/// A request target: target characters, nonempty (RFC 9112 §3.2).
pub open spec fn target_ok(t: Seq<u8>) -> bool {
    t.len() > 0 && forall|i: int| 0 <= i < t.len() ==> hs::is_target_char(#[trigger] t[i])
}

/// "Host" as the proxy writes it.
pub open spec fn host_name() -> Seq<u8> {
    seq![0x48u8, 0x6f, 0x73, 0x74]
}

/// The forwarded field lines: each a field a handler could send
/// ([`name_ok`], [`value_ok`]: not Content-Length or Transfer-Encoding
/// under any spelling, no CR, LF or NUL), and none of them Host (the
/// proxy writes the one Host line itself).
pub open spec fn fwd_ok(fs: Seq<SField>) -> bool {
    fields_ok(fs) && forall|i: int| 0 <= i < fs.len() ==> !hs::ci_eq(#[trigger] fs[i].0, hs::name_host())
}

/// The field lines on the wire: Host, the forwarded ones, then
/// Content-Length if the request has a body.
pub open spec fn req_fields(host: Seq<u8>, fs: Seq<SField>, cl: Option<u64>) -> Seq<SField> {
    let a = seq![(host_name(), host)] + fs;
    match cl {
        Some(n) => a.push((cl_name(), dec(n as nat))),
        None => a,
    }
}

/// `" HTTP/1.1" CRLF`
pub open spec fn version_crlf() -> Seq<u8> {
    seq![hs::SP] + hs::http1_prefix() + seq![0x31u8] + crlf()
}

/// `method SP target SP "HTTP/1.1" CRLF`
pub open spec fn request_line(m: Seq<u8>, t: Seq<u8>) -> Seq<u8> {
    m + seq![hs::SP] + t + version_crlf()
}

/// The request head [`write_request`] writes.
pub open spec fn req_head(m: Seq<u8>, t: Seq<u8>, host: Seq<u8>, fs: Seq<SField>, cl: Option<u64>) -> Seq<u8> {
    request_line(m, t) + lines(req_fields(host, fs, cl)) + crlf()
}

pub open spec fn body_of(cl: Option<u64>) -> hs::Body {
    match cl {
        Some(n) => hs::Body::Length(n),
        None => hs::Body::Empty,
    }
}

pub open spec fn cl_ok(cl: Option<u64>) -> bool {
    match cl {
        Some(n) => n <= MAX_LENGTH,
        None => true,
    }
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

/// A request head written by [`write_request`], followed by anything at
/// all (its body, then whatever comes next on the connection), parses
/// under verilith-http's specification to exactly what was written, with
/// the body framing `body_of(cl)`: the backend's request ends exactly
/// where the proxy's does.
pub proof fn theorem_request_parses(
    m: Seq<u8>,
    t: Seq<u8>,
    host: Seq<u8>,
    fs: Seq<SField>,
    cl: Option<u64>,
    rest: Seq<u8>,
    max: nat,
)
    requires
        method_ok(m),
        target_ok(t),
        value_ok(host),
        fwd_ok(fs),
        cl_ok(cl),
        req_fields(host, fs, cl).len() <= max,
    ensures
        ({
            let h = req_head(m, t, host, fs, cl);
            let b = h + rest;
            let all = req_fields(host, fs, cl);
            match hs::parse_request(b, max) {
                hs::Parsed::Done(r, end) => {
                    &&& end == h.len()
                    &&& r.minor == 1
                    &&& hs::span_bytes(b, r.method) == m
                    &&& hs::span_bytes(b, r.target) == t
                    &&& r.headers.len() == all.len()
                    &&& forall|i: int|
                        0 <= i < all.len() ==> hs::span_bytes(b, #[trigger] r.headers[i].name)
                            == all[i].0 && hs::span_bytes(b, r.headers[i].value) == all[i].1
                    &&& hs::request_body(b, r) == Some(body_of(cl))
                },
                _ => false,
            }
        }),
{
    let h = req_head(m, t, host, fs, cl);
    let b = h + rest;
    let all = req_fields(host, fs, cl);
    lemma_req_fields_ok(host, fs, cl);
    let pre = request_line(m, t);
    assert(h =~= pre + lines(all) + crlf());
    assert(b =~= pre + (lines(all) + crlf() + rest));
    lemma_request_line(m, t, lines(all) + crlf() + rest);
    assert(b.subrange(pre.len() as int, b.len() as int) =~= lines(all) + (crlf() + rest));
    lemma_parse_lines(b, pre.len() as int, all, crlf() + rest, max);
    match hs::parse_headers(b, pre.len() as int, max) {
        hs::Parsed::Done(hdrs, end) => {
            assert(end == h.len());
            lemma_req_fields_of(b, hdrs, host, fs, cl);
            let r = hs::SpecRequest {
                method: hs::SpecSpan { start: 0, end: m.len() as int },
                target: hs::SpecSpan { start: m.len() as int + 1, end: m.len() as int + 1 + t.len() },
                minor: 1u8,
                headers: hdrs,
            };
            assert(hs::parse_request(b, max) == hs::Parsed::Done(r, end));
        },
        _ => {},
    }
}

/// The request line parses to its method, its target and version 1.1.
proof fn lemma_request_line(m: Seq<u8>, t: Seq<u8>, rest: Seq<u8>)
    requires
        method_ok(m),
        target_ok(t),
    ensures
        ({
            let pre = request_line(m, t);
            let b = pre + rest;
            let me = m.len() as int;
            let ts = me + 1;
            let te = ts + t.len();
            &&& hs::skip_empty_lines(b, 0) == hs::Parsed::Done((), 0)
            &&& hs::run_then(b, 0, hs::Cls::Token, hs::SP) == hs::Parsed::Done(me, ts)
            &&& hs::run_then(b, ts, hs::Cls::Target, hs::SP) == hs::Parsed::Done(te, te + 1)
            &&& hs::parse_version(b, te + 1) == hs::Parsed::Done(1u8, te + 9)
            &&& hs::lit(b, te + 9, hs::crlf()) == hs::Parsed::Done((), pre.len() as int)
            &&& hs::span_bytes(b, hs::SpecSpan { start: 0, end: me }) == m
            &&& hs::span_bytes(b, hs::SpecSpan { start: ts, end: te }) == t
            &&& pre.len() == te + 11
        }),
{
    let pre = request_line(m, t);
    let b = pre + rest;
    let me = m.len() as int;
    let ts = me + 1;
    let te = ts + t.len();
    assert(pre.len() == te + 11);
    assert forall|i: int| 0 <= i < me implies #[trigger] b[i] == m[i] by {
        assert(b[i] == pre[i]);
    }
    assert(b[me] == hs::SP) by {
        assert(b[me] == pre[me]);
    }
    assert forall|i: int| ts <= i < te implies #[trigger] b[i] == t[i - ts] by {
        assert(b[i] == pre[i]);
    }
    let v = version_crlf();
    assert forall|i: int| 0 <= i < 11 implies #[trigger] b[te + i] == v[i] by {
        assert(b[te + i] == pre[te + i]);
    }
    // Method.
    assert(hs::is_tchar(m[0]));
    assert(b[0] == m[0]);
    assert(b[0] != hs::CR);
    assert forall|i: int| 0 <= i < me implies hs::in_cls(hs::Cls::Token, #[trigger] b[i]) by {
        assert(b[i] == m[i]);
    }
    assert(!hs::is_tchar(hs::SP));
    lemma_run_end_exact(b, 0, me, hs::Cls::Token);
    // Target.
    assert forall|i: int| ts <= i < te implies hs::in_cls(hs::Cls::Target, #[trigger] b[i]) by {
        assert(b[i] == t[i - ts]);
    }
    assert(b[te] == v[0]);
    assert(b[te] == hs::SP);
    assert(!hs::is_target_char(hs::SP));
    lemma_run_end_exact(b, ts, te, hs::Cls::Target);
    // Version.
    let p7 = hs::http1_prefix();
    assert(b.subrange(te + 1, te + 8) =~= p7) by {
        assert forall|i: int| 0 <= i < 7 implies b.subrange(te + 1, te + 8)[i] == p7[i] by {
            assert(b[te + 1 + i] == v[1 + i]);
        }
    }
    lemma_lit_done(b, te + 1, p7);
    assert(b[te + 8] == v[8]);
    assert(b[te + 8] == 0x31u8);
    assert(is_digit(0x31u8));
    assert(b.subrange(te + 9, te + 11) =~= hs::crlf()) by {
        assert(b[te + 9] == v[9]);
        assert(b[te + 10] == v[10]);
    }
    lemma_lit_done(b, te + 9, hs::crlf());
    assert(hs::span_bytes(b, hs::SpecSpan { start: 0, end: me }) =~= m) by {
        assert forall|i: int| 0 <= i < me implies b.subrange(0, me)[i] == m[i] by {}
    }
    assert(hs::span_bytes(b, hs::SpecSpan { start: ts, end: te }) =~= t) by {
        assert forall|i: int| 0 <= i < t.len() implies b.subrange(ts, te)[i] == t[i] by {
            assert(b[ts + i] == t[i]);
        }
    }
}

/// Every field line on the wire is well formed.
proof fn lemma_req_fields_ok(host: Seq<u8>, fs: Seq<SField>, cl: Option<u64>)
    requires
        value_ok(host),
        fwd_ok(fs),
        cl_ok(cl),
    ensures
        forall|i: int|
            0 <= i < req_fields(host, fs, cl).len() ==> line_ok(#[trigger] req_fields(host, fs, cl)[i]),
{
    let all = req_fields(host, fs, cl);
    let a = seq![(host_name(), host)] + fs;
    assert forall|i: int| 0 <= i < all.len() implies line_ok(#[trigger] all[i]) by {
        if i == 0 {
            assert(all[0] == (host_name(), host));
            assert forall|j: int| 0 <= j < host_name().len() implies hs::is_tchar(
                #[trigger] host_name()[j],
            ) by {}
        } else if i < a.len() {
            assert(all[i] == a[i]);
            assert(a[i] == fs[i - 1]);
            assert(name_ok(fs[i - 1].0));
        } else {
            match cl {
                Some(n) => {
                    assert(all[i] == (cl_name(), dec(n as nat)));
                    lemma_dec_digits(n as nat);
                    let d = dec(n as nat);
                    assert forall|j: int| 0 <= j < cl_name().len() implies hs::is_tchar(
                        #[trigger] cl_name()[j],
                    ) by {}
                    assert forall|j: int| 0 <= j < d.len() implies hs::is_value_char(
                        #[trigger] d[j],
                    ) by {
                        assert(is_digit(d[j]));
                    }
                    assert(is_digit(d[0]));
                    assert(is_digit(d[d.len() - 1]));
                },
                None => {},
            }
        }
    }
}

/// The framing analysis of the parsed field lines: one Host, no
/// Transfer-Encoding, and Content-Length exactly `cl`.
proof fn lemma_req_fields_of(
    b: Seq<u8>,
    hdrs: Seq<hs::SpecHeader>,
    host: Seq<u8>,
    fs: Seq<SField>,
    cl: Option<u64>,
)
    requires
        value_ok(host),
        fwd_ok(fs),
        cl_ok(cl),
        hdrs.len() == req_fields(host, fs, cl).len(),
        forall|k: int|
            0 <= k < hdrs.len() ==> hs::span_bytes(b, #[trigger] hdrs[k].name) == req_fields(
                host,
                fs,
                cl,
            )[k].0 && hs::span_bytes(b, hdrs[k].value) == req_fields(host, fs, cl)[k].1,
    ensures
        hs::fields_of(b, hdrs) matches Some(fl) && fl.cl == cl && !fl.te.present && fl.hosts == 1,
{
    let nf = fs.len() as int;
    assert forall|k: int| 1 <= k <= nf + 1 implies (hs::fields_of(b, #[trigger] hdrs.take(k)) matches Some(
        fl,
    ) && fl.cl is None && !fl.te.present && fl.hosts == 1) by {
        lemma_req_prefix(b, hdrs, host, fs, cl, k);
    }
    match cl {
        None => {
            assert(hdrs.take(nf + 1) =~= hdrs);
        },
        Some(n) => {
            assert(hdrs.take(nf + 2) =~= hdrs);
            assert(hdrs.drop_last() =~= hdrs.take(nf + 1));
            let h = hdrs.last();
            assert(req_fields(host, fs, cl)[nf + 1] == (cl_name(), dec(n as nat)));
            assert(hs::span_bytes(b, h.name) == cl_name());
            assert(hs::span_bytes(b, h.value) == dec(n as nat));
            assert(hs::ci_eq(cl_name(), hs::name_content_length()));
            lemma_dec_digits(n as nat);
            assert(hs::content_length_value(dec(n as nat)) == Some(n));
        },
    }
}

proof fn lemma_req_prefix(
    b: Seq<u8>,
    hdrs: Seq<hs::SpecHeader>,
    host: Seq<u8>,
    fs: Seq<SField>,
    cl: Option<u64>,
    k: int,
)
    requires
        fwd_ok(fs),
        1 <= k <= fs.len() + 1,
        hdrs.len() == req_fields(host, fs, cl).len(),
        forall|j: int|
            0 <= j < hdrs.len() ==> hs::span_bytes(b, #[trigger] hdrs[j].name) == req_fields(
                host,
                fs,
                cl,
            )[j].0,
    ensures
        hs::fields_of(b, hdrs.take(k)) matches Some(fl) && fl.cl is None && !fl.te.present
            && fl.hosts == 1,
    decreases k,
{
    let p = hdrs.take(k);
    let all = req_fields(host, fs, cl);
    let a = seq![(host_name(), host)] + fs;
    assert(p.drop_last() =~= hdrs.take(k - 1));
    let h = p.last();
    assert(h == hdrs[k - 1]);
    let name = hs::span_bytes(b, h.name);
    if k == 1 {
        assert(hdrs.take(0) =~= Seq::<hs::SpecHeader>::empty());
        assert(all[0] == (host_name(), host));
        assert(name == host_name());
        assert(hs::ci_eq(host_name(), hs::name_host()));
        assert(!hs::ci_eq(host_name(), hs::name_content_length()));
        assert(!hs::ci_eq(host_name(), hs::name_transfer_encoding()));
        assert(!hs::ci_eq_dash(host_name(), hs::name_content_length()));
        assert(!hs::ci_eq_dash(host_name(), hs::name_transfer_encoding()));
    } else {
        lemma_req_prefix(b, hdrs, host, fs, cl, k - 1);
        assert(all[k - 1] == a[k - 1]);
        assert(a[k - 1] == fs[k - 2]);
        assert(name == fs[k - 2].0);
        assert(name_ok(fs[k - 2].0));
        assert(!hs::ci_eq(fs[k - 2].0, hs::name_host()));
        lemma_ci_eq_dash(name, hs::name_content_length());
        lemma_ci_eq_dash(name, hs::name_transfer_encoding());
    }
}

proof fn lemma_fields_ok_at(fs: Seq<SField>, i: int)
    requires
        fields_ok(fs),
        0 <= i < fs.len(),
    ensures
        name_ok(fs[i].0) && value_ok(fs[i].1),
{
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

fn tchar(c: u8) -> (r: bool)
    ensures
        r == hs::is_tchar(c),
{
    verilith_server::respond::tchar(c)
}

/// Whether `m` is a method ([`method_ok`]).
pub fn check_method(m: &[u8]) -> (r: bool)
    ensures
        r == method_ok(m@),
{
    if m.len() == 0 {
        return false;
    }
    let mut i = 0;
    while i < m.len()
        invariant
            0 <= i <= m.len(),
            forall|j: int| 0 <= j < i ==> hs::is_tchar(#[trigger] m@[j]),
        decreases m.len() - i,
    {
        if !tchar(m[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `t` is a request target ([`target_ok`]).
pub fn check_target(t: &[u8]) -> (r: bool)
    ensures
        r == target_ok(t@),
{
    if t.len() == 0 {
        return false;
    }
    let mut i = 0;
    while i < t.len()
        invariant
            0 <= i <= t.len(),
            forall|j: int| 0 <= j < i ==> hs::is_target_char(#[trigger] t@[j]),
        decreases t.len() - i,
    {
        let c = t[i];
        if !((c >= 0x21 && c <= 0x7E) || c >= 0x80) {
            return false;
        }
        i += 1;
    }
    true
}

/// `ci_eq(n, "host")`.
pub fn is_host(n: &[u8]) -> (r: bool)
    ensures
        r == hs::ci_eq(n@, hs::name_host()),
{
    let host: [u8; 4] = [0x68, 0x6f, 0x73, 0x74];
    assert(host@ =~= hs::name_host());
    verilith_http::framing::ci_eq_exec(n, &host)
}

/// Whether the forwarded fields may be written ([`fwd_ok`]).
pub fn check_forwarded(fields: &[Field]) -> (r: bool)
    ensures
        r == fwd_ok(fields_view(fields@)),
{
    let ghost fv = fields_view(fields@);
    let mut i = 0;
    while i < fields.len()
        invariant
            0 <= i <= fields.len(),
            fv == fields_view(fields@),
            fv.len() == fields.len(),
            forall|j: int|
                0 <= j < i ==> name_ok(#[trigger] fv[j].0) && value_ok(fv[j].1) && !hs::ci_eq(
                    fv[j].0,
                    hs::name_host(),
                ),
        decreases fields.len() - i,
    {
        let f = &fields[i];
        assert(fv[i as int] == (f.name@, f.value@));
        if !verilith_server::respond::check_name(f.name) || !verilith_server::respond::check_value(f.value) || is_host(f.name) {
            proof {
                if fwd_ok(fv) {
                    assert(fields_ok(fv));
                    assert(0 <= i < fv.len());
                    lemma_fields_ok_at(fv, i as int);
                    assert(!hs::ci_eq(fv[i as int].0, hs::name_host()));
                }
            }
            return false;
        }
        i += 1;
    }
    true
}

/// Whether [`write_request`] may write this request: every precondition
/// of [`theorem_request_parses`], decided exactly.
pub fn check_request(method: &[u8], target: &[u8], host: &[u8], fields: &[Field], cl: Option<u64>) -> (r: bool)
    ensures
        r == (method_ok(method@) && target_ok(target@) && value_ok(host@) && fwd_ok(
            fields_view(fields@),
        ) && cl_ok(cl)),
{
    let cl_good = match cl {
        Some(n) => n <= MAX_LENGTH,
        None => true,
    };
    cl_good && check_method(method) && check_target(target) && verilith_server::respond::check_value(host)
        && check_forwarded(fields)
}

/// Appends the request head [`req_head`] to `out`, if [`check_request`]
/// says it may (returning false, and writing nothing, otherwise). The
/// backend then reads it as [`theorem_request_parses`] says.
pub fn write_request(
    out: &mut Vec<u8>,
    method: &[u8],
    target: &[u8],
    host: &[u8],
    fields: &[Field],
    cl: Option<u64>,
) -> (ok: bool)
    ensures
        ok == (method_ok(method@) && target_ok(target@) && value_ok(host@) && fwd_ok(
            fields_view(fields@),
        ) && cl_ok(cl)),
        ok ==> final(out)@ == old(out)@ + req_head(method@, target@, host@, fields_view(fields@), cl),
        !ok ==> final(out)@ == old(out)@,
{
    if !check_request(method, target, host, fields, cl) {
        return false;
    }
    let ghost o = out@;
    let ghost fv = fields_view(fields@);
    verilith_core::prims::extend(out, method);
    out.push(hs::SP);
    verilith_core::prims::extend(out, target);
    let v: [u8; 11] = [0x20, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x31, 0x2e, 0x31, 0x0d, 0x0a];
    assert(v@ =~= version_crlf());
    verilith_core::prims::extend(out, &v);
    assert(out@ =~= o + request_line(method@, target@));
    let ghost o2 = out@;
    let hn: [u8; 4] = [0x48, 0x6f, 0x73, 0x74];
    assert(hn@ =~= host_name());
    verilith_server::respond::push_line(out, &hn, host);
    verilith_server::respond::push_lines(out, fields);
    proof {
        let a = seq![(host_name(), host@)] + fv;
        assert(lines(seq![(host_name(), host@)]) =~= line((host_name(), host@))) by {
            assert(seq![(host_name(), host@)].drop_first() =~= Seq::<SField>::empty());
            assert(lines(Seq::<SField>::empty()) =~= Seq::<u8>::empty());
        }
        lemma_lines_concat(seq![(host_name(), host@)], fv);
        assert(out@ =~= o2 + lines(a));
    }
    match cl {
        Some(n) => {
            let ghost o3 = out@;
            let name: [u8; 14] = [0x43u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x4c, 0x65, 0x6e, 0x67, 0x74, 0x68];
            assert(name@ =~= cl_name());
            verilith_core::prims::extend(out, &name);
            out.push(hs::COLON);
            out.push(hs::SP);
            verilith_server::respond::push_dec(out, n);
            out.push(hs::CR);
            out.push(hs::LF);
            proof {
                let a = seq![(host_name(), host@)] + fv;
                assert(out@ =~= o3 + line((cl_name(), dec(n as nat))));
                lemma_lines_push(a, (cl_name(), dec(n as nat)));
            }
        },
        None => {},
    }
    out.push(hs::CR);
    out.push(hs::LF);
    assert(out@ =~= o + req_head(method@, target@, host@, fv, cl));
    true
}

} // verus!
