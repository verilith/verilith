//! Theorems about the spec.
//!
//! - **Extension stability**: once the bytes received so far are enough to
//!   accept or reject a head, more bytes never change the answer. So the
//!   result depends only on the head itself, never on what follows it (the
//!   body, or the next pipelined request), and a parser that is fed a
//!   stream in pieces cannot be made to disagree with one that sees it
//!   whole.
//! - **Heads end in CRLF CRLF**, which makes the incremental shortcut in
//!   `parse::request_resume` sound.
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// `p` is a final answer: `Done` or `Invalid`.
pub open spec fn decided<T>(p: Parsed<T>) -> bool {
    !(p is Partial)
}

proof fn lemma_run_end_ext(b: Seq<u8>, c: Seq<u8>, i: int, k: Cls)
    requires
        0 <= i <= b.len(),
    ensures
        run_end(b, i, k) < b.len() ==> run_end(b + c, i, k) == run_end(b, i, k),
        run_end(b, i, k) <= b.len(),
        run_end(b, i, k) >= i,
    decreases b.len() - i,
{
    if i < b.len() {
        assert((b + c)[i] == b[i]);
        if in_cls(k, b[i]) {
            lemma_run_end_ext(b, c, i + 1, k);
        }
    }
}

proof fn lemma_trim_ext(b: Seq<u8>, c: Seq<u8>, s: int, e: int)
    requires
        0 <= s,
        e <= b.len(),
    ensures
        trim_end(b + c, s, e) == trim_end(b, s, e),
    decreases e - s,
{
    if e > s {
        assert((b + c)[e - 1] == b[e - 1]);
        lemma_trim_ext(b, c, s, e - 1);
    }
}

proof fn lemma_lit_ext(b: Seq<u8>, c: Seq<u8>, i: int, s: Seq<u8>)
    requires
        0 <= i <= b.len(),
    ensures
        decided(lit(b, i, s)) ==> lit(b + c, i, s) == lit(b, i, s),
        lit(b, i, s) matches Parsed::Done(_, e) ==> e <= b.len(),
{
    let bc = b + c;
    let n = if b.len() - i < s.len() {
        b.len() - i
    } else {
        s.len() as int
    };
    let n2 = if bc.len() - i < s.len() {
        bc.len() - i
    } else {
        s.len() as int
    };
    assert(bc.subrange(i, i + n) =~= b.subrange(i, i + n));
    if b.subrange(i, i + n) != s.subrange(0, n) {
        // A mismatch in the first n bytes is also one in the first n2.
        if bc.subrange(i, i + n2) == s.subrange(0, n2) {
            assert(b.subrange(i, i + n) =~= s.subrange(0, n)) by {
                assert forall|j: int| 0 <= j < n implies #[trigger] b.subrange(i, i + n)[j]
                    == s.subrange(0, n)[j] by {
                    assert(bc.subrange(i, i + n2)[j] == s.subrange(0, n2)[j]);
                    assert(bc[i + j] == b[i + j]);
                }
            }
        }
    } else if n == s.len() {
        assert(n2 == n);
    }
}

proof fn lemma_run_then_ext(b: Seq<u8>, c: Seq<u8>, i: int, k: Cls, d: u8)
    requires
        0 <= i <= b.len(),
    ensures
        decided(run_then(b, i, k, d)) ==> run_then(b + c, i, k, d) == run_then(b, i, k, d),
        run_then(b, i, k, d) matches Parsed::Done(_, e) ==> i < e <= b.len(),
{
    lemma_run_end_ext(b, c, i, k);
    let e = run_end(b, i, k);
    if e < b.len() {
        assert((b + c)[e] == b[e]);
    }
}

proof fn lemma_version_ext(b: Seq<u8>, c: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        decided(parse_version(b, i)) ==> parse_version(b + c, i) == parse_version(b, i),
        parse_version(b, i) matches Parsed::Done(_, e) ==> i < e <= b.len(),
{
    lemma_lit_ext(b, c, i, http1_prefix());
    if let Parsed::Done(_, j) = lit(b, i, http1_prefix()) {
        if j < b.len() {
            assert((b + c)[j] == b[j]);
        }
    }
}

proof fn lemma_skip_ext(b: Seq<u8>, c: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        decided(skip_empty_lines(b, i)) ==> skip_empty_lines(b + c, i) == skip_empty_lines(b, i),
        skip_empty_lines(b, i) matches Parsed::Done(_, e) ==> i <= e < b.len(),
    decreases b.len() - i,
{
    if i < b.len() {
        assert((b + c)[i] == b[i]);
        if b[i] == CR && i + 1 < b.len() {
            assert((b + c)[i + 1] == b[i + 1]);
            if b[i + 1] == LF {
                lemma_skip_ext(b, c, i + 2);
            }
        }
    }
}

proof fn lemma_header_ext(b: Seq<u8>, c: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        decided(parse_header(b, i)) ==> parse_header(b + c, i) == parse_header(b, i),
        parse_header(b, i) matches Parsed::Done(_, e) ==> i < e <= b.len(),
{
    lemma_run_then_ext(b, c, i, Cls::Token, COLON);
    if let Parsed::Done(ne, v0) = run_then(b, i, Cls::Token, COLON) {
        lemma_run_end_ext(b, c, v0, Cls::Ows);
        let vs = run_end(b, v0, Cls::Ows);
        lemma_run_end_ext(b, c, vs, Cls::Value);
        let e = run_end(b, vs, Cls::Value);
        lemma_lit_ext(b, c, e, crlf());
        if e == b.len() {
            assert(b.subrange(e, e) =~= crlf().subrange(0, 0));
        }
        if decided(lit(b, e, crlf())) {
            // A decided lit at e means e < b.len(), so both runs ended inside b.
            assert(e < b.len());
            lemma_trim_ext(b, c, vs, e);
        }
    }
}

proof fn lemma_headers_ext(b: Seq<u8>, c: Seq<u8>, i: int, max: nat)
    requires
        0 <= i <= b.len(),
    ensures
        decided(parse_headers(b, i, max)) ==> parse_headers(b + c, i, max) == parse_headers(
            b,
            i,
            max,
        ),
        parse_headers(b, i, max) matches Parsed::Done(_, e) ==> i < e <= b.len(),
    decreases b.len() - i,
{
    if i < b.len() {
        assert((b + c)[i] == b[i]);
        if b[i] == CR {
            lemma_lit_ext(b, c, i, crlf());
        } else if max > 0 {
            lemma_header_ext(b, c, i);
            if let Parsed::Done(h, n) = parse_header(b, i) {
                lemma_headers_ext(b, c, n, (max - 1) as nat);
            }
        }
    }
}

/// **Extension stability for requests.**
pub proof fn theorem_request_ext(b: Seq<u8>, c: Seq<u8>, max: nat)
    ensures
        decided(parse_request(b, max)) ==> parse_request(b + c, max) == parse_request(b, max),
        parse_request(b, max) matches Parsed::Done(_, e) ==> e <= b.len(),
{
    lemma_skip_ext(b, c, 0);
    if let Parsed::Done(_, s) = skip_empty_lines(b, 0) {
        lemma_run_then_ext(b, c, s, Cls::Token, SP);
        if let Parsed::Done(me, t) = run_then(b, s, Cls::Token, SP) {
            lemma_run_then_ext(b, c, t, Cls::Target, SP);
            if let Parsed::Done(te, v) = run_then(b, t, Cls::Target, SP) {
                lemma_version_ext(b, c, v);
                if let Parsed::Done(minor, h) = parse_version(b, v) {
                    lemma_lit_ext(b, c, h, crlf());
                    if let Parsed::Done(_, h2) = lit(b, h, crlf()) {
                        lemma_headers_ext(b, c, h2, max);
                    }
                }
            }
        }
    }
}

proof fn lemma_status_ext(b: Seq<u8>, c: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        decided(parse_status(b, i)) ==> parse_status(b + c, i) == parse_status(b, i),
        parse_status(b, i) matches Parsed::Done(_, e) ==> e <= b.len(),
{
    if i < b.len() {
        assert((b + c)[i] == b[i]);
    }
    if i + 1 < b.len() {
        assert((b + c)[i + 1] == b[i + 1]);
    }
    if i + 2 < b.len() {
        assert((b + c)[i + 2] == b[i + 2]);
    }
}

/// **Extension stability for responses.**
pub proof fn theorem_response_ext(b: Seq<u8>, c: Seq<u8>, max: nat)
    ensures
        decided(parse_response(b, max)) ==> parse_response(b + c, max) == parse_response(b, max),
        parse_response(b, max) matches Parsed::Done(_, e) ==> e <= b.len(),
{
    lemma_version_ext(b, c, 0);
    if let Parsed::Done(minor, j) = parse_version(b, 0) {
        if j < b.len() {
            assert((b + c)[j] == b[j]);
            if b[j] == SP {
                lemma_status_ext(b, c, j + 1);
                if let Parsed::Done(code, k) = parse_status(b, j + 1) {
                    if k < b.len() {
                        assert((b + c)[k] == b[k]);
                    }
                    let rs = if k < b.len() && b[k] == SP {
                        k + 1
                    } else {
                        k
                    };
                    lemma_run_end_ext(b, c, rs, Cls::Value);
                    let re = if rs > k {
                        run_end(b, rs, Cls::Value)
                    } else {
                        k
                    };
                    lemma_lit_ext(b, c, re, crlf());
                    if re == b.len() {
                        assert(b.subrange(re, re) =~= crlf().subrange(0, 0));
                    }
                    if decided(lit(b, re, crlf())) {
                        assert(re < b.len());
                        // With k == b.len(), rs == k == re and lit is Partial.
                        assert(k < b.len());
                    }
                    if let Parsed::Done(_, h) = lit(b, re, crlf()) {
                        lemma_headers_ext(b, c, h, max);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Heads end in CRLF CRLF
// ---------------------------------------------------------------------------

/// `b[e-4..e]` is CR LF CR LF.
pub open spec fn crlfcrlf_at(b: Seq<u8>, e: int) -> bool {
    4 <= e <= b.len() && b[e - 4] == CR && b[e - 3] == LF && b[e - 2] == CR && b[e - 1] == LF
}

proof fn lemma_header_crlf(b: Seq<u8>, i: int)
    requires
        0 <= i <= b.len(),
    ensures
        parse_header(b, i) matches Parsed::Done(_, e) ==> e <= b.len() && b[e - 2] == CR && b[e
            - 1] == LF && i + 2 < e,
{
    lemma_run_then_ext(b, Seq::empty(), i, Cls::Token, COLON);
    if let Parsed::Done(ne, v0) = run_then(b, i, Cls::Token, COLON) {
        let vs = run_end(b, v0, Cls::Ows);
        lemma_run_end_ext(b, Seq::empty(), v0, Cls::Ows);
        let e = run_end(b, vs, Cls::Value);
        lemma_run_end_ext(b, Seq::empty(), vs, Cls::Value);
        lemma_lit_ext(b, Seq::empty(), e, crlf());
        if let Parsed::Done(_, n) = lit(b, e, crlf()) {
            assert(b.subrange(e, e + 2)[0] == crlf().subrange(0, 2)[0]);
            assert(b.subrange(e, e + 2)[1] == crlf().subrange(0, 2)[1]);
        }
    }
}

/// The field block at `i` ends in CRLF, preceded by another CRLF unless it
/// is just the final CRLF.
proof fn lemma_headers_crlf(b: Seq<u8>, i: int, max: nat)
    requires
        0 <= i <= b.len(),
    ensures
        parse_headers(b, i, max) matches Parsed::Done(_, e) ==> e <= b.len() && b[e - 2] == CR
            && b[e - 1] == LF && (e == i + 2 || crlfcrlf_at(b, e)),
    decreases b.len() - i,
{
    if i < b.len() {
        if b[i] == CR {
            if let Parsed::Done(_, n) = lit(b, i, crlf()) {
                lemma_lit_ext(b, Seq::empty(), i, crlf());
                assert(b.subrange(i, i + 2)[0] == crlf().subrange(0, 2)[0]);
                assert(b.subrange(i, i + 2)[1] == crlf().subrange(0, 2)[1]);
            }
        } else if max > 0 {
            lemma_header_crlf(b, i);
            if let Parsed::Done(h, n) = parse_header(b, i) {
                lemma_headers_crlf(b, n, (max - 1) as nat);
                lemma_headers_ext(b, Seq::empty(), n, (max - 1) as nat);
            }
        }
    }
}

/// A complete request head ends in CR LF CR LF.
pub proof fn theorem_request_crlfcrlf(b: Seq<u8>, max: nat)
    ensures
        parse_request(b, max) matches Parsed::Done(_, e) ==> crlfcrlf_at(b, e),
{
    if let Parsed::Done(_, s) = skip_empty_lines(b, 0) {
        lemma_skip_ext(b, Seq::empty(), 0);
        if let Parsed::Done(me, t) = run_then(b, s, Cls::Token, SP) {
            lemma_run_then_ext(b, Seq::empty(), s, Cls::Token, SP);
            if let Parsed::Done(te, v) = run_then(b, t, Cls::Target, SP) {
                lemma_run_then_ext(b, Seq::empty(), t, Cls::Target, SP);
                if let Parsed::Done(minor, h) = parse_version(b, v) {
                    lemma_version_ext(b, Seq::empty(), v);
                    if let Parsed::Done(_, h2) = lit(b, h, crlf()) {
                        lemma_lit_ext(b, Seq::empty(), h, crlf());
                        assert(b.subrange(h, h + 2)[0] == crlf().subrange(0, 2)[0]);
                        assert(b.subrange(h, h + 2)[1] == crlf().subrange(0, 2)[1]);
                        lemma_headers_crlf(b, h2, max);
                    }
                }
            }
        }
    }
}

/// A complete response head ends in CR LF CR LF.
pub proof fn theorem_response_crlfcrlf(b: Seq<u8>, max: nat)
    ensures
        parse_response(b, max) matches Parsed::Done(_, e) ==> crlfcrlf_at(b, e),
{
    if let Parsed::Done((minor, code, reason), h) = parse_status_line(b, 0) {
        lemma_version_ext(b, Seq::empty(), 0);
        let j = parse_version(b, 0)->Done_1;
        lemma_status_ext(b, Seq::empty(), j + 1);
        let k = parse_status(b, j + 1)->Done_1;
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
        lemma_run_end_ext(b, Seq::empty(), rs, Cls::Value);
        lemma_lit_ext(b, Seq::empty(), re, crlf());
        assert(b.subrange(re, re + 2)[0] == crlf().subrange(0, 2)[0]);
        assert(b.subrange(re, re + 2)[1] == crlf().subrange(0, 2)[1]);
        assert(h == re + 2);
        lemma_headers_crlf(b, h, max);
    }
}

/// If a request head is complete in `b` but not in its first `last` bytes,
/// a CR LF CR LF ends somewhere in `b[last..]`.
pub proof fn theorem_request_resume(b: Seq<u8>, last: int, max: nat)
    requires
        0 <= last <= b.len(),
        !(parse_request(b.subrange(0, last), max) is Done),
    ensures
        parse_request(b, max) matches Parsed::Done(_, e) ==> last < e && crlfcrlf_at(b, e),
{
    theorem_request_crlfcrlf(b, max);
    let a = b.subrange(0, last);
    let c = b.subrange(last, b.len() as int);
    assert(a + c =~= b);
    if let Parsed::Done(r, e) = parse_request(b, max) {
        if e <= last {
            // The head lies within `a`, so parsing `a` alone already decides.
            let a2 = b.subrange(0, e);
            let c2 = b.subrange(e, last);
            assert(a2 + c2 =~= a);
            assert(a2 + b.subrange(e, b.len() as int) =~= b);
            lemma_request_prefix(b, e, max);
            theorem_request_ext(a2, c2, max);
            assert(false);
        }
    }
}

/// A complete head is already complete in the prefix it occupies.
proof fn lemma_request_prefix(b: Seq<u8>, e: int, max: nat)
    requires
        parse_request(b, max) matches Parsed::Done(_, f) && f == e,
    ensures
        parse_request(b.subrange(0, e), max) == parse_request(b, max),
{
    theorem_request_ext(b, Seq::empty(), max);
    theorem_request_crlfcrlf(b, max);
    assert(agree(b, b.subrange(0, e), e)) by {
        assert forall|j: int| 0 <= j < e implies #[trigger] b[j] == b.subrange(0, e)[j] by {}
    }
    theorem_request_agree(b, b.subrange(0, e), max);
}

// ---------------------------------------------------------------------------
// A `Done` result depends only on the bytes it consumed
// ---------------------------------------------------------------------------

/// `b` and `b2` have the same first `n` bytes.
pub open spec fn agree(b: Seq<u8>, b2: Seq<u8>, n: int) -> bool {
    &&& 0 <= n <= b.len()
    &&& n <= b2.len()
    &&& forall|j: int| 0 <= j < n ==> #[trigger] b[j] == b2[j]
}

proof fn lemma_run_end_agree(b: Seq<u8>, b2: Seq<u8>, i: int, k: Cls, n: int)
    requires
        0 <= i,
        run_end(b, i, k) < n,
        agree(b, b2, n),
    ensures
        run_end(b2, i, k) == run_end(b, i, k),
    decreases b.len() - i,
{
    if i <= b.len() {
        lemma_run_end_ext(b, Seq::empty(), i, k);
    }
    assert(b[i] == b2[i]);
    if i < b.len() && in_cls(k, b[i]) {
        lemma_run_end_agree(b, b2, i + 1, k, n);
    }
}

proof fn lemma_trim_agree(b: Seq<u8>, b2: Seq<u8>, s: int, e: int)
    requires
        0 <= s,
        agree(b, b2, e),
    ensures
        trim_end(b2, s, e) == trim_end(b, s, e),
    decreases e - s,
{
    if e > s {
        lemma_trim_agree(b, b2, s, e - 1);
    }
}

proof fn lemma_lit_agree(b: Seq<u8>, b2: Seq<u8>, i: int, s: Seq<u8>, n: int)
    requires
        0 <= i,
        lit(b, i, s) matches Parsed::Done(_, e) && e <= n,
        agree(b, b2, n),
    ensures
        lit(b2, i, s) == lit(b, i, s),
{
    assert(b2.subrange(i, i + s.len()) =~= b.subrange(i, i + s.len()));
}

proof fn lemma_run_then_agree(b: Seq<u8>, b2: Seq<u8>, i: int, k: Cls, d: u8, n: int)
    requires
        0 <= i,
        run_then(b, i, k, d) matches Parsed::Done(_, e) && e <= n,
        agree(b, b2, n),
    ensures
        run_then(b2, i, k, d) == run_then(b, i, k, d),
{
    lemma_run_end_agree(b, b2, i, k, n);
    let e = run_end(b, i, k);
    if i <= b.len() {
        lemma_run_end_ext(b, Seq::empty(), i, k);
    }
    assert(b[e] == b2[e]);
}

proof fn lemma_version_agree(b: Seq<u8>, b2: Seq<u8>, i: int, n: int)
    requires
        0 <= i,
        parse_version(b, i) matches Parsed::Done(_, e) && e <= n,
        agree(b, b2, n),
    ensures
        parse_version(b2, i) == parse_version(b, i),
{
    lemma_lit_agree(b, b2, i, http1_prefix(), n);
}

proof fn lemma_header_agree(b: Seq<u8>, b2: Seq<u8>, i: int, n: int)
    requires
        0 <= i,
        parse_header(b, i) matches Parsed::Done(_, e) && e <= n,
        agree(b, b2, n),
    ensures
        parse_header(b2, i) == parse_header(b, i),
{
    lemma_header_ext(b, Seq::empty(), i);
    lemma_run_then_ext(b, Seq::empty(), i, Cls::Token, COLON);
    let ne = run_end(b, i, Cls::Token);
    let v0 = ne + 1;
    let vs = run_end(b, v0, Cls::Ows);
    lemma_run_end_ext(b, Seq::empty(), v0, Cls::Ows);
    let e = run_end(b, vs, Cls::Value);
    lemma_run_end_ext(b, Seq::empty(), vs, Cls::Value);
    lemma_lit_ext(b, Seq::empty(), e, crlf());
    lemma_run_then_agree(b, b2, i, Cls::Token, COLON, n);
    lemma_run_end_agree(b, b2, v0, Cls::Ows, n);
    lemma_run_end_agree(b, b2, vs, Cls::Value, n);
    lemma_lit_agree(b, b2, e, crlf(), n);
    lemma_trim_agree(b, b2, vs, e);
}

proof fn lemma_headers_agree(b: Seq<u8>, b2: Seq<u8>, i: int, max: nat, n: int)
    requires
        0 <= i,
        parse_headers(b, i, max) matches Parsed::Done(_, e) && e <= n,
        agree(b, b2, n),
    ensures
        parse_headers(b2, i, max) == parse_headers(b, i, max),
    decreases b.len() - i,
{
    lemma_headers_ext(b, Seq::empty(), i, max);
    if b[i] == CR {
        lemma_lit_agree(b, b2, i, crlf(), n);
    } else {
        lemma_header_ext(b, Seq::empty(), i);
        let m = parse_header(b, i)->Done_1;
        lemma_headers_ext(b, Seq::empty(), m, (max - 1) as nat);
        lemma_header_agree(b, b2, i, n);
        lemma_headers_agree(b, b2, m, (max - 1) as nat, n);
    }
}

proof fn lemma_skip_agree(b: Seq<u8>, b2: Seq<u8>, i: int, n: int)
    requires
        0 <= i,
        skip_empty_lines(b, i) matches Parsed::Done(_, e) && e < n,
        agree(b, b2, n),
    ensures
        skip_empty_lines(b2, i) == skip_empty_lines(b, i),
    decreases b.len() - i,
{
    if i <= b.len() {
        lemma_skip_ext(b, Seq::empty(), i);
    }
    assert(b[i] == b2[i]);
    if b[i] == CR {
        if i + 2 <= b.len() {
            lemma_skip_ext(b, Seq::empty(), i + 2);
        }
        assert(b[i + 1] == b2[i + 1]);
        lemma_skip_agree(b, b2, i + 2, n);
    }
}

/// A complete request head parses the same in any input that starts with
/// the same head bytes.
pub proof fn theorem_request_agree(b: Seq<u8>, b2: Seq<u8>, max: nat)
    requires
        parse_request(b, max) matches Parsed::Done(_, e) && agree(b, b2, e),
    ensures
        parse_request(b2, max) == parse_request(b, max),
{
    let n = parse_request(b, max)->Done_1;
    theorem_request_ext(b, Seq::empty(), max);
    lemma_skip_ext(b, Seq::empty(), 0);
    let s = skip_empty_lines(b, 0)->Done_1;
    lemma_run_then_ext(b, Seq::empty(), s, Cls::Token, SP);
    let t = run_then(b, s, Cls::Token, SP)->Done_1;
    lemma_run_then_ext(b, Seq::empty(), t, Cls::Target, SP);
    let v = run_then(b, t, Cls::Target, SP)->Done_1;
    lemma_version_ext(b, Seq::empty(), v);
    let h = parse_version(b, v)->Done_1;
    lemma_lit_ext(b, Seq::empty(), h, crlf());
    let h2 = lit(b, h, crlf())->Done_1;
    lemma_headers_ext(b, Seq::empty(), h2, max);
    lemma_skip_agree(b, b2, 0, n);
    lemma_run_then_agree(b, b2, s, Cls::Token, SP, n);
    lemma_run_then_agree(b, b2, t, Cls::Target, SP, n);
    lemma_version_agree(b, b2, v, n);
    lemma_lit_agree(b, b2, h, crlf(), n);
    lemma_headers_agree(b, b2, h2, max, n);
}

} // verus!
