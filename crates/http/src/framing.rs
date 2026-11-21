//! Message framing, proven to compute exactly `spec::request_body` and
//! `spec::response_body`: the decision that rules out request smuggling.
use crate::parse::*;
use crate::spec::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

#[inline(always)]
pub fn lower_exec(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if c >= 0x41 && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

/// `lower(c) == l`, computed as one OR and one compare: a lowercase
/// letter in `l` also matches its uppercase form, an uppercase `l` never
/// matches, and any other `l` must match exactly. With a constant literal
/// the mask and the test on `l` fold away.
#[inline(always)]
pub fn lower_eq(c: u8, l: u8) -> (r: bool)
    ensures
        r == (lower(c) == l),
{
    let m: u8 = if 0x61 <= l && l <= 0x7A {
        0x20
    } else {
        0
    };
    proof {
        assert(((c | m) == l && !(0x41 <= l && l <= 0x5A)) == ((if 0x41 <= c && c <= 0x5A {
            (c + 0x20) as u8
        } else {
            c
        }) == l)) by (bit_vector)
            requires
                m == (if 0x61 <= l && l <= 0x7A {
                    0x20u8
                } else {
                    0u8
                }),
        ;
    }
    (c | m) == l && !(0x41 <= l && l <= 0x5A)
}

/// Case-insensitive equality of `s` with the lowercase literal `lit`.
#[inline(always)]
pub fn ci_eq_exec(s: &[u8], lit: &[u8]) -> (r: bool)
    ensures
        r == ci_eq(s@, lit@),
{
    if s.len() != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < s.len()
        invariant
            s@.len() == lit@.len(),
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> lower(#[trigger] s@[j]) == lit@[j],
        decreases s@.len() - i,
    {
        if !lower_eq(get8(s, i), lit[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// `ci_eq_exec`, with `_` in `s` also matching `-` (spec `ci_eq_dash`).
#[inline(always)]
pub fn ci_eq_dash_exec(s: &[u8], lit: &[u8]) -> (r: bool)
    ensures
        r == ci_eq_dash(s@, lit@),
{
    if s.len() != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < s.len()
        invariant
            s@.len() == lit@.len(),
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> lower(#[trigger] s@[j]) == lit@[j] || (s@[j] == 0x5F && lit@[j] == 0x2D),
        decreases s@.len() - i,
    {
        let c = get8(s, i);
        if !lower_eq(c, lit[i]) && !(c == 0x5F && lit[i] == 0x2D) {
            return false;
        }
        i += 1;
    }
    true
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

/// Content-Length value (spec `content_length_value`).
pub fn content_length_exec(v: &[u8]) -> (r: Option<u64>)
    ensures
        r == content_length_value(v@),
{
    if v.len() == 0 || v.len() > 19 {
        return None;
    }
    let mut acc: u64 = 0;
    let mut i = 0;
    proof {
        assert(v@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(pow10(19) == 10000000000000000000nat) by (compute_only);
    }
    while i < v.len()
        invariant
            i <= v@.len() <= 19,
            pow10(19) == 10000000000000000000nat,
            forall|j: int| 0 <= j < i ==> is_digit(#[trigger] v@[j]),
            acc as nat == decimal(v@.subrange(0, i as int)),
            (acc as nat) < pow10(i as nat),
        decreases v@.len() - i,
    {
        let c = get8(v, i);
        if c < 0x30 || c > 0x39 {
            return None;
        }
        proof {
            let ghost s1 = v@.subrange(0, i + 1);
            assert(s1.drop_last() =~= v@.subrange(0, i as int));
            lemma_pow10_mono(i as nat, 18);
            let ghost p = pow10(i as nat);
            assert(acc * 10 + (c - 0x30) < 10 * p) by (nonlinear_arith)
                requires
                    acc < p,
                    c - 0x30 <= 9,
            ;
        }
        acc = acc * 10 + (c - 0x30) as u64;
        i += 1;
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    Some(acc)
}

pub proof fn lemma_pow10_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_mono(a, (b - 1) as nat);
    }
}

/// The transfer-coding list `v` (spec `te_list(v, 0, st)`).
pub fn te_list_exec(v: &[u8], st0: TeState) -> (r: Option<TeState>)
    ensures
        r == te_list(v@, 0, st0),
{
    let mut st = st0;
    let mut i: usize = 0;
    let chunked: [u8; 7] = [0x63u8, 0x68, 0x75, 0x6e, 0x6b, 0x65, 0x64];
    proof {
        assert(chunked@ =~= coding_chunked());
    }
    loop
        invariant
            i <= v@.len(),
            chunked@ == coding_chunked(),
            te_list(v@, 0, st0) == te_list(v@, i as int, st),
        decreases v@.len() - i,
    {
        let (a, _) = scan_ows(v, i);
        proof {
            lemma_run_end_bounds(v@, i as int, Cls::Ows);
        }
        if a >= v.len() {
            return Some(st);
        }
        if get8(v, a) == COMMA {
            i = a + 1;
            continue ;
        }
        let (e, _) = scan_token(v, a);
        proof {
            lemma_run_end_bounds(v@, a as int, Cls::Token);
        }
        if e == a {
            return None;
        }
        if st.chunked_last {
            return None;
        }
        st = TeState { present: true, chunked_last: ci_eq_exec(slice_subrange(v, a, e), chunked.as_slice()) };
        let (f, _) = scan_ows(v, e);
        proof {
            lemma_run_end_bounds(v@, e as int, Cls::Ows);
        }
        if f >= v.len() {
            return Some(st);
        }
        if get8(v, f) != COMMA {
            return None;
        }
        i = f + 1;
    }
}

/// A rejected prefix rejects the whole list.
pub proof fn lemma_fields_none(b: Seq<u8>, hs: Seq<SpecHeader>, k: int)
    requires
        0 <= k <= hs.len(),
        fields_of(b, hs.subrange(0, k)) is None,
    ensures
        fields_of(b, hs) is None,
    decreases hs.len() - k,
{
    if k < hs.len() {
        let s1 = hs.subrange(0, k + 1);
        assert(s1.drop_last() =~= hs.subrange(0, k));
        lemma_fields_none(b, hs, k + 1);
    } else {
        assert(hs.subrange(0, k) =~= hs);
    }
}

/// The exec form of `spec::Fields`. `hosts` saturates at 2, which is all
/// the framing rules distinguish.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldsExec {
    pub cl: Option<u64>,
    pub te: TeState,
    pub hosts: u8,
}

pub open spec fn fields_agree(x: FieldsExec, f: Fields) -> bool {
    &&& x.cl == f.cl
    &&& x.te == f.te
    &&& x.hosts <= 2
    &&& (x.hosts < 2 ==> x.hosts as nat == f.hosts)
    &&& (x.hosts == 2 ==> f.hosts >= 2)
}

pub open spec fn hspan(b: Seq<u8>, s: Span) -> Seq<u8> {
    b.subrange(s.start as int, s.end as int)
}

/// `fx` is the exec form of the framing fields of `hs` (`None` when they
/// reject the message).
pub open spec fn fx_agrees(b: Seq<u8>, hs: Seq<Header>, fx: Option<FieldsExec>) -> bool {
    match fields_of(b, headers_view(hs)) {
        Some(f) => fx matches Some(x) && fields_agree(x, f),
        None => fx is None,
    }
}

/// The framing fields of no field lines.
pub fn fields_start() -> (r: FieldsExec)
    ensures
        fields_agree(r, fields_init()),
{
    FieldsExec { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 }
}

/// One field line's effect on the framing fields (spec `fields_step`).
#[inline(always)]
pub fn field_step_exec(b: &[u8], h: Header, x: FieldsExec) -> (r: Option<FieldsExec>)
    requires
        hdr_ok(h, b@.len() as int),
    ensures
        forall|f: Fields| #[trigger]
            fields_agree(x, f) ==> match fields_step(b@, f, h@) {
                Some(g) => r matches Some(y) && fields_agree(y, g),
                None => r is None,
            },
{
    // Only names of length 14, 17 or 4 can matter; skip the rest without
    // slicing.
    let nl = h.name.end - h.name.start;
    if nl != 14 && nl != 17 && nl != 4 {
        proof {
            assert(!ci_eq(hspan(b@, h.name), name_content_length()));
            assert(!ci_eq(hspan(b@, h.name), name_transfer_encoding()));
            assert(!ci_eq(hspan(b@, h.name), name_host()));
            assert(!ci_eq_dash(hspan(b@, h.name), name_content_length()));
            assert(!ci_eq_dash(hspan(b@, h.name), name_transfer_encoding()));
        }
        return Some(x);
    }
    let cl_name: [u8; 14] = [
        0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68,
    ];
    let te_name: [u8; 17] = [
        0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69,
        0x6e, 0x67,
    ];
    let host_name: [u8; 4] = [0x68u8, 0x6f, 0x73, 0x74];
    proof {
        assert(cl_name@ =~= name_content_length());
        assert(te_name@ =~= name_transfer_encoding());
        assert(host_name@ =~= name_host());
    }
    let name = slice_subrange(b, h.name.start, h.name.end);
    let value = slice_subrange(b, h.value.start, h.value.end);
    let mut y = x;
    if ci_eq_exec(name, cl_name.as_slice()) {
        match content_length_exec(value) {
            Some(n) => {
                if let Some(m) = x.cl {
                    if m != n {
                        return None;
                    }
                }
                y.cl = Some(n);
            },
            None => {
                return None;
            },
        }
    } else if ci_eq_exec(name, te_name.as_slice()) {
        if x.te.present {
            return None;
        }
        match te_list_exec(value, TeState { present: true, chunked_last: false }) {
            Some(te) => {
                y.te = te;
            },
            None => {
                return None;
            },
        }
    } else if ci_eq_dash_exec(name, cl_name.as_slice()) || ci_eq_dash_exec(name, te_name.as_slice()) {
        return None;
    } else if ci_eq_exec(name, host_name.as_slice()) {
        if x.hosts < 2 {
            y.hosts = x.hosts + 1;
        }
    }
    Some(y)
}

/// `fields_of(b, hs.push(h))` is `fields_of(b, hs)` stepped by `h`.
pub proof fn lemma_fields_push(b: Seq<u8>, hs: Seq<SpecHeader>, h: SpecHeader)
    ensures
        fields_of(b, hs.push(h)) == match fields_of(b, hs) {
            Some(f) => fields_step(b, f, h),
            None => None,
        },
{
    assert(hs.push(h).drop_last() =~= hs);
}

/// The framing fields of `hs` (spec `fields_of`).
pub fn fields_exec(b: &[u8], hs: &[Header]) -> (r: Option<FieldsExec>)
    requires
        hdrs_ok(hs@, b@.len() as int),
    ensures
        match fields_of(b@, headers_view(hs@)) {
            Some(f) => r matches Some(x) && fields_agree(x, f),
            None => r is None,
        },
{
    let mut x = FieldsExec {
        cl: None,
        te: TeState { present: false, chunked_last: false },
        hosts: 0,
    };
    let ghost hv = headers_view(hs@);
    let mut i = 0;
    proof {
        assert(hv.subrange(0, 0) =~= Seq::<SpecHeader>::empty());
    }
    while i < hs.len()
        invariant
            i <= hs@.len(),
            hv == headers_view(hs@),
            hdrs_ok(hs@, b@.len() as int),
            fields_of(b@, hv.subrange(0, i as int)) matches Some(f) && fields_agree(x, f),
        decreases hs@.len() - i,
    {
        let h = hs[i];
        let ghost f = fields_of(b@, hv.subrange(0, i as int))->Some_0;
        proof {
            assert(hdr_ok(hs@[i as int], b@.len() as int));
            assert(hv.subrange(0, i + 1) =~= hv.subrange(0, i as int).push(h@));
            lemma_fields_push(b@, hv.subrange(0, i as int), h@);
        }
        match field_step_exec(b, h, x) {
            Some(y) => {
                x = y;
            },
            None => {
                proof {
                    lemma_fields_none(b@, hv, i + 1);
                }
                return None;
            },
        }
        i += 1;
    }
    proof {
        assert(hv.subrange(0, hs@.len() as int) =~= hv);
    }
    Some(x)
}

/// `request_body_exec` from the framing fields `fx` of `hs`, as
/// `request_fx` computes them.
pub fn request_body_fx(b: &[u8], line: RequestLine, hs: &[Header], fx: Option<FieldsExec>) -> (r: Option<Body>)
    requires
        fx_agrees(b@, hs@, fx),
    ensures
        r == request_body(
            b@,
            SpecRequest {
                method: line.method@,
                target: line.target@,
                minor: line.minor,
                headers: headers_view(hs@),
            },
        ),
{
    match fx {
        None => None,
        Some(f) => if f.hosts > 1 || (line.minor >= 1 && f.hosts == 0) {
            None
        } else {
            framing_exec(&f, line.minor)
        },
    }
}

/// `request_framing_exec` from the framing fields `fx` of `hs`.
pub fn request_framing_fx(b: &[u8], minor: u8, hs: &[Header], fx: Option<FieldsExec>) -> (r: Option<Body>)
    requires
        fx_agrees(b@, hs@, fx),
    ensures
        r == match fields_of(b@, headers_view(hs@)) {
            None => None,
            Some(f) => request_framing(f, minor),
        },
{
    match fx {
        None => None,
        Some(f) => framing_exec(&f, minor),
    }
}

/// `response_body_exec` from the framing fields `fx` of `hs`, as
/// `response_fx` computes them.
pub fn response_body_fx(b: &[u8], line: StatusLine, hs: &[Header], fx: Option<FieldsExec>, head: bool, connect: bool) -> (r:
    Option<Body>)
    requires
        fx_agrees(b@, hs@, fx),
    ensures
        r == response_body(
            b@,
            SpecResponse {
                minor: line.minor,
                status: line.status,
                reason: line.reason@,
                headers: headers_view(hs@),
            },
            head,
            connect,
        ),
{
    match fx {
        None => None,
        Some(f) => {
            let s = line.status;
            if f.te.present && (f.cl.is_some() || line.minor == 0) {
                None
            } else if head || (100 <= s && s <= 199) || s == 204 || s == 304 || (connect && 200 <= s
                && s <= 299) {
                Some(Body::Empty)
            } else if f.te.present {
                if f.te.chunked_last {
                    Some(Body::Chunked)
                } else {
                    Some(Body::Close)
                }
            } else {
                match f.cl {
                    Some(n) => Some(Body::Length(n)),
                    None => Some(Body::Close),
                }
            }
        },
    }
}

/// The body framing of a request (spec `request_body`), or `None` if the
/// request must be rejected.
pub fn request_body_exec(b: &[u8], line: RequestLine, hs: &[Header]) -> (r: Option<Body>)
    requires
        hdrs_ok(hs@, b@.len() as int),
    ensures
        r == request_body(
            b@,
            SpecRequest {
                method: line.method@,
                target: line.target@,
                minor: line.minor,
                headers: headers_view(hs@),
            },
        ),
{
    match fields_exec(b, hs) {
        None => None,
        Some(f) => if f.hosts > 1 || (line.minor >= 1 && f.hosts == 0) {
            None
        } else {
            framing_exec(&f, line.minor)
        },
    }
}

/// `request_body` without the Host rule: only Content-Length and
/// Transfer-Encoding, the rules that decide where the message ends.
pub fn request_framing_exec(b: &[u8], minor: u8, hs: &[Header]) -> (r: Option<Body>)
    requires
        hdrs_ok(hs@, b@.len() as int),
    ensures
        r == match fields_of(b@, headers_view(hs@)) {
            None => None,
            Some(f) => request_framing(f, minor),
        },
{
    match fields_exec(b, hs) {
        None => None,
        Some(f) => framing_exec(&f, minor),
    }
}

pub fn framing_exec(f: &FieldsExec, minor: u8) -> (r: Option<Body>)
    ensures
        forall|g: Fields| fields_agree(*f, g) ==> r == request_framing(g, minor),
{
    if f.te.present {
        if minor == 0 || f.cl.is_some() || !f.te.chunked_last {
            None
        } else {
            Some(Body::Chunked)
        }
    } else {
        match f.cl {
            Some(n) => Some(Body::Length(n)),
            None => Some(Body::Empty),
        }
    }
}

/// The body framing of a response (spec `response_body`), or `None` if the
/// response must be rejected.
pub fn response_body_exec(b: &[u8], line: StatusLine, hs: &[Header], head: bool, connect: bool) -> (r:
    Option<Body>)
    requires
        hdrs_ok(hs@, b@.len() as int),
    ensures
        r == response_body(
            b@,
            SpecResponse {
                minor: line.minor,
                status: line.status,
                reason: line.reason@,
                headers: headers_view(hs@),
            },
            head,
            connect,
        ),
{
    match fields_exec(b, hs) {
        None => None,
        Some(f) => {
            let s = line.status;
            if f.te.present && (f.cl.is_some() || line.minor == 0) {
                None
            } else if head || (100 <= s && s <= 199) || s == 204 || s == 304 || (connect && 200 <= s
                && s <= 299) {
                Some(Body::Empty)
            } else if f.te.present {
                if f.te.chunked_last {
                    Some(Body::Chunked)
                } else {
                    Some(Body::Close)
                }
            } else {
                match f.cl {
                    Some(n) => Some(Body::Length(n)),
                    None => Some(Body::Close),
                }
            }
        },
    }
}

} // verus!
