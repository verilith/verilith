//! A streaming head parser: the head grammar and framing rules of
//! `spec.rs` as a byte-at-a-time state machine, for callers that receive a
//! head in pieces and cannot keep the earlier pieces (llhttp's API, as
//! Node.js uses it). `stream_proof.rs` proves that the machine accepts
//! exactly the heads `spec::parse_request` (or `parse_response`) accepts
//! with a valid framing, with the same end, version and framing fields; so
//! the uniqueness theorems carry over to it.
use crate::framing::*;
use crate::parse::*;
use crate::scan::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// What the name of the current field line can still turn out to be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NameM {
    /// Bytes so far, saturating at 32.
    pub len: u8,
    /// The name so far is a prefix of `content-length`, case-insensitively.
    pub cl: bool,
    pub te: bool,
    pub host: bool,
    /// ... with `_` also matching `-`.
    pub cld: bool,
    pub ted: bool,
}

/// What the value of the current field line is being checked as.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VK {
    /// No framing role.
    Other,
    Host,
    /// Content-Length: leading OWS, digits so far, trailing OWS.
    ClLead,
    ClDig { n: u64, cnt: u8 },
    ClTrail { n: u64 },
    /// Transfer-Encoding: between elements (`last`: the last coding so
    /// far is `chunked`), in a coding (`k` bytes, `m`: a prefix of
    /// `chunked`), and after a coding.
    TeSep { last: bool },
    TeTok { k: u8, m: bool },
    TeAfter { last: bool },
}

/// Where in the head the machine is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ph {
    // Request line.
    /// Before the method: a CR starts an empty line.
    RStart,
    RStartLf,
    Method,
    /// After the method's SP: the target must not be empty.
    Target0,
    Target,
    /// `k` bytes of `HTTP/1.` matched; at 7 a digit follows.
    RVer { k: u8 },
    RCr,
    RLf,
    // Status line.
    SVer { k: u8 },
    SSp,
    /// `k` digits of the status code read.
    Code { k: u8 },
    Reason,
    SLf,
    // Field lines.
    /// Start of a field line, or of the final CRLF.
    Line,
    EndLf,
    Name { m: NameM },
    Val { v: VK },
    ValLf { v: VK },
    /// The head is complete and its framing is valid.
    Done,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HS {
    pub ph: Ph,
    /// The framing fields of the field lines so far.
    pub f: FieldsExec,
    pub minor: u8,
    pub status: u16,
    pub req: bool,
    /// Whether the Host rule of `spec::request_body` is checked. Callers
    /// that check Host themselves (Node.js does, as its
    /// `requireHostHeader` option) start without it.
    pub host: bool,
}

pub open spec fn fields_none() -> FieldsExec {
    FieldsExec { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 }
}

pub open spec fn request_start_with(host: bool) -> HS {
    HS { ph: Ph::RStart, f: fields_none(), minor: 0, status: 0, req: true, host }
}

pub open spec fn request_start() -> HS {
    request_start_with(true)
}

pub open spec fn response_start() -> HS {
    HS { ph: Ph::SVer { k: 0 }, f: fields_none(), minor: 0, status: 0, req: false, host: false }
}

/// The Host rule of `spec::request_body`.
pub open spec fn hosts_ok(f: FieldsExec, minor: u8) -> bool {
    !(f.hosts > 1 || (minor >= 1 && f.hosts == 0))
}

pub open spec fn dash_match(c: u8, x: u8) -> bool {
    lower(c) == x || (c == 0x5F && x == 0x2D)
}

pub open spec fn name_start() -> NameM {
    NameM { len: 0, cl: true, te: true, host: true, cld: true, ted: true }
}

pub open spec fn name_next(m: NameM, c: u8) -> NameM {
    let l = m.len as int;
    NameM {
        len: if m.len < 32 {
            (m.len + 1) as u8
        } else {
            32
        },
        cl: m.cl && l < 14 && lower(c) == name_content_length()[l],
        te: m.te && l < 17 && lower(c) == name_transfer_encoding()[l],
        host: m.host && l < 4 && lower(c) == name_host()[l],
        cld: m.cld && l < 14 && dash_match(c, name_content_length()[l]),
        ted: m.ted && l < 17 && dash_match(c, name_transfer_encoding()[l]),
    }
}

/// The value check a name selects, at its colon (spec `fields_step`).
pub open spec fn name_end(f: FieldsExec, m: NameM) -> Option<VK> {
    if m.len == 14 && m.cl {
        Some(VK::ClLead)
    } else if m.len == 17 && m.te {
        if f.te.present {
            None
        } else {
            Some(VK::TeSep { last: false })
        }
    } else if (m.len == 14 && m.cld) || (m.len == 17 && m.ted) {
        None
    } else if m.len == 4 && m.host {
        Some(VK::Host)
    } else {
        Some(VK::Other)
    }
}

pub open spec fn tok_end(k: u8, m: bool) -> bool {
    m && k == 7
}

/// One value byte (a value character other than CR).
pub open spec fn vstep(v: VK, c: u8) -> Option<VK> {
    match v {
        VK::Other => Some(VK::Other),
        VK::Host => Some(VK::Host),
        VK::ClLead => if is_ows(c) {
            Some(VK::ClLead)
        } else if is_digit(c) {
            Some(VK::ClDig { n: (c - 0x30) as u64, cnt: 1 })
        } else {
            None
        },
        VK::ClDig { n, cnt } => if is_digit(c) {
            if cnt >= 19 {
                None
            } else {
                Some(VK::ClDig { n: (n * 10 + (c - 0x30)) as u64, cnt: (cnt + 1) as u8 })
            }
        } else if is_ows(c) {
            Some(VK::ClTrail { n })
        } else {
            None
        },
        VK::ClTrail { n } => if is_ows(c) {
            Some(VK::ClTrail { n })
        } else {
            None
        },
        VK::TeSep { last } => if is_ows(c) || c == COMMA {
            Some(VK::TeSep { last })
        } else if is_tchar(c) {
            if last {
                None
            } else {
                Some(VK::TeTok { k: 1, m: lower(c) == coding_chunked()[0] })
            }
        } else {
            None
        },
        VK::TeTok { k, m } => if is_tchar(c) {
            Some(
                VK::TeTok {
                    k: if k < 8 {
                        (k + 1) as u8
                    } else {
                        8
                    },
                    m: m && k < 7 && lower(c) == coding_chunked()[k as int],
                },
            )
        } else if is_ows(c) {
            Some(VK::TeAfter { last: tok_end(k, m) })
        } else if c == COMMA {
            Some(VK::TeSep { last: tok_end(k, m) })
        } else {
            None
        },
        VK::TeAfter { last } => if is_ows(c) {
            Some(VK::TeAfter { last })
        } else if c == COMMA {
            Some(VK::TeSep { last })
        } else {
            None
        },
    }
}

/// Folds a complete field line's value into the fields (spec
/// `fields_step`).
pub open spec fn apply(f: FieldsExec, v: VK) -> Option<FieldsExec> {
    match v {
        VK::Other => Some(f),
        VK::Host => Some(
            FieldsExec {
                hosts: if f.hosts < 2 {
                    (f.hosts + 1) as u8
                } else {
                    2
                },
                ..f
            },
        ),
        VK::ClLead => None,
        VK::ClDig { n, cnt } => if f.cl is None || f.cl == Some(n) {
            Some(FieldsExec { cl: Some(n), ..f })
        } else {
            None
        },
        VK::ClTrail { n } => if f.cl is None || f.cl == Some(n) {
            Some(FieldsExec { cl: Some(n), ..f })
        } else {
            None
        },
        VK::TeSep { last } => Some(
            FieldsExec { te: TeState { present: true, chunked_last: last }, ..f },
        ),
        VK::TeTok { k, m } => Some(
            FieldsExec { te: TeState { present: true, chunked_last: tok_end(k, m) }, ..f },
        ),
        VK::TeAfter { last } => Some(
            FieldsExec { te: TeState { present: true, chunked_last: last }, ..f },
        ),
    }
}

/// `request_framing` on exec fields.
pub open spec fn request_framing_x(f: FieldsExec, minor: u8) -> Option<Body> {
    if f.te.present {
        if minor == 0 || f.cl is Some || !f.te.chunked_last {
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

/// `response_framing` on exec fields.
pub open spec fn response_framing_x(f: FieldsExec, minor: u8, status: u16, head: bool, connect: bool) -> Option<
    Body,
> {
    if f.te.present && (f.cl is Some || minor == 0) {
        None
    } else if head || (100 <= status <= 199) || status == 204 || status == 304 || (connect && 200
        <= status <= 299) {
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
}

/// Whether a complete head with these fields is accepted (spec
/// `request_body` and `response_body` are `Some`).
pub open spec fn head_ok(s: HS) -> bool {
    if s.req {
        (s.host ==> hosts_ok(s.f, s.minor)) && request_framing_x(s.f, s.minor) is Some
    } else {
        !(s.f.te.present && (s.f.cl is Some || s.minor == 0))
    }
}

/// One step of the machine, or `None` if `c` makes the head invalid.
pub open spec fn hstep(s: HS, c: u8) -> Option<HS> {
    match s.ph {
        Ph::RStart => if c == CR {
            Some(HS { ph: Ph::RStartLf, ..s })
        } else if is_tchar(c) {
            Some(HS { ph: Ph::Method, ..s })
        } else {
            None
        },
        Ph::RStartLf => if c == LF {
            Some(HS { ph: Ph::RStart, ..s })
        } else {
            None
        },
        Ph::Method => if is_tchar(c) {
            Some(s)
        } else if c == SP {
            Some(HS { ph: Ph::Target0, ..s })
        } else {
            None
        },
        Ph::Target0 => if is_target_char(c) {
            Some(HS { ph: Ph::Target, ..s })
        } else {
            None
        },
        Ph::Target => if is_target_char(c) {
            Some(s)
        } else if c == SP {
            Some(HS { ph: Ph::RVer { k: 0 }, ..s })
        } else {
            None
        },
        Ph::RVer { k } => if k < 7 {
            if c == http1_prefix()[k as int] {
                Some(HS { ph: Ph::RVer { k: (k + 1) as u8 }, ..s })
            } else {
                None
            }
        } else if is_digit(c) {
            Some(HS { ph: Ph::RCr, minor: (c - 0x30) as u8, ..s })
        } else {
            None
        },
        Ph::RCr => if c == CR {
            Some(HS { ph: Ph::RLf, ..s })
        } else {
            None
        },
        Ph::RLf => if c == LF {
            Some(HS { ph: Ph::Line, ..s })
        } else {
            None
        },
        Ph::SVer { k } => if k < 7 {
            if c == http1_prefix()[k as int] {
                Some(HS { ph: Ph::SVer { k: (k + 1) as u8 }, ..s })
            } else {
                None
            }
        } else if is_digit(c) {
            Some(HS { ph: Ph::SSp, minor: (c - 0x30) as u8, ..s })
        } else {
            None
        },
        Ph::SSp => if c == SP {
            Some(HS { ph: Ph::Code { k: 0 }, ..s })
        } else {
            None
        },
        Ph::Code { k } => if k < 3 {
            if is_digit(c) && s.status < 100 {
                Some(
                    HS {
                        ph: Ph::Code { k: (k + 1) as u8 },
                        status: (s.status * 10 + (c - 0x30)) as u16,
                        ..s
                    },
                )
            } else {
                None
            }
        } else if c == SP {
            Some(HS { ph: Ph::Reason, ..s })
        } else if c == CR {
            Some(HS { ph: Ph::SLf, ..s })
        } else {
            None
        },
        Ph::Reason => if is_value_char(c) {
            Some(s)
        } else if c == CR {
            Some(HS { ph: Ph::SLf, ..s })
        } else {
            None
        },
        Ph::SLf => if c == LF {
            Some(HS { ph: Ph::Line, ..s })
        } else {
            None
        },
        Ph::Line => if c == CR {
            Some(HS { ph: Ph::EndLf, ..s })
        } else if is_tchar(c) {
            Some(HS { ph: Ph::Name { m: name_next(name_start(), c) }, ..s })
        } else {
            None
        },
        Ph::EndLf => if c == LF && head_ok(s) {
            Some(HS { ph: Ph::Done, ..s })
        } else {
            None
        },
        Ph::Name { m } => if is_tchar(c) {
            Some(HS { ph: Ph::Name { m: name_next(m, c) }, ..s })
        } else if c == COLON {
            match name_end(s.f, m) {
                Some(v) => Some(HS { ph: Ph::Val { v }, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::Val { v } => if c == CR {
            Some(HS { ph: Ph::ValLf { v }, ..s })
        } else if is_value_char(c) {
            match vstep(v, c) {
                Some(v2) => Some(HS { ph: Ph::Val { v: v2 }, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::ValLf { v } => if c == LF {
            match apply(s.f, v) {
                Some(f) => Some(HS { ph: Ph::Line, f, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::Done => None,
    }
}

/// Runs the machine over `b`, stopping at `Done`: the final state and the
/// bytes consumed.
pub open spec fn hrun(s: HS, b: Seq<u8>) -> Option<(HS, nat)>
    decreases b.len(),
{
    if b.len() == 0 || s.ph is Done {
        Some((s, 0))
    } else {
        match hstep(s, b[0]) {
            None => None,
            Some(s2) => match hrun(s2, b.drop_first()) {
                None => None,
                Some((s3, k)) => Some((s3, k + 1)),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------

#[inline(always)]
fn is_tchar_exec(c: u8) -> (r: bool)
    ensures
        r == is_tchar(c),
{
    crate::parse::tchar(c)
}

#[inline(always)]
fn is_ows_exec(c: u8) -> (r: bool)
    ensures
        r == is_ows(c),
{
    c == SP || c == HTAB
}

#[inline(always)]
fn is_value_char_exec(c: u8) -> (r: bool)
    ensures
        r == is_value_char(c),
{
    c == HTAB || (c >= 0x20 && c != 0x7F)
}

#[inline(always)]
fn is_digit_exec(c: u8) -> (r: bool)
    ensures
        r == is_digit(c),
{
    c >= 0x30 && c <= 0x39
}

#[inline(always)]
fn is_target_char_exec(c: u8) -> (r: bool)
    ensures
        r == is_target_char(c),
{
    (c >= 0x21 && c <= 0x7E) || c >= 0x80
}

#[inline(always)]
fn dash_match_exec(c: u8, x: u8) -> (r: bool)
    ensures
        r == dash_match(c, x),
{
    lower_exec(c) == x || (c == 0x5F && x == 0x2D)
}

fn name_next_exec(m: NameM, c: u8) -> (r: NameM)
    ensures
        r == name_next(m, c),
{
    let cl: [u8; 14] = [
        0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68,
    ];
    let te: [u8; 17] = [
        0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69,
        0x6e, 0x67,
    ];
    let host: [u8; 4] = [0x68u8, 0x6f, 0x73, 0x74];
    proof {
        assert(cl@ =~= name_content_length());
        assert(te@ =~= name_transfer_encoding());
        assert(host@ =~= name_host());
    }
    let l = m.len as usize;
    let lc = lower_exec(c);
    NameM {
        len: if m.len < 32 {
            m.len + 1
        } else {
            32
        },
        cl: m.cl && l < 14 && lc == cl[l],
        te: m.te && l < 17 && lc == te[l],
        host: m.host && l < 4 && lc == host[l],
        cld: m.cld && l < 14 && dash_match_exec(c, cl[l]),
        ted: m.ted && l < 17 && dash_match_exec(c, te[l]),
    }
}

fn name_end_exec(f: &FieldsExec, m: NameM) -> (r: Option<VK>)
    ensures
        r == name_end(*f, m),
{
    if m.len == 14 && m.cl {
        Some(VK::ClLead)
    } else if m.len == 17 && m.te {
        if f.te.present {
            None
        } else {
            Some(VK::TeSep { last: false })
        }
    } else if (m.len == 14 && m.cld) || (m.len == 17 && m.ted) {
        None
    } else if m.len == 4 && m.host {
        Some(VK::Host)
    } else {
        Some(VK::Other)
    }
}

fn vstep_exec(v: VK, c: u8) -> (r: Option<VK>)
    requires
        cl_inv(v),
    ensures
        r == vstep(v, c),
        r matches Some(v2) ==> cl_inv(v2),
{
    let chunked: [u8; 7] = [0x63u8, 0x68, 0x75, 0x6e, 0x6b, 0x65, 0x64];
    proof {
        assert(chunked@ =~= coding_chunked());
    }
    match v {
        VK::Other => Some(VK::Other),
        VK::Host => Some(VK::Host),
        VK::ClLead => if is_ows_exec(c) {
            Some(VK::ClLead)
        } else if is_digit_exec(c) {
            proof {
                assert(pow10(1) == 10) by (compute_only);
            }
            Some(VK::ClDig { n: (c - 0x30) as u64, cnt: 1 })
        } else {
            None
        },
        VK::ClDig { n, cnt } => if is_digit_exec(c) {
            if cnt >= 19 {
                None
            } else {
                proof {
                    lemma_cl_digits_bound(n, cnt, (c - 0x30) as u8);
                }
                Some(VK::ClDig { n: n * 10 + (c - 0x30) as u64, cnt: cnt + 1 })
            }
        } else if is_ows_exec(c) {
            Some(VK::ClTrail { n })
        } else {
            None
        },
        VK::ClTrail { n } => if is_ows_exec(c) {
            Some(VK::ClTrail { n })
        } else {
            None
        },
        VK::TeSep { last } => if is_ows_exec(c) || c == COMMA {
            Some(VK::TeSep { last })
        } else if is_tchar_exec(c) {
            if last {
                None
            } else {
                Some(VK::TeTok { k: 1, m: lower_exec(c) == chunked[0] })
            }
        } else {
            None
        },
        VK::TeTok { k, m } => if is_tchar_exec(c) {
            Some(
                VK::TeTok {
                    k: if k < 8 {
                        k + 1
                    } else {
                        8
                    },
                    m: m && k < 7 && lower_exec(c) == chunked[k as usize],
                },
            )
        } else if is_ows_exec(c) {
            Some(VK::TeAfter { last: m && k == 7 })
        } else if c == COMMA {
            Some(VK::TeSep { last: m && k == 7 })
        } else {
            None
        },
        VK::TeAfter { last } => if is_ows_exec(c) {
            Some(VK::TeAfter { last })
        } else if c == COMMA {
            Some(VK::TeSep { last })
        } else {
            None
        },
    }
}

/// A Content-Length accumulator never overflows: it is the value of at
/// most 19 digits. (The machine keeps that invariant: see `cl_inv`.)
pub open spec fn cl_inv(v: VK) -> bool {
    match v {
        VK::ClDig { n, cnt } => 1 <= cnt <= 19 && (n as nat) < pow10(cnt as nat),
        _ => true,
    }
}

pub open spec fn hs_inv(s: HS) -> bool {
    match s.ph {
        Ph::Val { v } => cl_inv(v),
        Ph::ValLf { v } => cl_inv(v),
        _ => true,
    }
}

proof fn lemma_cl_digits_bound(n: u64, cnt: u8, d: u8)
    requires
        1 <= cnt < 19,
        (n as nat) < pow10(cnt as nat),
        d <= 9,
    ensures
        n * 10 + d < pow10((cnt + 1) as nat),
        n * 10 + d <= u64::MAX,
{
    let p = pow10(cnt as nat);
    assert(pow10((cnt + 1) as nat) == 10 * p);
    assert(n * 10 + d < 10 * p) by (nonlinear_arith)
        requires
            (n as nat) < p,
            d <= 9,
    ;
    lemma_pow10_mono((cnt + 1) as nat, 19);
    assert(pow10(19) == 10000000000000000000nat) by (compute_only);
}

fn apply_exec(f: FieldsExec, v: VK) -> (r: Option<FieldsExec>)
    ensures
        r == apply(f, v),
{
    match v {
        VK::Other => Some(f),
        VK::Host => Some(
            FieldsExec {
                hosts: if f.hosts < 2 {
                    f.hosts + 1
                } else {
                    2
                },
                ..f
            },
        ),
        VK::ClLead => None,
        VK::ClDig { n, .. } | VK::ClTrail { n } => match f.cl {
            None => Some(FieldsExec { cl: Some(n), ..f }),
            Some(m) => if m == n {
                Some(FieldsExec { cl: Some(n), ..f })
            } else {
                None
            },
        },
        VK::TeSep { last } | VK::TeAfter { last } => Some(
            FieldsExec { te: TeState { present: true, chunked_last: last }, ..f },
        ),
        VK::TeTok { k, m } => Some(
            FieldsExec { te: TeState { present: true, chunked_last: m && k == 7 }, ..f },
        ),
    }
}

pub fn request_framing_x_exec(f: &FieldsExec, minor: u8) -> (r: Option<Body>)
    ensures
        r == request_framing_x(*f, minor),
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

pub fn response_framing_x_exec(f: &FieldsExec, minor: u8, status: u16, head: bool, connect: bool) -> (r:
    Option<Body>)
    ensures
        r == response_framing_x(*f, minor, status, head, connect),
{
    if f.te.present && (f.cl.is_some() || minor == 0) {
        None
    } else if head || (100 <= status && status <= 199) || status == 204 || status == 304 || (connect
        && 200 <= status && status <= 299) {
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
}

pub fn head_ok_exec(s: &HS) -> (r: bool)
    ensures
        r == head_ok(*s),
{
    if s.req {
        (!s.host || !(s.f.hosts > 1 || (s.minor >= 1 && s.f.hosts == 0))) && request_framing_x_exec(
            &s.f,
            s.minor,
        ).is_some()
    } else {
        !(s.f.te.present && (s.f.cl.is_some() || s.minor == 0))
    }
}

/// One step (spec `hstep`).
pub fn hstep_exec(s: HS, c: u8) -> (r: Option<HS>)
    requires
        hs_inv(s),
    ensures
        r == hstep(s, c),
        r matches Some(s2) ==> hs_inv(s2),
{
    let http1: [u8; 7] = [0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E];
    proof {
        assert(http1@ =~= http1_prefix());
    }
    match s.ph {
        Ph::RStart => if c == CR {
            Some(HS { ph: Ph::RStartLf, ..s })
        } else if is_tchar_exec(c) {
            Some(HS { ph: Ph::Method, ..s })
        } else {
            None
        },
        Ph::RStartLf => if c == LF {
            Some(HS { ph: Ph::RStart, ..s })
        } else {
            None
        },
        Ph::Method => if is_tchar_exec(c) {
            Some(s)
        } else if c == SP {
            Some(HS { ph: Ph::Target0, ..s })
        } else {
            None
        },
        Ph::Target0 => if is_target_char_exec(c) {
            Some(HS { ph: Ph::Target, ..s })
        } else {
            None
        },
        Ph::Target => if is_target_char_exec(c) {
            Some(s)
        } else if c == SP {
            Some(HS { ph: Ph::RVer { k: 0 }, ..s })
        } else {
            None
        },
        Ph::RVer { k } => if k < 7 {
            if c == http1[k as usize] {
                Some(HS { ph: Ph::RVer { k: k + 1 }, ..s })
            } else {
                None
            }
        } else if is_digit_exec(c) {
            Some(HS { ph: Ph::RCr, minor: c - 0x30, ..s })
        } else {
            None
        },
        Ph::RCr => if c == CR {
            Some(HS { ph: Ph::RLf, ..s })
        } else {
            None
        },
        Ph::RLf => if c == LF {
            Some(HS { ph: Ph::Line, ..s })
        } else {
            None
        },
        Ph::SVer { k } => if k < 7 {
            if c == http1[k as usize] {
                Some(HS { ph: Ph::SVer { k: k + 1 }, ..s })
            } else {
                None
            }
        } else if is_digit_exec(c) {
            Some(HS { ph: Ph::SSp, minor: c - 0x30, ..s })
        } else {
            None
        },
        Ph::SSp => if c == SP {
            Some(HS { ph: Ph::Code { k: 0 }, ..s })
        } else {
            None
        },
        Ph::Code { k } => if k < 3 {
            if is_digit_exec(c) && s.status < 100 {
                Some(HS { ph: Ph::Code { k: k + 1 }, status: s.status * 10 + (c - 0x30) as u16, ..s })
            } else {
                None
            }
        } else if c == SP {
            Some(HS { ph: Ph::Reason, ..s })
        } else if c == CR {
            Some(HS { ph: Ph::SLf, ..s })
        } else {
            None
        },
        Ph::Reason => if is_value_char_exec(c) {
            Some(s)
        } else if c == CR {
            Some(HS { ph: Ph::SLf, ..s })
        } else {
            None
        },
        Ph::SLf => if c == LF {
            Some(HS { ph: Ph::Line, ..s })
        } else {
            None
        },
        Ph::Line => if c == CR {
            Some(HS { ph: Ph::EndLf, ..s })
        } else if is_tchar_exec(c) {
            let m0 = NameM { len: 0, cl: true, te: true, host: true, cld: true, ted: true };
            Some(HS { ph: Ph::Name { m: name_next_exec(m0, c) }, ..s })
        } else {
            None
        },
        Ph::EndLf => if c == LF && head_ok_exec(&s) {
            Some(HS { ph: Ph::Done, ..s })
        } else {
            None
        },
        Ph::Name { m } => if is_tchar_exec(c) {
            Some(HS { ph: Ph::Name { m: name_next_exec(m, c) }, ..s })
        } else if c == COLON {
            match name_end_exec(&s.f, m) {
                Some(v) => Some(HS { ph: Ph::Val { v }, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::Val { v } => if c == CR {
            Some(HS { ph: Ph::ValLf { v }, ..s })
        } else if is_value_char_exec(c) {
            match vstep_exec(v, c) {
                Some(v2) => Some(HS { ph: Ph::Val { v: v2 }, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::ValLf { v } => if c == LF {
            match apply_exec(s.f, v) {
                Some(f) => Some(HS { ph: Ph::Line, f, ..s }),
                None => None,
            }
        } else {
            None
        },
        Ph::Done => None,
    }
}

/// The machine run over `b[i..e]`, without stopping.
pub open spec fn hfold(s: HS, b: Seq<u8>, i: int, e: int) -> Option<HS>
    decreases e - i,
{
    if i >= e {
        Some(s)
    } else {
        match hstep(s, b[i]) {
            None => None,
            Some(s2) => hfold(s2, b, i + 1, e),
        }
    }
}

proof fn lemma_hfold_fixed(s: HS, b: Seq<u8>, i: int, e: int)
    requires
        i <= e,
        forall|k: int| i <= k < e ==> hstep(s, #[trigger] b[k]) == Some(s),
    ensures
        hfold(s, b, i, e) == Some(s),
    decreases e - i,
{
    if i < e {
        lemma_hfold_fixed(s, b, i + 1, e);
    }
}

pub open spec fn name_dead(len: u8) -> NameM {
    NameM { len, cl: false, te: false, host: false, cld: false, ted: false }
}

pub open spec fn len_after(len: u8, n: int) -> u8 {
    if n == 0 {
        len
    } else if len + n <= 32 {
        (len + n) as u8
    } else {
        32
    }
}

proof fn lemma_hfold_name(s: HS, len: u8, b: Seq<u8>, i: int, e: int)
    requires
        i <= e,
        s.ph == (Ph::Name { m: name_dead(len) }),
        forall|k: int| i <= k < e ==> is_tchar(#[trigger] b[k]),
    ensures
        hfold(s, b, i, e) == Some(HS { ph: Ph::Name { m: name_dead(len_after(len, e - i)) }, ..s }),
    decreases e - i,
{
    if i < e {
        let len2: u8 = if len < 32 {
            (len + 1) as u8
        } else {
            32
        };
        let s2 = HS { ph: Ph::Name { m: name_dead(len2) }, ..s };
        assert(is_tchar(b[i]));
        assert(hstep(s, b[i]) == Some(s2));
        lemma_hfold_name(s2, len2, b, i + 1, e);
    }
}

/// The bytes `hbulk_exec` steps over in phase `ph`.
pub open spec fn bulk_byte(ph: Ph, c: u8) -> bool {
    match ph {
        Ph::Target => is_target_char(c),
        Ph::Reason => is_value_char(c),
        Ph::Val { v } => (v is Other || v is Host) && is_value_char(c),
        Ph::Name { .. } => is_tchar(c),
        _ => false,
    }
}

/// Steps over a run of bytes from `i` at once, where the step is trivial:
/// URL bytes, reason-phrase bytes, value bytes of a field with no framing
/// role (all with the SIMD scanners), and the rest of a field name that
/// can no longer be a framing one. The result is what stepping each byte
/// gives.
pub fn hbulk_exec(s: &HS, d: &[u8], i: usize) -> (r: (HS, usize))
    requires
        i <= d@.len(),
    ensures
        i <= r.1 <= d@.len(),
        hfold(*s, d@, i as int, r.1 as int) == Some(r.0),
        forall|k: int| i <= k < r.1 ==> bulk_byte(s.ph, #[trigger] d@[k]),
        hs_inv(*s) ==> hs_inv(r.0),
{
    match s.ph {
        Ph::Target => {
            let (e, _) = scan_target_fast(d, i);
            proof {
                lemma_run_end_bounds(d@, i as int, Cls::Target);
                lemma_hfold_fixed(*s, d@, i as int, e as int);
            }
            (*s, e)
        },
        Ph::Reason | Ph::Val { v: VK::Other } | Ph::Val { v: VK::Host } => {
            let (e, _) = scan_value_fast(d, i);
            proof {
                lemma_run_end_bounds(d@, i as int, Cls::Value);
                assert forall|k: int| i <= k < e implies hstep(*s, #[trigger] d@[k]) == Some(*s) by {
                    assert(is_value_char(d@[k]));
                }
                lemma_hfold_fixed(*s, d@, i as int, e as int);
            }
            (*s, e)
        },
        Ph::Name { m } => {
            if m.cl || m.te || m.host || m.cld || m.ted {
                return (*s, i);
            }
            let (e, _) = scan_token(d, i);
            proof {
                lemma_run_end_bounds(d@, i as int, Cls::Token);
                assert(m == name_dead(m.len));
                lemma_hfold_name(*s, m.len, d@, i as int, e as int);
            }
            let n = e - i;
            let len = if n == 0 {
                m.len
            } else if n <= 32 && m.len as usize + n <= 32 {
                (m.len as usize + n) as u8
            } else {
                32
            };
            let m2 = NameM { len, cl: false, te: false, host: false, cld: false, ted: false };
            (HS { ph: Ph::Name { m: m2 }, ..*s }, e)
        },
        _ => {
            proof {
                lemma_hfold_fixed(*s, d@, i as int, i as int);
            }
            (*s, i)
        },
    }
}

pub fn request_start_exec(host: bool) -> (r: HS)
    ensures
        r == request_start_with(host),
{
    HS {
        ph: Ph::RStart,
        f: FieldsExec { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 },
        minor: 0,
        status: 0,
        req: true,
        host,
    }
}

pub fn response_start_exec() -> (r: HS)
    ensures
        r == response_start(),
{
    HS {
        ph: Ph::SVer { k: 0 },
        f: FieldsExec { cl: None, te: TeState { present: false, chunked_last: false }, hosts: 0 },
        minor: 0,
        status: 0,
        req: false,
        host: false,
    }
}

} // verus!
