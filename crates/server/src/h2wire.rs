//! What the HTTP/2 engine reads and writes around the verified core
//! (`h2core.rs`), verified: the parts of `h2.rs` that decide what bytes
//! mean or which bytes are sent.
//!
//! - [`check_preface`]: the client connection preface (RFC 9113 §3.4).
//!   A connection goes on only once its first 24 bytes are exactly the
//!   preface, and is refused as soon as a byte differs.
//! - [`request_fields`]: a request's decoded fields (§8.2, §8.3), against
//!   the fold `fields_seen`. They are a request only if every name is
//!   non-empty and lowercase, no value holds NUL, CR or LF, the
//!   pseudo-header fields come first and are exactly one each of
//!   `:method`, `:scheme` and a non-empty `:path` with at most one
//!   `:authority`, no connection-specific field is present (§8.2.2), `te`
//!   is only `trailers`, and every Content-Length is a decimal length,
//!   all the same (RFC 9110 §8.6). The Content-Length is returned for
//!   the core to count DATA against (§8.1.1). HTTP/3 (`h3.rs`) checks its
//!   requests with the same function (RFC 9114 §4.3).
//! - [`write_headers`]: a response's header block as HEADERS then
//!   CONTINUATION frames (`header_frames`). A receiver following
//!   verilith-h2's specification reads the bytes back as exactly those
//!   frames (`lemma_reads_as`): all on the stream, END_STREAM on HEADERS
//!   as asked, END_HEADERS on the last frame only, each fragment at most
//!   [`CHUNK`] bytes, and the fragments, joined, the block
//!   (`lemma_header_frames`).
//! - [`data_head`]: a DATA frame's header; it and `n` body bytes are
//!   exactly a DATA frame with those bytes (`lemma_data_frame`). Which
//!   bytes of the body, how many and when END_STREAM is set is
//!   [`crate::h2core::Core::send_data`]'s.
//! - `lemma_response_rt`: a whole response as the core sends it, its
//!   header frames then its DATA frames in the sizes `send_data` chose,
//!   reads back as exactly those frames: the block, then exactly the body,
//!   END_STREAM on the last DATA frame (or on HEADERS, for an empty body)
//!   and nowhere else.
use vstd::prelude::*;

use verilith_h2::Frame;
#[cfg(verus_keep_ghost)]
use verilith_h2::spec;
#[cfg(verus_keep_ghost)]
use verilith_h2::spec::{MAX_31, MAX_MAX_FRAME_SIZE, MIN_MAX_FRAME_SIZE};
#[cfg(verus_keep_ghost)]
use verilith_h2::lemmas::lemma_roundtrip;
use verilith_http::parse::Header;
#[cfg(verus_keep_ghost)]
use verilith_http::parse::hdr_ok;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::content_length_value;
#[cfg(verus_keep_ghost)]
use verilith_core::scan::{any_upper_spec, any_nul_cr_lf_spec};
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------
// The connection preface (§3.4).

/// "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"
pub open spec fn preface() -> Seq<u8> {
    seq![
        0x50u8, 0x52, 0x49, 0x20, 0x2a, 0x20, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x32, 0x2e, 0x30,
        0x0d, 0x0a, 0x0d, 0x0a, 0x53, 0x4d, 0x0d, 0x0a, 0x0d, 0x0a,
    ]
}

/// What the start of a connection says about the preface.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Pre {
    /// A byte differs from the preface: PROTOCOL_ERROR.
    Bad,
    /// What has arrived is the preface so far.
    More,
    /// The first 24 bytes are the preface.
    Done,
}

pub open spec fn preface_res(b: Seq<u8>) -> Pre {
    let n = if b.len() < 24 { b.len() } else { 24 };
    if b.take(n as int) != preface().take(n as int) {
        Pre::Bad
    } else if n < 24 {
        Pre::More
    } else {
        Pre::Done
    }
}

pub fn check_preface(b: &[u8]) -> (r: Pre)
    ensures
        r == preface_res(b@),
{
    let p: [u8; 24] = [
        0x50u8, 0x52, 0x49, 0x20, 0x2a, 0x20, 0x48, 0x54, 0x54, 0x50, 0x2f, 0x32, 0x2e, 0x30,
        0x0d, 0x0a, 0x0d, 0x0a, 0x53, 0x4d, 0x0d, 0x0a, 0x0d, 0x0a,
    ];
    proof {
        assert(p@ =~= preface());
    }
    let n = if b.len() < 24 { b.len() } else { 24 };
    let mut i = 0;
    while i < n
        invariant
            n <= b@.len(),
            n <= 24,
            p@ == preface(),
            0 <= i <= n,
            forall|k: int| 0 <= k < i ==> b@[k] == p@[k],
        decreases n - i,
    {
        if b[i] != p[i] {
            proof {
                assert(b@.take(n as int)[i as int] != preface().take(n as int)[i as int]);
            }
            return Pre::Bad;
        }
        i += 1;
    }
    proof {
        assert(b@.take(n as int) =~= preface().take(n as int));
    }
    if n < 24 { Pre::More } else { Pre::Done }
}

// ---------------------------------------------------------------------
// A request's fields (§8.2, §8.3).

/// ":method"
pub open spec fn n_method() -> Seq<u8> { seq![0x3au8, 0x6d, 0x65, 0x74, 0x68, 0x6f, 0x64] }
/// ":scheme"
pub open spec fn n_scheme() -> Seq<u8> { seq![0x3au8, 0x73, 0x63, 0x68, 0x65, 0x6d, 0x65] }
/// ":path"
pub open spec fn n_path() -> Seq<u8> { seq![0x3au8, 0x70, 0x61, 0x74, 0x68] }
/// ":authority"
pub open spec fn n_authority() -> Seq<u8> { seq![0x3au8, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x74, 0x79] }
/// "connection"
pub open spec fn n_connection() -> Seq<u8> { seq![0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e] }
/// "keep-alive"
pub open spec fn n_keep_alive() -> Seq<u8> { seq![0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65] }
/// "proxy-connection"
pub open spec fn n_proxy_connection() -> Seq<u8> {
    seq![0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e]
}
/// "transfer-encoding"
pub open spec fn n_transfer_encoding() -> Seq<u8> {
    seq![0x74u8, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67]
}
/// "upgrade"
pub open spec fn n_upgrade() -> Seq<u8> { seq![0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65] }
/// "te"
pub open spec fn n_te() -> Seq<u8> { seq![0x74u8, 0x65] }
/// "trailers"
pub open spec fn v_trailers() -> Seq<u8> { seq![0x74u8, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72, 0x73] }
/// "content-length"
pub open spec fn n_content_length() -> Seq<u8> {
    seq![0x63u8, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68]
}

/// Connection-specific fields, which a request must not carry (§8.2.2).
pub open spec fn connection_specific(n: Seq<u8>) -> bool {
    n == n_connection() || n == n_keep_alive() || n == n_proxy_connection()
        || n == n_transfer_encoding() || n == n_upgrade()
}

/// What the fields so far have shown.
pub ghost struct Seen {
    pub method: nat,
    pub scheme: nat,
    pub path: nat,
    pub authority: nat,
    /// A regular (not pseudo-header) field has been seen.
    pub regular: bool,
    /// The Content-Length declared so far.
    pub cl: Option<u64>,
}

pub open spec fn seen0() -> Seen {
    Seen { method: 0, scheme: 0, path: 0, authority: 0, regular: false, cl: None }
}

/// One field `n: v` after `s`: None if it makes the request malformed.
pub open spec fn field_step(s: Seen, n: Seq<u8>, v: Seq<u8>) -> Option<Seen> {
    if n.len() == 0 || any_upper_spec(n) || any_nul_cr_lf_spec(v) {
        // §8.2.1: lowercase names; §8.2.1: no NUL, CR or LF in a value.
        None
    } else if n[0] == 0x3a {
        // §8.3: pseudo-header fields before regular ones, only the four
        // a request defines, and a non-empty :path.
        if s.regular {
            None
        } else if n == n_method() {
            Some(Seen { method: s.method + 1, ..s })
        } else if n == n_scheme() {
            Some(Seen { scheme: s.scheme + 1, ..s })
        } else if n == n_path() {
            if v.len() == 0 { None } else { Some(Seen { path: s.path + 1, ..s }) }
        } else if n == n_authority() {
            Some(Seen { authority: s.authority + 1, ..s })
        } else {
            None
        }
    } else if connection_specific(n) {
        None
    } else if n == n_te() && v != v_trailers() {
        None
    } else if n == n_content_length() {
        // RFC 9110 §8.6: a decimal length; several must agree.
        match content_length_value(v) {
            Some(l) => if s.cl is Some && s.cl != Some(l) {
                None
            } else {
                Some(Seen { regular: true, cl: Some(l), ..s })
            },
            None => None,
        }
    } else {
        Some(Seen { regular: true, ..s })
    }
}

pub open spec fn name_of(a: Seq<u8>, h: Header) -> Seq<u8> {
    a.subrange(h.name.start as int, h.name.end as int)
}

pub open spec fn value_of(a: Seq<u8>, h: Header) -> Seq<u8> {
    a.subrange(h.value.start as int, h.value.end as int)
}

/// The first `k` fields of `fs`, as spans into `a`, folded from
/// [`seen0`]; None once one is malformed (or not within `a`).
pub open spec fn fields_seen(a: Seq<u8>, fs: Seq<Header>, k: nat) -> Option<Seen>
    decreases k,
{
    if k == 0 {
        Some(seen0())
    } else if k > fs.len() {
        None
    } else {
        match fields_seen(a, fs, (k - 1) as nat) {
            Some(s) => if hdr_ok(fs[k - 1], a.len() as int) {
                field_step(s, name_of(a, fs[k - 1]), value_of(a, fs[k - 1]))
            } else {
                None
            },
            None => None,
        }
    }
}

/// The fields are a request (§8.3): exactly one `:method`, `:scheme` and
/// `:path`, at most one `:authority`, and each field well formed; then
/// the Content-Length they declare, if any.
pub open spec fn request_fields_spec(a: Seq<u8>, fs: Seq<Header>) -> Option<Option<u64>> {
    match fields_seen(a, fs, fs.len()) {
        Some(s) => if s.method == 1 && s.scheme == 1 && s.path == 1 && s.authority <= 1 {
            Some(s.cl)
        } else {
            None
        },
        None => None,
    }
}

proof fn lemma_seen_none(a: Seq<u8>, fs: Seq<Header>, k: nat, j: nat)
    requires
        fields_seen(a, fs, k) is None,
        k <= j,
    ensures
        fields_seen(a, fs, j) is None,
    decreases j - k,
{
    if j > k {
        lemma_seen_none(a, fs, k, (j - 1) as nat);
    }
}

#[inline(always)]
fn eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            0 <= i <= a@.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// Which name a pseudo-header field has.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PName {
    Method,
    Scheme,
    Path,
    Authority,
    Other,
}

#[inline(always)]
fn pseudo_name(n: &[u8]) -> (r: PName)
    ensures
        r == PName::Method <==> n@ == n_method(),
        r == PName::Scheme <==> n@ == n_scheme(),
        r == PName::Path <==> n@ == n_path(),
        r == PName::Authority <==> n@ == n_authority(),
{
    let m: [u8; 7] = [0x3a, 0x6d, 0x65, 0x74, 0x68, 0x6f, 0x64];
    let s: [u8; 7] = [0x3a, 0x73, 0x63, 0x68, 0x65, 0x6d, 0x65];
    let p: [u8; 5] = [0x3a, 0x70, 0x61, 0x74, 0x68];
    let au: [u8; 10] = [0x3a, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x74, 0x79];
    proof {
        assert(m@ =~= n_method());
        assert(s@ =~= n_scheme());
        assert(p@ =~= n_path());
        assert(au@ =~= n_authority());
        assert(n_method() != n_scheme()) by { assert(n_method()[1] != n_scheme()[1]); }
    }
    if eq(n, &m) {
        PName::Method
    } else if eq(n, &s) {
        PName::Scheme
    } else if eq(n, &p) {
        PName::Path
    } else if eq(n, &au) {
        PName::Authority
    } else {
        PName::Other
    }
}

/// Which regular name, of those §8.2.2 and §8.1.1 care about.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RName {
    ConnSpecific,
    Te,
    ContentLength,
    Other,
}

#[inline(always)]
fn regular_name(n: &[u8]) -> (r: RName)
    ensures
        r == RName::ConnSpecific <==> connection_specific(n@),
        r == RName::Te <==> n@ == n_te(),
        r == RName::ContentLength <==> n@ == n_content_length(),
{
    let c: [u8; 10] = [0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let k: [u8; 10] = [0x6b, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65];
    let pc: [u8; 16] = [0x70, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let te: [u8; 17] = [0x74, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x2d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67];
    let u: [u8; 7] = [0x75, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65];
    let t: [u8; 2] = [0x74, 0x65];
    let cl: [u8; 14] = [0x63, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74, 0x2d, 0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68];
    proof {
        assert(c@ =~= n_connection());
        assert(k@ =~= n_keep_alive());
        assert(pc@ =~= n_proxy_connection());
        assert(te@ =~= n_transfer_encoding());
        assert(u@ =~= n_upgrade());
        assert(t@ =~= n_te());
        assert(cl@ =~= n_content_length());
        assert(n_connection().len() != n_te().len());
        assert(n_keep_alive().len() != n_te().len());
        assert(n_proxy_connection().len() != n_te().len());
        assert(n_transfer_encoding().len() != n_te().len());
        assert(n_upgrade().len() != n_te().len());
        assert(n_connection().len() != n_content_length().len());
        assert(n_keep_alive().len() != n_content_length().len());
        assert(n_proxy_connection().len() != n_content_length().len());
        assert(n_transfer_encoding().len() != n_content_length().len());
        assert(n_upgrade().len() != n_content_length().len());
    }
    let r = if eq(n, &c) || eq(n, &k) || eq(n, &pc) || eq(n, &te) || eq(n, &u) {
        RName::ConnSpecific
    } else if eq(n, &t) {
        RName::Te
    } else if eq(n, &cl) {
        RName::ContentLength
    } else {
        RName::Other
    };
    r
}

#[inline(always)]
fn is_trailers(v: &[u8]) -> (r: bool)
    ensures
        r == (v@ == v_trailers()),
{
    let t: [u8; 8] = [0x74, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72, 0x73];
    proof {
        assert(t@ =~= v_trailers());
    }
    eq(v, &t)
}

/// `request_fields_spec`: None if the fields (spans into `a`) are not
/// a valid request (§8.3); otherwise the Content-Length they declare, if
/// any, for the core to check the stream's DATA against (§8.1.1).
pub fn request_fields(a: &[u8], fields: &[Header]) -> (r: Option<Option<u64>>)
    ensures
        r == request_fields_spec(a@, fields@),
{
    let (mut m, mut s, mut p, mut au): (usize, usize, usize, usize) = (0, 0, 0, 0);
    let mut cl: Option<u64> = None;
    let mut regular = false;
    let mut i = 0;
    while i < fields.len()
        invariant
            0 <= i <= fields@.len(),
            m <= i && s <= i && p <= i && au <= i,
            fields_seen(a@, fields@, i as nat) == Some(Seen {
                method: m as nat,
                scheme: s as nat,
                path: p as nat,
                authority: au as nat,
                regular,
                cl,
            }),
        decreases fields.len() - i,
    {
        let f = fields[i];
        proof {
            assert(fields@[i as int] == f);
        }
        if !(f.name.start <= f.name.end && f.name.end <= a.len() && f.value.start <= f.value.end
            && f.value.end <= a.len()) {
            proof {
                lemma_seen_none(a@, fields@, (i + 1) as nat, fields@.len());
            }
            return None;
        }
        let n = slice_subrange(a, f.name.start, f.name.end);
        let v = slice_subrange(a, f.value.start, f.value.end);
        proof {
            assert(n@ == name_of(a@, f));
            assert(v@ == value_of(a@, f));
        }
        let ok = if n.len() == 0 || verilith_core::scan::any_upper(n) || verilith_core::scan::any_nul_cr_lf(v) {
            false
        } else if n[0] == 0x3a {
            if regular {
                false
            } else {
                match pseudo_name(n) {
                    PName::Method => {
                        m += 1;
                        true
                    },
                    PName::Scheme => {
                        s += 1;
                        true
                    },
                    PName::Path => if v.len() == 0 {
                        false
                    } else {
                        p += 1;
                        true
                    },
                    PName::Authority => {
                        au += 1;
                        true
                    },
                    PName::Other => false,
                }
            }
        } else {
            match regular_name(n) {
                RName::ConnSpecific => false,
                RName::Te => if !is_trailers(v) {
                    false
                } else {
                    regular = true;
                    true
                },
                RName::ContentLength => match verilith_http::framing::content_length_exec(v) {
                    Some(len) => match cl {
                        Some(c) if c != len => false,
                        _ => {
                            cl = Some(len);
                            regular = true;
                            true
                        },
                    },
                    None => false,
                },
                RName::Other => {
                    regular = true;
                    true
                },
            }
        };
        if !ok {
            proof {
                lemma_seen_none(a@, fields@, (i + 1) as nat, fields@.len());
            }
            return None;
        }
        i += 1;
    }
    if m == 1 && s == 1 && p == 1 && au <= 1 { Some(cl) } else { None }
}

// ---------------------------------------------------------------------
// Response frames.

/// The largest fragment and DATA payload we send: the smallest
/// SETTINGS_MAX_FRAME_SIZE a peer may have (§4.2), so any peer takes it.
pub const CHUNK: usize = 16384;

/// CONTINUATION frames carrying `rest`, `m` bytes each, the last with
/// END_HEADERS.
pub open spec fn conts(id: u32, rest: Seq<u8>, m: nat) -> Seq<spec::Frame>
    decreases rest.len(),
{
    if rest.len() == 0 || m == 0 {
        seq![]
    } else if rest.len() <= m {
        seq![spec::Frame::Continuation { stream: id, end_headers: true, fragment: rest }]
    } else {
        seq![spec::Frame::Continuation { stream: id, end_headers: false, fragment: rest.take(m as int) }]
            + conts(id, rest.skip(m as int), m)
    }
}

/// A header block on stream `id`: HEADERS with its first `m` bytes (and
/// END_STREAM if `end_stream`), then CONTINUATION frames with the rest.
pub open spec fn hframe(id: u32, end_stream: bool, end_headers: bool, frag: Seq<u8>) -> spec::Frame {
    spec::Frame::Headers { stream: id, end_stream, end_headers, pad: None, priority: None, fragment: frag }
}

pub open spec fn header_frames(id: u32, block: Seq<u8>, end_stream: bool, m: nat) -> Seq<spec::Frame> {
    if block.len() <= m {
        seq![hframe(id, end_stream, true, block)]
    } else {
        seq![hframe(id, end_stream, false, block.take(m as int))] + conts(id, block.skip(m as int), m)
    }
}

/// The bytes of frames, one after another.
pub open spec fn ser_all(fs: Seq<spec::Frame>) -> Seq<u8>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        spec::serialize(fs[0]) + ser_all(fs.skip(1))
    }
}

/// verilith-h2's `spec::parse`, kept folded in the proofs below.
#[verifier::opaque]
pub open spec fn parse_at(b: Seq<u8>, max: u32) -> spec::Res {
    spec::parse(b, max)
}

/// A receiver whose SETTINGS_MAX_FRAME_SIZE is `max` parses `b`, frame by
/// frame, as exactly `fs`, and `rest` follows them.
pub open spec fn reads_as(b: Seq<u8>, max: u32, fs: Seq<spec::Frame>, rest: Seq<u8>) -> bool
    decreases fs.len(),
{
    if fs.len() == 0 {
        b == rest
    } else {
        match parse_at(b, max) {
            spec::Res::Frame(f, n) => f == fs[0] && n <= b.len() && reads_as(b.skip(n as int), max, fs.skip(1), rest),
            _ => false,
        }
    }
}

/// Well-formed frames read back as themselves, whatever follows them.
pub proof fn lemma_reads_as(fs: Seq<spec::Frame>, max: u32, rest: Seq<u8>)
    requires
        forall|i: int| 0 <= i < fs.len() ==> spec::wf(#[trigger] fs[i], max),
    ensures
        reads_as(ser_all(fs) + rest, max, fs, rest),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(ser_all(fs) + rest =~= rest);
    } else {
        let t = fs.skip(1);
        assert forall|i: int| 0 <= i < t.len() implies spec::wf(#[trigger] t[i], max) by {
            assert(t[i] == fs[i + 1]);
        }
        lemma_reads_as(t, max, rest);
        let s0 = spec::serialize(fs[0]);
        let x = ser_all(t) + rest;
        let b = ser_all(fs) + rest;
        assert(ser_all(fs) == s0 + ser_all(t));
        assert(b =~= s0 + x);
        lemma_roundtrip(fs[0], max, x);
        assert(parse_at(b, max) == spec::Res::Frame(fs[0], s0.len())) by {
            reveal(parse_at);
        }
        assert(b.skip(s0.len() as int) =~= x);
    }
}

pub open spec fn frag_of(f: spec::Frame) -> Seq<u8> {
    match f {
        spec::Frame::Headers { fragment, .. } => fragment,
        spec::Frame::Continuation { fragment, .. } => fragment,
        _ => Seq::empty(),
    }
}

pub open spec fn end_headers_of(f: spec::Frame) -> bool {
    match f {
        spec::Frame::Headers { end_headers, .. } => end_headers,
        spec::Frame::Continuation { end_headers, .. } => end_headers,
        _ => false,
    }
}

/// The fragments of `fs`, joined.
pub open spec fn frags(fs: Seq<spec::Frame>) -> Seq<u8>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        frag_of(fs[0]) + frags(fs.skip(1))
    }
}

proof fn lemma_conts(id: u32, rest: Seq<u8>, m: nat, max: u32)
    requires
        1 <= m <= max <= MAX_MAX_FRAME_SIZE,
        1 <= id <= MAX_31,
    ensures
        ({
            let fs = conts(id, rest, m);
            &&& (fs.len() == 0 <==> rest.len() == 0)
            &&& frags(fs) == rest
            &&& forall|i: int| 0 <= i < fs.len() ==> (#[trigger] fs[i]) is Continuation
                && spec::stream_of(fs[i]) == id
                && spec::wf(fs[i], max)
                && frag_of(fs[i]).len() <= m
                && (end_headers_of(fs[i]) <==> i == fs.len() - 1)
        }),
    decreases rest.len(),
{
    let fs = conts(id, rest, m);
    if rest.len() == 0 {
    } else if rest.len() <= m {
        let f = spec::Frame::Continuation { stream: id, end_headers: true, fragment: rest };
        assert(fs =~= seq![f]);
        assert(fs.skip(1) =~= Seq::<spec::Frame>::empty());
        assert(frags(Seq::<spec::Frame>::empty()) == Seq::<u8>::empty());
        assert(frags(fs) == frag_of(fs[0]) + frags(fs.skip(1)));
        assert(frags(fs) =~= rest);
    } else {
        let f = spec::Frame::Continuation { stream: id, end_headers: false, fragment: rest.take(m as int) };
        let t = conts(id, rest.skip(m as int), m);
        lemma_conts(id, rest.skip(m as int), m, max);
        assert(fs =~= seq![f] + t);
        assert(fs.skip(1) =~= t);
        assert(frags(fs) == frag_of(f) + frags(t));
        assert(rest.take(m as int) + rest.skip(m as int) =~= rest);
        assert forall|i: int| 0 <= i < fs.len() implies (#[trigger] fs[i]) is Continuation
            && spec::stream_of(fs[i]) == id
            && spec::wf(fs[i], max)
            && frag_of(fs[i]).len() <= m
            && (end_headers_of(fs[i]) <==> i == fs.len() - 1) by {
            if i > 0 {
                assert(fs[i] == t[i - 1]);
            }
        }
    }
}

/// The frames of a header block: all on stream `id`, HEADERS first (with
/// END_STREAM as asked, no padding or priority), CONTINUATION after it,
/// END_HEADERS on the last only, each well formed for `max`, with at
/// most `m` bytes of fragment, and the fragments joined are the block.
pub proof fn lemma_header_frames(id: u32, block: Seq<u8>, end_stream: bool, m: nat, max: u32)
    requires
        1 <= m <= max <= MAX_MAX_FRAME_SIZE,
        1 <= id <= MAX_31,
    ensures
        ({
            let fs = header_frames(id, block, end_stream, m);
            &&& fs.len() >= 1
            &&& fs[0] matches spec::Frame::Headers { stream, end_stream: es, pad, priority, .. }
                && stream == id && es == end_stream && pad is None && priority is None
            &&& forall|i: int| 1 <= i < fs.len() ==> (#[trigger] fs[i]) is Continuation
            &&& forall|i: int| 0 <= i < fs.len() ==> spec::stream_of(#[trigger] fs[i]) == id
                && spec::wf(fs[i], max)
                && frag_of(fs[i]).len() <= m
                && (end_headers_of(fs[i]) <==> i == fs.len() - 1)
            &&& frags(fs) == block
            &&& forall|rest: Seq<u8>| #[trigger] reads_as(ser_all(fs) + rest, max, fs, rest)
        }),
{
    let fs = header_frames(id, block, end_stream, m);
    if block.len() <= m {
        assert(fs.skip(1) =~= Seq::<spec::Frame>::empty());
        assert(frags(Seq::<spec::Frame>::empty()) == Seq::<u8>::empty());
        assert(frags(fs) == frag_of(fs[0]) + frags(fs.skip(1)));
        assert(frags(fs) =~= block);
    } else {
        let t = conts(id, block.skip(m as int), m);
        lemma_conts(id, block.skip(m as int), m, max);
        assert(fs.skip(1) =~= t);
        assert(block.take(m as int) + block.skip(m as int) =~= block);
        assert forall|i: int| 1 <= i < fs.len() implies (#[trigger] fs[i]) is Continuation by {
            assert(fs[i] == t[i - 1]);
        }
        assert forall|i: int| 0 <= i < fs.len() implies spec::stream_of(#[trigger] fs[i]) == id
            && spec::wf(fs[i], max)
            && frag_of(fs[i]).len() <= m
            && (end_headers_of(fs[i]) <==> i == fs.len() - 1) by {
            if i > 0 {
                assert(fs[i] == t[i - 1]);
            }
        }
    }
    assert forall|rest: Seq<u8>| #[trigger] reads_as(ser_all(fs) + rest, max, fs, rest) by {
        lemma_reads_as(fs, max, rest);
    }
}

proof fn lemma_ser_cons(f: spec::Frame, t: Seq<spec::Frame>)
    ensures
        ser_all(seq![f] + t) == spec::serialize(f) + ser_all(t),
{
    assert((seq![f] + t).skip(1) =~= t);
}

/// Appends the header block `block` of stream `id`, as
/// `header_frames` with fragments of [`CHUNK`] bytes, for a peer whose
/// SETTINGS_MAX_FRAME_SIZE is `max`.
pub fn write_headers(id: u32, block: &[u8], end_stream: bool, max: u32, out: &mut Vec<u8>)
    requires
        1 <= id <= MAX_31,
        MIN_MAX_FRAME_SIZE <= max <= MAX_MAX_FRAME_SIZE,
    ensures
        final(out)@ == old(out)@ + ser_all(header_frames(id, block@, end_stream, CHUNK as nat)),
{
    let ghost m = CHUNK as nat;
    let ghost all = header_frames(id, block@, end_stream, m);
    proof {
        lemma_header_frames(id, block@, end_stream, m, max);
    }
    let first = if block.len() <= CHUNK { block.len() } else { CHUNK };
    let a = slice_subrange(block, 0, first);
    let f = Frame::Headers { stream: id, end_stream, end_headers: block.len() <= CHUNK, pad: None, priority: None, fragment: a };
    proof {
        if block@.len() <= m {
            assert(a@ =~= block@);
        } else {
            assert(a@ =~= block@.take(m as int));
        }
        assert(f@ == all[0]);
    }
    let ghost o0 = out@;
    let _ = verilith_h2::serialize(&f, max, out);
    let mut pos = first;
    proof {
        if block@.len() <= m {
            assert(all =~= seq![all[0]]);
            lemma_ser_cons(all[0], Seq::empty());
            assert(seq![all[0]] + Seq::<spec::Frame>::empty() =~= seq![all[0]]);
            assert(block@.skip(pos as int) =~= Seq::<u8>::empty());
        } else {
            assert(all =~= seq![all[0]] + conts(id, block@.skip(m as int), m));
            lemma_ser_cons(all[0], conts(id, block@.skip(m as int), m));
        }
    }
    while pos < block.len()
        invariant
            1 <= id <= MAX_31,
            MIN_MAX_FRAME_SIZE <= max <= MAX_MAX_FRAME_SIZE,
            m == CHUNK as nat,
            pos <= block@.len(),
            o0 + ser_all(all) == out@ + ser_all(conts(id, block@.skip(pos as int), m)),
        decreases block.len() - pos,
    {
        let left = block.len() - pos;
        let k = if left <= CHUNK { left } else { CHUNK };
        let c = slice_subrange(block, pos, pos + k);
        let f = Frame::Continuation { stream: id, end_headers: left <= CHUNK, fragment: c };
        let ghost r = block@.skip(pos as int);
        let ghost cs = conts(id, r, m);
        proof {
            lemma_conts(id, r, m, max);
            if left <= CHUNK {
                assert(c@ =~= r);
                assert(cs =~= seq![f@]);
                lemma_ser_cons(f@, Seq::empty());
                assert(seq![f@] + Seq::<spec::Frame>::empty() =~= seq![f@]);
                assert(block@.skip((pos + k) as int) =~= Seq::<u8>::empty());
            } else {
                assert(c@ =~= r.take(m as int));
                assert(r.skip(m as int) =~= block@.skip((pos + k) as int));
                assert(cs =~= seq![f@] + conts(id, block@.skip((pos + k) as int), m));
                lemma_ser_cons(f@, conts(id, block@.skip((pos + k) as int), m));
            }
            assert(spec::wf(f@, max)) by {
                assert(cs[0] == f@);
            }
        }
        let ghost before = out@;
        let _ = verilith_h2::serialize(&f, max, out);
        proof {
            assert(out@ + ser_all(conts(id, block@.skip((pos + k) as int), m)) =~= before + ser_all(cs));
        }
        pos += k;
    }
    proof {
        assert(block@.skip(pos as int) =~= Seq::<u8>::empty());
        assert(conts(id, Seq::<u8>::empty(), m) =~= Seq::<spec::Frame>::empty());
        assert(out@ + ser_all(Seq::<spec::Frame>::empty()) =~= out@);
    }
}

/// A DATA frame on stream `id` with `data`, END_STREAM if `end`, no
/// padding.
pub open spec fn data_frame(id: u32, end: bool, data: Seq<u8>) -> spec::Frame {
    spec::Frame::Data { stream: id, end_stream: end, pad: None, data }
}

/// The sum of `ns`.
pub open spec fn sum(ns: Seq<nat>) -> nat
    decreases ns.len(),
{
    if ns.len() == 0 { 0 } else { ns[0] + sum(ns.skip(1)) }
}

/// `body` in DATA frames of `ns[0]`, `ns[1]`, ... bytes, END_STREAM on
/// the last.
pub open spec fn data_frames(id: u32, body: Seq<u8>, ns: Seq<nat>) -> Seq<spec::Frame>
    decreases ns.len(),
{
    if ns.len() == 0 {
        seq![]
    } else {
        seq![data_frame(id, ns.len() == 1, body.take(ns[0] as int))]
            + data_frames(id, body.skip(ns[0] as int), ns.skip(1))
    }
}

pub open spec fn data_of(f: spec::Frame) -> Seq<u8> {
    match f {
        spec::Frame::Data { data, .. } => data,
        _ => Seq::empty(),
    }
}

/// The data of `fs`, joined.
pub open spec fn datas(fs: Seq<spec::Frame>) -> Seq<u8>
    decreases fs.len(),
{
    if fs.len() == 0 {
        Seq::empty()
    } else {
        data_of(fs[0]) + datas(fs.skip(1))
    }
}

pub open spec fn end_stream_of(f: spec::Frame) -> bool {
    match f {
        spec::Frame::Data { end_stream, .. } => end_stream,
        spec::Frame::Headers { end_stream, .. } => end_stream,
        _ => false,
    }
}

proof fn lemma_data_frames(id: u32, body: Seq<u8>, ns: Seq<nat>, max: u32)
    requires
        1 <= id <= MAX_31,
        MIN_MAX_FRAME_SIZE <= max <= MAX_MAX_FRAME_SIZE,
        sum(ns) == body.len(),
        forall|i: int| 0 <= i < ns.len() ==> 1 <= #[trigger] ns[i] <= CHUNK,
    ensures
        ({
            let fs = data_frames(id, body, ns);
            &&& fs.len() == ns.len()
            &&& datas(fs) == body
            &&& forall|i: int| 0 <= i < fs.len() ==> (#[trigger] fs[i]) is Data
                && spec::stream_of(fs[i]) == id
                && spec::wf(fs[i], max)
                && (end_stream_of(fs[i]) <==> i == fs.len() - 1)
        }),
    decreases ns.len(),
{
    let fs = data_frames(id, body, ns);
    if ns.len() > 0 {
        let t = ns.skip(1);
        assert forall|i: int| 0 <= i < t.len() implies 1 <= #[trigger] t[i] <= CHUNK by {
            assert(t[i] == ns[i + 1]);
        }
        let k = ns[0];
        let rest = data_frames(id, body.skip(k as int), t);
        lemma_data_frames(id, body.skip(k as int), t, max);
        let f = data_frame(id, ns.len() == 1, body.take(k as int));
        assert(fs =~= seq![f] + rest);
        assert(fs.skip(1) =~= rest);
        assert(datas(fs) == data_of(f) + datas(rest));
        assert(body.take(k as int) + body.skip(k as int) =~= body);
        lemma_data_frame(id, ns.len() == 1, body.take(k as int), max);
        assert forall|i: int| 0 <= i < fs.len() implies (#[trigger] fs[i]) is Data
            && spec::stream_of(fs[i]) == id
            && spec::wf(fs[i], max)
            && (end_stream_of(fs[i]) <==> i == fs.len() - 1) by {
            if i > 0 {
                assert(fs[i] == rest[i - 1]);
            }
        }
    } else {
        assert(body =~= Seq::<u8>::empty());
    }
}

/// The response on a stream, as the core sends it: the header block in
/// HEADERS and CONTINUATION frames, then the body in DATA frames of
/// `ns[0]`, `ns[1]`, ... bytes (each [`Core::send_data`]'s `n`, in
/// order; frames of other streams may come between them on the wire).
///
/// [`Core::send_data`]: crate::h2core::Core::send_data
pub open spec fn response(id: u32, block: Seq<u8>, body: Seq<u8>, ns: Seq<nat>) -> Seq<spec::Frame> {
    header_frames(id, block, body.len() == 0, CHUNK as nat) + data_frames(id, body, ns)
}

/// The response round trip: a receiver following verilith-h2's
/// specification reads [`response`]'s bytes back as exactly its frames,
/// whatever follows them; the fragments of the frames up to END_HEADERS
/// are the block; the DATA frames after it carry exactly the body; and
/// END_STREAM is on the last DATA frame, or on HEADERS when the body is
/// empty (§8.1), and nowhere else.
pub proof fn lemma_response_rt(id: u32, block: Seq<u8>, body: Seq<u8>, ns: Seq<nat>, max: u32, rest: Seq<u8>)
    requires
        1 <= id <= MAX_31,
        MIN_MAX_FRAME_SIZE <= max <= MAX_MAX_FRAME_SIZE,
        sum(ns) == body.len(),
        forall|i: int| 0 <= i < ns.len() ==> 1 <= #[trigger] ns[i] <= CHUNK,
    ensures
        ({
            let fs = response(id, block, body, ns);
            let h = header_frames(id, block, body.len() == 0, CHUNK as nat);
            &&& reads_as(ser_all(fs) + rest, max, fs, rest)
            &&& fs.take(h.len() as int) == h && frags(h) == block
            &&& fs.skip(h.len() as int) == data_frames(id, body, ns)
            &&& datas(fs.skip(h.len() as int)) == body
            &&& forall|i: int| 0 <= i < fs.len() ==> spec::stream_of(#[trigger] fs[i]) == id
                && (end_stream_of(fs[i]) <==> if body.len() == 0 { i == 0 } else { i == fs.len() - 1 })
        }),
{
    let m = CHUNK as nat;
    let h = header_frames(id, block, body.len() == 0, m);
    let d = data_frames(id, body, ns);
    let fs = h + d;
    lemma_header_frames(id, block, body.len() == 0, m, max);
    lemma_data_frames(id, body, ns, max);
    if body.len() > 0 {
        assert(ns.len() > 0);
    } else if ns.len() > 0 {
        assert(ns[0] >= 1);
        assert(sum(ns) >= ns[0]);
    }
    assert forall|i: int| 0 <= i < fs.len() implies spec::wf(#[trigger] fs[i], max) by {
        if i >= h.len() {
            assert(fs[i] == d[i - h.len()]);
        }
    }
    lemma_reads_as(fs, max, rest);
    assert(fs.take(h.len() as int) =~= h);
    assert(fs.skip(h.len() as int) =~= d);
    assert forall|i: int| 0 <= i < fs.len() implies spec::stream_of(#[trigger] fs[i]) == id
        && (end_stream_of(fs[i]) <==> if body.len() == 0 { i == 0 } else { i == fs.len() - 1 }) by {
        if i >= h.len() {
            assert(fs[i] == d[i - h.len()]);
        } else if i > 0 {
            assert(fs[i] is Continuation);
        }
    }
}

/// [`data_head`]'s bytes, then the `n` bytes of `data`, are exactly the
/// DATA frame with `data`, well formed for any peer.
pub proof fn lemma_data_frame(id: u32, end: bool, data: Seq<u8>, max: u32)
    requires
        1 <= id <= MAX_31,
        data.len() <= CHUNK,
        MIN_MAX_FRAME_SIZE <= max <= MAX_MAX_FRAME_SIZE,
    ensures
        spec::enc_head(data.len() as u32, spec::DATA, if end { 1u8 } else { 0u8 }, id) + data
            == spec::serialize(data_frame(id, end, data)),
        spec::wf(data_frame(id, end, data), max),
        reads_as(spec::serialize(data_frame(id, end, data)), max, seq![data_frame(id, end, data)], Seq::empty()),
{
    let f = data_frame(id, end, data);
    assert(spec::payload_of(f) =~= data);
    let b: u8 = if end { 1u8 } else { 0u8 };
    assert(b | 0u8 == b) by (bit_vector);
    assert(spec::flags_of(f) == b);
    lemma_reads_as(seq![f], max, Seq::empty());
    lemma_ser_cons(f, Seq::empty());
    assert(seq![f] + Seq::<spec::Frame>::empty() =~= seq![f]);
    assert(spec::serialize(f) + Seq::<u8>::empty() =~= spec::serialize(f));
}

/// The 9-byte header of a DATA frame of `n` bytes on stream `id`.
#[inline(always)]
pub fn data_head(id: u32, n: usize, end: bool) -> (r: [u8; 9])
    requires
        1 <= id <= MAX_31,
        n <= CHUNK,
    ensures
        r@ == spec::enc_head(n as u32, spec::DATA, if end { 1u8 } else { 0u8 }, id),
{
    match verilith_h2::encode_head(n as u32, 0, if end { 1 } else { 0 }, id) {
        Some(h) => h,
        None => {
            // Not reached: n and id are in range.
            [0u8; 9]
        },
    }
}

} // verus!
