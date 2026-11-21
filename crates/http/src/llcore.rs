//! The decisions of the llhttp drop-in (`llhttp.rs`), verified.
//!
//! `llhttp.rs` drives callbacks, spans and pausing, and is not verified.
//! Everything it decides about a head, though, it decides by calling this
//! module: which machine byte a wire byte stands for (`lstep_exec`), what a
//! request line without a version means (`l09_exec`), which runs of bytes
//! can be stepped at once (`lbulk_exec`), how the body of a complete head
//! is framed (`body_exec`), and how its state is packed into `llhttp_t`
//! between calls (`ph_pack`, `cs_pack`).
//!
//! The spec is `lstep`: one step of the adapter on one byte *of the wire*.
//! It differs from the verified machine's `stream::hstep` in two places,
//! both llhttp behaviours that Node.js's tests rely on:
//!
//! - llhttp takes the versions 0.9, 1.0, 1.1 and 2.0. For `HTTP/0.9` and
//!   `HTTP/2.0` the machine reads `HTTP/1.0` in their place (`ver_byte`),
//!   so it checks the rest of the head as HTTP/1.0's, and `LS::ver`
//!   records the real version.
//! - A request line that ends after the target (`GET /\r\n`) is llhttp's
//!   HTTP/0.9 request. The machine reads ` HTTP/1.0` before the CR (`l09`),
//!   unless the target is itself `HTTP/1.x` (`LS::tv`).
//!
//! `llproof.rs` proves what follows from that:
//!
//! - A head accepted with `ver == VER_1X` is a head the machine accepts,
//!   byte for byte, so the theorems of `stream_proof.rs` and `unique.rs`
//!   hold for it as they stand.
//! - A head accepted with any other version is one that *no* recipient in
//!   the model of `rfc.rs` accepts. So it cannot be read two ways either.
use crate::chunked::CState;
use crate::framing::*;
use crate::llproof::*;
use crate::parse::*;
use crate::spec::*;
use crate::stream::*;
use crate::stream_proof::*;
use crate::unique_chunked::*;
use vstd::prelude::*;

verus! {

/// HTTP/1.0 or HTTP/1.1: the machine read the wire's own bytes.
pub const VER_1X: u8 = 0;

/// HTTP/0.9, written out or implied by a request line with no version.
pub const VER_09: u8 = 1;

/// HTTP/2.0.
pub const VER_20: u8 = 2;

/// `LS::tv` once the target cannot be an HTTP/1.x version.
pub const TV_DEAD: u8 = 15;

/// The adapter's state in a head: the machine's, the version when it is
/// not 1.x, and how much of the request target matches `HTTP/1.` and a
/// digit so far (8: all of it; `TV_DEAD`: it does not).
#[derive(Clone, Copy)]
pub struct LS {
    pub hs: HS,
    pub ver: u8,
    pub tv: u8,
}

pub open spec fn is_ver_phase(ph: Ph) -> bool {
    ph is RVer || ph is SVer
}

pub open spec fn ver_k(ph: Ph) -> u8 {
    match ph {
        Ph::RVer { k } => k,
        Ph::SVer { k } => k,
        _ => 0,
    }
}

/// The byte the machine reads for wire byte `c`, and the version after
/// it. `None`: a version llhttp rejects.
pub open spec fn ver_byte(ph: Ph, ver: u8, c: u8) -> Option<(u8, u8)> {
    if !is_ver_phase(ph) {
        Some((c, ver))
    } else if ver_k(ph) == 5 {
        if c == 0x30 {
            Some((0x31u8, VER_09))
        } else if c == 0x32 {
            Some((0x31u8, VER_20))
        } else {
            Some((c, ver))
        }
    } else if ver_k(ph) == 7 {
        if ver == VER_09 {
            if c == 0x39 {
                Some((0x30u8, ver))
            } else {
                None
            }
        } else if ver == VER_20 {
            if c == 0x30 {
                Some((0x30u8, ver))
            } else {
                None
            }
        } else if c == 0x30 || c == 0x31 || !is_digit(c) {
            Some((c, ver))
        } else {
            None
        }
    } else {
        Some((c, ver))
    }
}

/// `tv` after target byte `c`.
pub open spec fn tv_next(tv: u8, c: u8) -> u8 {
    if tv < 7 && c == http1_prefix()[tv as int] {
        (tv + 1) as u8
    } else if tv == 7 && is_digit(c) {
        8
    } else {
        TV_DEAD
    }
}

/// One step on a wire byte other than the CR of a request line with no
/// version.
pub open spec fn lnorm(s: LS, c: u8) -> Option<LS> {
    match ver_byte(s.hs.ph, s.ver, c) {
        None => None,
        Some((m, v)) => match hstep(s.hs, m) {
            None => None,
            Some(h) => Some(
                LS {
                    hs: h,
                    ver: v,
                    tv: if h.ph == Ph::Target {
                        tv_next(
                            if s.hs.ph == Ph::Target0 {
                                0
                            } else {
                                s.tv
                            },
                            c,
                        )
                    } else {
                        s.tv
                    },
                },
            ),
        },
    }
}

/// A request line that ends after the target: the state after the version
/// llhttp implies, ` HTTP/1.0` as the machine reads it. `None` if the
/// target is itself an HTTP/1.x version, which every parser that splits
/// the line on spaces would take for the version.
pub open spec fn l09(s: LS) -> Option<LS> {
    if s.tv == 8 {
        None
    } else {
        Some(LS { hs: HS { ph: Ph::RCr, minor: 0, ..s.hs }, ver: VER_09, tv: s.tv })
    }
}

/// One step of the adapter on wire byte `c`.
pub open spec fn lstep(s: LS, c: u8) -> Option<LS> {
    if s.hs.ph == Ph::Target && c == CR {
        match l09(s) {
            None => None,
            Some(t) => lnorm(t, c),
        }
    } else {
        lnorm(s, c)
    }
}

/// The adapter run over the wire from position `j`, stopping at `Done`:
/// the final state and the position it stops at.
pub open spec fn lr(s: LS, w: Seq<u8>, j: int) -> Option<(LS, int)>
    decreases w.len() - j,
{
    if j < 0 || j >= w.len() || s.hs.ph is Done {
        Some((s, j))
    } else {
        match lstep(s, w[j]) {
            None => None,
            Some(s2) => lr(s2, w, j + 1),
        }
    }
}

/// The adapter stepped over `w[i..e]`, without stopping.
pub open spec fn lfold(s: LS, w: Seq<u8>, i: int, e: int) -> Option<LS>
    decreases e - i,
{
    if i >= e {
        Some(s)
    } else {
        match lstep(s, w[i]) {
            None => None,
            Some(s2) => lfold(s2, w, i + 1, e),
        }
    }
}

pub open spec fn lstart(req: bool) -> LS {
    LS {
        hs: if req {
            request_start_with(false)
        } else {
            response_start()
        },
        ver: VER_1X,
        tv: 0,
    }
}

/// ` HTTP/1.0`, the bytes `l09` stands for.
pub open spec fn http09_feed() -> Seq<u8> {
    seq![SP] + http1_prefix() + seq![0x30u8]
}

/// `l09` is the machine reading ` HTTP/1.0`.
pub proof fn lemma_l09_is_feed(s: HS)
    requires
        s.ph == Ph::Target,
    ensures
        hfold(s, http09_feed(), 0, 9) == Some(HS { ph: Ph::RCr, minor: 0, ..s }),
{
    let f = http09_feed();
    assert(f.len() == 9);
    assert(f[0] == SP && f[1] == 0x48 && f[2] == 0x54 && f[3] == 0x54 && f[4] == 0x50 && f[5] == 0x2F && f[6]
        == 0x31 && f[7] == 0x2E && f[8] == 0x30);
    let s0 = HS { ph: Ph::RVer { k: 0 }, ..s };
    let s1 = HS { ph: Ph::RVer { k: 1 }, ..s };
    let s2 = HS { ph: Ph::RVer { k: 2 }, ..s };
    let s3 = HS { ph: Ph::RVer { k: 3 }, ..s };
    let s4 = HS { ph: Ph::RVer { k: 4 }, ..s };
    let s5 = HS { ph: Ph::RVer { k: 5 }, ..s };
    let s6 = HS { ph: Ph::RVer { k: 6 }, ..s };
    let s7 = HS { ph: Ph::RVer { k: 7 }, ..s };
    let s8 = HS { ph: Ph::RCr, minor: 0, ..s };
    assert(hstep(s, f[0]) == Some(s0));
    assert(hstep(s0, f[1]) == Some(s1));
    assert(hstep(s1, f[2]) == Some(s2));
    assert(hstep(s2, f[3]) == Some(s3));
    assert(hstep(s3, f[4]) == Some(s4));
    assert(hstep(s4, f[5]) == Some(s5));
    assert(hstep(s5, f[6]) == Some(s6));
    assert(hstep(s6, f[7]) == Some(s7));
    assert(is_digit(f[8]));
    assert(hstep(s7, f[8]) == Some(s8));
    assert(hfold(s8, f, 9, 9) == Some(s8));
    assert(hfold(s7, f, 8, 9) == Some(s8));
    assert(hfold(s6, f, 7, 9) == Some(s8));
    assert(hfold(s5, f, 6, 9) == Some(s8));
    assert(hfold(s4, f, 5, 9) == Some(s8));
    assert(hfold(s3, f, 4, 9) == Some(s8));
    assert(hfold(s2, f, 3, 9) == Some(s8));
    assert(hfold(s1, f, 2, 9) == Some(s8));
    assert(hfold(s0, f, 1, 9) == Some(s8));
}

// ---------------------------------------------------------------------------
// Executable steps
// ---------------------------------------------------------------------------

/// `ver_byte`.
#[inline(always)]
pub fn ver_byte_exec(ph: Ph, ver: u8, c: u8) -> (r: Option<(u8, u8)>)
    ensures
        r == ver_byte(ph, ver, c),
{
    let k = match ph {
        Ph::RVer { k } => k,
        Ph::SVer { k } => k,
        _ => return Some((c, ver)),
    };
    if k == 5 {
        if c == 0x30 {
            Some((0x31u8, VER_09))
        } else if c == 0x32 {
            Some((0x31u8, VER_20))
        } else {
            Some((c, ver))
        }
    } else if k == 7 {
        if ver == VER_09 {
            if c == 0x39 {
                Some((0x30u8, ver))
            } else {
                None
            }
        } else if ver == VER_20 {
            if c == 0x30 {
                Some((0x30u8, ver))
            } else {
                None
            }
        } else if c == 0x30 || c == 0x31 || !(0x30 <= c && c <= 0x39) {
            Some((c, ver))
        } else {
            None
        }
    } else {
        Some((c, ver))
    }
}

/// `tv_next`.
#[inline(always)]
pub fn tv_next_exec(tv: u8, c: u8) -> (r: u8)
    ensures
        r == tv_next(tv, c),
{
    let http1: [u8; 7] = [0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E];
    proof {
        assert(http1@ =~= http1_prefix());
    }
    if tv < 7 && c == http1[tv as usize] {
        tv + 1
    } else if tv == 7 && 0x30 <= c && c <= 0x39 {
        8
    } else {
        TV_DEAD
    }
}

/// What `lstep_exec` found.
pub enum Stepped {
    /// The step, and the byte the machine read.
    Next(LS, u8),
    /// llhttp does not take this version.
    BadVersion,
    /// The machine rejects the byte.
    Invalid,
}

/// One step (spec `lnorm`): any wire byte but the CR that ends a request
/// line with no version, which `l09_exec` handles first.
#[inline(always)]
pub fn lstep_exec(s: LS, c: u8) -> (r: Stepped)
    requires
        hs_inv(s.hs),
    ensures
        match r {
            Stepped::Next(t, m) => lnorm(s, c) == Some(t) && hs_inv(t.hs) && ver_byte(s.hs.ph, s.ver, c) == Some(
                (m, t.ver),
            ) && hstep(s.hs, m) == Some(t.hs),
            Stepped::BadVersion => lnorm(s, c) is None && ver_byte(s.hs.ph, s.ver, c) is None,
            Stepped::Invalid => lnorm(s, c) is None && ver_byte(s.hs.ph, s.ver, c) is Some && hstep(
                s.hs,
                ver_byte(s.hs.ph, s.ver, c)->Some_0.0,
            ) is None,
        },
{
    let (m, v) = match ver_byte_exec(s.hs.ph, s.ver, c) {
        Some(x) => x,
        None => return Stepped::BadVersion,
    };
    let h = match hstep_exec(s.hs, m) {
        Some(h) => h,
        None => return Stepped::Invalid,
    };
    let tv = match h.ph {
        Ph::Target => {
            let from = match s.hs.ph {
                Ph::Target0 => 0,
                _ => s.tv,
            };
            tv_next_exec(from, c)
        },
        _ => s.tv,
    };
    Stepped::Next(LS { hs: h, ver: v, tv }, m)
}

/// A request line that ends after the target (spec `l09`). The caller
/// then steps the CR.
pub fn l09_exec(s: LS) -> (r: Option<LS>)
    requires
        s.hs.ph == Ph::Target,
        hs_inv(s.hs),
    ensures
        r == l09(s),
        r matches Some(t) ==> hs_inv(t.hs),
{
    if s.tv == 8 {
        None
    } else {
        Some(LS { hs: HS { ph: Ph::RCr, minor: 0, ..s.hs }, ver: VER_09, tv: s.tv })
    }
}

/// Steps over a run of bytes at once (`stream::hbulk_exec`), where each
/// step is the machine's own: not in a version, and in a target only once
/// it cannot be a version (`tv` is dead and stays dead). The result is
/// what stepping each wire byte gives.
#[inline(always)]
pub fn lbulk_exec(s: &LS, d: &[u8], i: usize) -> (r: (LS, usize))
    requires
        i <= d@.len(),
        hs_inv(s.hs),
    ensures
        i <= r.1 <= d@.len(),
        lfold(*s, d@, i as int, r.1 as int) == Some(r.0),
        hs_inv(r.0.hs),
        r.0.ver == s.ver,
        r.0.tv == s.tv,
        hfold(s.hs, d@, i as int, r.1 as int) == Some(r.0.hs),
{
    let ok = match s.hs.ph {
        Ph::Target => s.tv == TV_DEAD,
        Ph::Reason => true,
        Ph::Val { v } => match v {
            VK::Other => true,
            VK::Host => true,
            _ => false,
        },
        Ph::Name { .. } => true,
        _ => false,
    };
    if !ok {
        proof {
            assert(hfold(s.hs, d@, i as int, i as int) == Some(s.hs));
        }
        return (*s, i);
    }
    let (h, e) = hbulk_exec(&s.hs, d, i);
    let t = LS { hs: h, ver: s.ver, tv: s.tv };
    proof {
        lemma_bulk(*s, d@, i as int, e as int);
    }
    (t, e)
}

/// The phases `lbulk_exec` steps in bulk: no version, and no target that
/// could still be one.
pub open spec fn bulk_phase(s: LS) -> bool {
    match s.hs.ph {
        Ph::Target => s.tv == TV_DEAD,
        Ph::Reason => true,
        Ph::Val { v } => v is Other || v is Host,
        Ph::Name { .. } => true,
        _ => false,
    }
}

/// Over bytes `hbulk_exec` steps in bulk, the adapter's step is the
/// machine's.
proof fn lemma_bulk(s: LS, w: Seq<u8>, i: int, e: int)
    requires
        0 <= i <= e <= w.len(),
        bulk_phase(s),
        forall|k: int| i <= k < e ==> bulk_byte(s.hs.ph, #[trigger] w[k]),
    ensures
        hfold(s.hs, w, i, e) matches Some(h) && lfold(s, w, i, e) == Some(LS { hs: h, ver: s.ver, tv: s.tv }),
    decreases e - i,
{
    if i < e {
        let c = w[i];
        assert(bulk_byte(s.hs.ph, c));
        assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
        let h = hstep(s.hs, c)->Some_0;
        assert(hstep(s.hs, c) is Some);
        let t = LS { hs: h, ver: s.ver, tv: s.tv };
        if s.hs.ph == Ph::Target {
            assert(c != CR);
            assert(tv_next(TV_DEAD, c) == TV_DEAD);
        }
        assert(lstep(s, c) == Some(t));
        assert(bulk_phase(t));
        assert forall|k: int| i + 1 <= k < e implies bulk_byte(h.ph, #[trigger] w[k]) by {
            assert(bulk_byte(s.hs.ph, w[k]));
        }
        lemma_bulk(t, w, i + 1, e);
    }
}

// ---------------------------------------------------------------------------
// After a complete head
// ---------------------------------------------------------------------------

/// A complete request head the machine rejects only because its
/// Transfer-Encoding does not end in `chunked` (with no Content-Length).
/// llhttp calls `on_headers_complete` for such a head before it fails, so
/// the adapter reports the head too; `after_head` then never gives it a
/// body.
pub open spec fn deferred_te(s: HS) -> bool {
    s.req && s.f.te.present && !s.f.te.chunked_last && s.f.cl is None && (s.host ==> hosts_ok(s.f, s.minor))
}

pub fn deferred_te_exec(s: &HS) -> (r: bool)
    ensures
        r == deferred_te(*s),
        r ==> request_framing_x(s.f, s.minor) is None,
{
    s.req && s.f.te.present && !s.f.te.chunked_last && s.f.cl.is_none() && (!s.host || !(s.f.hosts > 1 || (s.minor
        >= 1 && s.f.hosts == 0)))
}

/// What follows a complete head.
pub enum After {
    /// The message is rejected.
    Reject,
    /// The rest of the stream is another protocol: llhttp's own rules
    /// (`llhttp__after_headers_complete` returned 1) found an upgrade or a
    /// CONNECT.
    Upgrade,
    /// A body with this framing.
    Body(Body),
}

/// What follows the head `hs`. `bad_te`: the head is a `deferred_te` one.
/// `how` is what llhttp's `after_headers_complete` returned (1: upgrade),
/// and `skip` whether `on_headers_complete` asked for the body to be
/// skipped, which is how a caller says a response answers a HEAD request.
///
/// The framing is the verified one. llhttp's rules choose only between it
/// and no body at all (an upgrade, or a skipped body), and a `deferred_te`
/// head gets no framing: it is rejected unless it upgrades or is skipped.
pub open spec fn after_head(hs: HS, bad_te: bool, how: i32, skip: bool) -> After {
    if how == 1 {
        After::Upgrade
    } else if hs.req {
        if skip {
            After::Body(Body::Empty)
        } else if bad_te {
            After::Reject
        } else {
            match request_framing_x(hs.f, hs.minor) {
                Some(b) => After::Body(b),
                None => After::Reject,
            }
        }
    } else {
        match response_framing_x(hs.f, hs.minor, hs.status, skip, false) {
            Some(b) => After::Body(b),
            None => After::Reject,
        }
    }
}

pub fn after_head_exec(hs: &HS, bad_te: bool, how: i32, skip: bool) -> (r: After)
    ensures
        r == after_head(*hs, bad_te, how, skip),
        // A head the machine accepted is never rejected here.
        hs.ph is Done && head_ok(*hs) && !bad_te ==> !(r is Reject),
{
    if how == 1 {
        After::Upgrade
    } else if hs.req {
        if skip {
            After::Body(Body::Empty)
        } else if bad_te {
            After::Reject
        } else {
            match request_framing_x_exec(&hs.f, hs.minor) {
                Some(b) => After::Body(b),
                None => After::Reject,
            }
        }
    } else {
        match response_framing_x_exec(&hs.f, hs.minor, hs.status, skip, false) {
            Some(b) => After::Body(b),
            None => After::Reject,
        }
    }
}

// ---------------------------------------------------------------------------
// The machine state between calls
// ---------------------------------------------------------------------------

/// States `ph_pack` keeps: a Transfer-Encoding coding counts at most 8
/// bytes, as the machine's own steps do (`lemma_packable_step`).
pub open spec fn vk_packable(v: VK) -> bool {
    v matches VK::TeTok { k, .. } ==> k <= 8
}

pub open spec fn ph_packable(ph: Ph) -> bool {
    match ph {
        Ph::Val { v } => vk_packable(v),
        Ph::ValLf { v } => vk_packable(v),
        _ => true,
    }
}

/// The machine only reaches states `ph_pack` keeps.
pub proof fn lemma_packable_step(s: HS, c: u8)
    requires
        ph_packable(s.ph),
        hstep(s, c) is Some,
    ensures
        ph_packable(hstep(s, c)->Some_0.ph),
{
    let t = hstep(s, c)->Some_0;
    match s.ph {
        Ph::Val { v } => {
            if c != CR {
                assert(vstep(v, c) is Some ==> vk_packable(vstep(v, c)->Some_0));
            }
        },
        Ph::Name { m } => {
            if c == COLON {
                assert(name_end(s.f, m) is Some ==> vk_packable(name_end(s.f, m)->Some_0));
            }
        },
        _ => {},
    }
}

fn vk_pack(v: VK) -> (r: (u8, u8, u64))
    requires
        vk_packable(v),
    ensures
        vk_unpack_spec(r.0, r.1, r.2) == v,
{
    assert(0u8 & 15 == 0 && 1u8 & 15 == 1 && 2u8 & 15 == 2 && 3u8 & 15 == 3 && 4u8 & 15 == 4 && 5u8 & 15 == 5 && 7u8
        & 15 == 7) by (bit_vector);
    match v {
        VK::Other => (0, 0, 0),
        VK::Host => (1, 0, 0),
        VK::ClLead => (2, 0, 0),
        VK::ClDig { n, cnt } => (3, cnt, n),
        VK::ClTrail { n } => (4, 0, n),
        VK::TeSep { last } => (5, last as u8, 0),
        VK::TeTok { k, m } => {
            assert((6u8 | (k << 4)) & 15 == 6 && (6u8 | (k << 4)) >> 4 == k) by (bit_vector)
                requires
                    k <= 8,
            ;
            (6 | (k << 4), m as u8, 0)
        },
        VK::TeAfter { last } => (7, last as u8, 0),
    }
}

pub open spec fn vk_unpack_spec(t: u8, b: u8, w: u64) -> VK {
    let tag = t & 15;
    if tag == 0 {
        VK::Other
    } else if tag == 1 {
        VK::Host
    } else if tag == 2 {
        VK::ClLead
    } else if tag == 3 {
        VK::ClDig { n: w, cnt: b }
    } else if tag == 4 {
        VK::ClTrail { n: w }
    } else if tag == 5 {
        VK::TeSep { last: b != 0 }
    } else if tag == 6 {
        VK::TeTok { k: t >> 4, m: b != 0 }
    } else {
        VK::TeAfter { last: b != 0 }
    }
}

fn vk_unpack(t: u8, b: u8, w: u64) -> (r: VK)
    ensures
        r == vk_unpack_spec(t, b, w),
{
    let tag = t & 15;
    if tag == 0 {
        VK::Other
    } else if tag == 1 {
        VK::Host
    } else if tag == 2 {
        VK::ClLead
    } else if tag == 3 {
        VK::ClDig { n: w, cnt: b }
    } else if tag == 4 {
        VK::ClTrail { n: w }
    } else if tag == 5 {
        VK::TeSep { last: b != 0 }
    } else if tag == 6 {
        VK::TeTok { k: t >> 4, m: b != 0 }
    } else {
        VK::TeAfter { last: b != 0 }
    }
}

/// The phase as `(tag, small, bits, wide)`, for the private fields of
/// `llhttp_t`. `ph_unpack` gives the phase back.
pub fn ph_pack(ph: Ph) -> (r: (u8, u8, u8, u64))
    requires
        ph_packable(ph),
    ensures
        ph_unpack_spec(r.0, r.1, r.2, r.3) == ph,
{
    match ph {
        Ph::RStart => (0, 0, 0, 0),
        Ph::RStartLf => (1, 0, 0, 0),
        Ph::Method => (2, 0, 0, 0),
        Ph::Target0 => (3, 0, 0, 0),
        Ph::Target => (4, 0, 0, 0),
        Ph::RVer { k } => (5, k, 0, 0),
        Ph::RCr => (6, 0, 0, 0),
        Ph::RLf => (7, 0, 0, 0),
        Ph::SVer { k } => (8, k, 0, 0),
        Ph::SSp => (9, 0, 0, 0),
        Ph::Code { k } => (10, k, 0, 0),
        Ph::Reason => (11, 0, 0, 0),
        Ph::SLf => (12, 0, 0, 0),
        Ph::Line => (13, 0, 0, 0),
        Ph::EndLf => (14, 0, 0, 0),
        Ph::Name { m } => {
            let (b0, b1, b2, b3, b4) = (m.cl, m.te, m.host, m.cld, m.ted);
            let c: u8 = if b0 { 1 } else { 0 };
            let t: u8 = if b1 { 2 } else { 0 };
            let h: u8 = if b2 { 4 } else { 0 };
            let cd: u8 = if b3 { 8 } else { 0 };
            let td: u8 = if b4 { 16 } else { 0 };
            let bits = c | t | h | cd | td;
            assert((bits & 1 != 0) == b0 && (bits & 2 != 0) == b1 && (bits & 4 != 0) == b2 && (bits & 8 != 0) == b3
                && (bits & 16 != 0) == b4) by (bit_vector)
                requires
                    bits == c | t | h | cd | td,
                    c == (if b0 { 1u8 } else { 0u8 }),
                    t == (if b1 { 2u8 } else { 0u8 }),
                    h == (if b2 { 4u8 } else { 0u8 }),
                    cd == (if b3 { 8u8 } else { 0u8 }),
                    td == (if b4 { 16u8 } else { 0u8 }),
            ;
            (15, m.len, bits, 0)
        },
        Ph::Val { v } => {
            let (t, b, w) = vk_pack(v);
            (16, t, b, w)
        },
        Ph::ValLf { v } => {
            let (t, b, w) = vk_pack(v);
            (17, t, b, w)
        },
        Ph::Done => (18, 0, 0, 0),
    }
}

pub open spec fn ph_unpack_spec(tag: u8, small: u8, bits: u8, wide: u64) -> Ph {
    if tag == 0 {
        Ph::RStart
    } else if tag == 1 {
        Ph::RStartLf
    } else if tag == 2 {
        Ph::Method
    } else if tag == 3 {
        Ph::Target0
    } else if tag == 4 {
        Ph::Target
    } else if tag == 5 {
        Ph::RVer { k: small }
    } else if tag == 6 {
        Ph::RCr
    } else if tag == 7 {
        Ph::RLf
    } else if tag == 8 {
        Ph::SVer { k: small }
    } else if tag == 9 {
        Ph::SSp
    } else if tag == 10 {
        Ph::Code { k: small }
    } else if tag == 11 {
        Ph::Reason
    } else if tag == 12 {
        Ph::SLf
    } else if tag == 13 {
        Ph::Line
    } else if tag == 14 {
        Ph::EndLf
    } else if tag == 15 {
        Ph::Name {
            m: NameM {
                len: small,
                cl: bits & 1 != 0,
                te: bits & 2 != 0,
                host: bits & 4 != 0,
                cld: bits & 8 != 0,
                ted: bits & 16 != 0,
            },
        }
    } else if tag == 16 {
        Ph::Val { v: vk_unpack_spec(small, bits, wide) }
    } else if tag == 17 {
        Ph::ValLf { v: vk_unpack_spec(small, bits, wide) }
    } else {
        Ph::Done
    }
}

pub fn ph_unpack(tag: u8, small: u8, bits: u8, wide: u64) -> (r: Ph)
    ensures
        r == ph_unpack_spec(tag, small, bits, wide),
{
    if tag == 0 {
        Ph::RStart
    } else if tag == 1 {
        Ph::RStartLf
    } else if tag == 2 {
        Ph::Method
    } else if tag == 3 {
        Ph::Target0
    } else if tag == 4 {
        Ph::Target
    } else if tag == 5 {
        Ph::RVer { k: small }
    } else if tag == 6 {
        Ph::RCr
    } else if tag == 7 {
        Ph::RLf
    } else if tag == 8 {
        Ph::SVer { k: small }
    } else if tag == 9 {
        Ph::SSp
    } else if tag == 10 {
        Ph::Code { k: small }
    } else if tag == 11 {
        Ph::Reason
    } else if tag == 12 {
        Ph::SLf
    } else if tag == 13 {
        Ph::Line
    } else if tag == 14 {
        Ph::EndLf
    } else if tag == 15 {
        Ph::Name {
            m: NameM {
                len: small,
                cl: bits & 1 != 0,
                te: bits & 2 != 0,
                host: bits & 4 != 0,
                cld: bits & 8 != 0,
                ted: bits & 16 != 0,
            },
        }
    } else if tag == 16 {
        Ph::Val { v: vk_unpack(small, bits, wide) }
    } else if tag == 17 {
        Ph::ValLf { v: vk_unpack(small, bits, wide) }
    } else {
        Ph::Done
    }
}

/// The chunked decoder's state as `(tag, n)`. `cs_unpack` gives it back.
pub fn cs_pack(c: CState) -> (r: (u8, u64))
    ensures
        cs_unpack_spec(r.0, r.1) == c,
{
    match c {
        CState::SizeStart => (0, 0),
        CState::Size { n } => (1, n),
        CState::SizeWs { n } => (2, n),
        CState::ExtPreName { n } => (3, n),
        CState::ExtName { n } => (4, n),
        CState::ExtNameWs { n } => (5, n),
        CState::ExtPreVal { n } => (6, n),
        CState::ExtTok { n } => (7, n),
        CState::ExtQ { n } => (8, n),
        CState::ExtQEsc { n } => (9, n),
        CState::ExtValEnd { n } => (10, n),
        CState::ExtValWs { n } => (11, n),
        CState::SizeLf { n } => (12, n),
        CState::Data { left } => (13, left),
        CState::DataCr => (14, 0),
        CState::DataLf => (15, 0),
        CState::TrStart => (16, 0),
        CState::TrName => (17, 0),
        CState::TrValue => (18, 0),
        CState::TrLf => (19, 0),
        CState::EndLf => (20, 0),
        CState::Done => (21, 0),
    }
}

pub open spec fn cs_unpack_spec(t: u8, n: u64) -> CState {
    if t == 0 {
        CState::SizeStart
    } else if t == 1 {
        CState::Size { n }
    } else if t == 2 {
        CState::SizeWs { n }
    } else if t == 3 {
        CState::ExtPreName { n }
    } else if t == 4 {
        CState::ExtName { n }
    } else if t == 5 {
        CState::ExtNameWs { n }
    } else if t == 6 {
        CState::ExtPreVal { n }
    } else if t == 7 {
        CState::ExtTok { n }
    } else if t == 8 {
        CState::ExtQ { n }
    } else if t == 9 {
        CState::ExtQEsc { n }
    } else if t == 10 {
        CState::ExtValEnd { n }
    } else if t == 11 {
        CState::ExtValWs { n }
    } else if t == 12 {
        CState::SizeLf { n }
    } else if t == 13 {
        CState::Data { left: n }
    } else if t == 14 {
        CState::DataCr
    } else if t == 15 {
        CState::DataLf
    } else if t == 16 {
        CState::TrStart
    } else if t == 17 {
        CState::TrName
    } else if t == 18 {
        CState::TrValue
    } else if t == 19 {
        CState::TrLf
    } else if t == 20 {
        CState::EndLf
    } else {
        CState::Done
    }
}

pub fn cs_unpack(t: u8, n: u64) -> (r: CState)
    ensures
        r == cs_unpack_spec(t, n),
{
    if t == 0 {
        CState::SizeStart
    } else if t == 1 {
        CState::Size { n }
    } else if t == 2 {
        CState::SizeWs { n }
    } else if t == 3 {
        CState::ExtPreName { n }
    } else if t == 4 {
        CState::ExtName { n }
    } else if t == 5 {
        CState::ExtNameWs { n }
    } else if t == 6 {
        CState::ExtPreVal { n }
    } else if t == 7 {
        CState::ExtTok { n }
    } else if t == 8 {
        CState::ExtQ { n }
    } else if t == 9 {
        CState::ExtQEsc { n }
    } else if t == 10 {
        CState::ExtValEnd { n }
    } else if t == 11 {
        CState::ExtValWs { n }
    } else if t == 12 {
        CState::SizeLf { n }
    } else if t == 13 {
        CState::Data { left: n }
    } else if t == 14 {
        CState::DataCr
    } else if t == 15 {
        CState::DataLf
    } else if t == 16 {
        CState::TrStart
    } else if t == 17 {
        CState::TrName
    } else if t == 18 {
        CState::TrValue
    } else if t == 19 {
        CState::TrLf
    } else if t == 20 {
        CState::EndLf
    } else {
        CState::Done
    }
}

// ---------------------------------------------------------------------------
// A whole head at once
// ---------------------------------------------------------------------------

/// A head taken by the one-shot parser.
pub struct Fast {
    /// Where the head ends.
    pub end: usize,
    /// The machine's state at the end of the head.
    pub done: HS,
    /// The method (requests).
    pub method: Span,
    /// The request target, or the reason phrase.
    pub span: Span,
}

/// The whole head at the start of `b`, parsed by the verified one-shot
/// parser (`parse.rs`) when it is an HTTP/1.0 or 1.1 head. The result is
/// the adapter's own run over those bytes: the same head end and the same
/// final state, so the same framing.
#[inline(always)]
pub fn fast_head_exec(b: &[u8], req: bool, max: usize, hs: &mut Vec<Header>) -> (r: Option<Fast>)
    ensures
        hdrs_ok(final(hs)@, b@.len() as int),
        r matches Some(h) ==> {
            &&& h.end <= b@.len()
            &&& h.done.ph is Done
            &&& head_ok(h.done)
            &&& hs_inv(h.done)
            &&& lr(lstart(req), b@, 0) matches Some((t, e)) && t.hs == h.done && t.ver == VER_1X && e == h.end
            &&& req ==> h.method.start <= h.method.end <= h.span.start <= h.span.end <= h.end
            &&& !req ==> h.span.start <= h.span.end <= h.end
        },
{
    let mut fx = None;
    if req {
        let (out, _) = request_fx(b, max, hs, true, &mut fx);
        let (l, e) = match out {
            Out::Done(l, e) => (l, e),
            _ => return None,
        };
        if l.minor > 1 {
            return None;
        }
        let f = match fx {
            Some(f) => f,
            None => return None,
        };
        let done = HS { ph: Ph::Done, f, minor: l.minor, status: 0, req: true, host: false };
        if !head_ok_exec(&done) {
            return None;
        }
        if !(l.method.start <= l.method.end && l.method.end <= l.target.start && l.target.start <= l.target.end
            && l.target.end <= e) {
            return None;
        }
        proof {
            let w = b@;
            let mx = if max as nat >= w.len() { max as nat } else { w.len() };
            let q = parse_request(w, max as nat)->Done_0;
            let g = fields_of(w, q.headers)->Some_0;
            assert(request_framing(g, q.minor) == request_framing_x(f, l.minor));
            theorem_stream_request_complete(w, max as nat, false);
            lemma_fast_request(w, max as nat, done);
        }
        Some(Fast { end: e, done, method: l.method, span: l.target })
    } else {
        let (out, _) = response_fx(b, max, hs, true, &mut fx);
        let (l, e) = match out {
            Out::Done(l, e) => (l, e),
            _ => return None,
        };
        if l.minor > 1 {
            return None;
        }
        let f = match fx {
            Some(f) => f,
            None => return None,
        };
        let done = HS { ph: Ph::Done, f, minor: l.minor, status: l.status, req: false, host: false };
        if !head_ok_exec(&done) {
            return None;
        }
        if !(l.reason.start <= l.reason.end && l.reason.end <= e) {
            return None;
        }
        proof {
            let w = b@;
            let q = parse_response(w, max as nat)->Done_0;
            let g = fields_of(w, q.headers)->Some_0;
            assert(response_framing(g, q.minor, q.status, false, false) == response_framing_x(
                f,
                l.minor,
                l.status,
                false,
                false,
            ));
            theorem_stream_response_complete(w, max as nat, false, false);
            lemma_fast_response(w, max as nat, done);
        }
        Some(Fast { end: e, done, method: Span { start: 0, end: 0 }, span: l.reason })
    }
}

} // verus!
