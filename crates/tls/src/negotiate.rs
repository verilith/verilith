//! Negotiation, proven to compute exactly `spec::negotiate`, and server
//! name checking, proven to compute exactly `spec::valid_host_name`.
//!
//! Every loop is over the ClientHello (each byte at most once per server
//! preference) or over the server's own preference lists, so the work is
//! at most the ClientHello's length times the length of the longest
//! preference list, plus that list's length.
use crate::hello::*;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// Whether the 2-byte values in `b[s..e]` include `x`.
fn contains_u16(b: &[u8], s: usize, e: usize, x: u16) -> (r: bool)
    requires
        s <= e <= b@.len(),
        (e - s) % 2 == 0,
    ensures
        r == u16s(b@, s as int, e as int).contains(x),
{
    let ghost l = u16s(b@, s as int, e as int);
    let mut p = s;
    while p < e
        invariant
            s <= p <= e <= b@.len(),
            (p - s) % 2 == 0,
            (e - s) % 2 == 0,
            l == u16s(b@, s as int, e as int),
            forall|j: int| 0 <= j < (p - s) / 2 ==> l[j] != x,
        decreases e - p,
    {
        let v = (b[p] as u16) * 256 + b[p + 1] as u16;
        proof {
            let j = (p - s) / 2;
            assert(s + 2 * j == p);
            assert(l[j] == be16(b@, p as int) as u16);
        }
        if v == x {
            proof {
                assert(l[(p - s) / 2] == x);
            }
            return true;
        }
        p = p + 2;
    }
    proof {
        assert(p == e);
        assert forall|j: int| 0 <= j < l.len() implies l[j] != x by {}
    }
    false
}

/// `first_in(prefs, 0, u16s(b, s, e))`.
fn first_in_x(prefs: &[u16], b: &[u8], s: usize, e: usize) -> (r: Option<u16>)
    requires
        s <= e <= b@.len(),
        (e - s) % 2 == 0,
    ensures
        r == first_in(prefs@, 0, u16s(b@, s as int, e as int)),
{
    let ghost off = u16s(b@, s as int, e as int);
    let mut i: usize = 0;
    while i < prefs.len()
        invariant
            i <= prefs@.len(),
            s <= e <= b@.len(),
            (e - s) % 2 == 0,
            off == u16s(b@, s as int, e as int),
            first_in(prefs@, 0, off) == first_in(prefs@, i as int, off),
        decreases prefs@.len() - i,
    {
        if contains_u16(b, s, e, prefs[i]) {
            return Some(prefs[i]);
        }
        i = i + 1;
    }
    None
}

/// `find_share(b, pos, end, g)`.
fn find_share_x(b: &[u8], pos: usize, end: usize, g: u16) -> (r: Option<Span>)
    requires
        end <= b@.len(),
    ensures
        ov(r) == find_share(b@, pos as int, end as int, g),
        r matches Some(sp) ==> sp.start <= sp.end <= end,
{
    let mut p = pos;
    loop
        invariant
            end <= b@.len(),
            find_share(b@, pos as int, end as int, g) == find_share(b@, p as int, end as int, g),
        decreases end - p,
    {
        if p >= end || end - p < 4 {
            return None;
        }
        let v = match vec16_x(b, p + 2, end) {
            Some(v) => v,
            None => return None,
        };
        let t = (b[p] as u16) * 256 + b[p + 1] as u16;
        proof {
            assert(t as nat == be16(b@, p as int));
        }
        if t == g {
            return Some(v);
        }
        p = v.end;
    }
}

/// `pick_share(b, s, e, groups, 0)`.
fn pick_share_x(b: &[u8], s: usize, e: usize, groups: &[u16]) -> (r: Option<(u16, Span)>)
    requires
        e <= b@.len(),
    ensures
        match r {
            None => pick_share(b@, s as int, e as int, groups@, 0) is None,
            Some((g, sp)) => pick_share(b@, s as int, e as int, groups@, 0) == Some((g, sp@))
                && sp.start <= sp.end <= e,
        },
{
    let mut i: usize = 0;
    while i < groups.len()
        invariant
            i <= groups@.len(),
            e <= b@.len(),
            pick_share(b@, s as int, e as int, groups@, 0) == pick_share(
                b@,
                s as int,
                e as int,
                groups@,
                i as int,
            ),
        decreases groups@.len() - i,
    {
        match find_share_x(b, s, e, groups[i]) {
            Some(sp) => return Some((groups[i], sp)),
            None => {},
        }
        i = i + 1;
    }
    None
}

/// Whether `a[as_..ae]` and `b[bs..be]` are the same bytes.
fn same_bytes(a: &[u8], as_: usize, ae: usize, b: &[u8], bs: usize, be: usize) -> (r: bool)
    requires
        as_ <= ae <= a@.len(),
        bs <= be <= b@.len(),
    ensures
        r == (a@.subrange(as_ as int, ae as int) == b@.subrange(bs as int, be as int)),
{
    if ae - as_ != be - bs {
        proof {
            assert(a@.subrange(as_ as int, ae as int).len() != b@.subrange(
                bs as int,
                be as int,
            ).len());
        }
        return false;
    }
    let n = ae - as_;
    let ghost x = a@.subrange(as_ as int, ae as int);
    let ghost y = b@.subrange(bs as int, be as int);
    let mut k: usize = 0;
    while k < n
        invariant
            n == ae - as_,
            n == be - bs,
            as_ <= ae <= a@.len(),
            bs <= be <= b@.len(),
            k <= n,
            x == a@.subrange(as_ as int, ae as int),
            y == b@.subrange(bs as int, be as int),
            forall|j: int| 0 <= j < k ==> #[trigger] x[j] == y[j],
        decreases n - k,
    {
        if a[as_ + k] != b[bs + k] {
            proof {
                assert(x[k as int] != y[k as int]);
            }
            return false;
        }
        proof {
            assert(x[k as int] == y[k as int]);
        }
        k = k + 1;
    }
    proof {
        assert(x =~= y);
    }
    true
}

/// `alpn_has(b, pos, end, cfg[ns..ne])`.
fn alpn_has_x(b: &[u8], pos: usize, end: usize, cfg: &[u8], ns: usize, ne: usize) -> (r: Option<
    Span,
>)
    requires
        end <= b@.len(),
        ns <= ne <= cfg@.len(),
    ensures
        ov(r) == alpn_has(b@, pos as int, end as int, cfg@.subrange(ns as int, ne as int)),
{
    let ghost name = cfg@.subrange(ns as int, ne as int);
    let mut p = pos;
    loop
        invariant
            end <= b@.len(),
            ns <= ne <= cfg@.len(),
            name == cfg@.subrange(ns as int, ne as int),
            alpn_has(b@, pos as int, end as int, name) == alpn_has(b@, p as int, end as int, name),
        decreases end - p,
    {
        if p >= end {
            return None;
        }
        let v = match vec8_x(b, p, end) {
            Some(v) => v,
            None => return None,
        };
        if same_bytes(b, v.start, v.end, cfg, ns, ne) {
            return Some(v);
        }
        p = v.end;
    }
}

/// `pick_alpn(cfg, 0, cfg.len(), b, cs, ce)`.
fn pick_alpn_x(cfg: &[u8], b: &[u8], cs: usize, ce: usize) -> (r: Option<(Span, Span)>)
    requires
        ce <= b@.len(),
    ensures
        ov2(r) == pick_alpn(cfg@, 0, cfg@.len() as int, b@, cs as int, ce as int),
{
    let n = cfg.len();
    let mut p: usize = 0;
    loop
        invariant
            n == cfg@.len(),
            ce <= b@.len(),
            pick_alpn(cfg@, 0, n as int, b@, cs as int, ce as int) == pick_alpn(
                cfg@,
                p as int,
                n as int,
                b@,
                cs as int,
                ce as int,
            ),
        decreases n - p,
    {
        if p >= n {
            return None;
        }
        let v = match vec8_x(cfg, p, n) {
            Some(v) => v,
            None => return None,
        };
        match alpn_has_x(b, cs, ce, cfg, v.start, v.end) {
            Some(c) => return Some((v, c)),
            None => {},
        }
        p = v.end;
    }
}

/// What the server chose for a full handshake (`spec::SpecChoice`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Choice {
    pub suite: u16,
    pub group: u16,
    /// The client's key_exchange for `group`, in the ClientHello body.
    pub share: Span,
    pub signature_scheme: u16,
    /// The protocol: its span in the server's ALPN list, and in the
    /// ClientHello body.
    pub alpn: Option<(Span, Span)>,
}

/// Why negotiation failed: the alert to send (§6.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NegAlert {
    ProtocolVersion,
    IllegalParameter,
    MissingExtension,
    HandshakeFailure,
    NoApplicationProtocol,
}

impl NegAlert {
    pub open spec fn spec(self) -> SpecNegAlert {
        match self {
            NegAlert::ProtocolVersion => SpecNegAlert::ProtocolVersion,
            NegAlert::IllegalParameter => SpecNegAlert::IllegalParameter,
            NegAlert::MissingExtension => SpecNegAlert::MissingExtension,
            NegAlert::HandshakeFailure => SpecNegAlert::HandshakeFailure,
            NegAlert::NoApplicationProtocol => SpecNegAlert::NoApplicationProtocol,
        }
    }

    /// The `AlertDescription` code (§6).
    pub fn code(self) -> u8 {
        match self {
            NegAlert::ProtocolVersion => 70,
            NegAlert::IllegalParameter => 47,
            NegAlert::MissingExtension => 109,
            NegAlert::HandshakeFailure => 40,
            NegAlert::NoApplicationProtocol => 120,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Outcome {
    Accept(Choice),
    Retry { suite: u16, group: u16 },
    Reject(NegAlert),
}

impl Outcome {
    pub open spec fn view(self) -> SpecOutcome {
        match self {
            Outcome::Accept(c) => SpecOutcome::Accept(
                SpecChoice {
                    suite: c.suite,
                    group: c.group,
                    share: c.share@,
                    signature_scheme: c.signature_scheme,
                    alpn: ov2(c.alpn),
                },
            ),
            Outcome::Retry { suite, group } => SpecOutcome::Retry { suite, group },
            Outcome::Reject(a) => SpecOutcome::Reject(a.spec()),
        }
    }
}

/// The server's choices for a full handshake, from a ClientHello `h`
/// that `ClientHello::parse` returned for `b` (`spec::negotiate`).
/// `alpn` is the server's protocols in ALPN wire form
/// (`protocol_name_list`'s contents), most preferred first.
pub fn negotiate(
    b: &[u8],
    h: &ClientHello,
    suites: &[u16],
    groups: &[u16],
    sigs: &[u16],
    alpn: &[u8],
) -> (r: Outcome)
    requires
        h.spans_ok(b@.len()),
    ensures
        forall|s: SpecHello|
            parse_client_hello(b@) == Ok::<SpecHello, SpecAlert>(s) && #[trigger] h.models(s) ==> r@
                == crate::spec::negotiate(b@, s, suites@, groups@, sigs@, alpn@),
{
    let (vs, ve) = match h.supported_versions {
        None => return Outcome::Reject(NegAlert::ProtocolVersion),
        Some(sp) => (sp.start, sp.end),
    };
    if !contains_u16(b, vs, ve, TLS13) {
        return Outcome::Reject(NegAlert::ProtocolVersion);
    }
    let cm = h.compression_methods;
    if !(cm.end - cm.start == 1 && b[cm.start] == 0) {
        return Outcome::Reject(NegAlert::IllegalParameter);
    }
    let (sa, sg, ks) = match (h.signature_algorithms, h.supported_groups, h.key_shares) {
        (Some(sa), Some(sg), Some(ks)) => (sa, sg, ks),
        _ => return Outcome::Reject(NegAlert::MissingExtension),
    };
    let suite = match first_in_x(suites, b, h.cipher_suites.start, h.cipher_suites.end) {
        Some(x) => x,
        None => return Outcome::Reject(NegAlert::HandshakeFailure),
    };
    let sig = match first_in_x(sigs, b, sa.start, sa.end) {
        Some(x) => x,
        None => return Outcome::Reject(NegAlert::HandshakeFailure),
    };
    let a = match h.alpn {
        None => None,
        Some(sp) => match pick_alpn_x(alpn, b, sp.start, sp.end) {
            Some(x) => Some(x),
            None => return Outcome::Reject(NegAlert::NoApplicationProtocol),
        },
    };
    match pick_share_x(b, ks.start, ks.end, groups) {
        Some((g, sp)) => Outcome::Accept(
            Choice { suite, group: g, share: sp, signature_scheme: sig, alpn: a },
        ),
        None => match first_in_x(groups, b, sg.start, sg.end) {
            Some(g) => Outcome::Retry { suite, group: g },
            None => Outcome::Reject(NegAlert::HandshakeFailure),
        },
    }
}

// ---------------------------------------------------------------------------
// Server names
// ---------------------------------------------------------------------------

#[inline(always)]
fn host_char_x(c: u8) -> (r: bool)
    ensures
        r == host_char(c),
{
    (0x30 <= c && c <= 0x39) || (0x41 <= c && c <= 0x5a) || (0x61 <= c && c <= 0x7a) || c == 0x2d
        || c == 0x5f
}

/// Whether `h` is a host name a server can match against its
/// certificates (`spec::valid_host_name`): what RFC 6066 allows in
/// server_name, no IP address literals, no final dot.
pub fn valid_host_name_x(h: &[u8]) -> (r: bool)
    ensures
        r == valid_host_name(h@),
{
    let n = h.len();
    if n < 1 || n > 253 {
        return false;
    }
    let mut i: usize = 0;
    let mut start: usize = 0;
    let mut digits = true;
    loop
        invariant
            n == h@.len(),
            1 <= n <= 253,
            start <= i <= n,
            digits == all_digits(h@, start as int, i as int),
            labels_ok(h@, 0, 0) == labels_ok(h@, i as int, start as int),
        decreases n - i,
    {
        if i == n {
            let ok = i - start >= 1 && i - start <= 63 && h[start] != 0x2d && h[i - 1] != 0x2d
                && !digits;
            return ok;
        }
        let c = h[i];
        if c == 0x2e {
            let ok = i - start >= 1 && i - start <= 63 && h[start] != 0x2d && h[i - 1] != 0x2d;
            if !ok {
                return false;
            }
            start = i + 1;
            digits = true;
        } else {
            if !host_char_x(c) {
                return false;
            }
            digits = digits && 0x30 <= c && c <= 0x39;
            proof {
                if !digits {
                    if all_digits(h@, start as int, i + 1) {
                        assert(is_digit(h@[i as int]));
                    }
                }
            }
        }
        i = i + 1;
    }
}

} // verus!
