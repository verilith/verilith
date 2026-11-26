//! The ClientHello parser, proven to compute exactly
//! `spec::parse_client_hello`, with no panics, no out-of-bounds access, no
//! overflow, no allocation (unless a ClientHello has more than 16 extension
//! types or key share groups of 64 or more, see `seen.rs`), and at most
//! `12n + 2100` steps for an `n`-byte body.
//!
//! It makes one pass over the extensions, noting where each one it
//! interprets is, then checks those. It copies nothing: what it returns
//! are spans of the input.
use crate::seen::*;
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// A half-open span `[start, end)` of the input.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl View for Span {
    type V = (int, int);

    open spec fn view(&self) -> (int, int) {
        (self.start as int, self.end as int)
    }
}

impl Span {
    /// The bytes of the span.
    #[inline(always)]
    pub fn of<'a>(&self, b: &'a [u8]) -> (r: &'a [u8])
        requires
            self.start <= self.end <= b@.len(),
        ensures
            r@ == b@.subrange(self.start as int, self.end as int),
    {
        vstd::slice::slice_subrange(b, self.start, self.end)
    }

    /// Its length.
    #[inline(always)]
    pub fn len(&self) -> (r: usize)
        requires
            self.start <= self.end,
        ensures
            r == self.end - self.start,
    {
        self.end - self.start
    }
}

pub open spec fn ov(o: Option<Span>) -> Option<(int, int)> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}

pub open spec fn ov2(o: Option<(Span, Span)>) -> Option<((int, int), (int, int))> {
    match o {
        Some((a, c)) => Some((a@, c@)),
        None => None,
    }
}

/// The alerts this crate can ask a connection to send (§6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Alert {
    DecodeError,
    IllegalParameter,
}

impl Alert {
    pub open spec fn spec(self) -> SpecAlert {
        match self {
            Alert::DecodeError => SpecAlert::Decode,
            Alert::IllegalParameter => SpecAlert::Illegal,
        }
    }

    /// The `AlertDescription` code (§6).
    pub fn code(self) -> u8 {
        match self {
            Alert::DecodeError => 50,
            Alert::IllegalParameter => 47,
        }
    }
}

// ---------------------------------------------------------------------------
// Vectors
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn vec8_x(b: &[u8], pos: usize, end: usize) -> (r: Option<Span>)
    requires
        end <= b@.len(),
    ensures
        ov(r) == vec8(b@, pos as int, end as int),
{
    if pos >= end {
        return None;
    }
    let l = b[pos] as usize;
    if l > end - pos - 1 {
        return None;
    }
    Some(Span { start: pos + 1, end: pos + 1 + l })
}

#[inline(always)]
pub fn vec16_x(b: &[u8], pos: usize, end: usize) -> (r: Option<Span>)
    requires
        end <= b@.len(),
    ensures
        ov(r) == vec16(b@, pos as int, end as int),
{
    if pos >= end || end - pos < 2 {
        return None;
    }
    let l = (b[pos] as usize) * 256 + b[pos + 1] as usize;
    if l > end - pos - 2 {
        return None;
    }
    Some(Span { start: pos + 2, end: pos + 2 + l })
}

#[inline(always)]
pub fn whole16_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == whole16(b@, s as int, e as int),
{
    match vec16_x(b, s, e) {
        Some(l) => if l.end == e {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

#[inline(always)]
pub fn whole8_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == whole8(b@, s as int, e as int),
{
    match vec8_x(b, s, e) {
        Some(l) => if l.end == e {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Extension contents
// ---------------------------------------------------------------------------

#[inline(always)]
fn u16_list_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == u16_list(b@, s as int, e as int),
{
    match whole16_x(b, s, e) {
        Some(l) => if (l.end - l.start) % 2 == 0 && l.end - l.start >= 2 {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

#[inline(always)]
fn versions_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == versions_list(b@, s as int, e as int),
{
    match whole8_x(b, s, e) {
        Some(l) => if (l.end - l.start) % 2 == 0 && l.end - l.start >= 2 {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

#[inline(always)]
fn psk_modes_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == psk_modes_list(b@, s as int, e as int),
{
    match whole8_x(b, s, e) {
        Some(l) => if l.end - l.start >= 1 {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

#[inline(always)]
fn cookie_x(b: &[u8], s: usize, e: usize) -> (r: Option<Span>)
    requires
        e <= b@.len(),
    ensures
        ov(r) == cookie_value(b@, s as int, e as int),
{
    match whole16_x(b, s, e) {
        Some(l) => if l.end - l.start >= 1 {
            Some(l)
        } else {
            None
        },
        None => None,
    }
}

/// server_name: `Some(host)` when well formed, `host` the host name if any.
fn server_name_x(b: &[u8], s: usize, e: usize) -> (r: (Option<Option<Span>>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        r.0 matches Some(Some(sp)) ==> sp.start <= sp.end <= e,
        match r.0 {
            None => server_name(b@, s as int, e as int) is None,
            Some(h) => server_name(b@, s as int, e as int) == Some(ov(h)),
        },
        r.1@ <= e - s + 1,
{
    let l = match whole16_x(b, s, e) {
        Some(l) => l,
        None => return (None, Ghost(0)),
    };
    if l.end - l.start < 1 {
        return (None, Ghost(0));
    }
    let mut pos = l.start;
    let mut found: Option<Span> = None;
    let ghost mut steps: nat = 0;
    loop
        invariant
            l.start <= pos <= l.end,
            l.end == e,
            e <= b@.len(),
            s + 2 == l.start,
            l.end - l.start >= 1,
            whole16(b@, s as int, e as int) == Some((l.start as int, l.end as int)),
            steps <= pos - l.start,
            found matches Some(f) ==> f.start <= f.end <= pos,
            server_names(b@, l.start as int, l.end as int, None) == server_names(
                b@,
                pos as int,
                l.end as int,
                ov(found),
            ),
        decreases l.end - pos,
    {
        if pos == l.end {
            return (Some(found), Ghost(steps));
        }
        proof {
            steps = steps + 1;
        }
        let v = match vec16_x(b, pos + 1, l.end) {
            Some(v) => v,
            None => return (None, Ghost(steps)),
        };
        if b[pos] == 0 {
            if found.is_some() || v.end - v.start < 1 {
                return (None, Ghost(steps));
            }
            found = Some(v);
        }
        pos = v.end;
    }
}

/// The ALPN list's contents, when well formed.
fn alpn_x(b: &[u8], s: usize, e: usize) -> (r: (Option<Span>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        ov(r.0) == alpn_list(b@, s as int, e as int),
        r.1@ <= e - s + 1,
{
    let l = match whole16_x(b, s, e) {
        Some(l) => l,
        None => return (None, Ghost(0)),
    };
    if l.end - l.start < 2 {
        return (None, Ghost(0));
    }
    let mut pos = l.start;
    let ghost mut steps: nat = 0;
    loop
        invariant
            l.start <= pos <= l.end,
            l.end == e,
            e <= b@.len(),
            s + 2 == l.start,
            l.end - l.start >= 2,
            whole16(b@, s as int, e as int) == Some((l.start as int, l.end as int)),
            steps <= pos - l.start,
            protocol_names(b@, l.start as int, l.end as int) == protocol_names(
                b@,
                pos as int,
                l.end as int,
            ),
        decreases l.end - pos,
    {
        if pos == l.end {
            return (Some(l), Ghost(steps));
        }
        proof {
            steps = steps + 1;
        }
        let v = match vec8_x(b, pos, l.end) {
            Some(v) => v,
            None => return (None, Ghost(steps)),
        };
        if v.end - v.start < 1 {
            return (None, Ghost(steps));
        }
        pos = v.end;
    }
}

pub open spec fn app16(acc: Seq<u16>, r: Option<Seq<u16>>) -> Option<Seq<u16>> {
    match r {
        Some(x) => Some(acc + x),
        None => None,
    }
}

/// key_share: the span of its contents, and whether two entries share a
/// group.
fn key_share_x(b: &[u8], s: usize, e: usize) -> (r: (Option<(Span, bool)>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        match r.0 {
            None => key_share_list(b@, s as int, e as int) is None,
            Some((sp, dup)) => key_share_list(b@, s as int, e as int) matches Some((sp2, g)) && sp2
                == sp@ && dup == !groups_distinct(g),
        },
        5 * r.1@ <= 18 * (e - s) + 5 * (SPILL_STEPS + 1),
{
    let l = match whole16_x(b, s, e) {
        Some(l) => l,
        None => return (None, Ghost(0)),
    };
    let mut pos = l.start;
    let mut seen = Seen::new();
    let mut dup = false;
    let ghost mut acc: Seq<u16> = Seq::empty();
    let ghost mut steps: nat = 0;
    proof {
        assert(acc + key_share_entries(b@, pos as int, l.end as int).unwrap() =~= key_share_entries(
            b@,
            pos as int,
            l.end as int,
        ).unwrap());
    }
    loop
        invariant
            l.start <= pos <= l.end,
            l.end == e,
            e <= b@.len(),
            s + 2 == l.start,
            whole16(b@, s as int, e as int) == Some((l.start as int, l.end as int)),
            seen.wf(),
            forall|t: u16| #[trigger] seen@.contains(t) <==> acc.contains(t),
            dup == !groups_distinct(acc),
            5 * steps <= 18 * (pos - l.start) + (if seen.spilled() {
                5 * SPILL_STEPS
            } else {
                0
            }),
            key_share_entries(b@, l.start as int, l.end as int) == app16(
                acc,
                key_share_entries(b@, pos as int, l.end as int),
            ),
        decreases l.end - pos,
    {
        if pos == l.end {
            proof {
                assert(acc + Seq::<u16>::empty() =~= acc);
            }
            return (Some((l, dup)), Ghost(steps));
        }
        if l.end - pos < 2 {
            return (None, Ghost(steps));
        }
        let v = match vec16_x(b, pos + 2, l.end) {
            Some(v) => v,
            None => return (None, Ghost(steps)),
        };
        if v.end - v.start < 1 {
            return (None, Ghost(steps));
        }
        let g = (b[pos] as u16) * 256 + b[pos + 1] as u16;
        let ghost was_spilled = seen.spilled();
        let (had, cost) = seen.insert(g);
        proof {
            assert(g == be16(b@, pos as int) as u16);
            let rest = key_share_entries(b@, v.end as int, l.end as int);
            if let Some(rest) = rest {
                assert(acc + (seq![g] + rest) =~= acc.push(g) + rest);
            }
            assert forall|t: u16| #[trigger] seen@.contains(t) <==> acc.push(g).contains(t) by {
                if t == g {
                    assert(acc.push(g)[acc.len() as int] == g);
                } else if acc.push(g).contains(t) {
                    let i = choose|i: int| 0 <= i < acc.push(g).len() && acc.push(g)[i] == t;
                    assert(acc[i] == t);
                } else if acc.contains(t) {
                    let i = choose|i: int| 0 <= i < acc.len() && acc[i] == t;
                    assert(acc.push(g)[i] == t);
                }
            }
            let a2 = acc.push(g);
            if dup || had {
                if had {
                    let i = choose|i: int| 0 <= i < acc.len() && acc[i] == g;
                    assert(a2[i] == a2[acc.len() as int]);
                } else {
                    let (i, j) = choose|i: int, j: int| 0 <= i < j < acc.len() && acc[i] == acc[j];
                    assert(a2[i] == a2[j]);
                }
            } else {
                assert forall|i: int, j: int| 0 <= i < j < a2.len() implies a2[i] != a2[j] by {
                    if j == acc.len() {
                        assert(acc[i] != g) by {
                            if acc[i] == g {
                                assert(acc.contains(g));
                            }
                        }
                    } else {
                        assert(a2[i] == acc[i] && a2[j] == acc[j]);
                    }
                }
            }
            acc = a2;
            steps = steps + 1 + cost@;
        }
        dup = dup || had;
        pos = v.end;
    }
}

pub open spec fn add_count(k: nat, r: Option<nat>) -> Option<nat> {
    match r {
        Some(x) => Some(k + x),
        None => None,
    }
}

fn psk_identities_x(b: &[u8], s: usize, e: usize) -> (r: (Option<usize>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        match r.0 {
            None => psk_identities(b@, s as int, e as int) is None,
            Some(k) => psk_identities(b@, s as int, e as int) == Some(k as nat),
        },
        r.1@ <= e - s,
{
    let mut pos = s;
    let mut k: usize = 0;
    let ghost mut steps: nat = 0;
    loop
        invariant
            s <= pos <= e,
            e <= b@.len(),
            k <= pos - s,
            steps <= pos - s,
            psk_identities(b@, s as int, e as int) == add_count(
                k as nat,
                psk_identities(b@, pos as int, e as int),
            ),
        decreases e - pos,
    {
        if pos == e {
            return (Some(k), Ghost(steps));
        }
        let v = match vec16_x(b, pos, e) {
            Some(v) => v,
            None => return (None, Ghost(steps)),
        };
        if v.end - v.start < 1 || e - v.end < 4 {
            return (None, Ghost(steps));
        }
        proof {
            steps = steps + 1;
        }
        k = k + 1;
        pos = v.end + 4;
    }
}

fn psk_binders_x(b: &[u8], s: usize, e: usize) -> (r: (Option<usize>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        match r.0 {
            None => psk_binders(b@, s as int, e as int) is None,
            Some(k) => psk_binders(b@, s as int, e as int) == Some(k as nat),
        },
        r.1@ <= e - s,
{
    let mut pos = s;
    let mut k: usize = 0;
    let ghost mut steps: nat = 0;
    loop
        invariant
            s <= pos <= e,
            e <= b@.len(),
            k <= pos - s,
            steps <= pos - s,
            psk_binders(b@, s as int, e as int) == add_count(
                k as nat,
                psk_binders(b@, pos as int, e as int),
            ),
        decreases e - pos,
    {
        if pos == e {
            return (Some(k), Ghost(steps));
        }
        let v = match vec8_x(b, pos, e) {
            Some(v) => v,
            None => return (None, Ghost(steps)),
        };
        if v.end - v.start < 32 {
            return (None, Ghost(steps));
        }
        proof {
            steps = steps + 1;
        }
        k = k + 1;
        pos = v.end;
    }
}

fn offered_psks_x(b: &[u8], s: usize, e: usize) -> (r: (Option<(Span, Span)>, Ghost<nat>))
    requires
        s <= e <= b@.len(),
    ensures
        ov2(r.0) == offered_psks(b@, s as int, e as int),
        r.1@ <= e - s,
{
    let ids = match vec16_x(b, s, e) {
        Some(v) => v,
        None => return (None, Ghost(0)),
    };
    let bs = match whole16_x(b, ids.end, e) {
        Some(v) => v,
        None => return (None, Ghost(0)),
    };
    if ids.end - ids.start < 7 || bs.end - bs.start < 33 {
        return (None, Ghost(0));
    }
    let (k1, c1) = psk_identities_x(b, ids.start, ids.end);
    let (k2, c2) = psk_binders_x(b, bs.start, bs.end);
    match (k1, k2) {
        (Some(a), Some(c)) => if a == c {
            (Some((ids, bs)), Ghost(c1@ + c2@))
        } else {
            (None, Ghost(c1@ + c2@))
        },
        _ => (None, Ghost(c1@ + c2@)),
    }
}

// ---------------------------------------------------------------------------
// The extension block
// ---------------------------------------------------------------------------

/// The extension types with a slot in `ExtScan`, by slot.
pub open spec fn known(k: int) -> u16 {
    if k == 0 {
        EXT_SERVER_NAME
    } else if k == 1 {
        EXT_ALPN
    } else if k == 2 {
        EXT_SUPPORTED_VERSIONS
    } else if k == 3 {
        EXT_SUPPORTED_GROUPS
    } else if k == 4 {
        EXT_SIGNATURE_ALGORITHMS
    } else if k == 5 {
        EXT_SIGNATURE_ALGORITHMS_CERT
    } else if k == 6 {
        EXT_KEY_SHARE
    } else if k == 7 {
        EXT_PSK_KEY_EXCHANGE_MODES
    } else if k == 8 {
        EXT_PRE_SHARED_KEY
    } else if k == 9 {
        EXT_COOKIE
    } else if k == 10 {
        EXT_EARLY_DATA
    } else {
        EXT_ECH
    }
}

pub const SLOTS: usize = 12;

#[inline(always)]
fn slot_of(t: u16) -> (r: Option<usize>)
    ensures
        r matches Some(k) ==> k < SLOTS && known(k as int) == t,
        r is None ==> forall|k: int| 0 <= k < SLOTS ==> known(k) != t,
{
    match t {
        0 => Some(0),
        16 => Some(1),
        43 => Some(2),
        10 => Some(3),
        13 => Some(4),
        50 => Some(5),
        51 => Some(6),
        45 => Some(7),
        41 => Some(8),
        44 => Some(9),
        42 => Some(10),
        0xfe0d => Some(11),
        _ => None,
    }
}

pub open spec fn app_exts(acc: Seq<SpecExt>, r: Option<Seq<SpecExt>>) -> Option<Seq<SpecExt>> {
    match r {
        Some(x) => Some(acc + x),
        None => None,
    }
}

proof fn lemma_find_push(acc: Seq<SpecExt>, x: SpecExt, t: u16)
    ensures
        find_ext(acc.push(x), t) == (match find_ext(acc, t) {
            Some(d) => Some(d),
            None => if x.typ == t {
                Some(x.data)
            } else {
                None
            },
        }),
    decreases acc.len(),
{
    if acc.len() == 0 {
        assert(acc.push(x)[0] == x);
        assert(acc.push(x).drop_first() =~= Seq::<SpecExt>::empty());
    } else {
        assert(acc.push(x)[0] == acc[0]);
        assert(acc.push(x).drop_first() =~= acc.drop_first().push(x));
        lemma_find_push(acc.drop_first(), x, t);
    }
}

proof fn lemma_find_in(acc: Seq<SpecExt>, t: u16)
    ensures
        find_ext(acc, t) matches Some(d) ==> exists|i: int| 0 <= i < acc.len() && acc[i].data == d,
    decreases acc.len(),
{
    if acc.len() > 0 && acc[0].typ != t {
        lemma_find_in(acc.drop_first(), t);
        if let Some(d) = find_ext(acc, t) {
            let i = choose|i: int| 0 <= i < acc.drop_first().len() && acc.drop_first()[i].data == d;
            assert(acc[i + 1].data == d);
        }
    }
}

/// What one pass over the extension block finds.
pub struct ExtScan {
    /// The data of the first extension of each type `known(k)`.
    pub slots: [Option<Span>; SLOTS],
    /// Two extensions of one type, or pre_shared_key not last.
    pub illegal: bool,
}

fn scan_exts(b: &[u8], xs: usize, xe: usize) -> (r: (Option<ExtScan>, Ghost<Seq<SpecExt>>, Ghost<nat>))
    requires
        xs <= xe <= b@.len(),
    ensures
        r.0 is None ==> parse_exts(b@, xs as int, xe as int) is None,
        r.0 matches Some(x) ==> {
            &&& parse_exts(b@, xs as int, xe as int) == Some(r.1@)
            &&& forall|k: int|
                0 <= k < SLOTS ==> ov(#[trigger] x.slots@[k]) == find_ext(r.1@, known(k))
            &&& forall|k: int|
                0 <= k < SLOTS ==> (#[trigger] x.slots@[k] matches Some(sp) ==> xs <= sp.start
                    <= sp.end <= xe)
            &&& x.illegal == (!exts_distinct(r.1@) || !psk_last(r.1@))
        },
        4 * r.2@ <= 18 * (xe - xs) + 4 * (SPILL_STEPS + 1),
{
    let mut slots: [Option<Span>; SLOTS] = [None; SLOTS];
    let mut pos = xs;
    let mut seen = Seen::new();
    let mut dup = false;
    let mut psk_seen = false;
    let mut psk_bad = false;
    let ghost mut acc: Seq<SpecExt> = Seq::empty();
    let ghost mut steps: nat = 0;
    proof {
        if let Some(x) = parse_exts(b@, xs as int, xe as int) {
            assert(acc + x =~= x);
        }
    }
    loop
        invariant
            xs <= pos <= xe,
            xe <= b@.len(),
            seen.wf(),
            forall|t: u16| #[trigger] seen@.contains(t) <==> exists|i: int|
                0 <= i < acc.len() && acc[i].typ == t,
            forall|k: int| 0 <= k < SLOTS ==> ov(#[trigger] slots@[k]) == find_ext(acc, known(k)),
            forall|k: int|
                0 <= k < SLOTS ==> (#[trigger] slots@[k] matches Some(sp) ==> xs <= sp.start
                    <= sp.end <= pos),
            dup == !exts_distinct(acc),
            psk_seen == exists|i: int| 0 <= i < acc.len() && acc[i].typ == EXT_PRE_SHARED_KEY,
            psk_bad == !psk_last(acc),
            4 * steps <= 18 * (pos - xs) + (if seen.spilled() {
                4 * SPILL_STEPS
            } else {
                0
            }),
            parse_exts(b@, xs as int, xe as int) == app_exts(
                acc,
                parse_exts(b@, pos as int, xe as int),
            ),
        decreases xe - pos,
    {
        if pos == xe {
            proof {
                assert(acc + Seq::<SpecExt>::empty() =~= acc);
            }
            return (Some(ExtScan { slots, illegal: dup || psk_bad }), Ghost(acc), Ghost(steps));
        }
        if xe - pos < 2 {
            return (None, Ghost(acc), Ghost(steps));
        }
        let v = match vec16_x(b, pos + 2, xe) {
            Some(v) => v,
            None => return (None, Ghost(acc), Ghost(steps)),
        };
        let t = (b[pos] as u16) * 256 + b[pos + 1] as u16;
        let ghost x = SpecExt { typ: t, data: (v.start as int, v.end as int) };
        let ghost a2 = acc.push(x);
        let ghost old_slots = slots@;
        let ghost was_seen = seen@;
        let (had, cost) = seen.insert(t);
        let ghost mut k0: int = -1;
        if !had {
            match slot_of(t) {
                Some(k) => {
                    slots[k] = Some(v);
                    proof {
                        k0 = k as int;
                    }
                },
                None => {},
            }
        }
        proof {
            assert(t == be16(b@, pos as int) as u16);
            if let Some(rest) = parse_exts(b@, v.end as int, xe as int) {
                assert(acc + (seq![x] + rest) =~= a2 + rest);
            }
            assert(a2[acc.len() as int] == x);
            assert forall|i: int| 0 <= i < acc.len() implies a2[i] == acc[i] by {}
            assert forall|u: u16| #[trigger] seen@.contains(u) <==> exists|i: int|
                0 <= i < a2.len() && a2[i].typ == u by {
                if u == t {
                    assert(a2[acc.len() as int].typ == u);
                } else if exists|i: int| 0 <= i < a2.len() && a2[i].typ == u {
                    let i = choose|i: int| 0 <= i < a2.len() && a2[i].typ == u;
                    assert(acc[i].typ == u);
                } else if exists|i: int| 0 <= i < acc.len() && acc[i].typ == u {
                    let i = choose|i: int| 0 <= i < acc.len() && acc[i].typ == u;
                    assert(a2[i].typ == u);
                }
            }
            assert forall|k: int| 0 <= k < SLOTS implies ov(#[trigger] slots@[k]) == find_ext(
                a2,
                known(k),
            ) by {
                lemma_find_push(acc, x, known(k));
                if had {
                    let i = choose|i: int| 0 <= i < acc.len() && acc[i].typ == t;
                    lemma_find_none(acc, t, i);
                } else {
                    lemma_find_typ(acc, t);
                }
                if k != k0 {
                    assert(slots@[k] == old_slots[k]);
                    if k0 >= 0 && known(k) == t {
                        lemma_known_inj(k, k0);
                    }
                }
            }
            if dup || had {
                if had {
                    let i = choose|i: int| 0 <= i < acc.len() && acc[i].typ == t;
                    assert(a2[i].typ == a2[acc.len() as int].typ);
                } else {
                    let (i, j) = choose|i: int, j: int|
                        0 <= i < j < acc.len() && acc[i].typ == acc[j].typ;
                    assert(a2[i].typ == a2[j].typ);
                }
            } else {
                assert forall|i: int, j: int| 0 <= i < j < a2.len() implies a2[i].typ
                    != a2[j].typ by {
                    if j == acc.len() {
                        if acc[i].typ == t {
                            assert(seen@.contains(t));
                        }
                    } else {
                        assert(a2[i] == acc[i] && a2[j] == acc[j]);
                    }
                }
            }
            // pre_shared_key is last in `a2` exactly when it is not in `acc`.
            if psk_seen {
                let i = choose|i: int| 0 <= i < acc.len() && acc[i].typ == EXT_PRE_SHARED_KEY;
                assert(a2[i].typ == EXT_PRE_SHARED_KEY);
            } else {
                assert forall|i: int| 0 <= i < a2.len() - 1 implies a2[i].typ
                    != EXT_PRE_SHARED_KEY by {
                    assert(a2[i] == acc[i]);
                }
            }
            if t == EXT_PRE_SHARED_KEY {
                assert(a2[acc.len() as int].typ == EXT_PRE_SHARED_KEY);
            } else if !psk_seen {
                assert forall|i: int| 0 <= i < a2.len() implies a2[i].typ != EXT_PRE_SHARED_KEY by {
                    if i < acc.len() {
                        assert(a2[i] == acc[i]);
                    }
                }
            }
            acc = a2;
            steps = steps + 1 + cost@;
        }
        psk_bad = psk_seen;
        psk_seen = psk_seen || t == EXT_PRE_SHARED_KEY;
        dup = dup || had;
        pos = v.end;
    }
}

proof fn lemma_known_inj(k1: int, k2: int)
    requires
        0 <= k1 < SLOTS,
        0 <= k2 < SLOTS,
        known(k1) == known(k2),
    ensures
        k1 == k2,
{
}

proof fn lemma_find_typ(acc: Seq<SpecExt>, t: u16)
    ensures
        find_ext(acc, t) is Some ==> exists|i: int| 0 <= i < acc.len() && acc[i].typ == t,
    decreases acc.len(),
{
    if acc.len() > 0 && acc[0].typ != t {
        lemma_find_typ(acc.drop_first(), t);
        if find_ext(acc, t) is Some {
            let i = choose|i: int| 0 <= i < acc.drop_first().len() && acc.drop_first()[i].typ == t;
            assert(acc[i + 1].typ == t);
        }
    }
}

proof fn lemma_find_none(acc: Seq<SpecExt>, t: u16, i: int)
    requires
        0 <= i < acc.len(),
        acc[i].typ == t,
    ensures
        find_ext(acc, t) is Some,
    decreases acc.len(),
{
    if acc[0].typ != t {
        lemma_find_none(acc.drop_first(), t, i - 1);
    }
}

// ---------------------------------------------------------------------------
// ClientHello
// ---------------------------------------------------------------------------

/// A parsed ClientHello (§4.1.2). Every span is a position in the body it
/// was parsed from; `random` is always `[2, 34)`.
#[derive(Clone, Copy, Debug)]
pub struct ClientHello {
    pub legacy_version: u16,
    pub session_id: Span,
    /// The cipher suites, 2 bytes each.
    pub cipher_suites: Span,
    pub compression_methods: Span,
    /// The contents of the extensions vector, for extensions this crate
    /// does not interpret.
    pub extensions: Span,
    /// The host name in server_name (RFC 6066 §3).
    pub server_name: Option<Span>,
    /// The contents of `protocol_name_list` (RFC 7301 §3.1).
    pub alpn: Option<Span>,
    /// The contents of supported_versions' `versions`, 2 bytes each.
    pub supported_versions: Option<Span>,
    /// supported_groups' `named_group_list`, 2 bytes each.
    pub supported_groups: Option<Span>,
    /// signature_algorithms' `supported_signature_algorithms`, 2 bytes
    /// each.
    pub signature_algorithms: Option<Span>,
    pub signature_algorithms_cert: Option<Span>,
    /// key_share's `client_shares`.
    pub key_shares: Option<Span>,
    pub psk_modes: Option<Span>,
    /// pre_shared_key's `identities` and `binders`.
    pub pre_shared_key: Option<(Span, Span)>,
    pub cookie: Option<Span>,
    pub early_data: bool,
    /// encrypted_client_hello's data (RFC 9849), not interpreted here.
    pub ech: Option<Span>,
}

impl ClientHello {
    /// This is the spec's ClientHello.
    pub open spec fn models(self, s: SpecHello) -> bool {
        &&& self.legacy_version == s.outer.legacy_version
        &&& self.session_id@ == s.outer.session_id
        &&& self.cipher_suites@ == s.outer.cipher_suites
        &&& self.compression_methods@ == s.outer.compression_methods
        &&& self.extensions@ == s.outer.extensions
        &&& self.models_exts(s)
    }

    pub open spec fn ext_spans_ok(self, n: nat) -> bool {
        &&& self.server_name matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.alpn matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.key_shares matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.supported_versions matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
        &&& self.supported_groups matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
        &&& self.signature_algorithms matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
        &&& self.ech matches Some(sp) ==> sp.start <= sp.end <= n
    }

    /// Every span is inside an `n`-byte body, and the lists of 2-byte
    /// values have even lengths.
    pub open spec fn spans_ok(self, n: nat) -> bool {
        &&& self.cipher_suites.start <= self.cipher_suites.end <= n
        &&& (self.cipher_suites.end - self.cipher_suites.start) % 2 == 0
        &&& self.compression_methods.start < self.compression_methods.end <= n
        &&& self.server_name matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.alpn matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.key_shares matches Some(sp) ==> sp.start <= sp.end <= n
        &&& self.supported_versions matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
        &&& self.supported_groups matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
        &&& self.signature_algorithms matches Some(sp) ==> sp.start <= sp.end <= n && (sp.end
            - sp.start) % 2 == 0
    }

    /// The interpreted extensions are the spec's.
    pub open spec fn models_exts(self, s: SpecHello) -> bool {
        &&& ov(self.server_name) == s.server_name
        &&& ov(self.alpn) == s.alpn
        &&& ov(self.supported_versions) == s.supported_versions
        &&& ov(self.supported_groups) == s.supported_groups
        &&& ov(self.signature_algorithms) == s.signature_algorithms
        &&& ov(self.signature_algorithms_cert) == s.signature_algorithms_cert
        &&& ov(self.key_shares) == s.key_shares
        &&& ov(self.psk_modes) == s.psk_modes
        &&& ov2(self.pre_shared_key) == s.pre_shared_key
        &&& ov(self.cookie) == s.cookie
        &&& self.early_data == s.early_data
        &&& ov(self.ech) == s.ech
    }

    /// Parses a ClientHello body (the handshake message without its
    /// 4-byte header).
    pub fn parse(b: &[u8]) -> (r: Result<ClientHello, Alert>)
        ensures
            r matches Ok(h) ==> parse_client_hello(b@) matches Ok(s) && h.models(s),
            r matches Ok(h) ==> h.spans_ok(b@.len()),
            r matches Err(a) ==> parse_client_hello(b@) == Err::<SpecHello, SpecAlert>(a.spec()),
    {
        Self::parse_counted(b).0
    }

    /// `parse`, and the steps it takes: at most `12n + 2100` for an
    /// `n`-byte body. A step is one turn of a loop.
    pub fn parse_counted(b: &[u8]) -> (r: (Result<ClientHello, Alert>, Ghost<nat>))
        ensures
            r.0 matches Ok(h) ==> parse_client_hello(b@) matches Ok(s) && h.models(s),
            r.0 matches Ok(h) ==> h.spans_ok(b@.len()),
            r.0 matches Err(a) ==> parse_client_hello(b@) == Err::<SpecHello, SpecAlert>(a.spec()),
            r.1@ <= 12 * b@.len() + 2100,
    {
        let n = b.len();
        let ghost bs = b@;
        let (sid, cs, cm, x) = match outer_x(b) {
            Some(v) => v,
            None => return (Err(Alert::DecodeError), Ghost(0)),
        };
        let (scan, exts, c0) = scan_exts(b, x.start, x.end);
        let scan = match scan {
            Some(s) => s,
            None => return (Err(Alert::DecodeError), Ghost(c0@)),
        };
        let lv = (b[0] as u16) * 256 + b[1] as u16;
        let ghost o = SpecOuter {
            legacy_version: lv,
            session_id: sid@,
            cipher_suites: cs@,
            compression_methods: cm@,
            extensions: x@,
            exts: exts@,
        };
        proof {
            assert(lv == be16(bs, 0) as u16);
            assert(parse_outer(bs) == Some(o));
        }
        if scan.illegal {
            return (Err(Alert::IllegalParameter), Ghost(c0@));
        }
        let (r, c1) = interpret(b, &scan, Ghost(o));
        let h = match r {
            Err(a) => return (Err(a), Ghost(c0@ + c1@)),
            Ok(h) => h,
        };
        let h = ClientHello {
            legacy_version: lv,
            session_id: sid,
            cipher_suites: cs,
            compression_methods: cm,
            extensions: x,
            ..h
        };
        (Ok(h), Ghost(c0@ + c1@))
    }
}

/// The fields before the extensions, and the span of the extensions'
/// contents.
fn outer_x(b: &[u8]) -> (r: Option<(Span, Span, Span, Span)>)
    ensures
        r is None ==> parse_outer(b@) is None,
        r matches Some((sid, cs, cm, x)) ==> {
            &&& b@.len() >= 35
            &&& x.start <= x.end <= b@.len()
            &&& parse_exts(b@, x.start as int, x.end as int) matches Some(exts) ==> parse_outer(b@)
                == Some(
                SpecOuter {
                    legacy_version: be16(b@, 0) as u16,
                    session_id: sid@,
                    cipher_suites: cs@,
                    compression_methods: cm@,
                    extensions: x@,
                    exts,
                },
            )
            &&& parse_exts(b@, x.start as int, x.end as int) is None ==> parse_outer(b@) is None
        },
{
    let n = b.len();
    if n < 35 {
        return None;
    }
    let sid = match vec8_x(b, 34, n) {
        Some(v) => v,
        None => return None,
    };
    if sid.end - sid.start > 32 {
        return None;
    }
    let cs = match vec16_x(b, sid.end, n) {
        Some(v) => v,
        None => return None,
    };
    if (cs.end - cs.start) % 2 != 0 || cs.end - cs.start < 2 {
        return None;
    }
    let cm = match vec8_x(b, cs.end, n) {
        Some(v) => v,
        None => return None,
    };
    if cm.end - cm.start < 1 {
        return None;
    }
    let x = if cm.end == n {
        Span { start: n, end: n }
    } else {
        match whole16_x(b, cm.end, n) {
            Some(v) => v,
            None => return None,
        }
    };
    proof {
        if cm.end == n {
            assert(parse_exts(b@, n as int, n as int) == Some(Seq::<SpecExt>::empty()));
        }
    }
    Some((sid, cs, cm, x))
}

pub open spec fn oov(r: Option<Option<Span>>) -> Option<Option<(int, int)>> {
    match r {
        Some(o) => Some(ov(o)),
        None => None,
    }
}

pub open spec fn slot_ok(b: Seq<u8>, slot: Option<Span>) -> bool {
    slot matches Some(sp) ==> sp.start <= sp.end <= b.len()
}

pub open spec fn span_len(slot: Option<Span>) -> nat {
    match slot {
        Some(sp) => (sp.end - sp.start) as nat,
        None => 0,
    }
}

fn chk_sni(b: &[u8], slot: Option<Span>) -> (r: (Option<Option<Span>>, Ghost<nat>))
    requires
        slot_ok(b@, slot),
    ensures
        r.0 matches Some(Some(sp)) ==> sp.start <= sp.end <= b@.len(),
        match r.0 {
            None => opt(ov(slot), |s: int, e: int| server_name(b@, s, e)) is None,
            Some(h) => opt(ov(slot), |s: int, e: int| server_name(b@, s, e)) matches Some(v) && (
            match v {
                Some(hh) => hh,
                None => None,
            }) == ov(h),
        },
        r.1@ <= span_len(slot) + 1,
{
    match slot {
        None => (Some(None), Ghost(0)),
        Some(sp) => {
            let (r, c) = server_name_x(b, sp.start, sp.end);
            (r, c)
        },
    }
}

fn chk_alpn(b: &[u8], slot: Option<Span>) -> (r: (Option<Option<Span>>, Ghost<nat>))
    requires
        slot_ok(b@, slot),
    ensures
        r.0 matches Some(Some(sp)) ==> sp.start <= sp.end <= b@.len(),
        oov(r.0) == opt(ov(slot), |s: int, e: int| alpn_list(b@, s, e)),
        r.1@ <= span_len(slot) + 1,
{
    match slot {
        None => (Some(None), Ghost(0)),
        Some(sp) => {
            let (r, c) = alpn_x(b, sp.start, sp.end);
            match r {
                Some(v) => (Some(Some(v)), c),
                None => (None, c),
            }
        },
    }
}

fn chk_versions(b: &[u8], slot: Option<Span>) -> (r: Option<Option<Span>>)
    requires
        slot_ok(b@, slot),
    ensures
        r matches Some(Some(sp)) ==> sp.start <= sp.end <= b@.len() && (sp.end - sp.start) % 2 == 0,
        oov(r) == opt(ov(slot), |s: int, e: int| versions_list(b@, s, e)),
{
    match slot {
        None => Some(None),
        Some(sp) => match versions_x(b, sp.start, sp.end) {
            Some(v) => Some(Some(v)),
            None => None,
        },
    }
}

fn chk_u16_list(b: &[u8], slot: Option<Span>) -> (r: Option<Option<Span>>)
    requires
        slot_ok(b@, slot),
    ensures
        r matches Some(Some(sp)) ==> sp.start <= sp.end <= b@.len() && (sp.end - sp.start) % 2 == 0,
        oov(r) == opt(ov(slot), |s: int, e: int| u16_list(b@, s, e)),
{
    match slot {
        None => Some(None),
        Some(sp) => match u16_list_x(b, sp.start, sp.end) {
            Some(v) => Some(Some(v)),
            None => None,
        },
    }
}

fn chk_psk_modes(b: &[u8], slot: Option<Span>) -> (r: Option<Option<Span>>)
    requires
        slot_ok(b@, slot),
    ensures
        oov(r) == opt(ov(slot), |s: int, e: int| psk_modes_list(b@, s, e)),
{
    match slot {
        None => Some(None),
        Some(sp) => match psk_modes_x(b, sp.start, sp.end) {
            Some(v) => Some(Some(v)),
            None => None,
        },
    }
}

fn chk_cookie(b: &[u8], slot: Option<Span>) -> (r: Option<Option<Span>>)
    requires
        slot_ok(b@, slot),
    ensures
        oov(r) == opt(ov(slot), |s: int, e: int| cookie_value(b@, s, e)),
{
    match slot {
        None => Some(None),
        Some(sp) => match cookie_x(b, sp.start, sp.end) {
            Some(v) => Some(Some(v)),
            None => None,
        },
    }
}

fn chk_key_share(b: &[u8], slot: Option<Span>) -> (r: (Option<(Option<Span>, bool)>, Ghost<nat>))
    requires
        slot_ok(b@, slot),
    ensures
        r.0 matches Some((Some(sp), _)) ==> sp.start <= sp.end <= b@.len(),
        match r.0 {
            None => opt(ov(slot), |s: int, e: int| key_share_list(b@, s, e)) is None,
            Some((sp, dup)) => opt(ov(slot), |s: int, e: int| key_share_list(b@, s, e)) matches Some(
                v,
            ) && (match v {
                Some((sp2, _)) => Some(sp2),
                None => None,
            }) == ov(sp) && (dup == (v matches Some((_, g)) && !groups_distinct(g))),
        },
        5 * r.1@ <= 18 * span_len(slot) + 5 * (SPILL_STEPS + 1),
{
    match slot {
        None => (Some((None, false)), Ghost(0)),
        Some(sp) => {
            let (r, c) = key_share_x(b, sp.start, sp.end);
            match r {
                Some((v, d)) => (Some((Some(v), d)), c),
                None => (None, c),
            }
        },
    }
}

fn chk_psk(b: &[u8], slot: Option<Span>) -> (r: (Option<Option<(Span, Span)>>, Ghost<nat>))
    requires
        slot_ok(b@, slot),
    ensures
        match r.0 {
            None => opt(ov(slot), |s: int, e: int| offered_psks(b@, s, e)) is None,
            Some(p) => opt(ov(slot), |s: int, e: int| offered_psks(b@, s, e)) == Some(ov2(p)),
        },
        r.1@ <= span_len(slot),
{
    match slot {
        None => (Some(None), Ghost(0)),
        Some(sp) => {
            let (r, c) = offered_psks_x(b, sp.start, sp.end);
            match r {
                Some(v) => (Some(Some(v)), c),
                None => (None, c),
            }
        },
    }
}

/// Step 3 and 4 of `spec::parse_client_hello`: the contents of each
/// extension, then the key share groups. The ClientHello's outer fields
/// are left for the caller to fill in.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn interpret(b: &[u8], scan: &ExtScan, Ghost(o): Ghost<SpecOuter>) -> (r: (
    Result<ClientHello, Alert>,
    Ghost<nat>,
))
    requires
        parse_outer(b@) == Some(o),
        exts_distinct(o.exts),
        psk_last(o.exts),
        forall|k: int| 0 <= k < SLOTS ==> ov(#[trigger] scan.slots@[k]) == find_ext(o.exts, known(k)),
        forall|k: int|
            0 <= k < SLOTS ==> (#[trigger] scan.slots@[k] matches Some(sp) ==> sp.start <= sp.end
                <= b@.len()),
    ensures
        r.0 matches Ok(h) ==> parse_client_hello(b@) matches Ok(s) && h.models_exts(s) && s.outer
            == o,
        r.0 matches Ok(h) ==> h.ext_spans_ok(b@.len()),
        r.0 matches Err(a) ==> parse_client_hello(b@) == Err::<SpecHello, SpecAlert>(a.spec()),
        r.1@ <= 7 * b@.len() + 1050,
{
    let sl = &scan.slots;
    let ghost bs = b@;
    let ghost x = o.exts;
    proof {
        assert(slot_ok(bs, sl@[0]));
        assert(slot_ok(bs, sl@[1]));
        assert(slot_ok(bs, sl@[2]));
        assert(slot_ok(bs, sl@[3]));
        assert(slot_ok(bs, sl@[4]));
        assert(slot_ok(bs, sl@[5]));
        assert(slot_ok(bs, sl@[6]));
        assert(slot_ok(bs, sl@[7]));
        assert(slot_ok(bs, sl@[8]));
        assert(slot_ok(bs, sl@[9]));
        assert(slot_ok(bs, sl@[10]));
        assert(ov(sl@[0]) == find_ext(x, EXT_SERVER_NAME));
        assert(ov(sl@[1]) == find_ext(x, EXT_ALPN));
        assert(ov(sl@[2]) == find_ext(x, EXT_SUPPORTED_VERSIONS));
        assert(ov(sl@[3]) == find_ext(x, EXT_SUPPORTED_GROUPS));
        assert(ov(sl@[4]) == find_ext(x, EXT_SIGNATURE_ALGORITHMS));
        assert(ov(sl@[5]) == find_ext(x, EXT_SIGNATURE_ALGORITHMS_CERT));
        assert(ov(sl@[6]) == find_ext(x, EXT_KEY_SHARE));
        assert(ov(sl@[7]) == find_ext(x, EXT_PSK_KEY_EXCHANGE_MODES));
        assert(ov(sl@[8]) == find_ext(x, EXT_PRE_SHARED_KEY));
        assert(ov(sl@[9]) == find_ext(x, EXT_COOKIE));
        assert(ov(sl@[10]) == find_ext(x, EXT_EARLY_DATA));
        assert(ov(sl@[11]) == find_ext(x, EXT_ECH));
    }
    let (sni, c1) = chk_sni(b, sl[0]);
    let (alpn, c2) = chk_alpn(b, sl[1]);
    let sv = chk_versions(b, sl[2]);
    let sg = chk_u16_list(b, sl[3]);
    let sa = chk_u16_list(b, sl[4]);
    let sac = chk_u16_list(b, sl[5]);
    let (ks, c3) = chk_key_share(b, sl[6]);
    let pm = chk_psk_modes(b, sl[7]);
    let (psk, c4) = chk_psk(b, sl[8]);
    let ck = chk_cookie(b, sl[9]);
    let ed_bad = match sl[10] {
        Some(sp) => sp.start != sp.end,
        None => false,
    };
    let ghost steps = c1@ + c2@ + c3@ + c4@;
    proof {
        assert(span_len(sl@[0]) <= bs.len());
        assert(span_len(sl@[1]) <= bs.len());
        assert(span_len(sl@[6]) <= bs.len());
        assert(span_len(sl@[8]) <= bs.len());
    }
    if sni.is_none() || alpn.is_none() || sv.is_none() || sg.is_none() || sa.is_none()
        || sac.is_none() || ks.is_none() || pm.is_none() || psk.is_none() || ck.is_none() {
        return (Err(Alert::DecodeError), Ghost(steps));
    }
    let sni = sni.unwrap();
    let alpn = alpn.unwrap();
    let sv = sv.unwrap();
    let sg = sg.unwrap();
    let sa = sa.unwrap();
    let sac = sac.unwrap();
    let (ks, ks_dup) = ks.unwrap();
    let pm = pm.unwrap();
    let psk = psk.unwrap();
    let ck = ck.unwrap();
    if ed_bad {
        return (Err(Alert::DecodeError), Ghost(steps));
    }
    if ks_dup {
        return (Err(Alert::IllegalParameter), Ghost(steps));
    }
    proof {
        let ghost want = SpecHello {
            outer: o,
            server_name: ov(sni),
            alpn: ov(alpn),
            supported_versions: ov(sv),
            supported_groups: ov(sg),
            signature_algorithms: ov(sa),
            signature_algorithms_cert: ov(sac),
            key_shares: ov(ks),
            psk_modes: ov(pm),
            pre_shared_key: ov2(psk),
            cookie: ov(ck),
            early_data: sl@[10] is Some,
            ech: ov(sl@[11]),
        };
        assert(parse_client_hello(bs) == Ok::<SpecHello, SpecAlert>(want));
    }
    let h = ClientHello {
        legacy_version: 0,
        session_id: Span { start: 0, end: 0 },
        cipher_suites: Span { start: 0, end: 0 },
        compression_methods: Span { start: 0, end: 0 },
        extensions: Span { start: 0, end: 0 },
        server_name: sni,
        alpn,
        supported_versions: sv,
        supported_groups: sg,
        signature_algorithms: sa,
        signature_algorithms_cert: sac,
        key_shares: ks,
        psk_modes: pm,
        pre_shared_key: psk,
        cookie: ck,
        early_data: sl[10].is_some(),
        ech: sl[11],
    };
    (Ok(h), Ghost(steps))
}

} // verus!
