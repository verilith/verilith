//! Verified caching rules (RFC 9111): what the proxy's shared cache may
//! store, for how long, and when a request bypasses it.
//!
//! [`cc_of`] reads a Cache-Control list (RFC 9111 §5.2): comma-separated
//! directives, where a comma inside a quoted string does not separate
//! (so `private="a, b"` is one directive), names compared ignoring case,
//! and `max-age` and `s-maxage` taken from their first occurrence, as
//! delta-seconds capped at 2^31 (§1.2.2). [`storable`] is §3 for a shared
//! cache, narrowed: only GET, only the status codes RFC 9110 §15.1 calls
//! heuristically cacheable (never 206 or 304), never `no-store` in the
//! request or response, never `private` or `no-cache` (the proxy does
//! not revalidate), an `Authorization` request only when the response
//! says `public`, `must-revalidate` or `s-maxage` (§3.5), never a
//! response that sets a cookie or varies on anything but
//! Accept-Encoding, and only with an explicit lifetime (`s-maxage`, else
//! `max-age`: no heuristic freshness, no Expires). [`fresh`] is §4.2:
//! the lifetime exceeds the age (the backend's `Age` plus the time the
//! response has been stored). [`decide`] computes all of it exactly.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use verilith_http::spec::{is_ows, lower, trim_end};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{element, lead};
#[cfg(verus_keep_ghost)]
use verilith_server::persist::{lemma_lead, lemma_trim};
use crate::hop::same_ci_exec;
#[cfg(verus_keep_ghost)]
use crate::hop::same_ci;
use vstd::slice::slice_subrange;
#[cfg(verus_only)]
use verilith_core::num::is_digit;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// Where the directive starting at `i` ends: the next comma outside a
/// quoted string (`q`: inside one), or the end. A backslash in a quoted
/// string escapes the next byte.
pub open spec fn item_end(v: Seq<u8>, i: int, q: bool) -> int
    decreases v.len() - i,
{
    if i < 0 || i >= v.len() {
        if i < 0 { 0 } else { v.len() as int }
    } else if !q && v[i] == 0x2c {
        i
    } else if q && v[i] == 0x5c {
        if i + 2 >= v.len() { v.len() as int } else { item_end(v, i + 2, q) }
    } else if v[i] == 0x22 {
        item_end(v, i + 1, !q)
    } else {
        item_end(v, i + 1, q)
    }
}

/// The first `=` in `s`, or its length.
pub open spec fn eq_at(s: Seq<u8>, i: int) -> int
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() || s[i] == 0x3d { i } else { eq_at(s, i + 1) }
}

pub open spec fn cap() -> nat {
    0x8000_0000
}

/// `delta-seconds = 1*DIGIT`, capped at 2^31; `None` if not digits.
pub open spec fn delta(s: Seq<u8>) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        None
    } else if !is_digit(s.last()) {
        None
    } else if s.len() == 1 {
        Some((s.last() - 0x30) as nat)
    } else {
        match delta(s.drop_last()) {
            Some(d) => {
                let x = d * 10 + (s.last() - 0x30) as nat;
                Some(if x > cap() { cap() } else { x })
            },
            None => None,
        }
    }
}

/// The directives that matter here, folded over a list.
pub struct CC {
    pub no_store: bool,
    pub no_cache: bool,
    pub private: bool,
    pub public: bool,
    pub must_revalidate: bool,
    /// `Some(None)`: present but not delta-seconds.
    pub max_age: Option<Option<nat>>,
    pub s_maxage: Option<Option<nat>>,
}

pub open spec fn cc_init() -> CC {
    CC { no_store: false, no_cache: false, private: false, public: false, must_revalidate: false, max_age: None, s_maxage: None }
}

pub open spec fn d_no_store() -> Seq<u8> { seq![0x6eu8, 0x6f, 0x2d, 0x73, 0x74, 0x6f, 0x72, 0x65] }
pub open spec fn d_no_cache() -> Seq<u8> { seq![0x6eu8, 0x6f, 0x2d, 0x63, 0x61, 0x63, 0x68, 0x65] }
pub open spec fn d_private() -> Seq<u8> { seq![0x70u8, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65] }
pub open spec fn d_public() -> Seq<u8> { seq![0x70u8, 0x75, 0x62, 0x6c, 0x69, 0x63] }
pub open spec fn d_must_revalidate() -> Seq<u8> { seq![0x6du8, 0x75, 0x73, 0x74, 0x2d, 0x72, 0x65, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65] }
pub open spec fn d_max_age() -> Seq<u8> { seq![0x6du8, 0x61, 0x78, 0x2d, 0x61, 0x67, 0x65] }
pub open spec fn d_s_maxage() -> Seq<u8> { seq![0x73u8, 0x2d, 0x6d, 0x61, 0x78, 0x61, 0x67, 0x65] }

/// One directive `d` (trimmed) folded into `c`.
pub open spec fn cc_step(c: CC, d: Seq<u8>) -> CC {
    let e = eq_at(d, 0);
    let name = d.subrange(0, e);
    let val = if e < d.len() { d.subrange(e + 1, d.len() as int) } else { Seq::empty() };
    let dv = if e < d.len() { delta(val) } else { None };
    if same_ci(name, d_no_store()) {
        CC { no_store: true, ..c }
    } else if same_ci(name, d_no_cache()) {
        CC { no_cache: true, ..c }
    } else if same_ci(name, d_private()) {
        CC { private: true, ..c }
    } else if same_ci(name, d_public()) {
        CC { public: true, ..c }
    } else if same_ci(name, d_must_revalidate()) {
        CC { must_revalidate: true, ..c }
    } else if same_ci(name, d_max_age()) {
        if c.max_age is None { CC { max_age: Some(dv), ..c } } else { c }
    } else if same_ci(name, d_s_maxage()) {
        if c.s_maxage is None { CC { s_maxage: Some(dv), ..c } } else { c }
    } else {
        c
    }
}

/// The directives of `v[i..]`, folded into `c`.
pub open spec fn cc_from(v: Seq<u8>, i: int, c: CC) -> CC
    decreases v.len() - i,
{
    if i < 0 || i > v.len() {
        c
    } else {
        let e = item_end(v, i, false);
        let c2 = cc_step(c, element(v, i, e));
        if e >= v.len() || e < i { c2 } else { cc_from(v, e + 1, c2) }
    }
}

pub open spec fn cc_of(v: Seq<u8>) -> CC {
    cc_from(v, 0, cc_init())
}

/// RFC 9110 §15.1's heuristically cacheable status codes.
pub open spec fn cacheable_status(s: u16) -> bool {
    s == 200 || s == 203 || s == 204 || s == 300 || s == 301 || s == 308 || s == 404 || s == 405 || s == 410
        || s == 414 || s == 501
}

/// The explicit freshness lifetime in seconds: `s-maxage` for a shared
/// cache, else `max-age` (§4.2.1); 0 if neither is usable.
pub open spec fn lifetime(r: CC) -> nat {
    match r.s_maxage {
        Some(Some(n)) => n,
        Some(None) => 0,
        None => match r.max_age {
            Some(Some(n)) => n,
            _ => 0,
        },
    }
}

/// The directives, as the code holds them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cc {
    pub no_store: bool,
    pub no_cache: bool,
    pub private: bool,
    pub public: bool,
    pub must_revalidate: bool,
    pub max_age: Option<Option<u64>>,
    pub s_maxage: Option<Option<u64>>,
}

pub open spec fn opt_view(o: Option<Option<u64>>) -> Option<Option<nat>> {
    match o {
        Some(Some(n)) => Some(Some(n as nat)),
        Some(None) => Some(None),
        None => None,
    }
}

impl View for Cc {
    type V = CC;

    open spec fn view(&self) -> CC {
        CC {
            no_store: self.no_store,
            no_cache: self.no_cache,
            private: self.private,
            public: self.public,
            must_revalidate: self.must_revalidate,
            max_age: opt_view(self.max_age),
            s_maxage: opt_view(self.s_maxage),
        }
    }
}

pub open spec fn capped(c: Cc) -> bool {
    &&& (c.max_age matches Some(Some(n)) ==> n <= cap())
    &&& (c.s_maxage matches Some(Some(n)) ==> n <= cap())
}

/// What the request contributes.
#[derive(Clone, Copy, Debug)]
pub struct ReqFacts {
    pub get: bool,
    pub authorization: bool,
    pub cc: Cc,
}

/// What the response contributes besides Cache-Control.
#[derive(Clone, Copy, Debug)]
pub struct RespFacts {
    pub status: u16,
    pub set_cookie: bool,
    /// No Vary, or Vary naming only Accept-Encoding.
    pub vary_ok: bool,
    pub cc: Cc,
}

pub open spec fn storable(q: ReqFacts, r: RespFacts) -> bool {
    &&& q.get
    &&& cacheable_status(r.status)
    &&& !q.cc@.no_store
    &&& !r.cc@.no_store
    &&& !r.cc@.private
    &&& !r.cc@.no_cache
    &&& (q.authorization ==> r.cc@.public || r.cc@.must_revalidate || r.cc@.s_maxage is Some)
    &&& !r.set_cookie
    &&& r.vary_ok
    &&& lifetime(r.cc@) > 0
}

/// The request asks not to be answered from the cache without the origin
/// (`no-cache`, `no-store`, `max-age=0`, or `Pragma: no-cache`).
pub open spec fn bypass(q: CC, pragma_no_cache: bool) -> bool {
    q.no_cache || q.no_store || q.max_age == Some(Some(0nat)) || pragma_no_cache
}

/// A stored response is fresh: its lifetime exceeds its age.
pub open spec fn fresh(lifetime: nat, age: nat, resident: nat) -> bool {
    lifetime > age + resident
}

// ---------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------

proof fn lemma_item_end(v: Seq<u8>, i: int, q: bool)
    requires
        0 <= i <= v.len(),
    ensures
        i <= item_end(v, i, q) <= v.len(),
        item_end(v, i, q) < v.len() ==> v[item_end(v, i, q)] == 0x2c,
    decreases v.len() - i,
{
    if i < v.len() {
        if !q && v[i] == 0x2c {
        } else if q && v[i] == 0x5c {
            if i + 2 < v.len() {
                lemma_item_end(v, i + 2, q);
            }
        } else if v[i] == 0x22 {
            lemma_item_end(v, i + 1, !q);
        } else {
            lemma_item_end(v, i + 1, q);
        }
    }
}

proof fn lemma_eq_at(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= eq_at(s, i) <= s.len(),
    decreases s.len() - i,
{
    if i < s.len() && s[i] != 0x3d {
        lemma_eq_at(s, i + 1);
    }
}

/// [`delta`], as a u64 (at most 2^31).
pub fn delta_exec(s: &[u8]) -> (r: Option<u64>)
    ensures
        match delta(s@) {
            Some(d) => r == Some(d as u64) && d <= cap(),
            None => r is None,
        },
{
    if s.len() == 0 {
        return None;
    }
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            acc <= cap(),
            i == 0 ==> acc == 0,
            i > 0 ==> delta(s@.subrange(0, i as int)) == Some(acc as nat),
            forall|j: int| 0 <= j < i ==> is_digit(#[trigger] s@[j]),
        decreases s.len() - i,
    {
        let c = s[i];
        if !(c >= 0x30 && c <= 0x39) {
            proof {
                lemma_delta_bad(s@, i as int);
            }
            return None;
        }
        let x = acc * 10 + (c - 0x30) as u64;
        let ghost old_acc = acc;
        acc = if x > 0x8000_0000 { 0x8000_0000 } else { x };
        proof {
            let p = s@.subrange(0, i + 1);
            assert(p.drop_last() =~= s@.subrange(0, i as int));
            assert(p.last() == c);
            assert(is_digit(p.last()));
            if i == 0 {
                assert(p.len() == 1);
                assert(old_acc == 0);
                assert(delta(p) == Some((p.last() - 0x30) as nat));
            } else {
                assert(delta(p.drop_last()) == Some(old_acc as nat));
                assert(delta(p) == Some(if old_acc as nat * 10 + (c - 0x30) as nat > cap() { cap() } else { old_acc as nat * 10 + (c - 0x30) as nat }));
            }
        }
        i += 1;
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    Some(acc)
}

/// A non-digit anywhere makes `delta` None.
proof fn lemma_delta_bad(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        !is_digit(s[i]),
    ensures
        delta(s) is None,
    decreases s.len(),
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_delta_bad(s.drop_last(), i);
    }
}

fn cc_step_exec(c: Cc, d: &[u8]) -> (r: Cc)
    requires
        capped(c),
    ensures
        r@ == cc_step(c@, d@),
        capped(r),
{
    let mut e = 0;
    proof {
        lemma_eq_at(d@, 0);
    }
    while e < d.len() && d[e] != 0x3d
        invariant
            0 <= e <= d.len(),
            eq_at(d@, 0) == eq_at(d@, e as int),
        decreases d.len() - e,
    {
        e += 1;
    }
    let name = slice_subrange(d, 0, e);
    assert(name@ =~= d@.subrange(0, e as int));
    let dv: Option<u64> = if e < d.len() {
        let val = slice_subrange(d, e + 1, d.len());
        assert(val@ =~= d@.subrange(e + 1, d@.len() as int));
        delta_exec(val)
    } else {
        None
    };
    let ns: [u8; 8] = [0x6e, 0x6f, 0x2d, 0x73, 0x74, 0x6f, 0x72, 0x65];
    let nc: [u8; 8] = [0x6e, 0x6f, 0x2d, 0x63, 0x61, 0x63, 0x68, 0x65];
    let pr: [u8; 7] = [0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65];
    let pu: [u8; 6] = [0x70, 0x75, 0x62, 0x6c, 0x69, 0x63];
    let mr: [u8; 15] = [0x6d, 0x75, 0x73, 0x74, 0x2d, 0x72, 0x65, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x61, 0x74, 0x65];
    let ma: [u8; 7] = [0x6d, 0x61, 0x78, 0x2d, 0x61, 0x67, 0x65];
    let sm: [u8; 8] = [0x73, 0x2d, 0x6d, 0x61, 0x78, 0x61, 0x67, 0x65];
    assert(ns@ =~= d_no_store());
    assert(nc@ =~= d_no_cache());
    assert(pr@ =~= d_private());
    assert(pu@ =~= d_public());
    assert(mr@ =~= d_must_revalidate());
    assert(ma@ =~= d_max_age());
    assert(sm@ =~= d_s_maxage());
    if same_ci_exec(name, &ns) {
        Cc { no_store: true, ..c }
    } else if same_ci_exec(name, &nc) {
        Cc { no_cache: true, ..c }
    } else if same_ci_exec(name, &pr) {
        Cc { private: true, ..c }
    } else if same_ci_exec(name, &pu) {
        Cc { public: true, ..c }
    } else if same_ci_exec(name, &mr) {
        Cc { must_revalidate: true, ..c }
    } else if same_ci_exec(name, &ma) {
        if c.max_age.is_none() {
            Cc { max_age: Some(dv), ..c }
        } else {
            c
        }
    } else if same_ci_exec(name, &sm) {
        if c.s_maxage.is_none() {
            Cc { s_maxage: Some(dv), ..c }
        } else {
            c
        }
    } else {
        c
    }
}

/// [`cc_of`]: the Cache-Control directives of `v`.
pub fn cc_exec(v: &[u8]) -> (r: Cc)
    ensures
        r@ == cc_of(v@),
        capped(r),
{
    let len = v.len();
    let mut i: usize = 0;
    let mut c = Cc { no_store: false, no_cache: false, private: false, public: false, must_revalidate: false, max_age: None, s_maxage: None };
    assert(c@ == cc_init());
    loop
        invariant
            len == v@.len(),
            i <= len,
            cc_of(v@) == cc_from(v@, i as int, c@),
            capped(c),
        decreases len - i,
    {
        proof {
            lemma_item_end(v@, i as int, false);
        }
        // The directive's end: a comma outside quotes.
        let mut e = i;
        let mut q = false;
        while e < len && (q || v[e] != 0x2c)
            invariant
                len == v@.len(),
                i <= e,
                item_end(v@, i as int, false) == item_end(v@, e as int, q),
                e <= len,
            decreases len + 2 - e,
        {
            proof {
                lemma_item_end(v@, e as int, q);
            }
            if q && v[e] == 0x5c {
                if len - e <= 2 {
                    e = len;
                } else {
                    e += 2;
                }
            } else {
                if v[e] == 0x22 {
                    q = !q;
                }
                e += 1;
            }
        }
        proof {
            lemma_item_end(v@, i as int, false);
            if e < len {
                assert(!q && v@[e as int] == 0x2c);
            }
        }
        assert(e as int == item_end(v@, i as int, false));
        let mut s = i;
        proof {
            lemma_lead(v@, i as int, e as int);
        }
        while s < e && (v[s] == 0x20 || v[s] == 0x09)
            invariant
                len == v@.len(),
                i <= s <= e <= len,
                lead(v@, i as int, e as int) == lead(v@, s as int, e as int),
            decreases e - s,
        {
            s += 1;
        }
        let mut t = e;
        proof {
            lemma_trim(v@, s as int, e as int);
        }
        while t > s && (v[t - 1] == 0x20 || v[t - 1] == 0x09)
            invariant
                len == v@.len(),
                s <= t <= e <= len,
                trim_end(v@, s as int, e as int) == trim_end(v@, s as int, t as int),
            decreases t - s,
        {
            t -= 1;
        }
        let d = slice_subrange(v, s, t);
        assert(d@ =~= element(v@, i as int, e as int));
        c = cc_step_exec(c, d);
        if e >= len {
            return c;
        }
        i = e + 1;
    }
}

proof fn lemma_item_end_past(v: Seq<u8>, i: int, q: bool)
    requires
        i >= v.len(),
    ensures
        item_end(v, i, q) == v.len(),
{
}

/// [`lifetime`], in seconds.
pub fn lifetime_exec(r: &Cc) -> (n: u64)
    requires
        capped(*r),
    ensures
        n as nat == lifetime(r@),
        n <= cap(),
{
    match r.s_maxage {
        Some(Some(n)) => n as u64,
        Some(None) => 0,
        None => match r.max_age {
            Some(Some(n)) => n as u64,
            _ => 0,
        },
    }
}

fn cacheable_status_exec(s: u16) -> (r: bool)
    ensures
        r == cacheable_status(s),
{
    s == 200 || s == 203 || s == 204 || s == 300 || s == 301 || s == 308 || s == 404 || s == 405 || s == 410
        || s == 414 || s == 501
}

/// [`storable`], and if so the lifetime (seconds).
pub fn decide(q: &ReqFacts, r: &RespFacts) -> (out: Option<u64>)
    requires
        capped(r.cc),
    ensures
        out is Some <==> storable(*q, *r),
        out matches Some(n) ==> n as nat == lifetime(r.cc@),
{
    let life = lifetime_exec(&r.cc);
    let ok = q.get && cacheable_status_exec(r.status) && !q.cc.no_store && !r.cc.no_store && !r.cc.private
        && !r.cc.no_cache && (!q.authorization || r.cc.public || r.cc.must_revalidate || r.cc.s_maxage.is_some())
        && !r.set_cookie && r.vary_ok && life > 0;
    if ok { Some(life) } else { None }
}

/// [`bypass`].
pub fn bypass_exec(q: &Cc, pragma_no_cache: bool) -> (r: bool)
    ensures
        r == bypass(q@, pragma_no_cache),
{
    q.no_cache || q.no_store || matches!(q.max_age, Some(Some(0))) || pragma_no_cache
}

/// [`fresh`].
pub fn fresh_exec(lifetime: u64, age: u64, resident: u64) -> (r: bool)
    ensures
        r == fresh(lifetime as nat, age as nat, resident as nat),
{
    (lifetime as u128) > (age as u128) + (resident as u128)
}

} // verus!
