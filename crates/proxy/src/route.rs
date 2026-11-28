//! Verified routing: which upstream a request goes to.
//!
//! A route names a host (or any host) and a path prefix as path
//! components. A request's path is first resolved by verilith-server's
//! verified `path::resolve_exec` (segments percent-decoded, `.` and `..`
//! applied, `%2f`, `%5c`, `%00` and escapes above the root refused), so
//! that `/api/../admin`, `/%61dmin` and `/admin` are the same path to the
//! router, and the prefix is matched component by component, never in the
//! middle of a segment (`/api` does not match `/apix`). [`choose`] picks
//! `best`: among the matching routes, one that names the host before one
//! that does not, then the longest prefix, then the first listed.
use vstd::prelude::*;
use crate::hop::same_ci_exec;
#[cfg(verus_keep_ghost)]
use crate::hop::same_ci;

verus! {

/// A route, as the specification sees it.
pub struct SRoute {
    pub host: Option<Seq<u8>>,
    pub prefix: Seq<Seq<u8>>,
}

pub open spec fn matches(r: SRoute, host: Seq<u8>, comps: Seq<Seq<u8>>) -> bool {
    &&& (r.host matches Some(h) ==> same_ci(h, host))
    &&& r.prefix.len() <= comps.len()
    &&& comps.take(r.prefix.len() as int) == r.prefix
}

/// `a` is preferred to `b`.
pub open spec fn better(a: SRoute, b: SRoute) -> bool {
    (a.host is Some && b.host is None) || ((a.host is Some) == (b.host is Some) && a.prefix.len() > b.prefix.len())
}

pub open spec fn same_rank(a: SRoute, b: SRoute) -> bool {
    (a.host is Some) == (b.host is Some) && a.prefix.len() == b.prefix.len()
}

/// The route a request goes to: `Some(i)` for a matching route that no
/// matching route is better than, and that comes first among those as
/// good; `None` when no route matches.
pub open spec fn best(rs: Seq<SRoute>, host: Seq<u8>, comps: Seq<Seq<u8>>, r: Option<usize>) -> bool {
    match r {
        None => forall|j: int| 0 <= j < rs.len() ==> !matches(#[trigger] rs[j], host, comps),
        Some(i) => {
            &&& i < rs.len()
            &&& matches(rs[i as int], host, comps)
            &&& forall|j: int| 0 <= j < rs.len() && matches(#[trigger] rs[j], host, comps) ==> !better(rs[j], rs[i as int])
                && (same_rank(rs[j], rs[i as int]) ==> i <= j)
        },
    }
}

/// A route: an optional host, a prefix as path components, and where it
/// goes (an index into the proxy's upstreams).
pub struct Route {
    pub host: Option<Vec<u8>>,
    pub prefix: Vec<Vec<u8>>,
    pub upstream: usize,
}

pub open spec fn comps_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|c: Vec<u8>| c@)
}

pub open spec fn route_view(r: Route) -> SRoute {
    SRoute {
        host: match r.host {
            Some(h) => Some(h@),
            None => None,
        },
        prefix: comps_view(r.prefix@),
    }
}

pub open spec fn routes_view(rs: Seq<Route>) -> Seq<SRoute> {
    rs.map_values(|r: Route| route_view(r))
}

/// Byte strings equal.
pub fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
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

/// [`matches`].
pub fn matches_exec(r: &Route, host: &[u8], comps: &Vec<Vec<u8>>) -> (m: bool)
    ensures
        m == matches(route_view(*r), host@, comps_view(comps@)),
{
    let hok = match &r.host {
        Some(h) => same_ci_exec(h.as_slice(), host),
        None => true,
    };
    if !hok {
        return false;
    }
    let n = r.prefix.len();
    if n > comps.len() {
        return false;
    }
    let ghost pv = comps_view(r.prefix@);
    let ghost cv = comps_view(comps@);
    let mut i = 0;
    while i < n
        invariant
            n == r.prefix.len(),
            n <= comps.len(),
            0 <= i <= n,
            pv == comps_view(r.prefix@),
            cv == comps_view(comps@),
            forall|j: int| 0 <= j < i ==> cv[j] == pv[j],
        decreases n - i,
    {
        if !eq_bytes(r.prefix[i].as_slice(), comps[i].as_slice()) {
            assert(cv.take(n as int)[i as int] != pv[i as int]);
            return false;
        }
        i += 1;
    }
    assert(cv.take(n as int) =~= pv);
    true
}

fn better_exec(a: &Route, b: &Route) -> (r: bool)
    ensures
        r == better(route_view(*a), route_view(*b)),
{
    (a.host.is_some() && b.host.is_none()) || (a.host.is_some() == b.host.is_some() && a.prefix.len() > b.prefix.len())
}

/// The route for a request to `host` whose resolved path is `comps`:
/// exactly `best`.
pub fn choose(rs: &Vec<Route>, host: &[u8], comps: &Vec<Vec<u8>>) -> (r: Option<usize>)
    ensures
        best(routes_view(rs@), host@, comps_view(comps@), r),
{
    let ghost rv = routes_view(rs@);
    let ghost cv = comps_view(comps@);
    let mut cur: Option<usize> = None;
    let mut k = 0;
    while k < rs.len()
        invariant
            0 <= k <= rs.len(),
            rv == routes_view(rs@),
            cv == comps_view(comps@),
            rv.len() == rs.len(),
            match cur {
                None => forall|j: int| 0 <= j < k ==> !matches(#[trigger] rv[j], host@, cv),
                Some(i) => {
                    &&& i < k
                    &&& matches(rv[i as int], host@, cv)
                    &&& forall|j: int| 0 <= j < k && matches(#[trigger] rv[j], host@, cv) ==> !better(rv[j], rv[i as int])
                        && (same_rank(rv[j], rv[i as int]) ==> i <= j)
                },
            },
        decreases rs.len() - k,
    {
        assert(rv[k as int] == route_view(rs@[k as int]));
        if matches_exec(&rs[k], host, comps) {
            match cur {
                None => {
                    cur = Some(k);
                },
                Some(i) => {
                    assert(rv[i as int] == route_view(rs@[i as int]));
                    if better_exec(&rs[k], &rs[i]) {
                        cur = Some(k);
                    }
                },
            }
        }
        k += 1;
    }
    cur
}

} // verus!
