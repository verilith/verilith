//! The URL Standard's API setters, proven against `spec::set_protocol`,
//! `spec::set_username`, ... `spec::set_hash`.
//!
//! Each setter runs the state of the basic URL parser that the Standard
//! names as its state override, on the setter's input, and is proven to
//! leave the URL that `spec::run_url` leaves. The new href is then
//! assembled from the old URL's other components and the new one
//! (`assemble`), and proven to be the new record's serialization, so no
//! setter parses its result again.
use crate::encode::*;
use crate::host::*;
use crate::parse::*;
use crate::spec::*;
use crate::url::*;
use crate::ascii::*;
use vstd::prelude::*;

verus! {


// ---------------------------------------------------------------------------
// The components of a URL, as slices of its href
// ---------------------------------------------------------------------------

/// The pieces of a URL with a host, by offset.
proof fn lemma_authority_parts(u: &Url)
    requires
        u.wf(),
        u@.host is Some,
    ensures
        ({
            let url = u@;
            let h = u.href@;
            let sl = url.scheme.len() as int;
            let ue = u.username_end as int;
            let hs = u.host_start as int;
            let he = u.host_end as int;
            let ps = o_path_start(url) as int;
            &&& sl + 3 <= ue <= hs <= he <= ps <= h.len()
            &&& h.subrange(sl + 3, ue) == url.username
            &&& (url.password.len() > 0 <==> hs > ue + 1)
            &&& (url.password.len() > 0 ==> h.subrange(ue + 1, hs - 1) == url.password)
            &&& h.subrange(hs, he) == host_serialize(url.host->0)
            &&& h.subrange(he, ps) == port_serialize(url)
            &&& dot_len(url) == 0
        }),
{
    let url = u@;
    let h = u.href@;
    lemma_serialize_parts(url);
    let sl = url.scheme.len() as int;
    let au = authority_serialize(url);
    let c = credentials_serialize(url);
    let hb = host_serialize(url.host->0);
    let pt = port_serialize(url);
    assert(au =~= seq![b'/', b'/'] + c + hb + pt);
    let a = h.subrange(sl + 1, o_path_start(url) as int);
    assert(a == au);
    assert(h.subrange(sl + 3, u.username_end as int) =~= a.subrange(2, 2 + url.username.len() as int));
    if includes_credentials(url) {
        let pw = if url.password.len() > 0 {
            seq![b':'] + url.password
        } else {
            Seq::<u8>::empty()
        };
        assert(c =~= url.username + pw + seq![b'@']);
        assert(au.subrange(2, 2 + url.username.len() as int) =~= url.username);
        if url.password.len() > 0 {
            let ue = u.username_end as int;
            let hs = u.host_start as int;
            let k = 2 + url.username.len() as int + 1;
            assert(h.subrange(ue + 1, hs - 1) =~= a.subrange(k, k + url.password.len() as int));
            assert(au.subrange(k, k + url.password.len() as int) =~= url.password);
        }
    } else {
        assert(url.username.len() == 0);
        assert(c.len() == 0);
        assert(h.subrange(sl + 3, u.username_end as int) =~= url.username);
    }
    let hs = u.host_start as int;
    let he = u.host_end as int;
    let k = 2 + c.len() as int;
    assert(h.subrange(hs, he) =~= a.subrange(k, k + hb.len() as int));
    assert(au.subrange(k, k + hb.len() as int) =~= hb);
    let k2 = k + hb.len() as int;
    assert(h.subrange(he, o_path_start(url) as int) =~= a.subrange(k2, k2 + pt.len() as int));
    assert(au.subrange(k2, k2 + pt.len() as int) =~= pt);
}

/// The scheme.
fn scheme_of(u: &Url) -> (r: &[u8])
    requires
        u.wf(),
    ensures
        r@ == u@.scheme,
{
    url_scheme(u)
}

/// The username (when the URL has a host).
fn username_of(u: &Url) -> (r: &[u8])
    requires
        u.ok(),
    ensures
        r@ == u@.username,
{
    if u.host_kind.is_some() {
        proof {
            lemma_authority_parts(u);
        }
        vstd::slice::slice_subrange(u.href.as_slice(), u.scheme_end + 3, u.username_end)
    } else {
        proof {
            assert(u@.username =~= Seq::<u8>::empty());
        }
        &[]
    }
}

/// The password (when the URL has a host).
fn password_of(u: &Url) -> (r: &[u8])
    requires
        u.ok(),
    ensures
        r@ == u@.password,
{
    if u.host_kind.is_some() {
        proof {
            lemma_authority_parts(u);
        }
        if u.host_start - u.username_end > 1 {
            vstd::slice::slice_subrange(u.href.as_slice(), u.username_end + 1, u.host_start - 1)
        } else {
            proof {
                assert(u@.password =~= Seq::<u8>::empty());
            }
            &[]
        }
    } else {
        proof {
            assert(u@.password =~= Seq::<u8>::empty());
        }
        &[]
    }
}

/// The serialized host, if any.
fn host_of(u: &Url) -> (r: Option<&[u8]>)
    requires
        u.wf(),
    ensures
        r is Some <==> u@.host is Some,
        r matches Some(h) ==> h@ == host_serialize(u@.host->0),
{
    if u.host_kind.is_some() {
        proof {
            lemma_authority_parts(u);
        }
        Some(vstd::slice::slice_subrange(u.href.as_slice(), u.host_start, u.host_end))
    } else {
        None
    }
}

/// Where the path ends.
fn path_end_of(u: &Url) -> (r: usize)
    requires
        u.wf(),
    ensures
        r == o_query_start(u@) + dot_len(u@),
        r <= u.href@.len(),
{
    proof {
        lemma_serialize_parts(u@);
    }
    match u.query_start {
        Some(q) => q,
        None => match u.fragment_start {
            Some(f) => f,
            None => u.href.len(),
        },
    }
}

/// The serialized path.
fn path_of(u: &Url) -> (r: &[u8])
    requires
        u.wf(),
    ensures
        r@ == path_serialize(u@.path),
{
    proof {
        lemma_serialize_parts(u@);
    }
    let e = path_end_of(u);
    vstd::slice::slice_subrange(u.href.as_slice(), u.path_start, e)
}

/// The query, if any.
fn query_of(u: &Url) -> (r: Option<&[u8]>)
    requires
        u.wf(),
    ensures
        r is Some <==> u@.query is Some,
        r matches Some(q) ==> q@ == u@.query->0,
{
    proof {
        lemma_serialize_parts(u@);
    }
    match u.query_start {
        Some(q) => {
            let e = match u.fragment_start {
                Some(f) => f,
                None => u.href.len(),
            };
            proof {
                let h = u.href@;
                let qq = u@.query->0;
                let qs = q as int;
                assert(h.subrange(qs, e as int) =~= seq![b'?'] + qq);
                assert(h.subrange(qs + 1, e as int) =~= h.subrange(qs, e as int).skip(1));
                assert((seq![b'?'] + qq).skip(1) =~= qq);
            }
            Some(vstd::slice::slice_subrange(u.href.as_slice(), q + 1, e))
        },
        None => None,
    }
}

/// The fragment, if any.
fn fragment_of(u: &Url) -> (r: Option<&[u8]>)
    requires
        u.wf(),
    ensures
        r is Some <==> u@.fragment is Some,
        r matches Some(f) ==> f@ == u@.fragment->0,
{
    proof {
        lemma_serialize_parts(u@);
    }
    match u.fragment_start {
        Some(f) => {
            let e = u.href.len();
            proof {
                let h = u.href@;
                let ff = u@.fragment->0;
                let fs = f as int;
                assert(h.subrange(fs, e as int) =~= seq![b'#'] + ff);
                assert(h.subrange(fs + 1, e as int) =~= h.subrange(fs, e as int).skip(1));
                assert((seq![b'#'] + ff).skip(1) =~= ff);
            }
            Some(vstd::slice::slice_subrange(u.href.as_slice(), f + 1, e))
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Assembling a URL from its components
// ---------------------------------------------------------------------------

fn sat(a: usize, b: usize) -> (r: usize) {
    if a > usize::MAX - b {
        usize::MAX
    } else {
        a + b
    }
}

/// A capacity for `assemble`'s href (a hint: the href grows past it if
/// needed).
fn assemble_cap(scheme: &[u8], username: &[u8], password: &[u8], host: Option<&[u8]>, path: &[u8], query: Option<&[u8]>, fragment: Option<&[u8]>) -> usize {
    let mut cap = sat(scheme.len(), sat(path.len(), 16));
    match host {
        Some(hb) => {
            cap = sat(cap, sat(hb.len(), sat(username.len(), password.len())));
        },
        None => {},
    }
    match query {
        Some(q) => {
            cap = sat(cap, q.len());
        },
        None => {},
    }
    match fragment {
        Some(f) => {
            cap = sat(cap, f.len());
        },
        None => {},
    }
    cap
}

/// What `assemble` needs of a record: the conditions of `Url::ok` that do
/// not mention the href.
pub open spec fn assemblable(url: UrlRecord) -> bool {
    &&& path_ok(url.path)
    &&& (is_special(url) ==> url.path is List)
    &&& url_ascii(url)
    &&& crate::creds::creds_ok(url)
}

/// The URL whose record is `url`, from its serialized components. The
/// username and password are only read when there is a host.
#[verifier::rlimit(100)]
fn assemble(
    scheme: &[u8],
    username: &[u8],
    password: &[u8],
    host: Option<&[u8]>,
    host_kind: Option<HostKind>,
    port: Option<u16>,
    path: &[u8],
    opaque: bool,
    query: Option<&[u8]>,
    fragment: Option<&[u8]>,
    Ghost(url): Ghost<UrlRecord>,
) -> (u: Url)
    requires
        assemblable(url),
        scheme@ == url.scheme,
        url.host is Some ==> username@ == url.username && password@ == url.password,
        host is Some <==> url.host is Some,
        host matches Some(h) ==> h@ == host_serialize(url.host->0),
        host_kind == host_kind_of(url),
        port == url.port,
        path@ == path_serialize(url.path),
        opaque == (url.path is Opaque),
        query is Some <==> url.query is Some,
        query matches Some(q) ==> q@ == url.query->0,
        fragment is Some <==> url.fragment is Some,
        fragment matches Some(f) ==> f@ == url.fragment->0,
    ensures
        u.ok(),
        u@ == url,
{
    let tracked mut meter = Meter { n: 0 };
    let cap = assemble_cap(scheme, username, password, host, path, query, fragment);
    let mut h: Vec<u8> = Vec::with_capacity(cap);
    append(&mut h, scheme, Tracked(&mut meter));
    let scheme_end = h.len();
    h.push(b':');
    let after_colon = h.len();
    let ghost a = url.scheme + seq![b':'];
    proof {
        assert(h@ =~= a);
    }
    let username_end;
    let host_start;
    let host_end;
    match host {
        Some(hb) => {
            h.push(b'/');
            h.push(b'/');
            append(&mut h, username, Tracked(&mut meter));
            username_end = h.len();
            if password.len() > 0 {
                h.push(b':');
                append(&mut h, password, Tracked(&mut meter));
            }
            if username.len() > 0 || password.len() > 0 {
                h.push(b'@');
            }
            proof {
                assert(h@ =~= a + seq![b'/', b'/'] + credentials_serialize(url));
            }
            host_start = h.len();
            append(&mut h, hb, Tracked(&mut meter));
            host_end = h.len();
            proof {
                assert(username_end == o_username_end(url));
                assert(host_start == o_host_start(url));
                assert(host_end == o_host_end(url));
            }
            match port {
                Some(p) => {
                    h.push(b':');
                    push_decimal(&mut h, p as u32);
                },
                None => {},
            }
            proof {
                assert(h@ =~= a + seq![b'/', b'/'] + credentials_serialize(url) + host_serialize(url.host->0) + port_serialize(url));
                assert(h@ =~= a + authority_serialize(url));
            }
        },
        None => {
            username_end = after_colon;
            host_start = after_colon;
            host_end = after_colon;
            proof {
                assert(h@ =~= a + authority_serialize(url));
            }
        },
    }
    proof {
        if !opaque {
            lemma_segments_dot(url.path->List_0);
        }
        if path.len() >= 2 {
            assert(path@[0] == path[0]);
        }
    }
    let dot = host.is_none() && !opaque && path.len() >= 2 && path[0] == b'/' && path[1] == b'/';
    proof {
        assert(dot == needs_dot_slash(url));
    }
    if dot {
        h.push(b'/');
        h.push(b'.');
    }
    let path_start = h.len();
    proof {
        assert(path_start == o_path_start(url) + dot_len(url));
    }
    append(&mut h, path, Tracked(&mut meter));
    let ghost d = if dot { seq![b'/', b'.'] } else { Seq::<u8>::empty() };
    proof {
        assert(h@ =~= a + authority_serialize(url) + d + path_serialize(url.path));
    }
    let query_start = match query {
        Some(q) => {
            let s = h.len();
            proof {
                assert(s == o_query_start(url) + dot_len(url));
            }
            h.push(b'?');
            append(&mut h, q, Tracked(&mut meter));
            Some(s)
        },
        None => None,
    };
    proof {
        assert(h@ =~= a + authority_serialize(url) + d + path_serialize(url.path) + query_serialize(url));
    }
    let fragment_start = match fragment {
        Some(f) => {
            let s = h.len();
            proof {
                assert(s == o_fragment_start(url) + dot_len(url));
            }
            h.push(b'#');
            append(&mut h, f, Tracked(&mut meter));
            Some(s)
        },
        None => None,
    };
    proof {
        assert(h@ =~= serialize(url, false));
    }
    let special = is_special_exec(scheme);
    let total = h.len();
    let u = Url {
        href: h,
        scheme_end,
        username_end,
        host_start,
        host_end,
        port,
        path_start,
        query_start,
        fragment_start,
        host_kind,
        opaque_path: opaque,
        special,
        has_dot: dot,
        rec: Ghost(url),
    };
    proof {
        let d = dot_len(url);
        assert(u.href@ == serialize(url, false));
        assert(u.scheme_end == url.scheme.len());
        assert(u.username_end == o_username_end(url));
        assert(u.host_start == o_host_start(url));
        assert(u.host_end == o_host_end(url));
        assert(u.path_start == o_path_start(url) + d);
        assert(u.query_start == (if url.query is Some {
            Some((o_query_start(url) + d) as usize)
        } else {
            None
        }));
        assert(u.fragment_start == (if url.fragment is Some {
            Some((o_fragment_start(url) + d) as usize)
        } else {
            None
        }));
        assert(u.has_dot == needs_dot_slash(url));
        assert(u.special == is_special(url));
        assert(u.host_kind == host_kind_of(url));
        assert(u.opaque_path == (url.path is Opaque));
        assert(u.port == url.port);
        assert(path_ok(url.path));
        assert(u.href@.len() <= usize::MAX);
        assert(u.wf());
    }
    u
}


// ---------------------------------------------------------------------------
// Running the parser with a state override
// ---------------------------------------------------------------------------

pub open spec fn brackets(c: u8, inside: bool) -> bool {
    if c == b'[' {
        true
    } else if c == b']' {
        false
    } else {
        inside
    }
}

/// The host state on a byte that it adds to its buffer.
proof fn lemma_host_char(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Host || m.state == State::Hostname,
        m.url.scheme != s_file(),
        0 <= p < input.len(),
        !(input[p] == b':' && !m.inside_brackets),
        !is_authority_end(input, p, is_special(m.url)),
    ensures
        run_url(input, None, so, m, p) == run_url(
            input,
            None,
            so,
            Machine { inside_brackets: brackets(input[p], m.inside_brackets), buffer: m.buffer.push(input[p]), ..m },
            p + 1,
        ),
{
}

/// The host state at the end of the host.
proof fn lemma_host_end(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Host || m.state == State::Hostname,
        m.url.scheme != s_file(),
        0 <= p <= input.len(),
        !c_is(input, p, b':') || m.inside_brackets,
        is_authority_end(input, p, is_special(m.url)),
    ensures
        run_url(input, None, so, m, p) == (if is_special(m.url) && m.buffer.len() == 0 {
            m.url
        } else if m.buffer.len() == 0 && (includes_credentials(m.url) || m.url.port is Some) {
            m.url
        } else {
            match host_parse(m.buffer, !is_special(m.url)) {
                None => m.url,
                Some(h) => UrlRecord { host: Some(h), ..m.url },
            }
        }),
{
}

/// The host state at a ":" outside brackets.
proof fn lemma_host_colon(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Host || m.state == State::Hostname,
        m.url.scheme != s_file(),
        0 <= p < input.len(),
        input[p] == b':',
        !m.inside_brackets,
    ensures
        run_url(input, None, so, m, p) == (if m.buffer.len() == 0 || so == Some(State::Hostname) {
            m.url
        } else {
            match host_parse(m.buffer, !is_special(m.url)) {
                None => m.url,
                Some(h) => run_url(
                    input,
                    None,
                    so,
                    Machine { url: UrlRecord { host: Some(h), ..m.url }, buffer: Seq::empty(), state: State::Port, ..m },
                    p + 1,
                ),
            }
        }),
{
}

/// The port state on a digit.
proof fn lemma_port_digit(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Port,
        0 <= p < input.len(),
        is_ascii_digit(input[p]),
    ensures
        run_url(input, None, so, m, p) == run_url(input, None, so, Machine { buffer: m.buffer.push(input[p]), ..m }, p + 1),
{
}

/// The port state after its digits, with a state override.
proof fn lemma_port_end(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Port,
        0 <= p <= input.len(),
        p < input.len() ==> !is_ascii_digit(input[p]),
    ensures
        run_url(input, None, so, m, p) == (if m.buffer.len() == 0 || radix_value(m.buffer, 10) > 65535 {
            m.url
        } else {
            let port = radix_value(m.buffer, 10);
            UrlRecord {
                port: if default_port(m.url.scheme) == Some(port as u16) {
                    None
                } else {
                    Some(port as u16)
                },
                ..m.url
            }
        }),
{
}

/// The file host state on a byte that it adds to its buffer.
proof fn lemma_file_host_char(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::FileHost,
        0 <= p < input.len(),
        !(input[p] == b'/' || input[p] == b'\\' || input[p] == b'?' || input[p] == b'#'),
    ensures
        run_url(input, None, so, m, p) == run_url(input, None, so, Machine { buffer: m.buffer.push(input[p]), ..m }, p + 1),
{
}

/// The file host state at the end of the host, with a state override.
proof fn lemma_file_host_end(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::FileHost,
        0 <= p <= input.len(),
        p < input.len() ==> (input[p] == b'/' || input[p] == b'\\' || input[p] == b'?' || input[p] == b'#'),
    ensures
        run_url(input, None, so, m, p) == (if m.buffer.len() == 0 {
            UrlRecord { host: Some(Host::Empty), ..m.url }
        } else {
            match host_parse(m.buffer, !is_special(m.url)) {
                None => m.url,
                Some(h) => UrlRecord {
                    host: Some(if h == Host::Domain(s_localhost()) { Host::Empty } else { h }),
                    ..m.url
                },
            }
        }),
{
}

/// The host state with a state override on a file URL hands over to the
/// file host state.
proof fn lemma_host_file(input: Seq<u8>, so: Option<State>, m: Machine)
    requires
        so is Some,
        m.state == State::Host || m.state == State::Hostname,
        m.url.scheme == s_file(),
    ensures
        run_url(input, None, so, m, 0) == run_url(input, None, so, Machine { state: State::FileHost, ..m }, 0),
{
    let m2 = Machine { state: State::FileHost, ..m };
    if input.len() == 0 {
        assert(run_url(input, None, so, m, 0) == run_url(input, None, so, m2, 0));
    }
}

// ---------------------------------------------------------------------------
// The host and hostname setters
// ---------------------------------------------------------------------------

pub open spec fn host_machine(url: UrlRecord, st: State, buffer: Seq<u8>, inside: bool) -> Machine {
    Machine {
        state: st,
        url,
        buffer,
        at_sign_seen: false,
        inside_brackets: inside,
        password_token_seen: false,
    }
}

fn no_bytes() -> (r: &'static [u8])
    ensures
        r@ == Seq::<u8>::empty(),
{
    let r: &'static [u8] = &[];
    proof {
        assert(r@ =~= Seq::<u8>::empty());
    }
    r
}

pub open spec fn host_parse_ascii_ok(h: Host) -> bool {
    is_ascii(host_serialize(h))
}

/// `u` with the host `hb` (serialized, of kind `kind`) and port `port`.
fn with_host(u: &Url, hb: &[u8], kind: HostKind, port: Option<u16>, Ghost(h): Ghost<Host>) -> (r: Url)
    requires
        u.ok(),
        hb@ == host_serialize(h),
        kind == kind_of(h),
        host_parse_ascii_ok(h),
    ensures
        r.ok(),
        r@ == (UrlRecord { host: Some(h), port, ..u@ }),
{
    let ghost url = UrlRecord { host: Some(h), port, ..u@ };
    proof {
        assert(crate::creds::creds_ok(url));
        assert(url_ascii(url));
    }
    let q = query_of(u);
    let f = fragment_of(u);
    assemble(
        scheme_of(u),
        username_of(u),
        password_of(u),
        Some(hb),
        Some(kind),
        port,
        path_of(u),
        u.opaque_path,
        q,
        f,
        Ghost(url),
    )
}

/// The href of a URL with a host, around the host.
proof fn lemma_host_split(url: UrlRecord, h: Host)
    requires
        url.host is Some,
    ensures
        ({
            let a = url.scheme + seq![b':'] + seq![b'/', b'/'] + credentials_serialize(url);
            let b = port_serialize(url) + path_serialize(url.path) + query_serialize(url) + fragment_serialize(url);
            let url2 = UrlRecord { host: Some(h), ..url };
            &&& serialize(url, false) == a + host_serialize(url.host->0) + b
            &&& serialize(url2, false) == a + host_serialize(h) + b
            &&& a.len() == o_host_start(url)
        }),
{
    let a = url.scheme + seq![b':'] + seq![b'/', b'/'] + credentials_serialize(url);
    let b = port_serialize(url) + path_serialize(url.path) + query_serialize(url) + fragment_serialize(url);
    let url2 = UrlRecord { host: Some(h), ..url };
    assert(credentials_serialize(url2) == credentials_serialize(url));
    assert(port_serialize(url2) == port_serialize(url));
    assert(query_serialize(url2) == query_serialize(url));
    assert(fragment_serialize(url2) == fragment_serialize(url));
    assert(serialize(url, false) =~= a + host_serialize(url.host->0) + b);
    assert(serialize(url2, false) =~= a + host_serialize(h) + b);
}

proof fn lemma_splice_href(u: &Url, hh: Host, h: Seq<u8>, host_end: int)
    requires
        u.ok(),
        u@.host is Some,
        h == u.href@.subrange(0, u.host_start as int) + host_serialize(hh) + u.href@.subrange(u.host_end as int, u.href@.len() as int),
    ensures
        h == serialize(UrlRecord { host: Some(hh), ..u@ }, false),
{
    let url = u@;
    lemma_serialize_parts(url);
    lemma_authority_parts(u);
    lemma_host_split(url, hh);
    let a = url.scheme + seq![b':'] + seq![b'/', b'/'] + credentials_serialize(url);
    let b = port_serialize(url) + path_serialize(url.path) + query_serialize(url) + fragment_serialize(url);
    let old = u.href@;
    assert(old.subrange(0, u.host_start as int) =~= a);
    assert(old.subrange(u.host_end as int, old.len() as int) =~= b);
    assert(h =~= a + host_serialize(hh) + b);
}

proof fn lemma_splice_ok(u: &Url, r: &Url, hh: Host)
    requires
        u.ok(),
        u@.host is Some,
        is_ascii(host_serialize(hh)),
        r@ == (UrlRecord { host: Some(hh), ..u@ }),
        r.href@ == serialize(r@, false),
        r.href@.len() <= usize::MAX,
        r.scheme_end == u.scheme_end,
        r.username_end == u.username_end,
        r.host_start == u.host_start,
        r.host_end == u.host_start + host_serialize(hh).len(),
        r.port == u.port,
        r.path_start == r.host_end + (u.path_start - u.host_end),
        r.query_start == (match u.query_start {
            Some(q) => Some((r.host_end + (q - u.host_end)) as usize),
            None => None,
        }),
        r.fragment_start == (match u.fragment_start {
            Some(f) => Some((r.host_end + (f - u.host_end)) as usize),
            None => None,
        }),
        r.host_kind == Some(kind_of(hh)),
        r.opaque_path == u.opaque_path,
        r.special == u.special,
        !r.has_dot,
    ensures
        r.ok(),
{
    let url = u@;
    let url2 = r@;
    lemma_serialize_parts(url);
    lemma_serialize_parts(url2);
    lemma_authority_parts(u);
    assert(url_ascii(url2));
}

/// `u` with the host that `buf` parses to, spliced into the href in place
/// of the old one (`u` has a host; credentials and port stay).
fn splice_host(u: &Url, buf: &[u8], opaque: bool) -> (r: Option<(Url, Ghost<Host>)>)
    requires
        u.ok(),
        u@.host is Some,
    ensures
        r is None ==> host_parse(buf@, opaque) is None,
        r matches Some((n, h)) ==> host_parse(buf@, opaque) == Some(h@) && n.ok() && n@ == (UrlRecord { host: Some(h@), ..u@ }),
{
    let ghost url = u@;
    let tracked mut meter = Meter { n: 0 };
    let n = u.href.len();
    proof {
        lemma_serialize_parts(url);
        lemma_authority_parts(u);
    }
    let mut h: Vec<u8> = Vec::with_capacity(sat(n, sat(buf.len(), sat(buf.len(), 16))));
    append_range(&mut h, u.href.as_slice(), 0, u.host_start, Tracked(&mut meter));
    match host_parse_exec(buf, opaque, &mut h, &mut crate::host::Scratch::new(), false, Tracked(&mut meter)) {
        None => None,
        Some((kind, gh)) => {
            let ghost hh = gh@;
            let ghost url2 = UrlRecord { host: Some(hh), ..url };
            let host_end = h.len();
            append_range(&mut h, u.href.as_slice(), u.host_end, n, Tracked(&mut meter));
            let total = h.len();
            proof {
                lemma_splice_href(u, hh, h@, host_end as int);
                lemma_host_parse_ascii(buf@, opaque);
            }
            let path_start = host_end + (u.path_start - u.host_end);
            let query_start = match u.query_start {
                Some(q) => Some(host_end + (q - u.host_end)),
                None => None,
            };
            let fragment_start = match u.fragment_start {
                Some(f) => Some(host_end + (f - u.host_end)),
                None => None,
            };
            let r = Url {
                href: h,
                scheme_end: u.scheme_end,
                username_end: u.username_end,
                host_start: u.host_start,
                host_end,
                port: u.port,
                path_start,
                query_start,
                fragment_start,
                host_kind: Some(kind),
                opaque_path: u.opaque_path,
                special: u.special,
                has_dot: false,
                rec: Ghost(url2),
            };
            proof {
                assert(r.href@.len() == total);
                lemma_splice_ok(u, &r, hh);
            }
            Some((r, Ghost(hh)))
        },
    }
}

/// The file host state with a state override, from the start of `v`.
fn file_host_override(u: &Url, v: &[u8], Ghost(st): Ghost<State>) -> (r: (Option<Url>, bool))
    requires
        u.ok(),
        u@.path is List,
        u@.scheme == s_file(),
        st == State::Host || st == State::Hostname,
    ensures
        ({
            let want = run_url(v@, None, Some(st), initial_machine(st, u@), 0);
            &&& r.0 matches Some(n) ==> n.ok() && n@ == want
            &&& r.0 is None ==> want == u@
        }),
{
    let ghost so = Some(st);
    let ghost url = u@;
    let ghost target = run_url(v@, None, so, initial_machine(st, url), 0);
    let tracked mut meter = Meter { n: 0 };
    let n = v.len();
    proof {
        lemma_host_file(v@, so, initial_machine(st, url));
        assert(v@.take(0) =~= Seq::<u8>::empty());
    }
    let mut k = 0;
    while k < n && !(v[k] == b'/' || v[k] == b'\\' || v[k] == b'?' || v[k] == b'#')
        invariant
            k <= n == v@.len(),
            so == Some(st),
            target == run_url(v@, None, so, host_machine(url, State::FileHost, v@.take(k as int), false), k as int),
        decreases n - k,
    {
        proof {
            lemma_file_host_char(v@, so, host_machine(url, State::FileHost, v@.take(k as int), false), k as int);
            assert(v@.take(k as int).push(v@[k as int]) =~= v@.take(k + 1));
        }
        k += 1;
    }
    proof {
        lemma_file_host_end(v@, so, host_machine(url, State::FileHost, v@.take(k as int), false), k as int);
        assert(host_serialize(Host::Empty) =~= Seq::<u8>::empty());
        assert(is_ascii(Seq::<u8>::empty()));
    }
    if k == 0 {
        return (Some(with_host(u, no_bytes(), HostKind::Empty, u.port, Ghost(Host::Empty))), true);
    }
    let buf = vstd::slice::slice_subrange(v, 0, k);
    proof {
        assert(buf@ =~= v@.take(k as int));
    }
    let mut hb: Vec<u8> = Vec::new();
    match host_parse_exec(buf, false, &mut hb, &mut crate::host::Scratch::new(), false, Tracked(&mut meter)) {
        None => (None, false),
        Some((kind, gh)) => {
            let ghost h = gh@;
            proof {
                assert(hb@ =~= host_serialize(h));
                lemma_host_parse_ascii(buf@, false);
            }
            let local = match kind {
                HostKind::Domain => is_localhost(hb.as_slice(), 0),
                _ => false,
            };
            proof {
                assert(hb@.subrange(0, hb@.len() as int) =~= hb@);
                assert(local == (h == Host::Domain(s_localhost())));
            }
            if local {
                (Some(with_host(u, no_bytes(), HostKind::Empty, u.port, Ghost(Host::Empty))), true)
            } else {
                (Some(with_host(u, hb.as_slice(), kind, u.port, Ghost(h))), true)
            }
        },
    }
}

/// The port state with a state override, after the host setter's ":" at
/// `i` set the host to `h`.
fn port_after_host(u: &Url, v: &[u8], i: usize, hb: &[u8], kind: HostKind, Ghost(h): Ghost<Host>, Ghost(st): Ghost<State>) -> (r: Url)
    requires
        u.ok(),
        u@.path is List,
        i < v.len(),
        hb@ == host_serialize(h),
        kind == kind_of(h),
        host_parse_ascii_ok(h),
    ensures
        r.ok(),
        r@ == run_url(v@, None, Some(st), host_machine(UrlRecord { host: Some(h), ..u@ }, State::Port, Seq::empty(), false), i + 1),
{
    let ghost so = Some(st);
    let ghost url2 = UrlRecord { host: Some(h), ..u@ };
    let ghost target = run_url(v@, None, so, host_machine(url2, State::Port, Seq::empty(), false), i + 1);
    let tracked mut meter = Meter { n: 0 };
    let n = v.len();
    let mut j = i + 1;
    proof {
        assert(v@.subrange(i + 1, j as int) =~= Seq::<u8>::empty());
    }
    while j < n && v[j] >= b'0' && v[j] <= b'9'
        invariant
            i < j <= n == v@.len(),
            so == Some(st),
            target == run_url(v@, None, so, host_machine(url2, State::Port, v@.subrange(i + 1, j as int), false), j as int),
            all_ascii_digits(v@.subrange(i + 1, j as int)),
        decreases n - j,
    {
        proof {
            lemma_port_digit(v@, so, host_machine(url2, State::Port, v@.subrange(i + 1, j as int), false), j as int);
            assert(v@.subrange(i + 1, j as int).push(v@[j as int]) =~= v@.subrange(i + 1, j + 1));
        }
        j += 1;
    }
    proof {
        lemma_port_end(v@, so, host_machine(url2, State::Port, v@.subrange(i + 1, j as int), false), j as int);
    }
    if j == i + 1 {
        return with_host(u, hb, kind, u.port, Ghost(h));
    }
    let digits = vstd::slice::slice_subrange(v, i + 1, j);
    let pv = port_value(digits, Tracked(&mut meter));
    if pv > 65535 {
        return with_host(u, hb, kind, u.port, Ghost(h));
    }
    let p = pv as u16;
    let port = if default_port_exec(scheme_of(u)) == Some(p) {
        None
    } else {
        Some(p)
    };
    with_host(u, hb, kind, port, Ghost(h))
}

/// The host and hostname setters' parse, on input without tab or newline,
/// of a URL with a list path. `None` if the URL stays as it is; the bool is
/// whether the setter reports success.
fn host_override(u: &Url, v: &[u8], hostname: bool) -> (r: (Option<Url>, bool))
    requires
        u.ok(),
        u@.path is List,
    ensures
        ({
            let st = if hostname { State::Hostname } else { State::Host };
            let want = run_url(v@, None, Some(st), initial_machine(st, u@), 0);
            &&& r.0 matches Some(n) ==> n.ok() && n@ == want
            &&& r.0 is None ==> want == u@
        }),
{
    let ghost st = if hostname { State::Hostname } else { State::Host };
    let ghost so = Some(st);
    let ghost url = u@;
    let ghost target = run_url(v@, None, so, initial_machine(st, url), 0);
    let tracked mut meter = Meter { n: 0 };
    if is_file_exec(scheme_of(u)) {
        return file_host_override(u, v, Ghost(st));
    }
    let n = v.len();
    let special = u.special;
    let mut inside = false;
    let mut i = 0;
    proof {
        assert(v@.take(0) =~= Seq::<u8>::empty());
    }
    while i < n && !(v[i] == b':' && !inside) && !(v[i] == b'/' || v[i] == b'?' || v[i] == b'#' || (special && v[i] == b'\\'))
        invariant
            i <= n == v@.len(),
            special == is_special(url),
            url.scheme != s_file(),
            so == Some(st),
            st == State::Host || st == State::Hostname,
            target == run_url(v@, None, so, host_machine(url, st, v@.take(i as int), inside), i as int),
        decreases n - i,
    {
        proof {
            lemma_host_char(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
            assert(v@.take(i as int).push(v@[i as int]) =~= v@.take(i + 1));
        }
        if v[i] == b'[' {
            inside = true;
        } else if v[i] == b']' {
            inside = false;
        }
        i += 1;
    }
    let buf = vstd::slice::slice_subrange(v, 0, i);
    proof {
        assert(buf@ =~= v@.take(i as int));
    }
    if i < n && v[i] == b':' && !inside {
        proof {
            lemma_host_colon(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
        }
        if i == 0 || hostname {
            return (None, false);
        }
        let mut hb: Vec<u8> = Vec::new();
        return match host_parse_exec(buf, !special, &mut hb, &mut crate::host::Scratch::new(), false, Tracked(&mut meter)) {
            None => (None, false),
            Some((kind, gh)) => {
                let ghost h = gh@;
                proof {
                    assert(hb@ =~= host_serialize(h));
                    lemma_host_parse_ascii(buf@, !special);
                }
                (Some(port_after_host(u, v, i, hb.as_slice(), kind, Ghost(h), Ghost(st))), true)
            },
        };
    }
    proof {
        lemma_host_end(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
    }
    if special && i == 0 {
        return (None, false);
    }
    if i == 0 && (u.host_start - u.scheme_end > 3 || u.port.is_some()) {
        return (None, false);
    }
    if u.host_kind.is_some() {
        return match splice_host(u, buf, !special) {
            None => (None, false),
            Some((n, _)) => (Some(n), true),
        };
    }
    let mut hb: Vec<u8> = Vec::new();
    match host_parse_exec(buf, !special, &mut hb, &mut crate::host::Scratch::new(), false, Tracked(&mut meter)) {
        None => (None, false),
        Some((kind, gh)) => {
            let ghost h = gh@;
            proof {
                assert(hb@ =~= host_serialize(h));
                lemma_host_parse_ascii(buf@, !special);
            }
            (Some(with_host(u, hb.as_slice(), kind, u.port, Ghost(h))), true)
        },
    }
}


/// Removes tab and newline from `value`, then runs `f`... (Verus has no
/// closures over slices here, so each setter calls `clean` itself.)
fn clean(value: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == remove_tab_newline(value@),
{
    let tracked mut meter = Meter { n: 0 };
    proof {
        assert(value@.subrange(0, value@.len() as int) =~= value@);
    }
    crate::api::remove_tab_newline_exec(value, 0, value.len(), Tracked(&mut meter))
}

/// The host and hostname setters. `None` if the URL stays as it is; the
/// bool is whether the setter reports success.
pub(crate) fn set_host_bytes(u: &Url, value: &[u8], hostname: bool) -> (r: (Option<Url>, bool))
    requires
        u.ok(),
    ensures
        ({
            let want = if hostname { set_hostname(u@, value@) } else { set_host(u@, value@) };
            &&& r.0 matches Some(n) ==> n.ok() && n@ == want
            &&& r.0 is None ==> want == u@
        }),
{
    if u.opaque_path {
        return (None, false);
    }
    let tracked mut meter = Meter { n: 0 };
    if !crate::api::any_tab_newline(value, Tracked(&mut meter)) {
        proof {
            crate::api::lemma_filter_identity(value@);
        }
        host_override(u, value, hostname)
    } else {
        let v = clean(value);
        host_override(u, v.as_slice(), hostname)
    }
}

/// The hostname setter when only the new host is wanted: the host is
/// appended to `out` and no URL is built. `None` when this does not apply
/// (a file URL, or `value` holding a tab or newline); call `set_host_bytes`
/// then. `Some((None, _))`: the URL stays as it is, and the setter reports
/// failure (`out` may then hold part of a host). `Some((Some(k), h))`: the URL gets host `h`, of kind `k`, and
/// nothing else changes.
pub(crate) fn hostname_host(u: &Url, value: &[u8], out: &mut Vec<u8>, sc: &mut crate::host::Scratch) -> (r: Option<(Option<HostKind>, Ghost<Option<Host>>)>)
    requires
        u.ok(),
    ensures
        r matches Some((k, gh)) ==> match gh@ {
            None => k is None && set_hostname(u@, value@) == u@,
            Some(h) => k == Some(kind_of(h)) && set_hostname(u@, value@) == (UrlRecord { host: Some(h), ..u@ })
                && final(out)@ == old(out)@ + host_serialize(h),
        },
{
    if u.opaque_path {
        return Some((None, Ghost(None)));
    }
    if is_file_exec(scheme_of(u)) {
        return None;
    }
    let tracked mut meter = Meter { n: 0 };
    if crate::api::any_tab_newline(value, Tracked(&mut meter)) {
        return None;
    }
    proof {
        crate::api::lemma_filter_identity(value@);
    }
    let ghost st = State::Hostname;
    let ghost so = Some(st);
    let ghost url = u@;
    let ghost target = run_url(value@, None, so, initial_machine(st, url), 0);
    let v = value;
    let n = v.len();
    let special = u.special;
    let mut inside = false;
    let mut i = 0;
    proof {
        assert(v@.take(0) =~= Seq::<u8>::empty());
    }
    while i < n && !(v[i] == b':' && !inside) && !(v[i] == b'/' || v[i] == b'?' || v[i] == b'#' || (special && v[i] == b'\\'))
        invariant
            i <= n == v@.len(),
            special == is_special(url),
            url.scheme != s_file(),
            so == Some(st),
            st == State::Hostname,
            target == run_url(v@, None, so, host_machine(url, st, v@.take(i as int), inside), i as int),
        decreases n - i,
    {
        proof {
            lemma_host_char(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
            assert(v@.take(i as int).push(v@[i as int]) =~= v@.take(i + 1));
        }
        if v[i] == b'[' {
            inside = true;
        } else if v[i] == b']' {
            inside = false;
        }
        i += 1;
    }
    let buf = vstd::slice::slice_subrange(v, 0, i);
    proof {
        assert(buf@ =~= v@.take(i as int));
    }
    if i < n && v[i] == b':' && !inside {
        proof {
            lemma_host_colon(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
        }
        return Some((None, Ghost(None)));
    }
    proof {
        lemma_host_end(v@, so, host_machine(url, st, v@.take(i as int), inside), i as int);
    }
    if special && i == 0 {
        return Some((None, Ghost(None)));
    }
    if i == 0 && (u.host_start - u.scheme_end > 3 || u.port.is_some()) {
        return Some((None, Ghost(None)));
    }
    proof {
        assert(set_hostname(u@, value@) == target);
        assert(!(special && buf@.len() == 0));
        assert(!(buf@.len() == 0 && (includes_credentials(url) || url.port is Some))) by {
            if url.host is Some {
                lemma_authority_parts(u);
            }
        }
    }
    match host_parse_exec(buf, !special, out, sc, false, Tracked(&mut meter)) {
        None => Some((None, Ghost(None))),
        Some((kind, gh)) => {
            proof {
                assert(target == (UrlRecord { host: Some(gh@), ..url }));
            }
            Some((Some(kind), Ghost(Some(gh@))))
        },
    }
}

/// Whether a URL cannot have a username, password or port.
fn cannot_have_creds(u: &Url) -> (r: bool)
    requires
        u.wf(),
    ensures
        r == cannot_have_credentials_or_port(u@),
{
    match u.host_kind {
        None => true,
        Some(HostKind::Empty) => true,
        Some(_) => is_file_exec(scheme_of(u)),
    }
}

/// `u` with another port (it has a host).
fn with_port(u: &Url, port: Option<u16>) -> (r: Url)
    requires
        u.ok(),
        u@.host is Some,
    ensures
        r.ok(),
        r@ == (UrlRecord { port, ..u@ }),
{
    let hb = host_of(u).unwrap();
    let kind = u.host_kind.unwrap();
    with_host(u, hb, kind, port, Ghost(u@.host->0))
}

/// The username and password setters.
pub(crate) fn set_credential(u: &Url, value: &[u8], password: bool) -> (r: Option<Url>)
    requires
        u.ok(),
    ensures
        ({
            let want = if password { set_password(u@, value@) } else { set_username(u@, value@) };
            &&& r matches Some(n) ==> n.ok() && n@ == want
            &&& r is None ==> want == u@
        }),
{
    if cannot_have_creds(u) {
        return None;
    }
    let tracked mut meter = Meter { n: 0 };
    let mut e: Vec<u8> = Vec::new();
    append_pe(&mut e, value, 0, value.len(), EncodeSet::Userinfo, Tracked(&mut meter));
    proof {
        assert(value@.subrange(0, value@.len() as int) =~= value@);
        assert(e@ =~= pe_seq(value@, EncodeSet::Userinfo));
        lemma_pe_seq_ascii(value@, EncodeSet::Userinfo);
    }
    let ghost url = if password {
        UrlRecord { password: e@, ..u@ }
    } else {
        UrlRecord { username: e@, ..u@ }
    };
    let (un, pw) = if password {
        (username_of(u), e.as_slice())
    } else {
        (e.as_slice(), password_of(u))
    };
    let q = query_of(u);
    let f = fragment_of(u);
    Some(assemble(scheme_of(u), un, pw, host_of(u), u.host_kind, u.port, path_of(u), u.opaque_path, q, f, Ghost(url)))
}

// ---------------------------------------------------------------------------
// The port setter
// ---------------------------------------------------------------------------

fn port_override(u: &Url, v: &[u8]) -> (r: (Option<Url>, bool))
    requires
        u.ok(),
        u@.host is Some,
    ensures
        ({
            let want = run_url(v@, None, Some(State::Port), initial_machine(State::Port, u@), 0);
            &&& r.0 matches Some(n) ==> n.ok() && n@ == want
            &&& r.0 is None ==> want == u@
        }),
{
    let ghost so = Some(State::Port);
    let ghost url = u@;
    let ghost target = run_url(v@, None, so, initial_machine(State::Port, url), 0);
    let tracked mut meter = Meter { n: 0 };
    let n = v.len();
    let mut j = 0;
    proof {
        assert(v@.take(0) =~= Seq::<u8>::empty());
    }
    while j < n && v[j] >= b'0' && v[j] <= b'9'
        invariant
            j <= n == v@.len(),
            so == Some(State::Port),
            target == run_url(v@, None, so, host_machine(url, State::Port, v@.take(j as int), false), j as int),
            all_ascii_digits(v@.take(j as int)),
        decreases n - j,
    {
        proof {
            lemma_port_digit(v@, so, host_machine(url, State::Port, v@.take(j as int), false), j as int);
            assert(v@.take(j as int).push(v@[j as int]) =~= v@.take(j + 1));
        }
        j += 1;
    }
    proof {
        lemma_port_end(v@, so, host_machine(url, State::Port, v@.take(j as int), false), j as int);
    }
    if j == 0 {
        return (None, false);
    }
    let digits = vstd::slice::slice_subrange(v, 0, j);
    proof {
        assert(digits@ =~= v@.take(j as int));
    }
    let pv = port_value(digits, Tracked(&mut meter));
    if pv > 65535 {
        return (None, false);
    }
    let p = pv as u16;
    let port = if default_port_exec(scheme_of(u)) == Some(p) {
        None
    } else {
        Some(p)
    };
    (Some(with_port(u, port)), true)
}

/// The port setter.
pub(crate) fn set_port_bytes(u: &Url, value: &[u8]) -> (r: (Option<Url>, bool))
    requires
        u.ok(),
    ensures
        ({
            let want = set_port(u@, value@);
            &&& r.0 matches Some(n) ==> n.ok() && n@ == want
            &&& r.0 is None ==> want == u@
        }),
{
    if cannot_have_creds(u) {
        return (None, false);
    }
    if value.len() == 0 {
        return (Some(with_port(u, None)), true);
    }
    let v = clean(value);
    if v.len() == 0 {
        proof {
            assert(v@ =~= Seq::<u8>::empty());
            lemma_port_end(v@, Some(State::Port), initial_machine(State::Port, u@), 0);
        }
        return (None, true);
    }
    port_override(u, v.as_slice())
}

// ---------------------------------------------------------------------------
// The search and hash setters
// ---------------------------------------------------------------------------

proof fn lemma_query_run(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Query,
        m.url.query is Some,
        0 <= p <= input.len(),
    ensures
        run_url(input, None, so, m, p) == (UrlRecord {
            query: Some(m.url.query->0 + pe_seq(m.buffer + input.subrange(p, input.len() as int),
                if is_special(m.url) { EncodeSet::SpecialQuery } else { EncodeSet::Query })),
            ..m.url
        }),
    decreases input.len() - p,
{
    if p < input.len() {
        let m2 = Machine { buffer: m.buffer.push(input[p]), ..m };
        lemma_query_run(input, so, m2, p + 1);
        assert(m.buffer + input.subrange(p, input.len() as int) =~= m2.buffer + input.subrange(p + 1, input.len() as int));
    } else {
        assert(m.buffer + input.subrange(p, input.len() as int) =~= m.buffer);
    }
}

proof fn lemma_fragment_run(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Fragment,
        m.url.fragment is Some,
        0 <= p <= input.len(),
    ensures
        run_url(input, None, so, m, p) == (UrlRecord {
            fragment: Some(m.url.fragment->0 + pe_seq(input.subrange(p, input.len() as int), EncodeSet::Fragment)),
            ..m.url
        }),
    decreases input.len() - p,
{
    if p < input.len() {
        let f = m.url.fragment->0;
        let m2 = Machine { url: UrlRecord { fragment: Some(f + pe(input[p], EncodeSet::Fragment)), ..m.url }, ..m };
        lemma_fragment_run(input, so, m2, p + 1);
        let rest = input.subrange(p + 1, input.len() as int);
        assert(input.subrange(p, input.len() as int) =~= seq![input[p]] + rest);
        crate::encode::lemma_pe_seq_append(seq![input[p]], rest, EncodeSet::Fragment);
        assert(seq![input[p]] =~= Seq::<u8>::empty().push(input[p]));
        crate::encode::lemma_pe_seq_push(Seq::<u8>::empty(), input[p], EncodeSet::Fragment);
        assert(pe_seq(Seq::<u8>::empty(), EncodeSet::Fragment) =~= Seq::<u8>::empty());
        assert(f + pe(input[p], EncodeSet::Fragment) + pe_seq(rest, EncodeSet::Fragment) =~= f + pe_seq(input.subrange(p, input.len() as int), EncodeSet::Fragment));
    } else {
        assert(input.subrange(p, input.len() as int) =~= Seq::<u8>::empty());
        assert(pe_seq(Seq::<u8>::empty(), EncodeSet::Fragment) =~= Seq::<u8>::empty());
        assert(m.url.fragment->0 + Seq::<u8>::empty() =~= m.url.fragment->0);
    }
}

/// `value` without one leading `c`.
fn strip(value: &[u8], c: u8) -> (r: &[u8])
    ensures
        r@ == strip_leading(value@, c),
{
    if value.len() > 0 && value[0] == c {
        vstd::slice::slice_subrange(value, 1, value.len())
    } else {
        value
    }
}

/// The search setter.
pub(crate) fn set_search_bytes(u: &Url, value: &[u8]) -> (r: Url)
    requires
        u.ok(),
    ensures
        r.ok(),
        r@ == set_search(u@, value@),
{
    let f = fragment_of(u);
    if value.len() == 0 {
        let ghost url = UrlRecord { query: None, ..u@ };
        return assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, path_of(u), u.opaque_path, None, f, Ghost(url));
    }
    let v = clean(strip(value, b'?'));
    let set = if u.special { EncodeSet::SpecialQuery } else { EncodeSet::Query };
    let tracked mut meter = Meter { n: 0 };
    let mut q: Vec<u8> = Vec::new();
    append_pe(&mut q, v.as_slice(), 0, v.len(), set, Tracked(&mut meter));
    let ghost url0 = UrlRecord { query: Some(Seq::empty()), ..u@ };
    let ghost url = UrlRecord { query: Some(q@), ..u@ };
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
        lemma_query_run(v@, Some(State::Query), initial_machine(State::Query, url0), 0);
        assert(Seq::<u8>::empty() + v@.subrange(0, v@.len() as int) =~= v@);
        assert(Seq::<u8>::empty() + pe_seq(v@, set) =~= pe_seq(v@, set));
        assert(q@ =~= pe_seq(v@, set));
        lemma_pe_seq_ascii(v@, set);
    }
    assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, path_of(u), u.opaque_path, Some(q.as_slice()), f, Ghost(url))
}

/// The hash setter.
pub(crate) fn set_hash_bytes(u: &Url, value: &[u8]) -> (r: Url)
    requires
        u.ok(),
    ensures
        r.ok(),
        r@ == set_hash(u@, value@),
{
    let q = query_of(u);
    if value.len() == 0 {
        let ghost url = UrlRecord { fragment: None, ..u@ };
        return assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, path_of(u), u.opaque_path, q, None, Ghost(url));
    }
    let v = clean(strip(value, b'#'));
    let tracked mut meter = Meter { n: 0 };
    let mut f: Vec<u8> = Vec::new();
    append_pe(&mut f, v.as_slice(), 0, v.len(), EncodeSet::Fragment, Tracked(&mut meter));
    let ghost url0 = UrlRecord { fragment: Some(Seq::empty()), ..u@ };
    let ghost url = UrlRecord { fragment: Some(f@), ..u@ };
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
        lemma_fragment_run(v@, Some(State::Fragment), initial_machine(State::Fragment, url0), 0);
        assert(Seq::<u8>::empty() + pe_seq(v@, EncodeSet::Fragment) =~= pe_seq(v@, EncodeSet::Fragment));
        lemma_pe_seq_ascii(v@, EncodeSet::Fragment);
    }
    assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, path_of(u), u.opaque_path, q, Some(f.as_slice()), Ghost(url))
}


// ---------------------------------------------------------------------------
// The protocol setter
// ---------------------------------------------------------------------------

proof fn lemma_scheme_start(input: Seq<u8>, so: Option<State>, m: Machine)
    requires
        so is Some,
        m.state == State::SchemeStart,
        input.len() > 0,
    ensures
        run_url(input, None, so, m, 0) == (if is_ascii_alpha(input[0]) {
            run_url(input, None, so, Machine { buffer: m.buffer.push(ascii_lowercase(input[0])), state: State::Scheme, ..m }, 1)
        } else {
            m.url
        }),
{
}

proof fn lemma_scheme_char(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Scheme,
        0 <= p < input.len(),
        is_ascii_alphanumeric(input[p]) || input[p] == b'+' || input[p] == b'-' || input[p] == b'.',
    ensures
        run_url(input, None, so, m, p) == run_url(input, None, so, Machine { buffer: m.buffer.push(ascii_lowercase(input[p])), ..m }, p + 1),
{
}

proof fn lemma_scheme_end(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Scheme,
        0 <= p < input.len(),
        !(is_ascii_alphanumeric(input[p]) || input[p] == b'+' || input[p] == b'-' || input[p] == b'.'),
    ensures
        run_url(input, None, so, m, p) == (if input[p] != b':' {
            m.url
        } else {
            let url = m.url;
            let buffer = m.buffer;
            if is_special_scheme(url.scheme) && !is_special_scheme(buffer) {
                url
            } else if !is_special_scheme(url.scheme) && is_special_scheme(buffer) {
                url
            } else if (includes_credentials(url) || url.port is Some) && buffer == s_file() {
                url
            } else if url.scheme == s_file() && url.host == Some(Host::Empty) {
                url
            } else {
                let url = UrlRecord { scheme: buffer, ..url };
                if url.port == default_port(url.scheme) {
                    UrlRecord { port: None, ..url }
                } else {
                    url
                }
            }
        }),
{
}

fn lower(c: u8) -> (r: u8)
    ensures
        r == ascii_lowercase(c),
{
    if 0x41 <= c && c <= 0x5A {
        c + 32
    } else {
        c
    }
}

pub open spec fn scheme_machine(url: UrlRecord, buffer: Seq<u8>) -> Machine {
    Machine {
        state: State::Scheme,
        url,
        buffer,
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
    }
}

/// The protocol setter.
#[verifier::rlimit(40)]
pub(crate) fn set_protocol_bytes(u: &Url, value: &[u8]) -> (r: Option<Url>)
    requires
        u.ok(),
    ensures
        ({
            let want = set_protocol(u@, value@);
            &&& r matches Some(n) ==> n.ok() && n@ == want
            &&& r is None ==> want == u@
        }),
{
    let ghost url = u@;
    let ghost so = Some(State::SchemeStart);
    let mut v = clean(value);
    v.push(b':');
    proof {
        Seq::lemma_filter_push(value@, b':', |c: u8| !is_ascii_tab_or_newline(c));
        assert(v@ == remove_tab_newline(value@.push(b':')));
    }
    let ghost target = run_url(v@, None, so, initial_machine(State::SchemeStart, url), 0);
    let n = v.len();
    proof {
        lemma_scheme_start(v@, so, initial_machine(State::SchemeStart, url));
    }
    if !is_alpha(v[0]) {
        return None;
    }
    let mut buf: Vec<u8> = Vec::new();
    buf.push(lower(v[0]));
    let mut k = 1;
    proof {
        assert(buf@ =~= Seq::<u8>::empty().push(ascii_lowercase(v@[0])));
        assert(n > 1);
    }
    while is_scheme_char(v[k])
        invariant
            1 <= k < n == v@.len(),
            v@[n - 1] == b':',
            so == Some(State::SchemeStart),
            is_ascii(buf@),
            target == run_url(v@, None, so, scheme_machine(url, buf@), k as int),
        decreases n - k,
    {
        proof {
            lemma_scheme_char(v@, so, scheme_machine(url, buf@), k as int);
        }
        buf.push(lower(v[k]));
        k += 1;
    }
    proof {
        lemma_scheme_end(v@, so, scheme_machine(url, buf@), k as int);
    }
    if v[k] != b':' {
        return None;
    }
    let us = u.special;
    let bs = is_special_exec(buf.as_slice());
    if us != bs {
        return None;
    }
    let un = username_of(u);
    let pw = password_of(u);
    let file = buf.len() == 4 && buf[0] == b'f' && buf[1] == b'i' && buf[2] == b'l' && buf[3] == b'e';
    proof {
        if file {
            assert(buf@ =~= s_file());
        }
    }
    if (un.len() > 0 || pw.len() > 0 || u.port.is_some()) && file {
        return None;
    }
    let empty_host = match u.host_kind {
        Some(HostKind::Empty) => true,
        _ => false,
    };
    if is_file_exec(scheme_of(u)) && empty_host {
        return None;
    }
    let port = if u.port == default_port_exec(buf.as_slice()) {
        None
    } else {
        u.port
    };
    let ghost url2 = UrlRecord { scheme: buf@, port, ..url };
    let q = query_of(u);
    let f = fragment_of(u);
    Some(assemble(buf.as_slice(), un, pw, host_of(u), u.host_kind, port, path_of(u), u.opaque_path, q, f, Ghost(url2)))
}

// ---------------------------------------------------------------------------
// The pathname setter
// ---------------------------------------------------------------------------

/// The URL after the path state ends a segment (`spec::step_path` on EOF
/// or a slash).
pub open spec fn seg_end(url: UrlRecord, buffer: Seq<u8>, slash: bool) -> UrlRecord {
    if is_double_dot_segment(buffer) {
        let url = shorten_path(url);
        if !slash {
            push_segment(url, Seq::empty())
        } else {
            url
        }
    } else if is_single_dot_segment(buffer) && !slash {
        push_segment(url, Seq::empty())
    } else if !is_single_dot_segment(buffer) {
        let buffer = if url.scheme == s_file() && path_is_empty_list(url) && is_windows_drive_letter(buffer) {
            buffer.update(1, b':')
        } else {
            buffer
        };
        push_segment(url, buffer)
    } else {
        url
    }
}

pub open spec fn path_machine(url: UrlRecord, segs: Seq<Seq<u8>>, buffer: Seq<u8>) -> Machine {
    Machine {
        state: State::Path,
        url: UrlRecord { path: UrlPath::List(segs), ..url },
        buffer,
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
    }
}

pub open spec fn is_slash(input: Seq<u8>, p: int, special: bool) -> bool {
    c_is(input, p, b'/') || (special && c_is(input, p, b'\\'))
}

proof fn lemma_path_char(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Path,
        0 <= p < input.len(),
        !is_slash(input, p, is_special(m.url)),
    ensures
        run_url(input, None, so, m, p) == run_url(input, None, so, Machine { buffer: m.buffer + pe(input[p], EncodeSet::Path), ..m }, p + 1),
{
}

proof fn lemma_path_term(input: Seq<u8>, so: Option<State>, m: Machine, p: int)
    requires
        so is Some,
        m.state == State::Path,
        0 <= p <= input.len(),
        p < input.len() ==> is_slash(input, p, is_special(m.url)),
    ensures
        p < input.len() ==> run_url(input, None, so, m, p) == run_url(
            input,
            None,
            so,
            Machine { url: seg_end(m.url, m.buffer, true), buffer: Seq::empty(), ..m },
            p + 1,
        ),
        p == input.len() ==> run_url(input, None, so, m, p) == seg_end(m.url, m.buffer, false),
{
}

proof fn lemma_path_start(input: Seq<u8>, so: Option<State>, m: Machine)
    requires
        so is Some,
        m.state == State::PathStart,
    ensures
        is_special(m.url) ==> run_url(input, None, so, m, 0) == run_url(
            input,
            None,
            so,
            Machine { state: State::Path, ..m },
            if input.len() > 0 && (input[0] == b'/' || input[0] == b'\\') { 1 } else { 0 },
        ),
        !is_special(m.url) && input.len() > 0 ==> run_url(input, None, so, m, 0) == run_url(
            input,
            None,
            so,
            Machine { state: State::Path, ..m },
            if input[0] == b'/' { 1 } else { 0 },
        ),
        !is_special(m.url) && input.len() == 0 ==> run_url(input, None, so, m, 0) == (if m.url.host is None {
            push_segment(m.url, Seq::empty())
        } else {
            m.url
        }),
{
    let m2 = Machine { state: State::Path, ..m };
    if input.len() == 0 {
        assert(run_url(input, None, so, m2, 0) == run_url(input, None, so, m2, 0));
    }
}

/// The path being built: `out` is its serialization and `starts` where
/// each segment's "/" is.
pub open spec fn seg_inv(out: Seq<u8>, starts: Seq<usize>, segs: Seq<Seq<u8>>) -> bool {
    &&& out == segments_serialize(segs)
    &&& starts.len() == segs.len()
    &&& forall|i: int| 0 <= i < segs.len() ==> #[trigger] starts[i] == segments_serialize(segs.take(i)).len()
    &&& segments_ok(segs)
    &&& segs_ascii(segs)
}

fn push_seg(out: &mut Vec<u8>, starts: &mut Vec<usize>, seg: &[u8], Ghost(segs): Ghost<Seq<Seq<u8>>>)
    requires
        seg_inv(old(out)@, old(starts)@, segs),
        no_byte(seg@, b'/'),
        is_ascii(seg@),
    ensures
        seg_inv(final(out)@, final(starts)@, segs.push(seg@)),
{
    let tracked mut meter = Meter { n: 0 };
    let k = out.len();
    starts.push(k);
    out.push(b'/');
    append(out, seg, Tracked(&mut meter));
    proof {
        let s2 = segs.push(seg@);
        lemma_segments_push(segs, seg@);
        assert(out@ =~= segments_serialize(segs) + seq![b'/'] + seg@);
        assert forall|i: int| 0 <= i < s2.len() implies #[trigger] starts@[i] == segments_serialize(s2.take(i)).len() by {
            if i < segs.len() {
                assert(s2.take(i) =~= segs.take(i));
            } else {
                assert(s2.take(i) =~= segs);
            }
        }
        lemma_segments_ok_push(segs, seg@);
        assert forall|i: int| 0 <= i < s2.len() implies is_ascii(#[trigger] s2[i]) by {
            if i < segs.len() {
                assert(s2[i] == segs[i]);
            }
        }
    }
}

fn pop_seg(out: &mut Vec<u8>, starts: &mut Vec<usize>, Ghost(segs): Ghost<Seq<Seq<u8>>>)
    requires
        seg_inv(old(out)@, old(starts)@, segs),
        segs.len() > 0,
    ensures
        seg_inv(final(out)@, final(starts)@, segs.drop_last()),
{
    let k = starts.pop().unwrap();
    proof {
        let n = segs.len() as int;
        assert(segs.take(n - 1) =~= segs.drop_last());
        lemma_segments_last_slash(segs);
    }
    out.truncate(k);
    proof {
        let d = segs.drop_last();
        assert(out@ =~= segments_serialize(d));
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] starts@[i] == segments_serialize(d.take(i)).len() by {
            assert(d.take(i) =~= segs.take(i));
            assert(starts@[i] == old(starts)@[i]);
        }
        lemma_segments_ok_drop_last(segs);
        assert forall|i: int| 0 <= i < d.len() implies is_ascii(#[trigger] d[i]) by {
            assert(d[i] == segs[i]);
        }
    }
}

/// Ends the segment in `buf` (`seg_end`), on a slash or at the end.
fn end_seg(out: &mut Vec<u8>, starts: &mut Vec<usize>, buf: &mut Vec<u8>, slash: bool, file: bool, Ghost(url): Ghost<UrlRecord>, Ghost(segs): Ghost<Seq<Seq<u8>>>) -> (r: Ghost<Seq<Seq<u8>>>)
    requires
        seg_inv(old(out)@, old(starts)@, segs),
        no_byte(old(buf)@, b'/'),
        is_ascii(old(buf)@),
        url.path == UrlPath::List(segs),
        file == (url.scheme == s_file()),
    ensures
        seg_inv(final(out)@, final(starts)@, r@),
        seg_end(url, old(buf)@, slash) == (UrlRecord { path: UrlPath::List(r@), ..url }),
{
    let ghost b = buf@;
    let e = no_bytes();
    if is_double_dot_exec(buf.as_slice()) {
        let n = starts.len();
        let keep = file && n == 1 && out.len() == 3 && out[0] == b'/' && is_alpha(out[1]) && out[2] == b':';
        proof {
            lemma_segments_drive(segs);
            if n == 1 && out.len() == 3 {
                assert(out@[0] == out[0]);
            }
            assert(keep == (file && segs.len() == 1 && is_normalized_windows_drive_letter(segs[0])));
        }
        let ghost s1 = if keep || n == 0 { segs } else { segs.drop_last() };
        if !keep && n > 0 {
            pop_seg(out, starts, Ghost(segs));
        }
        proof {
            assert(shorten_path(url) == (UrlRecord { path: UrlPath::List(s1), ..url }));
        }
        if !slash {
            push_seg(out, starts, e, Ghost(s1));
            return Ghost(s1.push(Seq::empty()));
        }
        return Ghost(s1);
    }
    let single = is_single_dot_exec(buf.as_slice());
    if single {
        if !slash {
            push_seg(out, starts, e, Ghost(segs));
            return Ghost(segs.push(Seq::empty()));
        }
        return Ghost(segs);
    }
    let drive = file && starts.len() == 0 && buf.len() == 2 && is_alpha(buf[0]) && (buf[1] == b':' || buf[1] == b'|');
    proof {
        assert(drive == (url.scheme == s_file() && path_is_empty_list(url) && is_windows_drive_letter(b))) by {
            if segs.len() == 0 {
                assert(segs =~= Seq::<Seq<u8>>::empty());
            }
        }
    }
    if drive {
        buf.set(1, b':');
        proof {
            assert(buf@ =~= b.update(1, b':'));
        }
    }
    push_seg(out, starts, buf.as_slice(), Ghost(segs));
    Ghost(segs.push(buf@))
}

/// The pathname setter.
pub(crate) fn set_pathname_bytes(u: &Url, value: &[u8]) -> (r: Option<Url>)
    requires
        u.ok(),
    ensures
        ({
            let want = set_pathname(u@, value@);
            &&& r matches Some(n) ==> n.ok() && n@ == want
            &&& r is None ==> want == u@
        }),
{
    if u.opaque_path {
        return None;
    }
    let ghost so = Some(State::PathStart);
    let ghost url0 = UrlRecord { path: UrlPath::List(Seq::empty()), ..u@ };
    let v = clean(value);
    let ghost target = run_url(v@, None, so, initial_machine(State::PathStart, url0), 0);
    let n = v.len();
    let special = u.special;
    let file = is_file_exec(scheme_of(u));
    let q = query_of(u);
    let f = fragment_of(u);
    proof {
        lemma_path_start(v@, so, initial_machine(State::PathStart, url0));
    }
    let mut out: Vec<u8> = Vec::new();
    let mut starts: Vec<usize> = Vec::new();
    let ghost mut segs: Seq<Seq<u8>> = Seq::empty();
    proof {
        assert(segments_serialize(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
        assert(out@ =~= Seq::<u8>::empty());
        assert(starts@ =~= Seq::<usize>::empty());
        assert(url0 == (UrlRecord { path: UrlPath::List(segs), ..url0 }));
    }
    if !special && n == 0 {
        if u.host_kind.is_none() {
            push_seg(&mut out, &mut starts, no_bytes(), Ghost(segs));
            proof {
                segs = segs.push(Seq::empty());
            }
        }
        let ghost url = UrlRecord { path: UrlPath::List(segs), ..u@ };
        return Some(assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, out.as_slice(), false, q, f, Ghost(url)));
    }
    let mut p: usize = if special {
        if n > 0 && (v[0] == b'/' || v[0] == b'\\') { 1 } else { 0 }
    } else {
        if v[0] == b'/' { 1 } else { 0 }
    };
    let mut buf: Vec<u8> = Vec::new();
    proof {
        assert(buf@ =~= Seq::<u8>::empty());
        assert(initial_machine(State::PathStart, url0).buffer == Seq::<u8>::empty());
        assert(Machine { state: State::Path, ..initial_machine(State::PathStart, url0) } == path_machine(url0, segs, buf@));
    }
    while p < n
        invariant
            p <= n == v@.len(),
            so == Some(State::PathStart),
            special == is_special(url0),
            file == (url0.scheme == s_file()),
            seg_inv(out@, starts@, segs),
            no_byte(buf@, b'/'),
            is_ascii(buf@),
            target == run_url(v@, None, so, path_machine(url0, segs, buf@), p as int),
        decreases n - p,
    {
        let c = v[p];
        if c == b'/' || (special && c == b'\\') {
            proof {
                lemma_path_term(v@, so, path_machine(url0, segs, buf@), p as int);
            }
            let s2 = end_seg(&mut out, &mut starts, &mut buf, true, file, Ghost(UrlRecord { path: UrlPath::List(segs), ..url0 }), Ghost(segs));
            proof {
                segs = s2@;
            }
            buf = Vec::new();
            proof {
                assert(buf@ =~= Seq::<u8>::empty());
                assert(Machine { url: UrlRecord { path: UrlPath::List(segs), ..url0 }, buffer: Seq::empty(), ..path_machine(url0, s2@, Seq::empty()) } == path_machine(url0, segs, buf@));
            }
        } else {
            proof {
                lemma_path_char(v@, so, path_machine(url0, segs, buf@), p as int);
                assert(c != b'/');
                crate::parse::lemma_pe_seq_no_slash(seq![c], EncodeSet::Path);
                assert(seq![c] =~= Seq::<u8>::empty().push(c));
                crate::encode::lemma_pe_seq_push(Seq::<u8>::empty(), c, EncodeSet::Path);
                assert(pe_seq(Seq::<u8>::empty(), EncodeSet::Path) =~= Seq::<u8>::empty());
                assert(pe_seq(seq![c], EncodeSet::Path) =~= pe(c, EncodeSet::Path));
                lemma_pe_seq_ascii(seq![c], EncodeSet::Path);
                lemma_ascii_add(buf@, pe(c, EncodeSet::Path));
            }
            let ghost old_buf = buf@;
            push_pe(&mut buf, c, EncodeSet::Path);
            proof {
                assert(no_byte(buf@, b'/')) by {
                    assert forall|i: int| 0 <= i < buf@.len() implies buf@[i] != b'/' by {
                        if i >= old_buf.len() {
                            assert(buf@[i] == pe(c, EncodeSet::Path)[i - old_buf.len()]);
                        }
                    }
                }
            }
        }
        p += 1;
    }
    proof {
        lemma_path_term(v@, so, path_machine(url0, segs, buf@), p as int);
    }
    let s2 = end_seg(&mut out, &mut starts, &mut buf, false, file, Ghost(UrlRecord { path: UrlPath::List(segs), ..url0 }), Ghost(segs));
    let ghost url = UrlRecord { path: UrlPath::List(s2@), ..u@ };
    proof {
        assert(UrlRecord { path: UrlPath::List(s2@), ..url0 } == url);
        crate::ascii::lemma_segments_serialize_ascii(s2@);
    }
    Some(assemble(scheme_of(u), username_of(u), password_of(u), host_of(u), u.host_kind, u.port, out.as_slice(), false, q, f, Ghost(url)))
}

} // verus!
