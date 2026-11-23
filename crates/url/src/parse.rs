//! The basic URL parser, proven to compute exactly `spec::parse_url`.
//!
//! The parser runs the Standard's state machine, but writes the serialized
//! URL as it goes instead of building a URL record and serializing it at the
//! end, and runs of code points that a state handles alike (most of a path,
//! query or fragment) are processed in one go. `Parser::inv` ties the
//! parser's variables to the spec machine's (`gm`), state by state; each
//! state handler proves that running the spec machine from its old state
//! gives the same result as running it from its new one.
use crate::encode::*;
use crate::host::*;
use crate::spec::*;
use crate::tables::*;
use crate::url::*;
use vstd::prelude::*;

verus! {

pub enum Flow {
    Continue,
    Done,
    Fail,
}

pub struct Parser {
    pub href: Vec<u8>,
    pub p: usize,
    pub state: State,
    /// Start of the buffer in the input, for states whose buffer is a run of
    /// input bytes (authority, host, port, file host); in the path state,
    /// the start of the current segment in `href`.
    pub bs: usize,
    pub at_sign_seen: bool,
    pub inside_brackets: bool,
    pub pts: bool,
    pub special: bool,
    pub scheme_end: usize,
    pub username_end: usize,
    pub host_start: usize,
    pub host_end: usize,
    pub port: Option<u16>,
    pub path_start: usize,
    pub query_start: Option<usize>,
    pub fragment_start: Option<usize>,
    pub host_kind: Option<HostKind>,
    pub opaque_path: bool,
    pub gm: Ghost<Machine>,
}

/// The URL has nothing but (possibly) a scheme.
pub open spec fn fresh(url: UrlRecord) -> bool {
    &&& url.username.len() == 0
    &&& url.password.len() == 0
    &&& url.host is None
    &&& url.port is None
    &&& url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
    &&& url.query is None
    &&& url.fragment is None
}

/// The URL has a scheme, possibly credentials, and nothing else.
pub open spec fn creds_only(url: UrlRecord) -> bool {
    &&& url.host is None
    &&& url.port is None
    &&& url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
    &&& url.query is None
    &&& url.fragment is None
}

/// "scheme://" and credentials as the authority state writes them: the
/// ":" is written as soon as it is seen, the "@" not yet.
pub open spec fn authority_prefix(url: UrlRecord, pts: bool) -> Seq<u8> {
    url.scheme + seq![b':', b'/', b'/'] + url.username + (if pts {
        seq![b':'] + url.password
    } else {
        Seq::empty()
    })
}

/// "scheme://" and credentials, as serialized.
pub open spec fn head(url: UrlRecord) -> Seq<u8> {
    url.scheme + seq![b':', b'/', b'/'] + credentials_serialize(url)
}

pub open spec fn query_set(special: bool) -> EncodeSet {
    if special {
        EncodeSet::SpecialQuery
    } else {
        EncodeSet::Query
    }
}

/// The offsets of the components up to the path agree with the URL.
pub open spec fn offsets_ok(ps: &Parser, url: UrlRecord) -> bool {
    &&& ps.scheme_end == url.scheme.len()
    &&& ps.username_end == o_username_end(url)
    &&& ps.host_start == o_host_start(url)
    &&& ps.host_end == o_host_end(url)
    &&& ps.port == url.port
    &&& ps.path_start == o_path_start(url)
    &&& ps.host_kind == host_kind_of(url)
    &&& ps.opaque_path == (url.path is Opaque)
}

/// The query and fragment offsets agree with the URL.
pub open spec fn tail_offsets_ok(ps: &Parser, url: UrlRecord) -> bool {
    &&& ps.query_start == (if url.query is Some {
        Some(o_query_start(url) as usize)
    } else {
        None
    })
    &&& ps.fragment_start == (if url.fragment is Some {
        Some(o_fragment_start(url) as usize)
    } else {
        None
    })
}

/// The parser has finished: `href` is the URL's serialization (without the
/// "/." prefix) and every offset agrees.
pub open spec fn done_ok(ps: &Parser, url: UrlRecord) -> bool {
    &&& ps.href@ == core_serialize(url)
    &&& (is_special(url) ==> url.path is List)
    &&& offsets_ok(ps, url)
    &&& tail_offsets_ok(ps, url)
    &&& path_ok(url.path)
    &&& ps.special == is_special(url)
}

impl Parser {
    /// The measure the state machine's termination proof uses.
    pub open spec fn measure_lt(&self, other: &Parser) -> bool {
        let (s1, s2) = (self.state, other.state);
        phase(s1) < phase(s2) || (phase(s1) == phase(s2) && (self.p > other.p || (self.p == other.p
            && rank(s1) < rank(s2))))
    }

    pub open spec fn inv(&self, input: Seq<u8>, base: Option<UrlRecord>) -> bool {
        let m = self.gm@;
        let url = m.url;
        &&& self.p <= input.len()
        &&& self.state == m.state
        &&& self.at_sign_seen == m.at_sign_seen
        &&& self.inside_brackets == m.inside_brackets
        &&& self.pts == m.password_token_seen
        &&& self.special == is_special(url)
        &&& path_ok(url.path)
        &&& (is_special(url) ==> url.path is List)
        &&& match m.state {
            State::SchemeStart => fresh(url) && url.scheme.len() == 0 && m.buffer.len() == 0
                && self.href@.len() == 0 && !m.at_sign_seen && !m.inside_brackets
                && !m.password_token_seen,
            State::Scheme => fresh(url) && url.scheme.len() == 0 && self.href@ == m.buffer
                && !m.at_sign_seen && !m.inside_brackets && !m.password_token_seen,
            State::NoScheme => fresh(url) && url.scheme.len() == 0 && m.buffer.len() == 0
                && !m.at_sign_seen && !m.inside_brackets && !m.password_token_seen,
            State::SpecialRelativeOrAuthority | State::SpecialAuthoritySlashes
            | State::SpecialAuthorityIgnoreSlashes | State::PathOrAuthority
            | State::RelativeSlash => {
                &&& (m.state == State::SpecialRelativeOrAuthority ==> base is Some
                    && base->0.path is List && base->0.scheme == url.scheme)
                &&& (m.state == State::RelativeSlash ==> base is Some && base->0.scheme
                    == url.scheme)
                &&& fresh(url)
                &&& m.buffer.len() == 0
                &&& !m.at_sign_seen
                &&& !m.password_token_seen
                &&& !m.inside_brackets
                &&& self.href@ == url.scheme + seq![b':']
                &&& self.scheme_end == url.scheme.len()
            },
            State::Relative | State::File => {
                &&& fresh(url)
                &&& m.buffer.len() == 0
                &&& !m.at_sign_seen
                &&& !m.inside_brackets
                &&& !m.password_token_seen
                &&& (m.state == State::Relative ==> base is Some && base->0.path is List && (
                url.scheme.len() == 0 || url.scheme == base->0.scheme))
            },
            State::FileSlash => {
                &&& url.scheme == s_file()
                &&& url.host == Some(Host::Empty)
                &&& url.username.len() == 0
                &&& url.password.len() == 0
                &&& url.port is None
                &&& url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
                &&& url.query is None
                &&& url.fragment is None
                &&& m.buffer.len() == 0
                &&& !m.inside_brackets
            },
            State::Authority => {
                &&& creds_only(url)
                &&& !m.inside_brackets
                &&& self.bs <= self.p
                &&& m.buffer == input.subrange(self.bs as int, self.p as int)
                &&& self.href@ == authority_prefix(url, m.password_token_seen)
                &&& self.scheme_end == url.scheme.len()
                &&& self.username_end == url.scheme.len() + 3 + url.username.len()
                &&& (!m.password_token_seen ==> url.password.len() == 0)
            },
            State::Host | State::Hostname => {
                &&& creds_only(url)
                &&& self.bs <= self.p
                &&& m.buffer == input.subrange(self.bs as int, self.p as int)
                &&& self.href@ == head(url)
                &&& self.scheme_end == url.scheme.len()
                &&& self.username_end == url.scheme.len() + 3 + url.username.len()
                &&& self.host_start == self.href@.len()
            },
            State::Port => {
                &&& url.host is Some
                &&& url.port is None
                &&& url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
                &&& url.query is None
                &&& url.fragment is None
                &&& !m.inside_brackets
                &&& self.bs <= self.p
                &&& m.buffer == input.subrange(self.bs as int, self.p as int)
                &&& all_ascii_digits(m.buffer)
                &&& self.href@ == core_serialize(url)
                &&& self.scheme_end == url.scheme.len()
                &&& self.username_end == o_username_end(url)
                &&& self.host_start == o_host_start(url)
                &&& self.host_end == o_host_end(url)
                &&& self.host_kind == host_kind_of(url)
            },
            State::FileHost => {
                &&& url.scheme == s_file()
                &&& url.host == Some(Host::Empty)
                &&& url.username.len() == 0
                &&& url.password.len() == 0
                &&& url.port is None
                &&& url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
                &&& url.query is None
                &&& url.fragment is None
                &&& !m.inside_brackets
                &&& self.bs <= self.p
                &&& m.buffer == input.subrange(self.bs as int, self.p as int)
                &&& self.href@ == core_serialize(url)
            },
            State::PathStart => {
                &&& url.path is List
                &&& url.query is None
                &&& url.fragment is None
                &&& m.buffer.len() == 0
                &&& self.href@ == core_serialize(url)
                &&& offsets_ok(self, url)
                &&& tail_offsets_ok(self, url)
            },
            State::Path => {
                &&& url.path is List
                &&& url.query is None
                &&& url.fragment is None
                &&& no_byte(m.buffer, b'/')
                &&& self.href@ == core_serialize(url) + seq![b'/'] + m.buffer
                &&& self.bs + m.buffer.len() == self.href@.len()
                &&& offsets_ok(self, url)
                &&& tail_offsets_ok(self, url)
            },
            State::OpaquePath => {
                &&& url.path is Opaque
                &&& url.query is None
                &&& url.fragment is None
                &&& m.buffer.len() == 0
                &&& self.href@ == core_serialize(url)
                &&& offsets_ok(self, url)
                &&& tail_offsets_ok(self, url)
            },
            State::Query => {
                &&& url.query is Some
                &&& url.fragment is None
                &&& self.href@ == core_serialize(url) + pe_seq(m.buffer, query_set(self.special))
                &&& offsets_ok(self, url)
                &&& tail_offsets_ok(self, url)
            },
            State::Fragment => {
                &&& url.fragment is Some
                &&& self.href@ == core_serialize(url)
                &&& offsets_ok(self, url)
                &&& tail_offsets_ok(self, url)
            },
        }
    }
}

pub(crate) open spec fn base_rec(base: Option<&Url>) -> Option<UrlRecord> {
    match base {
        Some(b) => Some(b@),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Linear time
//
// A handler's work (the steps it adds to the meter) and the bytes it adds to
// `href` are paid for by a drop in the potential `pot`: COST_W per input byte
// consumed, and COST_W * (n + m + 2) per drop in `level`, which no
// transition raises (n is the input's length, m the base URL's). A step back
// in the input only happens with a drop in level, which more than pays for
// rereading. The bytes of `href` hold credit for removing them again (path
// shortening) or copying them once more (`finish`).
// ---------------------------------------------------------------------------

pub spec const COST_W: int = 128;

/// Every transition goes to a state of lower or equal level, and a state
/// only goes to itself by consuming input.
pub open spec fn level(s: State) -> nat {
    match s {
        State::SchemeStart => 20,
        State::Scheme => 19,
        State::NoScheme => 18,
        State::SpecialRelativeOrAuthority => 17,
        State::PathOrAuthority => 16,
        State::Relative => 15,
        State::RelativeSlash => 14,
        State::SpecialAuthoritySlashes => 13,
        State::SpecialAuthorityIgnoreSlashes => 12,
        State::Authority => 11,
        State::File => 10,
        State::FileSlash => 9,
        State::FileHost => 8,
        State::Host => 7,
        State::Hostname => 7,
        State::Port => 6,
        State::PathStart => 5,
        State::Path => 4,
        State::OpaquePath => 3,
        State::Query => 2,
        State::Fragment => 1,
    }
}

pub open spec fn base_len(base: Option<UrlRecord>) -> nat {
    match base {
        Some(u) => serialize(u, false).len(),
        None => 0,
    }
}

/// The weight of one level.
pub open spec fn level_w(input: Seq<u8>, base: Option<UrlRecord>) -> int {
    COST_W * (input.len() + base_len(base) + 2)
}

pub open spec fn pot(ps: &Parser, input: Seq<u8>, base: Option<UrlRecord>) -> int {
    level(ps.state) * level_w(input, base) + COST_W * (input.len() - ps.p) + ps.href@.len()
}

/// One level of drop pays for `w` of work.
pub proof fn lemma_level_drop(a: int, c: int, w: int)
    requires
        0 <= a < c,
        0 <= w,
    ensures
        a * w + w <= c * w,
{
    assert(a * w + w <= c * w) by (nonlinear_arith)
        requires
            0 <= a < c,
            0 <= w,
    ;
}

/// A step that lowers the level pays for up to `level_w` of work.
pub proof fn lemma_pot_drop(o: &Parser, n: &Parser, input: Seq<u8>, b: Option<UrlRecord>, c0: int, c1: int)
    requires
        level(n.state) < level(o.state),
        c1 + COST_W * (input.len() - n.p) + n.href@.len() + 1 <= c0 + level_w(input, b) + COST_W * (input.len() - o.p) + o.href@.len(),
    ensures
        c1 + pot(n, input, b) + 1 <= c0 + pot(o, input, b),
{
    lemma_level_drop(level(n.state) as int, level(o.state) as int, level_w(input, b));
}

/// A step that lowers the level by `d` pays for up to `d * level_w`.
pub proof fn lemma_pot_drop_n(o: &Parser, n: &Parser, input: Seq<u8>, b: Option<UrlRecord>, c0: int, c1: int, d: int)
    requires
        0 <= d,
        level(n.state) + d <= level(o.state),
        c1 + COST_W * (input.len() - n.p) + n.href@.len() + 1 <= c0 + d * level_w(input, b) + COST_W * (input.len() - o.p) + o.href@.len(),
    ensures
        c1 + pot(n, input, b) + 1 <= c0 + pot(o, input, b),
{
    let w = level_w(input, b);
    let a = level(n.state) as int;
    let c = level(o.state) as int;
    assert(a * w + d * w <= c * w) by (nonlinear_arith)
        requires
            0 <= a,
            a + d <= c,
            0 <= w,
    ;
}

/// A failing step at level at least `d` may spend up to `d * level_w`.
pub proof fn lemma_pot_fail(o: &Parser, input: Seq<u8>, b: Option<UrlRecord>, c0: int, c1: int, d: int)
    requires
        0 <= d <= level(o.state),
        o.p <= input.len(),
        c1 + 1 <= c0 + d * level_w(input, b) + COST_W * (input.len() - o.p) + o.href@.len(),
    ensures
        c1 + 1 <= c0 + pot(o, input, b),
{
    let w = level_w(input, b);
    let c = level(o.state) as int;
    assert(d * w <= c * w) by (nonlinear_arith)
        requires
            d <= c,
            0 <= w,
    ;
}

/// The outcome contract shared by every state handler; `c0` and `c1` are
/// the meter before and after.
pub open spec fn handler_ok(
    old_ps: &Parser,
    ps: &Parser,
    input: Seq<u8>,
    base: Option<UrlRecord>,
    r: Flow,
    c0: nat,
    c1: nat,
) -> bool {
    let before = run(input, base, None, old_ps.gm@, old_ps.p as int);
    match r {
        Flow::Continue => ps.inv(input, base) && ps.measure_lt(old_ps) && before == run(
            input,
            base,
            None,
            ps.gm@,
            ps.p as int,
        ) && c1 + pot(ps, input, base) + 1 <= c0 + pot(old_ps, input, base),
        Flow::Done => done_ok(ps, ps.gm@.url) && before == Some(ps.gm@.url) && c1 + ps.href@.len()
            + 1 <= c0 + pot(old_ps, input, base),
        Flow::Fail => before is None && c1 + 1 <= c0 + pot(old_ps, input, base),
    }
}

pub fn bytes_eq(a: &[u8], b: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    ensures
        final(cost).n <= old(cost).n + a.len() + 1,
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
            cost.n <= old(cost).n + i,
        decreases a.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
        }
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

pub fn is_file_exec(s: &[u8]) -> (r: bool)
    ensures
        r == (s@ == s_file()),
{
    let r = s.len() == 4 && s[0] == b'f' && s[1] == b'i' && s[2] == b'l' && s[3] == b'e';
    proof {
        if r {
            assert(s@ =~= s_file());
        }
        if s@ == s_file() {
            assert(s@[0] == b'f' && s@[1] == b'i' && s@[2] == b'l' && s@[3] == b'e');
        }
    }
    r
}

pub fn is_special_exec(s: &[u8]) -> (r: bool)
    ensures
        r == is_special_scheme(s@),
{
    let n = s.len();
    let r = if n == 2 {
        s[0] == b'w' && s[1] == b's'
    } else if n == 3 {
        (s[0] == b'f' && s[1] == b't' && s[2] == b'p') || (s[0] == b'w' && s[1] == b's' && s[2]
            == b's')
    } else if n == 4 {
        (s[0] == b'h' && s[1] == b't' && s[2] == b't' && s[3] == b'p') || (s[0] == b'f' && s[1]
            == b'i' && s[2] == b'l' && s[3] == b'e')
    } else if n == 5 {
        s[0] == b'h' && s[1] == b't' && s[2] == b't' && s[3] == b'p' && s[4] == b's'
    } else {
        false
    };
    proof {
        let v = s@;
        if r {
            if n == 2 {
                assert(v =~= s_ws());
            } else if n == 3 {
                if v[0] == b'f' {
                    assert(v =~= s_ftp());
                } else {
                    assert(v =~= s_wss());
                }
            } else if n == 4 {
                if v[0] == b'h' {
                    assert(v =~= s_http());
                } else {
                    assert(v =~= s_file());
                }
            } else {
                assert(v =~= s_https());
            }
        }
        if v == s_ftp() || v == s_file() || v == s_http() || v == s_https() || v == s_ws() || v
            == s_wss() {
            assert(v[0] == s@[0]);
        }
    }
    r
}

/// The scheme of a well-formed URL, as a slice of its href.
pub(crate) fn url_scheme(u: &Url) -> (r: &[u8])
    requires
        u.wf(),
    ensures
        r@ == u@.scheme,
{
    proof {
        lemma_serialize_parts(u@);
    }
    vstd::slice::slice_subrange(u.href.as_slice(), 0, u.scheme_end)
}

pub fn is_scheme_char(c: u8) -> (r: bool)
    ensures
        r == (is_ascii_alphanumeric(c) || c == b'+' || c == b'-' || c == b'.'),
{
    is_alpha(c) || is_digit(c) || c == b'+' || c == b'-' || c == b'.'
}

fn h_scheme_start(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::SchemeStart,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    if p < input.len() && is_alpha(input[p]) {
        let c = to_lower(input[p]);
        ps.href.push(c);
        ps.gm = Ghost(Machine { buffer: ps.gm@.buffer.push(c), state: State::Scheme, ..ps.gm@ });
        ps.state = State::Scheme;
        ps.p = p + 1;
        proof {
            assert(ps.href@ =~= ps.gm@.buffer);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    } else {
        ps.gm = Ghost(Machine { state: State::NoScheme, ..ps.gm@ });
        ps.state = State::NoScheme;
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    }
}

#[verifier::rlimit(40)]
fn h_scheme(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Scheme,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    let mut k = ps.p;
    while k < input.len() && is_scheme_char(input[k])
        invariant
            ps.inv(input@, b),
            ps.state == State::Scheme,
            ps.p == old(ps).p,
            old(ps).p <= k <= input.len(),
            target == run(input@, b, None, ps.gm@, k as int),
            cost.n == old(cost).n + (k - old(ps).p),
            ps.href@.len() == old(ps).href@.len() + (k - old(ps).p),
        decreases input.len() - k,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let c = to_lower(input[k]);
        ps.href.push(c);
        ps.gm = Ghost(Machine { buffer: ps.gm@.buffer.push(c), ..ps.gm@ });
        proof {
            assert(ps.href@ =~= ps.gm@.buffer);
        }
        k = k + 1;
    }
    if k < input.len() && input[k] == b':' {
        let sl = ps.href.len();
        let special = is_special_exec(ps.href.as_slice());
        let file = is_file_exec(ps.href.as_slice());
        let same_as_base = match base {
            Some(bu) => {
                proof {
                    lemma_serialize_parts(bu@);
                }
                bytes_eq(url_scheme(bu), ps.href.as_slice(), Tracked(cost))
            },
            None => false,
        };
        proof {
            assert(cost.n <= old(cost).n + (k - old(ps).p) + base_len(b) + 1);
        }
        let ghost scheme = ps.gm@.buffer;
        let ghost url = UrlRecord { scheme, ..ps.gm@.url };
        ps.href.push(b':');
        ps.scheme_end = sl;
        ps.special = special;
        proof {
            assert(ps.href@ =~= url.scheme + seq![b':']);
        }
        if file {
            ps.gm = Ghost(Machine { url, buffer: Seq::empty(), state: State::File, ..ps.gm@ });
            ps.state = State::File;
            ps.p = k + 1;
            proof {
                lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
                assert(ps.href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1);
                assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
            }
            Flow::Continue
        } else if special && same_as_base {
            ps.gm = Ghost(
                Machine {
                    url,
                    buffer: Seq::empty(),
                    state: State::SpecialRelativeOrAuthority,
                    ..ps.gm@
                },
            );
            ps.state = State::SpecialRelativeOrAuthority;
            ps.p = k + 1;
            proof {
                lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
                assert(ps.href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1);
                assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
            }
            Flow::Continue
        } else if special {
            ps.gm = Ghost(
                Machine { url, buffer: Seq::empty(), state: State::SpecialAuthoritySlashes, ..ps.gm@ },
            );
            ps.state = State::SpecialAuthoritySlashes;
            ps.p = k + 1;
            proof {
                lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
                assert(ps.href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1);
                assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
            }
            Flow::Continue
        } else if k + 1 < input.len() && input[k + 1] == b'/' {
            ps.gm = Ghost(
                Machine { url, buffer: Seq::empty(), state: State::PathOrAuthority, ..ps.gm@ },
            );
            ps.state = State::PathOrAuthority;
            ps.p = k + 2;
            proof {
                lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
                assert(ps.href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1);
                assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
            }
            Flow::Continue
        } else {
            let ghost url2 = UrlRecord { path: UrlPath::Opaque(Seq::empty()), ..url };
            ps.gm = Ghost(
                Machine { url: url2, buffer: Seq::empty(), state: State::OpaquePath, ..ps.gm@ },
            );
            ps.state = State::OpaquePath;
            let sl1 = ps.href.len();
            ps.username_end = sl1;
            ps.host_start = sl1;
            ps.host_end = sl1;
            ps.port = None;
            ps.path_start = sl1;
            ps.host_kind = None;
            ps.opaque_path = true;
            ps.query_start = None;
            ps.fragment_start = None;
            proof {
                assert(core_serialize(url2) =~= url.scheme + seq![b':']);
            }
            ps.p = k + 1;
            proof {
                lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
                assert(ps.href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1);
                assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
            }
            Flow::Continue
        }
    } else {
        ps.href.clear();
        ps.gm = Ghost(Machine { buffer: Seq::empty(), state: State::NoScheme, ..ps.gm@ });
        ps.state = State::NoScheme;
        ps.p = 0;
        proof {
            lemma_level_drop(level(ps.state) as int, level(old(ps).state) as int, level_w(input@, b));
            assert(cost.n + pot(ps, input@, b) + 1 <= old(cost).n + pot(old(ps), input@, b));
        }
        Flow::Continue
    }
}

/// A fragment-only reference against a base with an opaque path.
fn no_scheme_fragment(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::NoScheme,
        base == Some(bu),
        bu.wf(),
        bu.opaque_path,
        old(ps).p < input.len() && input@[old(ps).p as int] == b'#',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    let ghost b = bu@;
    proof {
        lemma_serialize_parts(b);
        assert(dot_len(b) == 0);
    }
    let sl = bu.scheme_end;
    let pe = match bu.fragment_start {
        Some(f) => f,
        None => bu.href.len(),
    };
    ps.href.clear();
    append_range(&mut ps.href, bu.href.as_slice(), 0, sl + 1, Tracked(cost));
    let ps0 = ps.href.len();
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, pe, Tracked(cost));
    let ghost url = UrlRecord {
        scheme: b.scheme,
        path: b.path,
        query: b.query,
        fragment: Some(Seq::empty()),
        ..ps.gm@.url
    };
    ps.query_start = match bu.query_start {
        Some(q) => Some(q - bu.path_start + ps0),
        None => None,
    };
    ps.fragment_start = Some(ps.href.len());
    ps.href.push(b'#');
    ps.scheme_end = sl;
    ps.username_end = ps0;
    ps.host_start = ps0;
    ps.host_end = ps0;
    ps.port = None;
    ps.path_start = ps0;
    ps.host_kind = None;
    ps.opaque_path = true;
    ps.special = bu.special;
    ps.gm = Ghost(Machine { url, state: State::Fragment, ..ps.gm@ });
    ps.state = State::Fragment;
    ps.p = p + 1;
    proof {
        assert(ps.href@ =~= core_serialize(url));
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn h_no_scheme(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::NoScheme,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    match base {
        None => Flow::Fail,
        Some(bu) => {
            let hash = p < input.len() && input[p] == b'#';
            if bu.opaque_path && hash {
                no_scheme_fragment(ps, input, base, bu, Tracked(cost))
            } else if bu.opaque_path {
                Flow::Fail
            } else if !is_file_exec(url_scheme(bu)) {
                ps.gm = Ghost(Machine { state: State::Relative, ..ps.gm@ });
                ps.state = State::Relative;
                proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
                Flow::Continue
            } else {
                ps.gm = Ghost(Machine { state: State::File, ..ps.gm@ });
                ps.state = State::File;
                proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
                Flow::Continue
            }
        },
    }
}

fn h_special_relative_or_authority(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::SpecialRelativeOrAuthority,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    if p < input.len() && input[p] == b'/' && p + 1 < input.len() && input[p + 1] == b'/' {
        ps.gm = Ghost(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..ps.gm@ });
        ps.state = State::SpecialAuthorityIgnoreSlashes;
        ps.p = p + 2;
    } else {
        ps.gm = Ghost(Machine { state: State::Relative, ..ps.gm@ });
        ps.state = State::Relative;
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn h_path_or_authority(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::PathOrAuthority,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    if p < input.len() && input[p] == b'/' {
        enter_authority(ps, input, base, p + 1);
    } else {
        let n = ps.href.len();
        ps.username_end = n;
        ps.host_start = n;
        ps.host_end = n;
        ps.port = None;
        ps.path_start = n;
        ps.host_kind = None;
        ps.opaque_path = false;
        ps.query_start = None;
        ps.fragment_start = None;
        proof {
            assert(core_serialize(ps.gm@.url) =~= ps.href@);
            assert(ps.gm@.buffer =~= Seq::<u8>::empty());
        }
        enter_path(ps, input, base);
    }
    proof {
        lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int);
    }
    Flow::Continue
}

/// Moves from a state whose href is the core serialization of a URL with an
/// empty list path to the path state, with the pointer where it is.
fn enter_path(ps: &mut Parser, input: &[u8], base: Option<&Url>)
    requires
        old(ps).p <= input.len(),
        old(ps).gm@.url.path is List,
        path_ok(old(ps).gm@.url.path),
        old(ps).gm@.url.query is None,
        old(ps).gm@.url.fragment is None,
        old(ps).href@ == core_serialize(old(ps).gm@.url),
        offsets_ok(old(ps), old(ps).gm@.url),
        tail_offsets_ok(old(ps), old(ps).gm@.url),
        old(ps).special == is_special(old(ps).gm@.url),
        old(ps).at_sign_seen == old(ps).gm@.at_sign_seen,
        old(ps).inside_brackets == old(ps).gm@.inside_brackets,
        old(ps).pts == old(ps).gm@.password_token_seen,
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).gm@ == (Machine { state: State::Path, buffer: Seq::empty(), ..old(ps).gm@ }),
        final(ps).state == State::Path,
        final(ps).p == old(ps).p,
        final(ps).href@.len() == old(ps).href@.len() + 1,
{
    ps.href.push(b'/');
    ps.bs = ps.href.len();
    ps.gm = Ghost(Machine { state: State::Path, buffer: Seq::empty(), ..ps.gm@ });
    ps.state = State::Path;
    proof {
        assert(ps.href@ =~= core_serialize(ps.gm@.url) + seq![b'/'] + ps.gm@.buffer);
    }
}

/// Shortens the path of a URL whose core serialization is `href` and whose
/// query and fragment are null.
#[verifier::rlimit(30)]
fn shorten_exec(href: &mut Vec<u8>, scheme_end: usize, path_start: usize, Ghost(url): Ghost<UrlRecord>, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(href)@ == core_serialize(url),
        url.path is List,
        path_ok(url.path),
        url.query is None,
        url.fragment is None,
        scheme_end == url.scheme.len(),
        path_start == o_path_start(url),
    ensures
        final(cost).n + final(href)@.len() <= old(cost).n + old(href)@.len() + 1,
        final(href)@ == core_serialize(shorten_path(url)),
        path_ok(shorten_path(url).path),
        shorten_path(url).path is List,
        o_path_start(shorten_path(url)) == o_path_start(url),
{
    let ghost segs = url.path->List_0;
    proof {
        lemma_core_parts(url);
        lemma_segments_drive(segs);
        lemma_segments_len(segs);
    }
    let n = href.len();
    let file = is_file_exec(vstd::slice::slice_subrange(href.as_slice(), 0, scheme_end));
    let ghost region = href@.subrange(path_start as int, n as int);
    proof {
        assert(region == segments_serialize(segs));
        if n - path_start == 3 {
            assert(region[0] == href@[path_start as int]);
            assert(region[1] == href@[path_start + 1]);
            assert(region[2] == href@[path_start + 2]);
        }
    }
    if file && n - path_start == 3 && href[path_start] == b'/' && is_alpha(href[path_start + 1])
        && href[path_start + 2] == b':' {
        return;
    }
    if n == path_start {
        proof {
            assert(segs.len() == 0);
        }
        return;
    }
    proof {
        assert(segs.len() > 0);
        lemma_segments_last_slash(segs);
        lemma_segments_ok_drop_last(segs);
    }
    let ghost kk = path_start + segments_serialize(segs.drop_last()).len();
    match last_index_of(href.as_slice(), n, b'/', Tracked(cost)) {
        Some(k) => {
            proof {
                assert(href@[kk] == region[kk - path_start]);
                if k < kk {
                    assert(href@.subrange(k + 1, n as int)[kk - k - 1] == href@[kk]);
                } else if k > kk {
                    assert(href@[k as int] == region[k - path_start]);
                }
                assert(k == kk);
            }
            href.truncate(k);
            proof {
                let u2 = shorten_path(url);
                lemma_core_parts(u2);
                assert(href@ =~= core_serialize(u2));
            }
        },
        None => {
            proof {
                assert(href@.subrange(0, n as int)[kk] == href@[kk]);
                assert(href@[kk] == region[kk - path_start]);
            }
            return;
        },
    }
}

/// The URL the relative state builds when c is not a slash: the base's
/// everything but the fragment.
pub open spec fn relative_url(url: UrlRecord, b: UrlRecord) -> UrlRecord {
    UrlRecord {
        scheme: b.scheme,
        username: b.username,
        password: b.password,
        host: b.host,
        port: b.port,
        path: b.path,
        query: b.query,
        ..url
    }
}

/// Writes the base's serialization up to its path (without "/.") and sets
/// the offsets up to the path from it.
fn copy_base_prefix(ps: &mut Parser, bu: &Url, Tracked(cost): Tracked<&mut Meter>)
    requires
        bu.wf(),
    ensures
        final(cost).n == old(cost).n + final(ps).href@.len(),
        final(ps).href@.len() <= bu.href@.len(),
        final(ps).href@ == bu@.scheme + seq![b':'] + authority_serialize(bu@),
        final(ps).scheme_end == bu.scheme_end,
        final(ps).username_end == bu.username_end,
        final(ps).host_start == bu.host_start,
        final(ps).host_end == bu.host_end,
        final(ps).port == bu.port,
        final(ps).host_kind == bu.host_kind,
        final(ps).path_start == o_path_start(bu@),
        final(ps).special == bu.special,
        final(ps).opaque_path == bu.opaque_path,
        final(ps).p == old(ps).p,
        final(ps).state == old(ps).state,
        final(ps).gm == old(ps).gm,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).pts == old(ps).pts,
{
    proof {
        lemma_serialize_parts(bu@);
    }
    let cps = if bu.has_dot {
        bu.path_start - 2
    } else {
        bu.path_start
    };
    ps.href.clear();
    append_range(&mut ps.href, bu.href.as_slice(), 0, cps, Tracked(cost));
    ps.scheme_end = bu.scheme_end;
    ps.username_end = bu.username_end;
    ps.host_start = bu.host_start;
    ps.host_end = bu.host_end;
    ps.port = bu.port;
    ps.host_kind = bu.host_kind;
    ps.path_start = cps;
    ps.special = bu.special;
    ps.opaque_path = bu.opaque_path;
}

/// The end of the base's path, and of its query, in its href.
fn base_ends(bu: &Url) -> (r: (usize, usize))
    requires
        bu.wf(),
    ensures
        r.0 == o_query_start(bu@) + dot_len(bu@),
        r.1 == o_fragment_start(bu@) + dot_len(bu@),
        bu.path_start <= r.0 <= r.1 <= bu.href@.len(),
{
    proof {
        lemma_serialize_parts(bu@);
    }
    let query_end = match bu.fragment_start {
        Some(f) => f,
        None => bu.href.len(),
    };
    let path_end = match bu.query_start {
        Some(q) => q,
        None => query_end,
    };
    (path_end, query_end)
}

fn h_relative(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Relative,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let bu = match base {
        None => {
            return Flow::Fail;
        },
        Some(bu) => bu,
    };
    let p = ps.p;
    let special = bu.special;
    if p < input.len() && (input[p] == b'/' || (special && input[p] == b'\\')) {
        let ghost b = bu@;
        proof {
            lemma_serialize_parts(b);
        }
        let sl = bu.scheme_end;
        ps.href.clear();
        ps.special = special;
        ps.scheme_end = sl;
        append_range(&mut ps.href, bu.href.as_slice(), 0, sl + 1, Tracked(cost));
        ps.gm = Ghost(
            Machine {
                state: State::RelativeSlash,
                url: UrlRecord { scheme: b.scheme, ..ps.gm@.url },
                ..ps.gm@
            },
        );
        ps.state = State::RelativeSlash;
        ps.p = p + 1;
        proof {
            assert(ps.gm@.buffer =~= Seq::<u8>::empty());
        }
        return Flow::Continue;
    }
    if p < input.len() && input[p] == b'?' {
        relative_query(ps, input, base, bu, Tracked(cost))
    } else if p < input.len() && input[p] == b'#' {
        relative_fragment(ps, input, base, bu, Tracked(cost))
    } else if p < input.len() {
        relative_path(ps, input, base, bu, Tracked(cost))
    } else {
        relative_eof(ps, input, base, bu, Tracked(cost))
    }
}

fn relative_query(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Relative,
        base == Some(bu),
        bu.wf(),
        old(ps).p < input.len() && input@[old(ps).p as int] == b'?',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = bu@;
    let ghost url = relative_url(ps.gm@.url, b);
    let p = ps.p;
    copy_base_prefix(ps, bu, Tracked(cost));
    let (path_end, _) = base_ends(bu);
    proof {
        lemma_serialize_parts(b);
    }
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, path_end, Tracked(cost));
    let ghost url2 = UrlRecord { query: Some(Seq::empty()), ..url };
    ps.query_start = Some(ps.href.len());
    ps.fragment_start = None;
    ps.href.push(b'?');
    ps.gm = Ghost(Machine { state: State::Query, url: url2, ..ps.gm@ });
    ps.state = State::Query;
    ps.p = p + 1;
    proof {
        lemma_core_parts(url2);
        assert(ps.href@ =~= core_serialize(url2) + pe_seq(ps.gm@.buffer, query_set(ps.special)));
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn relative_fragment(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Relative,
        base == Some(bu),
        bu.wf(),
        old(ps).p < input.len() && input@[old(ps).p as int] == b'#',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = bu@;
    let ghost url = relative_url(ps.gm@.url, b);
    let p = ps.p;
    copy_base_prefix(ps, bu, Tracked(cost));
    let (_, query_end) = base_ends(bu);
    proof {
        lemma_serialize_parts(b);
    }
    let cps = ps.href.len();
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, query_end, Tracked(cost));
    let ghost url2 = UrlRecord { fragment: Some(Seq::empty()), ..url };
    ps.query_start = match bu.query_start {
        Some(q) => Some(q - bu.path_start + cps),
        None => None,
    };
    ps.fragment_start = Some(ps.href.len());
    ps.href.push(b'#');
    ps.gm = Ghost(Machine { state: State::Fragment, url: url2, ..ps.gm@ });
    ps.state = State::Fragment;
    ps.p = p + 1;
    proof {
        lemma_core_parts(url2);
        assert(ps.href@ =~= core_serialize(url2));
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn relative_path(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Relative,
        base == Some(bu),
        bu.wf(),
        old(ps).p < input.len(),
        input@[old(ps).p as int] != b'?',
        input@[old(ps).p as int] != b'#',
        input@[old(ps).p as int] != b'/',
        !(bu.special && input@[old(ps).p as int] == b'\\'),
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = bu@;
    let ghost url1 = UrlRecord { query: None, ..relative_url(ps.gm@.url, b) };
    copy_base_prefix(ps, bu, Tracked(cost));
    let (path_end, _) = base_ends(bu);
    proof {
        lemma_serialize_parts(b);
    }
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, path_end, Tracked(cost));
    proof {
        lemma_core_parts(url1);
        assert(ps.href@ =~= core_serialize(url1));
    }
    shorten_exec(&mut ps.href, ps.scheme_end, ps.path_start, Ghost(url1), Tracked(cost));
    ps.query_start = None;
    ps.fragment_start = None;
    ps.gm = Ghost(Machine { url: shorten_path(url1), ..ps.gm@ });
    proof {
        assert(ps.gm@.buffer =~= Seq::<u8>::empty());
    }
    enter_path(ps, input, base);
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn relative_eof(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Relative,
        base == Some(bu),
        bu.wf(),
        old(ps).p >= input.len(),
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = bu@;
    let ghost url = relative_url(ps.gm@.url, b);
    copy_base_prefix(ps, bu, Tracked(cost));
    let (_, query_end) = base_ends(bu);
    proof {
        lemma_serialize_parts(b);
    }
    let cps = ps.href.len();
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, query_end, Tracked(cost));
    ps.query_start = match bu.query_start {
        Some(q) => Some(q - bu.path_start + cps),
        None => None,
    };
    ps.fragment_start = None;
    ps.gm = Ghost(Machine { url, ..ps.gm@ });
    proof {
        lemma_core_parts(url);
        assert(ps.href@ =~= core_serialize(url));
    }
    proof { lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1); }
    Flow::Done
}

fn h_relative_slash(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::RelativeSlash,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    if ps.special && p < input.len() && (input[p] == b'/' || input[p] == b'\\') {
        ps.gm = Ghost(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..ps.gm@ });
        ps.state = State::SpecialAuthorityIgnoreSlashes;
        ps.p = p + 1;
        proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
        return Flow::Continue;
    }
    if p < input.len() && input[p] == b'/' {
        enter_authority(ps, input, base, p + 1);
        proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
        return Flow::Continue;
    }
    let bu = match base {
        None => {
            return Flow::Fail;
        },
        Some(bu) => bu,
    };
    let ghost b = bu@;
    let ghost url = UrlRecord {
        username: b.username,
        password: b.password,
        host: b.host,
        port: b.port,
        ..ps.gm@.url
    };
    copy_base_prefix(ps, bu, Tracked(cost));
    ps.opaque_path = false;
    ps.query_start = None;
    ps.fragment_start = None;
    ps.gm = Ghost(Machine { url, ..ps.gm@ });
    proof {
        lemma_core_parts(url);
        assert(authority_serialize(url) == authority_serialize(b));
        assert(path_serialize(url.path) =~= Seq::<u8>::empty());
        assert(ps.href@ =~= core_serialize(url));
        assert(ps.gm@.buffer =~= Seq::<u8>::empty());
    }
    enter_path(ps, input, base);
    proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
    Flow::Continue
}

fn h_special_authority_slashes(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::SpecialAuthoritySlashes,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    ps.gm = Ghost(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..ps.gm@ });
    ps.state = State::SpecialAuthorityIgnoreSlashes;
    if p < input.len() && input[p] == b'/' && p + 1 < input.len() && input[p + 1] == b'/' {
        ps.p = p + 2;
    }
    proof { lemma_pot_drop(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int); }
    Flow::Continue
}

/// Moves from a state whose href is "scheme:" to the authority state, with
/// the pointer at `p`.
fn enter_authority(ps: &mut Parser, input: &[u8], base: Option<&Url>, p: usize)
    requires
        old(ps).inv(input@, base_rec(base)),
        p <= input.len(),
        fresh(old(ps).gm@.url),
        old(ps).href@ == old(ps).gm@.url.scheme + seq![b':'],
        old(ps).scheme_end == old(ps).gm@.url.scheme.len(),
        !old(ps).gm@.at_sign_seen,
        !old(ps).gm@.password_token_seen,
        !old(ps).gm@.inside_brackets,
        old(ps).gm@.buffer.len() == 0,
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).gm@ == (Machine { state: State::Authority, ..old(ps).gm@ }),
        final(ps).state == State::Authority,
        final(ps).p == p,
        final(ps).href@.len() == old(ps).href@.len() + 2,
{
    ps.href.push(b'/');
    ps.href.push(b'/');
    ps.username_end = ps.href.len();
    ps.bs = p;
    ps.p = p;
    ps.gm = Ghost(Machine { state: State::Authority, ..ps.gm@ });
    ps.state = State::Authority;
    proof {
        assert(ps.href@ =~= authority_prefix(ps.gm@.url, false));
        assert(input@.subrange(p as int, p as int) =~= ps.gm@.buffer);
    }
}

fn h_special_authority_ignore_slashes(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::SpecialAuthorityIgnoreSlashes,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    let mut k = ps.p;
    while k < input.len() && (input[k] == b'/' || input[k] == b'\\')
        invariant
            old(ps).p <= k <= input.len(),
            target == run(input@, b, None, ps.gm@, k as int),
            *ps == *old(ps),
            ps.inv(input@, b),
            ps.state == State::SpecialAuthorityIgnoreSlashes,
        decreases input.len() - k,
    {
        proof {
            assert(step(input@, b, None, ps.gm@, k as int) == Step::Next(ps.gm@, k as int));
        }
        k = k + 1;
    }
    enter_authority(ps, input, base, k);
    Flow::Continue
}

pub open spec fn userinfo_step(c: u8, u: Seq<u8>, pw: Seq<u8>, pts: bool) -> (Seq<u8>, Seq<u8>, bool) {
    if c == b':' && !pts {
        (u, pw, true)
    } else if pts {
        (u, pw + pe(c, EncodeSet::Userinfo), pts)
    } else {
        (u + pe(c, EncodeSet::Userinfo), pw, pts)
    }
}

/// One step of the machine, as `run` takes it.
proof fn lemma_run_next(
    input: Seq<u8>,
    b: Option<UrlRecord>,
    m: Machine,
    p: int,
    m2: Machine,
    p2: int,
)
    requires
        0 <= p <= input.len(),
        step(input, b, None, m, p) == Step::Next(m2, p2),
        -1 <= p2 < input.len(),
    ensures
        run(input, b, None, m, p) == run(input, b, None, m2, p2 + 1),
{
}

/// A step at the end of the input finishes the run.
proof fn lemma_run_eof(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, m2: Machine)
    requires
        step(input, b, None, m, input.len() as int) == Step::Next(m2, input.len() as int),
    ensures
        run(input, b, None, m, input.len() as int) == Some(m2.url),
{
}

proof fn lemma_run_fail(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        step(input, b, None, m, p) == Step::Fail,
    ensures
        run(input, b, None, m, p) is None,
{
}

proof fn lemma_step_authority_end(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::Authority,
        is_authority_end(input, p, is_special(m.url)),
    ensures
        step(input, b, None, m, p) == if m.at_sign_seen && m.buffer.len() == 0 {
            Step::Fail
        } else {
            Step::Next(Machine { buffer: Seq::empty(), state: State::Host, ..m }, p - m.buffer.len() - 1)
        },
{
}

proof fn lemma_step_authority_char(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p < input.len(),
        m.state == State::Authority,
        !is_authority_end(input, p, is_special(m.url)),
        input[p] != b'@',
    ensures
        step(input, b, None, m, p) == Step::Next(Machine { buffer: m.buffer.push(input[p]), ..m }, p),
{
}

proof fn lemma_append_userinfo_cons(c: u8, rest: Seq<u8>, u: Seq<u8>, pw: Seq<u8>, pts: bool)
    ensures
        append_userinfo(seq![c] + rest, u, pw, pts) == ({
            let (u2, pw2, pts2) = userinfo_step(c, u, pw, pts);
            append_userinfo(rest, u2, pw2, pts2)
        }),
{
    let s = seq![c] + rest;
    assert(s[0] == c);
    assert(s.skip(1) =~= rest);
}

proof fn lemma_append_userinfo_concat(a: Seq<u8>, b: Seq<u8>, u: Seq<u8>, pw: Seq<u8>, pts: bool)
    ensures
        append_userinfo(a + b, u, pw, pts) == ({
            let (u2, pw2, pts2) = append_userinfo(a, u, pw, pts);
            append_userinfo(b, u2, pw2, pts2)
        }),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        let c = a[0];
        assert(a =~= seq![c] + a.skip(1));
        assert(a + b =~= seq![c] + (a.skip(1) + b));
        lemma_append_userinfo_cons(c, a.skip(1) + b, u, pw, pts);
        lemma_append_userinfo_cons(c, a.skip(1), u, pw, pts);
        let (u2, pw2, pts2) = userinfo_step(c, u, pw, pts);
        lemma_append_userinfo_concat(a.skip(1), b, u2, pw2, pts2);
    }
}

/// One byte of the authority state's userinfo loop.
fn userinfo_byte(ps: &mut Parser, c: u8)
    requires
        old(ps).href@ == authority_prefix(old(ps).gm@.url, old(ps).pts),
        old(ps).username_end == old(ps).gm@.url.scheme.len() + 3 + old(ps).gm@.url.username.len(),
        !old(ps).pts ==> old(ps).gm@.url.password.len() == 0,
        old(ps).pts == old(ps).gm@.password_token_seen,
    ensures
        ({
            let (u2, pw2, pts2) = userinfo_step(
                c,
                old(ps).gm@.url.username,
                old(ps).gm@.url.password,
                old(ps).pts,
            );
            &&& final(ps).gm@ == (Machine {
                url: UrlRecord { username: u2, password: pw2, ..old(ps).gm@.url },
                password_token_seen: pts2,
                ..old(ps).gm@
            })
            &&& final(ps).pts == pts2
        }),
        final(ps).href@ == authority_prefix(final(ps).gm@.url, final(ps).pts),
        final(ps).username_end == final(ps).gm@.url.scheme.len() + 3 + final(ps).gm@.url.username.len(),
        !final(ps).pts ==> final(ps).gm@.url.password.len() == 0,
        final(ps).p == old(ps).p,
        final(ps).bs == old(ps).bs,
        final(ps).state == old(ps).state,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).special == old(ps).special,
        final(ps).scheme_end == old(ps).scheme_end,
        final(ps).href@.len() <= old(ps).href@.len() + 3,
{
    let ghost url = ps.gm@.url;
    proof {
        lemma_pe_len(c, EncodeSet::Userinfo);
    }
    if c == b':' && !ps.pts {
        ps.href.push(b':');
        ps.pts = true;
        ps.gm = Ghost(Machine { password_token_seen: true, ..ps.gm@ });
        proof {
            assert(url.password =~= Seq::<u8>::empty());
            assert(ps.href@ =~= authority_prefix(ps.gm@.url, true));
        }
    } else if ps.pts {
        push_pe(&mut ps.href, c, EncodeSet::Userinfo);
        ps.gm = Ghost(
            Machine {
                url: UrlRecord { password: url.password + pe(c, EncodeSet::Userinfo), ..url },
                ..ps.gm@
            },
        );
        proof {
            assert(ps.href@ =~= authority_prefix(ps.gm@.url, true));
        }
    } else {
        push_pe(&mut ps.href, c, EncodeSet::Userinfo);
        ps.username_end = ps.href.len();
        ps.gm = Ghost(
            Machine {
                url: UrlRecord { username: url.username + pe(c, EncodeSet::Userinfo), ..url },
                ..ps.gm@
            },
        );
        proof {
            assert(ps.href@ =~= authority_prefix(ps.gm@.url, false));
        }
    }
}

/// The authority state at its end character: write the "@", go back to
/// the start of the host.
fn authority_end(ps: &mut Parser, input: &[u8], base: Option<&Url>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Authority,
        is_authority_end(input@, old(ps).p as int, old(ps).special),
        !(old(ps).at_sign_seen && old(ps).bs == old(ps).p),
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Host,
        final(ps).p == old(ps).bs,
        final(ps).gm@ == (Machine { buffer: Seq::empty(), state: State::Host, ..old(ps).gm@ }),
        final(ps).href@.len() <= old(ps).href@.len() + 1,
{
    let ghost url = ps.gm@.url;
    if ps.pts && ps.href.len() == ps.username_end + 1 {
        ps.href.pop();
    }
    if ps.username_end > ps.scheme_end + 3 || ps.href.len() > ps.username_end {
        ps.href.push(b'@');
    }
    proof {
        assert(ps.href@ =~= head(url));
    }
    ps.host_start = ps.href.len();
    let bs = ps.bs;
    ps.gm = Ghost(Machine { buffer: Seq::empty(), state: State::Host, ..ps.gm@ });
    ps.state = State::Host;
    ps.p = bs;
    proof {
        assert(input@.subrange(bs as int, bs as int) =~= Seq::<u8>::empty());
    }
}

/// The authority state at an "@": the buffer becomes credentials.
fn authority_at(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Authority,
        old(ps).p < input.len(),
        input@[old(ps).p as int] == b'@',
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Authority,
        final(ps).special == old(ps).special,
        final(ps).p == old(ps).p + 1,
        final(ps).bs == old(ps).p + 1,
        final(cost).n == old(cost).n + (old(ps).p - old(ps).bs),
        final(ps).href@.len() <= old(ps).href@.len() + 3 * (old(ps).p - old(ps).bs) + 9,
        step(input@, base_rec(base), None, old(ps).gm@, old(ps).p as int) == Step::Next(
            final(ps).gm@,
            old(ps).p as int,
        ),
{
    let k = ps.p;
    let ghost u0 = ps.gm@.url.username;
    let ghost pw0 = ps.gm@.url.password;
    let ghost pts0 = ps.pts;
    let ghost buf = ps.gm@.buffer;
    let ghost full = if ps.at_sign_seen {
        seq![b'%', b'4', b'0'] + buf
    } else {
        buf
    };
    let ghost m0 = ps.gm@;
    let ghost special = ps.special;
    if ps.at_sign_seen {
        proof {
            lemma_append_userinfo_concat(seq![b'%', b'4', b'0'], buf, u0, pw0, pts0);
            assert(seq![b'%', b'4', b'0'] =~= seq![b'%'] + seq![b'4', b'0']);
            assert(seq![b'4', b'0'] =~= seq![b'4'] + seq![b'0']);
            assert(seq![b'0'] =~= seq![b'0'] + Seq::<u8>::empty());
            lemma_append_userinfo_cons(b'%', seq![b'4', b'0'], u0, pw0, pts0);
            let (u1, pw1, pts1) = userinfo_step(b'%', u0, pw0, pts0);
            lemma_append_userinfo_cons(b'4', seq![b'0'], u1, pw1, pts1);
            let (u2, pw2, pts2) = userinfo_step(b'4', u1, pw1, pts1);
            lemma_append_userinfo_cons(b'0', Seq::empty(), u2, pw2, pts2);
        }
        userinfo_byte(ps, b'%');
        userinfo_byte(ps, b'4');
        userinfo_byte(ps, b'0');
    }
    let mut i = ps.bs;
    while i < k
        invariant
            ps.bs <= i <= k < input.len(),
            ps.bs == old(ps).bs,
            old(ps).p == k,
            cost.n == old(cost).n + (i - old(ps).bs),
            ps.href@.len() <= old(ps).href@.len() + 9 + 3 * (i - old(ps).bs),
            ps.p == k,
            ps.state == State::Authority,
            ps.special == special,
            ps.at_sign_seen == m0.at_sign_seen,
            ps.inside_brackets == m0.inside_brackets,
            ps.scheme_end == m0.url.scheme.len(),
            ps.href@ == authority_prefix(ps.gm@.url, ps.pts),
            ps.username_end == ps.gm@.url.scheme.len() + 3 + ps.gm@.url.username.len(),
            !ps.pts ==> ps.gm@.url.password.len() == 0,
            ps.pts == ps.gm@.password_token_seen,
            ps.gm@ == (Machine {
                url: UrlRecord {
                    username: ps.gm@.url.username,
                    password: ps.gm@.url.password,
                    ..m0.url
                },
                password_token_seen: ps.gm@.password_token_seen,
                ..m0
            }),
            append_userinfo(full, u0, pw0, pts0) == append_userinfo(
                input@.subrange(i as int, k as int),
                ps.gm@.url.username,
                ps.gm@.url.password,
                ps.pts,
            ),
        decreases k - i,
    {
        let c = input[i];
        proof {
            let rest = input@.subrange(i + 1, k as int);
            assert(input@.subrange(i as int, k as int) =~= seq![c] + rest);
            lemma_append_userinfo_cons(c, rest, ps.gm@.url.username, ps.gm@.url.password, ps.pts);
        }
        proof {
            cost.n = cost.n + 1;
        }
        userinfo_byte(ps, c);
        i = i + 1;
    }
    proof {
        assert(input@.subrange(k as int, k as int) =~= Seq::<u8>::empty());
    }
    ps.at_sign_seen = true;
    ps.gm = Ghost(Machine { at_sign_seen: true, buffer: Seq::empty(), ..ps.gm@ });
    ps.bs = k + 1;
    ps.p = k + 1;
    proof {
        assert(input@.subrange(k + 1, k + 1) =~= Seq::<u8>::empty());
    }
}

/// The authority state collects a run of bytes other than "@" and its
/// end characters into its buffer.
proof fn lemma_run_authority_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::Authority,
        forall|j: int| p <= j < k ==> input[j] != b'@' && !is_authority_end(input, j, is_special(m.url)),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { buffer: m.buffer + input.subrange(p, k), ..m },
            k,
        ),
    decreases k - p,
{
    if p == k {
        assert(m.buffer + input.subrange(p, k) =~= m.buffer);
        assert(m == Machine { buffer: m.buffer, ..m });
    } else {
        let m2 = Machine { buffer: m.buffer.push(input[p]), ..m };
        lemma_step_authority_char(input, b, m, p);
        lemma_run_next(input, b, m, p, m2, p);
        lemma_run_authority_chars(input, b, m2, p + 1, k);
        assert(m2.buffer + input.subrange(p + 1, k) =~= m.buffer + input.subrange(p, k));
    }
}

/// An authority without "@", ":", "[" or "]" whose bytes the domain fast
/// path accepts is a plain host: scan it once, then parse it.
#[verifier::rlimit(60)]
fn authority_fast(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Flow>)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Authority,
    ensures
        r is None ==> *final(ps) == *old(ps),
        r is None ==> final(cost).n <= old(cost).n + (input.len() - old(ps).p) + 1,
        r matches Some(f) ==> handler_ok(old(ps), final(ps), input@, base_rec(base), f, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost c0 = cost.n;
    let p = ps.p;
    if ps.bs != p {
        return None;
    }
    let special = ps.special;
    let stop = if special {
        AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW
    } else {
        AUTHORITY_STOP | HOST_STOP | DOMAIN_SLOW
    };
    proof {
        crate::swar::lemma_plain_free_masks();
    }
    let k = crate::swar::find_cls_plain(input, p, input.len(), stop, Tracked(cost));
    if k == p {
        return None;
    }
    let end = k >= input.len() || input[k] == b'/' || input[k] == b'?' || input[k] == b'#' || (special
        && input[k] == b'\\');
    if !end {
        return None;
    }
    let ghost m0 = ps.gm@;
    proof {
        lemma_cls();
        assert forall|j: int| p <= j < k implies input@[j] != b'@' && !is_authority_end(input@, j, special)
            && host_plain(input@, j, special) && !cls_has(#[trigger] input@[j], DOMAIN_SLOW) by {
            let x = CLS@[input@[j] as int];
            lemma_and_or(x, AUTHORITY_STOP, BACKSLASH);
            lemma_and_or(x, AUTHORITY_STOP | BACKSLASH, HOST_STOP);
            lemma_and_or(x, AUTHORITY_STOP | BACKSLASH | HOST_STOP, DOMAIN_SLOW);
            lemma_and_or(x, AUTHORITY_STOP, HOST_STOP);
            lemma_and_or(x, AUTHORITY_STOP | HOST_STOP, DOMAIN_SLOW);
            assert(!cls_has(input@[j], stop));
            assert(cls_has(input@[j], AUTHORITY_STOP) == cls_pred(AUTHORITY_STOP, input@[j]));
            assert(cls_has(input@[j], BACKSLASH) == cls_pred(BACKSLASH, input@[j]));
            assert(cls_has(input@[j], HOST_STOP) == cls_pred(HOST_STOP, input@[j]));
        }
        lemma_run_authority_chars(input@, b, m0, p as int, k as int);
        assert(m0.buffer + input@.subrange(p as int, k as int) =~= input@.subrange(p as int, k as int));
    }
    ps.gm = Ghost(Machine { buffer: input@.subrange(p as int, k as int), ..m0 });
    ps.p = k;
    let ghost m1 = ps.gm@;
    proof {
        lemma_step_authority_end(input@, b, m1, k as int);
    }
    authority_end(ps, input, base);
    proof {
        lemma_run_next(input@, b, m1, k as int, ps.gm@, p - 1);
    }
    let ghost h2 = ps.href@.len();
    let ghost c2 = cost.n;
    let ghost m2 = ps.gm@;
    proof {
        lemma_run_host_chars(input@, b, m2, p as int, k as int);
        assert(m2.buffer + input@.subrange(p as int, k as int) =~= input@.subrange(p as int, k as int));
    }
    ps.gm = Ghost(Machine { buffer: input@.subrange(p as int, k as int), ..m2 });
    ps.p = k;
    let ghost m3 = ps.gm@;
    proof {
        lemma_step_host(input@, b, m3, k as int);
    }
    if host_end(ps, input, base, sc, false, true, Tracked(cost)) {
        proof {
            lemma_run_next(input@, b, m3, k as int, ps.gm@, k - 1);
            assert(c2 == c0 + (k - p) + 1);
            assert(cost.n <= c2 + 96 * (k - p) + 8);
            assert(ps.href@.len() <= h2 + 8 * (k - p) + 42);
            assert(h2 <= old(ps).href@.len() + 1);
            assert(level(ps.state) <= 6);
            lemma_pot_drop_n(old(ps), ps, input@, b, c0 as int, cost.n as int, 1);
        }
        Some(Flow::Continue)
    } else {
        proof {
            lemma_run_fail(input@, b, m3, k as int);
            assert(cost.n <= c0 + 97 * (k - p) + 9);
            lemma_pot_fail(old(ps), input@, b, c0 as int, cost.n as int, 1);
        }
        Some(Flow::Fail)
    }
}

fn h_authority(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Authority,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    match authority_fast(ps, input, base, sc, Tracked(cost)) {
        Some(f) => {
            return f;
        },
        None => {},
    }
    let special = ps.special;
    let ghost cs = cost.n;
    loop
        invariant
            ps.inv(input@, b),
            cs <= old(cost).n + (input.len() - old(ps).p) + 1,
            old(ps).bs <= old(ps).p <= input.len(),
            cost.n + COST_W * (input.len() - ps.p) + ps.href@.len() + 8 * (ps.p - ps.bs) <= cs + COST_W * (input.len() - old(ps).p) + old(ps).href@.len() + 8 * (old(ps).p - old(ps).bs),
            ps.state == State::Authority,
            ps.special == special,
            target == run(input@, b, None, ps.gm@, ps.p as int),
            target == run(input@, b, None, old(ps).gm@, old(ps).p as int),
            b == base_rec(base),
            old(ps).state == State::Authority,
        decreases input.len() - ps.p,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let k = ps.p;
        let ghost m = ps.gm@;
        if k >= input.len() || input[k] == b'/' || input[k] == b'?' || input[k] == b'#' || (special
            && input[k] == b'\\') {
            proof {
                lemma_step_authority_end(input@, b, m, k as int);
            }
            if ps.at_sign_seen && ps.bs == k {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                    lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 2);
                }
                return Flow::Fail;
            }
            let ghost bs = ps.bs;
            authority_end(ps, input, base);
            proof {
                lemma_run_next(input@, b, m, k as int, ps.gm@, bs - 1);
                lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 2);
            }
            return Flow::Continue;
        }
        if input[k] == b'@' {
            authority_at(ps, input, base, Tracked(cost));
            proof {
                lemma_run_next(input@, b, m, k as int, ps.gm@, k as int);
            }
        } else {
            let stop = if special {
                AUTHORITY_STOP | BACKSLASH
            } else {
                AUTHORITY_STOP
            };
            proof {
                crate::swar::lemma_plain_free_masks();
            }
            let k2 = crate::swar::find_cls_plain(input, k + 1, input.len(), stop, Tracked(cost));
            proof {
                lemma_cls();
                assert forall|j: int| k <= j < k2 implies input@[j] != b'@' && !is_authority_end(
                    input@,
                    j,
                    special,
                ) by {
                    if j > k {
                        lemma_and_or(CLS@[input@[j] as int], AUTHORITY_STOP, BACKSLASH);
                        assert(!cls_has(input@[j], stop));
                        assert(cls_has(input@[j], AUTHORITY_STOP) == cls_pred(AUTHORITY_STOP, input@[j]));
                        assert(cls_has(input@[j], BACKSLASH) == cls_pred(BACKSLASH, input@[j]));
                    }
                }
                lemma_run_authority_chars(input@, b, m, k as int, k2 as int);
                assert(m.buffer + input@.subrange(k as int, k2 as int) =~= input@.subrange(
                    ps.bs as int,
                    k2 as int,
                ));
            }
            ps.gm = Ghost(Machine { buffer: input@.subrange(ps.bs as int, k2 as int), ..ps.gm@ });
            ps.p = k2;
        }
    }
}

proof fn lemma_step_host(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::Host || m.state == State::Hostname,
    ensures
        step(input, b, None, m, p) == step_host(input, b, None, m, p),
{
}

/// The host state's end: parse the buffer as a host and write it.
#[verifier::rlimit(80)]
fn host_end(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, to_port: bool, clean: bool, Tracked(cost): Tracked<&mut Meter>) -> (ok: bool)
    requires
        clean ==> forall|j: int| old(ps).bs <= j < old(ps).p ==> !cls_has(#[trigger] input@[j], DOMAIN_SLOW),
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Host || old(ps).state == State::Hostname,
        to_port ==> old(ps).p < input.len() && !old(ps).inside_brackets,
    ensures
        final(cost).n <= old(cost).n + host_cost((old(ps).p - old(ps).bs) as nat),
        final(ps).href@.len() <= old(ps).href@.len() + host_growth((old(ps).p - old(ps).bs) as nat),
        ({
            let m = old(ps).gm@;
            match host_parse(m.buffer, !is_special(m.url)) {
                None => !ok,
                Some(h) => {
                    let url = UrlRecord { host: Some(h), ..m.url };
                    let st = if to_port { State::Port } else { State::PathStart };
                    &&& ok
                    &&& final(ps).gm@ == (Machine { url, buffer: Seq::empty(), state: st, ..m })
                    &&& final(ps).p == if to_port { old(ps).p + 1 } else { old(ps).p as int }
                    &&& final(ps).inv(input@, base_rec(base))
                }
            }
        }),
{
    let k = ps.p;
    let bs = ps.bs;
    let ghost m = ps.gm@;
    let ghost hs = ps.href@;
    let special = ps.special;
    let hs_in = vstd::slice::slice_subrange(input, bs, k);
    proof {
        if clean {
            assert forall|j: int| 0 <= j < hs_in.len() implies !cls_has(#[trigger] hs_in@[j], DOMAIN_SLOW) by {
                assert(hs_in@[j] == input@[bs + j]);
            }
        }
    }
    match host_parse_exec(hs_in, !special, &mut ps.href, sc, clean, Tracked(cost)) {
        None => false,
        Some((kind, h)) => {
            let ghost url = UrlRecord { host: Some(h@), ..m.url };
            ps.host_end = ps.href.len();
            ps.host_kind = Some(kind);
            ps.port = None;
            ps.opaque_path = false;
            ps.query_start = None;
            ps.fragment_start = None;
            proof {
                lemma_core_parts(url);
                assert(path_serialize(url.path) =~= Seq::<u8>::empty());
                assert(ps.href@ =~= core_serialize(url));
                assert(hs.len() == url.scheme.len() + 3 + credentials_serialize(url).len());
            }
            if to_port {
                ps.gm = Ghost(Machine { url, buffer: Seq::empty(), state: State::Port, ..m });
                ps.state = State::Port;
                ps.bs = k + 1;
                ps.p = k + 1;
                proof {
                    assert(input@.subrange(k + 1, k + 1) =~= Seq::<u8>::empty());
                    assert(all_ascii_digits(Seq::<u8>::empty()));
                }
            } else {
                ps.path_start = ps.href.len();
                ps.gm = Ghost(Machine { url, buffer: Seq::empty(), state: State::PathStart, ..m });
                ps.state = State::PathStart;
            }
            proof {
assert(ps.inv(input@, base_rec(base)));
            }
            true
        },
    }
}

pub open spec fn host_plain(input: Seq<u8>, j: int, special: bool) -> bool {
    &&& input[j] != b':'
    &&& input[j] != b'/'
    &&& input[j] != b'?'
    &&& input[j] != b'#'
    &&& input[j] != b'['
    &&& input[j] != b']'
    &&& !(special && input[j] == b'\\')
}

/// The host state collects a run of plain host bytes into its buffer.
proof fn lemma_run_host_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::Host || m.state == State::Hostname,
        forall|j: int| p <= j < k ==> host_plain(input, j, is_special(m.url)),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { buffer: m.buffer + input.subrange(p, k), ..m },
            k,
        ),
    decreases k - p,
{
    if p == k {
        assert(m.buffer + input.subrange(p, k) =~= m.buffer);
        assert(m == Machine { buffer: m.buffer, ..m });
    } else {
        let m2 = Machine { buffer: m.buffer.push(input[p]), ..m };
        assert(host_plain(input, p, is_special(m.url)));
        lemma_step_host(input, b, m, p);
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_next(input, b, m, p, m2, p);
        lemma_run_host_chars(input, b, m2, p + 1, k);
        assert(m2.buffer + input.subrange(p + 1, k) =~= m.buffer + input.subrange(p, k));
    }
}

#[verifier::rlimit(150)]
fn h_host(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Host || old(ps).state == State::Hostname,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    let special = ps.special;
    let mut clean = ps.p == ps.bs;
    loop
        invariant
            ps.inv(input@, b),
            ps.state == State::Host || ps.state == State::Hostname,
            clean ==> forall|j: int| ps.bs <= j < ps.p ==> !cls_has(#[trigger] input@[j], DOMAIN_SLOW),
            ps.special == special,
            old(ps).p <= ps.p,
            old(ps).bs <= old(ps).p <= input.len(),
            cost.n + COST_W * (input.len() - ps.p) + ps.href@.len() + 104 * (ps.p - ps.bs) <= old(cost).n + COST_W * (input.len() - old(ps).p) + old(ps).href@.len() + 104 * (old(ps).p - old(ps).bs),
            target == run(input@, b, None, ps.gm@, ps.p as int),
            target == run(input@, b, None, old(ps).gm@, old(ps).p as int),
            b == base_rec(base),
            old(ps).state == State::Host || old(ps).state == State::Hostname,
        decreases input.len() - ps.p,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let k = ps.p;
        let ghost m = ps.gm@;
        proof {
            lemma_step_host(input@, b, m, k as int);
        }
        let end = k >= input.len() || input[k] == b'/' || input[k] == b'?' || input[k] == b'#' || (
        special && input[k] == b'\\');
        if !end && input[k] == b':' && !ps.inside_brackets {
            if ps.bs == k {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                    lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Fail;
            }
            if host_end(ps, input, base, sc, true, clean, Tracked(cost)) {
                proof {
                    lemma_run_next(input@, b, m, k as int, ps.gm@, k as int);
                    lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Continue;
            } else {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                    lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Fail;
            }
        }
        if end {
            if special && ps.bs == k {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                    lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Fail;
            }
            if host_end(ps, input, base, sc, false, clean, Tracked(cost)) {
                proof {
                    lemma_run_next(input@, b, m, k as int, ps.gm@, k - 1);
                    lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Continue;
            } else {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                    lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Fail;
            }
        }
        let c = input[k];
        clean = clean && cls(c) & DOMAIN_SLOW == 0;
        if c == b'[' {
            ps.inside_brackets = true;
        } else if c == b']' {
            ps.inside_brackets = false;
        }
        ps.gm = Ghost(
            Machine { inside_brackets: ps.inside_brackets, buffer: ps.gm@.buffer.push(c), ..ps.gm@ },
        );
        ps.p = k + 1;
        proof {
            assert(input@.subrange(ps.bs as int, k + 1) =~= input@.subrange(
                ps.bs as int,
                k as int,
            ).push(c));
            lemma_run_next(input@, b, m, k as int, ps.gm@, k as int);
        }
        let stop = if special {
            HOST_STOP | BACKSLASH
        } else {
            HOST_STOP
        };
        // While the host is clean, also stop at bytes the domain fast path rejects.
        let mask = if clean {
            stop | DOMAIN_SLOW
        } else {
            stop
        };
        proof {
            crate::swar::lemma_plain_free_masks();
        }
        let k2 = crate::swar::find_cls_plain(input, k + 1, input.len(), mask, Tracked(cost));
        proof {
            lemma_cls();
            assert forall|j: int| k + 1 <= j < k2 implies !cls_has(#[trigger] input@[j], stop) && (clean
                ==> !cls_has(input@[j], DOMAIN_SLOW)) by {
                lemma_and_or(CLS@[input@[j] as int], stop, DOMAIN_SLOW);
            }
            assert forall|j: int| k + 1 <= j < k2 implies host_plain(input@, j, special) by {
                lemma_and_or(CLS@[input@[j] as int], HOST_STOP, BACKSLASH);
                assert(!cls_has(input@[j], stop));
                assert(cls_has(input@[j], HOST_STOP) == cls_pred(HOST_STOP, input@[j]));
                assert(cls_has(input@[j], BACKSLASH) == cls_pred(BACKSLASH, input@[j]));
            }
            lemma_run_host_chars(input@, b, ps.gm@, k + 1, k2 as int);
            assert(ps.gm@.buffer + input@.subrange(k + 1, k2 as int) =~= input@.subrange(
                ps.bs as int,
                k2 as int,
            ));
        }
        ps.gm = Ghost(Machine { buffer: input@.subrange(ps.bs as int, k2 as int), ..ps.gm@ });
        ps.p = k2;
    }
}

pub fn default_port_exec(s: &[u8]) -> (r: Option<u16>)
    ensures
        r == default_port(s@),
{
    let n = s.len();
    let ftp = n == 3 && s[0] == b'f' && s[1] == b't' && s[2] == b'p';
    let http = n == 4 && s[0] == b'h' && s[1] == b't' && s[2] == b't' && s[3] == b'p';
    let ws = n == 2 && s[0] == b'w' && s[1] == b's';
    let https = n == 5 && s[0] == b'h' && s[1] == b't' && s[2] == b't' && s[3] == b'p' && s[4]
        == b's';
    let wss = n == 3 && s[0] == b'w' && s[1] == b's' && s[2] == b's';
    proof {
        let v = s@;
        assert(ftp <==> v =~= s_ftp());
        assert(http <==> v =~= s_http());
        assert(ws <==> v =~= s_ws());
        assert(https <==> v =~= s_https());
        assert(wss <==> v =~= s_wss());
    }
    if ftp {
        Some(21)
    } else if http || ws {
        Some(80)
    } else if https || wss {
        Some(443)
    } else {
        None
    }
}

/// `min(radix_value(s, 10), 65536)`.
pub(crate) fn port_value(s: &[u8], Tracked(cost): Tracked<&mut Meter>) -> (r: u32)
    requires
        all_ascii_digits(s@),
    ensures
        r as nat == if radix_value(s@, 10) > 65535 { 65536 } else { radix_value(s@, 10) },
        final(cost).n == old(cost).n + s.len(),
{
    let mut v: u32 = 0;
    let mut i = 0;
    proof {
        assert(s@.take(0) =~= Seq::<u8>::empty());
    }
    while i < s.len()
        invariant
            i <= s.len(),
            all_ascii_digits(s@),
            v as nat == if radix_value(s@.take(i as int), 10) > 65535 {
                65536
            } else {
                radix_value(s@.take(i as int), 10)
            },
            cost.n == old(cost).n + i,
        decreases s.len() - i,
    {
        proof {
            cost.n = cost.n + 1;
            assert(s@.take(i + 1).drop_last() =~= s@.take(i as int));
            assert(s@.take(i + 1).last() == s@[i as int]);
            assert(is_ascii_digit(s@[i as int]));
        }
        let d = (s[i] - b'0') as u32;
        if v < 65536 {
            v = v * 10 + d;
            if v > 65535 {
                v = 65536;
            }
        }
        i = i + 1;
    }
    proof {
        assert(s@.take(s.len() as int) =~= s@);
    }
    v
}

proof fn lemma_step_port(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::Port,
    ensures
        step(input, b, None, m, p) == step_port(input, b, None, m, p),
{
}

/// The port state's end: write the port unless it is the default, and go
/// to the path start state.
fn port_end(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (ok: bool)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Port,
    ensures
        ({
            let m = old(ps).gm@;
            let url = m.url;
            if m.buffer.len() == 0 {
                &&& ok
                &&& final(ps).gm@ == (Machine { state: State::PathStart, ..m })
            } else {
                let port = radix_value(m.buffer, 10);
                if port > 65535 {
                    !ok
                } else {
                    let url2 = UrlRecord {
                        port: if default_port(url.scheme) == Some(port as u16) {
                            None
                        } else {
                            Some(port as u16)
                        },
                        ..url
                    };
                    &&& ok
                    &&& final(ps).gm@ == (Machine {
                        url: url2,
                        buffer: Seq::empty(),
                        state: State::PathStart,
                        ..m
                    })
                }
            }
        }),
        ok ==> final(ps).inv(input@, base_rec(base)),
        ok ==> final(ps).p == old(ps).p,
        final(cost).n <= old(cost).n + (old(ps).p - old(ps).bs),
        final(ps).href@.len() <= old(ps).href@.len() + 6,
{
    let ghost m = ps.gm@;
    let ghost url = m.url;
    if ps.bs == ps.p {
        ps.path_start = ps.href.len();
        ps.port = None;
        ps.opaque_path = false;
        ps.query_start = None;
        ps.fragment_start = None;
        ps.gm = Ghost(Machine { state: State::PathStart, ..m });
        ps.state = State::PathStart;
        proof {
            lemma_core_parts(url);
        }
        return true;
    }
    let v = port_value(vstd::slice::slice_subrange(input, ps.bs, ps.p), Tracked(cost));
    if v > 65535 {
        return false;
    }
    proof {
        lemma_core_parts(url);
        assert(ps.href@.subrange(0, ps.scheme_end as int) == url.scheme);
    }
    let dp = default_port_exec(vstd::slice::slice_subrange(ps.href.as_slice(), 0, ps.scheme_end));
    let ghost url2 = UrlRecord {
        port: if dp == Some(v as u16) {
            None
        } else {
            Some(v as u16)
        },
        ..url
    };
    if dp == Some(v as u16) {
        ps.port = None;
    } else {
        ps.href.push(b':');
        push_decimal(&mut ps.href, v);
        ps.port = Some(v as u16);
    }
    ps.path_start = ps.href.len();
    ps.opaque_path = false;
    ps.query_start = None;
    ps.fragment_start = None;
    ps.gm = Ghost(Machine { url: url2, buffer: Seq::empty(), state: State::PathStart, ..m });
    ps.state = State::PathStart;
    proof {
        lemma_core_parts(url2);
        assert(path_serialize(url2.path) =~= Seq::<u8>::empty());
        assert(ps.href@ =~= core_serialize(url2));
    }
    true
}

fn h_port(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Port,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    let special = ps.special;
    loop
        invariant
            ps.inv(input@, b),
            ps.state == State::Port,
            ps.special == special,
            old(ps).p <= ps.p,
            old(ps).bs <= old(ps).p <= input.len(),
            ps.bs == old(ps).bs,
            cost.n + COST_W * (input.len() - ps.p) + ps.href@.len() + 2 * (ps.p - ps.bs) <= old(cost).n + COST_W * (input.len() - old(ps).p) + old(ps).href@.len() + 2 * (old(ps).p - old(ps).bs),
            target == run(input@, b, None, ps.gm@, ps.p as int),
            target == run(input@, b, None, old(ps).gm@, old(ps).p as int),
            b == base_rec(base),
            old(ps).state == State::Port,
        decreases input.len() - ps.p,
    {
        proof {
            cost.n = cost.n + 1;
        }
        let k = ps.p;
        let ghost m = ps.gm@;
        proof {
            lemma_step_port(input@, b, m, k as int);
        }
        if k < input.len() && b'0' <= input[k] && input[k] <= b'9' {
            ps.gm = Ghost(Machine { buffer: ps.gm@.buffer.push(input@[k as int]), ..ps.gm@ });
            ps.p = k + 1;
            proof {
                assert(input@.subrange(ps.bs as int, k + 1) =~= input@.subrange(
                    ps.bs as int,
                    k as int,
                ).push(input@[k as int]));
                lemma_run_next(input@, b, m, k as int, ps.gm@, k as int);
            }
        } else if k >= input.len() || input[k] == b'/' || input[k] == b'?' || input[k] == b'#' || (
        special && input[k] == b'\\') {
            if port_end(ps, input, base, Tracked(cost)) {
                proof {
                    lemma_run_next(input@, b, m, k as int, ps.gm@, k - 1);
                    lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Continue;
            } else {
                proof {
                    lemma_run_fail(input@, b, m, k as int);
                lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
                }
                return Flow::Fail;
            }
        } else {
            proof {
                lemma_run_fail(input@, b, m, k as int);
                lemma_pot_fail(old(ps), input@, b, old(cost).n as int, cost.n as int, 1);
            }
            return Flow::Fail;
        }
    }
}

/// The URL "file://" plus a host: `Host::Empty`, or the base's host.
pub open spec fn file_prefix_url(url: UrlRecord, host: Option<Host>) -> UrlRecord {
    UrlRecord {
        scheme: s_file(),
        username: Seq::empty(),
        password: Seq::empty(),
        host,
        port: None,
        path: UrlPath::List(Seq::empty()),
        query: None,
        fragment: None,
    }
}

pub(crate) open spec fn base_host(base: Option<&Url>) -> Option<Host> {
    match base {
        None => Some(Host::Empty),
        Some(bu) => bu@.host,
    }
}

/// Writes "file:", and "//" and the host when there is one: the empty host,
/// or the base's host.
#[verifier::rlimit(30)]
fn file_prefix(ps: &mut Parser, hb: Option<&Url>, Tracked(cost): Tracked<&mut Meter>)
    requires
        hb matches Some(bu) ==> bu.wf(),
    ensures
        final(cost).n <= old(cost).n + final(ps).href@.len(),
        final(ps).href@.len() <= 7 + match hb {
            Some(bu) => bu.href@.len(),
            None => 0,
        },
        ({
            let u = file_prefix_url(old(ps).gm@.url, base_host(hb));
            &&& final(ps).href@ == core_serialize(u)
            &&& offsets_ok(final(ps), u)
            &&& tail_offsets_ok(final(ps), u)
        }),
        final(ps).special,
        final(ps).p == old(ps).p,
        final(ps).bs == old(ps).bs,
        final(ps).state == old(ps).state,
        final(ps).gm == old(ps).gm,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).pts == old(ps).pts,
{
    let ghost u = file_prefix_url(ps.gm@.url, base_host(hb));
    ps.href.clear();
    ps.href.push(b'f');
    ps.href.push(b'i');
    ps.href.push(b'l');
    ps.href.push(b'e');
    ps.href.push(b':');
    ps.scheme_end = 4;
    ps.special = true;
    ps.port = None;
    ps.opaque_path = false;
    ps.query_start = None;
    ps.fragment_start = None;
    match hb {
        None => {
            ps.href.push(b'/');
            ps.href.push(b'/');
            ps.username_end = 7;
            ps.host_start = 7;
            ps.host_end = 7;
            ps.path_start = 7;
            ps.host_kind = Some(HostKind::Empty);
        },
        Some(bu) => {
            let ghost b = bu@;
            proof {
                lemma_serialize_parts(b);
            }
            match bu.host_kind {
                None => {
                    ps.username_end = 5;
                    ps.host_start = 5;
                    ps.host_end = 5;
                    ps.path_start = 5;
                    ps.host_kind = None;
                },
                Some(k) => {
                    let ghost h = b.host->0;
                    proof {
                        let hr = bu.href@;
                        let sl = b.scheme.len() as int;
                        let au = authority_serialize(b);
                        let cr = credentials_serialize(b);
                        assert(hr.subrange(sl + 1, o_path_start(b) as int) == au);
                        assert(au =~= seq![b'/', b'/'] + cr + host_serialize(h) + port_serialize(b));
                        assert(hr.subrange(bu.host_start as int, bu.host_end as int) =~= host_serialize(h)) by {
                            assert forall|i: int| 0 <= i < host_serialize(h).len() implies hr.subrange(
                                bu.host_start as int,
                                bu.host_end as int,
                            )[i] == host_serialize(h)[i] by {
                                assert(hr[bu.host_start + i] == au[2 + cr.len() + i]);
                            }
                        }
                    }
                    ps.href.push(b'/');
                    ps.href.push(b'/');
                    append_range(&mut ps.href, bu.href.as_slice(), bu.host_start, bu.host_end, Tracked(cost));
                    ps.username_end = 7;
                    ps.host_start = 7;
                    ps.host_end = ps.href.len();
                    ps.path_start = ps.href.len();
                    ps.host_kind = Some(k);
                },
            }
        },
    }
    proof {
        lemma_core_parts(u);
        assert(ps.href@ =~= core_serialize(u));
    }
}

/// Appends the base's path, and its query if `with_query`.
fn append_base_path(ps: &mut Parser, bu: &Url, with_query: bool, Ghost(u): Ghost<UrlRecord>, Tracked(cost): Tracked<&mut Meter>)
    requires
        bu.wf(),
        old(ps).href@ == core_serialize(u),
        u.path == UrlPath::List(Seq::<Seq<u8>>::empty()),
        u.query is None,
        u.fragment is None,
        offsets_ok(old(ps), u),
        tail_offsets_ok(old(ps), u),
    ensures
        final(cost).n + old(ps).href@.len() == old(cost).n + final(ps).href@.len(),
        final(ps).href@.len() <= old(ps).href@.len() + bu.href@.len(),
        ({
            let u2 = UrlRecord {
                path: bu@.path,
                query: if with_query { bu@.query } else { None },
                ..u
            };
            &&& final(ps).href@ == core_serialize(u2)
            &&& offsets_ok(final(ps), u2)
            &&& tail_offsets_ok(final(ps), u2)
        }),
        final(ps).special == old(ps).special,
        final(ps).p == old(ps).p,
        final(ps).bs == old(ps).bs,
        final(ps).state == old(ps).state,
        final(ps).gm == old(ps).gm,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).pts == old(ps).pts,
        final(ps).scheme_end == old(ps).scheme_end,
{
    let ghost b = bu@;
    let ghost u2 = UrlRecord { path: b.path, query: if with_query { b.query } else { None }, ..u };
    proof {
        lemma_serialize_parts(b);
        lemma_core_parts(u);
        lemma_core_parts(u2);
    }
    let (path_end, query_end) = base_ends(bu);
    let cps = ps.href.len();
    append_range(&mut ps.href, bu.href.as_slice(), bu.path_start, path_end, Tracked(cost));
    ps.opaque_path = bu.opaque_path;
    if with_query {
        match bu.query_start {
            Some(q) => {
                ps.query_start = Some(ps.href.len());
                append_range(&mut ps.href, bu.href.as_slice(), path_end, query_end, Tracked(cost));
            },
            None => {},
        }
    }
    proof {
        assert(ps.href@ =~= core_serialize(u2));
    }
}

proof fn lemma_step_file(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::File,
    ensures
        step(input, b, None, m, p) == step_file(input, b, None, m, p),
{
}

pub fn starts_with_drive_exec(s: &[u8], p: usize) -> (r: bool)
    requires
        p <= s.len(),
    ensures
        r == starts_with_windows_drive_letter(s@.skip(p as int)),
{
    let n = s.len() - p;
    let r = n >= 2 && is_alpha(s[p]) && (s[p + 1] == b':' || s[p + 1] == b'|') && (n == 2 || s[p
        + 2] == b'/' || s[p + 2] == b'\\' || s[p + 2] == b'?' || s[p + 2] == b'#');
    proof {
        let t = s@.skip(p as int);
        if n >= 2 {
            assert(t[0] == s@[p as int]);
            assert(t[1] == s@[p + 1]);
        }
        if n >= 3 {
            assert(t[2] == s@[p + 2]);
        }
    }
    r
}

/// The file state at "/" or "\": go to the file slash state.
fn file_to_slash(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::File,
        old(ps).p < input.len(),
        input@[old(ps).p as int] == b'/' || input@[old(ps).p as int] == b'\\',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    let ghost m = ps.gm@;
    let p = ps.p;
    proof {
        lemma_step_file(input@, base_rec(base), m, p as int);
    }
    let ghost url = UrlRecord { scheme: s_file(), host: Some(Host::Empty), ..m.url };
    ps.gm = Ghost(Machine { state: State::FileSlash, url, ..m });
    ps.state = State::FileSlash;
    ps.special = true;
    ps.p = p + 1;
    proof {
        lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p as int);
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

/// The file state without a file base: "file://" and an empty host, then
/// the path state.
fn file_plain(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::File,
        !(old(ps).p < input.len() && (input@[old(ps).p as int] == b'/' || input@[old(ps).p as int]
            == b'\\')),
        !(base_rec(base) is Some && base_rec(base)->0.scheme == s_file()),
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    let ghost m = ps.gm@;
    let p = ps.p;
    proof {
        lemma_step_file(input@, base_rec(base), m, p as int);
    }
    let ghost url = UrlRecord { scheme: s_file(), host: Some(Host::Empty), ..m.url };
    file_prefix(ps, None, Tracked(cost));
    proof {
        assert(url == file_prefix_url(m.url, Some(Host::Empty))) by {
            assert(m.url.username =~= Seq::<u8>::empty());
            assert(m.url.password =~= Seq::<u8>::empty());
        }
    }
    ps.gm = Ghost(Machine { url, ..m });
    enter_path(ps, input, base);
    proof {
        assert(m.buffer =~= Seq::<u8>::empty());
        lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p - 1);
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

/// The file state with a file base, at "?", "#" or the end of the input.
fn file_base_tail(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::File,
        base == Some(bu),
        bu.wf(),
        bu@.scheme == s_file(),
        old(ps).p == input.len() || input@[old(ps).p as int] == b'?' || input@[old(ps).p as int]
            == b'#',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    let ghost m = ps.gm@;
    let ghost b = bu@;
    let p = ps.p;
    proof {
        lemma_step_file(input@, base_rec(base), m, p as int);
    }
    let ghost u0 = file_prefix_url(m.url, b.host);
    let ghost urlb = UrlRecord {
        host: b.host,
        path: b.path,
        query: b.query,
        ..UrlRecord { scheme: s_file(), host: Some(Host::Empty), ..m.url }
    };
    proof {
        assert(m.url.username =~= Seq::<u8>::empty());
        assert(m.url.password =~= Seq::<u8>::empty());
    }
    file_prefix(ps, base, Tracked(cost));
    let q = p < input.len() && input[p] == b'?';
    append_base_path(ps, bu, !q, Ghost(u0), Tracked(cost));
    let ghost u2 = UrlRecord { path: b.path, query: if !q { b.query } else { None }, ..u0 };
    if q {
        ps.gm = Ghost(Machine { url: u2, state: State::PathStart, ..m });
        ps.state = State::PathStart;
        begin_query(ps, input, base);
        proof {
            lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p as int);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    proof {
        assert(u2 == urlb);
        lemma_core_parts(u2);
    }
    if p == input.len() {
        ps.gm = Ghost(Machine { url: u2, ..m });
        proof {
            lemma_run_eof(input@, base_rec(base), m, Machine { url: u2, ..m });
            assert(done_ok(ps, u2));
        }
        proof { lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1); }
        Flow::Done
    } else {
        let ghost u3 = UrlRecord { fragment: Some(Seq::empty()), ..u2 };
        ps.fragment_start = Some(ps.href.len());
        ps.href.push(b'#');
        ps.gm = Ghost(Machine { url: u3, state: State::Fragment, ..m });
        ps.state = State::Fragment;
        ps.p = p + 1;
        proof {
            lemma_core_parts(u3);
            assert(ps.href@ =~= core_serialize(u3));
            lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p as int);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    }
}

/// The file state with a file base, at a path byte: the base's path,
/// shortened unless the input starts with a drive letter.
fn file_base_path(ps: &mut Parser, input: &[u8], base: Option<&Url>, bu: &Url, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::File,
        base == Some(bu),
        bu.wf(),
        bu@.scheme == s_file(),
        old(ps).p < input.len(),
        input@[old(ps).p as int] != b'?',
        input@[old(ps).p as int] != b'#',
        input@[old(ps).p as int] != b'/',
        input@[old(ps).p as int] != b'\\',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    let ghost m = ps.gm@;
    let ghost b = bu@;
    let p = ps.p;
    proof {
        lemma_step_file(input@, base_rec(base), m, p as int);
        assert(m.url.username =~= Seq::<u8>::empty());
        assert(m.url.password =~= Seq::<u8>::empty());
        assert(m.buffer =~= Seq::<u8>::empty());
    }
    let ghost u0 = file_prefix_url(m.url, b.host);
    let drive = starts_with_drive_exec(input, p);
    file_prefix(ps, base, Tracked(cost));
    if drive {
        ps.gm = Ghost(Machine { url: u0, ..m });
    } else {
        append_base_path(ps, bu, false, Ghost(u0), Tracked(cost));
        let ghost u1 = UrlRecord { path: b.path, ..u0 };
        shorten_exec(&mut ps.href, ps.scheme_end, ps.path_start, Ghost(u1), Tracked(cost));
        ps.gm = Ghost(Machine { url: shorten_path(u1), ..m });
    }
    enter_path(ps, input, base);
    proof {
        lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p - 1);
    }
    proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
    Flow::Continue
}

fn h_file(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::File,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let p = ps.p;
    if p < input.len() && (input[p] == b'/' || input[p] == b'\\') {
        return file_to_slash(ps, input, base, Tracked(cost));
    }
    match base {
        Some(bu) => {
            if is_file_exec(url_scheme(bu)) {
                if p == input.len() || input[p] == b'?' || input[p] == b'#' {
                    file_base_tail(ps, input, base, bu, Tracked(cost))
                } else {
                    file_base_path(ps, input, base, bu, Tracked(cost))
                }
            } else {
                file_plain(ps, input, base, Tracked(cost))
            }
        },
        None => file_plain(ps, input, base, Tracked(cost)),
    }
}

proof fn lemma_segments_first(segs: Seq<Seq<u8>>)
    requires
        segs.len() > 0,
    ensures
        ({
            let s = segments_serialize(segs);
            let n = segs[0].len() as int;
            &&& s.len() >= 1 + n
            &&& s[0] == b'/'
            &&& s.subrange(1, 1 + n) == segs[0]
            &&& segs.len() == 1 ==> s.len() == 1 + n
            &&& segs.len() > 1 ==> s.len() > 1 + n && s[1 + n] == b'/'
        }),
    decreases segs.len(),
{
    let s = segments_serialize(segs);
    let a = segments_serialize(segs.drop_last());
    assert(s =~= a + seq![b'/'] + segs.last());
    if segs.len() == 1 {
        assert(a =~= Seq::<u8>::empty());
        assert(s.subrange(1, 1 + segs[0].len() as int) =~= segs[0]);
    } else {
        lemma_segments_first(segs.drop_last());
        assert(segs.drop_last()[0] == segs[0]);
        lemma_segments_len(segs.drop_last());
        assert(s.subrange(1, 1 + segs[0].len() as int) =~= a.subrange(1, 1 + segs[0].len() as int));
        if segs.len() == 2 {
            assert(a.len() == 1 + segs[0].len() as int);
            assert(s[1 + segs[0].len() as int] == b'/');
        } else {
            assert(s[1 + segs[0].len() as int] == a[1 + segs[0].len() as int]);
        }
    }
}

proof fn lemma_segments_first_drive(segs: Seq<Seq<u8>>)
    requires
        segments_ok(segs),
    ensures
        (segs.len() > 0 && is_normalized_windows_drive_letter(segs[0])) <==> ({
            let s = segments_serialize(segs);
            s.len() >= 3 && s[0] == b'/' && is_ascii_alpha(s[1]) && s[2] == b':' && (s.len() == 3
                || s[3] == b'/')
        }),
{
    let s = segments_serialize(segs);
    if segs.len() > 0 {
        lemma_segments_first(segs);
        let n = segs[0].len() as int;
        let t = s.subrange(1, 1 + n);
        if n >= 1 {
            assert(s[1] == t[0]);
        }
        if n >= 2 {
            assert(s[2] == t[1]);
        }
        if n >= 3 {
            assert(s[3] == t[2]);
            assert(segs[0][2] != b'/');
        }
    } else {
        assert(s.len() == 0);
    }
}

proof fn lemma_step_file_slash(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::FileSlash,
    ensures
        step(input, b, None, m, p) == step_file_slash(input, b, None, m, p),
{
}

/// The base's path starts with a normalized Windows drive letter segment.
fn base_drive(bu: &Url) -> (r: bool)
    requires
        bu.wf(),
        bu@.path is List,
    ensures
        r == (bu@.path->List_0.len() > 0 && is_normalized_windows_drive_letter(
            bu@.path->List_0[0],
        )),
{
    let ghost b = bu@;
    let (path_end, _) = base_ends(bu);
    proof {
        lemma_serialize_parts(b);
        lemma_segments_first_drive(b.path->List_0);
    }
    let a = bu.path_start;
    let h = bu.href.as_slice();
    let n = path_end - a;
    let ghost s = bu.href@.subrange(a as int, path_end as int);
    proof {
        if n >= 1 {
            assert(s[0] == bu.href@[a as int]);
        }
        if n >= 2 {
            assert(s[1] == bu.href@[a + 1]);
        }
        if n >= 3 {
            assert(s[2] == bu.href@[a + 2]);
        }
        if n >= 4 {
            assert(s[3] == bu.href@[a + 3]);
        }
    }
    n >= 3 && h[a] == b'/' && is_alpha(h[a + 1]) && h[a + 2] == b':' && (n == 3 || h[a + 3] == b'/')
}

#[verifier::rlimit(100)]
fn h_file_slash(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::FileSlash,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let p = ps.p;
    proof {
        lemma_step_file_slash(input@, base_rec(base), m, p as int);
        assert(m.buffer =~= Seq::<u8>::empty());
        assert(url.username =~= Seq::<u8>::empty());
        assert(url.password =~= Seq::<u8>::empty());
        assert(url == file_prefix_url(url, Some(Host::Empty)));
    }
    if p < input.len() && (input[p] == b'/' || input[p] == b'\\') {
        file_prefix(ps, None, Tracked(cost));
        ps.gm = Ghost(Machine { state: State::FileHost, ..m });
        ps.state = State::FileHost;
        ps.bs = p + 1;
        ps.p = p + 1;
        proof {
            assert(input@.subrange(p + 1, p + 1) =~= Seq::<u8>::empty());
            lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p as int);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    let fb = match base {
        Some(bu) => is_file_exec(url_scheme(bu)),
        None => false,
    };
    if fb {
        let bu = base.unwrap();
        let ghost b = bu@;
        let ghost u0 = file_prefix_url(url, b.host);
        file_prefix(ps, base, Tracked(cost));
        let drive = starts_with_drive_exec(input, p);
        if !drive && base_drive(bu) {
            proof {
                lemma_serialize_parts(b);
                lemma_segments_first(b.path->List_0);
            }
            let a = bu.path_start;
            let ghost seg = b.path->List_0[0];
            proof {
                assert(bu.href@.subrange(a + 1, a + 3) =~= seg) by {
                    let s = bu.href@.subrange(a as int, (o_query_start(b) + dot_len(b)) as int);
                    assert(s.subrange(1, 3) =~= seg);
                    assert(bu.href@[a + 1] == s[1]);
                    assert(bu.href@[a + 2] == s[2]);
                }
            }
            append_range(&mut ps.href, bu.href.as_slice(), a, a + 3, Tracked(cost));
            let ghost u1 = push_segment(u0, seg);
            proof {
                lemma_core_parts(u0);
                lemma_core_parts(u1);
                lemma_segments_push(Seq::empty(), seg);
                assert(Seq::<Seq<u8>>::empty().push(seg).drop_last() =~= Seq::<Seq<u8>>::empty());
                assert(no_byte(seg, b'/'));
                lemma_segments_ok_push(Seq::empty(), seg);
                assert(ps.href@ =~= core_serialize(u1));
            }
            ps.gm = Ghost(Machine { url: u1, ..m });
        } else {
            ps.gm = Ghost(Machine { url: u0, ..m });
        }
        enter_path(ps, input, base);
        proof {
            lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    } else {
        file_prefix(ps, None, Tracked(cost));
        enter_path(ps, input, base);
        proof {
            lemma_run_next(input@, base_rec(base), m, p as int, ps.gm@, p - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    }
}

proof fn lemma_step_file_host(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::FileHost,
    ensures
        step(input, b, None, m, p) == step_file_host(input, b, None, m, p),
{
}

pub open spec fn file_host_end(input: Seq<u8>, j: int) -> bool {
    input[j] == b'/' || input[j] == b'\\' || input[j] == b'?' || input[j] == b'#'
}

/// The file host state collects a run of host bytes into its buffer.
proof fn lemma_run_file_host_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::FileHost,
        forall|j: int| p <= j < k ==> !file_host_end(input, j),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { buffer: m.buffer + input.subrange(p, k), ..m },
            k,
        ),
    decreases k - p,
{
    if p == k {
        assert(m.buffer + input.subrange(p, k) =~= m.buffer);
        assert(m == Machine { buffer: m.buffer, ..m });
    } else {
        let m2 = Machine { buffer: m.buffer.push(input[p]), ..m };
        assert(!file_host_end(input, p));
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_file_host_chars(input, b, m2, p + 1, k);
        assert(m2.buffer + input.subrange(p + 1, k) =~= m.buffer + input.subrange(p, k));
    }
}

/// Sets the offsets of "file://" plus a host ending at `href`'s end.
fn set_file_offsets(ps: &mut Parser, host_start: usize, kind: HostKind)
    ensures
        final(ps).username_end == host_start,
        final(ps).host_start == host_start,
        final(ps).host_end == old(ps).href.len(),
        final(ps).path_start == old(ps).href.len(),
        final(ps).port is None,
        final(ps).host_kind == Some(kind),
        !final(ps).opaque_path,
        final(ps).query_start is None,
        final(ps).fragment_start is None,
        final(ps).href == old(ps).href,
        final(ps).p == old(ps).p,
        final(ps).bs == old(ps).bs,
        final(ps).state == old(ps).state,
        final(ps).gm == old(ps).gm,
        final(ps).special == old(ps).special,
        final(ps).scheme_end == 4,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).pts == old(ps).pts,
{
    let n = ps.href.len();
    ps.scheme_end = 4;
    ps.username_end = host_start;
    ps.host_start = host_start;
    ps.host_end = n;
    ps.path_start = n;
    ps.port = None;
    ps.host_kind = Some(kind);
    ps.opaque_path = false;
    ps.query_start = None;
    ps.fragment_start = None;
}

pub(crate) fn is_localhost(s: &[u8], a: usize) -> (r: bool)
    requires
        a <= s.len(),
    ensures
        r == (s@.subrange(a as int, s.len() as int) == s_localhost()),
{
    let r = s.len() - a == 9 && s[a] == b'l' && s[a + 1] == b'o' && s[a + 2] == b'c' && s[a + 3]
        == b'a' && s[a + 4] == b'l' && s[a + 5] == b'h' && s[a + 6] == b'o' && s[a + 7] == b's'
        && s[a + 8] == b't';
    proof {
        let t = s@.subrange(a as int, s.len() as int);
        if r {
            assert(t =~= s_localhost());
        }
        if t == s_localhost() {
            assert(t.len() == 9);
            assert(t[0] == s@[a as int]);
            assert(t[1] == s@[a + 1]);
            assert(t[2] == s@[a + 2]);
            assert(t[3] == s@[a + 3]);
            assert(t[4] == s@[a + 4]);
            assert(t[5] == s@[a + 5]);
            assert(t[6] == s@[a + 6]);
            assert(t[7] == s@[a + 7]);
            assert(t[8] == s@[a + 8]);
        }
    }
    r
}

/// The file host state at a drive letter: the buffer becomes the first
/// path segment.
fn file_host_drive(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::FileHost,
        is_windows_drive_letter(old(ps).gm@.buffer),
    ensures
        final(cost).n == old(cost).n + (old(ps).p - old(ps).bs),
        final(ps).href@.len() == old(ps).href@.len() + 1 + (old(ps).p - old(ps).bs),
        final(ps).inv(input@, base_rec(base)),
        final(ps).gm@ == (Machine { state: State::Path, ..old(ps).gm@ }),
        final(ps).p == old(ps).p,
{
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let n = ps.href.len();
    set_file_offsets(ps, n, HostKind::Empty);
    ps.href.push(b'/');
    append_range(&mut ps.href, input, ps.bs, ps.p, Tracked(cost));
    ps.bs = n + 1;
    ps.gm = Ghost(Machine { state: State::Path, ..m });
    ps.state = State::Path;
    proof {
        lemma_core_parts(url);
        assert(ps.href@ =~= core_serialize(url) + seq![b'/'] + m.buffer);
        assert(no_byte(m.buffer, b'/'));
    }
}

/// The file host state at the end of a non-drive-letter host.
fn file_host_end_host(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (ok: bool)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::FileHost,
    ensures
        final(cost).n <= old(cost).n + host_cost((old(ps).p - old(ps).bs) as nat),
        final(ps).href@.len() <= old(ps).href@.len() + host_growth((old(ps).p - old(ps).bs) as nat),
        ({
            let m = old(ps).gm@;
            let r = if m.buffer.len() == 0 {
                Some(Host::Empty)
            } else {
                match host_parse(m.buffer, false) {
                    None => None,
                    Some(h) => Some(if h == Host::Domain(s_localhost()) { Host::Empty } else { h }),
                }
            };
            match r {
                None => !ok,
                Some(h) => ok && final(ps).gm@ == (Machine {
                    url: UrlRecord { host: Some(h), ..m.url },
                    buffer: Seq::empty(),
                    state: State::PathStart,
                    ..m
                }) && final(ps).inv(input@, base_rec(base)) && final(ps).p == old(ps).p,
            }
        }),
{
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let n = ps.href.len();
    proof {
        lemma_core_parts(url);
    }
    let ghost h2: Host;
    if ps.bs == ps.p {
        proof {
            h2 = Host::Empty;
        }
        set_file_offsets(ps, n, HostKind::Empty);
    } else {
        match host_parse_exec(vstd::slice::slice_subrange(input, ps.bs, ps.p), false, &mut ps.href, sc, false, Tracked(cost)) {
            None => {
                return false;
            },
            Some((kind, h)) => {
                proof {
                    assert(ps.href@.subrange(n as int, ps.href@.len() as int) =~= host_serialize(h@));
                }
                let lh = is_localhost(ps.href.as_slice(), n);
                let is_domain = match kind {
                    HostKind::Domain => true,
                    _ => false,
                };
                let local = is_domain && lh;
                if local {
                    ps.href.truncate(n);
                    proof {
                        assert(h@ == Host::Domain(s_localhost()));
                        h2 = Host::Empty;
                    }
                    set_file_offsets(ps, n, HostKind::Empty);
                } else {
                    proof {
                        if kind == HostKind::Domain {
                            assert(ps.href@.subrange(n as int, ps.href@.len() as int) != s_localhost());
                            assert(h@ != Host::Domain(s_localhost()));
                        }
                        h2 = h@;
                        assert(ps.href@.subrange(n as int, ps.href@.len() as int) =~= host_serialize(h@));
                    }
                    set_file_offsets(ps, n, kind);
                }
            },
        }
    }
    let ghost url2 = UrlRecord { host: Some(h2), ..url };
    ps.gm = Ghost(Machine { url: url2, buffer: Seq::empty(), state: State::PathStart, ..m });
    ps.state = State::PathStart;
    proof {
        lemma_core_parts(url2);
        assert(ps.href@ =~= core_serialize(url2));
        assert(m.buffer.len() == 0 ==> h2 == Host::Empty);
        assert(m.buffer.len() > 0 ==> host_parse(m.buffer, false) is Some);
        assert(offsets_ok(ps, url2));
        assert(tail_offsets_ok(ps, url2));
        assert(ps.inv(input@, base_rec(base)));
    }
    true
}

#[verifier::rlimit(60)]
fn h_file_host(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::FileHost,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost m = ps.gm@;
    let p = ps.p;
    let mut k = p;
    while k < input.len() && input[k] != b'/' && input[k] != b'\\' && input[k] != b'?' && input[k]
        != b'#'
        invariant
            p <= k <= input.len(),
            forall|j: int| p <= j < k ==> !file_host_end(input@, j),
        decreases input.len() - k,
    {
        k = k + 1;
    }
    proof {
        lemma_run_file_host_chars(input@, b, m, p as int, k as int);
    }
    ps.gm = Ghost(Machine { buffer: m.buffer + input@.subrange(p as int, k as int), ..m });
    ps.p = k;
    proof {
        assert(ps.gm@.buffer =~= input@.subrange(ps.bs as int, k as int));
    }
    let ghost m1 = ps.gm@;
    proof {
        lemma_step_file_host(input@, b, m1, k as int);
    }
    let bs = ps.bs;
    let drive = k - bs == 2 && is_alpha(input[bs]) && (input[bs + 1] == b':' || input[bs + 1]
        == b'|');
    proof {
        if k - bs == 2 {
            assert(m1.buffer[0] == input@[bs as int]);
            assert(m1.buffer[1] == input@[bs + 1]);
        }
        assert(drive == is_windows_drive_letter(m1.buffer));
    }
    if drive {
        file_host_drive(ps, input, base, Tracked(cost));
        proof {
            assert(k == input.len() || file_host_end(input@, k as int));
            assert(step(input@, b, None, m1, k as int) == Step::Next(ps.gm@, k - 1));
            lemma_run_next(input@, b, m1, k as int, ps.gm@, k - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    if file_host_end_host(ps, input, base, sc, Tracked(cost)) {
        proof {
            assert(m1.buffer.len() == 0 ==> m1.buffer =~= Seq::<u8>::empty());
            lemma_run_next(input@, b, m1, k as int, ps.gm@, k - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Continue
    } else {
        proof {
            lemma_run_fail(input@, b, m1, k as int);
        }
        proof { lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        Flow::Fail
    }
}

proof fn lemma_step_path_start(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p <= input.len(),
        m.state == State::PathStart,
    ensures
        step(input, b, None, m, p) == step_path_start(input, b, None, m, p),
{
}

/// Enters the query state from a state whose `href` is the core
/// serialization, at a "?".
fn begin_query(ps: &mut Parser, input: &[u8], base: Option<&Url>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::PathStart || old(ps).state == State::OpaquePath,
        old(ps).p < input.len(),
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Query,
        final(ps).p == old(ps).p + 1,
        final(ps).gm@ == (Machine {
            url: UrlRecord { query: Some(Seq::empty()), ..old(ps).gm@.url },
            state: State::Query,
            ..old(ps).gm@
        }),
        final(ps).href@.len() == old(ps).href@.len() + 1,
{
    let ghost m = ps.gm@;
    let ghost url2 = UrlRecord { query: Some(Seq::empty()), ..m.url };
    ps.query_start = Some(ps.href.len());
    ps.href.push(b'?');
    ps.gm = Ghost(Machine { url: url2, state: State::Query, ..m });
    ps.state = State::Query;
    ps.p = ps.p + 1;
    proof {
        lemma_core_parts(m.url);
        lemma_core_parts(url2);
        assert(ps.href@ =~= core_serialize(url2) + pe_seq(m.buffer, query_set(ps.special)));
    }
}

/// Enters the fragment state from a state whose `href` is the core
/// serialization, at a "#".
fn begin_fragment(ps: &mut Parser, input: &[u8], base: Option<&Url>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::PathStart || old(ps).state == State::OpaquePath,
        old(ps).p < input.len(),
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Fragment,
        final(ps).p == old(ps).p + 1,
        final(ps).gm@ == (Machine {
            url: UrlRecord { fragment: Some(Seq::empty()), ..old(ps).gm@.url },
            state: State::Fragment,
            ..old(ps).gm@
        }),
        final(ps).href@.len() == old(ps).href@.len() + 1,
{
    let ghost m = ps.gm@;
    let ghost url2 = UrlRecord { fragment: Some(Seq::empty()), ..m.url };
    ps.fragment_start = Some(ps.href.len());
    ps.href.push(b'#');
    ps.gm = Ghost(Machine { url: url2, state: State::Fragment, ..m });
    ps.state = State::Fragment;
    ps.p = ps.p + 1;
    proof {
        lemma_core_parts(m.url);
        lemma_core_parts(url2);
        assert(ps.href@ =~= core_serialize(url2));
    }
}

#[verifier::rlimit(60)]
fn h_path_start(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::PathStart,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let p = ps.p;
    let ghost m = ps.gm@;
    proof {
        lemma_step_path_start(input@, b, m, p as int);
        assert(m.buffer =~= Seq::<u8>::empty());
    }
    if ps.special {
        if p < input.len() && (input[p] == b'/' || input[p] == b'\\') {
            ps.p = p + 1;
        }
        enter_path(ps, input, base);
        proof {
            lemma_run_next(input@, b, m, p as int, ps.gm@, ps.p - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    if p < input.len() && input[p] == b'?' {
        begin_query(ps, input, base);
        proof {
            lemma_run_next(input@, b, m, p as int, ps.gm@, p as int);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    if p < input.len() && input[p] == b'#' {
        begin_fragment(ps, input, base);
        proof {
            lemma_run_next(input@, b, m, p as int, ps.gm@, p as int);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    if p < input.len() {
        if input[p] == b'/' {
            ps.p = p + 1;
        }
        enter_path(ps, input, base);
        proof {
            lemma_run_next(input@, b, m, p as int, ps.gm@, ps.p - 1);
        }
        proof { lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1); }
        return Flow::Continue;
    }
    proof {
        reveal(run);
    }
    proof { lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1); }
    Flow::Done
}

pub open spec fn pct2e(s: Seq<u8>, i: int) -> bool {
    s[i] == b'%' && s[i + 1] == b'2' && (s[i + 2] == b'e' || s[i + 2] == b'E')
}

fn is_pct2e(s: &[u8], i: usize) -> (r: bool)
    requires
        i + 3 <= s.len(),
    ensures
        r == pct2e(s@, i as int),
{
    s[i] == b'%' && s[i + 1] == b'2' && (s[i + 2] == b'e' || s[i + 2] == b'E')
}

proof fn lemma_lower_seq(s: Seq<u8>)
    ensures
        ascii_lowercase_seq(s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] ascii_lowercase_seq(s)[i] == ascii_lowercase(s[i]),
{
}

proof fn lemma_lower_at(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        ascii_lowercase_seq(s)[i] == ascii_lowercase(s[i]),
        ascii_lowercase_seq(s).len() == s.len(),
{
}

pub fn is_single_dot_exec(s: &[u8]) -> (r: bool)
    ensures
        r == is_single_dot_segment(s@),
{
    let n = s.len();
    let r = (n == 1 && s[0] == b'.') || (n == 3 && is_pct2e(s, 0));
    proof {
        let v = s@;
        let l = ascii_lowercase_seq(v);
        lemma_lower_seq(v);
        if n == 1 && v[0] == b'.' {
            assert(v =~= seq![b'.']);
        }
        if n == 3 {
            lemma_lower_at(v, 0);
            lemma_lower_at(v, 1);
            lemma_lower_at(v, 2);
            if pct2e(v, 0) {
                assert(l =~= seq![b'%', b'2', b'e']);
            }
        }
        if v == seq![b'.'] {
            assert(n == 1 && v[0] == b'.');
        }
        if l == seq![b'%', b'2', b'e'] {
            assert(n == 3);
            assert(l[0] == b'%' && l[1] == b'2' && l[2] == b'e');
        }
    }
    r
}

pub fn is_double_dot_exec(s: &[u8]) -> (r: bool)
    ensures
        r == is_double_dot_segment(s@),
{
    let n = s.len();
    let a = n == 2 && s[0] == b'.' && s[1] == b'.';
    let b = n == 4 && s[0] == b'.' && is_pct2e(s, 1);
    let c = n == 4 && is_pct2e(s, 0) && s[3] == b'.';
    let d = n == 6 && is_pct2e(s, 0) && is_pct2e(s, 3);
    proof {
        let v = s@;
        let l = ascii_lowercase_seq(v);
        lemma_lower_seq(v);
        if n == 2 {
            assert(a <==> v =~= seq![b'.', b'.']);
        } else {
            assert(v != seq![b'.', b'.']);
        }
        if n == 4 {
            lemma_lower_at(v, 0);
            lemma_lower_at(v, 1);
            lemma_lower_at(v, 2);
            lemma_lower_at(v, 3);
            assert(b <==> l =~= seq![b'.', b'%', b'2', b'e']);
            assert(c <==> l =~= seq![b'%', b'2', b'e', b'.']);
        } else {
            assert(l != seq![b'.', b'%', b'2', b'e']);
            assert(l != seq![b'%', b'2', b'e', b'.']);
        }
        if n == 6 {
            lemma_lower_at(v, 0);
            lemma_lower_at(v, 1);
            lemma_lower_at(v, 2);
            lemma_lower_at(v, 3);
            lemma_lower_at(v, 4);
            lemma_lower_at(v, 5);
            assert(d <==> l =~= seq![b'%', b'2', b'e', b'%', b'2', b'e']);
        } else {
            assert(l != seq![b'%', b'2', b'e', b'%', b'2', b'e']);
        }
    }
    a || b || c || d
}

/// A byte that ends a path segment.
pub open spec fn path_end_byte(input: Seq<u8>, j: int, special: bool) -> bool {
    input[j] == b'/' || input[j] == b'?' || input[j] == b'#' || (special && input[j] == b'\\')
}

/// The URL after the path state finishes a segment, as `step_path` computes it.
pub open spec fn path_seg_url(url: UrlRecord, buffer: Seq<u8>, slash: bool) -> UrlRecord {
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
        let buffer = if url.scheme == s_file() && path_is_empty_list(url) && is_windows_drive_letter(
            buffer,
        ) {
            buffer.update(1, b':')
        } else {
            buffer
        };
        push_segment(url, buffer)
    } else {
        url
    }
}

/// The path state collects a run of segment bytes into its buffer.
proof fn lemma_run_path_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::Path,
        forall|j: int| p <= j < k ==> !path_end_byte(input, j, is_special(m.url)),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { buffer: m.buffer + pe_seq(input.subrange(p, k), EncodeSet::Path), ..m },
            k,
        ),
    decreases k - p,
{
    if p == k {
        assert(input.subrange(p, k) =~= Seq::<u8>::empty());
        assert(pe_seq(input.subrange(p, k), EncodeSet::Path) =~= Seq::<u8>::empty());
        assert(m.buffer + Seq::<u8>::empty() =~= m.buffer);
        assert(m == Machine { buffer: m.buffer, ..m });
    } else {
        let c = input[p];
        let m2 = Machine { buffer: m.buffer + pe(c, EncodeSet::Path), ..m };
        assert(!path_end_byte(input, p, is_special(m.url)));
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_path_chars(input, b, m2, p + 1, k);
        let tail = input.subrange(p + 1, k);
        assert(input.subrange(p, k) =~= seq![c] + tail);
        lemma_pe_seq_cons(c, tail, EncodeSet::Path);
        assert(m2.buffer + pe_seq(tail, EncodeSet::Path) =~= m.buffer + pe_seq(
            input.subrange(p, k),
            EncodeSet::Path,
        ));
    }
}

/// The path state at the end of a segment.
proof fn lemma_run_path_end(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, k: int)
    requires
        0 <= k <= input.len(),
        m.state == State::Path,
        k == input.len() || path_end_byte(input, k, is_special(m.url)),
    ensures
        ({
            let slash = k < input.len() && (input[k] == b'/' || (is_special(m.url) && input[k]
                == b'\\'));
            let url = path_seg_url(m.url, m.buffer, slash);
            let m2 = Machine { url, buffer: Seq::empty(), ..m };
            if k == input.len() {
                run(input, b, None, m, k) == Some(url)
            } else if input[k] == b'?' {
                run(input, b, None, m, k) == run(
                    input,
                    b,
                    None,
                    Machine { state: State::Query, url: UrlRecord { query: Some(Seq::empty()), ..url }, ..m2 },
                    k + 1,
                )
            } else if input[k] == b'#' {
                run(input, b, None, m, k) == run(
                    input,
                    b,
                    None,
                    Machine {
                        state: State::Fragment,
                        url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                        ..m2
                    },
                    k + 1,
                )
            } else {
                run(input, b, None, m, k) == run(input, b, None, m2, k + 1)
            }
        }),
{
}

pub(crate) proof fn lemma_pe_seq_no_slash(s: Seq<u8>, set: EncodeSet)
    requires
        no_byte(s, b'/'),
    ensures
        no_byte(pe_seq(s, set), b'/'),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_pe_seq_no_slash(s.drop_last(), set);
        let c = s.last();
        assert(c == s[s.len() - 1]);
        let e = pe(c, set);
        assert(no_byte(e, b'/')) by {
            if in_encode_set(set, c) {
                assert(e == seq![b'%', upper_hex_digit((c / 16) as nat), upper_hex_digit((c % 16) as nat)]);
            }
        }
        assert forall|i: int| 0 <= i < pe_seq(s, set).len() implies pe_seq(s, set)[i] != b'/' by {
            let a = pe_seq(s.drop_last(), set);
            assert(pe_seq(s, set) == a + e);
            if i >= a.len() {
                assert(pe_seq(s, set)[i] == e[i - a.len()]);
            }
        }
    }
}

/// The whole-path fast run accepts byte `j` (the run starts at `p0` with an
/// empty segment): "/", or a byte that needs no encoding, is not "\\", and
/// is not a "." or "%" that starts a segment (so no segment is a dot
/// segment).
pub open spec fn fast_at(input: Seq<u8>, j: int, p0: int) -> bool {
    let c = input[j];
    c == b'/' || (!in_path_set(c) && c != b'\\' && !((c == b'.' || c == b'%') && (j == p0 || input[j
        - 1] == b'/')))
}

/// The URL after the path state reads `s` with segment buffer `cur`, when
/// no segment is a dot segment or a drive letter needing a fix.
pub open spec fn segs_acc(url: UrlRecord, cur: Seq<u8>, s: Seq<u8>) -> UrlRecord
    decreases s.len(),
{
    if s.len() == 0 {
        url
    } else if s[0] == b'/' {
        segs_acc(push_segment(url, cur), Seq::empty(), s.skip(1))
    } else {
        segs_acc(url, cur.push(s[0]), s.skip(1))
    }
}

/// The segment buffer after the path state reads `s`.
pub open spec fn tail_acc(cur: Seq<u8>, s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        cur
    } else if s[0] == b'/' {
        tail_acc(Seq::empty(), s.skip(1))
    } else {
        tail_acc(cur.push(s[0]), s.skip(1))
    }
}

proof fn lemma_tail_acc_slash(cur: Seq<u8>, s: Seq<u8>)
    requires
        s.len() > 0,
        s[s.len() - 1] == b'/',
    ensures
        tail_acc(cur, s) == Seq::<u8>::empty(),
    decreases s.len(),
{
    if s.len() > 1 {
        let t = s.skip(1);
        assert(t[t.len() - 1] == s[s.len() - 1]);
        if s[0] == b'/' {
            lemma_tail_acc_slash(Seq::empty(), t);
        } else {
            lemma_tail_acc_slash(cur.push(s[0]), t);
        }
    } else {
        assert(s[0] == b'/');
        assert(s.skip(1) =~= Seq::<u8>::empty());
        assert(tail_acc(Seq::<u8>::empty(), s.skip(1)) == Seq::<u8>::empty());
    }
}

/// A segment that does not start with "." or "%" is not a dot segment.
proof fn lemma_not_dot(buf: Seq<u8>)
    requires
        buf.len() > 0 ==> buf[0] != b'.' && buf[0] != b'%',
    ensures
        !is_single_dot_segment(buf),
        !is_double_dot_segment(buf),
{
    lemma_lower_seq(buf);
    if buf.len() > 0 {
        lemma_lower_at(buf, 0);
    }
}

/// Reading `s` pushes plain segments: the serialization grows by `s`.
proof fn lemma_segs_acc(url: UrlRecord, cur: Seq<u8>, s: Seq<u8>)
    requires
        url.path is List,
        path_ok(url.path),
        no_byte(cur, b'/'),
    ensures
        segs_acc(url, cur, s).path is List,
        path_ok(segs_acc(url, cur, s).path),
        no_byte(tail_acc(cur, s), b'/'),
        segments_serialize(segs_acc(url, cur, s).path->List_0) + seq![b'/'] + tail_acc(cur, s)
            == segments_serialize(url.path->List_0) + seq![b'/'] + cur + s,
        segs_acc(url, cur, s) == (UrlRecord { path: segs_acc(url, cur, s).path, ..url }),
        !path_is_empty_list(url) ==> !path_is_empty_list(segs_acc(url, cur, s)),
    decreases s.len(),
{
    let segs = url.path->List_0;
    if s.len() == 0 {
        assert(segments_serialize(segs) + seq![b'/'] + cur + s =~= segments_serialize(segs)
            + seq![b'/'] + cur);
    } else if s[0] == b'/' {
        let u1 = push_segment(url, cur);
        lemma_segments_push(segs, cur);
        lemma_segments_ok_push(segs, cur);
        lemma_segs_acc(u1, Seq::empty(), s.skip(1));
        assert(s =~= seq![b'/'] + s.skip(1));
        assert(segments_serialize(segs.push(cur)) + seq![b'/'] + Seq::<u8>::empty() + s.skip(1)
            =~= segments_serialize(segs) + seq![b'/'] + cur + s);
    } else {
        let c2 = cur.push(s[0]);
        assert(no_byte(c2, b'/')) by {
            assert forall|i: int| 0 <= i < c2.len() implies c2[i] != b'/' by {
                if i < cur.len() {
                    assert(c2[i] == cur[i]);
                }
            }
        }
        lemma_segs_acc(url, c2, s.skip(1));
        assert(s =~= seq![s[0]] + s.skip(1));
        assert(segments_serialize(segs) + seq![b'/'] + c2 + s.skip(1) =~= segments_serialize(segs)
            + seq![b'/'] + cur + s);
    }
}

/// The path state over a run of fast bytes.
proof fn lemma_run_path_fast(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p0: int, p: int, k: int)
    requires
        0 <= p0 <= p <= k <= input.len(),
        m.state == State::Path,
        m.url.path is List,
        m.url.scheme != s_file() || !path_is_empty_list(m.url),
        forall|j: int| p <= j < k ==> fast_at(input, j, p0),
        m.buffer.len() > 0 ==> m.buffer[0] != b'.' && m.buffer[0] != b'%',
        m.buffer.len() == 0 ==> (p == p0 || input[p - 1] == b'/'),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine {
                url: segs_acc(m.url, m.buffer, input.subrange(p, k)),
                buffer: tail_acc(m.buffer, input.subrange(p, k)),
                ..m
            },
            k,
        ),
        ({
            let t = tail_acc(m.buffer, input.subrange(p, k));
            t.len() > 0 ==> t[0] != b'.' && t[0] != b'%'
        }),
    decreases k - p,
{
    let s = input.subrange(p, k);
    if p == k {
        assert(s =~= Seq::<u8>::empty());
        assert(m == Machine { url: m.url, buffer: m.buffer, ..m });
    } else {
        let c = input[p];
        assert(s[0] == c);
        assert(s.skip(1) =~= input.subrange(p + 1, k));
        assert(fast_at(input, p, p0));
        if c == b'/' {
            lemma_run_path_end(input, b, m, p);
            lemma_not_dot(m.buffer);
            let m2 = Machine { url: push_segment(m.url, m.buffer), buffer: Seq::empty(), ..m };
            assert(path_seg_url(m.url, m.buffer, true) == push_segment(m.url, m.buffer));
            lemma_run_path_fast(input, b, m2, p0, p + 1, k);
        } else {
            assert(!path_end_byte(input, p, is_special(m.url)));
            lemma_run_path_chars(input, b, m, p, p + 1);
            assert(input.subrange(p, p + 1) =~= seq![c]);
            assert(!in_encode_set(EncodeSet::Path, c));
            lemma_pe_seq_cons(c, Seq::empty(), EncodeSet::Path);
            assert(seq![c] =~= seq![c] + Seq::<u8>::empty());
            assert(pe_seq(Seq::<u8>::empty(), EncodeSet::Path) =~= Seq::<u8>::empty());
            assert(pe_seq(input.subrange(p, p + 1), EncodeSet::Path) =~= seq![c]);
            let m2 = Machine { buffer: m.buffer.push(c), ..m };
            assert(m.buffer + seq![c] =~= m.buffer.push(c));
            assert(m2.buffer[0] == if m.buffer.len() > 0 { m.buffer[0] } else { c });
            lemma_run_path_fast(input, b, m2, p0, p + 1, k);
        }
    }
}

/// Bit `k` of a mask.
pub open spec fn pbit(m: u32, k: u32) -> bool {
    (m >> k) & 1u32 == 1u32
}

/// Bit `j` of the stop mask of a 17-byte window: the fast path run stops at
/// `w[j + 1]` given the byte `w[j]` before it.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn path_mask16(w: &[u8]) -> (m: u32)
    requires
        w.len() == 17,
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> #[trigger] pbit(m, j) == pstop(w@[j + 1], w@[j as int]),
{
    let m = crate::simd::path_mask16_sse(w);
    proof {
        assert forall|j: u32| j < 16 implies #[trigger] pbit(m, j) == pstop(w@[j + 1], w@[j as int]) by {
            assert(verilith_simd::sse2::bit(m, j) == pstop(w@[j + 1], w@[j as int]));
        }
    }
    m
}

/// Bit `j` of the stop mask of a 17-byte window: the fast path run stops at
/// `w[j + 1]` given the byte `w[j]` before it.
#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn path_mask16(w: &[u8]) -> (m: u32)
    requires
        w.len() == 17,
    ensures
        m < 0x10000,
        forall|j: u32| j < 16 ==> #[trigger] pbit(m, j) == pstop(w@[j + 1], w@[j as int]),
{
    if verilith_simd::neon::has_neon() {
        let m = crate::simd::path_mask16_neon(w);
        proof {
            assert forall|j: u32| j < 16 implies #[trigger] pbit(m, j) == pstop(w@[j + 1], w@[j as int]) by {
                assert(verilith_simd::sse2::bit(m, j) == pstop(w@[j + 1], w@[j as int]));
            }
        }
        return m;
    }
    let mut m: u32 = 0;
    let mut i: u32 = 0;
    proof {
        assert((1u32 << 0u32) == 1u32) by (bit_vector);
    }
    while i < 16
        invariant
            i <= 16,
            w.len() == 17,
            m < (1u32 << i),
            forall|j: u32| j < i ==> #[trigger] pbit(m, j) == pstop(w@[j + 1], w@[j as int]),
        decreases 16 - i,
    {
        let c = w[i as usize + 1];
        let prev = w[i as usize];
        let st = (c <= 0x20) | (c >= 0x7F) | (c == 0x22) | (c == 0x23) | (c == 0x3C) | (c == 0x3E)
            | (c == 0x3F) | (c == 0x5C) | (c == 0x5E) | (c == 0x60) | (c == 0x7B) | (c == 0x7D) | (((c
            == 0x2E) | (c == 0x25)) & (prev == 0x2F));
        let x = st as u32;
        proof {
            assert(st == pstop(c, prev));
            assert forall|j: u32| j < i + 1 implies #[trigger] pbit(m | (x << i), j) == pstop(w@[j + 1], w@[j as int]) by {
                crate::encode::lemma_mask_bit(m, x, i, j);
                if j < i {
                    assert(pbit(m, j) == pstop(w@[j + 1], w@[j as int]));
                } else {
                    assert(j == i);
                    assert(w@[j + 1] == c && w@[j as int] == prev);
                    assert((x == 1) == st);
                }
            }
            crate::encode::lemma_mask_bit(m, x, i, 0);
        }
        m = m | (x << i);
        i = i + 1;
    }
    proof {
        assert((1u32 << 16u32) == 0x10000u32) by (bit_vector);
    }
    m
}

/// Bits of a 16-bit mask shifted down by `d`.
proof fn lemma_shr_bit(m: u32, d: u32, i: u32)
    requires
        m < 0x10000,
        d < 16,
        i < 32,
    ensures
        (m >> d) < 0x10000,
        d + i < 16 ==> (pbit(m >> d, i) == pbit(m, (d + i) as u32)),
        d + i >= 16 ==> !pbit(m >> d, i),
{
    assert((m >> d) < 0x10000u32) by (bit_vector)
        requires
            m < 0x10000u32,
    ;
    assert(d + i < 16 ==> ((((m >> d) >> i) & 1u32 == 1u32) == ((m >> ((d + i) as u32)) & 1u32 == 1u32))) by (bit_vector)
        requires
            d < 16u32,
            i < 32u32,
    ;
    assert(d + i >= 16 ==> (((m >> d) >> i) & 1u32 != 1u32)) by (bit_vector)
        requires
            m < 0x10000u32,
            d < 16u32,
            i < 32u32,
    ;
}

pub open spec fn pstop(c: u8, prev: u8) -> bool {
    in_path_set(c) || c == b'\\' || ((c == b'.' || c == b'%') && prev == b'/')
}

/// The first `i` in `d..16` where the fast run stops at `w[i + 1]`, or 16.
#[inline(always)]
fn path_first16(w: &[u8], d: u32) -> (r: u32)
    requires
        w.len() == 17,
        d < 16,
    ensures
        d <= r <= 16,
        forall|j: u32| d <= j < r ==> !pstop(#[trigger] w@[j + 1], w@[j as int]),
        r < 16 ==> pstop(w@[r + 1], w@[r as int]),
{
    // One vector compare chain and a movemask: bit `j` of `m` is the stop
    // at `w[j + 1]`, and the lowest set bit at or above `d` is the answer.
    let m = path_mask16(w);
    let g = m >> d;
    proof {
        lemma_shr_bit(m, d, 0);
    }
    let r0 = verilith_simd::sse2::first_set16(g);
    proof {
        if r0 < 16 {
            lemma_shr_bit(m, d, r0 as u32);
            assert(verilith_simd::sse2::bit(g, r0 as u32));
        }
    }
    let r = if r0 < 16 { d + r0 as u32 } else { 16 };
    proof {
        assert forall|j: u32| d <= j < r implies !pstop(#[trigger] w@[j + 1], w@[j as int]) by {
            let i = (j - d) as u32;
            lemma_shr_bit(m, d, i);
            assert(!verilith_simd::sse2::bit(g, i));
            assert(j == (d + i) as u32);
        }
        if r < 16 {
            assert(pbit(m, r));
        }
    }
    r
}

/// The end of the fast run from `p`: the first byte that is not `fast_at`.
fn path_fast_scan(input: &[u8], p: usize, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        p < input.len(),
    ensures
        final(cost).n <= old(cost).n + 2 * (k - p) + 18,
        p <= k <= input.len(),
        forall|j: int| p <= j < k ==> fast_at(input@, j, p as int),
        k < input.len() ==> !fast_at(input@, k as int, p as int),
{
    let t = vstd::slice::slice_subrange(input, 0, input.len());
    let n = t.len();
    proof {
        lemma_cls();
        assert(t@ =~= input@);
    }
    let c = t[p];
    if cls(c) & (PATH | BACKSLASH) != 0 || c == b'.' || c == b'%' {
        proof {
            lemma_and_or(CLS@[c as int], PATH, BACKSLASH);
            assert(cls_has(c, PATH) == cls_pred(PATH, c));
            assert(cls_has(c, BACKSLASH) == cls_pred(BACKSLASH, c));
        }
        return p;
    }
    proof {
        lemma_and_or(CLS@[c as int], PATH, BACKSLASH);
        assert(cls_has(c, PATH) == cls_pred(PATH, c));
        assert(cls_has(c, BACKSLASH) == cls_pred(BACKSLASH, c));
        assert(fast_at(input@, p as int, p as int));
    }
    let mut k = p + 1;
    while n - k >= 16
        invariant
            p < k <= n == input.len(),
            t@ == input@,
            forall|j: int| p <= j < k ==> fast_at(input@, j, p as int),
            cost.n <= old(cost).n + (k - p),
        decreases n - k,
    {
        let w = vstd::slice::slice_subrange(t, k - 1, k + 16);
        let r = path_first16(w, 0);
        if r < 16 {
            proof {
                assert forall|j: int| p <= j < k + r implies fast_at(input@, j, p as int) by {
                    if j >= k {
                        let jj = (j - k) as u32;
                        assert(input@[j] == w@[jj + 1]);
                        assert(input@[j - 1] == w@[jj as int]);
                        assert(!pstop(w@[jj + 1], w@[jj as int]));
                    }
                }
                assert(input@[k + r] == w@[r + 1]);
                assert(input@[k + r - 1] == w@[r as int]);
            }
            return k + r as usize;
        }
        proof {
            cost.n = cost.n + 1;
        }
        proof {
            assert forall|j: int| p <= j < k + 16 implies fast_at(input@, j, p as int) by {
                if j >= k {
                    let jj = (j - k) as u32;
                    assert(input@[j] == w@[jj + 1]);
                    assert(input@[j - 1] == w@[jj as int]);
                    assert(!pstop(w@[jj + 1], w@[jj as int]));
                }
            }
        }
        k = k + 16;
    }
    // Fewer than 16 bytes remain: the last 16 bytes of the input, from
    // the first unchecked one.
    if n >= 17 && k < n {
        let st = n - 16;
        let w = vstd::slice::slice_subrange(t, st - 1, n);
        let d = (k - st) as u32;
        let r = path_first16(w, d);
        proof {
            assert forall|j: int| p <= j < st + r implies fast_at(input@, j, p as int) by {
                if j >= k {
                    let jj = (j - st) as u32;
                    assert(input@[j] == w@[jj + 1]);
                    assert(input@[j - 1] == w@[jj as int]);
                    assert(!pstop(w@[jj + 1], w@[jj as int]));
                }
            }
        }
        if r == 16 {
            return n;
        }
        proof {
            assert(input@[st + r] == w@[r + 1]);
            assert(input@[st + r - 1] == w@[r as int]);
        }
        return st + r as usize;
    }
    loop
        invariant
            p < k <= n == input.len(),
            t@ == input@,
            forall|j: int| p <= j < k ==> fast_at(input@, j, p as int),
            cost.n <= old(cost).n + (k - p),
        decreases n - k,
    {
        if k >= n {
            return k;
        }
        let c = t[k];
        let stop = cls(c) & (PATH | BACKSLASH) != 0 || ((c == b'.' || c == b'%') && t[k - 1] == b'/');
        proof {
            lemma_cls();
            lemma_and_or(CLS@[c as int], PATH, BACKSLASH);
            assert(cls_has(c, PATH) == cls_pred(PATH, c));
            assert(cls_has(c, BACKSLASH) == cls_pred(BACKSLASH, c));
            assert(stop == !fast_at(input@, k as int, p as int));
        }
        if stop {
            return k;
        }
        k = k + 1;
    }
}

/// `path_fast`'s copy of the whole segments in `input[p..q]`.
fn path_fast_segs(ps: &mut Parser, input: &[u8], base: Option<&Url>, q: usize, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Path,
        old(ps).bs == old(ps).href@.len(),
        old(ps).gm@.url.scheme != s_file() || !path_is_empty_list(old(ps).gm@.url),
        old(ps).p < q <= input.len(),
        input@[q - 1] == b'/',
        forall|j: int| old(ps).p <= j < q ==> fast_at(input@, j, old(ps).p as int),
    ensures
        final(cost).n == old(cost).n + (q - old(ps).p),
        final(ps).href@.len() == old(ps).href@.len() + (q - old(ps).p),
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Path,
        final(ps).p == q,
        final(ps).bs == final(ps).href@.len(),
        final(ps).gm@.url.scheme == old(ps).gm@.url.scheme,
        final(ps).special == old(ps).special,
        run(input@, base_rec(base), None, old(ps).gm@, old(ps).p as int) == run(
            input@,
            base_rec(base),
            None,
            final(ps).gm@,
            final(ps).p as int,
        ),
{
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let p = ps.p;
    let ghost seg = input@.subrange(p as int, q as int);
    proof {
        assert(m.buffer.len() == 0);
        lemma_run_path_fast(input@, base_rec(base), m, p as int, p as int, q as int);
        assert(seg[seg.len() - 1] == input@[q - 1]);
        lemma_tail_acc_slash(m.buffer, seg);
        lemma_segs_acc(url, m.buffer, seg);
    }
    let ghost url2 = segs_acc(url, m.buffer, seg);
    let ghost h0 = ps.href@;
    append_range(&mut ps.href, input, p, q, Tracked(cost));
    ps.bs = ps.href.len();
    ps.gm = Ghost(Machine { url: url2, buffer: Seq::empty(), ..m });
    ps.p = q;
    proof {
        assert(core_serialize(url) =~= url.scheme + seq![b':'] + authority_serialize(url)
            + segments_serialize(url.path->List_0));
        assert(core_serialize(url2) =~= url.scheme + seq![b':'] + authority_serialize(url)
            + segments_serialize(url2.path->List_0));
        assert(m.buffer =~= Seq::<u8>::empty());
        assert(h0 =~= core_serialize(url) + seq![b'/']);
        assert(ps.href@ =~= h0 + seg);
        assert(segments_serialize(url2.path->List_0) + seq![b'/'] =~= segments_serialize(
            url.path->List_0,
        ) + seq![b'/'] + seg);
        let pre = url.scheme + seq![b':'] + authority_serialize(url);
        assert(ps.href@ =~= pre + (segments_serialize(url.path->List_0) + seq![b'/'] + seg));
        assert(ps.href@ =~= pre + (segments_serialize(url2.path->List_0) + seq![b'/']));
        assert(ps.href@ =~= core_serialize(url2) + seq![b'/'] + Seq::<u8>::empty());
    }
}

/// `path_fast` when the run reaches the end of the path: copy the rest of
/// the path, push its last segment and leave the path state.
#[verifier::rlimit(60)]
fn path_fast_end(ps: &mut Parser, input: &[u8], base: Option<&Url>, k: usize, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Path,
        old(ps).bs == old(ps).href@.len(),
        old(ps).gm@.url.scheme != s_file() || !path_is_empty_list(old(ps).gm@.url),
        old(ps).p < k <= input.len(),
        k == input.len() || input@[k as int] == b'?' || input@[k as int] == b'#',
        forall|j: int| old(ps).p <= j < k ==> fast_at(input@, j, old(ps).p as int),
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
        r is Continue ==> final(ps).state == State::Query || final(ps).state == State::Fragment,
        !(r is Fail),
        final(cost).n == old(cost).n + (k - old(ps).p),
        r is Continue ==> final(ps).p == k + 1 && final(ps).href@.len() == old(ps).href@.len() + (k - old(ps).p) + 1,
        r is Done ==> final(ps).href@.len() == old(ps).href@.len() + (k - old(ps).p),
{
    let ghost b = base_rec(base);
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let p = ps.p;
    let ghost s = input@.subrange(p as int, k as int);
    proof {
        assert(m.buffer.len() == 0);
        lemma_run_path_fast(input@, b, m, p as int, p as int, k as int);
        lemma_segs_acc(url, m.buffer, s);
    }
    let ghost url3 = segs_acc(url, m.buffer, s);
    let ghost tail = tail_acc(m.buffer, s);
    let ghost url4 = push_segment(url3, tail);
    proof {
        lemma_not_dot(tail);
        lemma_run_path_end(input@, b, Machine { url: url3, buffer: tail, ..m }, k as int);
        assert(path_seg_url(url3, tail, false) == url4);
        lemma_segments_push(url3.path->List_0, tail);
        lemma_segments_ok_push(url3.path->List_0, tail);
    }
    let ghost h0 = ps.href@;
    let ghost c0 = cost.n;
    append_range(&mut ps.href, input, p, k, Tracked(cost));
    let ghost h1 = ps.href@.len();
    proof {
        assert(h1 == h0.len() + (k - p));
        assert(cost.n == c0 + (k - p));
    }
    ps.gm = Ghost(Machine { url: url4, buffer: Seq::empty(), ..m });
    ps.p = k;
    proof {
        let pre = url.scheme + seq![b':'] + authority_serialize(url);
        assert(m.buffer =~= Seq::<u8>::empty());
        assert(core_serialize(url) =~= pre + segments_serialize(url.path->List_0));
        assert(core_serialize(url4) =~= pre + segments_serialize(url4.path->List_0));
        assert(h0 =~= core_serialize(url) + seq![b'/']);
        assert(ps.href@ =~= h0 + s);
        assert(segments_serialize(url4.path->List_0) =~= segments_serialize(url3.path->List_0)
            + seq![b'/'] + tail);
        assert(segments_serialize(url3.path->List_0) + seq![b'/'] + tail =~= segments_serialize(
            url.path->List_0,
        ) + seq![b'/'] + Seq::<u8>::empty() + s);
        assert(ps.href@ =~= pre + (segments_serialize(url.path->List_0) + seq![b'/'] + s));
        assert(ps.href@ =~= core_serialize(url4));
        lemma_core_parts(url4);
    }
    if k < input.len() {
        ps.gm = Ghost(Machine { state: State::PathStart, ..ps.gm@ });
        ps.state = State::PathStart;
        if input[k] == b'?' {
            begin_query(ps, input, base);
        } else {
            begin_fragment(ps, input, base);
        }
        proof {
            assert(ps.href@.len() == h1 + 1);
            assert(ps.p == k + 1);
            lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), old(cost).n as int, cost.n as int, 1);
        }
        Flow::Continue
    } else {
        proof {
            assert(ps.href@.len() == h1);
            lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
        }
        Flow::Done
    }
}

/// `input[p..w]` has no byte that ends a path segment.
pub open spec fn seg_prefix(input: Seq<u8>, p: int, w: int, special: bool) -> bool {
    &&& p <= w <= input.len()
    &&& forall|j: int| p <= j < w ==> !path_end_byte(input, j, special)
}

/// With an empty segment buffer and no file scheme, copies the path in one
/// run when it has no byte to encode, no "\\" and no segment starting
/// with "." or "%"; otherwise copies the whole segments before the first
/// such byte and leaves the rest to the per-segment code.
fn path_fast(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Flow>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Path,
    ensures
        r is None ==> exists|w: int|
            #[trigger] seg_prefix(input@, final(ps).p as int, w, old(ps).special) && final(cost).n
                + final(ps).href@.len() <= old(cost).n + old(ps).href@.len() + 5 * (final(ps).p
                - old(ps).p) + 3 * (w - final(ps).p) + 20,
        r is None ==> {
            &&& final(ps).inv(input@, base_rec(base))
            &&& final(ps).state == State::Path
            &&& old(ps).p <= final(ps).p
            &&& final(ps).special == old(ps).special
            &&& run(input@, base_rec(base), None, old(ps).gm@, old(ps).p as int) == run(
                input@,
                base_rec(base),
                None,
                final(ps).gm@,
                final(ps).p as int,
            )
        },
        r matches Some(f) ==> {
            &&& handler_ok(old(ps), final(ps), input@, base_rec(base), f, old(cost).n, final(cost).n)
            &&& (f is Continue ==> final(ps).state == State::Query || final(ps).state == State::Fragment)
            &&& !(f is Fail)
        },
{
    hide(run);
    hide(step);
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let p = ps.p;
    let ghost special = ps.special;
    proof {
        assert(seg_prefix(input@, p as int, p as int, special));
    }
    if ps.bs != ps.href.len() || p >= input.len() {
        return None;
    }
    let se = ps.scheme_end;
    proof {
        lemma_core_parts(url);
        assert(ps.href@.subrange(0, se as int) =~= url.scheme);
    }
    // A file URL's first segment may be a drive letter to fix; once the
    // path has a segment, file URLs read paths like the others.
    if is_file_exec(vstd::slice::slice_subrange(ps.href.as_slice(), 0, se)) && ps.href.len() - ps.path_start <= 1 {
        return None;
    }
    proof {
        if url.scheme == s_file() && path_is_empty_list(url) {
            assert(ps.href@.len() > ps.path_start + 1);
            assert(path_serialize(url.path) =~= Seq::<u8>::empty());
            assert(o_query_start(url) == ps.path_start);
            assert(query_serialize(url).len() == 0);
            assert(fragment_serialize(url).len() == 0);
            assert(ps.href@.len() == o_query_start(url) + 1);
        }
    }
    let ghost c0 = cost.n;
    let k = path_fast_scan(input, p, Tracked(cost));
    if k > p && (k == input.len() || input[k] == b'?' || input[k] == b'#') {
        let ghost c1 = cost.n;
        let r = path_fast_end(ps, input, base, k, Tracked(cost));
        proof {
            assert(c1 <= c0 + 2 * (k - p) + 18);
            if r is Continue {
                assert(level(ps.state) <= 2);
                lemma_pot_drop_n(old(ps), ps, input@, base_rec(base), c0 as int, cost.n as int, 1);
            } else {
                lemma_pot_fail(old(ps), input@, base_rec(base), c0 as int, (cost.n + ps.href@.len()) as int, 1);
            }
        }
        return Some(r);
    }
    let ghost c1 = cost.n;
    let mut q = k;
    while q > p && input[q - 1] != b'/'
        invariant
            p <= q <= k <= input.len(),
            forall|j: int| q <= j < k ==> input@[j] != b'/',
            cost.n == c1 + (k - q),
        decreases q,
    {
        proof {
            cost.n = cost.n + 1;
        }
        q = q - 1;
    }
    proof {
        assert forall|j: int| q <= j < k implies !path_end_byte(input@, j, special) by {
            assert(fast_at(input@, j, p as int));
        }
        assert(seg_prefix(input@, q as int, k as int, special));
    }
    if q > p {
        path_fast_segs(ps, input, base, q, Tracked(cost));
    }
    proof {
        assert(seg_prefix(input@, ps.p as int, k as int, special));
    }
    None
}

/// Moves the path state to the end of the current segment, encoding the
/// segment's bytes into `href` in one pass.
fn path_run_until(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Path,
    ensures
        final(cost).n <= old(cost).n + 22 * (k - old(ps).p) + 21,
        final(ps).href@.len() <= old(ps).href@.len() + 3 * (k - old(ps).p),
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Path,
        final(ps).p == k,
        old(ps).p <= k <= input.len(),
        forall|j: int| old(ps).p <= j < k ==> !path_end_byte(input@, j, old(ps).special),
        k < input.len() ==> path_end_byte(input@, k as int, old(ps).special),
        final(ps).special == old(ps).special,
        final(ps).gm@ == (Machine {
            buffer: old(ps).gm@.buffer + pe_seq(
                input@.subrange(old(ps).p as int, k as int),
                EncodeSet::Path,
            ),
            ..old(ps).gm@
        }),
{
    let ghost m = ps.gm@;
    let p = ps.p;
    let special = ps.special;
    let stop = if special {
        PATH_STOP | BACKSLASH
    } else {
        PATH_STOP
    };
    let k = append_pe_until(&mut ps.href, input, p, input.len(), EncodeSet::Path, stop, Tracked(cost));
    proof {
        lemma_cls();
        assert forall|j: int| p <= j <= k && j < input.len() implies cls_has(input@[j], stop)
            == path_end_byte(input@, j, special) by {
            lemma_and_or(CLS@[input@[j] as int], PATH_STOP, BACKSLASH);
            assert(cls_has(input@[j], PATH_STOP) == cls_pred(PATH_STOP, input@[j]));
            assert(cls_has(input@[j], BACKSLASH) == cls_pred(BACKSLASH, input@[j]));
        }
        assert forall|j: int| p <= j < k implies input@[j] != b'/' by {
            assert(!cls_has(input@[j], stop));
            assert(cls_has(input@[j], stop) == path_end_byte(input@, j, special));
        }
    }
    let ghost add = pe_seq(input@.subrange(p as int, k as int), EncodeSet::Path);
    proof {
        lemma_pe_seq_no_slash(input@.subrange(p as int, k as int), EncodeSet::Path);
        lemma_pe_seq_len(input@.subrange(p as int, k as int), EncodeSet::Path);
    }
    ps.gm = Ghost(Machine { buffer: m.buffer + add, ..m });
    ps.p = k;
    proof {
        assert(ps.href@ =~= core_serialize(m.url) + seq![b'/'] + ps.gm@.buffer);
        assert forall|i: int| 0 <= i < ps.gm@.buffer.len() implies ps.gm@.buffer[i] != b'/' by {
            if i >= m.buffer.len() {
                assert(ps.gm@.buffer[i] == add[i - m.buffer.len()]);
            } else {
                assert(ps.gm@.buffer[i] == m.buffer[i]);
            }
        }
    }
    k
}

/// The facts about `href` in the path state that the segment helpers use.
pub open spec fn seg_pre(href: Seq<u8>, ss: int, url: UrlRecord, buf: Seq<u8>, scheme_end: usize, path_start: usize) -> bool {
    &&& href == core_serialize(url) + seq![b'/'] + buf
    &&& ss + buf.len() == href.len()
    &&& url.path is List
    &&& path_ok(url.path)
    &&& url.query is None
    &&& url.fragment is None
    &&& no_byte(buf, b'/')
    &&& scheme_end == url.scheme.len()
    &&& path_start == o_path_start(url)
}

/// A ".." segment.
fn seg_double(href: &mut Vec<u8>, ss: usize, scheme_end: usize, path_start: usize, slash: bool, Ghost(url): Ghost<UrlRecord>, Ghost(buf): Ghost<Seq<u8>>, Tracked(cost): Tracked<&mut Meter>)
    requires
        seg_pre(old(href)@, ss as int, url, buf, scheme_end, path_start),
    ensures
        final(cost).n + final(href)@.len() <= old(cost).n + old(href)@.len() + 2,
        ({
            let u1 = shorten_path(url);
            let u2 = if !slash { push_segment(u1, Seq::empty()) } else { u1 };
            &&& final(href)@ == core_serialize(u2)
            &&& path_ok(u2.path)
            &&& u2.path is List
        }),
{
    proof {
        lemma_core_parts(url);
    }
    href.truncate(ss - 1);
    proof {
        assert(href@ =~= core_serialize(url));
    }
    shorten_exec(href, scheme_end, path_start, Ghost(url), Tracked(cost));
    let ghost u1 = shorten_path(url);
    if !slash {
        href.push(b'/');
        proof {
            lemma_core_parts(u1);
            let u2 = push_segment(u1, Seq::empty());
            lemma_core_parts(u2);
            lemma_segments_push(u1.path->List_0, Seq::empty());
            lemma_segments_ok_push(u1.path->List_0, Seq::empty());
            assert(href@ =~= core_serialize(u2));
        }
    }
}

/// A segment other than "." or "..": append it, normalizing a Windows
/// drive letter at the start of a file path.
fn seg_push(href: &mut Vec<u8>, ss: usize, scheme_end: usize, path_start: usize, Ghost(url): Ghost<UrlRecord>, Ghost(buf): Ghost<Seq<u8>>)
    requires
        seg_pre(old(href)@, ss as int, url, buf, scheme_end, path_start),
    ensures
        ({
            let seg = if url.scheme == s_file() && path_is_empty_list(url) && is_windows_drive_letter(buf) {
                buf.update(1, b':')
            } else {
                buf
            };
            let u2 = push_segment(url, seg);
            &&& final(href)@ == core_serialize(u2)
            &&& path_ok(u2.path)
            &&& u2.path is List
        }),
        final(href)@.len() == old(href)@.len(),
{
    let ghost segs = url.path->List_0;
    let n = href.len();
    proof {
        lemma_core_parts(url);
        lemma_segments_len(segs);
        assert(href@.subrange(0, scheme_end as int) =~= url.scheme);
    }
    let empty = ss - 1 == path_start;
    let drive = n - ss == 2 && is_alpha(href[ss]) && (href[ss + 1] == b':' || href[ss + 1] == b'|');
    let file = drive && empty && is_file_exec(vstd::slice::slice_subrange(href.as_slice(), 0, scheme_end));
    proof {
        assert(empty <==> path_is_empty_list(url)) by {
            if segs.len() > 0 {
                assert(segments_serialize(segs).len() > 0);
            } else {
                assert(segs =~= Seq::<Seq<u8>>::empty());
            }
        }
        if n - ss == 2 {
            assert(buf[0] == href@[ss as int]);
            assert(buf[1] == href@[ss + 1]);
        }
        assert(drive <==> is_windows_drive_letter(buf));
    }
    let ghost seg = if file && empty && drive {
        buf.update(1, b':')
    } else {
        buf
    };
    if file && empty && drive {
        href.set(ss + 1, b':');
    }
    proof {
        assert(no_byte(seg, b'/'));
        lemma_segments_push(segs, seg);
        lemma_segments_ok_push(segs, seg);
        let u2 = push_segment(url, seg);
        lemma_core_parts(u2);
        assert(href@ =~= core_serialize(u2));
    }
}

/// The path state finishes a segment: `href` becomes the core
/// serialization of the URL with the segment applied.
#[verifier::rlimit(60)]
fn path_segment(ps: &mut Parser, input: &[u8], base: Option<&Url>, slash: bool, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Path,
    ensures
        final(cost).n + final(ps).href@.len() <= old(cost).n + old(ps).href@.len() + 2,
        ({
            let url2 = path_seg_url(old(ps).gm@.url, old(ps).gm@.buffer, slash);
            &&& final(ps).gm@ == (Machine { url: url2, buffer: Seq::empty(), ..old(ps).gm@ })
            &&& final(ps).href@ == core_serialize(url2)
            &&& url2.path is List
            &&& path_ok(url2.path)
            &&& url2.query is None
            &&& url2.fragment is None
            &&& url2.scheme == old(ps).gm@.url.scheme
            &&& offsets_ok(final(ps), url2)
            &&& tail_offsets_ok(final(ps), url2)
        }),
        final(ps).p == old(ps).p,
        final(ps).state == old(ps).state,
        final(ps).special == old(ps).special,
        final(ps).at_sign_seen == old(ps).at_sign_seen,
        final(ps).inside_brackets == old(ps).inside_brackets,
        final(ps).pts == old(ps).pts,
{
    let ghost m = ps.gm@;
    let ghost url = m.url;
    let ghost buf = m.buffer;
    let ss = ps.bs;
    let n = ps.href.len();
    proof {
        assert(ps.href@.subrange(ss as int, n as int) =~= buf);
    }
    // Dot segments start with "." or "%".
    let maybe_dot = n > ss && (ps.href[ss] == b'.' || ps.href[ss] == b'%');
    let dd = maybe_dot && is_double_dot_exec(vstd::slice::slice_subrange(ps.href.as_slice(), ss, n));
    let sd = maybe_dot && is_single_dot_exec(vstd::slice::slice_subrange(ps.href.as_slice(), ss, n));
    proof {
        if !maybe_dot {
            if n > ss {
                lemma_lower_seq(buf);
                lemma_lower_at(buf, 0);
                assert(buf[0] == ps.href@[ss as int]);
            } else {
                lemma_lower_seq(buf);
            }
            assert(!is_double_dot_segment(buf));
            assert(!is_single_dot_segment(buf));
        }
    }
    let ghost url2 = path_seg_url(url, buf, slash);
    if dd {
        seg_double(&mut ps.href, ss, ps.scheme_end, ps.path_start, slash, Ghost(url), Ghost(buf), Tracked(cost));
    } else if sd && !slash {
        ps.href.truncate(ss);
        proof {
            lemma_core_parts(url);
            lemma_segments_push(url.path->List_0, Seq::empty());
            lemma_segments_ok_push(url.path->List_0, Seq::empty());
            lemma_core_parts(url2);
            assert(ps.href@ =~= core_serialize(url2));
        }
    } else if !sd {
        seg_push(&mut ps.href, ss, ps.scheme_end, ps.path_start, Ghost(url), Ghost(buf));
    } else {
        ps.href.truncate(ss - 1);
        proof {
            assert(ps.href@ =~= core_serialize(url));
        }
    }
    ps.gm = Ghost(Machine { url: url2, buffer: Seq::empty(), ..m });
}

#[verifier::rlimit(100)]
fn h_path(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Path,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, ps.gm@, ps.p as int);
    let special = ps.special;
    loop
        invariant
            ps.inv(input@, b),
            ps.state == State::Path,
            ps.special == special,
            old(ps).p <= ps.p,
            old(ps).p <= input.len(),
            cost.n + COST_W * (input.len() - ps.p) + ps.href@.len() <= old(cost).n + COST_W * (input.len() - old(ps).p) + old(ps).href@.len(),
            target == run(input@, b, None, ps.gm@, ps.p as int),
            target == run(input@, b, None, old(ps).gm@, old(ps).p as int),
            b == base_rec(base),
            old(ps).state == State::Path,
        decreases input.len() - ps.p,
    {
        let ghost ca = cost.n;
        let ghost pa = ps.p;
        let ghost ha = ps.href@.len();
        let ghost psa = *ps;
        match path_fast(ps, input, base, Tracked(cost)) {
            Some(f) => {
                proof {
                    assert(pot(&psa, input@, b) == 4 * level_w(input@, b) + COST_W * (input.len() - pa) + ha);
                    assert(pot(old(ps), input@, b) == 4 * level_w(input@, b) + COST_W * (input.len() - old(ps).p) + old(ps).href@.len());
                }
                return f;
            },
            None => {},
        }
        // One tick for each pass that does not leave through the fast path.
        proof {
            cost.n = cost.n + 1;
        }
        let p = ps.p;
        let ghost cb = cost.n;
        let ghost hb = ps.href@.len();
        let ghost w = choose|w: int|
            #[trigger] seg_prefix(input@, p as int, w, special) && cb + hb <= ca + ha + 5 * (p - pa) + 3 * (w - p) + 21;
        let ghost m0 = ps.gm@;
        let k = path_run_until(ps, input, base, Tracked(cost));
        proof {
            lemma_run_path_chars(input@, b, m0, p as int, k as int);
            assert(w <= k) by {
                if w > k {
                    assert(!path_end_byte(input@, k as int, special));
                }
            }
            assert(cost.n + ps.href@.len() <= ca + ha + 5 * (p - pa) + 28 * (k - p) + 42);
        }
        let slash = k < input.len() && (input[k] == b'/' || (special && input[k] == b'\\'));
        proof {
            lemma_run_path_end(input@, b, ps.gm@, k as int);
        }
        path_segment(ps, input, base, slash, Tracked(cost));
        if slash {
            enter_path(ps, input, base);
            ps.p = k + 1;
        } else if k < input.len() {
            ps.gm = Ghost(Machine { state: State::PathStart, ..ps.gm@ });
            ps.state = State::PathStart;
            if input[k] == b'?' {
                begin_query(ps, input, base);
            } else {
                begin_fragment(ps, input, base);
            }
            proof {
                lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
            }
            return Flow::Continue;
        } else {
            proof {
                lemma_pot_fail(old(ps), input@, b, old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
            }
            return Flow::Done;
        }
    }
}

pub open spec fn opaque_plain(input: Seq<u8>, j: int) -> bool {
    &&& input[j] != b'?'
    &&& input[j] != b'#'
    &&& !(input[j] == b' ' && (remaining_starts_with(input, j, b'?') || remaining_starts_with(
        input,
        j,
        b'#',
    )))
}

pub open spec fn opaque_push(url: UrlRecord, s: Seq<u8>) -> UrlRecord {
    UrlRecord { path: UrlPath::Opaque(url.path->Opaque_0 + s), ..url }
}

/// The opaque path state copies a run of plain bytes, C0-encoded.
proof fn lemma_run_opaque_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::OpaquePath,
        m.url.path is Opaque,
        forall|j: int| p <= j < k ==> opaque_plain(input, j),
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine {
                url: opaque_push(m.url, pe_seq(input.subrange(p, k), EncodeSet::C0Control)),
                ..m
            },
            k,
        ),
    decreases k - p,
{
    let set = EncodeSet::C0Control;
    if p == k {
        assert(input.subrange(p, k) =~= Seq::<u8>::empty());
        assert(pe_seq(input.subrange(p, k), set) =~= Seq::<u8>::empty());
        assert(m.url.path->Opaque_0 + Seq::<u8>::empty() =~= m.url.path->Opaque_0);
        assert(opaque_push(m.url, Seq::<u8>::empty()) == m.url);
    } else {
        let c = input[p];
        assert(opaque_plain(input, p));
        let add = pe(c, set);
        assert(c == b' ' ==> add == seq![b' ']) by {
            if c == b' ' {
                assert(!in_encode_set(set, c));
            }
        }
        let m2 = Machine { url: opaque_push(m.url, add), ..m };
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_opaque_chars(input, b, m2, p + 1, k);
        let tail = input.subrange(p + 1, k);
        assert(input.subrange(p, k) =~= seq![c] + tail);
        lemma_pe_seq_cons(c, tail, set);
        assert(m.url.path->Opaque_0 + add + pe_seq(tail, set) =~= m.url.path->Opaque_0 + pe_seq(
            input.subrange(p, k),
            set,
        ));
    }
}

/// A space before "?" or "#" in an opaque path becomes "%20".
proof fn lemma_run_opaque_space(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int)
    requires
        0 <= p < input.len() - 1,
        m.state == State::OpaquePath,
        m.url.path is Opaque,
        input[p] == b' ',
        input[p + 1] == b'?' || input[p + 1] == b'#',
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { url: opaque_push(m.url, seq![b'%', b'2', b'0']), ..m },
            p + 1,
        ),
{
}

/// The opaque path state at "?", "#" or the end of the input.
proof fn lemma_run_opaque_end(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, k: int)
    requires
        0 <= k <= input.len(),
        m.state == State::OpaquePath,
        k == input.len() || input[k] == b'?' || input[k] == b'#',
    ensures
        k == input.len() ==> run(input, b, None, m, k) == Some(m.url),
        k < input.len() && input[k] == b'?' ==> run(input, b, None, m, k) == run(
            input,
            b,
            None,
            Machine { url: UrlRecord { query: Some(Seq::empty()), ..m.url }, state: State::Query, ..m },
            k + 1,
        ),
        k < input.len() && input[k] == b'#' ==> run(input, b, None, m, k) == run(
            input,
            b,
            None,
            Machine {
                url: UrlRecord { fragment: Some(Seq::empty()), ..m.url },
                state: State::Fragment,
                ..m
            },
            k + 1,
        ),
{
}

/// Moves the opaque path state to `k`, appending `input[p..k]` C0-encoded.
#[verifier::rlimit(40)]
fn opaque_run(ps: &mut Parser, input: &[u8], base: Option<&Url>, k: usize, Tracked(cost): Tracked<&mut Meter>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::OpaquePath,
        old(ps).p <= k <= input.len(),
    ensures
        final(cost).n <= old(cost).n + 3 * (k - old(ps).p),
        final(ps).href@.len() <= old(ps).href@.len() + 3 * (k - old(ps).p),
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::OpaquePath,
        final(ps).p == k,
        final(ps).gm@ == (Machine {
            url: opaque_push(
                old(ps).gm@.url,
                pe_seq(input@.subrange(old(ps).p as int, k as int), EncodeSet::C0Control),
            ),
            ..old(ps).gm@
        }),
{
    let ghost m = ps.gm@;
    let p = ps.p;
    append_pe(&mut ps.href, input, p, k, EncodeSet::C0Control, Tracked(cost));
    proof {
        lemma_pe_seq_len(input@.subrange(p as int, k as int), EncodeSet::C0Control);
    }
    let ghost url = opaque_push(
        m.url,
        pe_seq(input@.subrange(p as int, k as int), EncodeSet::C0Control),
    );
    ps.gm = Ghost(Machine { url, ..m });
    ps.p = k;
    proof {
        lemma_core_parts(url);
        lemma_core_parts(m.url);
        assert(ps.href@ =~= core_serialize(url));
    }
}

fn opaque_space(ps: &mut Parser, input: &[u8], base: Option<&Url>)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::OpaquePath,
    ensures
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::OpaquePath,
        final(ps).p == old(ps).p,
        final(ps).gm@ == (Machine {
            url: opaque_push(old(ps).gm@.url, seq![b'%', b'2', b'0']),
            ..old(ps).gm@
        }),
        final(ps).href@.len() == old(ps).href@.len() + 3,
{
    let ghost m = ps.gm@;
    ps.href.push(b'%');
    ps.href.push(b'2');
    ps.href.push(b'0');
    let ghost url = opaque_push(m.url, seq![b'%', b'2', b'0']);
    ps.gm = Ghost(Machine { url, ..m });
    proof {
        lemma_core_parts(url);
        lemma_core_parts(m.url);
        assert(ps.href@ =~= core_serialize(url));
    }
}

fn opaque_end(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::OpaquePath,
        old(ps).p == input.len() || input@[old(ps).p as int] == b'?' || input@[old(ps).p as int]
            == b'#',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
        final(cost).n == old(cost).n,
        r == Flow::Continue ==> level(final(ps).state) <= 2 && final(ps).p == old(ps).p + 1
            && final(ps).href@.len() == old(ps).href@.len() + 1,
        r == Flow::Done ==> final(ps).href@.len() == old(ps).href@.len(),
        r != Flow::Fail,
{
    let ghost m = ps.gm@;
    let k = ps.p;
    proof {
        lemma_run_opaque_end(input@, base_rec(base), m, k as int);
        lemma_core_parts(m.url);
    }
    if k == input.len() {
        proof {
            lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
        }
        return Flow::Done;
    }
    if input[k] == b'?' {
        let ghost url = UrlRecord { query: Some(Seq::empty()), ..m.url };
        ps.query_start = Some(ps.href.len());
        ps.href.push(b'?');
        ps.gm = Ghost(Machine { url, state: State::Query, ..m });
        ps.state = State::Query;
        ps.p = k + 1;
        proof {
            lemma_core_parts(url);
            assert(pe_seq(m.buffer, query_set(ps.special)) =~= Seq::<u8>::empty());
            assert(ps.href@ =~= core_serialize(url) + pe_seq(m.buffer, query_set(ps.special)));
        }
        Flow::Continue
    } else {
        let ghost url = UrlRecord { fragment: Some(Seq::empty()), ..m.url };
        ps.fragment_start = Some(ps.href.len());
        ps.href.push(b'#');
        ps.gm = Ghost(Machine { url, state: State::Fragment, ..m });
        ps.state = State::Fragment;
        ps.p = k + 1;
        proof {
            lemma_core_parts(url);
            assert(ps.href@ =~= core_serialize(url));
        }
        Flow::Continue
    }
}

#[verifier::rlimit(80)]
fn h_opaque_path(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::OpaquePath,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost b = base_rec(base);
    let ghost m = ps.gm@;
    let p = ps.p;
    let mut k = p;
    while k < input.len() && input[k] != b'?' && input[k] != b'#'
        invariant
            p <= k <= input.len(),
            forall|j: int| p <= j < k ==> input@[j] != b'?' && input@[j] != b'#',
            cost.n == old(cost).n + (k - p),
        decreases input.len() - k,
    {
        proof {
            cost.n = cost.n + 1;
        }
        k = k + 1;
    }
    // Only the byte just before "?" or "#" can be a space that needs "%20".
    let sp = k > p && k < input.len() && input[k - 1] == b' ';
    let k1 = if sp {
        k - 1
    } else {
        k
    };
    proof {
        assert forall|j: int| p <= j < k1 implies opaque_plain(input@, j) by {
            assert(j + 1 < k || j + 1 == k);
        }
        lemma_run_opaque_chars(input@, b, m, p as int, k1 as int);
    }
    opaque_run(ps, input, base, k1, Tracked(cost));
    if sp {
        proof {
            lemma_run_opaque_space(input@, b, ps.gm@, k1 as int);
        }
        opaque_space(ps, input, base);
        ps.p = k;
    }
    proof {
        assert(cost.n <= old(cost).n + 4 * (k - p));
        assert(ps.href@.len() <= old(ps).href@.len() + 3 * (k - p) + 3);
        assert(ps.p == k);
    }
    let r = opaque_end(ps, input, base, Tracked(cost));
    proof {
        if r == Flow::Continue {
            lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
        } else {
            lemma_pot_fail(old(ps), input@, b, old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
        }
    }
    r
}

/// The query state collects a run of bytes other than "#" into its buffer.
proof fn lemma_run_query_chars(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, k: int)
    requires
        0 <= p <= k <= input.len(),
        m.state == State::Query,
        forall|j: int| p <= j < k ==> input[j] != b'#',
    ensures
        run(input, b, None, m, p) == run(
            input,
            b,
            None,
            Machine { buffer: m.buffer + input.subrange(p, k), ..m },
            k,
        ),
    decreases k - p,
{
    if p == k {
        assert(m.buffer + input.subrange(p, k) =~= m.buffer);
        assert(m == Machine { buffer: m.buffer, ..m });
    } else {
        let m2 = Machine { buffer: m.buffer.push(input[p]), ..m };
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_query_chars(input, b, m2, p + 1, k);
        assert(m2.buffer + input.subrange(p + 1, k) =~= m.buffer + input.subrange(p, k));
    }
}

/// The query state at "#" or the end of the input.
proof fn lemma_run_query_end(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, k: int)
    requires
        0 <= k <= input.len(),
        m.state == State::Query,
        m.url.query is Some,
        k == input.len() || input[k] == b'#',
    ensures
        ({
            let set = if is_special(m.url) { EncodeSet::SpecialQuery } else { EncodeSet::Query };
            let url = UrlRecord { query: Some(m.url.query->0 + pe_seq(m.buffer, set)), ..m.url };
            if k == input.len() {
                run(input, b, None, m, k) == Some(url)
            } else {
                run(input, b, None, m, k) == run(
                    input,
                    b,
                    None,
                    Machine {
                        url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                        buffer: Seq::empty(),
                        state: State::Fragment,
                        ..m
                    },
                    k + 1,
                )
            }
        }),
{
}

/// Moves the query state to `k`, encoding `input[p..k]` into `href`.
fn query_run(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (k: usize)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Query,
    ensures
        final(cost).n <= old(cost).n + 22 * (k - old(ps).p) + 21,
        final(ps).href@.len() <= old(ps).href@.len() + 3 * (k - old(ps).p),
        final(ps).inv(input@, base_rec(base)),
        final(ps).state == State::Query,
        final(ps).p == k,
        old(ps).p <= k <= input.len(),
        forall|j: int| old(ps).p <= j < k ==> input@[j] != b'#',
        k < input.len() ==> input@[k as int] == b'#',
        final(ps).gm@ == (Machine {
            buffer: old(ps).gm@.buffer + input@.subrange(old(ps).p as int, k as int),
            ..old(ps).gm@
        }),
{
    let ghost m = ps.gm@;
    let p = ps.p;
    let set = if ps.special {
        EncodeSet::SpecialQuery
    } else {
        EncodeSet::Query
    };
    let k = append_pe_until(&mut ps.href, input, p, input.len(), set, HASH, Tracked(cost));
    proof {
        lemma_cls();
        lemma_pe_seq_append(m.buffer, input@.subrange(p as int, k as int), set);
        lemma_pe_seq_len(input@.subrange(p as int, k as int), set);
        assert forall|j: int| p <= j < k implies input@[j] != b'#' by {
            assert(!cls_has(input@[j], HASH));
        }
        if k < input.len() {
            assert(cls_has(input@[k as int], HASH));
        }
    }
    ps.gm = Ghost(Machine { buffer: m.buffer + input@.subrange(p as int, k as int), ..m });
    ps.p = k;
    proof {
        assert(ps.href@ =~= core_serialize(m.url) + pe_seq(ps.gm@.buffer, query_set(ps.special)));
    }
    k
}

/// The query state at "#" or the end of the input.
#[verifier::rlimit(30)]
fn query_end(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Query,
        old(ps).p == input.len() || input@[old(ps).p as int] == b'#',
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
        r != Flow::Fail,
        final(cost).n == old(cost).n,
        r == Flow::Continue ==> final(ps).state == State::Fragment && final(ps).p == old(ps).p + 1
            && final(ps).href@.len() == old(ps).href@.len() + 1,
        r == Flow::Done ==> final(ps).href@.len() == old(ps).href@.len(),
{
    let ghost m = ps.gm@;
    let ghost set = query_set(ps.special);
    let ghost url = UrlRecord { query: Some(m.url.query->0 + pe_seq(m.buffer, set)), ..m.url };
    let k = ps.p;
    proof {
        lemma_run_query_end(input@, base_rec(base), m, k as int);
        lemma_core_parts(url);
        lemma_core_parts(m.url);
        assert(ps.href@ =~= core_serialize(url));
    }
    if k < input.len() {
        let ghost url2 = UrlRecord { fragment: Some(Seq::empty()), ..url };
        ps.fragment_start = Some(ps.href.len());
        ps.href.push(b'#');
        ps.gm = Ghost(Machine { url: url2, buffer: Seq::empty(), state: State::Fragment, ..m });
        ps.state = State::Fragment;
        ps.p = k + 1;
        proof {
            lemma_core_parts(url2);
            assert(ps.href@ =~= core_serialize(url2));
        }
        Flow::Continue
    } else {
        ps.gm = Ghost(Machine { url, buffer: Seq::empty(), ..m });
        Flow::Done
    }
}

fn h_query(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Query,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    hide(run);
    hide(step);
    let ghost m = ps.gm@;
    let ghost b = base_rec(base);
    let p = ps.p;
    let k = query_run(ps, input, base, Tracked(cost));
    proof {
        lemma_run_query_chars(input@, b, m, p as int, k as int);
    }
    let r = query_end(ps, input, base, Tracked(cost));
    proof {
        if r == Flow::Continue {
            lemma_pot_drop_n(old(ps), ps, input@, b, old(cost).n as int, cost.n as int, 1);
        } else {
            lemma_pot_fail(old(ps), input@, b, old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
        }
    }
    r
}

proof fn lemma_pe_seq_cons(c: u8, s: Seq<u8>, set: EncodeSet)
    ensures
        pe_seq(seq![c] + s, set) == pe(c, set) + pe_seq(s, set),
{
    lemma_pe_seq_append(seq![c], s, set);
    lemma_pe_seq_push(Seq::empty(), c, set);
    assert(Seq::<u8>::empty().push(c) =~= seq![c]);
    assert(pe_seq(Seq::<u8>::empty(), set) =~= Seq::<u8>::empty());
    assert(Seq::<u8>::empty() + pe(c, set) =~= pe(c, set));
}

/// The fragment state runs to the end of the input.
proof fn lemma_run_fragment(input: Seq<u8>, b: Option<UrlRecord>, m: Machine, p: int, f: Seq<u8>)
    requires
        0 <= p <= input.len(),
        m.state == State::Fragment,
        m.url.fragment == Some(f),
    ensures
        run(input, b, None, m, p) == Some(
            UrlRecord {
                fragment: Some(f + pe_seq(input.subrange(p, input.len() as int), EncodeSet::Fragment)),
                ..m.url
            },
        ),
    decreases input.len() - p,
{
    let rest = input.subrange(p, input.len() as int);
    if p == input.len() {
        assert(rest =~= Seq::<u8>::empty());
        assert(pe_seq(rest, EncodeSet::Fragment) =~= Seq::<u8>::empty());
        assert(f + pe_seq(rest, EncodeSet::Fragment) =~= f);
        assert(m.url == UrlRecord { fragment: Some(f), ..m.url });
    } else {
        let c = input[p];
        let f2 = f + pe(c, EncodeSet::Fragment);
        let m2 = Machine { url: UrlRecord { fragment: Some(f2), ..m.url }, ..m };
        assert(step(input, b, None, m, p) == Step::Next(m2, p));
        lemma_run_fragment(input, b, m2, p + 1, f2);
        let tail = input.subrange(p + 1, input.len() as int);
        assert(rest =~= seq![c] + tail);
        lemma_pe_seq_cons(c, tail, EncodeSet::Fragment);
        assert(f2 + pe_seq(tail, EncodeSet::Fragment) =~= f + pe_seq(rest, EncodeSet::Fragment));
        if p + 1 >= input.len() {
            assert(tail =~= Seq::<u8>::empty());
            assert(pe_seq(tail, EncodeSet::Fragment) =~= Seq::<u8>::empty());
            assert(f2 + pe_seq(tail, EncodeSet::Fragment) =~= f2);
        }
    }
}

fn h_fragment(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
        old(ps).state == State::Fragment,
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    let ghost m = ps.gm@;
    let ghost f = m.url.fragment->0;
    let p = ps.p;
    append_pe(&mut ps.href, input, p, input.len(), EncodeSet::Fragment, Tracked(cost));
    let ghost url = UrlRecord {
        fragment: Some(f + pe_seq(input@.subrange(p as int, input.len() as int), EncodeSet::Fragment)),
        ..m.url
    };
    proof {
        lemma_run_fragment(input@, base_rec(base), m, p as int, f);
        lemma_pe_seq_len(input@.subrange(p as int, input.len() as int), EncodeSet::Fragment);
        lemma_core_parts(url);
        lemma_core_parts(m.url);
        assert(ps.href@ =~= core_serialize(url));
    }
    ps.gm = Ghost(Machine { url, ..m });
    proof {
        lemma_pot_fail(old(ps), input@, base_rec(base), old(cost).n as int, (cost.n + ps.href@.len()) as int, 1);
    }
    Flow::Done
}

#[inline(always)]
fn handle(ps: &mut Parser, input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Flow)
    requires
        old(ps).inv(input@, base_rec(base)),
        base matches Some(b) ==> b.wf(),
    ensures
        handler_ok(old(ps), final(ps), input@, base_rec(base), r, old(cost).n, final(cost).n),
{
    match ps.state {
        State::SchemeStart => h_scheme_start(ps, input, base, Tracked(cost)),
        State::Scheme => h_scheme(ps, input, base, Tracked(cost)),
        State::NoScheme => h_no_scheme(ps, input, base, Tracked(cost)),
        State::SpecialRelativeOrAuthority => h_special_relative_or_authority(ps, input, base, Tracked(cost)),
        State::PathOrAuthority => h_path_or_authority(ps, input, base, Tracked(cost)),
        State::Relative => h_relative(ps, input, base, Tracked(cost)),
        State::RelativeSlash => h_relative_slash(ps, input, base, Tracked(cost)),
        State::SpecialAuthoritySlashes => h_special_authority_slashes(ps, input, base, Tracked(cost)),
        State::SpecialAuthorityIgnoreSlashes => h_special_authority_ignore_slashes(ps, input, base, Tracked(cost)),
        State::Authority => h_authority(ps, input, base, sc, Tracked(cost)),
        State::Host | State::Hostname => h_host(ps, input, base, sc, Tracked(cost)),
        State::Port => h_port(ps, input, base, Tracked(cost)),
        State::File => h_file(ps, input, base, Tracked(cost)),
        State::FileSlash => h_file_slash(ps, input, base, Tracked(cost)),
        State::FileHost => h_file_host(ps, input, base, sc, Tracked(cost)),
        State::PathStart => h_path_start(ps, input, base, Tracked(cost)),
        State::Path => h_path(ps, input, base, Tracked(cost)),
        State::OpaquePath => h_opaque_path(ps, input, base, Tracked(cost)),
        State::Query => h_query(ps, input, base, Tracked(cost)),
        State::Fragment => h_fragment(ps, input, base, Tracked(cost)),
    }
}

/// The machine after "http://" or "https://" (scheme `input[..se]`), at
/// the authority state.
pub open spec fn fast_authority_machine(input: Seq<u8>, se: int) -> Machine {
    Machine {
        url: UrlRecord { scheme: input.subrange(0, se), ..new_url() },
        state: State::Authority,
        ..initial_machine(State::SchemeStart, new_url())
    }
}

/// The scheme state reads the lowercase letters of `input[k..se]`.
proof fn lemma_run_scheme_lower(input: Seq<u8>, b: Option<UrlRecord>, k: int, se: int)
    requires
        1 <= k <= se < input.len(),
        forall|j: int| 0 <= j < se ==> is_ascii_lower_alpha(#[trigger] input[j]),
    ensures
        run(input, b, None, Machine { buffer: input.subrange(0, k), state: State::Scheme, ..initial_machine(State::SchemeStart, new_url()) }, k)
            == run(input, b, None, Machine { buffer: input.subrange(0, se), state: State::Scheme, ..initial_machine(State::SchemeStart, new_url()) }, se),
    decreases se - k,
{
    if k < se {
        let m = Machine { buffer: input.subrange(0, k), state: State::Scheme, ..initial_machine(State::SchemeStart, new_url()) };
        let m2 = Machine { buffer: input.subrange(0, k + 1), state: State::Scheme, ..initial_machine(State::SchemeStart, new_url()) };
        assert(input.subrange(0, k).push(ascii_lowercase(input[k])) =~= input.subrange(0, k + 1));
        assert(step(input, b, None, m, k) == Step::Next(m2, k));
        lemma_run_next(input, b, m, k, m2, k);
        lemma_run_scheme_lower(input, b, k + 1, se);
    }
}

/// The run from the start over "http://" or "https://".
#[verifier::rlimit(30)]
proof fn lemma_scheme_fast_run(input: Seq<u8>, b: Option<UrlRecord>, se: int)
    requires
        se == 4 || se == 5,
        se + 3 < input.len(),
        input[0] == b'h' && input[1] == b't' && input[2] == b't' && input[3] == b'p',
        se == 5 ==> input[4] == b's',
        input[se] == b':' && input[se + 1] == b'/' && input[se + 2] == b'/',
        input[se + 3] != b'/' && input[se + 3] != b'\\',
    ensures
        run(input, b, None, initial_machine(State::SchemeStart, new_url()), 0) == run(
            input,
            b,
            None,
            fast_authority_machine(input, se),
            se + 3,
        ),
{
    hide(run);
    hide(step);
    let m0 = initial_machine(State::SchemeStart, new_url());
    let sch = input.subrange(0, se);
    if se == 5 {
        assert(sch =~= s_https());
    } else {
        assert(sch =~= s_http());
    }
    assert(is_special_scheme(sch));
    assert(sch != s_file());
    // The scheme start state reads "h", the scheme state the other letters.
    let m1 = Machine { buffer: input.subrange(0, 1), state: State::Scheme, ..m0 };
    assert(Seq::<u8>::empty().push(ascii_lowercase(input[0])) =~= input.subrange(0, 1));
    assert(step(input, b, None, m0, 0) == Step::Next(m1, 0)) by {
        reveal(step);
    }
    lemma_run_next(input, b, m0, 0, m1, 0);
    assert forall|j: int| 0 <= j < se implies is_ascii_lower_alpha(#[trigger] input[j]) by {}
    lemma_run_scheme_lower(input, b, 1, se);
    // ":" sets the scheme, "//" leads to the authority.
    let ms = Machine { buffer: sch, state: State::Scheme, ..m0 };
    let url = UrlRecord { scheme: sch, ..new_url() };
    let mu = Machine { url, buffer: Seq::empty(), ..ms };
    let m_ign = Machine { state: State::SpecialAuthorityIgnoreSlashes, ..mu };
    if b is Some && b->0.scheme == sch {
        let m_sroa = Machine { state: State::SpecialRelativeOrAuthority, ..mu };
        assert(step(input, b, None, ms, se) == Step::Next(m_sroa, se)) by {
        reveal(step);
    }
        lemma_run_next(input, b, ms, se, m_sroa, se);
        assert(step(input, b, None, m_sroa, se + 1) == Step::Next(m_ign, se + 2)) by {
        reveal(step);
    }
        lemma_run_next(input, b, m_sroa, se + 1, m_ign, se + 2);
    } else {
        let m_sas = Machine { state: State::SpecialAuthoritySlashes, ..mu };
        assert(step(input, b, None, ms, se) == Step::Next(m_sas, se)) by {
        reveal(step);
    }
        lemma_run_next(input, b, ms, se, m_sas, se);
        assert(step(input, b, None, m_sas, se + 1) == Step::Next(m_ign, se + 2)) by {
        reveal(step);
    }
        lemma_run_next(input, b, m_sas, se + 1, m_ign, se + 2);
    }
    let ma = Machine { state: State::Authority, ..m_ign };
    assert(step(input, b, None, m_ign, se + 3) == Step::Next(ma, se + 2)) by {
        reveal(step);
    }
    lemma_run_next(input, b, m_ign, se + 3, ma, se + 2);
    assert(ma == fast_authority_machine(input, se));
}

/// "http://" or "https://" followed by a byte other than "/" and "\" (and
/// no base needed): skip the scheme states and go to the authority state.
fn scheme_fast(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::SchemeStart,
        old(ps).p == 0,
        old(ps).gm@ == initial_machine(State::SchemeStart, new_url()),
        base matches Some(b) ==> b.wf(),
    ensures
        !r ==> *final(ps) == *old(ps) && final(cost).n == old(cost).n,
        r ==> {
            &&& final(ps).inv(input@, base_rec(base))
            &&& final(ps).state == State::Authority
            &&& run(input@, base_rec(base), None, old(ps).gm@, 0) == run(
                input@,
                base_rec(base),
                None,
                final(ps).gm@,
                final(ps).p as int,
            )
            &&& final(cost).n + pot(final(ps), input@, base_rec(base)) + 1 <= old(cost).n + pot(
                old(ps),
                input@,
                base_rec(base),
            )
            &&& final(ps).scheme_end == 4 || final(ps).scheme_end == 5
            &&& final(ps).gm@ == fast_authority_machine(input@, final(ps).scheme_end as int)
            &&& (input@.subrange(0, final(ps).scheme_end as int) == s_http() || input@.subrange(
                0,
                final(ps).scheme_end as int,
            ) == s_https())
            &&& final(ps).p == final(ps).scheme_end + 3
            &&& final(ps).p < input.len()
            &&& final(ps).bs == final(ps).p
            &&& final(ps).username_end == final(ps).p
            &&& final(ps).href@ == input@.subrange(0, final(ps).p as int)
            &&& forall|i: int| 0 <= i < final(ps).p ==> input@[i] > 0x20
            &&& final(cost).n == old(cost).n + 8
        },
{
    hide(run);
    hide(step);
    let n = input.len();
    if n < 9 || input[0] != b'h' || input[1] != b't' || input[2] != b't' || input[3] != b'p' {
        return false;
    }
    // Without branches: whether the scheme is "http" or "https" is a coin
    // toss the branch predictor would lose.
    let se: usize = 4 + (input[4] == b's') as usize;
    let p = se + 3;
    let ok = (input[se] == b':') & (input[se + 1] == b'/') & (input[se + 2] == b'/') & (input[p] != b'/') & (
    input[p] != b'\\');
    if !ok {
        return false;
    }
    let ghost b = base_rec(base);
    proof {
        lemma_scheme_fast_run(input@, b, se as int);
        assert(ps.gm@ == initial_machine(State::SchemeStart, new_url()));
    }
    let ghost ps0 = *ps;
    // A fixed-size copy (no memcpy call), cut back for "http://".
    append_range(&mut ps.href, input, 0, 8, Tracked(cost));
    ps.href.truncate(p);
    proof {
        assert(ps.href@ =~= ps0.href@ + input@.subrange(0, p as int));
    }
    ps.scheme_end = se;
    ps.username_end = p;
    ps.special = true;
    ps.bs = p;
    ps.p = p;
    ps.state = State::Authority;
    ps.gm = Ghost(fast_authority_machine(input@, se as int));
    proof {
        let sch = input@.subrange(0, se as int);
        if se == 5 {
            assert(sch =~= s_https());
        } else {
            assert(sch =~= s_http());
        }
        assert(is_special(ps.gm@.url));
        assert(ps.href@ =~= authority_prefix(ps.gm@.url, false));
        assert(input@.subrange(p as int, p as int) =~= ps.gm@.buffer);
        assert(path_ok(ps.gm@.url.path)) by {
            assert(ps.gm@.url.path == new_url().path);
            assert(path_ok(ps0.gm@.url.path));
        }
        assert(ps.inv(input@, b));
        lemma_pot_drop_n(&ps0, ps, input@, b, old(cost).n as int, cost.n as int, 9);
        assert forall|i: int| 0 <= i < p implies input@[i] > 0x20 by {
            if i >= se {
                assert(i == se || i == se + 1 || i == se + 2);
            } else if i == 4 {
                assert(input@[4] == b's');
            }
        }
    }
    true
}

// ---------------------------------------------------------------------------
// The simple absolute fast path
//
// Most URLs are "http://" or "https://", a lowercase domain, and a path,
// query and fragment that need no percent-encoding: the serialization is
// the input itself (with a "/" inserted when the path is empty). For such
// an input the parser below scans each component once and copies the
// input into `href` with one `memcpy`, as ada's `try_parse_simple_absolute`
// does. It runs before the input is trimmed and cleaned of tabs and
// newlines: every byte it accepts is above 0x20, so neither changes the
// input. It is proven to compute the state machine's result.
// ---------------------------------------------------------------------------

/// A byte the fast path accepts in the host: one the authority and host
/// states append to their buffer, and the domain parser keeps as it is.
pub open spec fn simple_host_at(input: Seq<u8>, i: int) -> bool {
    &&& host_plain(input, i, true)
    &&& input[i] != b'@'
    &&& !cls_has(input[i], DOMAIN_SLOW)
}

/// Where the path state starts reading: after the "/" that ends the host.
pub open spec fn simple_p1(input: Seq<u8>, k: int) -> int {
    if k < input.len() && input[k] == b'/' {
        k + 1
    } else {
        k
    }
}

/// What the fast path's scans establish, for the scheme `input[..se]`, the
/// host `input[se + 3..k]`, the path ending at `j`, the query (when
/// `input[j]` is "?") ending at `q`, and the fragment after `q`.
pub open spec fn simple_shape(input: Seq<u8>, se: int, k: int, j: int, q: int) -> bool {
    let n = input.len() as int;
    let p = se + 3;
    let p1 = simple_p1(input, k);
    &&& se == 4 || se == 5
    &&& input.subrange(0, se) == s_http() || input.subrange(0, se) == s_https()
    &&& p < k <= n
    &&& (forall|i: int| p <= i < k ==> #[trigger] simple_host_at(input, i))
    &&& (k < n ==> input[k] == b'/' || input[k] == b'?' || input[k] == b'#')
    &&& !ends_in_a_number(input.subrange(p, k))
    &&& p1 <= j <= n
    &&& (p1 == k ==> j == k)
    &&& (forall|i: int| p1 <= i < j ==> #[trigger] fast_at(input, i, p1))
    &&& (j < n ==> input[j] == b'?' || input[j] == b'#')
    &&& j <= q <= n
    &&& (if j < n && input[j] == b'?' {
        &&& j + 1 <= q
        &&& (forall|i: int| j + 1 <= i < q ==> !in_special_query_set(#[trigger] input[i]))
        &&& (q < n ==> input[q] == b'#')
    } else {
        q == j
    })
    &&& (forall|i: int| q + 1 <= i < n ==> !in_fragment_set(#[trigger] input[i]))
}

/// The URL such an input parses to.
pub open spec fn simple_url(input: Seq<u8>, se: int, k: int, j: int, q: int) -> UrlRecord {
    let n = input.len() as int;
    let p1 = simple_p1(input, k);
    let url_h = UrlRecord {
        host: Some(Host::Domain(input.subrange(se + 3, k))),
        ..UrlRecord { scheme: input.subrange(0, se), ..new_url() }
    };
    let s = input.subrange(p1, j);
    let url4 = push_segment(segs_acc(url_h, Seq::empty(), s), tail_acc(Seq::empty(), s));
    let url5 = if j < n && input[j] == b'?' {
        UrlRecord { query: Some(input.subrange(j + 1, q)), ..url4 }
    } else {
        url4
    };
    if q < n {
        UrlRecord { fragment: Some(input.subrange(q + 1, n)), ..url5 }
    } else {
        url5
    }
}

/// A lowercase ASCII domain without forbidden code points that does not
/// end in a number is its own host.
proof fn lemma_host_simple(s: Seq<u8>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> !cls_has(#[trigger] s[i], DOMAIN_SLOW),
        !ends_in_a_number(s),
    ensures
        host_parse(s, false) == Some(Host::Domain(s)),
{
    lemma_cls();
    assert forall|i: int| 0 <= i < s.len() implies !(#[trigger] s[i] >= 0x80 || is_ascii_upper_alpha(s[i])
        || is_forbidden_domain_code_point(s[i])) by {
        assert(cls_has(s[i], DOMAIN_SLOW) == cls_pred(DOMAIN_SLOW, s[i]));
    }
    assert(no_byte(s, b'%'));
    lemma_percent_decode_identity(s);
    assert(s[0] != b'[');
    assert(is_ascii(s));
    assert(ascii_lowercase_seq(s) =~= s);
    assert(!contains_forbidden_domain_code_point(s));
    assert(domain_parse(s) == Some(s));
}

/// The state machine from the authority state on such an input.
#[verifier::rlimit(100)]
proof fn lemma_simple_run(input: Seq<u8>, b: Option<UrlRecord>, se: int, k: int, j: int, q: int)
    requires
        simple_shape(input, se, k, j, q),
    ensures
        run(input, b, None, fast_authority_machine(input, se), se + 3) == Some(simple_url(input, se, k, j, q)),
{
    hide(run);
    hide(step);
    let n = input.len() as int;
    let p = se + 3;
    let p1 = simple_p1(input, k);
    let m0 = fast_authority_machine(input, se);
    let url0 = m0.url;
    assert(url0.scheme == input.subrange(0, se));
    assert(is_special(url0)) by {
        assert(is_special_scheme(input.subrange(0, se)));
    }
    assert(url0.scheme != s_file()) by {
        assert(url0.scheme[0] == b'h');
        assert(s_file()[0] == b'f');
    }
    // The authority state collects the host and rewinds to its start.
    assert forall|i: int| p <= i < k implies input[i] != b'@' && !is_authority_end(input, i, is_special(m0.url))
        && host_plain(input, i, is_special(m0.url)) by {
        assert(simple_host_at(input, i));
    }
    lemma_run_authority_chars(input, b, m0, p, k);
    let host = input.subrange(p, k);
    let ma = Machine { buffer: m0.buffer + host, ..m0 };
    assert(m0.buffer + host =~= host);
    lemma_step_authority_end(input, b, ma, k);
    let mb = Machine { buffer: Seq::empty(), state: State::Host, ..ma };
    lemma_run_next(input, b, ma, k, mb, p - 1);
    // The host state collects it again and parses it.
    lemma_run_host_chars(input, b, mb, p, k);
    let mc = Machine { buffer: mb.buffer + host, ..mb };
    assert(mb.buffer + host =~= host);
    assert forall|i: int| 0 <= i < host.len() implies !cls_has(#[trigger] host[i], DOMAIN_SLOW) by {
        assert(simple_host_at(input, p + i));
    }
    lemma_host_simple(host);
    lemma_step_host(input, b, mc, k);
    let url_h = UrlRecord { host: Some(Host::Domain(host)), ..url0 };
    let md = Machine { url: url_h, buffer: Seq::empty(), state: State::PathStart, ..mc };
    assert(step(input, b, None, mc, k) == Step::Next(md, k - 1));
    lemma_run_next(input, b, mc, k, md, k - 1);
    // The path start state.
    lemma_step_path_start(input, b, md, k);
    let me = Machine { state: State::Path, ..md };
    if p1 == k + 1 {
        assert(step(input, b, None, md, k) == Step::Next(me, k));
        lemma_run_next(input, b, md, k, me, k);
    } else {
        assert(step(input, b, None, md, k) == Step::Next(me, k - 1));
        lemma_run_next(input, b, md, k, me, k - 1);
    }
    // The path.
    let s = input.subrange(p1, j);
    assert(me.buffer.len() == 0);
    lemma_run_path_fast(input, b, me, p1, p1, j);
    lemma_segs_acc(url_h, Seq::empty(), s);
    let url3 = segs_acc(url_h, Seq::empty(), s);
    let tail = tail_acc(Seq::empty(), s);
    let mf = Machine { url: url3, buffer: tail, ..me };
    assert(mf == Machine { url: segs_acc(me.url, me.buffer, s), buffer: tail_acc(me.buffer, s), ..me });
    lemma_run_path_end(input, b, mf, j);
    lemma_not_dot(tail);
    let url4 = push_segment(url3, tail);
    assert(url3.scheme == url0.scheme);
    assert(path_seg_url(url3, tail, false) == url4);
    let m2 = Machine { url: url4, buffer: Seq::empty(), ..mf };
    let target = simple_url(input, se, k, j, q);
    assert(url_h == UrlRecord {
        host: Some(Host::Domain(input.subrange(se + 3, k))),
        ..UrlRecord { scheme: input.subrange(0, se), ..new_url() }
    });
    if j == n {
        assert(target == url4);
    } else if input[j] == b'?' {
        // The query.
        let mq = Machine { state: State::Query, url: UrlRecord { query: Some(Seq::empty()), ..url4 }, ..m2 };
        assert forall|i: int| j + 1 <= i < q implies input[i] != b'#' by {
            assert(!in_special_query_set(input[i]));
        }
        lemma_run_query_chars(input, b, mq, j + 1, q);
        let qs = input.subrange(j + 1, q);
        let mq2 = Machine { buffer: mq.buffer + qs, ..mq };
        assert(mq.buffer + qs =~= qs);
        lemma_run_query_end(input, b, mq2, q);
        assert forall|i: int| 0 <= i < qs.len() implies !in_encode_set(EncodeSet::SpecialQuery, #[trigger] qs[i]) by {
            assert(!in_special_query_set(input[j + 1 + i]));
        }
        lemma_pe_seq_identity(qs, EncodeSet::SpecialQuery);
        assert(Seq::<u8>::empty() + qs =~= qs);
        let url5 = UrlRecord { query: Some(qs), ..url4 };
        assert(UrlRecord { query: Some(mq2.url.query->0 + pe_seq(mq2.buffer, EncodeSet::SpecialQuery)), ..mq2.url } == url5);
        if q == n {
            assert(target == url5);
        } else {
            // The fragment.
            let mr = Machine {
                url: UrlRecord { fragment: Some(Seq::empty()), ..url5 },
                buffer: Seq::empty(),
                state: State::Fragment,
                ..mq2
            };
            lemma_run_fragment(input, b, mr, q + 1, Seq::empty());
            let fs = input.subrange(q + 1, n);
            assert forall|i: int| 0 <= i < fs.len() implies !in_encode_set(EncodeSet::Fragment, #[trigger] fs[i]) by {
                assert(!in_fragment_set(input[q + 1 + i]));
            }
            lemma_pe_seq_identity(fs, EncodeSet::Fragment);
            assert(Seq::<u8>::empty() + fs =~= fs);
            assert(target == UrlRecord { fragment: Some(fs), ..url5 });
        }
    } else {
        // The fragment, after an empty query-less path.
        assert(q == j);
        let mr = Machine { state: State::Fragment, url: UrlRecord { fragment: Some(Seq::empty()), ..url4 }, ..m2 };
        lemma_run_fragment(input, b, mr, j + 1, Seq::empty());
        let fs = input.subrange(j + 1, n);
        assert forall|i: int| 0 <= i < fs.len() implies !in_encode_set(EncodeSet::Fragment, #[trigger] fs[i]) by {
            assert(!in_fragment_set(input[j + 1 + i]));
        }
        lemma_pe_seq_identity(fs, EncodeSet::Fragment);
        assert(Seq::<u8>::empty() + fs =~= fs);
        assert(target == UrlRecord { fragment: Some(fs), ..url4 });
    }
}

/// The pieces of such a URL's serialization.
#[verifier::rlimit(60)]
proof fn lemma_simple_parts(input: Seq<u8>, se: int, k: int, j: int, q: int)
    requires
        simple_shape(input, se, k, j, q),
    ensures
        ({
            let url = simple_url(input, se, k, j, q);
            let n = input.len() as int;
            let slash = k < n && input[k] == b'/';
            &&& url.scheme == input.subrange(0, se)
            &&& url.username.len() == 0
            &&& url.password.len() == 0
            &&& url.host == Some(Host::Domain(input.subrange(se + 3, k)))
            &&& url.port is None
            &&& url.path is List
            &&& path_ok(url.path)
            &&& path_serialize(url.path) == (if slash {
                input.subrange(k, j)
            } else {
                seq![b'/']
            })
            &&& (url.query is Some) == (j < n && input[j] == b'?')
            &&& query_serialize(url) == (if j < n && input[j] == b'?' {
                input.subrange(j, q)
            } else {
                Seq::<u8>::empty()
            })
            &&& (url.fragment is Some) == (q < n)
            &&& fragment_serialize(url) == (if q < n {
                input.subrange(q, n)
            } else {
                Seq::<u8>::empty()
            })
        }),
{
    let n = input.len() as int;
    let p1 = simple_p1(input, k);
    let url_h = UrlRecord {
        host: Some(Host::Domain(input.subrange(se + 3, k))),
        ..UrlRecord { scheme: input.subrange(0, se), ..new_url() }
    };
    let s = input.subrange(p1, j);
    assert(segments_ok(Seq::<Seq<u8>>::empty()));
    lemma_segs_acc(url_h, Seq::empty(), s);
    let url3 = segs_acc(url_h, Seq::empty(), s);
    let tail = tail_acc(Seq::empty(), s);
    let segs = url3.path->List_0;
    lemma_segments_push(segs, tail);
    lemma_segments_ok_push(segs, tail);
    assert(segments_serialize(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
    assert(segments_serialize(segs.push(tail)) =~= seq![b'/'] + s);
    if k < n && input[k] == b'/' {
        assert(p1 == k + 1);
        assert(input.subrange(k, j) =~= seq![input[k]] + input.subrange(k + 1, j));
        assert(seq![b'/'] + s =~= input.subrange(k, j));
    } else {
        assert(s =~= Seq::<u8>::empty());
        assert(seq![b'/'] + s =~= seq![b'/']);
    }
    let url = simple_url(input, se, k, j, q);
    if j < n && input[j] == b'?' {
        assert(seq![b'?'] + input.subrange(j + 1, q) =~= input.subrange(j, q));
    }
    if q < n {
        assert(input[q] == b'#');
        assert(seq![b'#'] + input.subrange(q + 1, n) =~= input.subrange(q, n));
    }
}

/// Every byte of such an input is above 0x20 (so trimming and removing
/// tabs and newlines leave it as it is).
proof fn lemma_simple_printable(input: Seq<u8>, se: int, k: int, j: int, q: int)
    requires
        simple_shape(input, se, k, j, q),
        forall|i: int| 0 <= i < se + 3 ==> input[i] > 0x20,
    ensures
        forall|i: int| 0 <= i < input.len() ==> input[i] > 0x20,
{
    let n = input.len() as int;
    let p1 = simple_p1(input, k);
    lemma_cls();
    assert forall|i: int| 0 <= i < n implies input[i] > 0x20 by {
        if i < se + 3 {
        } else if i < k {
            assert(simple_host_at(input, i));
            assert(cls_has(input[i], DOMAIN_SLOW) == cls_pred(DOMAIN_SLOW, input[i]));
        } else if i == k {
        } else if i >= p1 && i < j {
            assert(fast_at(input, i, p1));
        } else if i == j {
        } else if i < q {
            assert(!in_special_query_set(input[i]));
        } else if i == q {
        } else {
            assert(!in_fragment_set(input[i]));
        }
    }
}

/// The href the fast path writes is the serialization, and its offsets
/// are the URL's.
#[verifier::rlimit(40)]
proof fn lemma_simple_href(input: Seq<u8>, se: int, k: int, j: int, q: int, h0: Seq<u8>, href: Seq<u8>)
    requires
        simple_shape(input, se, k, j, q),
        h0 == input.subrange(0, se + 3),
        h0 == input.subrange(0, se) + seq![b':', b'/', b'/'],
        href == (if k < input.len() && input[k] == b'/' {
            h0 + input.subrange(se + 3, input.len() as int)
        } else {
            h0 + input.subrange(se + 3, k) + seq![b'/'] + input.subrange(k, input.len() as int)
        }),
    ensures
        ({
            let url = simple_url(input, se, k, j, q);
            let n = input.len() as int;
            let d: int = if k < n && input[k] == b'/' { 0 } else { 1 };
            &&& href == core_serialize(url)
            &&& o_username_end(url) == se + 3
            &&& o_host_start(url) == se + 3
            &&& o_host_end(url) == k
            &&& o_path_start(url) == k
            &&& o_query_start(url) == j + d
            &&& o_fragment_start(url) == q + d
            &&& url.port is None
            &&& url.path is List
            &&& path_ok(url.path)
            &&& (url.query is Some) == (j < n && input[j] == b'?')
            &&& (url.fragment is Some) == (q < n)
            &&& url.scheme == input.subrange(0, se)
            &&& url.host == Some(Host::Domain(input.subrange(se + 3, k)))
        }),
{
    lemma_simple_parts(input, se, k, j, q);
    let url = simple_url(input, se, k, j, q);
    let n = input.len() as int;
    let p = se + 3;
    let host = input.subrange(p, k);
    assert(credentials_serialize(url) =~= Seq::<u8>::empty());
    assert(port_serialize(url) =~= Seq::<u8>::empty());
    let auth = seq![b'/', b'/'] + host;
    assert(authority_serialize(url) =~= auth);
    let pre = url.scheme + seq![b':'] + authority_serialize(url);
    assert(h0 =~= url.scheme + seq![b':', b'/', b'/']);
    assert(pre =~= h0 + host);
    assert(pre =~= input.subrange(0, k));
    let tl = path_serialize(url.path) + query_serialize(url) + fragment_serialize(url);
    if !(j < n && input[j] == b'?') {
        assert(input.subrange(j, q) =~= Seq::<u8>::empty());
    }
    assert(query_serialize(url) == input.subrange(j, q));
    if q == n {
        assert(input.subrange(q, n) =~= Seq::<u8>::empty());
    }
    assert(fragment_serialize(url) == input.subrange(q, n));
    assert(input.subrange(j, n) =~= input.subrange(j, q) + input.subrange(q, n));
    if k < n && input[k] == b'/' {
        assert(input.subrange(k, n) =~= input.subrange(k, j) + input.subrange(j, n));
        assert(tl =~= input.subrange(k, n));
        assert(href =~= input.subrange(0, k) + input.subrange(k, n));
    } else {
        assert(j == k);
        assert(query_serialize(url) + fragment_serialize(url) =~= input.subrange(k, n));
        assert(href =~= input.subrange(0, k) + seq![b'/'] + input.subrange(k, n));
    }
    assert(core_serialize(url) =~= pre + tl);
}

/// Finishes an "http://" or "https://" URL in the authority state (as
/// `scheme_fast` leaves it) when it has the simple shape: scans the host,
/// path, query and fragment, then copies the rest of the input into `href`
/// in one go. Leaves `ps` as it was otherwise.
#[verifier::rlimit(150)]
fn simple_rest(ps: &mut Parser, input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: bool)
    requires
        old(ps).inv(input@, base_rec(base)),
        old(ps).state == State::Authority,
        old(ps).scheme_end == 4 || old(ps).scheme_end == 5,
        old(ps).gm@ == fast_authority_machine(input@, old(ps).scheme_end as int),
        input@.subrange(0, old(ps).scheme_end as int) == s_http() || input@.subrange(
            0,
            old(ps).scheme_end as int,
        ) == s_https(),
        old(ps).p == old(ps).scheme_end + 3,
        old(ps).p < input.len(),
        old(ps).username_end == old(ps).p,
        old(ps).href@ == input@.subrange(0, old(ps).p as int),
        forall|i: int| 0 <= i < old(ps).p ==> input@[i] > 0x20,
    ensures
        !r ==> *final(ps) == *old(ps),
        final(cost).n <= old(cost).n + 12 * input.len() + 64,
        r ==> done_ok(final(ps), final(ps).gm@.url),
        r ==> run(input@, base_rec(base), None, old(ps).gm@, old(ps).p as int) == Some(final(ps).gm@.url),
        r ==> forall|i: int| 0 <= i < input.len() ==> input@[i] > 0x20,
        r ==> final(ps).href@.len() <= input.len() + 1,
{
    let ghost b = base_rec(base);
    let ghost c0 = cost.n;
    let ghost se = ps.scheme_end as int;
    let n = input.len();
    let p = ps.p;
    // The host: a run of lowercase domain bytes, up to the end, "/", "?"
    // or "#" (a port, credentials or anything to map go the long way).
    proof {
        crate::swar::lemma_plain_free_masks();
    }
    let k = crate::swar::find_cls_plain(input, p, n, AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW, Tracked(cost));
    if k == p || (k < n && input[k] != b'/' && input[k] != b'?' && input[k] != b'#') {
        return false;
    }
    proof {
        lemma_cls();
        assert forall|i: int| p <= i < k implies #[trigger] simple_host_at(input@, i) by {
            let x = CLS@[input@[i] as int];
            lemma_and_or(x, AUTHORITY_STOP, BACKSLASH);
            lemma_and_or(x, AUTHORITY_STOP | BACKSLASH, HOST_STOP);
            lemma_and_or(x, AUTHORITY_STOP | BACKSLASH | HOST_STOP, DOMAIN_SLOW);
            assert(!cls_has(input@[i], AUTHORITY_STOP | BACKSLASH | HOST_STOP | DOMAIN_SLOW));
            assert(cls_has(input@[i], AUTHORITY_STOP) == cls_pred(AUTHORITY_STOP, input@[i]));
            assert(cls_has(input@[i], BACKSLASH) == cls_pred(BACKSLASH, input@[i]));
            assert(cls_has(input@[i], HOST_STOP) == cls_pred(HOST_STOP, input@[i]));
        }
    }
    let ghost c1 = cost.n;
    if ends_in_a_number_exec(vstd::slice::slice_subrange(input, p, k), Tracked(cost)) {
        return false;
    }
    let ghost c2 = cost.n;
    // The path: plain bytes, no "\" and no dot segment.
    let slash = k < n && input[k] == b'/';
    let p1 = if slash {
        k + 1
    } else {
        k
    };
    let j = if slash && p1 < n {
        path_fast_scan(input, p1, Tracked(cost))
    } else {
        p1
    };
    if j < n && input[j] != b'?' && input[j] != b'#' {
        return false;
    }
    let ghost c3 = cost.n;
    // The query and the fragment: bytes that need no encoding.
    let has_q = j < n && input[j] == b'?';
    let q = if has_q {
        scan_special_query(input, j + 1, n, Tracked(cost))
    } else {
        j
    };
    if q < n && input[q] != b'#' {
        return false;
    }
    let ghost c4 = cost.n;
    if q < n {
        let f = scan_fragment(input, q + 1, n, Tracked(cost));
        if f < n {
            return false;
        }
    }
    let ghost c5 = cost.n;
    proof {
        assert(c1 == c0 + (k - p) + 1);
        assert(c2 <= c1 + 3 * (k - p) + 1);
        assert(c3 <= c2 + 2 * (j - p1) + 18);
        assert(c4 <= c3 + 2 * (q - j) + 18);
        assert(c5 <= c4 + (n - q) + 1);
        assert(simple_shape(input@, se, k as int, j as int, q as int));
        lemma_simple_run(input@, b, se, k as int, j as int, q as int);
        lemma_simple_parts(input@, se, k as int, j as int, q as int);
        lemma_simple_printable(input@, se, k as int, j as int, q as int);
    }
    // The serialization is the input, with a "/" for an empty path.
    let ghost url = simple_url(input@, se, k as int, j as int, q as int);
    let ghost h0 = ps.href@;
    if slash {
        append_range(&mut ps.href, input, p, n, Tracked(cost));
    } else {
        append_range(&mut ps.href, input, p, k, Tracked(cost));
        ps.href.push(b'/');
        append_range(&mut ps.href, input, k, n, Tracked(cost));
    }
    let d: usize = if slash {
        0
    } else {
        1
    };
    ps.host_start = p;
    ps.host_end = k;
    ps.host_kind = Some(HostKind::Domain);
    ps.port = None;
    ps.path_start = k;
    ps.opaque_path = false;
    ps.query_start = if has_q {
        Some(j + d)
    } else {
        None
    };
    ps.fragment_start = if q < n {
        Some(q + d)
    } else {
        None
    };
    ps.gm = Ghost(Machine { url, ..ps.gm@ });
    proof {
        let url0 = old(ps).gm@.url;
        assert(h0 =~= url0.scheme + seq![b':', b'/', b'/']);
        if slash {
            assert(ps.href@ =~= h0 + input@.subrange(p as int, n as int));
        } else {
            assert(ps.href@ =~= h0 + input@.subrange(p as int, k as int) + seq![b'/'] + input@.subrange(k as int, n as int));
        }
        lemma_simple_href(input@, se, k as int, j as int, q as int, h0, ps.href@);
        assert(kind_of(Host::Domain(input@.subrange(p as int, k as int))) == HostKind::Domain);
    }
    true
}

/// The work bound of `parse_simple` for an `n`-byte input.
pub open spec fn simple_cost(n: nat) -> int {
    16 * (n as int) + 128
}

/// The fast path for an "http://" or "https://" URL already in canonical
/// form, on the input as given (before trimming and removing tabs and
/// newlines, which cannot change an input it accepts). `None` means it did
/// not apply, not that the input is invalid.
pub(crate) fn parse_simple(input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.wf(),
    ensures
        final(cost).n <= old(cost).n + simple_cost(input.len() as nat),
        r matches Some(u) ==> u.wf() && run(
            input@,
            base_rec(base),
            None,
            initial_machine(State::SchemeStart, new_url()),
            0,
        ) == Some(u@),
        r is Some ==> input.len() > 0 && forall|i: int| 0 <= i < input.len() ==> input@[i] > 0x20,
{
    let n = input.len();
    if n < 9 || input[0] != b'h' {
        return None;
    }
    let ghost b = base_rec(base);
    // The same buffer the state machine would take, so that it can take it
    // back when this does not apply.
    let need = n.saturating_add(8);
    let c = crate::host::capacity(&sc.href);
    let mut href: Vec<u8> = Vec::new();
    if c >= need && c / 2 <= need {
        core::mem::swap(&mut href, &mut sc.href);
        href.clear();
    } else {
        href = Vec::with_capacity(need);
    }
    let mut ps = Parser {
        href,
        p: 0,
        state: State::SchemeStart,
        bs: 0,
        at_sign_seen: false,
        inside_brackets: false,
        pts: false,
        special: false,
        scheme_end: 0,
        username_end: 0,
        host_start: 0,
        host_end: 0,
        port: None,
        path_start: 0,
        query_start: None,
        fragment_start: None,
        host_kind: None,
        opaque_path: false,
        gm: Ghost(initial_machine(State::SchemeStart, new_url())),
    };
    proof {
        assert(!is_special_scheme(Seq::<u8>::empty())) by {
            assert(Seq::<u8>::empty() != s_ftp() && Seq::<u8>::empty() != s_file());
            assert(Seq::<u8>::empty().len() != s_http().len());
            assert(Seq::<u8>::empty().len() != s_https().len());
            assert(Seq::<u8>::empty().len() != s_ws().len());
            assert(Seq::<u8>::empty().len() != s_wss().len());
        }
    }
    if !scheme_fast(&mut ps, input, base, Tracked(cost)) {
        sc.href = ps.href;
        return None;
    }
    let ghost m = ps.gm@;
    let ghost p = ps.p;
    if !simple_rest(&mut ps, input, base, Tracked(cost)) {
        sc.href = ps.href;
        return None;
    }
    proof {
        assert(ps.href@.len() <= n + 1);
    }
    Some(finish(ps, Tracked(cost)))
}

/// Runs the state machine on `input` (already trimmed and without tabs and
/// newlines).
/// The state machine's work bound for an `n`-byte input and an `m`-byte
/// base: the potential of the start state.
pub open spec fn machine_cost(n: nat, m: nat) -> int {
    20 * (COST_W * (n + m + 2)) + COST_W * n
}

pub(crate) fn run_machine(input: &[u8], base: Option<&Url>, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.wf(),
    ensures
        final(cost).n <= old(cost).n + machine_cost(input.len() as nat, base_len(base_rec(base))),
        r matches Some(u) ==> u.wf() && run(
            input@,
            base_rec(base),
            None,
            initial_machine(State::SchemeStart, new_url()),
            0,
        ) == Some(u@),
        r is None ==> run(
            input@,
            base_rec(base),
            None,
            initial_machine(State::SchemeStart, new_url()),
            0,
        ) is None,
{
    run_machine_in(input, base, &mut crate::host::Scratch::new(), Tracked(cost))
}

/// `run_machine` with scratch storage kept by the caller: the href is
/// written into `sc.href` when that has room (else into a new buffer), and
/// on failure the buffer is left there for reuse.
pub(crate) fn run_machine_in(input: &[u8], base: Option<&Url>, sc: &mut crate::host::Scratch, Tracked(cost): Tracked<&mut Meter>) -> (r: Option<Url>)
    requires
        base matches Some(b) ==> b.wf(),
    ensures
        final(cost).n <= old(cost).n + machine_cost(input.len() as nat, base_len(base_rec(base))),
        r matches Some(u) ==> u.wf() && run(
            input@,
            base_rec(base),
            None,
            initial_machine(State::SchemeStart, new_url()),
            0,
        ) == Some(u@),
        r is None ==> run(
            input@,
            base_rec(base),
            None,
            initial_machine(State::SchemeStart, new_url()),
            0,
        ) is None,
{
    let ghost b = base_rec(base);
    let ghost target = run(input@, b, None, initial_machine(State::SchemeStart, new_url()), 0);
    // Take the spare buffer when it has room but is not much bigger than
    // needed (the URL may keep it).
    let need = input.len().saturating_add(8);
    let c = crate::host::capacity(&sc.href);
    let mut href: Vec<u8> = Vec::new();
    if c >= need && c / 2 <= need {
        core::mem::swap(&mut href, &mut sc.href);
        href.clear();
    } else {
        href = Vec::with_capacity(need);
    }
    let mut ps = Parser {
        href,
        p: 0,
        state: State::SchemeStart,
        bs: 0,
        at_sign_seen: false,
        inside_brackets: false,
        pts: false,
        special: false,
        scheme_end: 0,
        username_end: 0,
        host_start: 0,
        host_end: 0,
        port: None,
        path_start: 0,
        query_start: None,
        fragment_start: None,
        host_kind: None,
        opaque_path: false,
        gm: Ghost(initial_machine(State::SchemeStart, new_url())),
    };
    proof {
        assert(!is_special_scheme(Seq::<u8>::empty())) by {
            assert(Seq::<u8>::empty() != s_ftp() && Seq::<u8>::empty() != s_file());
            assert(Seq::<u8>::empty().len() != s_http().len());
            assert(Seq::<u8>::empty().len() != s_https().len());
            assert(Seq::<u8>::empty().len() != s_ws().len());
            assert(Seq::<u8>::empty().len() != s_wss().len());
        }
    }
    proof {
        assert(pot(&ps, input@, b) == machine_cost(input.len() as nat, base_len(b)));
    }
    if scheme_fast(&mut ps, input, base, Tracked(cost)) {
    }
    loop
        invariant
            base matches Some(bb) ==> bb.wf(),
            b == base_rec(base),
            ps.inv(input@, b),
            target == run(input@, b, None, ps.gm@, ps.p as int),
            target == run(input@, b, None, initial_machine(State::SchemeStart, new_url()), 0),
            cost.n + pot(&ps, input@, b) <= old(cost).n + machine_cost(input.len() as nat, base_len(b)),
        decreases phase(ps.state), input@.len() - ps.p, rank(ps.state),
    {
        let ghost before = ps;
        proof {
            cost.n = cost.n + 1;
        }
        match handle(&mut ps, input, base, sc, Tracked(cost)) {
            Flow::Continue => {},
            Flow::Done => {
                return Some(finish(ps, Tracked(cost)));
            },
            Flow::Fail => {
                if crate::host::capacity(&ps.href) <= 4096 {
                    sc.href = ps.href;
                }
                return None;
            },
        }
    }
}

/// Builds the URL: inserts "/." before a path that would otherwise read as
/// an authority, and shifts the later offsets.
#[verifier::rlimit(50)]
fn finish(ps: Parser, Tracked(cost): Tracked<&mut Meter>) -> (u: Url)
    requires
        done_ok(&ps, ps.gm@.url),
    ensures
        final(cost).n <= old(cost).n + ps.href@.len(),
        u.wf(),
        u@ == ps.gm@.url,
{
    let ghost url = ps.gm@.url;
    let n = ps.href.len();
    let a = ps.path_start;
    proof {
        lemma_core_parts(url);
    }
    let path_end = match ps.query_start {
        Some(q) => q,
        None => match ps.fragment_start {
            Some(f) => f,
            None => n,
        },
    };
    proof {
        let s = ps.href@.subrange(a as int, path_end as int);
        assert(s == path_serialize(url.path));
        if !ps.opaque_path {
            lemma_segments_dot(url.path->List_0);
        }
        if path_end - a >= 2 {
            assert(s[0] == ps.href@[a as int]);
            assert(s[1] == ps.href@[a + 1]);
        }
    }
    let dot = ps.host_kind.is_none() && !ps.opaque_path && path_end - a >= 2 && ps.href[a] == b'/'
        && ps.href[a + 1] == b'/';
    proof {
        assert(dot == needs_dot_slash(url));
    }
    if !dot {
        proof {
            assert(ps.href@ =~= serialize(url, false));
        }
        return Url {
            href: ps.href,
            scheme_end: ps.scheme_end,
            username_end: ps.username_end,
            host_start: ps.host_start,
            host_end: ps.host_end,
            port: ps.port,
            path_start: ps.path_start,
            query_start: ps.query_start,
            fragment_start: ps.fragment_start,
            host_kind: ps.host_kind,
            opaque_path: ps.opaque_path,
            special: ps.special,
            has_dot: false,
            rec: Ghost(url),
        };
    }
    let mut href: Vec<u8> = Vec::with_capacity(n);
    append_range(&mut href, ps.href.as_slice(), 0, a, Tracked(cost));
    href.push(b'/');
    href.push(b'.');
    append_range(&mut href, ps.href.as_slice(), a, n, Tracked(cost));
    let total = href.len();
    proof {
        assert(total == n + 2);
        assert(href@ =~= serialize(url, false));
    }
    Url {
        href,
        scheme_end: ps.scheme_end,
        username_end: ps.username_end,
        host_start: ps.host_start,
        host_end: ps.host_end,
        port: ps.port,
        path_start: a + 2,
        query_start: match ps.query_start {
            Some(q) => Some(q + 2),
            None => None,
        },
        fragment_start: match ps.fragment_start {
            Some(f) => Some(f + 2),
            None => None,
        },
        host_kind: ps.host_kind,
        opaque_path: ps.opaque_path,
        special: ps.special,
        has_dot: true,
        rec: Ghost(url),
    }
}

} // verus!
