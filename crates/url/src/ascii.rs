//! Every URL the parser returns serializes to ASCII.
//!
//! The Standard percent-encodes every non-ASCII byte that reaches a URL
//! component, and the host parser only returns ASCII hosts. This file
//! proves that over the spec state machine (`lemma_parse_url_ascii`), so the
//! getters can hand out `href` as a `&str` without checking it again.
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// ASCII components
// ---------------------------------------------------------------------------

pub open spec fn segs_ascii(segs: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < segs.len() ==> is_ascii(#[trigger] segs[i])
}

pub open spec fn path_ascii(p: UrlPath) -> bool {
    match p {
        UrlPath::Opaque(s) => is_ascii(s),
        UrlPath::List(segs) => segs_ascii(segs),
    }
}

pub open spec fn opt_ascii(o: Option<Seq<u8>>) -> bool {
    match o {
        Some(s) => is_ascii(s),
        None => true,
    }
}

pub open spec fn host_ascii(h: Option<Host>) -> bool {
    match h {
        Some(h) => is_ascii(host_serialize(h)),
        None => true,
    }
}

/// Every component of `u` is ASCII.
pub open spec fn url_ascii(u: UrlRecord) -> bool {
    &&& is_ascii(u.scheme)
    &&& is_ascii(u.username)
    &&& is_ascii(u.password)
    &&& host_ascii(u.host)
    &&& path_ascii(u.path)
    &&& opt_ascii(u.query)
    &&& opt_ascii(u.fragment)
}

pub open spec fn base_ascii(base: Option<UrlRecord>) -> bool {
    match base {
        Some(b) => url_ascii(b),
        None => true,
    }
}

/// The machine invariant: the URL is ASCII, and so is the buffer, except in
/// the states that collect raw input for the host parser, the port or the
/// query (which encodes its buffer when it ends).
pub open spec fn machine_ascii(m: Machine) -> bool {
    &&& url_ascii(m.url)
    &&& !(m.state == State::Authority || m.state == State::Host || m.state == State::Hostname
        || m.state == State::Port || m.state == State::FileHost || m.state == State::Query)
        ==> is_ascii(m.buffer)
}

// ---------------------------------------------------------------------------
// Sequences
// ---------------------------------------------------------------------------

pub broadcast proof fn lemma_ascii_add(a: Seq<u8>, b: Seq<u8>)
    ensures
        #[trigger] is_ascii(a + b) == (is_ascii(a) && is_ascii(b)),
{
    if is_ascii(a) && is_ascii(b) {
        assert forall|i: int| 0 <= i < (a + b).len() implies (a + b)[i] < 0x80 by {
            if i >= a.len() {
                assert((a + b)[i] == b[i - a.len()]);
            }
        }
    }
    if is_ascii(a + b) {
        assert forall|i: int| 0 <= i < a.len() implies a[i] < 0x80 by {
            assert((a + b)[i] == a[i]);
        }
        assert forall|i: int| 0 <= i < b.len() implies b[i] < 0x80 by {
            assert((a + b)[i + a.len()] == b[i]);
        }
    }
}

pub broadcast proof fn lemma_ascii_push(a: Seq<u8>, c: u8)
    ensures
        #[trigger] is_ascii(a.push(c)) == (is_ascii(a) && c < 0x80),
{
    if is_ascii(a) && c < 0x80 {
        assert forall|i: int| 0 <= i < a.push(c).len() implies a.push(c)[i] < 0x80 by {
            if i < a.len() {
                assert(a.push(c)[i] == a[i]);
            }
        }
    }
    if is_ascii(a.push(c)) {
        assert(a.push(c)[a.len() as int] == c);
        assert forall|i: int| 0 <= i < a.len() implies a[i] < 0x80 by {
            assert(a.push(c)[i] == a[i]);
        }
    }
}

pub broadcast proof fn lemma_ascii_empty()
    ensures
        #[trigger] is_ascii(Seq::<u8>::empty()),
{
}

pub broadcast proof fn lemma_ascii_skip(a: Seq<u8>, k: int)
    requires
        is_ascii(a),
        0 <= k <= a.len(),
    ensures
        #[trigger] is_ascii(a.skip(k)),
{
    assert forall|i: int| 0 <= i < a.skip(k).len() implies a.skip(k)[i] < 0x80 by {
        assert(a.skip(k)[i] == a[i + k]);
    }
}

pub broadcast proof fn lemma_ascii_update(a: Seq<u8>, k: int, c: u8)
    requires
        is_ascii(a),
        c < 0x80,
    ensures
        #[trigger] is_ascii(a.update(k, c)),
{
}

pub broadcast proof fn lemma_ascii_lowercase_seq(a: Seq<u8>)
    requires
        is_ascii(a),
    ensures
        #[trigger] is_ascii(ascii_lowercase_seq(a)),
{
    assert forall|i: int| 0 <= i < ascii_lowercase_seq(a).len() implies ascii_lowercase_seq(a)[i]
        < 0x80 by {
        assert(ascii_lowercase_seq(a)[i] == ascii_lowercase(a[i]));
    }
}

pub broadcast proof fn lemma_pe_ascii(c: u8, set: EncodeSet)
    ensures
        #[trigger] is_ascii(pe(c, set)),
{
    if in_encode_set(set, c) {
        let e = percent_encode_byte(c);
        assert(e[0] == b'%');
        assert(c / 16 < 16 && c % 16 < 16);
        assert(e[1] < 0x80 && e[2] < 0x80);
    } else {
        assert(c <= 0x7E);
        assert(pe(c, set)[0] == c);
    }
}

pub broadcast proof fn lemma_pe_seq_ascii(s: Seq<u8>, set: EncodeSet)
    ensures
        #[trigger] is_ascii(pe_seq(s, set)),
    decreases s.len(),
{
    broadcast use lemma_ascii_add, lemma_pe_ascii, lemma_ascii_empty;

    if s.len() > 0 {
        lemma_pe_seq_ascii(s.drop_last(), set);
    }
}

// ---------------------------------------------------------------------------
// Serializers
// ---------------------------------------------------------------------------

pub broadcast proof fn lemma_decimal_ascii(n: nat)
    ensures
        #[trigger] is_ascii(decimal(n)),
    decreases n,
{
    broadcast use lemma_ascii_add;

    if n >= 10 {
        lemma_decimal_ascii(n / 10);
        assert(is_ascii(seq![(b'0' + n % 10) as u8]));
    } else {
        assert(is_ascii(seq![(b'0' + n) as u8]));
    }
}

pub proof fn lemma_lower_hex_ascii(n: nat)
    ensures
        is_ascii(lower_hex(n)),
    decreases n,
{
    broadcast use lemma_ascii_add;

    if n >= 16 {
        lemma_lower_hex_ascii(n / 16);
        assert(is_ascii(seq![lower_hex_digit(n % 16)]));
    } else {
        assert(is_ascii(seq![lower_hex_digit(n)]));
    }
}

proof fn lemma_ipv6_serialize_from_ascii(pieces: Seq<u16>, i: int, compress: Option<int>, ignore0: bool)
    ensures
        is_ascii(ipv6_serialize_from(pieces, i, compress, ignore0)),
    decreases 8 - i,
{
    broadcast use lemma_ascii_add, lemma_ascii_empty;

    if i < 8 {
        if ignore0 && pieces[i] == 0 {
            lemma_ipv6_serialize_from_ascii(pieces, i + 1, compress, true);
        } else if compress == Some(i) {
            lemma_ipv6_serialize_from_ascii(pieces, i + 1, compress, true);
            assert(is_ascii(seq![b':', b':']));
            assert(is_ascii(seq![b':']));
        } else {
            lemma_ipv6_serialize_from_ascii(pieces, i + 1, compress, false);
            lemma_lower_hex_ascii(pieces[i] as nat);
            assert(is_ascii(seq![b':']));
        }
    }
}

pub proof fn lemma_host_serialize_ascii(h: Host)
    requires
        h matches Host::Domain(s) ==> is_ascii(s),
        h matches Host::Opaque(s) ==> is_ascii(s),
    ensures
        is_ascii(host_serialize(h)),
{
    broadcast use lemma_ascii_add, lemma_decimal_ascii, lemma_ascii_empty;

    match h {
        Host::Ipv4(a) => {
            assert(is_ascii(seq![b'.']));
        },
        Host::Ipv6(a) => {
            lemma_ipv6_serialize_from_ascii(a, 0, ipv6_compress(a), false);
            assert(is_ascii(seq![b'[']));
            assert(is_ascii(seq![b']']));
        },
        _ => {},
    }
}

pub broadcast proof fn lemma_host_parse_ascii(s: Seq<u8>, is_opaque: bool)
    ensures
        #[trigger] host_parse(s, is_opaque) matches Some(h) ==> is_ascii(host_serialize(h)),
{
    broadcast use lemma_pe_seq_ascii, lemma_ascii_lowercase_seq;

    if let Some(h) = host_parse(s, is_opaque) {
        lemma_host_serialize_ascii(h);
    }
}

pub broadcast proof fn lemma_append_userinfo_ascii(buf: Seq<u8>, username: Seq<u8>, password: Seq<u8>, pts: bool)
    requires
        is_ascii(username),
        is_ascii(password),
    ensures
        is_ascii((#[trigger] append_userinfo(buf, username, password, pts)).0),
        is_ascii(append_userinfo(buf, username, password, pts).1),
    decreases buf.len(),
{
    broadcast use lemma_ascii_add, lemma_pe_ascii;

    if buf.len() > 0 {
        if buf[0] == b':' && !pts {
            lemma_append_userinfo_ascii(buf.skip(1), username, password, true);
        } else {
            let e = pe(buf[0], EncodeSet::Userinfo);
            if pts {
                lemma_append_userinfo_ascii(buf.skip(1), username, password + e, pts);
            } else {
                lemma_append_userinfo_ascii(buf.skip(1), username + e, password, pts);
            }
        }
    }
}

pub broadcast proof fn lemma_segments_serialize_ascii(segs: Seq<Seq<u8>>)
    ensures
        #[trigger] is_ascii(segments_serialize(segs)) == segs_ascii(segs),
    decreases segs.len(),
{
    broadcast use lemma_ascii_add, lemma_ascii_empty;

    if segs.len() > 0 {
        lemma_segments_serialize_ascii(segs.drop_last());
        assert(is_ascii(seq![b'/']));
        if segs_ascii(segs) {
            assert(segs_ascii(segs.drop_last())) by {
                assert forall|i: int| 0 <= i < segs.drop_last().len() implies is_ascii(
                    #[trigger] segs.drop_last()[i],
                ) by {
                    assert(segs.drop_last()[i] == segs[i]);
                }
            }
            assert(is_ascii(segs.last())) by {
                assert(segs.last() == segs[segs.len() - 1]);
            }
        }
        if segs_ascii(segs.drop_last()) && is_ascii(segs.last()) {
            assert forall|i: int| 0 <= i < segs.len() implies is_ascii(#[trigger] segs[i]) by {
                if i < segs.len() - 1 {
                    assert(segs.drop_last()[i] == segs[i]);
                }
            }
        }
    }
}

/// An ASCII URL serializes to ASCII.
pub proof fn lemma_serialize_ascii(u: UrlRecord)
    requires
        url_ascii(u),
    ensures
        is_ascii(serialize(u, false)),
{
    broadcast use lemma_ascii_add, lemma_ascii_empty, lemma_decimal_ascii, lemma_segments_serialize_ascii;

    assert(is_ascii(seq![b':']));
    assert(is_ascii(seq![b'@']));
    assert(is_ascii(seq![b'/', b'/']));
    assert(is_ascii(seq![b'/', b'.']));
    assert(is_ascii(seq![b'?']));
    assert(is_ascii(seq![b'#']));
}

// ---------------------------------------------------------------------------
// The state machine
// ---------------------------------------------------------------------------

pub open spec fn step_ascii(s: Step) -> bool {
    match s {
        Step::Next(m, _) => machine_ascii(m),
        Step::Return(u) => url_ascii(u),
        Step::Fail => true,
    }
}

proof fn lemma_shorten_path_ascii(url: UrlRecord)
    requires
        url_ascii(url),
    ensures
        url_ascii(shorten_path(url)),
{
    if let UrlPath::List(segs) = url.path {
        if segs.len() > 0 {
            assert forall|i: int| 0 <= i < segs.drop_last().len() implies is_ascii(
                #[trigger] segs.drop_last()[i],
            ) by {
                assert(segs.drop_last()[i] == segs[i]);
            }
        }
    }
}

proof fn lemma_push_segment_ascii(url: UrlRecord, seg: Seq<u8>)
    requires
        url_ascii(url),
        is_ascii(seg),
    ensures
        url_ascii(push_segment(url, seg)),
{
    if let UrlPath::List(segs) = url.path {
        assert forall|i: int| 0 <= i < segs.push(seg).len() implies is_ascii(#[trigger] segs.push(seg)[i]) by {
            if i < segs.len() {
                assert(segs.push(seg)[i] == segs[i]);
            }
        }
    }
}

proof fn lemma_step_scheme_start_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::SchemeStart,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_scheme_start(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_scheme_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Scheme,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_scheme(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_no_scheme_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::NoScheme,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_no_scheme(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    lemma_shorten_path_ascii(url);
    lemma_shorten_path_ascii(UrlRecord { query: None, ..url });
    if let Some(b) = base {
        lemma_shorten_path_ascii(UrlRecord { scheme: b.scheme, query: None, ..url });
        lemma_shorten_path_ascii(UrlRecord {
            username: b.username,
            password: b.password,
            host: b.host,
            port: b.port,
            path: b.path,
            query: None,
            scheme: b.scheme,
            ..url
        });
        lemma_shorten_path_ascii(UrlRecord { host: b.host, path: b.path, query: None, ..url });
    }
}

proof fn lemma_step_special_relative_or_authority_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::SpecialRelativeOrAuthority,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_special_relative_or_authority(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_path_or_authority_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::PathOrAuthority,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_path_or_authority(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_relative_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Relative,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_relative(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    lemma_shorten_path_ascii(url);
    lemma_shorten_path_ascii(UrlRecord { query: None, ..url });
    if let Some(b) = base {
        lemma_shorten_path_ascii(UrlRecord { scheme: b.scheme, query: None, ..url });
        lemma_shorten_path_ascii(UrlRecord {
            username: b.username,
            password: b.password,
            host: b.host,
            port: b.port,
            path: b.path,
            query: None,
            scheme: b.scheme,
            ..url
        });
        lemma_shorten_path_ascii(UrlRecord { host: b.host, path: b.path, query: None, ..url });
    }
}

proof fn lemma_step_relative_slash_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::RelativeSlash,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_relative_slash(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_special_authority_slashes_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::SpecialAuthoritySlashes,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_special_authority_slashes(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_special_authority_ignore_slashes_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::SpecialAuthorityIgnoreSlashes,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_special_authority_ignore_slashes(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_authority_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Authority,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_authority(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_host_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        (m.state == State::Host || m.state == State::Hostname),
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_host(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_port_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Port,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_port(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_file_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::File,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_file(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    lemma_shorten_path_ascii(url);
    lemma_shorten_path_ascii(UrlRecord { query: None, ..url });
    if let Some(b) = base {
        lemma_shorten_path_ascii(UrlRecord { scheme: b.scheme, query: None, ..url });
        lemma_shorten_path_ascii(UrlRecord {
            username: b.username,
            password: b.password,
            host: b.host,
            port: b.port,
            path: b.path,
            query: None,
            scheme: b.scheme,
            ..url
        });
        lemma_shorten_path_ascii(UrlRecord { host: b.host, path: b.path, query: None, ..url });
    }
}

proof fn lemma_step_file_slash_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::FileSlash,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_file_slash(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    lemma_shorten_path_ascii(url);
    lemma_shorten_path_ascii(UrlRecord { query: None, ..url });
    if let Some(b) = base {
        lemma_shorten_path_ascii(UrlRecord { scheme: b.scheme, query: None, ..url });
        lemma_shorten_path_ascii(UrlRecord {
            username: b.username,
            password: b.password,
            host: b.host,
            port: b.port,
            path: b.path,
            query: None,
            scheme: b.scheme,
            ..url
        });
        lemma_shorten_path_ascii(UrlRecord { host: b.host, path: b.path, query: None, ..url });
    }
}

proof fn lemma_step_file_host_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::FileHost,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_file_host(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_path_start_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::PathStart,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_path_start(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    lemma_shorten_path_ascii(url);
    lemma_shorten_path_ascii(UrlRecord { query: None, ..url });
    if let Some(b) = base {
        lemma_shorten_path_ascii(UrlRecord { scheme: b.scheme, query: None, ..url });
        lemma_shorten_path_ascii(UrlRecord {
            username: b.username,
            password: b.password,
            host: b.host,
            port: b.port,
            path: b.path,
            query: None,
            scheme: b.scheme,
            ..url
        });
        lemma_shorten_path_ascii(UrlRecord { host: b.host, path: b.path, query: None, ..url });
    }
}

proof fn lemma_step_path_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Path,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_path(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

    let url = m.url;
    let buffer = m.buffer;
    if is_double_dot_segment(buffer) {
        lemma_shorten_path_ascii(url);
        lemma_push_segment_ascii(shorten_path(url), Seq::empty());
    } else {
        lemma_push_segment_ascii(url, Seq::empty());
        if url.scheme == s_file() && path_is_empty_list(url) && is_windows_drive_letter(buffer) {
            lemma_push_segment_ascii(url, buffer.update(1, b':'));
        } else {
            lemma_push_segment_ascii(url, buffer);
        }
    }
}

proof fn lemma_step_opaque_path_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::OpaquePath,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_opaque_path(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_query_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Query,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_query(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

proof fn lemma_step_fragment_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        m.state == State::Fragment,
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step_fragment(input, base, so, m, p)),
{
    broadcast use lemma_ascii_add, lemma_ascii_push, lemma_ascii_empty, lemma_pe_ascii,
        lemma_host_parse_ascii, lemma_append_userinfo_ascii, lemma_pe_seq_ascii;

}

pub proof fn lemma_step_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        base_ascii(base),
        0 <= p <= input.len(),
    ensures
        step_ascii(step(input, base, so, m, p)),
{
    match m.state {
        State::SchemeStart => lemma_step_scheme_start_ascii(input, base, so, m, p),
        State::Scheme => lemma_step_scheme_ascii(input, base, so, m, p),
        State::NoScheme => lemma_step_no_scheme_ascii(input, base, so, m, p),
        State::SpecialRelativeOrAuthority => lemma_step_special_relative_or_authority_ascii(input, base, so, m, p),
        State::PathOrAuthority => lemma_step_path_or_authority_ascii(input, base, so, m, p),
        State::Relative => lemma_step_relative_ascii(input, base, so, m, p),
        State::RelativeSlash => lemma_step_relative_slash_ascii(input, base, so, m, p),
        State::SpecialAuthoritySlashes => lemma_step_special_authority_slashes_ascii(input, base, so, m, p),
        State::SpecialAuthorityIgnoreSlashes => lemma_step_special_authority_ignore_slashes_ascii(input, base, so, m, p),
        State::Authority => lemma_step_authority_ascii(input, base, so, m, p),
        State::Host | State::Hostname => lemma_step_host_ascii(input, base, so, m, p),
        State::Port => lemma_step_port_ascii(input, base, so, m, p),
        State::File => lemma_step_file_ascii(input, base, so, m, p),
        State::FileSlash => lemma_step_file_slash_ascii(input, base, so, m, p),
        State::FileHost => lemma_step_file_host_ascii(input, base, so, m, p),
        State::PathStart => lemma_step_path_start_ascii(input, base, so, m, p),
        State::Path => lemma_step_path_ascii(input, base, so, m, p),
        State::OpaquePath => lemma_step_opaque_path_ascii(input, base, so, m, p),
        State::Query => lemma_step_query_ascii(input, base, so, m, p),
        State::Fragment => lemma_step_fragment_ascii(input, base, so, m, p),
    }
}

pub proof fn lemma_run_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        base_ascii(base),
    ensures
        run(input, base, so, m, p) matches Some(u) ==> url_ascii(u),
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if 0 <= p <= input.len() {
        lemma_step_ascii(input, base, so, m, p);
        match step(input, base, so, m, p) {
            Step::Next(m2, p2) => {
                if p2 < input.len() && p2 + 1 >= 0 {
                    lemma_run_ascii(input, base, so, m2, p2 + 1);
                }
            },
            _ => {},
        }
    }
}

/// `lemma_run_ascii` for the URL a run leaves behind.
pub proof fn lemma_run_url_ascii(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_ascii(m),
        base_ascii(base),
    ensures
        url_ascii(run_url(input, base, so, m, p)),
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if 0 <= p <= input.len() {
        lemma_step_ascii(input, base, so, m, p);
        match step(input, base, so, m, p) {
            Step::Next(m2, p2) => {
                if p2 < input.len() && p2 + 1 >= 0 {
                    lemma_run_url_ascii(input, base, so, m2, p2 + 1);
                }
            },
            _ => {},
        }
    }
}

/// The theorem: the URL parser only returns ASCII URLs (given an ASCII base).
pub proof fn lemma_parse_url_ascii(input: Seq<u8>, base: Option<UrlRecord>)
    requires
        base_ascii(base),
    ensures
        parse_url(input, base) matches Some(u) ==> url_ascii(u) && is_ascii(serialize(u, false)),
{
    broadcast use lemma_ascii_empty;

    let i = remove_tab_newline(trim_c0_space(input));
    lemma_run_ascii(i, base, None, initial_machine(State::SchemeStart, new_url()), 0);
    if let Some(u) = parse_url(input, base) {
        lemma_serialize_ascii(u);
    }
}

} // verus!
