//! Credentials and a port only come with a host: every URL the parser
//! returns, and every URL a setter leaves, with a null host has an empty
//! username and password and a null port. The setters rely on it when they
//! give a URL without a host one (`set::set_host`).
use crate::spec::*;
use vstd::prelude::*;

verus! {

pub open spec fn creds_ok(url: UrlRecord) -> bool {
    url.host is None ==> url.username.len() == 0 && url.password.len() == 0 && url.port is None
}

pub open spec fn base_creds(base: Option<UrlRecord>) -> bool {
    match base {
        Some(b) => creds_ok(b),
        None => true,
    }
}

/// No credentials and no port.
pub open spec fn fresh(url: UrlRecord) -> bool {
    url.username.len() == 0 && url.password.len() == 0 && url.port is None
}

/// The states a setter's state override can reach.
pub open spec fn override_state(s: State) -> bool {
    s == State::SchemeStart || s == State::Scheme || s == State::Host || s == State::Hostname
        || s == State::FileHost || s == State::Port || s == State::PathStart || s == State::Path
        || s == State::Query || s == State::Fragment
}

/// The machine invariant. Without a state override, the URL has no
/// credentials or port until the authority state, which collects
/// credentials before the host state sets the host; so the authority and
/// host states are exempt, and the states before them have a fresh URL.
/// The port state is only ever entered with a host.
pub open spec fn machine_creds(m: Machine, so: Option<State>) -> bool {
    &&& (m.state == State::Port ==> m.url.host is Some)
    &&& if so is Some {
        override_state(m.state) && creds_ok(m.url)
    } else if m.state == State::SchemeStart || m.state == State::Scheme || m.state == State::NoScheme
        || m.state == State::File || m.state == State::FileSlash {
        fresh(m.url)
    } else if m.state == State::Authority || m.state == State::Host || m.state == State::Hostname {
        true
    } else {
        creds_ok(m.url)
    }
}

pub open spec fn step_creds(s: Step, so: Option<State>, len: int) -> bool {
    match s {
        Step::Next(m, p) => machine_creds(m, so) && (p >= len ==> creds_ok(m.url)),
        Step::Return(u) => creds_ok(u),
        Step::Fail => true,
    }
}

proof fn lemma_shorten_creds(url: UrlRecord)
    ensures
        shorten_path(url).host == url.host,
        shorten_path(url).username == url.username,
        shorten_path(url).password == url.password,
        shorten_path(url).port == url.port,
{
}

proof fn lemma_push_creds(url: UrlRecord, seg: Seq<u8>)
    ensures
        push_segment(url, seg).host == url.host,
        push_segment(url, seg).username == url.username,
        push_segment(url, seg).password == url.password,
        push_segment(url, seg).port == url.port,
{
}

proof fn lemma_step_scheme_start_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::SchemeStart,
    ensures
        step_creds(step_scheme_start(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_scheme_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Scheme,
    ensures
        step_creds(step_scheme(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_no_scheme_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::NoScheme,
    ensures
        step_creds(step_no_scheme(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_special_relative_or_authority_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::SpecialRelativeOrAuthority,
    ensures
        step_creds(step_special_relative_or_authority(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_path_or_authority_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::PathOrAuthority,
    ensures
        step_creds(step_path_or_authority(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_relative_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Relative,
    ensures
        step_creds(step_relative(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_relative_slash_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::RelativeSlash,
    ensures
        step_creds(step_relative_slash(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_special_authority_slashes_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::SpecialAuthoritySlashes,
    ensures
        step_creds(step_special_authority_slashes(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_special_authority_ignore_slashes_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::SpecialAuthorityIgnoreSlashes,
    ensures
        step_creds(step_special_authority_ignore_slashes(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_authority_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Authority,
    ensures
        step_creds(step_authority(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_host_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Host || m.state == State::Hostname,
    ensures
        step_creds(step_host(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_port_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Port,
    ensures
        step_creds(step_port(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_file_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::File,
    ensures
        step_creds(step_file(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_file_slash_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::FileSlash,
    ensures
        step_creds(step_file_slash(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_file_host_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::FileHost,
    ensures
        step_creds(step_file_host(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_path_start_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::PathStart,
    ensures
        step_creds(step_path_start(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_path_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Path,
    ensures
        step_creds(step_path(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_opaque_path_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::OpaquePath,
    ensures
        step_creds(step_opaque_path(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_query_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Query,
    ensures
        step_creds(step_query(input, base, so, m, p), so, input.len() as int),
{
}

proof fn lemma_step_fragment_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
        m.state == State::Fragment,
    ensures
        step_creds(step_fragment(input, base, so, m, p), so, input.len() as int),
{
}

pub proof fn lemma_step_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
        0 <= p <= input.len(),
    ensures
        step_creds(step(input, base, so, m, p), so, input.len() as int),
{
    match m.state {
        State::SchemeStart => lemma_step_scheme_start_creds(input, base, so, m, p),
        State::Scheme => lemma_step_scheme_creds(input, base, so, m, p),
        State::NoScheme => lemma_step_no_scheme_creds(input, base, so, m, p),
        State::SpecialRelativeOrAuthority => lemma_step_special_relative_or_authority_creds(input, base, so, m, p),
        State::PathOrAuthority => lemma_step_path_or_authority_creds(input, base, so, m, p),
        State::Relative => lemma_step_relative_creds(input, base, so, m, p),
        State::RelativeSlash => lemma_step_relative_slash_creds(input, base, so, m, p),
        State::SpecialAuthoritySlashes => lemma_step_special_authority_slashes_creds(input, base, so, m, p),
        State::SpecialAuthorityIgnoreSlashes => lemma_step_special_authority_ignore_slashes_creds(input, base, so, m, p),
        State::Authority => lemma_step_authority_creds(input, base, so, m, p),
        State::Host | State::Hostname => lemma_step_host_creds(input, base, so, m, p),
        State::Port => lemma_step_port_creds(input, base, so, m, p),
        State::File => lemma_step_file_creds(input, base, so, m, p),
        State::FileSlash => lemma_step_file_slash_creds(input, base, so, m, p),
        State::FileHost => lemma_step_file_host_creds(input, base, so, m, p),
        State::PathStart => lemma_step_path_start_creds(input, base, so, m, p),
        State::Path => lemma_step_path_creds(input, base, so, m, p),
        State::OpaquePath => lemma_step_opaque_path_creds(input, base, so, m, p),
        State::Query => lemma_step_query_creds(input, base, so, m, p),
        State::Fragment => lemma_step_fragment_creds(input, base, so, m, p),
    }
}

pub proof fn lemma_run_creds(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    requires
        machine_creds(m, so),
        base_creds(base),
    ensures
        run(input, base, so, m, p) matches Some(u) ==> creds_ok(u),
        so is Some ==> creds_ok(run_url(input, base, so, m, p)),
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if 0 <= p <= input.len() {
        lemma_step_creds(input, base, so, m, p);
        match step(input, base, so, m, p) {
            Step::Next(m2, p2) => {
                if p2 < input.len() && p2 + 1 >= 0 {
                    lemma_run_creds(input, base, so, m2, p2 + 1);
                }
            },
            _ => {},
        }
    }
}

/// The theorem: the URL parser only returns URLs with credentials and a
/// port only when they have a host (given such a base).
pub proof fn lemma_parse_url_creds(input: Seq<u8>, base: Option<UrlRecord>)
    requires
        base_creds(base),
    ensures
        parse_url(input, base) matches Some(u) ==> creds_ok(u),
{
    let i = remove_tab_newline(trim_c0_space(input));
    lemma_run_creds(i, base, None, initial_machine(State::SchemeStart, new_url()), 0);
}

} // verus!
