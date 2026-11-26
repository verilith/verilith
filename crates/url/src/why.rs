//! Why the parser rejects an input: `spec::run_r` agrees with `spec::run`,
//! and the reason a failed run leaves (`parse::Fault`) is turned into the
//! `spec::Why` the spec gives.
use crate::host::*;
use crate::parse::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// `run_r` succeeds exactly when `run` does, with the same URL.
pub proof fn lemma_run_r(input: Seq<u8>, base: Option<UrlRecord>, so: Option<State>, m: Machine, p: int)
    ensures
        run(input, base, so, m, p) == match run_r(input, base, so, m, p) {
            Ok(u) => Some(u),
            Err(_) => None,
        },
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if 0 <= p <= input.len() {
        match step(input, base, so, m, p) {
            Step::Next(m2, p2) => {
                if p2 < input.len() && p2 + 1 >= 0 {
                    lemma_run_r(input, base, so, m2, p2 + 1);
                }
            },
            _ => {},
        }
    }
}

/// `parse_why` is `None` exactly when `parse_url` succeeds.
pub proof fn lemma_parse_why(input: Seq<u8>, base: Option<UrlRecord>)
    ensures
        parse_why(input, base) is None <==> parse_url(input, base) is Some,
{
    lemma_run_r(remove_tab_newline(trim_c0_space(input)), base, None, initial_machine(State::SchemeStart, new_url()), 0);
}

/// `host_why`, computed.
pub fn host_why_exec(s: &[u8], is_opaque: bool) -> (w: Why)
    ensures
        w == host_why(s@, is_opaque),
{
    if s.len() > 0 && s[0] == b'[' {
        return Why::Ipv6;
    }
    if is_opaque {
        return Why::DomainChar;
    }
    let tracked mut meter = Meter { n: 0 };
    let d = percent_decode_exec(s, Tracked(&mut meter));
    let r: Vec<u8> = if is_ascii_exec(d.as_slice(), Tracked(&mut meter)) {
        let mut out: Vec<u8> = Vec::with_capacity(d.len());
        let mut i: usize = 0;
        while i < d.len()
            invariant
                i <= d.len(),
                out@ == ascii_lowercase_seq(d@.take(i as int)),
            decreases d.len() - i,
        {
            out.push(to_lower(d[i]));
            proof {
                assert(ascii_lowercase_seq(d@.take(i + 1)) =~= ascii_lowercase_seq(d@.take(i as int)).push(
                    ascii_lowercase(d@[i as int]),
                ));
            }
            i = i + 1;
        }
        proof {
            assert(d@.take(i as int) =~= d@);
        }
        out
    } else {
        let mut map: Vec<u32> = Vec::new();
        let mut out: Vec<u8> = Vec::new();
        if !crate::idna::domain_to_ascii_into(d.as_slice(), &mut map, &mut out, Tracked(&mut meter)) {
            return Why::Idna;
        }
        proof {
            assert(out@ =~= Seq::<u8>::empty() + domain_to_ascii(d@)->0);
        }
        if !is_ascii_exec(out.as_slice(), Tracked(&mut meter)) {
            return Why::Idna;
        }
        out
    };
    proof {
        assert(domain_parse_result(percent_decode(s@)) == Some(r@));
    }
    if r.len() == 0 {
        return Why::EmptyHost;
    }
    let mut i: usize = 0;
    while i < r.len()
        invariant
            i <= r.len(),
            r.len() > 0,
            !(s.len() > 0 && s@[0] == b'['),
            !is_opaque,
            domain_parse_result(percent_decode(s@)) == Some(r@),
            forall|j: int| 0 <= j < i ==> !is_forbidden_domain_code_point(#[trigger] r@[j]),
        decreases r.len() - i,
    {
        if is_forbidden_domain(r[i]) {
            proof {
                assert(is_forbidden_domain_code_point(r@[i as int]));
                assert(contains_forbidden_domain_code_point(r@));
            }
            return Why::Idna;
        }
        i = i + 1;
    }
    Why::Ipv4
}

/// `fault_why`, computed.
pub fn fault_why_exec(input: &[u8], f: Fault) -> (w: Why)
    requires
        fault_ok(f, input.len() as nat),
    ensures
        w == fault_why(input@, f),
{
    match f {
        Fault::NoBase => Why::NoBase,
        Fault::CannotBeABase => Why::CannotBeABase,
        Fault::EmptyHost => Why::EmptyHost,
        Fault::Port => Why::Port,
        Fault::Host(a, e, o) => host_why_exec(vstd::slice::slice_subrange(input, a, e), o),
    }
}

} // verus!
