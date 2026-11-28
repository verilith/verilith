//! DNSSEC validation against a signed local hierarchy (tests/sec): secure
//! answers get AD, proven-unsigned ones do not, and bogus ones are
//! SERVFAIL unless the client sets CD.
mod sec;

use std::sync::{Arc, OnceLock};
use std::time::Duration;
use verilith_dns::{Message, Section};
use verilith_resolver::service::{Options, Resolver};

const PORT: u16 = 10153;

fn resolver() -> &'static Arc<Resolver> {
    static R: OnceLock<Arc<Resolver>> = OnceLock::new();
    R.get_or_init(|| {
        let anchor = sec::start(PORT);
        let o = Options {
            roots: vec![sec::ROOT.to_vec()],
            upstream_port: PORT,
            timeout: Duration::from_millis(500),
            shards: 4,
            sets: 256,
            trust_anchors: vec![anchor],
        };
        Arc::new(Resolver::new(&o))
    })
}

struct Got {
    rcode: u16,
    ad: bool,
    answers: Vec<(String, u16, Vec<u8>)>,
}

/// Asks with DO set (and CD if `cd`), over TCP.
fn ask_flags(name: &str, qtype: u16, dnssec_ok: bool, cd: bool) -> Got {
    let mut m = Message::new(0x5151, 0x0100 | if cd { 0x0010 } else { 0 });
    m.push_question(name, qtype, 1).unwrap();
    m.push_record(Section::Additional, "", 41, 1232, if dnssec_ok { 0x8000 } else { 0 }, &[]).unwrap();
    let rep = resolver().answer(&m.to_bytes(), false).expect("a reply");
    let m = verilith_dns::parse(&rep).expect("the reply parses");
    Got {
        rcode: m.flags() & 15,
        ad: m.flags() & 0x0020 != 0,
        answers: m.answers().map(|r| (r.name().to_string(), r.rtype, r.rdata.to_vec())).collect(),
    }
}

fn ask(name: &str, qtype: u16) -> Got {
    ask_flags(name, qtype, true, false)
}

fn secure(name: &str, qtype: u16, rcode: u16) -> Got {
    let g = ask(name, qtype);
    assert_eq!(g.rcode, rcode, "{name} {qtype}: rcode");
    assert!(g.ad, "{name} {qtype}: AD");
    g
}

fn insecure(name: &str, qtype: u16, rcode: u16) -> Got {
    let g = ask(name, qtype);
    assert_eq!(g.rcode, rcode, "{name} {qtype}: rcode");
    assert!(!g.ad, "{name} {qtype}: no AD");
    g
}

fn bogus(name: &str, qtype: u16) {
    let g = ask(name, qtype);
    assert_eq!(g.rcode, 2, "{name} {qtype}: SERVFAIL");
    assert!(g.answers.is_empty());
}

const NOERROR: u16 = 0;
const NXDOMAIN: u16 = 3;

#[test]
fn secure_answers() {
    let g = secure("www.example.com", sec::A, NOERROR);
    assert_eq!(g.answers.len(), 2);
    let g = secure("alias.example.com", sec::A, NOERROR);
    assert_eq!(g.answers.iter().map(|a| a.1).collect::<Vec<_>>(), vec![sec::CNAME, sec::A, sec::A]);
    secure("www.example.com", sec::TXT, NOERROR);
    secure("www.ed.com", sec::A, NOERROR);
    let g = secure("out.example.com", sec::A, NOERROR);
    assert_eq!(g.answers.last().unwrap().2, vec![192, 0, 2, 40]);
    secure("www.n3", sec::A, NOERROR);
    secure("example.com", sec::DNSKEY, NOERROR);
    secure("example.com", sec::DS, NOERROR);
    // Asked again: from the cache, still secure.
    secure("www.example.com", sec::A, NOERROR);
}

#[test]
fn secure_denials() {
    secure("nx.example.com", sec::A, NXDOMAIN);
    secure("www.example.com", sec::AAAA, NOERROR);
    secure("nx.n3", sec::A, NXDOMAIN);
    secure("a.b.nx.n3", sec::A, NXDOMAIN);
    secure("www.n3", sec::AAAA, NOERROR);
    secure("x.deep.n3", sec::TXT, NOERROR);
    secure("nope.com", sec::A, NXDOMAIN);
    secure("nope", sec::A, NXDOMAIN);
}

#[test]
fn empty_non_terminals() {
    secure("b.c.example.com", sec::A, NOERROR);
    secure("deep.n3", sec::A, NOERROR);
}

#[test]
fn wildcards() {
    let g = secure("foo.wild.example.com", sec::A, NOERROR);
    assert_eq!(g.answers, vec![("foo.wild.example.com.".to_string(), sec::A, vec![192, 0, 2, 7])]);
    let g = secure("host.wild.example.com", sec::A, NOERROR);
    assert_eq!(g.answers[0].2, vec![192, 0, 2, 8]);
    secure("foo.wild.example.com", sec::TXT, NOERROR);
    let g = secure("a.wild.n3", sec::A, NOERROR);
    assert_eq!(g.answers[0].2, vec![192, 0, 2, 33]);
}

#[test]
fn unsigned_zones() {
    let g = insecure("www.unsigned.com", sec::A, NOERROR);
    assert_eq!(g.answers[0].2, vec![192, 0, 2, 50]);
    insecure("www.insecure", sec::A, NOERROR);
    insecure("www.unsigned.n3", sec::A, NOERROR);
    insecure("nx.unsigned.com", sec::A, NXDOMAIN);
    let g = insecure("tounsigned.example.com", sec::A, NOERROR);
    assert_eq!(g.answers.len(), 2);
}

#[test]
fn bogus_answers() {
    bogus("www.bad.com", sec::A);
    bogus("www.expired.com", sec::A);
    bogus("www.wrongds.com", sec::A);
    bogus("nx.strip.com", sec::A);
    bogus("www.strip.com", sec::AAAA);
    bogus("tobad.example.com", sec::A);
    // The rest of a zone with one bad RRset is fine.
    secure("bad.com", sec::SOA, NOERROR);
    secure("www.strip.com", sec::A, NOERROR);
}

#[test]
fn checking_disabled() {
    // CD: the data, unchecked, without AD.
    let g = ask_flags("www.bad.com", sec::A, true, true);
    assert_eq!(g.rcode, NOERROR);
    assert!(!g.ad);
    assert_eq!(g.answers[0].2, vec![192, 0, 2, 40]);
    // And it is not served from the cache to a validating query.
    bogus("www.bad.com", sec::A);
}

#[test]
fn ad_only_when_asked() {
    let g = ask_flags("www.example.com", sec::A, false, false);
    assert_eq!(g.rcode, NOERROR);
    assert!(!g.ad, "no DO, no AD: no AD bit");
}
