//! The resolver against a local hierarchy (tests/hier), over UDP, TCP,
//! DNS over TLS and DNS over HTTPS.
mod hier;

use std::sync::atomic::Ordering;
use std::sync::{Arc, OnceLock};
use std::time::Duration;
use verilith_dns::{Message, Section};
use verilith_resolver::service::{Options, Resolver};

const PORT: u16 = 10053;

fn resolver() -> &'static (Arc<Resolver>, Arc<std::sync::atomic::AtomicUsize>) {
    static R: OnceLock<(Arc<Resolver>, Arc<std::sync::atomic::AtomicUsize>)> = OnceLock::new();
    R.get_or_init(|| {
        let c = hier::start(PORT);
        let o = Options {
            roots: vec![hier::ROOT.to_vec()],
            upstream_port: PORT,
            timeout: Duration::from_millis(300),
            shards: 4,
            sets: 256,
        };
        (Arc::new(Resolver::new(&o)), c)
    })
}

fn query(name: &str, qtype: u16, edns: bool) -> Vec<u8> {
    let mut m = Message::new(0x4242, 0x0100);
    m.push_question(name, qtype, 1).unwrap();
    if edns {
        m.push_record(Section::Additional, "", 41, 1232, 0, &[]).unwrap();
    }
    m.to_bytes()
}

struct Got {
    rcode: u16,
    tc: bool,
    answers: Vec<(String, u16, Vec<u8>)>,
    authority: Vec<u16>,
    qname: String,
}

fn ask_with(name: &str, qtype: u16, udp: bool, edns: bool) -> Got {
    let r = &resolver().0;
    let rep = r.answer(&query(name, qtype, edns), udp).expect("a reply");
    let m = verilith_dns::parse(&rep).expect("the reply parses");
    assert_eq!(m.id(), 0x4242);
    assert!(m.flags() & 0x8000 != 0, "QR");
    assert!(m.flags() & 0x0080 != 0, "RA");
    assert!(m.flags() & 0x0100 != 0, "RD copied");
    let q = m.questions().next().unwrap();
    Got {
        rcode: m.flags() & 15,
        tc: m.flags() & 0x0200 != 0,
        answers: m.answers().map(|r| (r.name().to_string(), r.rtype, r.rdata.to_vec())).collect(),
        authority: m.authorities().map(|r| r.rtype).collect(),
        qname: q.name().to_string(),
    }
}

fn ask(name: &str, qtype: u16) -> Got {
    ask_with(name, qtype, true, true)
}

fn addrs(g: &Got) -> Vec<[u8; 4]> {
    g.answers.iter().filter(|a| a.1 == 1).map(|a| a.2.as_slice().try_into().unwrap()).collect()
}

#[test]
fn answers() {
    let g = ask("www.example.com", 1);
    assert_eq!(g.rcode, 0);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 1], [192, 0, 2, 2]]);
    // Again, from the cache.
    let g = ask("www.example.com", 1);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 1], [192, 0, 2, 2]]);
}

#[test]
fn case_is_kept() {
    let g = ask("WwW.ExAmPlE.CoM", 1);
    assert_eq!(g.qname, "WwW.ExAmPlE.CoM.");
    assert_eq!(addrs(&g).len(), 2);
}

#[test]
fn cname_in_zone() {
    let g = ask("alias.example.com", 1);
    assert_eq!(g.rcode, 0);
    assert_eq!(g.answers[0].1, 5);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 1], [192, 0, 2, 2]]);
}

#[test]
fn out_of_bailiwick_answer_is_ignored() {
    // example.com's server answers ext.example.com with a CNAME to
    // host.other.com and a forged A for it (6.6.6.6). The resolver follows
    // the CNAME to other.com's own servers, found through .net (no glue).
    let g = ask("ext.example.com", 1);
    assert_eq!(g.rcode, 0);
    assert_eq!(g.answers[0].1, 5);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 50]]);
    let g = ask("host.other.com", 1);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 50]]);
}

#[test]
fn out_of_bailiwick_glue_is_ignored() {
    // Every example.com response carries a forged address for the .com
    // servers; .com names keep resolving through the real one.
    let _ = ask("mixed.example.com", 1);
    let g = ask("h7.example.com", 1);
    assert_eq!(addrs(&g), vec![[10, 0, 0, 7]]);
    let g = ask("host.other.com", 1);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 50]]);
}

#[test]
fn negative() {
    let g = ask("nope.example.com", 1);
    assert_eq!(g.rcode, 3);
    assert!(g.answers.is_empty());
    assert_eq!(g.authority, vec![6]);
    let g = ask("www.example.com", 28);
    assert_eq!(g.rcode, 0);
    assert!(g.answers.is_empty());
    assert_eq!(g.authority, vec![6]);
    // From the cache.
    let g = ask("nope.example.com", 1);
    assert_eq!(g.rcode, 3);
}

#[test]
fn cname_loop_and_long_chain() {
    assert_eq!(ask("c1.example.com", 1).rcode, 2);
    // 13 links: over the limit of 8.
    assert_eq!(ask("deep.example.com", 1).rcode, 2);
    // 7 links: d6 -> ... -> d13.
    let g = ask("d6.example.com", 1);
    assert_eq!(g.rcode, 0);
    assert_eq!(addrs(&g), vec![[192, 0, 2, 13]]);
}

#[test]
fn bad_referrals() {
    // evil's server refers everything to "com" (up and sideways), naming
    // itself as com's server; loop.com's refers loop.com to itself.
    let t = std::time::Instant::now();
    assert_eq!(ask("x.evil", 1).rcode, 2);
    assert_eq!(ask("x.loop.com", 1).rcode, 2);
    assert!(t.elapsed() < Duration::from_secs(3));
    // .com is still served by its own server.
    assert_eq!(addrs(&ask("h9.example.com", 1)), vec![[10, 0, 0, 9]]);
}

#[test]
fn nxns_is_bounded() {
    let c = &resolver().1;
    let before = c.load(Ordering::Relaxed);
    assert_eq!(ask("www.nxns.com", 1).rcode, 2);
    let n = c.load(Ordering::Relaxed) - before;
    // At most MAX_NS_LOOKUPS (2) name server lookups reach .net, each a
    // query or two; 50 names without glue are not all chased.
    assert!(n <= 6, "{n} queries reached .net");
}

#[test]
fn truncation() {
    // 60 A records do not fit 512 bytes: TC over UDP without EDNS...
    let g = ask_with("big.example.com", 1, true, false);
    assert!(g.tc);
    assert!(g.answers.is_empty());
    // ... and they do over TCP.
    let g = ask_with("big.example.com", 1, false, false);
    assert!(!g.tc);
    assert_eq!(addrs(&g).len(), 60);
}

#[test]
fn refusals() {
    let r = &resolver().0;
    assert!(r.answer(b"\x00\x01garbage", true).is_none());
    // A response is not answered.
    let mut m = Message::new(1, 0x8000);
    m.push_question("www.example.com", 1, 1).unwrap();
    assert!(r.answer(&m.to_bytes(), true).is_none());
    // AXFR: NOTIMP. CHAOS: REFUSED.
    assert_eq!(ask("example.com", 252).rcode, 4);
    let mut m = Message::new(0x4242, 0x0100);
    m.push_question("version.bind", 16, 3).unwrap();
    let rep = r.answer(&m.to_bytes(), true).unwrap();
    assert_eq!(verilith_dns::parse(&rep).unwrap().flags() & 15, 5);
}

#[test]
fn many_names_through_the_cache() {
    for i in 100..400 {
        let g = ask(&format!("h{i}.example.com"), 1);
        assert_eq!(addrs(&g), vec![[10, 0, (i / 256) as u8, (i % 256) as u8]], "h{i}");
    }
}

#[test]
fn concurrent() {
    let hs: Vec<_> = (0..8)
        .map(|t| {
            std::thread::spawn(move || {
                for i in 0..50 {
                    let n = 1000 + t * 50 + i;
                    let g = ask(&format!("h{n}.example.com"), 1);
                    assert_eq!(addrs(&g), vec![[10, 0, (n / 256) as u8, (n % 256) as u8]]);
                }
            })
        })
        .collect();
    for h in hs {
        h.join().unwrap();
    }
}
