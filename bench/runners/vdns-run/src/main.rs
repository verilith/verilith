//! DNS through vdns's own API, the native side of the comparison with
//! c-ares (suites/dns/dns.c read). Cases read/MSG for every *.dns file:
//! parse into a reused verilith_dns::Message, then read every question and every
//! record: owner name, type, class, TTL, and the RDATA decoded into its
//! typed form.
//! check = questions and records * 1000003 + the sum of their types and
//! classes and the records' TTLs (for an OPT record, its type only), as the
//! c-ares driver computes it.
use std::hint::black_box;
use verilith_dns::Section;

fn read(m: &mut verilith_dns::Message, b: &[u8]) -> u64 {
    if !m.parse_into(b) {
        std::process::abort();
    }
    let (mut k, mut s, mut seen) = (0u64, 0u64, 0usize);
    for q in m.questions() {
        seen += q.name.len();
        s += q.qtype as u64 + q.qclass as u64;
        k += 1;
    }
    for sec in [Section::Answer, Section::Authority, Section::Additional] {
        for rr in m.records(sec) {
            seen += rr.name.len();
            black_box(rr.data());
            // An OPT record's class and TTL fields carry EDNS values, which
            // c-ares reports differently, so they stay out of the check.
            s += rr.rtype as u64;
            if rr.rtype != 41 {
                s += rr.rclass as u64 + rr.ttl as u64;
            } else {
                black_box((rr.rclass, rr.ttl));
            }
            k += 1;
        }
    }
    black_box(seen);
    k * 1000003 + s
}

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".dns") else { continue };
        let msg = std::fs::read(format!("{dir}/{name}")).unwrap();
        let mut m = verilith_dns::Message::new(0, 0);
        r.case(format!("read/{stem}"), msg.len() as u64, move || read(&mut m, black_box(&msg)));
    }
    r.main();
}
