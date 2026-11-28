//! A small DNS hierarchy for tests and benchmarks: authoritative servers
//! on 127.0.0.x, a root and the zones below it, with servers that lie in
//! the ways resolvers have been attacked (out-of-bailiwick records,
//! upward and sideways referrals, CNAME loops).
#![allow(dead_code)]
use std::net::UdpSocket;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use verilith_dns::{encode_name, Message, Section};

pub const A: u16 = 1;
pub const NS: u16 = 2;
pub const CNAME: u16 = 5;
pub const SOA: u16 = 6;
pub const AAAA: u16 = 28;

#[derive(Clone)]
pub struct Rec {
    pub name: String,
    pub rtype: u16,
    pub ttl: u32,
    pub rdata: Vec<u8>,
}

pub fn rec(name: &str, rtype: u16, ttl: u32, rdata: Vec<u8>) -> Rec {
    Rec { name: name.to_ascii_lowercase(), rtype, ttl, rdata }
}
pub fn a(name: &str, ip: [u8; 4]) -> Rec {
    rec(name, A, 300, ip.to_vec())
}
pub fn ns(name: &str, target: &str) -> Rec {
    rec(name, NS, 3600, encode_name(target).unwrap())
}
pub fn cname(name: &str, target: &str) -> Rec {
    rec(name, CNAME, 300, encode_name(target).unwrap())
}
pub fn soa(zone: &str) -> Rec {
    let mut r = encode_name(&format!("ns.{zone}")).unwrap();
    r.extend(encode_name(&format!("admin.{zone}")).unwrap());
    for v in [1u32, 3600, 600, 86400, 60] {
        r.extend_from_slice(&v.to_be_bytes());
    }
    rec(zone, SOA, 3600, r)
}

/// One authoritative server.
#[derive(Clone, Default)]
pub struct Server {
    pub zone: String,
    /// The zone's data, NS records for children (delegations) and their
    /// glue included.
    pub data: Vec<Rec>,
    /// Records added to every answer section, and to every additional
    /// section: lies.
    pub inject_answer: Vec<Rec>,
    pub inject_additional: Vec<Rec>,
    /// Answer every query with this referral instead (zone, ns name, glue).
    pub refer: Option<(String, String, [u8; 4])>,
    /// Counts the queries this server gets.
    pub count: Option<Arc<AtomicUsize>>,
}

fn under(name: &str, zone: &str) -> bool {
    zone.is_empty() || name == zone || name.ends_with(&format!(".{zone}"))
}

fn push(m: &mut Message, s: Section, r: &Rec) {
    m.push_record(s, &r.name, r.rtype, 1, r.ttl, &r.rdata).unwrap();
}

/// A server with its data indexed by owner name.
struct Indexed {
    s: Server,
    by_name: std::collections::HashMap<String, Vec<Rec>>,
    /// Every owner name and all its ancestors.
    names: std::collections::HashSet<String>,
}

impl Indexed {
    fn at(&self, name: &str) -> &[Rec] {
        self.by_name.get(name).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Some name at or below `name` has records.
    fn exists(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    fn respond(&self, query: &[u8]) -> Option<Vec<u8>> {
        let s = &self.s;
        if let Some(c) = &s.count {
            c.fetch_add(1, Ordering::Relaxed);
        }
        let qm = verilith_dns::parse(query)?;
        let q = qm.questions().next()?;
        let qname_raw = q.name().to_string();
        let qname = qname_raw.trim_end_matches('.').to_ascii_lowercase();
        let mut m = Message::new(qm.id(), 0x8000);
        m.push_question(qname_raw.trim_end_matches('.'), q.qtype, q.qclass).ok()?;
        if let Some((z, n, ip)) = &s.refer {
            push(&mut m, Section::Authority, &ns(z, n));
            push(&mut m, Section::Additional, &a(n, *ip));
            return Some(m.to_bytes_compressed());
        }
        // The deepest delegated child zone at or above qname.
        let mut child = None;
        let mut x = qname.as_str();
        loop {
            if x != s.zone && self.at(x).iter().any(|r| r.rtype == NS) && under(x, &s.zone) {
                child = Some(x.to_string());
                break;
            }
            if x.is_empty() || x == s.zone {
                break;
            }
            x = x.split_once('.').map(|(_, r)| r).unwrap_or("");
        }
        if let Some(c) = child {
            for r in self.at(&c).iter().filter(|r| r.rtype == NS) {
                push(&mut m, Section::Authority, r);
                let target = verilith_dns::Name::from_wire(&r.rdata).to_string();
                for g in self.at(target.trim_end_matches('.')).iter().filter(|g| g.rtype == A || g.rtype == AAAA) {
                    push(&mut m, Section::Additional, g);
                }
            }
            for r in &s.inject_additional {
                push(&mut m, Section::Additional, r);
            }
            return Some(m.to_bytes_compressed());
        }
        let mut m = Message::new(qm.id(), 0x8400);
        m.push_question(qname_raw.trim_end_matches('.'), q.qtype, q.qclass).ok()?;
        let mut cur = qname.clone();
        let mut hops = 0;
        let mut answered = false;
        loop {
            let hits: Vec<&Rec> = self.at(&cur).iter().filter(|r| r.rtype == q.qtype).collect();
            if !hits.is_empty() {
                for r in hits {
                    push(&mut m, Section::Answer, r);
                }
                answered = true;
                break;
            }
            match self.at(&cur).iter().find(|r| r.rtype == CNAME) {
                Some(c) if hops < 10 => {
                    push(&mut m, Section::Answer, c);
                    let t = verilith_dns::Name::from_wire(&c.rdata).to_string();
                    cur = t.trim_end_matches('.').to_ascii_lowercase();
                    hops += 1;
                    if !under(&cur, &s.zone) {
                        answered = true;
                        break;
                    }
                }
                _ => break,
            }
        }
        for r in &s.inject_answer {
            push(&mut m, Section::Answer, r);
        }
        for r in &s.inject_additional {
            push(&mut m, Section::Additional, r);
        }
        if !answered {
            if !self.by_name.contains_key(&cur) && !self.exists(&cur) {
                m = m.with_header(qm.id(), 0x8403);
            }
            if let Some(soa) = s.data.iter().find(|r| r.rtype == SOA) {
                push(&mut m, Section::Authority, soa);
            }
        }
        Some(m.to_bytes_compressed())
    }
}

/// Runs `server` on `ip`:`port` (UDP and TCP) in background threads.
pub fn run(ip: [u8; 4], port: u16, server: Server) {
    let mut by_name: std::collections::HashMap<String, Vec<Rec>> = Default::default();
    for r in &server.data {
        by_name.entry(r.name.clone()).or_default().push(r.clone());
    }
    let mut names = std::collections::HashSet::new();
    for k in by_name.keys() {
        let mut x = k.as_str();
        loop {
            names.insert(x.to_string());
            match x.split_once('.') {
                Some((_, r)) => x = r,
                None => break,
            }
        }
    }
    let s = Arc::new(Indexed { s: server, by_name, names });
    let addr = std::net::SocketAddr::from((ip, port));
    let u = UdpSocket::bind(addr).unwrap_or_else(|e| panic!("bind {addr}: {e}"));
    for _ in 0..2 {
        let u = u.try_clone().unwrap();
        let s = s.clone();
        std::thread::spawn(move || {
            let mut buf = [0u8; 4096];
            loop {
                let Ok((n, from)) = u.recv_from(&mut buf) else { continue };
                if let Some(r) = s.respond(&buf[..n]) {
                    let _ = u.send_to(&r, from);
                }
            }
        });
    }
    let t = std::net::TcpListener::bind(addr).unwrap();
    std::thread::spawn(move || {
        use std::io::{Read, Write};
        for c in t.incoming() {
            let Ok(mut c) = c else { continue };
            let s = s.clone();
            std::thread::spawn(move || {
                let mut len = [0u8; 2];
                while c.read_exact(&mut len).is_ok() {
                    let mut q = vec![0u8; u16::from_be_bytes(len) as usize];
                    if c.read_exact(&mut q).is_err() {
                        return;
                    }
                    if let Some(r) = s.respond(&q) {
                        let mut out = (r.len() as u16).to_be_bytes().to_vec();
                        out.extend(r);
                        let _ = c.write_all(&out);
                    }
                }
            });
        }
    });
}

pub const ROOT: [u8; 4] = [127, 0, 0, 2];
pub const COM: [u8; 4] = [127, 0, 0, 3];
pub const EXAMPLE: [u8; 4] = [127, 0, 0, 4];
pub const OTHER: [u8; 4] = [127, 0, 0, 5];
pub const NET: [u8; 4] = [127, 0, 0, 6];
pub const ELSEWHERE: [u8; 4] = [127, 0, 0, 7];
pub const EVIL: [u8; 4] = [127, 0, 0, 8];
pub const LOOP: [u8; 4] = [127, 0, 0, 9];

/// The whole hierarchy, on `port`. Returns the query counter of the .net
/// servers (where an NXNS attack's lookups land).
pub fn start(port: u16) -> Arc<AtomicUsize> {
    let net_count = Arc::new(AtomicUsize::new(0));
    run(ROOT, port, Server {
        zone: String::new(),
        data: vec![
            soa(""),
            ns("", "a.root-servers.test"),
            a("a.root-servers.test", ROOT),
            ns("com", "ns1.com-servers.net"),
            a("ns1.com-servers.net", COM),
            ns("net", "ns.net"),
            a("ns.net", NET),
            ns("evil", "ns.evil"),
            a("ns.evil", EVIL),
        ],
        ..Default::default()
    });
    let mut com = vec![
        soa("com"),
        ns("com", "ns1.com-servers.net"),
        ns("example.com", "ns1.example.com"),
        a("ns1.example.com", EXAMPLE),
        ns("other.com", "ns.elsewhere.net"),
        ns("loop.com", "ns.loop.com"),
        a("ns.loop.com", LOOP),
    ];
    // NXNS: a delegation to 50 name servers without glue, in a zone whose
    // servers do not exist.
    for i in 0..50 {
        com.push(ns("nxns.com", &format!("n{i}.nowhere.net")));
    }
    for i in 0..200 {
        com.push(ns(&format!("bulk{i}.com"), "ns1.example.com"));
    }
    run(COM, port, Server { zone: "com".into(), data: com, ..Default::default() });
    let mut ex = vec![
        soa("example.com"),
        ns("example.com", "ns1.example.com"),
        a("ns1.example.com", EXAMPLE),
        a("www.example.com", [192, 0, 2, 1]),
        a("www.example.com", [192, 0, 2, 2]),
        cname("alias.example.com", "www.example.com"),
        cname("ext.example.com", "host.other.com"),
        cname("c1.example.com", "c2.example.com"),
        cname("c2.example.com", "c1.example.com"),
        cname("deep.example.com", "d1.example.com"),
        a("mixed.example.com", [192, 0, 2, 9]),
    ];
    for i in 0..60 {
        ex.push(a("big.example.com", [198, 51, 100, i]));
    }
    for i in 1..=12 {
        ex.push(cname(&format!("d{i}.example.com"), &format!("d{}.example.com", i + 1)));
    }
    ex.push(a("d13.example.com", [192, 0, 2, 13]));
    for i in 0..10000 {
        ex.push(a(&format!("h{i}.example.com"), [10, (i / 65536) as u8, (i / 256 % 256) as u8, (i % 256) as u8]));
    }
    run(EXAMPLE, port, Server {
        zone: "example.com".into(),
        data: ex,
        // An out-of-bailiwick address for host.other.com in every answer,
        // and one for the .com servers in every additional section.
        inject_answer: vec![a("host.other.com", [6, 6, 6, 6])],
        inject_additional: vec![a("ns1.com-servers.net", [6, 6, 6, 6])],
        ..Default::default()
    });
    run(NET, port, Server {
        zone: "net".into(),
        data: vec![soa("net"), ns("net", "ns.net"), ns("elsewhere.net", "ns.elsewhere.net"), a("ns.elsewhere.net", ELSEWHERE)],
        count: Some(net_count.clone()),
        ..Default::default()
    });
    run(ELSEWHERE, port, Server {
        zone: "elsewhere.net".into(),
        data: vec![soa("elsewhere.net"), ns("elsewhere.net", "ns.elsewhere.net"), a("ns.elsewhere.net", OTHER)],
        ..Default::default()
    });
    run(OTHER, port, Server {
        zone: "other.com".into(),
        data: vec![soa("other.com"), ns("other.com", "ns.elsewhere.net"), a("host.other.com", [192, 0, 2, 50])],
        ..Default::default()
    });
    // A server for "evil" that refers every query to the root zone's
    // "com" (sideways and up), with its own address as com's server.
    run(EVIL, port, Server { zone: "evil".into(), refer: Some(("com".into(), "ns.evil".into(), EVIL)), ..Default::default() });
    // loop.com's server refers loop.com to itself.
    run(LOOP, port, Server { zone: "loop.com".into(), refer: Some(("loop.com".into(), "ns.loop.com".into(), LOOP)), ..Default::default() });
    net_count
}
