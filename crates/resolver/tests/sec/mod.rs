//! A signed DNS hierarchy for the DNSSEC tests: zones signed here, at
//! start-up, with fresh keys (RSA/SHA-256, ECDSA P-256 and P-384,
//! Ed25519), NSEC and NSEC3 chains, and an authoritative server that
//! answers as RFC 4035 §3.1 says: RRSIGs with the data, DS or the proof of
//! no DS with referrals, and NSEC or NSEC3 proofs of nonexistence and of
//! wildcard expansion. Some zones are broken on purpose.
#![allow(dead_code)]
use aws_lc_rs::rand::SystemRandom;
use aws_lc_rs::signature::{self, EcdsaKeyPair, Ed25519KeyPair, KeyPair, RsaKeyPair};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::net::UdpSocket;
use std::sync::Arc;
use verilith_dns::{encode_name, Message, Section};

pub const A: u16 = 1;
pub const NS: u16 = 2;
pub const CNAME: u16 = 5;
pub const SOA: u16 = 6;
pub const TXT: u16 = 16;
pub const AAAA: u16 = 28;
pub const OPT: u16 = 41;
pub const DS: u16 = 43;
pub const RRSIG: u16 = 46;
pub const NSEC: u16 = 47;
pub const DNSKEY: u16 = 48;
pub const NSEC3: u16 = 50;
pub const NSEC3PARAM: u16 = 51;

#[derive(Clone, Debug)]
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
pub fn txt(name: &str, s: &str) -> Rec {
    let mut r = vec![s.len() as u8];
    r.extend(s.as_bytes());
    rec(name, TXT, 300, r)
}
pub fn soa(zone: &str) -> Rec {
    let mut r = encode_name(&format!("ns.{zone}")).unwrap();
    r.extend(encode_name(&format!("admin.{zone}")).unwrap());
    for v in [1u32, 3600, 600, 86400, 60] {
        r.extend_from_slice(&v.to_be_bytes());
    }
    rec(zone, SOA, 3600, r)
}

/// Wire form, lowercase.
pub fn wire(n: &str) -> Vec<u8> {
    if n.is_empty() {
        return vec![0];
    }
    encode_name(&n.to_ascii_lowercase()).unwrap()
}

fn labels(n: &str) -> Vec<&str> {
    if n.is_empty() {
        vec![]
    } else {
        n.split('.').collect()
    }
}

fn under(name: &str, zone: &str) -> bool {
    zone.is_empty() || name == zone || name.ends_with(&format!(".{zone}"))
}

fn parent(n: &str) -> &str {
    n.split_once('.').map(|(_, r)| r).unwrap_or("")
}

/// Canonical DNS name order (RFC 4034 §6.1).
pub fn canon_cmp(x: &str, y: &str) -> std::cmp::Ordering {
    let (mut a, mut b) = (labels(x), labels(y));
    a.reverse();
    b.reverse();
    for (p, q) in a.iter().zip(b.iter()) {
        let o = p.as_bytes().cmp(q.as_bytes());
        if o != std::cmp::Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

fn bitmap(types: &[u16]) -> Vec<u8> {
    let mut t: Vec<u16> = types.to_vec();
    t.sort();
    t.dedup();
    let mut out = Vec::new();
    let mut w = 0;
    while w < 256 {
        let mut bits = [0u8; 32];
        let mut len = 0;
        for &x in &t {
            if (x >> 8) as usize == w {
                let lo = (x & 0xff) as usize;
                bits[lo / 8] |= 0x80 >> (lo % 8);
                len = len.max(lo / 8 + 1);
            }
        }
        if len > 0 {
            out.push(w as u8);
            out.push(len as u8);
            out.extend_from_slice(&bits[..len]);
        }
        w += 1;
    }
    out
}

pub fn key_tag(rd: &[u8]) -> u16 {
    let mut ac: u32 = 0;
    for (i, &b) in rd.iter().enumerate() {
        ac += if i % 2 == 0 { (b as u32) << 8 } else { b as u32 };
    }
    ac += (ac >> 16) & 0xffff;
    (ac & 0xffff) as u16
}

/// A zone's signing key.
pub enum Key {
    Rsa(RsaKeyPair),
    P256(EcdsaKeyPair),
    P384(EcdsaKeyPair),
    Ed(Ed25519KeyPair),
}

pub struct SigningKey {
    pub key: Key,
    pub flags: u16,
}

impl SigningKey {
    pub fn new(alg: u8, flags: u16) -> SigningKey {
        let key = match alg {
            8 => Key::Rsa(RsaKeyPair::generate(aws_lc_rs::rsa::KeySize::Rsa2048).unwrap()),
            13 => Key::P256(EcdsaKeyPair::generate(&signature::ECDSA_P256_SHA256_FIXED_SIGNING).unwrap()),
            14 => Key::P384(EcdsaKeyPair::generate(&signature::ECDSA_P384_SHA384_FIXED_SIGNING).unwrap()),
            15 => Key::Ed(Ed25519KeyPair::generate().unwrap()),
            _ => panic!("algorithm {alg}"),
        };
        SigningKey { key, flags }
    }
    pub fn alg(&self) -> u8 {
        match self.key {
            Key::Rsa(_) => 8,
            Key::P256(_) => 13,
            Key::P384(_) => 14,
            Key::Ed(_) => 15,
        }
    }
    pub fn public(&self) -> Vec<u8> {
        match &self.key {
            Key::Rsa(k) => {
                let p = k.public_key();
                let e = p.exponent().big_endian_without_leading_zero().to_vec();
                let n = p.modulus().big_endian_without_leading_zero().to_vec();
                let mut out = vec![e.len() as u8];
                out.extend(e);
                out.extend(n);
                out
            }
            Key::P256(k) | Key::P384(k) => k.public_key().as_ref()[1..].to_vec(),
            Key::Ed(k) => k.public_key().as_ref().to_vec(),
        }
    }
    pub fn dnskey(&self) -> Vec<u8> {
        let mut rd = self.flags.to_be_bytes().to_vec();
        rd.push(3);
        rd.push(self.alg());
        rd.extend(self.public());
        rd
    }
    pub fn tag(&self) -> u16 {
        key_tag(&self.dnskey())
    }
    pub fn sign(&self, data: &[u8]) -> Vec<u8> {
        let rng = SystemRandom::new();
        match &self.key {
            Key::Rsa(k) => {
                let mut sig = vec![0u8; k.public_modulus_len()];
                k.sign(&signature::RSA_PKCS1_SHA256, &rng, data, &mut sig).unwrap();
                sig
            }
            Key::P256(k) | Key::P384(k) => k.sign(&rng, data).unwrap().as_ref().to_vec(),
            Key::Ed(k) => k.sign(data).as_ref().to_vec(),
        }
    }
    /// The DS RDATA for this key of `owner` (SHA-256).
    pub fn ds(&self, owner: &str) -> Vec<u8> {
        let mut d = wire(owner);
        d.extend(self.dnskey());
        let h = aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA256, &d);
        let mut rd = self.tag().to_be_bytes().to_vec();
        rd.push(self.alg());
        rd.push(2);
        rd.extend(h.as_ref());
        rd
    }
}

pub fn now() -> u32 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() as u32
}

/// How a zone is to be signed.
pub struct Plan {
    pub zone: String,
    pub records: Vec<Rec>,
    /// KSK (signs the DNSKEY RRset) and ZSK (signs the rest); the same key
    /// for a single-key zone.
    pub ksk: SigningKey,
    pub zsk: Option<SigningKey>,
    /// NSEC3 (iterations, salt) instead of NSEC.
    pub nsec3: Option<(u16, Vec<u8>)>,
    /// Signature validity: inception and expiration.
    pub window: (u32, u32),
    /// Flip a bit in every signature over this type (bogus data).
    pub corrupt: Option<u16>,
}

/// A signed zone: the records, the RRSIGs by (owner, type), the denial
/// records by owner.
pub struct Signed {
    pub zone: String,
    pub data: Vec<Rec>,
    pub sigs: HashMap<(String, u16), Vec<Rec>>,
    /// NSEC or NSEC3 records, by owner, and their RRSIGs.
    pub denial: BTreeMap<String, (Rec, Vec<Rec>)>,
    pub nsec3: Option<(u16, Vec<u8>)>,
    /// NSEC3: owner hash label (base32hex) -> original name.
    pub hashes: Vec<(Vec<u8>, String)>,
}

fn rrsig_rdata(covered: u16, alg: u8, labels: u8, ttl: u32, window: (u32, u32), tag: u16, signer: &str) -> Vec<u8> {
    let mut rd = covered.to_be_bytes().to_vec();
    rd.push(alg);
    rd.push(labels);
    rd.extend(ttl.to_be_bytes());
    rd.extend(window.1.to_be_bytes());
    rd.extend(window.0.to_be_bytes());
    rd.extend(tag.to_be_bytes());
    rd.extend(wire(signer));
    rd
}

/// The RRSIG over `rs` (one RRset) by `key` of `zone`.
pub fn sign_rrset(rs: &[Rec], key: &SigningKey, zone: &str, window: (u32, u32), corrupt: bool) -> Rec {
    let owner = &rs[0].name;
    let lab = labels(owner);
    let nl = if lab.first() == Some(&"*") { lab.len() - 1 } else { lab.len() };
    let ttl = rs[0].ttl;
    let mut rd = rrsig_rdata(rs[0].rtype, key.alg(), nl as u8, ttl, window, key.tag(), zone);
    let mut data = rd.clone();
    let mut rdatas: Vec<&Vec<u8>> = rs.iter().map(|r| &r.rdata).collect();
    rdatas.sort();
    rdatas.dedup();
    for x in rdatas {
        data.extend(wire(owner));
        data.extend(rs[0].rtype.to_be_bytes());
        data.extend(1u16.to_be_bytes());
        data.extend(ttl.to_be_bytes());
        data.extend((x.len() as u16).to_be_bytes());
        data.extend(x);
    }
    let mut sig = key.sign(&data);
    if corrupt {
        let n = sig.len();
        sig[n / 2] ^= 1;
    }
    rd.extend(sig);
    rec(owner, RRSIG, ttl, rd)
}

const B32HEX: &[u8] = b"0123456789abcdefghijklmnopqrstuv";

pub fn base32hex(h: &[u8]) -> String {
    let mut out = String::new();
    let mut bits = 0u32;
    let mut acc = 0u64;
    for &b in h {
        acc = (acc << 8) | b as u64;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(B32HEX[((acc >> bits) & 31) as usize] as char);
        }
    }
    if bits > 0 {
        out.push(B32HEX[((acc << (5 - bits)) & 31) as usize] as char);
    }
    out
}

/// The NSEC3 hash of `name` (RFC 5155 §5), with aws-lc-rs's SHA-1.
pub fn nsec3_hash(name: &str, iterations: u16, salt: &[u8]) -> Vec<u8> {
    let sha1 = |d: &[u8]| aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA1_FOR_LEGACY_USE_ONLY, d).as_ref().to_vec();
    let mut x = wire(name);
    x.extend(salt);
    let mut h = sha1(&x);
    for _ in 0..iterations {
        let mut y = h.clone();
        y.extend(salt);
        h = sha1(&y);
    }
    h
}

fn join(l: &str, zone: &str) -> String {
    if zone.is_empty() {
        l.to_string()
    } else {
        format!("{l}.{zone}")
    }
}

impl Plan {
    pub fn sign(self) -> Signed {
        let zone = self.zone.clone();
        let zsk = self.zsk.as_ref().unwrap_or(&self.ksk);
        let mut data = self.records.clone();
        data.push(rec(&zone, DNSKEY, 3600, self.ksk.dnskey()));
        if let Some(z) = &self.zsk {
            data.push(rec(&zone, DNSKEY, 3600, z.dnskey()));
        }
        if let Some((it, salt)) = &self.nsec3 {
            let mut rd = vec![1u8, 0];
            rd.extend(it.to_be_bytes());
            rd.push(salt.len() as u8);
            rd.extend(salt);
            data.push(rec(&zone, NSEC3PARAM, 0, rd));
        }
        // Delegation points: names below the apex with NS records.
        let cuts: HashSet<String> =
            data.iter().filter(|r| r.rtype == NS && r.name != zone).map(|r| r.name.clone()).collect();
        let below_cut = |n: &str| cuts.iter().any(|c| n != c && under(n, c));
        // Authoritative names (not glue) and their types.
        let mut types: BTreeMap<String, Vec<u16>> = BTreeMap::new();
        for r in &data {
            if !below_cut(&r.name) {
                types.entry(r.name.clone()).or_default().push(r.rtype);
            }
        }
        let mut sets: BTreeMap<(String, u16), Vec<Rec>> = BTreeMap::new();
        for r in &data {
            if !below_cut(&r.name) {
                sets.entry((r.name.clone(), r.rtype)).or_default().push(r.clone());
            }
        }
        let mut sigs: HashMap<(String, u16), Vec<Rec>> = HashMap::new();
        for ((n, t), rs) in &sets {
            // Delegation NS records (and glue) are not signed.
            if *t == NS && cuts.contains(n) {
                continue;
            }
            let bad = self.corrupt == Some(*t);
            let mut v = vec![];
            if *t == DNSKEY {
                v.push(sign_rrset(rs, &self.ksk, &zone, self.window, bad));
            } else {
                v.push(sign_rrset(rs, zsk, &zone, self.window, bad));
            }
            sigs.insert((n.clone(), *t), v);
        }
        let mut denial = BTreeMap::new();
        let mut hashes = Vec::new();
        let mut names: Vec<String> = types.keys().cloned().collect();
        match &self.nsec3 {
            None => {
                names.sort_by(|x, y| canon_cmp(x, y));
                for (i, n) in names.iter().enumerate() {
                    let next = &names[(i + 1) % names.len()];
                    let mut ts = types[n].clone();
                    ts.push(NSEC);
                    if !(cuts.contains(n) && !ts.contains(&DS)) {
                        ts.push(RRSIG);
                    }
                    let mut rd = wire(next);
                    rd.extend(bitmap(&ts));
                    let r = rec(n, NSEC, 60, rd);
                    let s = sign_rrset(std::slice::from_ref(&r), zsk, &zone, self.window, self.corrupt == Some(NSEC));
                    denial.insert(n.clone(), (r, vec![s]));
                }
            }
            Some((it, salt)) => {
                // Empty non-terminals get NSEC3 records too (RFC 5155 §7.1).
                let mut all: HashSet<String> = names.iter().cloned().collect();
                for n in &names {
                    let mut x = n.as_str();
                    while x != zone && !x.is_empty() {
                        x = parent(x);
                        all.insert(x.to_string());
                    }
                }
                let mut hs: Vec<(Vec<u8>, String)> = all.iter().map(|n| (nsec3_hash(n, *it, salt), n.clone())).collect();
                hs.sort();
                for (i, (h, n)) in hs.iter().enumerate() {
                    let next = &hs[(i + 1) % hs.len()].0;
                    let mut ts = types.get(n).cloned().unwrap_or_default();
                    if !ts.is_empty() && !(cuts.contains(n) && !ts.contains(&DS)) {
                        ts.push(RRSIG);
                    }
                    let mut rd = vec![1u8, 0];
                    rd.extend(it.to_be_bytes());
                    rd.push(salt.len() as u8);
                    rd.extend(salt);
                    rd.push(20);
                    rd.extend(next);
                    rd.extend(bitmap(&ts));
                    let owner = join(&base32hex(h), &zone);
                    let r = rec(&owner, NSEC3, 60, rd);
                    let s = sign_rrset(std::slice::from_ref(&r), zsk, &zone, self.window, self.corrupt == Some(NSEC3));
                    denial.insert(owner, (r, vec![s]));
                }
                hashes = hs;
            }
        }
        Signed { zone, data, sigs, denial, nsec3: self.nsec3, hashes }
    }
}

/// One authoritative server for a signed (or, with no signatures,
/// unsigned) zone.
pub struct Server {
    z: Signed,
    by_name: HashMap<String, Vec<Rec>>,
    names: HashSet<String>,
    cuts: HashSet<String>,
    /// NSEC owners in canonical order.
    order: Vec<String>,
    /// Leave the denial records out of negative answers.
    pub strip_denial: bool,
}

impl Server {
    pub fn new(z: Signed) -> Server {
        let mut by_name: HashMap<String, Vec<Rec>> = HashMap::new();
        for r in &z.data {
            by_name.entry(r.name.clone()).or_default().push(r.clone());
        }
        let mut names = HashSet::new();
        for k in by_name.keys() {
            let mut x = k.as_str();
            loop {
                names.insert(x.to_string());
                if x.is_empty() {
                    break;
                }
                x = parent(x);
            }
        }
        let cuts = z.data.iter().filter(|r| r.rtype == NS && r.name != z.zone).map(|r| r.name.clone()).collect();
        let mut order: Vec<String> = z.denial.keys().cloned().collect();
        order.sort_by(|x, y| canon_cmp(x, y));
        Server { z, by_name, names, cuts, order, strip_denial: false }
    }

    fn at(&self, n: &str) -> &[Rec] {
        self.by_name.get(n).map(|v| v.as_slice()).unwrap_or(&[])
    }

    fn push_set(&self, m: &mut Message, s: Section, n: &str, t: u16, dnssec: bool) {
        for r in self.at(n).iter().filter(|r| r.rtype == t) {
            push(m, s, r);
        }
        if dnssec {
            for r in self.z.sigs.get(&(n.to_string(), t)).into_iter().flatten() {
                push(m, s, r);
            }
        }
    }

    fn push_denial(&self, m: &mut Message, owner: &str, seen: &mut HashSet<String>) {
        if self.strip_denial || !seen.insert(owner.to_string()) {
            return;
        }
        if let Some((r, s)) = self.z.denial.get(owner) {
            push(m, Section::Authority, r);
            for x in s {
                push(m, Section::Authority, x);
            }
        }
    }

    /// The NSEC owner that matches or covers `n`.
    fn nsec_for(&self, n: &str) -> String {
        let mut best = self.order.last().unwrap().clone();
        for o in &self.order {
            if canon_cmp(o, n) != std::cmp::Ordering::Greater {
                best = o.clone();
            }
        }
        best
    }

    /// The NSEC3 owner that matches or covers the hash of `n`.
    fn nsec3_for(&self, n: &str) -> String {
        let (it, salt) = self.z.nsec3.as_ref().unwrap();
        let h = nsec3_hash(n, *it, salt);
        let hs = &self.z.hashes;
        let mut best = hs.last().unwrap().0.clone();
        for (x, _) in hs {
            if *x <= h {
                best = x.clone();
            }
        }
        join(&base32hex(&best), &self.z.zone)
    }

    /// The zone apex (the name with the SOA) at or above `n`.
    fn apex(&self, n: &str) -> String {
        let mut x = n;
        while !x.is_empty() && !self.at(x).iter().any(|r| r.rtype == SOA) {
            x = parent(x);
        }
        x.to_string()
    }

    fn closest_encloser(&self, n: &str) -> String {
        let mut x = n;
        while !self.names.contains(x) {
            x = parent(x);
        }
        x.to_string()
    }

    /// Denial for a name that does not exist (`nx`), or for a missing
    /// type at an existing name.
    fn deny(&self, m: &mut Message, qname: &str, nx: bool, seen: &mut HashSet<String>) {
        if self.strip_denial || self.z.denial.is_empty() {
            return;
        }
        if self.z.nsec3.is_none() {
            self.push_denial(m, &self.nsec_for(qname), seen);
            if nx {
                let ce = self.closest_encloser(qname);
                self.push_denial(m, &self.nsec_for(&join("*", &ce)), seen);
            }
        } else if !nx {
            self.push_denial(m, &self.nsec3_for(qname), seen);
        } else {
            let ce = self.closest_encloser(qname);
            self.push_denial(m, &self.nsec3_for(&ce), seen);
            let ql = labels(qname);
            let cl = labels(&ce).len();
            let next_closer = ql[ql.len() - cl - 1..].join(".");
            self.push_denial(m, &self.nsec3_for(&next_closer), seen);
            self.push_denial(m, &self.nsec3_for(&join("*", &ce)), seen);
        }
    }

    pub fn respond(&self, query: &[u8]) -> Option<Vec<u8>> {
        let qm = verilith_dns::parse(query)?;
        let q = qm.questions().next()?;
        let raw = q.name().to_string();
        let raw = raw.trim_end_matches('.');
        let qname = raw.to_ascii_lowercase();
        let dnssec = qm.additionals().any(|r| r.rtype == OPT && r.ttl & 0x8000 != 0);
        let zone = &self.z.zone;
        let mut seen = HashSet::new();
        // A referral: the deepest cut at or above qname (for DS, strictly
        // above: the parent answers for it).
        let mut cut = None;
        let mut x = qname.as_str();
        loop {
            if x != zone && self.cuts.contains(x) && !(q.qtype == DS && x == qname) {
                cut = Some(x.to_string());
            }
            if x.is_empty() || x == zone {
                break;
            }
            x = parent(x);
        }
        if let Some(c) = cut {
            let mut m = Message::new(qm.id(), 0x8000);
            m.push_question(raw, q.qtype, q.qclass).ok()?;
            for r in self.at(&c).iter().filter(|r| r.rtype == NS) {
                push(&mut m, Section::Authority, r);
            }
            if dnssec {
                if self.at(&c).iter().any(|r| r.rtype == DS) {
                    self.push_set(&mut m, Section::Authority, &c, DS, true);
                } else if self.z.denial.is_empty() {
                } else if self.z.nsec3.is_some() {
                    self.push_denial(&mut m, &self.nsec3_for(&c), &mut seen);
                } else {
                    self.push_denial(&mut m, &c, &mut seen);
                }
            }
            for r in self.at(&c).iter().filter(|r| r.rtype == NS) {
                let t = verilith_dns::Name::from_wire(&r.rdata).to_string();
                for g in self.at(t.trim_end_matches('.')).iter().filter(|g| g.rtype == A || g.rtype == AAAA) {
                    push(&mut m, Section::Additional, g);
                }
            }
            return Some(finish(m, dnssec));
        }
        let mut m = Message::new(qm.id(), 0x8400);
        m.push_question(raw, q.qtype, q.qclass).ok()?;
        let mut cur = qname.clone();
        let mut hops = 0;
        loop {
            let here = self.at(&cur);
            if here.iter().any(|r| r.rtype == q.qtype) {
                self.push_set(&mut m, Section::Answer, &cur, q.qtype, dnssec);
                return Some(finish(m, dnssec));
            }
            if let Some(c) = here.iter().find(|r| r.rtype == CNAME) {
                if hops < 8 {
                    self.push_set(&mut m, Section::Answer, &cur, CNAME, dnssec);
                    let t = verilith_dns::Name::from_wire(&c.rdata).to_string();
                    cur = t.trim_end_matches('.').to_ascii_lowercase();
                    hops += 1;
                    if !under(&cur, zone) {
                        return Some(finish(m, dnssec));
                    }
                    continue;
                }
            }
            if self.names.contains(&cur) {
                // No data.
                self.push_set(&mut m, Section::Authority, &self.apex(&cur), SOA, dnssec);
                if dnssec {
                    self.deny(&mut m, &cur, false, &mut seen);
                }
                return Some(finish(m, dnssec));
            }
            // A wildcard at the closest encloser?
            let ce = self.closest_encloser(&cur);
            let w = join("*", &ce);
            let wild = self.at(&w);
            if !wild.is_empty() {
                let mut done = false;
                for t in [q.qtype, CNAME] {
                    let rs: Vec<&Rec> = wild.iter().filter(|r| r.rtype == t).collect();
                    if rs.is_empty() {
                        continue;
                    }
                    for r in &rs {
                        m.push_record(Section::Answer, &cur, r.rtype, 1, r.ttl, &r.rdata).unwrap();
                    }
                    if dnssec {
                        for s in self.z.sigs.get(&(w.clone(), t)).into_iter().flatten() {
                            m.push_record(Section::Answer, &cur, RRSIG, 1, s.ttl, &s.rdata).unwrap();
                        }
                        // The proof the name itself does not exist.
                        if self.z.denial.is_empty() {
                        } else if self.z.nsec3.is_none() {
                            self.push_denial(&mut m, &self.nsec_for(&cur), &mut seen);
                        } else {
                            let ql = labels(&cur);
                            let cl = labels(&ce).len();
                            let nc = ql[ql.len() - cl - 1..].join(".");
                            self.push_denial(&mut m, &self.nsec3_for(&nc), &mut seen);
                        }
                    }
                    done = true;
                    break;
                }
                if !done {
                    self.push_set(&mut m, Section::Authority, &self.apex(&cur), SOA, dnssec);
                    if dnssec {
                        self.deny(&mut m, &cur, true, &mut seen);
                    }
                }
                return Some(finish(m, dnssec));
            }
            m = m.with_header(qm.id(), 0x8403);
            self.push_set(&mut m, Section::Authority, &self.apex(&cur), SOA, dnssec);
            if dnssec {
                self.deny(&mut m, &cur, true, &mut seen);
            }
            return Some(finish(m, dnssec));
        }
    }
}

fn push(m: &mut Message, s: Section, r: &Rec) {
    m.push_record(s, &r.name, r.rtype, 1, r.ttl, &r.rdata).unwrap();
}

fn finish(mut m: Message, dnssec: bool) -> Vec<u8> {
    if dnssec {
        m.push_record(Section::Additional, "", OPT, 4096, 0x8000, &[]).unwrap();
    }
    m.to_bytes_compressed()
}

/// Runs `server` on `ip`:`port` (UDP, truncating at 1232 bytes, and TCP).
pub fn run(ip: [u8; 4], port: u16, server: Server) {
    let s = Arc::new(server);
    let addr = std::net::SocketAddr::from((ip, port));
    let u = UdpSocket::bind(addr).unwrap_or_else(|e| panic!("bind {addr}: {e}"));
    for _ in 0..2 {
        let u = u.try_clone().unwrap();
        let s = s.clone();
        std::thread::spawn(move || {
            let mut buf = [0u8; 4096];
            loop {
                let Ok((n, from)) = u.recv_from(&mut buf) else { continue };
                if let Some(mut r) = s.respond(&buf[..n]) {
                    if r.len() > 1232 {
                        // Header only, with TC.
                        r.truncate(12);
                        r[2] |= 0x02;
                        r[4..12].fill(0);
                    }
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

pub const ROOT: [u8; 4] = [127, 0, 1, 2];
pub const COM: [u8; 4] = [127, 0, 1, 3];
pub const EXAMPLE: [u8; 4] = [127, 0, 1, 4];
pub const N3: [u8; 4] = [127, 0, 1, 5];
pub const UNSIGNED: [u8; 4] = [127, 0, 1, 6];
pub const BAD: [u8; 4] = [127, 0, 1, 7];
pub const EXPIRED: [u8; 4] = [127, 0, 1, 8];
pub const WRONGDS: [u8; 4] = [127, 0, 1, 9];
pub const STRIP: [u8; 4] = [127, 0, 1, 10];
pub const ED: [u8; 4] = [127, 0, 1, 11];

/// The hierarchy, on `port`. Returns the root trust anchor (DS RDATA).
///
/// - `.` (RSA/SHA-256, NSEC) delegates `com` (signed), `n3` (signed,
///   NSEC3) and `insecure` (no DS).
/// - `com` (Ed25519, NSEC): `example.com` (P-256, separate KSK and ZSK),
///   `unsigned.com` (no DS), `bad.com` (A signatures corrupted),
///   `expired.com` (signatures expired), `wrongds.com` (DS for another
///   key), `strip.com` (negative answers without their proofs),
///   `ed.com` (Ed25519).
/// - `n3` (P-384, NSEC3, 5 iterations, salted): `deep.n3`, a wildcard,
///   and `unsigned.n3` (no DS).
pub fn start(port: u16) -> Vec<u8> {
    start_with(port, 0)
}

/// `start`, with `hosts` more names in example.com (h0 to h`hosts`-1,
/// one A record each), for benchmarks.
pub fn start_with(port: u16, hosts: u32) -> Vec<u8> {
    let t = now();
    let ok = (t - 3600, t + 30 * 86400);
    let root_k = SigningKey::new(8, 257);
    let com_k = SigningKey::new(15, 257);
    let ex_ksk = SigningKey::new(13, 257);
    let ex_zsk = SigningKey::new(13, 256);
    let n3_k = SigningKey::new(14, 257);
    let bad_k = SigningKey::new(13, 257);
    let exp_k = SigningKey::new(13, 257);
    let wrong_k = SigningKey::new(13, 257);
    let other_k = SigningKey::new(13, 257);
    let strip_k = SigningKey::new(13, 257);
    let ed_k = SigningKey::new(15, 257);

    let root = Plan {
        zone: String::new(),
        records: vec![
            soa(""),
            ns("", "a.root-servers.test"),
            ns("com", "ns.com"),
            a("ns.com", COM),
            rec("com", DS, 3600, com_k.ds("com")),
            ns("n3", "ns.n3"),
            a("ns.n3", N3),
            rec("n3", DS, 3600, n3_k.ds("n3")),
            ns("insecure", "ns.insecure"),
            a("ns.insecure", UNSIGNED),
        ],
        ksk: root_k,
        zsk: None,
        nsec3: None,
        window: ok,
        corrupt: None,
    };
    let anchor = root.ksk.ds("");
    let mut com = vec![soa("com"), ns("com", "ns.com"), a("ns.com", COM)];
    for (z, ip, k) in [
        ("example.com", EXAMPLE, Some(&ex_ksk)),
        ("unsigned.com", UNSIGNED, None),
        ("bad.com", BAD, Some(&bad_k)),
        ("expired.com", EXPIRED, Some(&exp_k)),
        ("wrongds.com", WRONGDS, Some(&other_k)),
        ("strip.com", STRIP, Some(&strip_k)),
        ("ed.com", ED, Some(&ed_k)),
    ] {
        com.push(ns(z, &format!("ns.{z}")));
        com.push(a(&format!("ns.{z}"), ip));
        if let Some(k) = k {
            com.push(rec(z, DS, 3600, k.ds(z)));
        }
    }
    let com = Plan { zone: "com".into(), records: com, ksk: com_k, zsk: None, nsec3: None, window: ok, corrupt: None };
    let zone = |z: &str, ip: [u8; 4], extra: Vec<Rec>| {
        let mut v = vec![soa(z), ns(z, &format!("ns.{z}")), a(&format!("ns.{z}"), ip)];
        v.extend(extra);
        v
    };
    let example = Plan {
        zone: "example.com".into(),
        records: zone("example.com", EXAMPLE, vec![
            a("www.example.com", [192, 0, 2, 1]),
            a("www.example.com", [192, 0, 2, 2]),
            txt("www.example.com", "hello"),
            cname("alias.example.com", "www.example.com"),
            cname("out.example.com", "www.ed.com"),
            cname("tounsigned.example.com", "www.unsigned.com"),
            cname("tobad.example.com", "www.bad.com"),
            a("*.wild.example.com", [192, 0, 2, 7]),
            a("host.wild.example.com", [192, 0, 2, 8]),
            a("a.b.c.example.com", [192, 0, 2, 9]),
        ])
        .into_iter()
        .chain((0..hosts).map(|i| a(&format!("h{i}.example.com"), [10, (i >> 16) as u8, (i >> 8) as u8, i as u8])))
        .collect(),
        ksk: ex_ksk,
        zsk: Some(ex_zsk),
        nsec3: None,
        window: ok,
        corrupt: None,
    };
    let n3 = Plan {
        zone: "n3".into(),
        records: vec![
            soa("n3"),
            ns("n3", "ns.n3"),
            a("ns.n3", N3),
            a("www.n3", [192, 0, 2, 31]),
            a("x.deep.n3", [192, 0, 2, 32]),
            a("*.wild.n3", [192, 0, 2, 33]),
            ns("unsigned.n3", "ns.unsigned.n3"),
            a("ns.unsigned.n3", UNSIGNED),
        ],
        ksk: n3_k,
        zsk: None,
        nsec3: Some((5, vec![0xab, 0xcd])),
        window: ok,
        corrupt: None,
    };
    let plain = |z: &str, ip: [u8; 4], k: SigningKey, window: (u32, u32), corrupt: Option<u16>| {
        Plan {
            zone: z.into(),
            records: zone(z, ip, vec![a(&format!("www.{z}"), [192, 0, 2, 40])]),
            ksk: k,
            zsk: None,
            nsec3: None,
            window,
            corrupt,
        }
        .sign()
    };
    run(ROOT, port, Server::new(root.sign()));
    run(COM, port, Server::new(com.sign()));
    run(EXAMPLE, port, Server::new(example.sign()));
    run(N3, port, Server::new(n3.sign()));
    run(BAD, port, Server::new(plain("bad.com", BAD, bad_k, ok, Some(A))));
    run(EXPIRED, port, Server::new(plain("expired.com", EXPIRED, exp_k, (t - 86400 * 10, t - 86400), None)));
    run(WRONGDS, port, Server::new(plain("wrongds.com", WRONGDS, wrong_k, ok, None)));
    let mut s = Server::new(plain("strip.com", STRIP, strip_k, ok, None));
    s.strip_denial = true;
    run(STRIP, port, s);
    run(ED, port, Server::new(plain("ed.com", ED, ed_k, ok, None)));
    // One server for every unsigned zone (no keys, no signatures).
    let mut u = Signed {
        zone: String::new(),
        data: vec![],
        sigs: HashMap::new(),
        denial: BTreeMap::new(),
        nsec3: None,
        hashes: vec![],
    };
    for z in ["unsigned.com", "insecure", "unsigned.n3"] {
        u.data.extend(zone(z, UNSIGNED, vec![a(&format!("www.{z}"), [192, 0, 2, 50])]));
    }
    run(UNSIGNED, port, Server::new_unsigned(u));
    anchor
}

impl Server {
    /// A server for several unsigned zones at once (no DNSSEC records).
    fn new_unsigned(z: Signed) -> Server {
        let mut s = Server::new(z);
        s.strip_denial = true;
        s.cuts.clear();
        s
    }
}
