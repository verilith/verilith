#![allow(dead_code)]
pub mod packets;
use verilith_dns::{Message, Section};

/// Small deterministic PRNG (xorshift64*), so tests need no dependencies.
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub fn byte(&mut self) -> u8 {
        self.next() as u8
    }
}

pub const SECTIONS: [Section; 3] = [Section::Answer, Section::Authority, Section::Additional];

/// Wire-form name from labels.
pub fn wire(labels: &[&[u8]]) -> Vec<u8> {
    let mut v = Vec::new();
    for l in labels {
        v.push(l.len() as u8);
        v.extend_from_slice(l);
    }
    v.push(0);
    v
}

pub fn random_name(r: &mut Rng) -> Vec<u8> {
    let mut v = Vec::new();
    for _ in 0..r.below(6) {
        let max = if r.below(8) == 0 { 63 } else { 10 };
        let len = 1 + r.below(max) as usize;
        if v.len() + 1 + len + 1 > 255 {
            break;
        }
        v.push(len as u8);
        for _ in 0..len {
            let c = if r.below(4) == 0 { r.byte() } else { b'a' + r.below(26) as u8 };
            v.push(c);
        }
    }
    v.push(0);
    v
}

pub fn random_message(r: &mut Rng) -> Message {
    let mut m = Message::new(r.next() as u16, r.next() as u16);
    let mut qnames = Vec::new();
    for _ in 0..r.below(3) {
        let n = random_name(r);
        m.add_question(&n, r.next() as u16, r.next() as u16).unwrap();
        qnames.push(n);
    }
    // Interleave sections to exercise insertion in the middle.
    for _ in 0..r.below(10) {
        let s = SECTIONS[r.below(3) as usize];
        let rdata: Vec<u8> = (0..r.below(40)).map(|_| r.byte()).collect();
        // Often reuse a question name, as answers do, so compression
        // points records at it.
        let name = if !qnames.is_empty() && r.below(2) == 0 {
            qnames[r.below(qnames.len() as u64) as usize].clone()
        } else {
            random_name(r)
        };
        let (t, class, ttl) = (r.next() as u16, r.next() as u16, r.next() as u32);
        match m.add_record(s, &name, t, class, ttl, &rdata) {
            // Random bytes rarely decode as a type with names in it; give
            // an NS record instead.
            Err(verilith_dns::BuildError::BadRdata) => m.add_record(s, &name, 2, class, ttl, &random_name(r)).unwrap(),
            x => x.unwrap(),
        }
    }
    m
}

pub fn same(a: &Message, b: &Message) -> bool {
    a.id() == b.id()
        && a.flags() == b.flags()
        && a.questions().len() == b.questions().len()
        && a.questions().zip(b.questions()).all(|(x, y)| x.name == y.name && x.qtype == y.qtype && x.qclass == y.qclass)
        && SECTIONS.iter().all(|&s| {
            a.records(s).len() == b.records(s).len()
                && a.records(s).zip(b.records(s)).all(|(x, y)| {
                    x.name == y.name && x.rtype == y.rtype && x.rclass == y.rclass && x.ttl == y.ttl && x.rdata == y.rdata
                })
        })
}

/// Writes `m` with RFC 1035 name compression: each name suffix already
/// written is replaced by a pointer to its first occurrence. Unverified; used
/// to produce realistic compressed input.
pub fn encode_compressed(m: &Message) -> Vec<u8> {
    let mut out = Vec::new();
    let mut seen: Vec<(Vec<u8>, usize)> = Vec::new();
    let u16 = |out: &mut Vec<u8>, x: u16| out.extend_from_slice(&x.to_be_bytes());
    let mut write_name = |out: &mut Vec<u8>, n: &[u8]| {
        let mut i = 0;
        while n[i] != 0 {
            let suffix = n[i..].to_vec();
            if let Some((_, off)) = seen.iter().find(|(s, _)| *s == suffix) {
                out.extend_from_slice(&(0xC000u16 | *off as u16).to_be_bytes());
                return;
            }
            if out.len() < 0x3FFF {
                seen.push((suffix, out.len()));
            }
            let len = n[i] as usize;
            out.extend_from_slice(&n[i..i + 1 + len]);
            i += 1 + len;
        }
        out.push(0);
    };
    u16(&mut out, m.id());
    u16(&mut out, m.flags());
    u16(&mut out, m.questions().len() as u16);
    for s in SECTIONS {
        u16(&mut out, m.records(s).len() as u16);
    }
    for q in m.questions() {
        write_name(&mut out, q.name);
        u16(&mut out, q.qtype);
        u16(&mut out, q.qclass);
    }
    for s in SECTIONS {
        for r in m.records(s) {
            write_name(&mut out, r.name);
            u16(&mut out, r.rtype);
            u16(&mut out, r.rclass);
            out.extend_from_slice(&r.ttl.to_be_bytes());
            u16(&mut out, r.rdata.len() as u16);
            out.extend_from_slice(r.rdata);
        }
    }
    out
}

/// Decodes a name at `pos` to its labels, via the verified decoder.
pub fn read_name(b: &[u8], pos: usize) -> Option<(Vec<Vec<u8>>, usize)> {
    let mut w = Vec::new();
    let (end, _) = verilith_dns::parse::read_name_into(b, pos, &mut w)?;
    Some((verilith_dns::Name::from_wire(&w).labels().map(|l| l.to_vec()).collect(), end))
}
