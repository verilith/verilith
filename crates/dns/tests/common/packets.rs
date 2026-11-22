//! Random DNS responses with typed RDATA, for the differential tests.
use super::*;
use verilith_dns::Section;

pub const TYPES: [u16; 25] =
    [1, 28, 2, 5, 12, 15, 16, 13, 6, 33, 35, 52, 64, 65, 256, 257, 41, 24, 43, 44, 46, 47, 48, 50, 51];

pub fn bytes(r: &mut Rng, d: &mut Vec<u8>, n: u64) {
    (0..n).for_each(|_| d.push(r.byte()));
}

pub fn rand_str(r: &mut Rng, max: u64) -> Vec<u8> {
    let n = r.below(max + 1) as usize;
    (0..n).map(|_| if r.below(4) == 0 { r.byte() } else { b'a' + r.below(26) as u8 }).collect()
}

pub fn cstring(r: &mut Rng, out: &mut Vec<u8>, max: u64) {
    let s = rand_str(r, max);
    out.push(s.len() as u8);
    out.extend_from_slice(&s);
}

/// A name inside RDATA: plain, or a label plus a pointer to the question
/// name at offset 12.
pub fn rd_name(r: &mut Rng, out: &mut Vec<u8>, plain: bool) {
    if plain || r.below(2) == 0 {
        out.extend_from_slice(&random_name(r));
    } else {
        out.extend_from_slice(&[3, b'w', b'w', b'w', 0xC0, 12]);
    }
}

pub fn random_rdata(r: &mut Rng, t: u16) -> Vec<u8> {
    let mut d = Vec::new();
    match t {
        1 => (0..4).for_each(|_| d.push(r.byte())),
        28 => (0..16).for_each(|_| d.push(r.byte())),
        2 | 5 | 12 => rd_name(r, &mut d, false),
        15 => {
            d.extend_from_slice(&(r.below(65536) as u16).to_be_bytes());
            rd_name(r, &mut d, false);
        }
        16 => (0..1 + r.below(3)).for_each(|_| cstring(r, &mut d, 20)),
        13 => (0..2).for_each(|_| cstring(r, &mut d, 10)),
        6 => {
            rd_name(r, &mut d, false);
            rd_name(r, &mut d, false);
            (0..20).for_each(|_| d.push(r.byte()));
        }
        33 => {
            (0..6).for_each(|_| d.push(r.byte()));
            rd_name(r, &mut d, false);
        }
        35 => {
            (0..4).for_each(|_| d.push(r.byte()));
            (0..3).for_each(|_| cstring(r, &mut d, 10));
            rd_name(r, &mut d, false);
        }
        52 => (0..3 + r.below(10)).for_each(|_| d.push(r.byte())),
        64 | 65 => {
            d.extend_from_slice(&(r.below(3) as u16).to_be_bytes());
            rd_name(r, &mut d, true);
            let mut k = 0u16;
            for _ in 0..r.below(4) {
                k += 1 + r.below(4) as u16;
                d.extend_from_slice(&k.to_be_bytes());
                let v = rand_str(r, 6);
                d.extend_from_slice(&(v.len() as u16).to_be_bytes());
                d.extend_from_slice(&v);
            }
        }
        256 => {
            (0..4).for_each(|_| d.push(r.byte()));
            d.extend_from_slice(b"https://");
            d.extend_from_slice(&rand_str(r, 8));
        }
        257 => {
            d.push(r.below(2) as u8 * 128);
            let tag = [b"issue".as_slice(), b"iodef", b"issuewild"][r.below(3) as usize];
            d.push(tag.len() as u8);
            d.extend_from_slice(tag);
            d.extend_from_slice(&rand_str(r, 12));
        }
        41 => {
            for _ in 0..r.below(3) {
                d.extend_from_slice(&(r.below(20) as u16).to_be_bytes());
                let v = rand_str(r, 6);
                d.extend_from_slice(&(v.len() as u16).to_be_bytes());
                d.extend_from_slice(&v);
            }
        }
        24 | 46 => {
            bytes(r, &mut d, 18);
            rd_name(r, &mut d, t == 46);
            let n = r.below(6);
            bytes(r, &mut d, n);
        }
        43 | 48 => {
            bytes(r, &mut d, 4);
            let n = r.below(8);
            bytes(r, &mut d, n);
        }
        44 => {
            bytes(r, &mut d, 2);
            let n = r.below(8);
            bytes(r, &mut d, n);
        }
        47 => {
            rd_name(r, &mut d, true);
            let n = r.below(6);
            bytes(r, &mut d, n);
        }
        50 | 51 => {
            bytes(r, &mut d, 4);
            cstring(r, &mut d, 4);
            if t == 50 {
                cstring(r, &mut d, 6);
                let n = r.below(6);
                bytes(r, &mut d, n);
            }
        }
        _ => unreachable!(),
    }
    d
}

pub fn random_packet(r: &mut Rng, n: u16) -> Vec<u8> {
    let mut b = vec![0x12, 0x34, 0x81, 0x80, 0, 1, 0, 0, 0, 0, 0, 0];
    b.extend_from_slice(&wire(&[b"example", b"com"]));
    b.extend_from_slice(&[0, 1, 0, 1]);
    let mut opt = false;
    let mut count = 0;
    for _ in 0..n {
        let mut t = TYPES[r.below(TYPES.len() as u64) as usize];
        if t == 41 {
            // At most one OPT, in the additional section with a root owner.
            if opt {
                t = 1;
            } else {
                opt = true;
                continue;
            }
        }
        b.extend_from_slice(&[0xC0, 12]);
        b.extend_from_slice(&t.to_be_bytes());
        b.extend_from_slice(&[0, 1, 0, 0, 0, 60]);
        let d = random_rdata(r, t);
        b.extend_from_slice(&(d.len() as u16).to_be_bytes());
        b.extend_from_slice(&d);
        count += 1;
    }
    b[7] = count;
    if opt {
        b.push(0);
        b.extend_from_slice(&41u16.to_be_bytes());
        b.extend_from_slice(&[0x10, 0, 0, 0, 0, 0]);
        let d = random_rdata(r, 41);
        b.extend_from_slice(&(d.len() as u16).to_be_bytes());
        b.extend_from_slice(&d);
        b[11] = 1;
    }
    b
}

pub fn mutate(r: &mut Rng, b: &mut Vec<u8>) {
    for _ in 0..1 + r.below(3) {
        let i = 12 + r.below((b.len() - 12) as u64) as usize;
        match r.below(3) {
            0 => b[i] = r.byte(),
            1 => b[i] = b[i].wrapping_add(1),
            _ => b[i] = b[i].wrapping_sub(1),
        }
    }
}

/// Every record of the message `b` as (section, type, RDATA start, RDATA
/// end), or `None` if a name does not decode or the message ends early.
pub fn record_spans(b: &[u8]) -> Option<Vec<(Section, u16, usize, usize)>> {
    let be16 = |p: usize| Some(u16::from_be_bytes([*b.get(p)?, *b.get(p + 1)?]) as usize);
    let name = |p: usize| verilith_dns::parse::read_name_into(b, p, &mut Vec::new()).map(|(e, _)| e);
    let mut p = 12;
    for _ in 0..be16(4)? {
        p = name(p)? + 4;
    }
    let mut v = vec![];
    for (s, n) in [(Section::Answer, be16(6)?), (Section::Authority, be16(8)?), (Section::Additional, be16(10)?)] {
        for _ in 0..n {
            let q = name(p)?;
            let t = be16(q)? as u16;
            let len = be16(q + 8)?;
            p = q + 10;
            if p + len > b.len() {
                return None;
            }
            v.push((s, t, p, p + len));
            p += len;
        }
    }
    Some(v)
}

/// Why vdns rejects a message that c-ares accepts.
pub fn why_vdns_rejects(b: &[u8]) -> String {
    why_vdns_rejects_typed(b, &|_, _| true)
}

/// The same, where `typed` says which records c-ares decodes (the others it
/// keeps as raw bytes).
pub fn why_vdns_rejects_typed(b: &[u8], typed: &dyn Fn(Section, u16) -> bool) -> String {
    let names = "vdns rejects the message (RFC 9267 rules, as in the name differential test)";
    let Some(spans) = record_spans(b) else { return names.into() };
    for (s, t, start, end) in spans {
        if verilith_dns::rdata::read_rdata(b, t, start, end).is_some() {
            continue;
        }
        if !typed(s, t) {
            if matches!(t, 2 | 5 | 6 | 12 | 15 | 24 | 33 | 35) {
                return format!(
                    "c-ares keeps malformed RDATA raw under ARES_DNS_PARSE_*_RAW; vdns decompresses names in it and so rejects it (type {t}, RFC 9267 s5)"
                );
            }
            continue;
        }
        let ctx = b;
        // c-ares stops after the fields it knows and skips the rest.
        if (start..end).any(|e| verilith_dns::rdata::read_rdata(ctx, t, start, e).is_some()) {
            return format!("c-ares ignores trailing bytes inside RDATA (type {t})");
        }
        if t == 257 {
            return "c-ares does not check CAA tags are alphanumeric (RFC 8659 s4.1)".into();
        }
        // A pointer in the RDATA to a root octet or another pointer.
        let d = &ctx[start..end];
        if (0..d.len().saturating_sub(1)).any(|i| {
            d[i] >= 0xC0 && {
                let t = ((d[i] as usize & 0x3F) << 8) | d[i + 1] as usize;
                t < ctx.len() && ctx[t] >= 0xC0
            }
        }) {
            return "c-ares follows pointers in RDATA to another pointer (RFC 9267 s2)".into();
        }
        if matches!(t, 64 | 65) {
            return "c-ares does not require SVCB/HTTPS keys in increasing order, or allows a compressed target".into();
        }
        return format!("other: vdns rejects RDATA of type {t}");
    }
    names.into()
}
