//! Unverified prototype: vdns's exact pointer rule and 255-octet
//! limit, but no allocation per label or per RDATA. Names are written in
//! uncompressed wire form into one arena; RDATA is a range into the input.
pub struct Rr { pub name: (u32, u16), pub rtype: u16, pub rclass: u16, pub ttl: u32, pub rdata: (u32, u16) }
pub struct Msg { pub id: u16, pub flags: u16, pub counts: [u16; 4], pub names: Vec<u8>, pub qs: Vec<((u32, u16), u16, u16)>, pub rrs: Vec<Rr> }

#[inline]
fn name(b: &[u8], pos: usize, arena: &mut Vec<u8>) -> Option<((u32, u16), usize)> {
    let start = arena.len();
    let (mut p, mut seg, mut saved, mut wire) = (pos, pos, None, 1usize);
    loop {
        let c = *b.get(p)?;
        if c == 0 { arena.push(0); return Some(((start as u32, (arena.len() - start) as u16), saved.unwrap_or(p + 1))); }
        if c >= 192 {
            let t = ((c as usize - 192) << 8) | *b.get(p + 1)? as usize;
            if t >= seg { return None; }
            saved.get_or_insert(p + 2); p = t; seg = t;
        } else if c >= 64 { return None; } else {
            let l = c as usize;
            let lab = b.get(p..p + 1 + l)?;
            wire += 1 + l; if wire > 255 { return None; }
            arena.extend_from_slice(lab); p += 1 + l;
        }
    }
}
#[inline] fn u16at(b: &[u8], p: usize) -> Option<u16> { Some(u16::from_be_bytes(b.get(p..p + 2)?.try_into().ok()?)) }

pub fn parse(b: &[u8]) -> Option<Msg> {
    let c = [u16at(b, 4)?, u16at(b, 6)?, u16at(b, 8)?, u16at(b, 10)?];
    let mut m = Msg { id: u16at(b, 0)?, flags: u16at(b, 2)?, counts: c, names: Vec::with_capacity(b.len() * 2), qs: Vec::with_capacity(c[0] as usize), rrs: Vec::with_capacity(c[1] as usize + c[2] as usize + c[3] as usize) };
    let mut p = 12;
    for _ in 0..c[0] { let (n, e) = name(b, p, &mut m.names)?; m.qs.push((n, u16at(b, e)?, u16at(b, e + 2)?)); p = e + 4; }
    for _ in 0..(c[1] as u32 + c[2] as u32 + c[3] as u32) {
        let (n, e) = name(b, p, &mut m.names)?;
        let f = b.get(e..e + 10)?;
        let rl = u16::from_be_bytes([f[8], f[9]]);
        if b.len() - (e + 10) < rl as usize { return None; }
        m.rrs.push(Rr { name: n, rtype: u16::from_be_bytes([f[0], f[1]]), rclass: u16::from_be_bytes([f[2], f[3]]), ttl: u32::from_be_bytes([f[4], f[5], f[6], f[7]]), rdata: ((e + 10) as u32, rl) });
        p = e + 10 + rl as usize;
    }
    Some(m)
}
