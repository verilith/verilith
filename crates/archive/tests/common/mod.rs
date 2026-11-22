//! Small zip and tar writers for building test archives byte by byte,
//! including ones no honest tool would write.
#![allow(dead_code)]

pub fn crc32(d: &[u8]) -> u32 {
    let mut c = 0xffff_ffffu32;
    for &b in d {
        c ^= b as u32;
        for _ in 0..8 {
            c = if c & 1 != 0 { (c >> 1) ^ 0xedb8_8320 } else { c >> 1 };
        }
    }
    !c
}

/// One tar member: (name, typeflag, data, linkname).
pub type TarMember<'a> = (&'a str, u8, &'a [u8], &'a str);

pub fn tar_header(name: &[u8], typeflag: u8, size: u64, link: &[u8]) -> [u8; 512] {
    let mut h = [0u8; 512];
    h[..name.len()].copy_from_slice(name);
    h[100..108].copy_from_slice(b"0000644\0");
    h[108..116].copy_from_slice(b"0000000\0");
    h[116..124].copy_from_slice(b"0000000\0");
    h[124..136].copy_from_slice(format!("{:011o}\0", size).as_bytes());
    h[136..148].copy_from_slice(b"14524560000\0");
    h[156] = typeflag;
    h[157..157 + link.len()].copy_from_slice(link);
    h[257..263].copy_from_slice(b"ustar\0");
    h[263..265].copy_from_slice(b"00");
    fix_checksum(&mut h);
    h
}

pub fn fix_checksum(h: &mut [u8; 512]) {
    h[148..156].copy_from_slice(b"        ");
    let sum: u32 = h.iter().map(|&b| b as u32).sum();
    h[148..156].copy_from_slice(format!("{:06o}\0 ", sum).as_bytes());
}

pub fn tar(members: &[TarMember]) -> Vec<u8> {
    let mut out = Vec::new();
    for &(name, t, data, link) in members {
        out.extend_from_slice(&tar_header(name.as_bytes(), t, data.len() as u64, link.as_bytes()));
        out.extend_from_slice(data);
        out.resize(out.len().div_ceil(512) * 512, 0);
    }
    out.resize(out.len() + 1024, 0);
    out
}

/// One zip member, with every field a test may want to lie about.
#[derive(Clone)]
pub struct ZipMember {
    pub name: Vec<u8>,
    /// The name in the local header.
    pub local_name: Vec<u8>,
    pub method: u16,
    /// The bytes stored in the archive.
    pub stored: Vec<u8>,
    pub crc: u32,
    pub size: u32,
    /// Unix mode (high 16 bits of the external attributes).
    pub mode: u32,
}

pub fn stored(name: &str, data: &[u8]) -> ZipMember {
    ZipMember {
        name: name.as_bytes().to_vec(),
        local_name: name.as_bytes().to_vec(),
        method: 0,
        stored: data.to_vec(),
        crc: crc32(data),
        size: data.len() as u32,
        mode: 0o100644,
    }
}

pub fn deflated(name: &str, data: &[u8]) -> ZipMember {
    ZipMember { method: 8, stored: verilith_zlib::deflate::compress_raw(data, 6), ..stored(name, data) }
}

pub fn zip_symlink(name: &str, target: &str) -> ZipMember {
    ZipMember { mode: 0o120777, ..stored(name, target.as_bytes()) }
}

fn local(m: &ZipMember) -> Vec<u8> {
    let mut o = Vec::new();
    o.extend_from_slice(&0x04034b50u32.to_le_bytes());
    o.extend_from_slice(&20u16.to_le_bytes());
    o.extend_from_slice(&0u16.to_le_bytes());
    o.extend_from_slice(&m.method.to_le_bytes());
    o.extend_from_slice(&[0, 0, 0x21, 0x58]);
    o.extend_from_slice(&m.crc.to_le_bytes());
    o.extend_from_slice(&(m.stored.len() as u32).to_le_bytes());
    o.extend_from_slice(&m.size.to_le_bytes());
    o.extend_from_slice(&(m.local_name.len() as u16).to_le_bytes());
    o.extend_from_slice(&0u16.to_le_bytes());
    o.extend_from_slice(&m.local_name);
    o.extend_from_slice(&m.stored);
    o
}

fn central(m: &ZipMember, offset: u32) -> Vec<u8> {
    let mut o = Vec::new();
    o.extend_from_slice(&0x02014b50u32.to_le_bytes());
    o.extend_from_slice(&0x031eu16.to_le_bytes());
    o.extend_from_slice(&20u16.to_le_bytes());
    o.extend_from_slice(&0u16.to_le_bytes());
    o.extend_from_slice(&m.method.to_le_bytes());
    o.extend_from_slice(&[0, 0, 0x21, 0x58]);
    o.extend_from_slice(&m.crc.to_le_bytes());
    o.extend_from_slice(&(m.stored.len() as u32).to_le_bytes());
    o.extend_from_slice(&m.size.to_le_bytes());
    o.extend_from_slice(&(m.name.len() as u16).to_le_bytes());
    o.extend_from_slice(&[0; 8]);
    o.extend_from_slice(&(m.mode << 16).to_le_bytes());
    o.extend_from_slice(&offset.to_le_bytes());
    o.extend_from_slice(&m.name);
    o
}

fn eocd(n: u16, cd_size: u32, cd_off: u32) -> Vec<u8> {
    let mut o = Vec::new();
    o.extend_from_slice(&0x06054b50u32.to_le_bytes());
    o.extend_from_slice(&[0; 4]);
    o.extend_from_slice(&n.to_le_bytes());
    o.extend_from_slice(&n.to_le_bytes());
    o.extend_from_slice(&cd_size.to_le_bytes());
    o.extend_from_slice(&cd_off.to_le_bytes());
    o.extend_from_slice(&0u16.to_le_bytes());
    o
}

pub fn zip(members: &[ZipMember]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut offs = Vec::new();
    for m in members {
        offs.push(out.len() as u32);
        out.extend_from_slice(&local(m));
    }
    zip_with_directory(out, members, &offs)
}

/// A zip whose central directory lists `members` at the given local header
/// offsets inside `body`, whatever is really there.
pub fn zip_with_directory(body: Vec<u8>, members: &[ZipMember], offs: &[u32]) -> Vec<u8> {
    let mut out = body;
    let cd_off = out.len() as u32;
    for (m, &o) in members.iter().zip(offs) {
        out.extend_from_slice(&central(m, o));
    }
    let cd_size = out.len() as u32 - cd_off;
    out.extend_from_slice(&eocd(members.len() as u16, cd_size, cd_off));
    out
}

/// A deterministic generator for mutation tests.
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
}

pub fn fixtures() -> Vec<(String, Vec<u8>)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let mut v: Vec<(String, Vec<u8>)> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .map(|p| (p.file_name().unwrap().to_string_lossy().into_owned(), std::fs::read(&p).unwrap()))
        .collect();
    v.sort();
    v
}
