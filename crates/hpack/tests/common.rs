//! Test helpers: decoding whole blocks through `feed`, split in various
//! ways, and a small (unverified) HPACK encoder for generated blocks.
#![allow(dead_code)]
use verilith_hpack::decoder::{Decoder, Feed};
use verilith_hpack::htables::{HUFF_CODE, HUFF_LEN};

pub type Hdr = (Vec<u8>, Vec<u8>, bool);

/// Decodes one header block, fed in pieces of the given sizes (cycled;
/// empty means all at once). `None` on a decoding error.
pub fn decode_block(d: &mut Decoder, block: &[u8], pieces: &[usize]) -> Option<Vec<Hdr>> {
    let mut out = Vec::new();
    let mut chunks: Vec<&[u8]> = Vec::new();
    let mut i = 0;
    let mut k = 0;
    while i < block.len() {
        let n = if pieces.is_empty() { block.len() } else { pieces[k % pieces.len()].max(1) };
        let e = (i + n).min(block.len());
        chunks.push(&block[i..e]);
        i = e;
        k += 1;
    }
    if chunks.is_empty() {
        chunks.push(&[]);
    }
    for (ci, c) in chunks.iter().enumerate() {
        let fin = ci + 1 == chunks.len();
        let mut c: &[u8] = c;
        loop {
            match d.feed(c, fin) {
                Feed::Field(n, never) => {
                    out.push((d.name().to_vec(), d.value().to_vec(), never));
                    c = &c[n..];
                }
                Feed::More => break,
                Feed::Final => break,
                Feed::Bad => return None,
            }
        }
    }
    d.end_block();
    Some(out)
}

pub fn table(d: &Decoder) -> Vec<(Vec<u8>, Vec<u8>)> {
    d.table.ents.iter().map(|e| (e.name.clone(), e.value.clone())).collect()
}

pub fn huff_encode(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut acc: u64 = 0;
    let mut nb = 0;
    for &c in s {
        acc = (acc << HUFF_LEN[c as usize]) | HUFF_CODE[c as usize] as u64;
        nb += HUFF_LEN[c as usize] as u32;
        while nb >= 8 {
            out.push((acc >> (nb - 8)) as u8);
            nb -= 8;
            acc &= (1u64 << nb) - 1;
        }
    }
    if nb > 0 {
        out.push(((acc << (8 - nb)) | ((1u64 << (8 - nb)) - 1)) as u8);
    }
    out
}

pub fn enc_int(out: &mut Vec<u8>, first: u8, n: u32, v: u64) {
    let k = (1u64 << n) - 1;
    if v < k {
        out.push(first | v as u8);
        return;
    }
    out.push(first | k as u8);
    let mut v = v - k;
    while v >= 128 {
        out.push((v % 128) as u8 | 0x80);
        v /= 128;
    }
    out.push(v as u8);
}

pub fn enc_str(out: &mut Vec<u8>, s: &[u8], huff: bool) {
    if huff {
        let h = huff_encode(s);
        enc_int(out, 0x80, 7, h.len() as u64);
        out.extend_from_slice(&h);
    } else {
        enc_int(out, 0, 7, s.len() as u64);
        out.extend_from_slice(s);
    }
}

pub fn dehex(s: &str) -> Vec<u8> {
    let h: String = s.chars().filter(|c| c.is_ascii_hexdigit()).collect();
    (0..h.len()).step_by(2).map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap()).collect()
}

/// A small deterministic PRNG (xorshift64*).
pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}
