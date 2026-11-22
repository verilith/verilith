//! Differential testing on stable Rust: every file of the directories
//! given, and `N` mutations of each (byte flips, insertions and deletions
//! of markup characters, splices), through verilith-xml and libexpat.
//! Prints each disagreement once per kind with a minimal sample.
//!
//!   cargo run --release --example mutate -- N DIR...
use std::collections::BTreeMap;
use vxml_fuzz::{unexplained, Diff};

const TOKENS: &[&[u8]] = &[
    b"<", b">", b"&", b";", b"'", b"\"", b"=", b"/", b"<!--", b"-->", b"<![CDATA[", b"]]>", b"<?", b"?>", b"&#",
    b"&#x", b"&amp;", b"&lt;", b"<!DOCTYPE a [", b"]>", b"<!ENTITY e '", b"&e;", b"%", b"<!ATTLIST a b CDATA '",
    b" ", b"\r", b"\n", b"\t", b"\0", b"\xc3\xa9", b"\xff", b"\xef\xbb\xbf", b"x", b"a", b":", b"-", b"1",
];

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
}

fn mutate(r: &mut Rng, d: &[u8], others: &[Vec<u8>]) -> Vec<u8> {
    let mut v = d.to_vec();
    for _ in 0..1 + r.below(3) {
        let at = r.below(v.len() + 1);
        match r.below(5) {
            0 if !v.is_empty() && at < v.len() => v[at] = r.next() as u8,
            1 if !v.is_empty() && at < v.len() => {
                let n = 1 + r.below(8).min(v.len() - at - 1);
                v.drain(at..at + n.min(v.len() - at));
            }
            2 => {
                let t = TOKENS[r.below(TOKENS.len())];
                v.splice(at..at, t.iter().cloned());
            }
            3 => {
                let o = &others[r.below(others.len())];
                if !o.is_empty() {
                    let a = r.below(o.len());
                    let b = (a + 1 + r.below(64)).min(o.len());
                    v.splice(at..at, o[a..b].iter().cloned());
                }
            }
            _ => {
                if at < v.len() {
                    let b = (at + 1 + r.below(16)).min(v.len());
                    let piece = v[at..b].to_vec();
                    v.splice(b..b, piece);
                }
            }
        }
    }
    v
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a[1].parse().unwrap();
    let mut files = Vec::new();
    for d in &a[2..] {
        for e in walk(std::path::Path::new(d)) {
            if let Ok(b) = std::fs::read(&e) {
                if b.len() <= 64 * 1024 {
                    files.push(b);
                }
            }
        }
    }
    let mut seen: BTreeMap<String, (usize, Vec<u8>)> = BTreeMap::new();
    let mut only_expat: Vec<Vec<u8>> = Vec::new();
    let mut r = Rng(0x9E3779B97F4A7C15);
    let mut runs = 0usize;
    for i in 0..files.len() {
        let mut inputs = vec![files[i].clone()];
        for _ in 0..n {
            inputs.push(mutate(&mut r, &files[i], &files));
        }
        for d in inputs {
            runs += 1;
            if let Some(diff) = unexplained(&d) {
                let key = match &diff {
                    Diff::OnlyOurs => format!(
                        "accepted only by verilith-xml (expat: {}){}",
                        vxml_fuzz::expat_reason(&d),
                        if d.iter().any(|&c| c >= 0x80) { ", non-ASCII" } else { ", ASCII only" }
                    ),
                    Diff::OnlyExpat => format!(
                        "accepted only by expat (verilith-xml: {})",
                        verilith_xml::parse(&d).err().map_or(String::new(), |e| format!("{:?}", e.kind))
                    ),
                    Diff::Infoset(..) => "different infoset".to_string(),
                };
                if diff == Diff::OnlyExpat {
                    only_expat.push(d.clone());
                }
                let e = seen.entry(key).or_insert((0, d.clone()));
                e.0 += 1;
                if d.len() < e.1.len() {
                    e.1 = d;
                }
            }
        }
    }
    println!("{runs} documents, {} files, {} unexplained kinds of difference", files.len(), seen.len());
    for (k, (count, sample)) in &seen {
        println!("{k}: {count}; smallest: {:?}", String::from_utf8_lossy(sample));
        if std::env::var("BYTES").is_ok() {
            println!("  bytes: {:?}", sample);
        }
    }
    if !seen.is_empty() {
        std::process::exit(1);
    }
    only_expat.sort_by_key(|d| d.len());
    only_expat.dedup();
    if std::env::var("SHOW").is_ok() {
        for d in only_expat.iter().take(60) {
            let e = verilith_xml::parse(d).unwrap_err();
            let at = e.offset.min(d.len());
            let lo = at.saturating_sub(30);
            let hi = (at + 30).min(d.len());
            println!("  only expat, ours fails at {}: ...{:?}...", e.offset, String::from_utf8_lossy(&d[lo..hi]));
        }
    }
}

fn walk(p: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    if p.is_dir() {
        for e in std::fs::read_dir(p).unwrap().flatten() {
            out.extend(walk(&e.path()));
        }
    } else if p.extension().map_or(false, |e| e == "xml") {
        out.push(p.to_path_buf());
    }
    out
}
