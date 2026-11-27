//! URLs, verilith-url's Rust API (`Url::parse_bytes`, `href`) against ada's
//! C++ API (suites/url/ada.cpp): parse/FILE parses every URL of FILE (one
//! per line), reads href of the valid ones and drops them. check = valid
//! URLs * 2^32 + total href length, as suites/url/url.c.
use verilith_url::Url;

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".txt") else { continue };
        let text = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = text.len() as u64;
        let lines: Vec<Vec<u8>> = text
            .split(|&c| c == b'\n')
            .map(|l| l.strip_suffix(b"\r").unwrap_or(l).to_vec())
            .filter(|l| !l.is_empty())
            .collect();
        r.case(format!("parse/{stem}"), len, move || {
            let (mut ok, mut href) = (0u64, 0u64);
            for l in &lines {
                if let Some(u) = Url::parse_bytes(std::hint::black_box(l), None) {
                    ok += 1;
                    href += u.href().len() as u64;
                }
            }
            (ok << 32) + href
        });
    }
    r.main();
}
