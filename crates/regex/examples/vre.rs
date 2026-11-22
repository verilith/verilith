// The same protocol as tests/diff/re2ref.cc, answered by vregex.
use std::io::{BufRead, Write};

fn unhex(h: &str) -> Vec<u8> {
    (0..h.len() / 2).map(|i| u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn main() {
    let stdin = std::io::stdin();
    let mut out = std::io::BufWriter::new(std::io::stdout());
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let (p, t) = match line.find(' ') {
            Some(i) => (&line[..i], &line[i + 1..]),
            None => (&line[..], ""),
        };
        let (pat, text) = (unhex(p), unhex(t));
        match verilith_regex::Regex::new(&pat) {
            Err(verilith_regex::Error::TooBig) => writeln!(out, "TOOBIG").unwrap(),
            Err(_) => writeln!(out, "ERR").unwrap(),
            Ok(re) => match re.captures_at(&text, 0) {
                None => writeln!(out, "NOMATCH").unwrap(),
                Some(c) => {
                    let v: Vec<String> =
                        c.iter().map(|&x| if x == usize::MAX { "-1".to_string() } else { x.to_string() }).collect();
                    writeln!(out, "{}", v.join(" ")).unwrap()
                }
            },
        }
    }
}
