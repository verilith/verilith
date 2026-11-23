//! The two-stage parser with small index windows (128 bytes) against the
//! one-pass parser, so documents cross many window refills.
use verilith_json::parser::{parse_into, Tape};
use verilith_json::stage2::parse2_window;

fn same(s: &[u8]) {
    let mut a = Tape::with_capacity(0);
    let ra = parse_into(s, true, &mut a);
    for win in [128usize, 256, 384, 65536] {
        let mut b = Tape::with_capacity(0);
        let mut idx = Vec::new();
        let rb = parse2_window(s, &mut b, &mut idx, win);
        assert_eq!(ra.is_ok(), rb.is_ok(), "accept differs, win {win}: {:?}", String::from_utf8_lossy(&s[..s.len().min(200)]));
        if let (Ok(x), Ok(y)) = (ra, rb) {
            assert_eq!(x, y);
            assert_eq!(format!("{:?}", a.toks), format!("{:?}", b.toks), "tokens differ, win {win}");
            assert_eq!(a.strs, b.strs);
            assert_eq!(a.aux, b.aux);
        }
    }
}

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn gen_doc(seed: &mut u64, out: &mut Vec<u8>, depth: u32) {
    match rng(seed) % if depth == 0 { 6 } else { 9 } {
        0 => out.extend_from_slice(b"null"),
        1 => out.extend_from_slice(b"true"),
        2 => out.extend_from_slice(format!("{}", rng(seed) as i64 % 100000).as_bytes()),
        3 => out.extend_from_slice(b"-12.5e-3"),
        4 | 5 => {
            out.push(b'"');
            let n = rng(seed) % 300;
            for _ in 0..n {
                match rng(seed) % 20 {
                    0 => out.extend_from_slice(b"\\\""),
                    1 => out.extend_from_slice(b"\\\\"),
                    2 => out.extend_from_slice(b"\\u00e9"),
                    3 => out.extend_from_slice("é€😀".as_bytes()),
                    4 => out.extend_from_slice(b"]},:["),
                    _ => out.push(b'a' + (rng(seed) % 26) as u8),
                }
            }
            out.push(b'"');
        }
        6 | 7 => {
            out.push(b'[');
            let n = rng(seed) % 12;
            for i in 0..n {
                if i > 0 {
                    out.push(b',');
                }
                if rng(seed) % 3 == 0 {
                    out.extend_from_slice(b"  \n ");
                }
                gen_doc(seed, out, depth - 1);
            }
            out.push(b']');
        }
        _ => {
            out.push(b'{');
            let n = rng(seed) % 10;
            for i in 0..n {
                if i > 0 {
                    out.push(b',');
                }
                out.extend_from_slice(format!("\"k{}\":", rng(seed) % 1000).as_bytes());
                gen_doc(seed, out, depth - 1);
            }
            out.push(b'}');
        }
    }
}

#[test]
fn random_documents() {
    let mut seed = 0x1234_5678_9abc_def1u64;
    for _ in 0..400 {
        let mut d = Vec::new();
        gen_doc(&mut seed, &mut d, 5);
        same(&d);
        // Damage one byte; both parsers must still agree.
        if !d.is_empty() {
            for b in [b'\x01', b'"', b'\\', b'\xff', b']', b' '] {
                let mut e = d.clone();
                let i = (rng(&mut seed) as usize) % e.len();
                e[i] = b;
                same(&e);
            }
            same(&d[..(rng(&mut seed) as usize) % d.len()]);
        }
    }
}

#[test]
fn long_strings_and_late_errors() {
    for n in [0usize, 1, 63, 64, 127, 128, 129, 255, 256, 383, 384, 385, 1000, 5000] {
        let body = "x".repeat(n);
        same(format!("\"{body}\"").as_bytes());
        same(format!("[\"{body}\",1]").as_bytes());
        same(format!("[\"{body}\x01\"]").as_bytes());
        same(format!("[\"{body}").as_bytes());
        same(format!("[\"{body}\\").as_bytes());
        same(format!("[\"{body}\\\"\"]").as_bytes());
        let mut v = format!("[\"{body}\"]").into_bytes();
        v.insert(2 + n / 2, 0xff);
        same(&v);
        same(format!("[{}1]", "1,".repeat(n)).as_bytes());
        same(format!("{}1{}", "[".repeat(n.min(900)), "]".repeat(n.min(900))).as_bytes());
        same(format!("{}{}", " ".repeat(n), "[1] x").as_bytes());
        same(format!("[1]{}", " ".repeat(n)).as_bytes());
        same(format!("[1]{}\x01", " ".repeat(n)).as_bytes());
        same(format!("\u{feff}[\"{body}\"]").as_bytes());
    }
}
