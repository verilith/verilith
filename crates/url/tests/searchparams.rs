//! The verified URLSearchParams parser and serializer against the plain
//! Rust ones they replaced, on random inputs, plus round trips.
use verilith_url::searchparams::UrlSearchParams;

fn old_decode(s: &[u8]) -> Vec<u8> {
    fn hex(c: u8) -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if c == b'%' && i + 2 < s.len() {
            if let (Some(h), Some(l)) = (hex(s[i + 1]), hex(s[i + 2])) {
                out.push(h * 16 + l);
                i += 3;
                continue;
            }
        }
        out.push(if c == b'+' { b' ' } else { c });
        i += 1;
    }
    out
}

fn old_encode(s: &[u8], out: &mut Vec<u8>) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    for &c in s {
        if c.is_ascii_alphanumeric() || matches!(c, b'*' | b'-' | b'.' | b'_') {
            out.push(c);
        } else if c == b' ' {
            out.push(b'+');
        } else {
            out.extend_from_slice(&[b'%', HEX[(c >> 4) as usize], HEX[(c & 15) as usize]]);
        }
    }
}

fn old_parse(input: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut list = Vec::new();
    let input = input.strip_prefix(b"?").unwrap_or(input);
    for part in input.split(|&c| c == b'&') {
        if part.is_empty() {
            continue;
        }
        let (k, v) = match part.iter().position(|&c| c == b'=') {
            Some(e) => (&part[..e], &part[e + 1..]),
            None => (part, &b""[..]),
        };
        list.push((old_decode(k), old_decode(v)));
    }
    list
}

fn old_serialize(list: &[(Vec<u8>, Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::new();
    for (i, (k, v)) in list.iter().enumerate() {
        if i > 0 {
            out.push(b'&');
        }
        old_encode(k, &mut out);
        out.push(b'=');
        old_encode(v, &mut out);
    }
    out
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn matches_old_and_round_trips() {
    let alphabet: &[u8] = b"a=&%+2Fz?  ~*._-\xc3\xa9\x00";
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for _ in 0..200_000 {
        let n = (rng.next() % 24) as usize;
        let s: Vec<u8> = (0..n).map(|_| alphabet[(rng.next() % alphabet.len() as u64) as usize]).collect();
        let p = UrlSearchParams::parse(&s);
        assert_eq!(p.list, old_parse(&s), "{:?}", String::from_utf8_lossy(&s));
        let b = p.to_bytes();
        assert_eq!(b, old_serialize(&p.list));
        assert_eq!(UrlSearchParams::parse(&b).list, p.list);
        // Arbitrary byte pairs survive serialize then parse.
        let mut q = UrlSearchParams::default();
        for _ in 0..(rng.next() % 4) {
            let k: Vec<u8> = (0..rng.next() % 6).map(|_| rng.next() as u8).collect();
            let v: Vec<u8> = (0..rng.next() % 6).map(|_| rng.next() as u8).collect();
            q.append(&k, &v);
        }
        assert_eq!(UrlSearchParams::parse(&q.to_bytes()).list, q.list);
    }
}

#[test]
fn examples() {
    let p = UrlSearchParams::parse(b"?a=b&&c&d=e=f&%zz=%41+%2B&=");
    let want: Vec<(Vec<u8>, Vec<u8>)> = vec![
        (b"a".to_vec(), b"b".to_vec()),
        (b"c".to_vec(), b"".to_vec()),
        (b"d".to_vec(), b"e=f".to_vec()),
        (b"%zz".to_vec(), b"A +".to_vec()),
        (b"".to_vec(), b"".to_vec()),
    ];
    assert_eq!(p.list, want);
    assert_eq!(p.to_bytes(), b"a=b&c=&d=e%3Df&%25zz=A+%2B&=".to_vec());
}
