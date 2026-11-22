mod common;
use common::*;
use verilith_dns::{encode_name, parse, Message, Name, Section};

/// A real response for `example.com A`, with the answer's owner name
/// compressed to a pointer at the question name.
const EXAMPLE_COM: &[u8] = &[
    0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, // header
    7, b'e', b'x', b'a', b'm', b'p', b'l', b'e', 3, b'c', b'o', b'm', 0, 0x00, 0x01, 0x00, 0x01,
    0xC0, 0x0C, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x0E, 0x10, 0x00, 0x04, 93, 184, 216, 34,
];

#[test]
fn parses_compressed_response() {
    let m = parse(EXAMPLE_COM).expect("parses");
    assert_eq!(m.id(), 0x1234);
    assert_eq!(m.flags(), 0x8180);
    let q = m.question(0).unwrap();
    assert_eq!(q.name().to_string(), "example.com.");
    let a = m.answers().next().unwrap();
    assert_eq!(a.name, q.name);
    assert_eq!(a.ttl, 3600);
    assert_eq!(a.rdata, &[93, 184, 216, 34]);
    assert_eq!(m.answers().len(), 1);
    assert_eq!(m.authorities().len(), 0);
}

#[test]
fn rejects_pointer_loops_and_forward_pointers() {
    let mut b = vec![0u8; 12];
    b.extend_from_slice(&[0xC0, 12]);
    assert!(read_name(&b, 12).is_none());
    let loop2 = [0u8; 12].iter().copied().chain([1, b'a', 0xC0, 12]).collect::<Vec<_>>();
    assert!(read_name(&loop2, 12).is_none());
    let fwd = [0u8; 12].iter().copied().chain([0xC0, 14, 0]).collect::<Vec<_>>();
    assert!(read_name(&fwd, 12).is_none());
    // A pointer may land on a root octet (a zero-length label, as c-ares and
    // BIND accept) ...
    let to_root = [0u8; 12].iter().copied().chain([0, 0xC0, 12]).collect::<Vec<_>>();
    assert_eq!(read_name(&to_root, 13).map(|(n, e)| (n.len(), e)), Some((0, 15)));
    // ... but not on another pointer, even a valid one (RFC 9267 §2).
    let to_ptr = [0u8; 12].iter().copied().chain([1, b'a', 0, 0xC0, 12, 0xC0, 15]).collect::<Vec<_>>();
    assert!(read_name(&to_ptr, 15).is_some());
    assert!(read_name(&to_ptr, 17).is_none());
    // Reserved label types 0b01 and 0b10.
    assert!(read_name(&[0x40, 0], 0).is_none());
    assert!(read_name(&[0x80, 0], 0).is_none());
}

#[test]
fn rejects_trailing_bytes_and_impossible_counts() {
    let mut b = EXAMPLE_COM.to_vec();
    b.push(0);
    assert!(parse(&b).is_none());
    let mut c = EXAMPLE_COM.to_vec();
    c[6] = 0xFF;
    c[7] = 0xFF;
    assert!(parse(&c).is_none());
}

#[test]
fn enforces_255_octet_limit_across_pointers() {
    let mut b = Vec::new();
    for _ in 0..4 {
        b.push(63);
        b.extend(std::iter::repeat(b'x').take(63));
    }
    b.push(0);
    assert!(read_name(&b, 0).is_none());
    let mut ok = b[..64 * 3].to_vec();
    ok.push(61);
    ok.extend(std::iter::repeat(b'y').take(61));
    ok.push(0);
    assert_eq!(read_name(&ok, 0).unwrap().0.len(), 4);
    let mut split = b[..64 * 2].to_vec();
    split.push(0);
    let start = split.len();
    split.push(63);
    split.extend(std::iter::repeat(b'z').take(63));
    split.push(63);
    split.extend(std::iter::repeat(b'z').take(63));
    split.extend_from_slice(&[0xC0, 0]);
    assert!(read_name(&split, start).is_none());
}

#[test]
fn builder_rejects_bad_input_and_leaves_message_unchanged() {
    let mut m = Message::new(1, 0);
    m.push_question("example.com", 1, 1).unwrap();
    assert!(m.add_question(b"\x03com", 1, 1).is_err()); // no root octet
    assert!(m.add_question(b"\x03com\x00\x00", 1, 1).is_err()); // trailing byte
    assert!(m.add_question(b"\xC0\x00", 1, 1).is_err()); // pointer
    assert!(m.push_question(&"a".repeat(64), 1, 1).is_err()); // label too long
    assert!(m.push_record(Section::Answer, "example.com", 1, 1, 0, &vec![0; 65536]).is_err());
    assert_eq!(m.questions().len(), 1);
    assert_eq!(m.to_bytes().len(), 12 + 13 + 4);
}

#[test]
fn presentation_format() {
    assert_eq!(encode_name("example.com.").unwrap(), wire(&[b"example", b"com"]));
    assert_eq!(encode_name("example.com").unwrap(), wire(&[b"example", b"com"]));
    assert_eq!(encode_name(".").unwrap(), vec![0]);
    assert_eq!(encode_name(r"a\.b.c").unwrap(), wire(&[b"a.b", b"c"]));
    assert_eq!(encode_name(r"\000x").unwrap(), wire(&[b"\0x"]));
    assert!(encode_name("a..b").is_err());
    let w = wire(&[b"a.b", b"\x01c", b"x y"]);
    assert_eq!(Name::from_wire(&w).to_string(), r"a\.b.\001c.x y.");
    assert_eq!(Name::from_wire(&[0]).to_string(), ".");
}

#[test]
fn roundtrip_random_messages() {
    let mut r = Rng(0x5eed);
    let mut reuse = Message::new(0, 0);
    for _ in 0..2000 {
        let m = random_message(&mut r);
        let plain = m.to_bytes();
        assert!(same(&parse(&plain).unwrap(), &m));
        let packed = encode_compressed(&m);
        assert!(packed.len() <= plain.len());
        assert!(same(&parse(&packed).unwrap(), &m), "compressed decode");
        assert!(reuse.parse_into(&packed));
        assert!(same(&reuse, &m));
    }
}

#[test]
fn random_and_mutated_input_never_panics() {
    let mut r = Rng(0xfeed);
    let mut accepted = 0;
    let mut reuse = Message::new(0, 0);
    for i in 0..200_000 {
        let mut b = if i % 2 == 0 {
            encode_compressed(&random_message(&mut r))
        } else {
            (0..r.below(80)).map(|_| r.byte()).collect()
        };
        for _ in 0..r.below(4) {
            if !b.is_empty() {
                let j = r.below(b.len() as u64) as usize;
                b[j] = r.byte();
            }
        }
        let parsed = parse(&b);
        assert_eq!(reuse.parse_into(&b), parsed.is_some());
        if let Some(m) = parsed {
            accepted += 1;
            assert!(same(&parse(&m.to_bytes()).unwrap(), &m));
            assert!(same(&reuse, &m));
            for q in m.questions() {
                let _ = q.name().to_string();
            }
        }
        for p in 0..b.len() {
            let _ = read_name(&b, p);
        }
    }
    assert!(accepted > 1000);
}

#[test]
fn rejects_c_ares_1164_pointer_chain_packet() {
    let mut b = vec![0x12, 0x34, 0x81, 0x80, 0, 1, 0x10, 0, 0, 0, 0, 0];
    b.extend_from_slice(&[1, b'a', 0, 0, 1, 0, 1]);
    let chain_start = b.len();
    b.extend_from_slice(&[0xC0, 12]);
    for i in 1..8000 {
        let prev = chain_start + 2 * (i - 1);
        b.extend_from_slice(&[0xC0 | (prev >> 8) as u8, prev as u8]);
    }
    let top = b.len() - 2;
    for _ in 0..0x1000 {
        b.extend_from_slice(&[0xC0 | (top >> 8) as u8, top as u8, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]);
    }
    let t = std::time::Instant::now();
    assert!(parse(&b).is_none());
    assert!(read_name(&b, top).is_none());
    assert!(t.elapsed() < std::time::Duration::from_millis(50));
}

#[test]
fn verified_compression_roundtrips() {
    // A response compressed the usual way comes out byte for byte the same.
    let m = parse(EXAMPLE_COM).unwrap();
    assert_eq!(m.to_bytes_compressed(), EXAMPLE_COM);
    let mut r = Rng(0xc0de);
    let (mut plain_total, mut packed_total) = (0, 0);
    for _ in 0..5000 {
        let m = random_message(&mut r);
        let plain = m.to_bytes();
        let packed = m.to_bytes_compressed();
        assert!(same(&parse(&packed).unwrap(), &m));
        assert!(packed.len() <= encode_compressed(&m).len());
        plain_total += plain.len();
        packed_total += packed.len();
    }
    println!("random messages: {plain_total} bytes uncompressed, {packed_total} compressed");
}
