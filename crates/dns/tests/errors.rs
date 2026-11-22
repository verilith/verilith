//! `try_parse` reports a reason for exactly the messages `parse` rejects,
//! and the reason names a real problem.
mod common;
use common::packets::*;
use common::*;
use verilith_dns::{parse, try_parse, ErrorKind, Part};

fn header(qd: u16, an: u16) -> Vec<u8> {
    let mut b = vec![0x12, 0x34, 0x81, 0x80];
    for c in [qd, an, 0, 0] {
        b.extend_from_slice(&c.to_be_bytes());
    }
    b
}

fn kind(b: &[u8]) -> (ErrorKind, usize, Part) {
    let e = try_parse(b).err().expect("rejected");
    (e.kind, e.offset, e.part)
}

#[test]
fn each_kind() {
    assert_eq!(kind(&[0; 5]).0, ErrorKind::ShortHeader);
    let mut b = header(1, 0);
    b.extend_from_slice(&[3, b'w', b'w']);
    assert_eq!(kind(&b), (ErrorKind::Truncated, 12, Part::Question(0)));
    let mut b = header(1, 0);
    b.extend_from_slice(&[0x40, 0, 0, 1, 0, 1]);
    assert_eq!(kind(&b), (ErrorKind::ReservedLabelType, 12, Part::Question(0)));
    let mut b = header(1, 0);
    b.extend_from_slice(&[0xC0, 12, 0, 1, 0, 1]);
    assert_eq!(kind(&b), (ErrorKind::PointerNotPrior, 12, Part::Question(0)));
    let mut b = header(1, 1);
    b.extend_from_slice(&[1, b'a', 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]);
    b.extend_from_slice(&[0xC0, 19]); // a second record whose owner points at the first's pointer
    let mut b2 = b.clone();
    b2[7] = 2;
    b2.extend_from_slice(&[0, 1, 0, 1, 0, 0, 0, 0, 0, 0]);
    assert_eq!(kind(&b2), (ErrorKind::PointerToPointer, 31, Part::Answer(1)));
    let mut b = header(1, 0);
    for _ in 0..5 {
        b.push(63);
        b.extend_from_slice(&[b'a'; 63]);
    }
    b.extend_from_slice(&[0, 0, 1, 0, 1]);
    assert_eq!(kind(&b).0, ErrorKind::NameTooLong);
    let mut b = header(1, 1);
    b.extend_from_slice(&[0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 9, 1, 2]);
    assert_eq!(kind(&b), (ErrorKind::Truncated, b.len(), Part::Answer(0)));
    // An NS record whose RDATA is a pointer forward.
    let mut b = header(1, 1);
    b.extend_from_slice(&[0, 0, 1, 0, 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 2, 0xC0, 40]);
    assert_eq!(kind(&b), (ErrorKind::BadRdata, 28, Part::Answer(0)));
    let mut b = header(1, 0);
    b.extend_from_slice(&[0, 0, 1, 0, 1, 0xFF]);
    assert_eq!(kind(&b), (ErrorKind::TrailingBytes, 17, Part::End));
    assert!(try_parse(&b[..17]).is_ok());
}

#[test]
fn agrees_with_parse() {
    let mut r = Rng(0xe7703);
    let mut kinds = std::collections::BTreeMap::new();
    for i in 0..300_000 {
        let n = 1 + r.below(4) as u16;
        let mut b = random_packet(&mut r, n);
        if i % 2 == 0 {
            mutate(&mut r, &mut b);
        }
        if i % 7 == 0 {
            let n = r.below(b.len() as u64) as usize;
            b.truncate(n);
        }
        match (parse(&b), try_parse(&b)) {
            (Some(_), Ok(_)) => {}
            (None, Err(e)) => {
                // A trailing-bytes verdict must be right: the message up to
                // that offset parses.
                if e.kind == ErrorKind::TrailingBytes {
                    assert!(e.offset < b.len() && parse(&b[..e.offset]).is_some(), "{b:02x?}");
                }
                *kinds.entry(format!("{:?}", e.kind)).or_insert(0) += 1;
            }
            _ => unreachable!(),
        }
    }
    println!("{kinds:?}");
}
