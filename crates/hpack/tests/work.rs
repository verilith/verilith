//! The work bound in practice: a block that resumes in the buffered path
//! with `fin` set costs time linear in its length. Before the bound was
//! proven, each field there copied the rest of the block, so this took
//! time quadratic in it (40,000 fields: 16 ms instead of 0.1 ms).
use std::time::Instant;
use verilith_hpack::decoder::{Decoder, Feed};

/// A literal field ("a: b") split after its second byte, then `n` indexed
/// fields in the same piece as the literal's end, decoded with `fin`.
fn split_block(n: usize) -> usize {
    let mut d = Decoder::new().unwrap();
    let mut block = vec![0x00, 0x01, b'a', 0x01, b'b'];
    block.extend(std::iter::repeat(0x82).take(n));
    let (first, rest) = block.split_at(2);
    assert!(matches!(d.feed(first, false), Feed::More));
    let mut input = rest;
    let mut fields = 0;
    loop {
        match d.feed(input, true) {
            Feed::Field(used, _) => {
                // The literal's field uses exactly its last three bytes.
                if fields == 0 {
                    assert_eq!(used, 3);
                    assert_eq!((d.name(), d.value()), (&b"a"[..], &b"b"[..]));
                } else {
                    assert_eq!(used, 1);
                    assert_eq!((d.name(), d.value()), (&b":method"[..], &b"GET"[..]));
                }
                fields += 1;
                input = &input[used..];
            }
            Feed::Final => break,
            _ => panic!("the block decodes"),
        }
    }
    fields
}

#[test]
fn resumed_block_is_linear() {
    let n = 200_000;
    let t = Instant::now();
    assert_eq!(split_block(n), n + 1);
    // Linear: well under a second even unoptimized. Quadratic copied
    // about 2 * 10^10 bytes here.
    assert!(t.elapsed().as_secs() < 5, "took {:?}", t.elapsed());
}
