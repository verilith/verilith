//! The README's example.
use verilith_hpack::decoder::{Decoder, Feed};

#[test]
fn readme_example() {
    let mut d = Decoder::new().unwrap();
    let block: &[u8] = &[0x82, 0x86, 0x84];
    let mut input = block;
    let mut got = Vec::new();
    loop {
        match d.feed(input, true) {
            Feed::Field(used, _never) => {
                got.push((d.name().to_vec(), d.value().to_vec()));
                input = &input[used..];
            }
            Feed::Final => break,
            Feed::More => panic!("More with fin"),
            Feed::Bad => panic!("COMPRESSION_ERROR"),
        }
    }
    d.end_block();
    let want: Vec<(Vec<u8>, Vec<u8>)> = [(":method", "GET"), (":scheme", "http"), (":path", "/")]
        .iter()
        .map(|(n, v)| (n.as_bytes().to_vec(), v.as_bytes().to_vec()))
        .collect();
    assert_eq!(got, want);
}
