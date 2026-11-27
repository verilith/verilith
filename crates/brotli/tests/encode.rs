// Round trips through the compressor and the verified decoder.
use verilith_brotli::decompress;

fn inputs() -> Vec<Vec<u8>> {
    let mut v: Vec<Vec<u8>> = vec![vec![], b"a".to_vec(), b"hello hello hello hello".to_vec()];
    let mut x: u32 = 1;
    let mut r = Vec::new();
    for _ in 0..300_000 {
        x = x.wrapping_mul(1103515245).wrapping_add(12345);
        r.push((x >> 16) as u8 % 7 + b'a');
    }
    v.push(r);
    for f in ["alice29.txt", "asyoulik.txt", "lcet10.txt", "plrabn12.txt", "mapsdatazrh", "x", "ukkonooa", "monkey"] {
        if let Ok(d) = std::fs::read(format!("tests/data/{f}")) {
            v.push(d);
        }
    }
    v
}

#[test]
fn stored_round_trip() {
    for d in inputs() {
        let c = verilith_brotli::encoder::compress_stored(&d);
        assert_eq!(decompress(&c, 1 << 30).unwrap(), d);
    }
}

#[test]
fn compressed_round_trip() {
    for d in inputs() {
        for q in [1u32, 4, 6, 11] {
            let c = verilith_brotli::compress::compress(&d, q, 22);
            assert_eq!(decompress(&c, 1 << 30).unwrap(), d, "quality {q}, len {}", d.len());
        }
    }
}
