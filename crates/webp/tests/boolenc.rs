//! The boolean encoder against the decoder, on pseudo-random bits.
use verilith_webp::enc_bool::BoolWriter;
use verilith_webp::vp8bool::BoolReader;

#[test]
fn round_trip() {
    let mut seed: u64 = 0x1234_5678_9abc_def1;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for n in [0usize, 1, 7, 100, 5000, 100_000] {
        let mut w = BoolWriter::new();
        let mut ws = Vec::new();
        for _ in 0..n {
            let r = next();
            let prob = (r & 0xff) as u8;
            // Bits that follow their probability, as in real streams.
            let bit = ((r >> 8) & 0xff) as u8 >= prob;
            w.put(prob, bit);
            ws.push((prob, bit));
        }
        let buf = w.finish();
        let mut rd = BoolReader::new(&buf, 0, buf.len());
        for (i, &(prob, bit)) in ws.iter().enumerate() {
            assert_eq!(rd.get_bit(&buf, prob), bit, "bit {i} of {n}");
        }
    }
}
