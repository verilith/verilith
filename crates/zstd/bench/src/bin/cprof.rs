//! Where level-N compression time goes on one file: the encoder alone
//! (match finding and entropy coding), the whole frame (with the check of
//! each block by the proven decoder), and decoding.
//! Usage: cprof LEVEL FILE
use std::time::Instant;
use verilith_zstd::enc::Enc;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let lv: i32 = a[1].parse().unwrap();
    let src = std::fs::read(&a[2]).unwrap();
    for _ in 0..3 {
        let mut e = Enc::new(&src, 1 << 21, lv);
        let mut out = Vec::new();
        let t = Instant::now();
        let mut pos = 0;
        let (mut tf, mut te) = (0f64, 0f64);
        while pos < src.len() {
            let end = (pos + 131072).min(src.len());
            out.clear();
            let t0 = Instant::now();
            e.block(&src, pos, end, 1, 4, 8, &mut out);
            te += t0.elapsed().as_secs_f64();
            pos = end;
        }
        let _ = tf;
        let el = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let v = verilith_zstd::compress_exec(&src, verilith_zstd::Params { wlog: 21, checksum: false, level: lv });
        let all = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let d = verilith_zstd::decompress(&v, 1 << 40).unwrap();
        let dt = t.elapsed().as_secs_f64();
        assert_eq!(d.len(), src.len());
        let mb = src.len() as f64 / 1e6;
        println!("enc-only {:.0} MB/s (block {:.0}), full {:.0} MB/s, decode {:.0} MB/s", mb / el, mb / te, mb / all, mb / dt);
    }
}
