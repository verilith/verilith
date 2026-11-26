//! Huffman encoding alone: vqpack's `write_str` (size, then codes) against
//! ls-qpack's `lsqpack_enc_enc_str`, in ns per input byte.
use std::time::Instant;

unsafe extern "C" {
    fn lsqpack_enc_enc_str(prefix_bits: u32, dst: *mut u8, dst_len: usize, s: *const u8, len: u32) -> i32;
}

fn main() {
    let vals: Vec<Vec<u8>> = (0..200)
        .map(|i| format!("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36 {i}").into_bytes())
        .collect();
    let total: usize = vals.iter().map(|v| v.len()).sum();
    let pt = verilith_qpack::henc::ptab().unwrap();
    let mut out = Vec::with_capacity(1 << 16);
    let mut buf = vec![0u8; 1 << 16];
    for _ in 0..5 {
        let t = Instant::now();
        for _ in 0..100 {
            out.clear();
            for v in &vals {
                verilith_qpack::encoder::write_str(&mut out, 0, 8, v, pt);
            }
        }
        let ours = t.elapsed().as_nanos() as f64 / (100 * total) as f64;
        let t = Instant::now();
        let mut n = 0;
        for _ in 0..100 {
            let mut off = 0;
            for v in &vals {
                let r = unsafe { lsqpack_enc_enc_str(7, buf.as_mut_ptr().add(off), buf.len() - off, v.as_ptr(), v.len() as u32) };
                off += r as usize;
            }
            n = off;
        }
        let theirs = t.elapsed().as_nanos() as f64 / (100 * total) as f64;
        assert_eq!(&out[..], &buf[..n]);
        println!("vqpack {ours:.2} ns/byte, ls-qpack {theirs:.2} ns/byte");
    }
}
