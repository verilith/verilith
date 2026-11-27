//! Snappy, verilith-snappy's Rust API against snappy's C API
//! (suites/snappy/snappy.c), the same cases and check values, into reused
//! buffers: uncompress/FILE `decompress_into`, validate/FILE `validate`,
//! compress/FILE `compress_into`.
fn main() {
    let mode = vbrun::mode("uncompress");
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let orig = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = orig.len();
        let case = format!("{mode}/{name}");
        if mode == "compress" {
            let mut out = vec![0u8; verilith_snappy::max_compressed_length(len)];
            let m = verilith_snappy::compress_into(&orig, &mut out).unwrap();
            let mut back = vec![0u8; len + 1];
            assert!(verilith_snappy::decompress_into(&out[..m], &mut back) == Ok(len) && back[..len] == orig[..], "{case}");
            r.case(case, len as u64, move || verilith_snappy::compress_into(std::hint::black_box(&orig), &mut out).unwrap() as u64);
        } else {
            let z = std::fs::read(format!("{dir}/snappy/{name}.sz")).unwrap();
            let mut out = vec![0u8; len + 1];
            let n = verilith_snappy::decompress_into(&z, &mut out).unwrap();
            assert!(n == len && out[..n] == orig[..], "{case}");
            if mode == "validate" {
                r.case(case, len as u64, move || {
                    assert!(verilith_snappy::validate(std::hint::black_box(&z)));
                    1
                });
            } else {
                r.case(case, len as u64, move || {
                    let n = verilith_snappy::decompress_into(std::hint::black_box(&z), &mut out).unwrap();
                    vbrun::mix(n as u64, &out[..n])
                });
            }
        }
    }
    r.main();
}
