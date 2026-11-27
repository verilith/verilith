//! WebP, verilith-webp's Rust API (`decode_to`, RGBA) against libwebp's
//! decode API (suites/webp/webp.c): rgba/FILE, check = strided sum of the
//! pixels. `decode_to` returns a new buffer each call; libwebp's
//! `WebPDecodeRGBAInto` writes into the caller's.
fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".webp") else { continue };
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = data.len() as u64;
        r.case(format!("rgba/{stem}"), len, move || {
            let (px, _, _) = verilith_webp::decode_to(std::hint::black_box(&data), verilith_webp::Mode::RGBA).unwrap();
            vbrun::strided_sum(&px)
        });
    }
    r.main();
}
