//! JPEG, verilith-jpeg's Rust API (`decode_to`, into a reused RGB buffer)
//! against the TurboJPEG API (suites/jpeg/jpeg.c): rgb/FILE, check =
//! strided sum of the pixels.
fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".jpg") else { continue };
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = data.len() as u64;
        let pic = verilith_jpeg::decode(&data).unwrap();
        let mut out = vec![0u8; pic.px.len()];
        match verilith_jpeg::decode::decode_to(&data, &mut out) {
            Ok(Some((_, _, 3))) => {}
            other => panic!("{name}: not an RGB picture of the expected size ({other:?})"),
        }
        r.case(format!("rgb/{stem}"), len, move || {
            verilith_jpeg::decode::decode_to(std::hint::black_box(&data), &mut out).unwrap().unwrap();
            vbrun::strided_sum(&out)
        });
    }
    r.main();
}
