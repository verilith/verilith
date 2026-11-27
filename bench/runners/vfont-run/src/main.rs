//! Fonts, verilith-font's Rust API (`sanitize`) against OTS's
//! (suites/font/font.cpp): sanitize/FILE, check = size of the sanitized font
//! (each sanitizer writes its own serialization).
fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        assert!(verilith_font::sanitize(&data).is_some(), "{name} is refused");
        let len = data.len() as u64;
        r.case(format!("sanitize/{name}"), len, move || verilith_font::sanitize(std::hint::black_box(&data)).unwrap().len() as u64);
    }
    r.main();
}
