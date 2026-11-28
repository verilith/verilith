//! How long each compressor takes on a 16 KiB HTML page, by level.
fn main() {
    let page: String = (0..320).map(|i| format!("<p>paragraph {i} of a page that proxies compress</p>\n")).collect();
    let b = page.as_bytes();
    let t = |name: &str, f: &dyn Fn() -> Vec<u8>| {
        let n = 20;
        let s = std::time::Instant::now();
        let mut len = 0;
        for _ in 0..n {
            len = f().len();
        }
        println!("{name:12} {:8.1} us  {len} bytes", s.elapsed().as_micros() as f64 / n as f64);
    };
    for q in [0u32, 1, 2, 3, 4, 5, 6] {
        t(&format!("br q{q}"), &|| verilith_brotli::compress::compress(b, q, 22));
    }
    for q in [0u32, 1, 2, 4] {
        t(&format!("br q{q} w18"), &|| verilith_brotli::compress::compress(b, q, 18));
    }
    let mut p = verilith_brotli::compress::params(1);
    p.dict = false;
    t("br q1 nodict", &|| verilith_brotli::compress::compress_with(b, p.clone(), 22));
    let tiny = b"<p>tiny</p>";
    t("br q1 tiny", &|| verilith_brotli::compress::compress(tiny, 1, 22));
    for l in [1, 3] {
        t(&format!("zstd {l}"), &|| verilith_zstd::compress::compress(b, l, false));
    }
    for l in [1u32, 6] {
        t(&format!("gzip {l}"), &|| verilith_zlib::gzip_compress(b, l));
    }
}
