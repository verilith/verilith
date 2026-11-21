//! PNG, vpng side of the comparison with libpng (suites/png/libpng.c):
//! decode a PNG held in memory to 8-bit RGBA.

/// Must match strided_sum in suites/png/libpng.c.
fn strided_sum(p: &[u8]) -> u64 {
    let mut s = p.len() as u64;
    for i in (0..p.len()).step_by(61) {
        s = s.wrapping_mul(31).wrapping_add(p[i] as u64);
    }
    s
}

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = name.strip_suffix(".png") else { continue };
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = data.len() as u64;
        r.case(format!("rgba8/{stem}"), len, move || {
            let (_, px) = verilith_png::top::decode(std::hint::black_box(&data), verilith_png::top::PixelFormat::Rgba8, 1 << 34).unwrap();
            strided_sum(&px)
        });
    }
    r.main();
}
