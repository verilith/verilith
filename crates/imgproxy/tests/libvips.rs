//! The filters against libvips itself: `scripts/vips_ref.py` runs an
//! installed libvips on test images as imgproxy calls it, and this checks
//! that the proxy's verified code gives the same bytes. Ignored unless
//! `VERILITH_VIPS_REF` names the script's output directory; set
//! `VERILITH_VIPS_C=1` when the script ran with `VIPS_NOVECTOR=1`.
//! Checked against libvips 8.15.1 (with Highway): blur and premultiplied
//! alpha agree byte for byte on both its vector and its C path.
use verilith_imgproxy::filter::{blur_rgba, pixelate_rgba, premul_rgba, unpremul_rgba};
use verilith_imgproxy::mask;

fn ours(px: &[u8], w: usize, h: usize, blur: f64, pix: usize, c_path: bool) -> Vec<u8> {
    let pre = blur > 0.0;
    let mut px = if pre { premul_rgba(px) } else { px.to_vec() };
    if blur > 0.0 {
        let g = if c_path {
            mask::gaussmat(blur, 0.2).map(|(m, s)| (m, s as i64))
        } else {
            mask::gaussblur(blur).unwrap()
        };
        if let Some((g, d)) = g.filter(|_| blur >= 0.2) {
            px = blur_rgba(&g, d, &px, w, h);
        }
    }
    let px = pixelate_rgba(px, w, h, pix);
    if pre {
        unpremul_rgba(&px)
    } else {
        px
    }
}

#[test]
#[ignore]
fn same_bytes_as_libvips() {
    let Ok(dir) = std::env::var("VERILITH_VIPS_REF") else { return };
    let c_path = std::env::var("VERILITH_VIPS_C").is_ok();
    // libvips 8.17 changed vips_shrink's 8-bit rounding to the fixed point
    // the proxy follows; before it, pixelate rounds differently.
    let ver = std::fs::read_to_string(format!("{dir}/version")).unwrap();
    let ver: Vec<u32> = ver.trim().split('.').map(|v| v.parse().unwrap()).collect();
    let old_shrink = (ver[0], ver[1]) < (8, 17);
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "in")).collect();
    names.sort();
    let mut bad = 0;
    for p in &names {
        let stem = p.file_stem().unwrap().to_str().unwrap().to_string();
        let parts: Vec<&str> = stem.split('_').collect();
        let (w, h) = parts[1].split_once('x').unwrap();
        let (w, h): (usize, usize) = (w.parse().unwrap(), h.parse().unwrap());
        let blur: f64 = parts[2][2..].parse().unwrap();
        let pix: usize = parts[3][3..].parse().unwrap();
        if old_shrink && pix > 1 {
            continue;
        }
        let src = std::fs::read(p).unwrap();
        let want = std::fs::read(p.with_extension("out")).unwrap();
        let got = ours(&src, w, h, blur, pix, c_path);
        if got != want {
            let diff = got.iter().zip(&want).filter(|(a, b)| a != b).count();
            let maxd = got.iter().zip(&want).map(|(a, b)| (*a as i32 - *b as i32).abs()).max().unwrap_or(0);
            eprintln!("{stem}: {diff} of {} bytes differ, by up to {maxd}", want.len());
            bad += 1;
        }
    }
    assert_eq!(bad, 0, "{bad} of {} cases differ", names.len());
}
