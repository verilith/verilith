//! The filters against libvips itself: `scripts/vips_ref.py` runs an
//! installed libvips on test images as imgproxy calls it, and this checks
//! that the proxy's verified code gives the same bytes. Ignored unless
//! `VERILITH_VIPS_REF` names the script's output directory; set
//! `VERILITH_VIPS_C=1` when the script ran with `VIPS_NOVECTOR=1`.
//! Checked against libvips 8.15.1 (with Highway): blur and premultiplied
//! alpha agree byte for byte on both its vector and its C path. Sharpen
//! goes through libvips's colour conversions, which the proxy computes as
//! current libvips's source does (single-precision matrices, `powf`);
//! 8.15 computes some of them in double precision, so there a few
//! lightness values land one LabS step apart (about 0.6% of colours) and
//! a few output bytes in 100,000 move by a level or two. The checks below
//! allow exactly that much for sharpen, and nothing for the rest.
use verilith_imgproxy::filter::{blur_rgba, pixelate_rgba, premul_rgba, unpremul_rgba};
use verilith_imgproxy::mask;

fn ours(px: &[u8], w: usize, h: usize, blur: f64, sharp: f64, pix: usize, c_path: bool) -> Vec<u8> {
    let pre = blur > 0.0 || sharp > 0.0;
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
    if sharp > 0.0 {
        px = verilith_imgproxy::colour::sharpen_rgba(&px, w, h, sharp).unwrap();
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
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "in") && p.file_name().unwrap().to_str().unwrap().starts_with(|c: char| c.is_ascii_digit())).collect();
    names.sort();
    let mut bad = 0;
    let (mut sh_bytes, mut sh_diff, mut sh_max) = (0, 0, 0);
    for p in &names {
        let stem = p.file_stem().unwrap().to_str().unwrap().to_string();
        let parts: Vec<&str> = stem.split('_').collect();
        let (w, h) = parts[1].split_once('x').unwrap();
        let (w, h): (usize, usize) = (w.parse().unwrap(), h.parse().unwrap());
        let blur: f64 = parts[2][2..].parse().unwrap();
        let sharp: f64 = parts[3][2..].parse().unwrap();
        let pix: usize = parts[4][3..].parse().unwrap();
        if old_shrink && pix > 1 {
            continue;
        }
        let src = std::fs::read(p).unwrap();
        let want = std::fs::read(p.with_extension("out")).unwrap();
        let got = ours(&src, w, h, blur, sharp, pix, c_path);
        if sharp > 0.0 {
            sh_bytes += want.len();
            sh_diff += got.iter().zip(&want).filter(|(a, b)| a != b).count();
            sh_max = sh_max.max(got.iter().zip(&want).map(|(a, b)| (*a as i32 - *b as i32).abs()).max().unwrap_or(0));
            continue;
        }
        if got != want {
            let diff = got.iter().zip(&want).filter(|(a, b)| a != b).count();
            let maxd = got.iter().zip(&want).map(|(a, b)| (*a as i32 - *b as i32).abs()).max().unwrap_or(0);
            eprintln!("{stem}: {diff} of {} bytes differ, by up to {maxd}", want.len());
            bad += 1;
        }
    }
    assert_eq!(bad, 0, "{bad} of {} cases differ", names.len());
    eprintln!("sharpen: {sh_diff} of {sh_bytes} bytes differ, by up to {sh_max}");
    assert!(sh_diff * 10000 <= sh_bytes && sh_max <= 2, "sharpen: {sh_diff} of {sh_bytes} bytes differ, by up to {sh_max}");
}

#[test]
#[ignore]
fn colour_conversions_as_libvips() {
    use verilith_imgproxy::colour::{labs_to_srgb, srgb_to_labs};
    let Ok(dir) = std::env::var("VERILITH_VIPS_REF") else { return };
    let want = std::fs::read(format!("{dir}/labs.out")).unwrap();
    let mut bad = 0;
    for i in 0..1 << 24 {
        let (r, g, b) = ((i >> 16) as u8, (i >> 8) as u8, i as u8);
        let (l, a, bb) = srgb_to_labs(r, g, b);
        let w = &want[i * 6..i * 6 + 6];
        let got = [l.to_le_bytes(), a.to_le_bytes(), bb.to_le_bytes()].concat();
        if got != w {
            bad += 1;
        }
    }
    let src = std::fs::read(format!("{dir}/srgb.in")).unwrap();
    let want = std::fs::read(format!("{dir}/srgb.out")).unwrap();
    let mut bad2 = 0;
    for (k, p) in src.chunks_exact(6).enumerate() {
        let v = |j: usize| i16::from_le_bytes([p[j], p[j + 1]]);
        let (r, g, b) = labs_to_srgb(v(0) as u16, v(2), v(4));
        if [r, g, b] != want[k * 3..k * 3 + 3] {
            bad2 += 1;
        }
    }
    eprintln!("sRGB to LabS: {bad} of 2^24 differ; LabS to sRGB: {bad2} of 2^20");
    // See the note at the top: libvips 8.15's double-precision matrices.
    assert!(bad * 100 <= 1 << 24 && bad2 * 10000 <= 1 << 20, "sRGB to LabS: {bad} of 2^24 differ; LabS to sRGB: {bad2} of 2^20");
}

#[test]
#[ignore]
fn attention_as_libvips() {
    let Ok(dir) = std::env::var("VERILITH_VIPS_REF") else { return };
    let list = std::fs::read_to_string(format!("{dir}/smart.txt")).unwrap();
    let ver = std::fs::read_to_string(format!("{dir}/version")).unwrap();
    let ver: Vec<u32> = ver.trim().split('.').map(|v| v.parse().unwrap()).collect();
    // Before 8.17 vips_shrink divides exactly (see the pixelate note).
    let exact = (ver[0], ver[1]) < (8, 17);
    let (mut same, mut all) = (0, 0);
    for line in list.lines() {
        let v: Vec<usize> = line.split(' ').map(|t| t.parse().unwrap()).collect();
        let (i, w, h, alpha, cw, ch, ax, ay) = (v[0], v[1], v[2], v[3] == 1, v[4], v[5], v[6], v[7]);
        let px = std::fs::read(format!("{dir}/smart{i:03}.rgba")).unwrap();
        let got = verilith_imgproxy::proxy::attention_point(&px, w, h, alpha, cw, ch, exact);
        all += 1;
        if got == (ax, ay) {
            same += 1;
        } else {
            eprintln!("{line}: ours {got:?}");
        }
    }
    eprintln!("attention: {same} of {all} the same");
    assert_eq!(same, all);
}
