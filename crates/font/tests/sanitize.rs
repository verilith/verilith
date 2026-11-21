mod common;
use common::*;

fn accepted(input: &[u8]) -> Vec<u8> {
    let out = verilith_font::sanitize(input).expect("font refused");
    assert!(verilith_font::font::check_font(&out), "output is not well formed");
    assert_eq!(verilith_font::sanitize(&out).as_deref(), Some(&out[..]), "not idempotent");
    out
}

#[test]
fn accepts_a_small_font() {
    accepted(&font());
}

#[test]
fn drops_unknown_tables() {
    let mut ts = tables(&[Vec::new(), triangle()]);
    ts.push((b"DSIG", vec![0, 0, 0, 1, 0, 0, 0, 0]));
    ts.push((b"zzzz", vec![1, 2, 3]));
    assert_eq!(accepted(&sfnt(0x0001_0000, &ts)), accepted(&font()));
}

#[test]
fn cuts_bytes_after_a_glyph() {
    let mut g = triangle();
    g.extend_from_slice(&[0xAA; 40]);
    let out = accepted(&sfnt(0x0001_0000, &tables(&[Vec::new(), g])));
    assert_eq!(out, accepted(&font()));
}

#[test]
fn refuses_a_glyph_that_contains_itself() {
    let f = sfnt(0x0001_0000, &tables(&[Vec::new(), composite(1)]));
    assert!(verilith_font::sanitize(&f).is_none());
    let f = sfnt(0x0001_0000, &tables(&[Vec::new(), composite(2), composite(1)]));
    assert!(verilith_font::sanitize(&f).is_none());
}

#[test]
fn accepts_a_composite_and_corrects_maxp() {
    let f = sfnt(0x0001_0000, &tables(&[Vec::new(), triangle(), composite(1)]));
    let out = accepted(&f);
    // maxp of the output: maxComponentElements and maxComponentDepth are 1,
    // though the input said 0 and 0... find maxp through the directory.
    let n = u16::from_be_bytes([out[4], out[5]]) as usize;
    let mut maxp = None;
    for i in 0..n {
        let r = 12 + 16 * i;
        if &out[r..r + 4] == b"maxp" {
            maxp = Some(u32::from_be_bytes([out[r + 8], out[r + 9], out[r + 10], out[r + 11]]) as usize);
        }
    }
    let m = maxp.unwrap();
    let rd = |o: usize| u16::from_be_bytes([out[m + o], out[m + o + 1]]);
    assert!(rd(10) >= 3, "maxCompositePoints");
    assert!(rd(12) >= 1, "maxCompositeContours");
    assert!(rd(28) >= 1, "maxComponentElements");
    assert!(rd(30) >= 1, "maxComponentDepth");
}

#[test]
fn refuses_a_component_that_does_not_exist() {
    let f = sfnt(0x0001_0000, &tables(&[Vec::new(), composite(7)]));
    assert!(verilith_font::sanitize(&f).is_none());
}

/// The same font wrapped as WOFF with every table stored uncompressed.
fn woff(sfnt_bytes: &[u8]) -> Vec<u8> {
    let n = u16::from_be_bytes([sfnt_bytes[4], sfnt_bytes[5]]) as usize;
    let mut recs = Vec::new();
    let mut total = 12 + 16 * n;
    for i in 0..n {
        let r = 12 + 16 * i;
        let rd = |o: usize| u32::from_be_bytes(sfnt_bytes[r + o..r + o + 4].try_into().unwrap());
        let (off, len) = (rd(8) as usize, rd(12) as usize);
        recs.push((sfnt_bytes[r..r + 4].to_vec(), rd(4), sfnt_bytes[off..off + len].to_vec()));
        total += (len + 3) / 4 * 4;
    }
    let mut body = Vec::new();
    let mut dir = Vec::new();
    let start = 44 + 20 * n;
    for (tag, sum, data) in &recs {
        dir.extend_from_slice(tag);
        be32(&mut dir, (start + body.len()) as u32);
        be32(&mut dir, data.len() as u32);
        be32(&mut dir, data.len() as u32);
        be32(&mut dir, *sum);
        body.extend_from_slice(data);
        while body.len() % 4 != 0 {
            body.push(0);
        }
    }
    let mut out = Vec::new();
    out.extend_from_slice(b"wOFF");
    out.extend_from_slice(&sfnt_bytes[0..4]);
    be32(&mut out, (start + body.len()) as u32);
    be16(&mut out, n as u16);
    be16(&mut out, 0);
    be32(&mut out, total as u32);
    out.extend_from_slice(&[0; 24]);
    out.extend_from_slice(&dir);
    out.extend_from_slice(&body);
    out
}

#[test]
fn woff_gives_the_same_font() {
    let f = font();
    assert_eq!(accepted(&woff(&f)), accepted(&f));
}

#[test]
fn woff_with_bytes_after_the_end_is_refused() {
    let mut w = woff(&font());
    w.extend_from_slice(&[0; 8]);
    assert!(verilith_font::sanitize(&w).is_none());
    // also when the header owns up to the longer length
    let len = w.len() as u32;
    w[8..12].copy_from_slice(&len.to_be_bytes());
    assert!(verilith_font::sanitize(&w).is_none());
}

/// A collection holding the font once.
fn ttc(sfnt_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"ttcf");
    be32(&mut out, 0x0001_0000);
    be32(&mut out, 1);
    be32(&mut out, 16);
    let n = u16::from_be_bytes([sfnt_bytes[4], sfnt_bytes[5]]) as usize;
    let mut f = sfnt_bytes.to_vec();
    for i in 0..n {
        let r = 12 + 16 * i + 8;
        let off = u32::from_be_bytes(f[r..r + 4].try_into().unwrap()) + 16;
        f[r..r + 4].copy_from_slice(&off.to_be_bytes());
    }
    out.extend_from_slice(&f);
    out
}

#[test]
fn collection_member_by_index() {
    let f = font();
    let c = ttc(&f);
    assert_eq!(verilith_font::sanitize_index(&c, 0), Some(accepted(&f)));
    assert!(verilith_font::sanitize_index(&c, 1).is_none());
}

#[test]
fn damaged_fonts_never_yield_a_malformed_font() {
    let f = font();
    let mut kept = 0;
    for i in 0..f.len() {
        for x in [0x01u8, 0x80, 0xFF] {
            let mut g = f.clone();
            g[i] ^= x;
            if let Some(out) = verilith_font::sanitize(&g) {
                assert!(verilith_font::font::check_font(&out), "byte {i} ^ {x:#x}");
                kept += 1;
            }
        }
    }
    // Most damage is repaired (checksums are recomputed, bad fields reset).
    assert!(kept > 0);
    for n in 0..f.len() {
        if let Some(out) = verilith_font::sanitize(&f[..n]) {
            assert!(verilith_font::font::check_font(&out), "cut at {n}");
        }
    }
    let w = woff(&f);
    for i in 0..w.len() {
        let mut g = w.clone();
        g[i] ^= 0xFF;
        if let Some(out) = verilith_font::sanitize(&g) {
            assert!(verilith_font::font::check_font(&out), "woff byte {i}");
        }
    }
}

#[test]
fn empty_and_tiny_inputs() {
    for n in 0..64 {
        assert!(verilith_font::sanitize(&vec![0u8; n]).is_none());
        assert!(verilith_font::sanitize(&vec![0xFFu8; n]).is_none());
    }
    for magic in [b"wOFF", b"wOF2", b"ttcf", b"OTTO"] {
        assert!(verilith_font::sanitize(magic).is_none());
    }
}
