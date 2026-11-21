//! A tiny TrueType font built by hand, for tests that must not depend on
//! font files being installed.
#![allow(dead_code)]

pub fn be16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_be_bytes());
}

pub fn be32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_be_bytes());
}

fn checksum(d: &[u8]) -> u32 {
    let mut s = 0u32;
    for c in d.chunks(4) {
        let mut w = [0u8; 4];
        w[..c.len()].copy_from_slice(c);
        s = s.wrapping_add(u32::from_be_bytes(w));
    }
    s
}

/// Lays tables out as an sfnt file with correct checksums.
pub fn sfnt(version: u32, tables: &[(&[u8; 4], Vec<u8>)]) -> Vec<u8> {
    let mut ts: Vec<&(&[u8; 4], Vec<u8>)> = tables.iter().collect();
    ts.sort_by_key(|t| *t.0);
    let n = ts.len() as u16;
    let mut out = Vec::new();
    be32(&mut out, version);
    be16(&mut out, n);
    let mut p = 1u16;
    let mut e = 0u16;
    while p * 2 <= n {
        p *= 2;
        e += 1;
    }
    be16(&mut out, p * 16);
    be16(&mut out, e);
    be16(&mut out, n * 16 - p * 16);
    let mut off = 12 + 16 * ts.len();
    let mut head_at = 0;
    for t in &ts {
        out.extend_from_slice(t.0);
        be32(&mut out, checksum(&t.1));
        be32(&mut out, off as u32);
        be32(&mut out, t.1.len() as u32);
        if t.0 == b"head" {
            head_at = off;
        }
        off += (t.1.len() + 3) / 4 * 4;
    }
    for t in &ts {
        out.extend_from_slice(&t.1);
        while out.len() % 4 != 0 {
            out.push(0);
        }
    }
    let adj = 0xB1B0_AFBAu32.wrapping_sub(checksum(&out));
    if head_at != 0 {
        out[head_at + 8..head_at + 12].copy_from_slice(&adj.to_be_bytes());
    }
    out
}

/// A glyph with one triangular contour.
pub fn triangle() -> Vec<u8> {
    let mut g = Vec::new();
    be16(&mut g, 1); // numberOfContours
    for v in [0i16, 0, 500, 500] {
        be16(&mut g, v as u16); // bounding box
    }
    be16(&mut g, 2); // endPtsOfContours
    be16(&mut g, 0); // instructionLength
    g.extend_from_slice(&[1, 1, 1]); // flags: on curve, 16-bit deltas
    for v in [0i16, 500, -250] {
        be16(&mut g, v as u16); // x
    }
    for v in [0i16, 0, 500] {
        be16(&mut g, v as u16); // y
    }
    g
}

/// A composite glyph with one component, glyph `of`.
pub fn composite(of: u16) -> Vec<u8> {
    let mut g = Vec::new();
    be16(&mut g, 0xFFFF);
    for v in [0i16, 0, 500, 500] {
        be16(&mut g, v as u16);
    }
    be16(&mut g, 0x0002); // flags: ARGS_ARE_XY_VALUES, byte arguments
    be16(&mut g, of);
    g.extend_from_slice(&[0, 0]);
    g
}

/// The tables of a font whose glyphs are `glyphs` (glyph 0 first; an empty
/// vector is an empty glyph). The letter A maps to glyph 1.
pub fn tables(glyphs: &[Vec<u8>]) -> Vec<(&'static [u8; 4], Vec<u8>)> {
    let ng = glyphs.len() as u16;
    let mut glyf = Vec::new();
    let mut loca = Vec::new();
    for g in glyphs {
        be32(&mut loca, glyf.len() as u32);
        glyf.extend_from_slice(g);
        while glyf.len() % 4 != 0 {
            glyf.push(0);
        }
    }
    be32(&mut loca, glyf.len() as u32);

    let mut head = Vec::new();
    be32(&mut head, 0x0001_0000);
    be32(&mut head, 0x0001_0000);
    be32(&mut head, 0);
    be32(&mut head, 0x5F0F_3CF5);
    be16(&mut head, 0x000B);
    be16(&mut head, 1000);
    head.extend_from_slice(&[0; 16]);
    for v in [0i16, 0, 500, 500] {
        be16(&mut head, v as u16);
    }
    be16(&mut head, 0);
    be16(&mut head, 8);
    be16(&mut head, 2);
    be16(&mut head, 1); // long loca
    be16(&mut head, 0);

    let mut maxp = Vec::new();
    be32(&mut maxp, 0x0001_0000);
    be16(&mut maxp, ng);
    for v in [3u16, 1, 3, 1, 2, 0, 0, 0, 0, 0, 0, 1, 1] {
        be16(&mut maxp, v);
    }

    let mut hhea = Vec::new();
    be32(&mut hhea, 0x0001_0000);
    for v in [800i16, -200, 0, 600, 0, 0, 500, 1, 0, 0, 0, 0, 0, 0, 0] {
        be16(&mut hhea, v as u16);
    }
    be16(&mut hhea, ng);

    let mut hmtx = Vec::new();
    for _ in 0..ng {
        be16(&mut hmtx, 600);
        be16(&mut hmtx, 0);
    }

    let mut cmap = Vec::new();
    be16(&mut cmap, 0);
    be16(&mut cmap, 1);
    be16(&mut cmap, 3);
    be16(&mut cmap, 1);
    be32(&mut cmap, 12);
    // format 4, two segments: A, and the final 0xFFFF
    for v in [4u16, 32, 0, 4, 4, 1, 0] {
        be16(&mut cmap, v);
    }
    for v in [0x41u16, 0xFFFF, 0, 0x41, 0xFFFF] {
        be16(&mut cmap, v);
    }
    be16(&mut cmap, 1u16.wrapping_sub(0x41)); // idDelta: A -> glyph 1
    be16(&mut cmap, 1);
    be16(&mut cmap, 0);
    be16(&mut cmap, 0);

    let mut name = Vec::new();
    for v in [0u16, 0, 6] {
        be16(&mut name, v);
    }

    let mut post = Vec::new();
    be32(&mut post, 0x0003_0000);
    post.extend_from_slice(&[0; 28]);

    let mut os2 = Vec::new();
    be16(&mut os2, 0); // version
    be16(&mut os2, 600);
    be16(&mut os2, 400);
    be16(&mut os2, 5);
    os2.extend_from_slice(&[0; 70]);

    vec![
        (b"head", head),
        (b"maxp", maxp),
        (b"hhea", hhea),
        (b"hmtx", hmtx),
        (b"cmap", cmap),
        (b"name", name),
        (b"post", post),
        (b"OS/2", os2),
        (b"glyf", glyf),
        (b"loca", loca),
    ]
}

/// A complete small font: an empty glyph 0 and a triangle.
pub fn font() -> Vec<u8> {
    sfnt(0x0001_0000, &tables(&[Vec::new(), triangle()]))
}
