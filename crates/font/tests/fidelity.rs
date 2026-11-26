//! The two properties beyond well-formedness: the output draws the same
//! as the input (`same::check_same`, which `sanitize` runs on everything
//! it returns), and a valid font is accepted.
mod common;
use common::*;
use verilith_font::{build, font, same};

/// The tables of an sfnt file, in directory order.
fn tables_of(f: &[u8]) -> Vec<([u8; 4], Vec<u8>)> {
    let n = u16::from_be_bytes([f[4], f[5]]) as usize;
    (0..n)
        .map(|i| {
            let r = &f[12 + 16 * i..28 + 16 * i];
            let off = u32::from_be_bytes([r[8], r[9], r[10], r[11]]) as usize;
            let len = u32::from_be_bytes([r[12], r[13], r[14], r[15]]) as usize;
            ([r[0], r[1], r[2], r[3]], f[off..off + len].to_vec())
        })
        .collect()
}

/// Lays tables out in the order given, with a gap after each, every
/// checksum zero and `checkSumAdjustment` left as it is: a font that is
/// valid in every table but not in its layout.
fn sloppy(version: u32, ts: &[([u8; 4], Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::new();
    be32(&mut out, version);
    be16(&mut out, ts.len() as u16);
    be16(&mut out, 0);
    be16(&mut out, 0);
    be16(&mut out, 0);
    let mut off = 12 + 16 * ts.len() + 8;
    for (tag, d) in ts {
        out.extend_from_slice(tag);
        be32(&mut out, 0);
        be32(&mut out, off as u32);
        be32(&mut out, d.len() as u32);
        off += d.len() + 5;
    }
    out.extend_from_slice(&[0xEE; 8]);
    for (_, d) in ts {
        out.extend_from_slice(d);
        out.extend_from_slice(&[0xEE; 5]);
    }
    out
}

fn table_index(ts: &[build::Table], tag: &[u8; 4]) -> usize {
    build::lookup(&ts.to_vec_clone(), u32::from_be_bytes(*tag)).unwrap()
}

trait CloneTables {
    fn to_vec_clone(&self) -> Vec<build::Table>;
}

impl CloneTables for [build::Table] {
    fn to_vec_clone(&self) -> Vec<build::Table> {
        self.iter().map(|t| build::Table { tag: t.tag, data: t.data.clone() }).collect()
    }
}

#[test]
fn the_output_draws_the_same() {
    let f = sfnt(0x0001_0000, &tables(&[Vec::new(), triangle(), composite(1)]));
    let ts = build::read_font(&f, 0).unwrap();
    let out = verilith_font::sanitize(&f).unwrap();
    assert!(same::check_same(&ts, &out));
}

#[test]
fn a_changed_outline_or_metric_is_noticed() {
    let f = font();
    let ts = build::read_font(&f, 0).unwrap();
    let out = verilith_font::sanitize(&f).unwrap();
    assert!(same::check_same(&ts, &out));
    // Change one byte of the input at a time in the tables that decide
    // how glyphs are drawn: the output no longer draws the same as it.
    for (tag, at) in [
        (b"glyf", 12),   // a contour end point of the triangle
        (b"glyf", 20),   // one of its coordinates
        (b"hmtx", 5),    // an advance width
        (b"head", 19),   // unitsPerEm
        (b"hhea", 5),    // the ascender
        (b"cmap", 30),   // a character's glyph
        (b"maxp", 21),   // maxFunctionDefs
    ] {
        let mut ts2 = ts.to_vec_clone();
        let i = table_index(&ts2, tag);
        ts2[i].data[at] ^= 0x01;
        assert!(!same::check_same(&ts2, &out), "{} byte {at}", String::from_utf8_lossy(tag));
    }
}

#[test]
fn a_valid_font_is_accepted_in_any_layout() {
    let good = verilith_font::sanitize(&font()).unwrap();
    let mut ts = tables_of(&good);
    ts.reverse();
    ts.insert(2, (*b"DSIG", vec![0, 0, 0, 1, 0, 0, 0, 0]));
    ts.push((*b"zzzz", vec![1, 2, 3]));
    let i = ts.iter().position(|t| &t.0 == b"head").unwrap();
    ts[i].1[8..12].copy_from_slice(&[0x12, 0x34, 0x56, 0x78]);
    let f = sloppy(0x0001_0000, &ts);
    assert_eq!(verilith_font::sanitize(&f).as_deref(), Some(&good[..]));
}

#[test]
fn laying_out_again_keeps_every_table() {
    let good = verilith_font::sanitize(&font()).unwrap();
    let ts = build::read_font(&good, 0).unwrap();
    let out = verilith_font::relay(&ts).expect("a valid font is laid out again");
    assert!(font::check_font(&out));
    assert!(same::check_same(&ts, &out));
    assert_eq!(out, good);
}
