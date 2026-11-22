//! Layout tables (GDEF, GSUB, GPOS) built by hand.
mod common;
use common::*;

fn words(ws: &[u16]) -> Vec<u8> {
    let mut v = Vec::new();
    for w in ws {
        be16(&mut v, *w);
    }
    v
}

/// Version 1.2: a format 2 glyph class definition and one mark glyph set.
fn gdef() -> Vec<u8> {
    words(&[
        1, 2, 14, 0, 0, 0, 24, // header
        2, 1, 1, 2, 3, // @14 class definition: glyphs 1..2 are marks
        1, 1, 0, 8, // @24 mark glyph sets: one, at 8
        1, 1, 2, // @32 coverage: glyph 2
    ])
}

/// One script and feature; a single substitution, and a chaining context
/// (format 3) reached through an extension, using mark filtering set 0.
fn gsub() -> Vec<u8> {
    let mut v = words(&[1, 0, 10, 30, 46]);
    // @10 script list
    v.extend(words(&[1]));
    v.extend(b"DFLT");
    v.extend(words(&[8, 4, 0, 0, 0xFFFF, 1, 0]));
    // @30 feature list
    v.extend(words(&[1]));
    v.extend(b"liga");
    v.extend(words(&[8, 0, 2, 0, 1]));
    // @46 lookup list
    v.extend(words(&[2, 6, 26]));
    // @52 lookup 0: single substitution, delta 1 on glyph 1
    v.extend(words(&[1, 0, 1, 8, 1, 6, 1, 1, 1, 1]));
    // @72 lookup 1: extension, mark filtering set 0
    v.extend(words(&[7, 0x10, 1, 10, 0]));
    // @82 extension to a chaining context at +8
    v.extend(words(&[1, 6, 0, 8]));
    // @90 chain format 3: one input coverage, one lookup record
    v.extend(words(&[3, 0, 1, 16, 0, 1, 0, 0]));
    // @106 coverage format 2: glyphs 1..2
    v.extend(words(&[2, 1, 1, 2, 0]));
    v
}

/// A pair adjustment (format 1) whose value record has a device table.
fn gpos() -> Vec<u8> {
    words(&[
        1, 0, 0, 0, 10, // header
        1, 4, // @10 lookup list
        2, 0, 1, 8, // @14 lookup: pair adjustment
        1, 28, 0x0044, 0, 1, 12, // @22 pair positioning, coverage at +28
        1, 2, 10, 8, // @34 pair set: glyph 2, advance 10, device at +8
        12, 13, 1, 0, // @42 device table
        1, 1, 1, // @50 coverage: glyph 1
    ])
}

fn with_layout(gdef: Vec<u8>, gsub: Vec<u8>, gpos: Vec<u8>) -> Vec<u8> {
    let mut ts = tables(&[Vec::new(), triangle(), triangle()]);
    ts.push((b"GDEF", gdef));
    ts.push((b"GSUB", gsub));
    ts.push((b"GPOS", gpos));
    sfnt(0x0001_0000, &ts)
}

fn has_table(font: &[u8], tag: &[u8; 4]) -> bool {
    let n = u16::from_be_bytes([font[4], font[5]]) as usize;
    (0..n).any(|i| &font[12 + 16 * i..16 + 16 * i] == tag)
}

#[test]
fn keeps_well_formed_layout_tables() {
    let f = with_layout(gdef(), gsub(), gpos());
    if let Ok(p) = std::env::var("VFONT_DUMP") {
        std::fs::write(p, &f).unwrap();
    }
    let out = verilith_font::sanitize(&f).expect("font refused");
    assert!(verilith_font::font::check_font(&out));
    for tag in [b"GDEF", b"GSUB", b"GPOS"] {
        assert!(has_table(&out, tag));
    }
    assert_eq!(verilith_font::sanitize(&out).as_deref(), Some(&out[..]));
}

#[test]
fn refuses_a_lookup_record_naming_no_lookup() {
    let mut g = gsub();
    assert_eq!(&g[102..106], &[0, 0, 0, 0]);
    g[105] = 2;
    assert!(verilith_font::sanitize(&with_layout(gdef(), g, gpos())).is_none());
}

#[test]
fn refuses_a_mark_filtering_set_gdef_does_not_define() {
    let mut g = gsub();
    g[81] = 1;
    assert!(verilith_font::sanitize(&with_layout(gdef(), g, gpos())).is_none());
}

#[test]
fn refuses_a_substitute_glyph_that_does_not_exist() {
    let mut g = gsub();
    assert_eq!(&g[64..66], &[0, 1]);
    g[65] = 3; // delta 3 with 3 glyphs
    assert!(verilith_font::sanitize(&with_layout(gdef(), g, gpos())).is_none());
}

#[test]
fn refuses_a_device_table_that_runs_off_the_end() {
    let mut p = gpos();
    p[45] = 200; // end size 200: needs 25 words
    assert!(verilith_font::sanitize(&with_layout(gdef(), gsub(), p)).is_none());
}

#[test]
fn repairs_a_default_language_system() {
    // Required feature 0 in a table without features, as in GNU Unifont.
    let mut g = words(&[1, 0, 10, 0, 0, 1]);
    g.extend(b"DFLT");
    g.extend(words(&[8, 4, 0, 0, 0, 0]));
    let out = verilith_font::sanitize(&with_layout(gdef(), g, gpos())).expect("font refused");
    assert!(has_table(&out, b"GSUB"));
}

#[test]
fn damaged_layout_tables_never_yield_a_malformed_font() {
    let (d, s, p) = (gdef(), gsub(), gpos());
    let mut kept = 0;
    let mut refused = 0;
    for which in 0..3 {
        let len = [d.len(), s.len(), p.len()][which];
        for i in 0..len {
            for x in [0x01u8, 0x02, 0x80, 0xFF] {
                let mut t = [d.clone(), s.clone(), p.clone()];
                t[which][i] ^= x;
                let [a, b, c] = t;
                match verilith_font::sanitize(&with_layout(a, b, c)) {
                    Some(out) => {
                        assert!(verilith_font::font::check_font(&out), "table {which} byte {i} ^ {x:#x}");
                        kept += 1;
                    }
                    None => refused += 1,
                }
            }
        }
        for n in 0..len {
            let mut t = [d.clone(), s.clone(), p.clone()];
            t[which].truncate(n);
            let [a, b, c] = t;
            if let Some(out) = verilith_font::sanitize(&with_layout(a, b, c)) {
                assert!(verilith_font::font::check_font(&out), "table {which} cut at {n}");
            }
        }
    }
    assert!(kept > 0 && refused > kept);
}
