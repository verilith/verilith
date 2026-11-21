//! `why FILE`: says which stage refuses a font (a debugging aid).
fn main() {
    let a = std::env::args().nth(1).expect("usage: why FILE");
    let input = std::fs::read(a).expect("read");
    let Some(ts) = verilith_font::build::read_font(&input, 0) else {
        println!("refused while reading the container");
        return;
    };
    let tags: Vec<String> =
        ts.iter().map(|t| String::from_utf8_lossy(&t.tag.to_be_bytes()).into_owned()).collect();
    println!("tables read: {}", tags.join(" "));
    let get = |tag: u32| verilith_font::build::lookup(&ts, tag).map(|i| &ts[i].data[..]);
    let Some(out) = verilith_font::build::build_tables(&ts) else {
        println!("refused while rebuilding the tables");
        // Try the parts one at a time.
        let (Some(head), Some(maxp), Some(cmap)) =
            (get(verilith_font::spec::T_HEAD), get(verilith_font::spec::T_MAXP), get(verilith_font::spec::T_CMAP))
        else {
            println!("  a required table is missing");
            return;
        };
        if head.len() < 54 || maxp.len() < 6 {
            println!("  head or maxp is too short");
            return;
        }
        let ng = u16::from_be_bytes([maxp[4], maxp[5]]);
        println!("  cmap: {}", verilith_font::build::rebuild_cmap(cmap, ng).is_some());
        if let (Some(glyf), Some(loca)) = (get(verilith_font::spec::T_GLYF), get(verilith_font::spec::T_LOCA)) {
            let fmt = u16::from_be_bytes([head[50], head[51]]);
            match verilith_font::build::rebuild_glyf(glyf, loca, fmt, ng) {
                Some((g, l, f)) => {
                    println!("  glyf: true");
                    let lim = verilith_font::graph::glyf_limits(&g, &l, f, ng);
                    println!("  glyph limits: {}", lim.is_some());
                }
                None => println!("  glyf: false"),
            }
        }
        if let Some(cff) = get(verilith_font::spec::T_CFF) {
            println!("  CFF: {}", verilith_font::cff::check_cff(cff, ng));
        }
        return;
    };
    let version = if verilith_font::build::lookup(&ts, verilith_font::spec::T_GLYF).is_some() {
        verilith_font::spec::TAG_TRUETYPE
    } else {
        verilith_font::spec::TAG_OTTO
    };
    let Some(font) = verilith_font::build::assemble(&out, version) else {
        println!("refused while laying out the file");
        return;
    };
    let ok = verilith_font::font::check_font(&font);
    println!("final check: {}", ok);
    if !ok {
        let find = |tag: u32| out.iter().find(|t| t.tag == tag).map(|t| &t.data[..]);
        let maxp = find(verilith_font::spec::T_MAXP).unwrap();
        let ng = u16::from_be_bytes([maxp[4], maxp[5]]) as usize;
        let mut ms = 0x10000;
        if let Some(t) = find(verilith_font::spec::T_GDEF) {
            let g = verilith_font::layout::check_gdef(t, ng);
            println!("  GDEF: {}", g);
            if g {
                ms = verilith_font::layout::mark_sets(t, vstd::prelude::Ghost::assume_new());
            }
        }
        if let Some(t) = find(verilith_font::spec::T_GSUB) {
            println!("  GSUB: {}", verilith_font::layout::check_layout(t, false, ng, ms));
        }
        if let Some(t) = find(verilith_font::spec::T_GPOS) {
            println!("  GPOS: {}", verilith_font::layout::check_layout(t, true, ng, ms));
        }
    }
}
