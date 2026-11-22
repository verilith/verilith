//! The UTS #46 tables against the UCD files, parsed independently of
//! tools/gen_idna.py, and the `axiom_*` of src/idna/data.rs for every code
//! point.
use verilith_text::idna::tables::*;

const N: usize = 0x110000;

fn data(name: &str) -> String {
    std::fs::read_to_string(format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

/// `(lo, hi, fields)` of each data line, and the default of the `@missing`
/// lines.
fn ranges(text: &str) -> (Vec<(usize, usize, Vec<String>)>, Vec<(usize, usize, String)>) {
    let mut v = Vec::new();
    let mut m = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("# @missing:") {
            let (r, val) = rest.split_once(';').unwrap();
            let (a, b) = r.trim().split_once("..").unwrap_or((r.trim(), r.trim()));
            m.push((usize::from_str_radix(a, 16).unwrap(), usize::from_str_radix(b, 16).unwrap(), val.trim().to_string()));
            continue;
        }
        let line = line.split('#').next().unwrap().trim();
        if line.is_empty() {
            continue;
        }
        let f: Vec<String> = line.split(';').map(|x| x.trim().to_string()).collect();
        let (a, b) = f[0].split_once("..").unwrap_or((&f[0], &f[0]));
        v.push((usize::from_str_radix(a, 16).unwrap(), usize::from_str_radix(b, 16).unwrap(), f[1..].to_vec()));
    }
    (v, m)
}

fn word(c: usize) -> u32 {
    let j = IDNA_L1[c >> 12] as usize + ((c >> 6) & 63);
    IDNA_DATA[IDNA_L2[j] as usize + (c & 63)]
}

#[test]
fn tables_match_ucd() {
    let mut status = vec![u32::MAX; N];
    let mut mapping: Vec<Vec<u32>> = vec![Vec::new(); N];
    for (a, b, f) in ranges(&data("IdnaMappingTable.txt")).0 {
        let st = match f[0].as_str() {
            "valid" => STATUS_VALID,
            "ignored" => STATUS_IGNORED,
            "mapped" => STATUS_MAPPED,
            "deviation" => STATUS_DEVIATION,
            "disallowed" => STATUS_DISALLOWED,
            s => panic!("{s}"),
        };
        let m: Vec<u32> = if st == STATUS_MAPPED || st == STATUS_DEVIATION {
            f.get(1).map(|s| s.split_whitespace().map(|x| u32::from_str_radix(x, 16).unwrap()).collect()).unwrap_or_default()
        } else {
            Vec::new()
        };
        for c in a..=b {
            status[c] = st;
            mapping[c] = m.clone();
        }
    }
    let mut mark = vec![false; N];
    let mut first = None;
    for line in data("UnicodeData.txt").lines() {
        let f: Vec<&str> = line.split(';').collect();
        let c = usize::from_str_radix(f[0], 16).unwrap();
        if f[1].ends_with(", First>") {
            first = Some(c);
            continue;
        }
        let lo = if f[1].ends_with(", Last>") { first.take().unwrap() } else { c };
        if matches!(f[2], "Mn" | "Mc" | "Me") {
            for x in lo..=c {
                mark[x] = true;
            }
        }
    }
    let names = ["L", "R", "AL", "EN", "ES", "ET", "AN", "CS", "NSM", "BN", "ON"];
    let long = [
        "Left_To_Right",
        "Right_To_Left",
        "Arabic_Letter",
        "European_Number",
        "European_Separator",
        "European_Terminator",
        "Arabic_Number",
        "Common_Separator",
        "Nonspacing_Mark",
        "Boundary_Neutral",
        "Other_Neutral",
    ];
    let mut bidi = vec![BIDI_OTHER; N];
    let (v, m) = ranges(&data("DerivedBidiClass.txt"));
    for (a, b, val) in m {
        let k = long.iter().position(|x| *x == val).map(|k| k as u32).unwrap_or(BIDI_OTHER);
        for c in a..=b {
            bidi[c] = k;
        }
    }
    for (a, b, f) in v {
        let k = names.iter().position(|x| *x == f[0]).map(|k| k as u32).unwrap_or(BIDI_OTHER);
        for c in a..=b {
            bidi[c] = k;
        }
    }
    let mut jt = vec![JT_U; N];
    for (a, b, f) in ranges(&data("DerivedJoiningType.txt")).0 {
        let k = match f[0].as_str() {
            "L" => JT_L,
            "R" => JT_R,
            "D" => JT_D,
            "T" => JT_T,
            "C" => JT_C,
            "U" => JT_U,
            s => panic!("{s}"),
        };
        for c in a..=b {
            jt[c] = k;
        }
    }
    for c in 0..N {
        let w = word(c);
        assert_eq!(w & 7, status[c], "status {c:X}");
        assert_eq!(w & 8 != 0, mark[c], "mark {c:X}");
        assert_eq!((w >> 4) & 15, bidi[c], "bidi {c:X}");
        assert_eq!((w >> 8) & 7, jt[c], "joining {c:X}");
        let (off, len) = ((w >> 16) as usize, ((w >> 11) & 31) as usize);
        assert_eq!(&IDNA_POOL[off..off + len], &mapping[c][..], "mapping {c:X}");
    }
}

#[test]
fn axioms_hold() {
    // axiom_idna_ascii
    for c in 0..0x80usize {
        let w = word(c);
        let (off, len) = ((w >> 16) as usize, ((w >> 11) & 31) as usize);
        if (0x41..=0x5A).contains(&c) {
            assert_eq!(w & 7, STATUS_MAPPED);
            assert_eq!(&IDNA_POOL[off..off + len], &[c as u32 + 0x20]);
        } else {
            assert_eq!(w & 7, STATUS_VALID);
        }
        assert_eq!(w & 8, 0);
        let b = (w >> 4) & 15;
        assert!(b != BIDI_R && b != BIDI_AL && b != BIDI_AN);
        assert_eq!((w >> 8) & 7, JT_U);
    }
    // axiom_idna_trie
    for i in 0..IDNA_L1_LEN {
        assert!(IDNA_L1[i] as usize + 64 <= IDNA_L2_LEN);
    }
    for j in 0..IDNA_L2_LEN {
        assert!(IDNA_L2[j] as usize + 64 <= IDNA_DATA_LEN);
    }
    // axiom_idna_mapping, for every word a code point can read (and for
    // the word of code points above U+10FFFF, which has no mapping)
    for &w in IDNA_DATA.iter() {
        let (off, len) = ((w >> 16) as usize, ((w >> 11) & 31) as usize);
        assert!(off + len <= IDNA_POOL_LEN);
        for &c in &IDNA_POOL[off..off + len] {
            assert!(char::from_u32(c).is_some());
        }
    }
}
