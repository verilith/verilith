//! Checks the trusted Unicode data: the generated tables against the UCD
//! files, parsed here independently of tools/gen_unicode.py, and each
//! `axiom_*` of src/unicode/data.rs and src/unicode/spec.rs for every code
//! point.
use std::collections::{HashMap, HashSet};
use verilith_text::unicode::data::*;
use verilith_text::unicode::tables::*;
use verilith_text::unicode::{normalize_reference, Form};

fn scalar(c: u32) -> bool {
    c <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&c)
}

fn decomp(c: u32, compat: bool) -> Vec<u32> {
    let d = decomp_of(c, compat, word_of(c));
    (0..d.len)
        .map(|m| {
            let (x, k) = decomp_elem(c, ccc_of(c), compat, &d, m);
            // axiom_pool, axiom_jamo: the class that comes with each character
            assert_eq!(k, ccc_of(x), "class of U+{x:04X} in the decomposition of U+{c:04X}");
            x
        })
        .collect()
}

fn second(c: u32) -> bool {
    flags_of(c) & FLAG_SECOND != 0
}

struct Ucd {
    ccc: HashMap<u32, u8>,
    dm: HashMap<u32, (bool, Vec<u32>)>,
    excluded: HashSet<u32>,
}

fn ucd() -> Ucd {
    let mut ccc = HashMap::new();
    let mut dm = HashMap::new();
    let mut ranges = vec![];
    for line in include_str!("data/UnicodeData.txt").lines() {
        let f: Vec<&str> = line.split(';').collect();
        let cp = u32::from_str_radix(f[0], 16).unwrap();
        if f[1].ends_with("First>") {
            ranges.push(cp);
        }
        let k: u8 = f[3].parse().unwrap();
        if k != 0 {
            ccc.insert(cp, k);
        }
        if !f[5].is_empty() {
            let compat = f[5].starts_with('<');
            let m = f[5].split_whitespace().filter(|p| !p.starts_with('<')).map(|p| u32::from_str_radix(p, 16).unwrap());
            dm.insert(cp, (compat, m.collect()));
        }
    }
    let mut excluded = HashSet::new();
    for line in include_str!("data/DerivedNormalizationProps.txt").lines() {
        let line = line.split('#').next().unwrap();
        let f: Vec<&str> = line.split(';').map(str::trim).collect();
        if f.len() > 1 && f[1] == "Full_Composition_Exclusion" {
            let (a, b) = f[0].split_once("..").unwrap_or((f[0], f[0]));
            for cp in u32::from_str_radix(a, 16).unwrap()..=u32::from_str_radix(b, 16).unwrap() {
                excluded.insert(cp);
            }
        }
    }
    Ucd { ccc, dm, excluded }
}

fn full(u: &Ucd, c: u32, compat: bool) -> Vec<u32> {
    if (0xAC00..0xAC00 + 11172).contains(&c) {
        let s = c - 0xAC00;
        let mut v = vec![0x1100 + s / 588, 0x1161 + (s % 588) / 28];
        if s % 28 != 0 {
            v.push(0x11A7 + s % 28);
        }
        return v;
    }
    match u.dm.get(&c) {
        Some((cm, m)) if compat || !cm => m.iter().flat_map(|&x| full(u, x, compat)).collect(),
        _ => vec![c],
    }
}

#[test]
fn tables_match_ucd() {
    let u = ucd();
    let mut pairs = HashMap::new();
    for (&cp, (compat, m)) in &u.dm {
        if !compat && m.len() == 2 && !u.excluded.contains(&cp) {
            pairs.insert((m[0], m[1]), cp);
        }
    }
    for c in 0..=0x10FFFFu32 {
        assert_eq!(ccc_of(c), *u.ccc.get(&c).unwrap_or(&0), "ccc U+{c:04X}");
        if scalar(c) {
            assert_eq!(decomp(c, false), full(&u, c, false), "canonical decomposition U+{c:04X}");
            assert_eq!(decomp(c, true), full(&u, c, true), "compatibility decomposition U+{c:04X}");
        }
    }
    // Every pair composes as it should, and the table holds nothing else.
    for (&(a, b), &p) in &pairs {
        assert_eq!(comp_of(a, b), Some(p), "U+{a:04X} U+{b:04X}");
    }
    assert_eq!(COMP_SECOND_LEN, pairs.len());
    let mut seen = 0;
    for a in 0..=0x10FFFFu32 {
        let w = REC_COMP[rec_of(a)];
        seen += (w & 255) as usize;
    }
    assert_eq!(seen, pairs.len(), "each first character owns its own pairs");
    // Hangul.
    for l in 0..19 {
        for v in 0..21 {
            let lv = 0xAC00 + (l * 21 + v) * 28;
            assert_eq!(comp_of(0x1100 + l, 0x1161 + v), Some(lv));
            for t in 1..28 {
                assert_eq!(comp_of(lv, 0x11A7 + t), Some(lv + t));
            }
        }
    }
}

/// Every `Some` of `comp_of` comes from one of these: a Hangul rule or an
/// entry of the first character's run of the pair table.
fn all_compositions() -> Vec<(u32, u32, u32)> {
    let mut v = vec![];
    for a in 0..=0x10FFFFu32 {
        let w = REC_COMP[rec_of(a)];
        let start = (w >> 8) as usize;
        for i in start..start + (w & 255) as usize {
            if i < COMP_SECOND_LEN {
                v.push((a, COMP_SECOND[i], COMP_RESULT[i]));
            }
        }
    }
    for l in 0..19 {
        for vv in 0..21 {
            let lv = 0xAC00 + (l * 21 + vv) * 28;
            v.push((0x1100 + l, 0x1161 + vv, lv));
            for t in 1..28 {
                v.push((lv, 0x11A7 + t, lv + t));
            }
        }
    }
    v
}

#[test]
fn axiom_trie_holds() {
    for &b in TRIE_INDEX.iter() {
        assert!(b as usize + 64 <= TRIE_DATA_LEN);
        for k in 0..64 {
            assert!(((TRIE_DATA[b as usize + k] & 0xFFFF) as usize) < REC_CCC_LEN);
        }
    }
}

#[test]
fn axiom_pool_holds() {
    for &p in POOL.iter() {
        assert_eq!((p >> 24) as u8, ccc_of(p & 0xFFFFFF));
    }
    for c in (0x1100..0x1113).chain(0x1161..0x1176).chain(0x11A7..0x11C3) {
        assert_eq!(ccc_of(c), 0);
    }
}

#[test]
fn axiom_comp_holds() {
    for (a, b, p) in all_compositions() {
        if comp_of(a, b) == Some(p) {
            assert!(second(b), "U+{b:04X} is the second of a pair");
            assert!(scalar(p) && ccc_of(p) == 0, "U+{p:04X} is a scalar starter");
        }
    }
}

const FORMS: [(bool, bool); 4] = [(false, false), (false, true), (true, false), (true, true)];

fn fast_flag(compose: bool, compat: bool) -> u16 {
    match (compose, compat) {
        (false, false) => FLAG_FAST_NFD,
        (false, true) => FLAG_FAST_NFKD,
        (true, false) => FLAG_FAST_NFC,
        (true, true) => FLAG_FAST_NFKC,
    }
}

fn bb_flag(compose: bool, compat: bool) -> u16 {
    match (compose, compat) {
        (false, false) => FLAG_BB_NFD,
        (false, true) => FLAG_BB_NFKD,
        (true, false) => FLAG_BB_NFC,
        (true, true) => FLAG_BB_NFKC,
    }
}

fn boundary(c: u32, compose: bool, compat: bool) -> bool {
    let d0 = decomp(c, compat)[0];
    ccc_of(d0) == 0 && (!compose || !second(d0))
}

#[test]
fn axioms_per_code_point() {
    for c in (0..=0x10FFFFu32).filter(|&c| scalar(c)) {
        let s = char::from_u32(c).unwrap().to_string();
        for (compose, compat) in FORMS {
            // axiom_decomp_scalar
            assert!(decomp(c, compat).iter().all(|&x| scalar(x)), "U+{c:04X}");
            let f = flags_of(c);
            // axiom_decomp_ordered, against the verified canonical ordering
            if !compose {
                let d: String = decomp(c, compat).iter().map(|&x| char::from_u32(x).unwrap()).collect();
                let form = if compat { Form::Nfkd } else { Form::Nfd };
                assert_eq!(normalize_reference(&d, form), d, "decomposition of U+{c:04X} is ordered");
            }
            // axiom_bb
            if f & bb_flag(compose, compat) != 0 {
                assert!(boundary(c, compose, compat), "boundary U+{c:04X}");
            }
            // axiom_fast_below
            let below = if compat { 0xA0 } else if compose { 0x300 } else { 0xC0 };
            if c < below {
                assert!(f & fast_flag(compose, compat) != 0, "U+{c:04X} below {below:#x}");
            }
            // axiom_ascii
            if c < 0x80 {
                assert!(f & fast_flag(compose, compat) != 0);
            }
            // axiom_fast, against the verified normalizer without the fast path
            if f & fast_flag(compose, compat) != 0 {
                assert!(boundary(c, compose, compat), "fast U+{c:04X} is a boundary");
                assert_eq!(ccc_of(c), 0, "fast U+{c:04X} is a starter");
                let form = match (compose, compat) {
                    (false, false) => Form::Nfd,
                    (false, true) => Form::Nfkd,
                    (true, false) => Form::Nfc,
                    (true, true) => Form::Nfkc,
                };
                assert_eq!(normalize_reference(&s, form), s, "fast U+{c:04X} is stable");
            }
        }
    }
}
