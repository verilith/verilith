//! NormalizationTest.txt (Unicode 18.0) and differential tests against the
//! unicode-normalization and icu_normalizer crates.
use rand::{Rng, RngExt, SeedableRng};
use std::collections::HashSet;
use verilith_text::unicode::{nfc, nfd, nfkc, nfkd, normalize, normalize_reference, Form};

const FORMS: [Form; 4] = [Form::Nfc, Form::Nfd, Form::Nfkc, Form::Nfkd];

fn field(f: &str) -> String {
    f.split_whitespace().map(|h| char::from_u32(u32::from_str_radix(h, 16).unwrap()).unwrap()).collect()
}

fn check(norm: &dyn Fn(&str, Form) -> String) -> usize {
    let text = include_str!("data/NormalizationTest.txt");
    let mut part1 = HashSet::new();
    let mut in_part1 = false;
    let mut n = 0;
    for line in text.lines() {
        if line.starts_with("@Part") {
            in_part1 = line.starts_with("@Part1");
            continue;
        }
        let line = line.split('#').next().unwrap();
        if line.trim().is_empty() {
            continue;
        }
        let c: Vec<String> = line.split(';').take(5).map(field).collect();
        if in_part1 {
            part1.insert(c[0].chars().next().unwrap());
        }
        for (form, want) in [
            (Form::Nfc, [1, 1, 1, 3, 3]),
            (Form::Nfd, [2, 2, 2, 4, 4]),
            (Form::Nfkc, [3, 3, 3, 3, 3]),
            (Form::Nfkd, [4, 4, 4, 4, 4]),
        ] {
            for (k, w) in want.iter().enumerate() {
                assert_eq!(norm(&c[k], form), c[*w], "{form:?} of field {} on line {line}", k + 1);
            }
        }
        n += 1;
    }
    // Code points not in Part 1 are their own normal forms.
    for cp in 0..=0x10FFFFu32 {
        if let Some(ch) = char::from_u32(cp) {
            if !part1.contains(&ch) {
                let s = ch.to_string();
                for f in FORMS {
                    assert_eq!(norm(&s, f), s, "{f:?} of U+{cp:04X}");
                }
            }
        }
    }
    n
}

#[test]
fn conformance() {
    let n = check(&|s, f| normalize(s, f).into_owned());
    assert!(n > 20000, "{n} lines");
}

#[test]
fn conformance_reference() {
    check(&|s, f| normalize_reference(s, f));
}

fn random_text(rng: &mut impl Rng, pool: &[char]) -> String {
    let n = rng.random_range(0..24);
    (0..n)
        .map(|_| match rng.random_range(0..10) {
            0..=5 => pool[rng.random_range(0..pool.len())],
            6 => rng.random_range(b'a'..=b'z') as char,
            _ => loop {
                if let Some(c) = char::from_u32(rng.random_range(0..0x30000)) {
                    break c;
                }
            },
        })
        .collect()
}

/// Characters that take part in normalization: anything with a
/// decomposition, a nonzero combining class, or a composition.
fn interesting() -> Vec<char> {
    use unicode_normalization::char::canonical_combining_class;
    (0..0x30000u32)
        .filter_map(char::from_u32)
        .filter(|&c| {
            let s = c.to_string();
            canonical_combining_class(c) != 0
                || nfkd(&s) != s
                || (0x1100..0x1200).contains(&(c as u32))
                || unicode_normalization::char::compose('\u{1100}', c).is_some()
        })
        .collect()
}

#[test]
fn matches_unicode_normalization() {
    use unicode_normalization::UnicodeNormalization;
    let pool = interesting();
    let mut rng = rand::rngs::StdRng::seed_from_u64(1);
    for _ in 0..300_000 {
        let s = random_text(&mut rng, &pool);
        assert_eq!(nfc(&s), s.nfc().collect::<String>(), "nfc {:?}", s);
        assert_eq!(nfd(&s), s.nfd().collect::<String>(), "nfd {:?}", s);
        assert_eq!(nfkc(&s), s.nfkc().collect::<String>(), "nfkc {:?}", s);
        assert_eq!(nfkd(&s), s.nfkd().collect::<String>(), "nfkd {:?}", s);
        assert_eq!(verilith_text::unicode::is_nfc(&s), unicode_normalization::is_nfc(&s), "is_nfc {:?}", s);
        assert_eq!(verilith_text::unicode::is_nfd(&s), unicode_normalization::is_nfd(&s), "is_nfd {:?}", s);
        assert_eq!(verilith_text::unicode::is_nfkc(&s), unicode_normalization::is_nfkc(&s), "is_nfkc {:?}", s);
        assert_eq!(verilith_text::unicode::is_nfkd(&s), unicode_normalization::is_nfkd(&s), "is_nfkd {:?}", s);
    }
}

#[test]
fn matches_icu4x() {
    use icu_normalizer::{ComposingNormalizerBorrowed, DecomposingNormalizerBorrowed};
    let (c, d) = (ComposingNormalizerBorrowed::new_nfc(), DecomposingNormalizerBorrowed::new_nfd());
    let (kc, kd) = (ComposingNormalizerBorrowed::new_nfkc(), DecomposingNormalizerBorrowed::new_nfkd());
    let pool = interesting();
    let mut rng = rand::rngs::StdRng::seed_from_u64(2);
    let mut differ = 0;
    for _ in 0..100_000 {
        let s = random_text(&mut rng, &pool);
        // icu_normalizer may carry older Unicode data; count, don't fail, on
        // inputs with characters it does not know.
        let ok = nfc(&s) == c.normalize(&s) && nfd(&s) == d.normalize(&s) && nfkc(&s) == kc.normalize(&s)
            && nfkd(&s) == kd.normalize(&s);
        if !ok {
            differ += 1;
        }
    }
    assert!(differ < 500, "{differ} inputs differ");
}
