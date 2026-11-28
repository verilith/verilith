//! NormalizationTest.txt (Unicode 18.0) and differential tests against the
//! unicode-normalization and icu_normalizer crates.
use rand::{Rng, RngExt, SeedableRng};
use std::collections::HashSet;
use verilith_text::unicode::{
    is_normalized, is_normalized_utf16, nfc, nfd, nfkc, nfkd, normalize, normalize_reference, normalize_utf16, Form,
};

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
fn conformance_utf16() {
    check(&|s, f| String::from_utf16(&normalize_utf16(&s.encode_utf16().collect::<Vec<_>>(), f)).unwrap());
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

/// The UTF-16 normalizer against the UTF-8 one, on text with unpaired
/// surrogates, which split it: each run between them is normalized on its
/// own and the surrogate kept.
#[test]
fn utf16_matches_utf8() {
    let pool = interesting();
    let mut rng = rand::rngs::StdRng::seed_from_u64(3);
    for _ in 0..200_000 {
        let pieces: Vec<String> = (0..rng.random_range(1..4)).map(|_| random_text(&mut rng, &pool)).collect();
        let lone: Vec<u16> = (1..pieces.len())
            .map(|_| if rng.random_bool(0.5) { rng.random_range(0xD800..0xDC00) } else { rng.random_range(0xDC00..0xE000) })
            .collect();
        let mut s: Vec<u16> = Vec::new();
        for (k, p) in pieces.iter().enumerate() {
            if k > 0 {
                s.push(lone[k - 1]);
            }
            s.extend(p.encode_utf16());
        }
        for f in FORMS {
            let mut want: Vec<u16> = Vec::new();
            let mut normal = true;
            let mut runs = Vec::new();
            // Split where the units are not well-formed, as ICU does.
            let mut run = String::new();
            for r in char::decode_utf16(s.iter().copied()) {
                match r {
                    Ok(c) => run.push(c),
                    Err(e) => {
                        runs.push((std::mem::take(&mut run), Some(e.unpaired_surrogate())));
                    }
                }
            }
            runs.push((run, None));
            for (r, u) in &runs {
                want.extend(normalize(r, f).encode_utf16());
                normal &= is_normalized(r, f);
                want.extend(u.iter());
            }
            assert_eq!(normalize_utf16(&s, f), want, "{f:?} of {s:04X?}");
            assert_eq!(is_normalized_utf16(&s, f), normal, "is_normalized {f:?} of {s:04X?}");
        }
    }
}

/// `valid16_prefix` (32 units at a time with AVX2 or NEON) stops at the
/// first unpaired surrogate, as `char::decode_utf16` does, for every
/// placement of surrogates around and inside the 32-unit steps.
#[test]
fn valid16_prefix_matches_decode() {
    let mut x: u64 = 0x2545F4914F6CDD1D;
    let mut rnd = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let pick = [0x41u16, 0x4E2D, 0xD7FF, 0xE000, 0xFFFF, 0xD83D, 0xDE00, 0xD800, 0xDFFF, 0xDBFF, 0xDC00, 0x00E9];
    for len in 0..130usize {
        for _ in 0..60 {
            let mut s: Vec<u16> = (0..len).map(|_| [0x41u16, 0x4E2D, 0xD7FF, 0xE000][(rnd() % 4) as usize]).collect();
            for _ in 0..(rnd() % 3) {
                if len > 0 {
                    let p = (rnd() as usize) % len;
                    s[p] = pick[(rnd() as usize) % pick.len()];
                }
            }
            let mut want = 0;
            for r in char::decode_utf16(s.iter().copied()) {
                match r {
                    Ok(c) => want += c.len_utf16(),
                    Err(_) => break,
                }
            }
            assert_eq!(verilith_text::unicode::norm16::valid16_prefix(&s).0, want, "{s:04X?}");
        }
    }
}

/// Both 32-unit surrogate tests (NEON on vsimd's emulation off AArch64)
/// are exact: true exactly when none of the 32 units is a surrogate.
#[test]
fn no_sur32_exact() {
    for p in 0..32usize {
        for u in (0u32..=0xFFFF).step_by(37).chain([0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000]) {
            let mut s = vec![0x4E2Du16; 40];
            s[3 + p] = u as u16;
            let want = !(0xD800..=0xDFFF).contains(&u);
            assert_eq!(verilith_text::utf::neon::no_sur32_neon(&s, 3), want, "neon {u:04X} at {p}");
            #[cfg(target_arch = "x86_64")]
            if std::is_x86_feature_detected!("avx2") {
                assert_eq!(verilith_text::utf::avx2::no_sur32(&s, 3), want, "avx2 {u:04X} at {p}");
            }
        }
    }
}
