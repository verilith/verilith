//! The facts the C API's UTF-16 glue relies on, checked against the UCD,
//! and its ICU conventions. `tests/c/icu_diff.c` diffs it against ICU.

use verilith_text::capi::*;
use verilith_text::unicode::{self, Form};

const FORMS: [Form; 4] = [Form::Nfc, Form::Nfd, Form::Nfkc, Form::Nfkd];

/// (code point, canonical combining class, decomposition) from UnicodeData.txt.
fn unicode_data() -> Vec<(u32, u32, String)> {
    std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/UnicodeData.txt"))
        .unwrap()
        .lines()
        .map(|l| {
            let f: Vec<&str> = l.split(';').collect();
            (u32::from_str_radix(f[0], 16).unwrap(), f[3].parse().unwrap(), f[5].to_string())
        })
        .collect()
}

#[test]
fn stable_below_is_stable() {
    let data = unicode_data();
    // The second characters of canonical pairs, which compositions end in.
    let seconds: Vec<u32> = data
        .iter()
        .filter(|(_, _, d)| !d.is_empty() && !d.starts_with('<'))
        .filter_map(|(_, _, d)| {
            let p: Vec<&str> = d.split(' ').collect();
            (p.len() == 2).then(|| u32::from_str_radix(p[1], 16).unwrap())
        })
        .collect();
    for form in FORMS {
        let b = stable_below(form) as u32;
        for &(c, ccc, ref d) in data.iter().filter(|e| e.0 < b) {
            assert_eq!(ccc, 0, "U+{c:04X}");
            assert!(!seconds.contains(&c), "U+{c:04X} ends a composition");
            let compat = matches!(form, Form::Nfkc | Form::Nfkd);
            let decomposes = matches!(form, Form::Nfd | Form::Nfkd);
            if decomposes || compat {
                assert!(d.is_empty() || (!compat && d.starts_with('<')), "U+{c:04X} decomposes in {form:?}");
            }
            let s = char::from_u32(c).unwrap().to_string();
            assert_eq!(unicode::normalize(&s, form), s, "U+{c:04X} in {form:?}");
        }
    }
}

fn utf16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

#[test]
fn normalize_conventions() {
    unsafe {
        let mut e = U_ZERO_ERROR;
        let nfc = vtext_unorm2_getNFCInstance(&mut e);
        let nfd = vtext_unorm2_getNFDInstance(&mut e);
        assert_eq!(e, U_ZERO_ERROR);

        // NUL-terminated input, preflighting, then an exact fit.
        let mut src = utf16("cafe\u{301}");
        src.push(0);
        let n = vtext_unorm2_normalize(nfc, src.as_ptr(), -1, core::ptr::null_mut(), 0, &mut e);
        assert_eq!((n, e), (4, U_BUFFER_OVERFLOW_ERROR));
        let mut out = [0u16; 4];
        e = U_ZERO_ERROR;
        let n = vtext_unorm2_normalize(nfc, src.as_ptr(), -1, out.as_mut_ptr(), 4, &mut e);
        assert_eq!((n, e), (4, U_STRING_NOT_TERMINATED_WARNING));
        assert_eq!(out[..], utf16("café")[..]);

        // An unpaired surrogate splits the text and is kept.
        let src = [0x65, 0xDC00, 0x301, 0x65, 0x301];
        let mut out = [0u16; 8];
        e = U_ZERO_ERROR;
        let n = vtext_unorm2_normalize(nfc, src.as_ptr(), 5, out.as_mut_ptr(), 8, &mut e);
        assert_eq!(&out[..n as usize], &[0x65, 0xDC00, 0x301, 0xE9]);
        assert_eq!(out[n as usize], 0);
        assert_eq!(vtext_unorm2_isNormalized(nfc, src.as_ptr(), 5, &mut e), 0);
        assert_eq!(vtext_unorm2_isNormalized(nfc, out.as_ptr(), n, &mut e), 1);
        assert_eq!(vtext_unorm2_quickCheck(nfd, out.as_ptr(), n, &mut e), UNORM_NO);

        // A failure going in is passed through untouched.
        e = U_BUFFER_OVERFLOW_ERROR;
        assert_eq!(vtext_unorm2_normalize(nfc, src.as_ptr(), 5, out.as_mut_ptr(), 8, &mut e), 0);
        assert_eq!(e, U_BUFFER_OVERFLOW_ERROR);
    }
}

#[test]
fn idna_conventions() {
    unsafe {
        let mut e = U_ZERO_ERROR;
        let idna = vtext_uidna_openUTS46(UIDNA_NONTRANSITIONAL_TO_ASCII | UIDNA_CHECK_BIDI, &mut e);
        let mut info = UIDNAInfo {
            size: core::mem::size_of::<UIDNAInfo>() as i16,
            is_transitional_different: 0,
            reserved_b3: 0,
            errors: 0,
            reserved_i2: 0,
            reserved_i3: 0,
        };
        let mut out = [0u8; 64];
        let name = b"Fa\xc3\x9f.Example.";
        let n = vtext_uidna_nameToASCII_UTF8(idna, name.as_ptr().cast(), name.len() as i32, out.as_mut_ptr().cast(), 64, &mut info, &mut e);
        assert_eq!(&out[..n as usize], b"xn--fa-hia.example.");
        assert_eq!((e, info.errors, info.is_transitional_different), (U_ZERO_ERROR, 0, 1));

        let name = b"-a..b\0";
        let n = vtext_uidna_nameToASCII_UTF8(idna, name.as_ptr().cast(), -1, out.as_mut_ptr().cast(), 64, &mut info, &mut e);
        assert!(n > 0);
        assert_eq!(info.errors & (UIDNA_ERROR_LEADING_HYPHEN | UIDNA_ERROR_EMPTY_LABEL), UIDNA_ERROR_LEADING_HYPHEN | UIDNA_ERROR_EMPTY_LABEL);

        // A too-small info struct is an argument error.
        info.size = 4;
        e = U_ZERO_ERROR;
        vtext_uidna_nameToASCII_UTF8(idna, name.as_ptr().cast(), 5, out.as_mut_ptr().cast(), 64, &mut info, &mut e);
        assert_eq!(e, U_ILLEGAL_ARGUMENT_ERROR);
        vtext_uidna_close(idna);
    }
}
