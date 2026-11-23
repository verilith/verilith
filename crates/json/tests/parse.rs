//! Runtime tests of the verified parser through its Rust API.
use verilith_json::parser::parse_document;
use verilith_json::spec::MAX_DEPTH;

fn accepts(s: &[u8]) -> bool {
    parse_document(s, true).is_ok()
}

fn single_string(s: &[u8]) -> Vec<u8> {
    let doc = verilith_json::parse(s).expect("should parse");
    let v = doc.root().as_bytes().expect("a string").into_owned();
    v
}

#[test]
fn scalars() {
    for s in [
        "null",
        "true",
        "false",
        "0",
        "-0",
        "1.5e+10",
        "-12.25E-3",
        "\"x\"",
        " \t\r\n1 ",
    ] {
        assert!(accepts(s.as_bytes()), "{s}");
    }
    for s in [
        "", " ", "nul", "tru", "01", "-", "1.", ".5", "1e", "+1", "\"", "'a'", "NaN", "1 2",
    ] {
        assert!(!accepts(s.as_bytes()), "{s}");
    }
}

#[test]
fn structures() {
    for s in [
        "[]",
        "{}",
        "[1,[2,{}]]",
        "{\"a\":{\"b\":[null]}}",
        "[ 1 , 2 ]",
        "{ \"a\" : 1 , \"b\" : 2 }",
    ] {
        assert!(accepts(s.as_bytes()), "{s}");
    }
    for s in [
        "[1,]",
        "[,1]",
        "{\"a\"}",
        "{\"a\":}",
        "{1:2}",
        "{\"a\":1,}",
        "[1 2]",
        "[",
        "{",
    ] {
        assert!(!accepts(s.as_bytes()), "{s}");
    }
}

#[test]
fn string_escapes() {
    assert_eq!(
        single_string(br#""a\"\\\/\b\f\n\r\t""#),
        b"a\"\\/\x08\x0c\n\r\t"
    );
    assert_eq!(single_string(b"\"\\u20AC\\u732b\""), "€猫".as_bytes());
    assert_eq!(single_string(b"\"\\uD83D\\udc31\""), "🐱".as_bytes());
    assert_eq!(single_string(b"\"\\u0041\\u00e9\""), "Aé".as_bytes());
    for s in [
        r#""\uD83D""#,
        r#""\uDC31""#,
        r#""\uD83D\u0041""#,
        r#""\x""#,
        "\"\t\"",
        r#""\u12""#,
    ] {
        assert!(!accepts(s.as_bytes()), "{s}");
    }
}

#[test]
fn bom_and_trailing_bytes() {
    assert!(accepts(b"\xEF\xBB\xBF{}"));
    assert!(!accepts(b"{} x"));
    // Without require_end, trailing bytes are left to the caller (cJSON_Parse).
    let (_, end) = parse_document(b"[1] xyz", false).ok().unwrap();
    assert_eq!(end, 3);
}

fn nested(n: usize) -> Vec<u8> {
    let mut v = vec![b'['; n];
    v.extend(std::iter::repeat(b']').take(n));
    v
}

#[test]
fn nesting_limit() {
    assert!(accepts(&nested(MAX_DEPTH)));
    assert!(!accepts(&nested(MAX_DEPTH + 1)));
    // Far deeper input is rejected without exhausting the stack.
    assert!(!accepts(&nested(1_000_000)));
    let mut objs = Vec::new();
    for _ in 0..MAX_DEPTH + 1 {
        objs.extend_from_slice(b"{\"a\":");
    }
    assert!(!accepts(&objs));
}

#[test]
fn long_sequences_use_loops() {
    let mut v = b"[".to_vec();
    for i in 0..1_000_000 {
        if i > 0 {
            v.push(b',');
        }
        v.push(b'0');
    }
    v.push(b']');
    let (tape, _) = parse_document(&v, true).ok().unwrap();
    assert_eq!(tape.toks.len(), 1_000_002);
}

/// Runs JSONTestSuite's test_parsing directory if JSON_TEST_SUITE points at it.
#[test]
fn json_test_suite() {
    let Ok(dir) = std::env::var("JSON_TEST_SUITE") else {
        eprintln!("JSON_TEST_SUITE not set; skipping");
        return;
    };
    let mut failures = Vec::new();
    let mut count = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let data = std::fs::read(&path).unwrap();
        let ok = accepts(&data);
        count += 1;
        if (name.starts_with("y_") && !ok) || (name.starts_with("n_") && ok) {
            failures.push(name);
        }
    }
    assert!(count > 300, "only {count} files found");
    assert!(failures.is_empty(), "mismatches: {failures:?}");
}

#[test]
fn rust_api() {
    let src = br#"{"a": [1, -2.5, "x\ny", true, null, {"b": {}}], "a": 3, "k\u00e9y": "v"}"#;
    let doc = verilith_json::parse(src).unwrap();
    let root = doc.root();
    assert_eq!(root.kind(), verilith_json::Type::Object);
    assert_eq!(root.len(), Some(3));
    let a = root.get("a").unwrap();
    assert_eq!(a.len(), Some(6));
    assert_eq!(a.at(0).unwrap().as_i64(), Some(1));
    assert_eq!(a.at(1).unwrap().as_f64(), Some(-2.5));
    assert_eq!(a.at(2).unwrap().as_str().as_deref(), Some("x\ny"));
    assert_eq!(a.at(3).unwrap().as_bool(), Some(true));
    assert!(a.at(4).unwrap().is_null());
    assert_eq!(a.at(5).unwrap().get("b").unwrap().len(), Some(0));
    assert!(a.at(6).is_none());
    assert_eq!(root.get("kéy").unwrap().as_str().as_deref(), Some("v"));
    let keys: Vec<String> = root.members().unwrap().map(|(k, _)| k.as_str().unwrap().into_owned()).collect();
    assert_eq!(keys, ["a", "a", "kéy"]);
    assert_eq!(format!("{:?}", a.at(5).unwrap()), r#"{"b": {}}"#);
    assert_eq!(verilith_json::parse(b"[1,").unwrap_err().offset, 3);
    let (d, end) = verilith_json::parse_prefix(b" 12 rest").unwrap();
    assert_eq!((d.root().as_i64(), end), (Some(12), 3));
}

/// Walking every container through the skip links visits each value once.
#[test]
fn walk_links() {
    fn walk(v: verilith_json::Value, n: &mut usize) {
        *n += 1;
        if let Some(e) = v.elements() { for c in e { walk(c, n); } }
        if let Some(m) = v.members() { for (_, c) in m { walk(c, n); } }
    }
    for s in ["[[1,[2,[3]],{}],{\"a\":[{},[]],\"b\":{\"c\":null}},4]", "{}", "[]", "7"] {
        let doc = verilith_json::parse(s.as_bytes()).unwrap();
        let mut n = 0;
        walk(doc.root(), &mut n);
        let scalars_and_containers = doc.tape().iter().filter(|t| !matches!(t.kind,
            verilith_json::parser::Kind::ArrEnd | verilith_json::parser::Kind::ObjEnd | verilith_json::parser::Kind::Key)).count();
        assert_eq!(n, scalars_and_containers, "{s}");
    }
}

#[test]
fn error_reasons() {
    use verilith_json::ErrorKind::*;
    let cases: &[(&[u8], usize, verilith_json::ErrorKind)] = &[
        (b"[1,", 3, UnexpectedEnd),
        (b"[1 true]", 3, UnexpectedByte(b't')),
        (b"{\"a\":\"b", 7, UnterminatedString),
        (b"[\"a\\x\"]", 3, InvalidEscape),
        (b"[\"\\uD800\"]", 2, InvalidEscape),
        (b"[\"a\tb\"]", 3, ControlCharacter(b'\t')),
        (b"[01]", 1, InvalidNumber),
        (b"[1.]", 1, InvalidNumber),
        (b"[tru]", 1, InvalidLiteral),
        (b"{} x", 3, TrailingData),
        (b"[\"\xC0\x80\"]", 2, InvalidUtf8),
        (b"[1,\n  2,\n  ]", 11, UnexpectedByte(b']')),
    ];
    for &(text, offset, kind) in cases {
        let e = verilith_json::parse(text).unwrap_err();
        assert_eq!((e.offset, e.kind), (offset, kind), "{:?}", String::from_utf8_lossy(text));
    }
    let e = verilith_json::parse(b"[1,\n  2,\n  ]").unwrap_err();
    assert_eq!((e.line, e.column), (3, 3));
    assert_eq!(e.to_string(), "unexpected ']' at line 3 column 3 (byte 11)");
    let deep = vec![b'['; 1001];
    assert_eq!(verilith_json::parse(&deep).unwrap_err().kind, TooDeep);
    let e = verilith_json::parse_prefix(b"[1, 2] tail \xFF").map(|(_, end)| end);
    assert_eq!(e.unwrap(), 6);
}

/// Error reporting never panics and stays inside the input.
#[test]
fn error_reasons_fuzz() {
    let alphabet = b"[]{},:\"\\ \n0123456789.eE+-utrfalsn\x01\xc3\xa9\xffx";
    let mut x: u64 = 0x2545F4914F6CDD1D;
    for _ in 0..300_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let n = (x % 24) as usize;
        let mut y = x;
        let s: Vec<u8> = (0..n)
            .map(|_| {
                y = y.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                alphabet[(y >> 33) as usize % alphabet.len()]
            })
            .collect();
        for e in [verilith_json::parse(&s).err(), verilith_json::parse_prefix(&s).err()].into_iter().flatten() {
            assert!(e.offset <= s.len(), "{e:?} {:?}", String::from_utf8_lossy(&s));
            assert!(e.line >= 1 && e.column >= 1);
        }
    }
}

/// Without the end check, a number must not be cut short where a lenient
/// reader (cJSON's strtod) would keep reading: `01` is not `0` then `1`.
#[test]
fn prefix_does_not_cut_numbers() {
    for t in ["01", "-01", "1.", "2e", "1E", "3+", "4-", "0.5.", "1e5e"] {
        assert!(verilith_json::parse_prefix(t.as_bytes()).is_err(), "{t}");
    }
    for (t, end) in [("1 2", 1), ("1,2", 1), ("1x", 1), ("\"a\"1", 3), ("true1", 4), ("[1]2", 3), ("1.5e3]", 5)] {
        assert_eq!(verilith_json::parse_prefix(t.as_bytes()).unwrap().1, end, "{t}");
    }
}

#[test]
fn eager_matches_lazy_and_std() {
    // xorshift, so the test is deterministic without a dependency.
    let mut r: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        r ^= r << 13;
        r ^= r >> 7;
        r ^= r << 17;
        r
    };
    let mut doc = String::from("[");
    let mut nums = Vec::new();
    for i in 0..200_000 {
        if i > 0 {
            doc.push(',');
        }
        let mut n = String::new();
        if next() % 2 == 0 {
            n.push('-');
        }
        let int_len = 1 + next() % 22;
        for k in 0..int_len {
            let d = next() % 10;
            n.push(char::from(b'0' + if k == 0 && int_len > 1 { 1 + d % 9 } else { d } as u8));
        }
        if next() % 2 == 0 {
            n.push('.');
            for _ in 0..1 + next() % 22 {
                n.push(char::from(b'0' + (next() % 10) as u8));
            }
        }
        if next() % 3 == 0 {
            n.push(if next() % 2 == 0 { 'e' } else { 'E' });
            if next() % 2 == 0 {
                n.push('-');
            }
            n.push_str(&(next() % 400).to_string());
        }
        doc.push_str(&n);
        nums.push(n);
        if next() % 4 == 0 {
            doc.push_str(",\"a\\n\\u00e9\\ud83d\\ude00b\\\"\",\"plain\"");
        }
    }
    doc.push(']');
    let b = doc.as_bytes();
    let eager = verilith_json::parse(b).unwrap();
    let mut lazy_p = verilith_json::Parser::lazy();
    let lazy = lazy_p.parse(b).unwrap();
    let (mut ei, mut li) = (eager.root().elements().unwrap(), lazy.root().elements().unwrap());
    let mut k = 0;
    loop {
        match (ei.next(), li.next()) {
            (None, None) => break,
            (Some(e), Some(l)) => {
                if let Some(v) = e.as_f64() {
                    let want: f64 = nums[k].parse().unwrap();
                    assert_eq!(v.to_bits(), want.to_bits(), "{}", nums[k]);
                    assert_eq!(l.as_f64().unwrap().to_bits(), want.to_bits());
                    k += 1;
                } else {
                    assert_eq!(e.as_bytes(), l.as_bytes());
                }
            }
            _ => panic!("length mismatch"),
        }
    }
    assert_eq!(k, nums.len());
}

#[test]
fn eager_digit_runs_at_every_offset() {
    // Digit runs of every length up to 40, at every alignment against the
    // 16-byte scans and the end of the input.
    let digits = b"9876543210123456789098765432101234567890";
    for len in 1..=digits.len() {
        for frac in [0usize, 1, 7, 15, 16, 17, 25] {
            for pad in 0..18 {
                let mut n = String::from_utf8(digits[..len].to_vec()).unwrap();
                if frac > 0 {
                    n.push('.');
                    n.push_str(std::str::from_utf8(&digits[digits.len() - frac..]).unwrap());
                }
                let want: f64 = n.parse().unwrap();
                for doc in [format!("{}{n}", " ".repeat(pad)), format!("{}[{n}]{}", " ".repeat(pad), " ".repeat(pad))] {
                    for mut p in [verilith_json::Parser::new(), verilith_json::Parser::lazy()] {
                        let d = p.parse(doc.as_bytes()).unwrap();
                        let r = d.root();
                        let v = if r.kind() == verilith_json::Type::Array { r.at(0).unwrap() } else { r };
                        assert_eq!(v.as_f64().unwrap().to_bits(), want.to_bits(), "{doc:?}");
                    }
                }
            }
        }
    }
}

#[test]
fn eager_keys_and_parser_reuse() {
    let mut p = verilith_json::Parser::new();
    for _ in 0..3 {
        let d = p.parse(br#"{"k\u00e9y": "v\tx", "a\"b": [1.5, "\ud83d\ude00"], "plain": 7}"#).unwrap();
        let m: Vec<_> = d.root().members().unwrap().map(|(k, v)| (k.as_bytes().into_owned(), v)).collect();
        assert_eq!(m[0].0, "k\u{e9}y".as_bytes());
        assert_eq!(&*m[0].1.as_bytes().unwrap(), b"v\tx");
        assert_eq!(m[1].0, b"a\"b");
        let a: Vec<_> = m[1].1.elements().unwrap().collect();
        assert_eq!(a[0].as_f64(), Some(1.5));
        assert_eq!(&*a[1].as_bytes().unwrap(), "\u{1F600}".as_bytes());
        assert_eq!(m[2].0, b"plain");
        assert_eq!(m[2].1.as_f64(), Some(7.0));
    }
}

#[test]
fn number_edge_lexemes() {
    let cases = [
        "0", "-0", "0.0", "-0.0e5", "1e100000", "-1e100000", "1e-100000", "1e99999", "1e-99999",
        "123456789012345678901234567890e-10", "0.0000000000000000000000000123", "1.7976931348623157e308",
        "1.7976931348623159e308", "4.9406564584124654e-324", "2.4703282292062327e-324",
        "2.4703282292062328e-324", "9007199254740993", "18446744073709551615", "18446744073709551616",
        "10000000000000000000", "9999999999999999999", "0.1e+1", "5E-1", "123.456e-0", "1e0000000000000000000000001",
    ];
    for c in cases {
        let want: f64 = c.parse().unwrap();
        for mut p in [verilith_json::Parser::new(), verilith_json::Parser::lazy()] {
            let doc = format!("[{c}]");
            let d = p.parse(doc.as_bytes()).unwrap();
            assert_eq!(d.root().at(0).unwrap().as_f64().unwrap().to_bits(), want.to_bits(), "{c}");
        }
    }
}

#[test]
fn escaped_strings_against_serde_json() {
    // Random mixes of plain runs, simple escapes, BMP and astral `\u`
    // escapes, of every length, read eagerly and lazily.
    let mut x: u64 = 0x2545F4914F6CDD1D;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let pieces = [
        "a", "plain text ", "0123456789abcdef0123", "\\n", "\\\"", "\\\\", "\\/", "\\t", "\\u0041", "\\u00e9",
        "\\u540d", "\\uffff", "\\ud83d\\ude00", "\\u0000", "é", "名",
    ];
    for _ in 0..3000 {
        let mut body = String::new();
        for _ in 0..next() % 12 {
            body.push_str(pieces[(next() % pieces.len() as u64) as usize]);
        }
        let doc = format!("[\"{body}\", {{\"{body}\": 1}}]");
        let want: serde_json::Value = serde_json::from_str(&doc).unwrap();
        let want = want[0].as_str().unwrap().as_bytes().to_vec();
        for mut p in [verilith_json::Parser::new(), verilith_json::Parser::lazy()] {
            let d = p.parse(doc.as_bytes()).unwrap();
            let r = d.root();
            assert_eq!(r.at(0).unwrap().as_bytes().unwrap().as_ref(), &want[..], "{doc}");
            let (k, _) = r.at(1).unwrap().members().unwrap().next().unwrap();
            assert_eq!(k.as_bytes().as_ref(), &want[..], "{doc}");
        }
    }
}

/// Every number an eager parse stores reads back as the nearest double:
/// random lexemes of every digit-run length, bit for bit against
/// `f64::from_str`, in arrays and as object members.
#[test]
fn eager_numbers_match_std() {
    let mut x = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let mut lexemes: Vec<String> = Vec::new();
    for _ in 0..40_000 {
        let mut s = String::new();
        if next() % 3 == 0 {
            s.push('-');
        }
        let ni = (next() % 21) as usize;
        if ni == 0 {
            s.push('0');
        } else {
            s.push((b'1' + (next() % 9) as u8) as char);
            for _ in 1..ni {
                s.push((b'0' + (next() % 10) as u8) as char);
            }
        }
        if next() % 4 != 0 {
            s.push('.');
            for _ in 0..1 + next() % 20 {
                s.push((b'0' + (next() % 10) as u8) as char);
            }
        }
        if next() % 5 == 0 {
            s.push(if next() % 2 == 0 { 'e' } else { 'E' });
            match next() % 3 {
                0 => s.push('-'),
                1 => s.push('+'),
                _ => {}
            }
            s.push_str(&(next() % 330).to_string());
        }
        lexemes.push(s);
    }
    let arr = format!("[{}]", lexemes.join(","));
    let obj = format!("{{{}}}", lexemes.iter().map(|l| format!("\"k\":{l}")).collect::<Vec<_>>().join(", "));
    let mut p = verilith_json::Parser::new();
    p.set_lazy(false);
    for (doc, is_obj) in [(arr, false), (obj, true)] {
        let d = p.parse(doc.as_bytes()).unwrap();
        let got: Vec<f64> = if is_obj {
            d.root().members().unwrap().map(|(_, v)| v.as_f64().unwrap()).collect()
        } else {
            d.root().elements().unwrap().map(|v| v.as_f64().unwrap()).collect()
        };
        assert_eq!(got.len(), lexemes.len());
        for (g, l) in got.iter().zip(&lexemes) {
            let want: f64 = l.parse().unwrap();
            assert_eq!(g.to_bits(), want.to_bits(), "{l}");
        }
    }
}

#[test]
fn wide_positions() {
    // Token positions are 48 bits, so inputs past 4 GiB fit.
    use verilith_json::parser::{Kind, Tok, NO};
    assert_eq!(std::mem::size_of::<Tok>(), 16);
    for (a, b) in [(0, 0), (5, 9), (0xFFFF_FFFF, 0x1_0000_0000), (0x1234_5678_9ABC, verilith_json::spec::MAX_INPUT)] {
        let t = Tok::new(Kind::Str, true, a, b, NO);
        assert_eq!((t.start(), t.end()), (a, b));
    }
    assert!(verilith_json::spec::MAX_INPUT > u32::MAX as usize);
}
