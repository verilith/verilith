//! The native C API (`src/native.rs`) against the Rust API it wraps: both
//! must describe every document the same way.
#![cfg(feature = "capi")]
use std::ffi::{c_char, CStr};
use verilith_json::native::*;

fn dump_rust(v: verilith_json::Value, out: &mut String) {
    use verilith_json::Type::*;
    match v.kind() {
        Null => out.push('n'),
        Bool => out.push_str(if v.as_bool().unwrap() { "t" } else { "f" }),
        Number => {
            out.push_str(&format!("#{}={:?}={:?}", v.as_number_str().unwrap(), v.as_f64().unwrap().to_bits(), v.as_i64()))
        }
        String => out.push_str(&format!("s{:?}", v.as_bytes().unwrap())),
        Array => {
            out.push_str(&format!("[{}:", v.len().unwrap()));
            v.elements().unwrap().for_each(|e| dump_rust(e, out));
            out.push(']');
        }
        Object => {
            out.push_str(&format!("{{{}:", v.len().unwrap()));
            for (k, e) in v.members().unwrap() {
                out.push_str(&format!("k{:?}", k.as_bytes()));
                dump_rust(e, out);
            }
            out.push('}');
        }
    }
}

unsafe fn bytes<'a>(s: *const c_char, len: usize) -> &'a [u8] {
    std::slice::from_raw_parts(s as *const u8, len)
}

unsafe fn dump_c(v: vjson_value, out: &mut String) {
    let (mut s, mut len) = (std::ptr::null(), 0usize);
    let mut it = std::mem::zeroed::<vjson_iter>();
    let mut e = std::mem::zeroed::<vjson_value>();
    match vjson_type(v) {
        VJSON_NULL => {
            assert!(vjson_is_null(v));
            out.push('n')
        }
        VJSON_BOOL => {
            let mut b = false;
            assert!(vjson_get_bool(v, &mut b));
            out.push_str(if b { "t" } else { "f" })
        }
        VJSON_NUMBER => {
            let (mut d, mut i) = (0f64, 0i64);
            assert!(vjson_get_number_text(v, &mut s, &mut len) && vjson_get_double(v, &mut d));
            let int = vjson_get_int64(v, &mut i).then_some(i);
            out.push_str(&format!("#{}={:?}={:?}", std::str::from_utf8(bytes(s, len)).unwrap(), d.to_bits(), int));
        }
        VJSON_STRING => {
            assert!(vjson_get_string(v, &mut s, &mut len));
            out.push_str(&format!("s{:?}", bytes(s, len)));
        }
        VJSON_ARRAY => {
            assert!(vjson_length(v, &mut len) && vjson_array_iter(v, &mut it));
            out.push_str(&format!("[{len}:"));
            let mut i = 0;
            loop {
                let t = vjson_array_next(&mut it, &mut e);
                if t == 0 {
                    break;
                }
                assert_eq!(t, vjson_type(e));
                // Random access finds the same element.
                let mut at = std::mem::zeroed::<vjson_value>();
                assert!(vjson_array_at(v, i, &mut at));
                assert_eq!(std::slice::from_raw_parts(&at as *const _ as *const usize, 2),
                    std::slice::from_raw_parts(&e as *const _ as *const usize, 2));
                i += 1;
                dump_c(e, out);
            }
            assert_eq!(i, len);
            assert!(!vjson_array_at(v, len, &mut e));
            out.push(']');
        }
        VJSON_OBJECT => {
            assert!(vjson_length(v, &mut len) && vjson_object_iter(v, &mut it));
            out.push_str(&format!("{{{len}:"));
            loop {
                let t = vjson_object_next(&mut it, &mut s, &mut len, &mut e);
                if t == 0 {
                    break;
                }
                assert_eq!(t, vjson_type(e));
                // Lookup finds a member with this name.
                assert!(vjson_object_get(v, s, len, std::ptr::null_mut()));
                out.push_str(&format!("k{:?}", bytes(s, len)));
                dump_c(e, out);
            }
            out.push('}');
        }
        t => panic!("type {t} in a parsed document"),
    }
}

/// Parses `text` both ways; returns whether it was accepted.
fn check(p: *mut vjson_parser, text: &[u8]) -> bool {
    unsafe {
        let mut root = std::mem::zeroed::<vjson_value>();
        let mut err = std::mem::zeroed::<vjson_error>();
        let r = vjson_parse(p, text.as_ptr() as *const c_char, text.len(), &mut root, &mut err);
        match verilith_json::parse(text) {
            Ok(doc) => {
                assert_eq!(r, 0, "{:?}", String::from_utf8_lossy(text));
                let (mut a, mut b) = (String::new(), String::new());
                dump_rust(doc.root(), &mut a);
                dump_c(root, &mut b);
                assert_eq!(a, b);
                true
            }
            Err(e) => {
                assert!(r > 0 && r == err.code);
                assert_eq!((err.offset, err.line, err.column), (e.offset, e.line, e.column));
                assert_eq!(vjson_type(root), VJSON_INVALID);
                // The message is the Rust one, without the byte.
                let msg = CStr::from_ptr(vjson_error_message(r)).to_str().unwrap();
                let rust = e.kind.to_string();
                assert!(rust.starts_with(msg) || msg.starts_with("unexpected byte") || msg.starts_with("control")
                    || msg.starts_with("nesting"), "{msg} / {rust}");
                false
            }
        }
    }
}

#[test]
fn agrees_with_the_rust_api() {
    let p = vjson_parser_new();
    let deep = format!("{}1{}", "[".repeat(1000), "]".repeat(1000));
    let too_deep = format!("{}1{}", "[".repeat(1001), "]".repeat(1001));
    let big: String = format!("[{}]", (0..5000).map(|i| format!("{{\"id\": {i}, \"s\": \"x\\ty{i}\"}}")).collect::<Vec<_>>().join(","));
    let docs: &[&str] = &[
        "null", "true", "false", "0", "-0", "1e400", "-1.5e-3", "9223372036854775807", "9223372036854775808",
        "-9223372036854775808", "0.1", "123456789012345678901234567890", "\"\"", "\"a\\u0000b\"",
        "\"\\ud83d\\ude00 \\\"q\\\" \\\\ \\/ \\b\\f\\n\\r\\t\"", "\"é漢字\"", "[]", "{}", "[[]]", "[{}]",
        "{\"a\":{\"b\":{\"c\":[1,2,{\"d\":null}]}}}", "{\"a\":1,\"a\":2,\"\\u0061\":3}", "{\"\":\"\"}",
        " [ 1 , \"two\" , [ 3.0 , false ] , { \"k\" : null } ] ", "\u{feff}[1]",
        &deep, &big,
        // Rejected.
        "", " ", "[", "[1,]", "{\"a\"}", "{\"a\":}", "nul", "01", "1.", "\"abc", "\"\\x\"", "\"\\ud800\"", "\"a\nb\"",
        "[1] 2", "{\"a\":1,}", "[1 2]", "'a'", &too_deep,
    ];
    let mut accepted = 0;
    // Twice, so that every document is also parsed with a used parser.
    for _ in 0..2 {
        for d in docs {
            accepted += check(p, d.as_bytes()) as usize;
        }
    }
    assert_eq!(accepted, 2 * 27);
    assert!(!check(p, b"\"\xff\""));
    assert!(!check(p, b"\"\xc3\""));
    unsafe { vjson_parser_free(p) };
}

/// Every prefix and every single-byte change of a document, both ways.
#[test]
fn mutations_agree() {
    let p = vjson_parser_new();
    let doc = br#"{"k\n": [1, -2.5e3, "s\u00e9", true, null, {"x": []}], "n": 12}"#;
    for i in 0..=doc.len() {
        check(p, &doc[..i]);
    }
    for i in 0..doc.len() {
        for c in [b'"', b'\\', b',', b'[', b'}', b'0', b' ', 0x00, 0xff, b'e'] {
            let mut m = doc.to_vec();
            m[i] = c;
            check(p, &m);
        }
    }
    unsafe { vjson_parser_free(p) };
}

/// JSONTestSuite through the C API, when it is available.
#[test]
fn json_test_suite() {
    let Some(dir) = std::env::var_os("JSON_TEST_SUITE") else { return };
    let p = vjson_parser_new();
    let mut n = 0;
    for f in std::fs::read_dir(dir).unwrap() {
        let path = f.unwrap().path();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let ok = check(p, &std::fs::read(&path).unwrap());
        if name.starts_with("y_") {
            assert!(ok, "{name}");
        } else if name.starts_with("n_") {
            assert!(!ok, "{name}");
        }
        n += 1;
    }
    assert!(n > 300);
    unsafe { vjson_parser_free(p) };
}
