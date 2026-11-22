//! The Rust API against serde_json: they must accept the same texts (except
//! where serde_json is stricter: its depth limit of 128, numbers too large
//! for f64 (vjson reads them as infinity), and a leading byte order mark,
//! which vjson skips), and what vjson accepts must survive a write and parse round
//! trip, serde deserialization must agree with serde_json's, and the eager
//! and lazy parsers must read the same strings and the same numbers as
//! `f64::from_str`.
#![no_main]
use libfuzzer_sys::fuzz_target;

fn same(a: verilith_json::Value, b: verilith_json::Value) -> bool {
    use verilith_json::Type::*;
    match (a.kind(), b.kind()) {
        (Null, Null) => true,
        (Bool, Bool) => a.as_bool() == b.as_bool(),
        (Number, Number) => a.as_number_str() == b.as_number_str(),
        (String, String) => a.as_bytes() == b.as_bytes(),
        (Array, Array) => a.len() == b.len() && a.elements().unwrap().zip(b.elements().unwrap()).all(|(x, y)| same(x, y)),
        (Object, Object) => {
            a.len() == b.len()
                && a.members().unwrap().zip(b.members().unwrap()).all(|((k, x), (l, y))| k.as_bytes() == l.as_bytes() && same(x, y))
        }
        _ => false,
    }
}

/// Same values, read through the two parsers' payloads.
fn same_read(a: verilith_json::Value, b: verilith_json::Value) -> bool {
    use verilith_json::Type::*;
    match a.kind() {
        Number => {
            let want = a.as_number_str().unwrap().parse::<f64>().unwrap().to_bits();
            a.as_f64().map(f64::to_bits) == Some(want) && b.as_f64().map(f64::to_bits) == Some(want)
        }
        String => a.as_bytes() == b.as_bytes(),
        Array => a.elements().unwrap().zip(b.elements().unwrap()).all(|(x, y)| same_read(x, y)),
        Object => a
            .members()
            .unwrap()
            .zip(b.members().unwrap())
            .all(|((k, x), (l, y))| k.as_bytes() == l.as_bytes() && same_read(x, y)),
        _ => true,
    }
}

fuzz_target!(|data: &[u8]| {
    let ours = verilith_json::parse(data);
    let theirs = serde_json::from_slice::<serde_json::Value>(data);
    match (&ours, &theirs) {
        (Ok(_), Err(_)) if data.starts_with(b"\xEF\xBB\xBF") => {}
        (Ok(_), Err(e)) => {
            let m = e.to_string();
            assert!(
                m.contains("recursion limit") || m.contains("number out of range"),
                "vjson accepted, serde_json: {m}"
            );
        }
        (Err(e), Ok(_)) => panic!("vjson rejected ({e}), serde_json accepted"),
        _ => {}
    }
    if let Ok(doc) = ours {
        let mut lazy = verilith_json::Parser::lazy();
        let l = lazy.parse(data).expect("lazy parser agrees");
        assert!(same_read(doc.root(), l.root()), "eager and lazy reads differ");
        let out = doc.to_vec();
        let back = verilith_json::parse(&out).expect("written text must parse");
        assert!(same(doc.root(), back.root()), "round trip differs");
        if let Ok(theirs) = theirs {
            let mine: serde_json::Value = verilith_json::from_slice(data).expect("serde from_slice");
            assert_eq!(mine, theirs, "serde values differ");
        }
    }
});
