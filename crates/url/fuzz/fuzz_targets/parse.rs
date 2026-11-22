//! Parses arbitrary bytes, optionally against a base (the bytes after the
//! first NUL), reads every getter, and checks that the serialization is a
//! fixed point: parsing the href again gives the same href.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_url::Url;

fn check(u: &Url) {
    let href = u.href().to_owned();
    assert_eq!(href.as_bytes(), u.as_bytes(), "href is not UTF-8");
    let again = Url::parse(&href, None).expect("href does not reparse");
    assert_eq!(again.href(), href, "href is not a fixed point");
    let parts = [
        u.protocol(),
        u.username(),
        u.password(),
        u.host(),
        u.hostname(),
        u.pathname(),
        u.search(),
        u.hash(),
    ];
    for p in parts {
        assert!(href.contains(p) || p == "?" || p == "#" || p.is_empty() || p.ends_with(':'));
    }
    let _ = (u.port(), u.query(), u.fragment(), u.origin(), u.has_opaque_path());
}

fuzz_target!(|data: &[u8]| {
    let (input, base) = match data.iter().position(|&c| c == 0) {
        Some(i) => (&data[..i], Some(&data[i + 1..])),
        None => (data, None),
    };
    let base = base.and_then(|b| Url::parse_bytes(b, None));
    if let Some(b) = &base {
        check(b);
    }
    if let Some(u) = Url::parse_bytes(input, base.as_ref()) {
        check(&u);
    }
});
