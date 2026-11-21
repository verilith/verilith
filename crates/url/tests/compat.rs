//! The `url`-crate-shaped API (`verilith_url::compat`) against the `url` crate.
//!
//! On every WPT input and the bundled corpus, where both crates produce the
//! same href, every accessor must agree, so code moving from `url` to
//! `verilith_url::compat` sees the same values. Where the hrefs differ the `url`
//! crate departs from the Standard (vurl passes WPT in full); those inputs
//! are counted, not compared.
use serde_json::Value;
use verilith_url::compat;

fn inputs() -> Vec<(String, Option<String>)> {
    let path = format!("{}/tests/data/urltestdata.json", env!("CARGO_MANIFEST_DIR"));
    let data: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let mut v = Vec::new();
    for case in data.as_array().unwrap() {
        let Some(obj) = case.as_object() else { continue };
        let base = obj["base"].as_str().map(str::to_owned);
        v.push((obj["input"].as_str().unwrap().to_owned(), base));
    }
    v
}

fn compare(a: &compat::Url, b: &url::Url) -> Vec<&'static str> {
    let mut bad = Vec::new();
    macro_rules! eq {
        ($name:literal, $x:expr, $y:expr) => {
            if $x != $y {
                bad.push($name);
            }
        };
    }
    eq!("scheme", a.scheme(), b.scheme());
    eq!("username", a.username(), b.username());
    eq!("password", a.password(), b.password());
    eq!("host_str", a.host_str(), b.host_str());
    eq!("domain", a.domain(), b.domain());
    eq!("host", a.host().map(|h| h.to_string()), b.host().map(|h| h.to_string()));
    eq!("port", a.port(), b.port());
    eq!("port_or_known_default", a.port_or_known_default(), b.port_or_known_default());
    eq!("path", a.path(), b.path());
    eq!(
        "path_segments",
        a.path_segments().map(|s| s.collect::<Vec<_>>()),
        b.path_segments().map(|s| s.collect::<Vec<_>>())
    );
    eq!("query", a.query(), b.query());
    eq!("fragment", a.fragment(), b.fragment());
    eq!("cannot_be_a_base", a.cannot_be_a_base(), b.cannot_be_a_base());
    eq!("has_host", a.has_host(), b.has_host());
    // The url crate gives blob: URLs of any scheme a tuple origin; the
    // Standard now does so only for http and https.
    if a.scheme() != "blob" {
        eq!("origin", a.origin_ascii(), b.origin().ascii_serialization());
    }
    eq!(
        "query_pairs",
        a.query_pairs().collect::<Vec<_>>(),
        b.query_pairs().map(|(k, v)| (k.into_owned(), v.into_owned())).collect::<Vec<_>>()
    );
    bad
}

#[test]
fn accessors_match_url_crate() {
    let (mut same, mut differ, mut both_fail, mut same_reason) = (0, 0, 0, 0);
    let mut failures = Vec::new();
    for (input, base) in inputs() {
        let (a, b) = match &base {
            Some(base) => {
                let (Ok(ab), Ok(bb)) = (compat::Url::parse(base), url::Url::parse(base)) else { continue };
                (ab.join(&input), bb.join(&input))
            }
            None => (compat::Url::parse(&input), url::Url::parse(&input)),
        };
        match (a, b) {
            (Ok(a), Ok(b)) if a.as_str() == b.as_str() => {
                same += 1;
                let bad = compare(&a, &b);
                if !bad.is_empty() {
                    failures.push(format!("{input:?} base {base:?}: {bad:?}"));
                }
            }
            (Err(a), Err(b)) => {
                both_fail += 1;
                if a.to_string() == b.to_string() {
                    same_reason += 1;
                }
            }
            _ => differ += 1,
        }
    }
    eprintln!("same href: {same}, both rejected: {both_fail} (same reason: {same_reason}), url crate differs: {differ}");
    assert!(same > 500);
    assert!(failures.is_empty(), "{} mismatches:\n{}", failures.len(), failures.join("\n"));
}

#[test]
fn parse_errors() {
    use compat::ParseError::*;
    // (input, reason, whether the url crate gives the same reason)
    let cases: &[(&str, compat::ParseError, bool)] = &[
        ("foo", RelativeUrlWithoutBase, true),
        ("http://", EmptyHost, true),
        ("http://a:99999/", InvalidPort, true),
        ("http://a:1x/", InvalidPort, true),
        ("http://[::1/", InvalidIpv6Address, true),
        ("http://[1::2::3]/", InvalidIpv6Address, true),
        ("http://1.2.3.256/", InvalidIpv4Address, true),
        ("http://0x100000000/", InvalidIpv4Address, true),
        ("http://\u{FFFD}/", IdnaError, true),
        ("http://%ef%bf%bd/", IdnaError, true),
        ("http://\u{300}a/", IdnaError, true),
        ("sc://a b/", InvalidDomainCharacter, true),
        ("sc://:1/", EmptyHost, true),
        ("http://@:www.example.com", EmptyHost, true),
        // The Standard rejects these as forbidden code points after UTS 46
        // mapping; as in the url crate, they are reported as IDNA errors.
        ("http://a b/", IdnaError, true),
        ("http://a<b/", IdnaError, true),
        ("file://example:1/", IdnaError, true),
    ];
    for &(input, want, agrees) in cases {
        assert_eq!(compat::Url::parse(input).err(), Some(want), "{input}");
        if agrees {
            assert_eq!(url::Url::parse(input).err().map(|e| e.to_string()), Some(want.to_string()), "url crate on {input}");
        }
    }
    let base = compat::Url::parse("mailto:x@y").unwrap();
    assert_eq!(base.join("z").err(), Some(RelativeUrlWithCannotBeABaseBase));
}

#[test]
fn setters_match_url_crate() {
    let start = "https://user:pw@example.com:8080/a/b?q=1#f";
    let mut a = compat::Url::parse(start).unwrap();
    let mut b = url::Url::parse(start).unwrap();
    macro_rules! both {
        ($($t:tt)*) => {
            assert_eq!(a.$($t)*.is_ok(), b.$($t)*.is_ok(), stringify!($($t)*));
            assert_eq!(a.as_str(), b.as_str(), stringify!($($t)*));
        };
    }
    macro_rules! both_unit {
        ($($t:tt)*) => {
            a.$($t)*;
            b.$($t)*;
            assert_eq!(a.as_str(), b.as_str(), stringify!($($t)*));
        };
    }
    both!(set_scheme("http"));
    both!(set_port(Some(81)));
    both!(set_port(None));
    both!(set_username("bob"));
    both!(set_password(Some("s3cret")));
    both!(set_password(None));
    both!(set_host(Some("example.org")));
    both!(set_host(Some("10.0.0.1")));
    both_unit!(set_path("/x y/z"));
    both_unit!(set_query(Some("a=b c")));
    both_unit!(set_query(Some("")));
    both_unit!(set_query(None));
    both_unit!(set_fragment(Some("frag ment")));
    both_unit!(set_fragment(Some("")));
    both_unit!(set_fragment(None));
    a.query_pairs_mut().append_pair("k", "v w").append_pair("&", "=");
    b.query_pairs_mut().append_pair("k", "v w").append_pair("&", "=");
    assert_eq!(a.as_str(), b.as_str());
    a.query_pairs_mut().clear();
    b.query_pairs_mut().clear();
    assert_eq!(a.as_str(), b.as_str());

    let mut a = compat::Url::parse("foo://h/p").unwrap();
    let mut b = url::Url::parse("foo://h/p").unwrap();
    both!(set_host(None));
    both!(set_host(Some("h2")));
    let mut a = compat::Url::parse("mailto:x").unwrap();
    let mut b = url::Url::parse("mailto:x").unwrap();
    both!(set_host(Some("h")));
    both!(set_username("u"));
    both!(set_port(Some(1)));
}

/// Long fragments and queries, where the scanners skip 16-byte blocks: every
/// byte value at every offset of a 40-byte run must encode as the `url`
/// crate does.
#[test]
fn long_fragments_and_queries_match_url_crate() {
    let chars: Vec<char> = (0x20u8..0x7F).map(|b| b as char).chain(['é', '\u{7F}', '\t', '\u{1}']).collect();
    for &c in &chars {
        for pos in [0usize, 7, 15, 16, 17, 31, 39] {
            let mut run: String = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMN".to_owned();
            run.replace_range(pos..pos + 1, &c.to_string());
            for input in [format!("http://h/p#{run}"), format!("http://h/p?{run}"), format!("http://h/p?{run}#{run}")] {
                let (Ok(a), Ok(b)) = (compat::Url::parse(&input), url::Url::parse(&input)) else { continue };
                assert_eq!(a.as_str(), b.as_str(), "{input:?}");
            }
        }
    }
}
