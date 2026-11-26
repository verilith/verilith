//! web-platform-tests URL data (url/resources), run against vurl.
use serde_json::Value;
use verilith_url::Url;

fn load(name: &str) -> Value {
    let path = format!("{}/tests/data/{}", env!("CARGO_MANIFEST_DIR"), name);
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn port_str(u: &Url) -> String {
    u.port().map(|p| p.to_string()).unwrap_or_default()
}

#[test]
fn urltestdata() {
    let data = load("urltestdata.json");
    let mut failures = Vec::new();
    let mut n = 0;
    for case in data.as_array().unwrap() {
        let Some(obj) = case.as_object() else { continue };
        n += 1;
        let input = obj["input"].as_str().unwrap();
        let base = match &obj["base"] {
            Value::String(b) => match Url::parse(b, None) {
                Some(u) => Some(u),
                None => {
                    if obj.get("failure").is_none() {
                        failures.push(format!("base {b:?} failed to parse"));
                    }
                    continue;
                }
            },
            _ => None,
        };
        let got = Url::parse(input, base.as_ref());
        if obj.get("failure").and_then(|f| f.as_bool()) == Some(true) {
            if let Some(u) = got {
                failures.push(format!("{input:?}: expected failure, got {}", u.href()));
            }
            continue;
        }
        let Some(u) = got else {
            failures.push(format!("{input:?} (base {:?}): failed to parse", obj["base"]));
            continue;
        };
        let checks: [(&str, String); 10] = [
            ("href", u.href().to_string()),
            ("protocol", u.protocol().to_string()),
            ("username", u.username().to_string()),
            ("password", u.password().to_string()),
            ("host", u.host().to_string()),
            ("hostname", u.hostname().to_string()),
            ("port", port_str(&u)),
            ("pathname", u.pathname().to_string()),
            ("search", u.search().to_string()),
            ("hash", u.hash().to_string()),
        ];
        for (k, v) in checks.iter() {
            if let Some(Value::String(want)) = obj.get(*k) {
                if want != v {
                    failures.push(format!("{input:?}: {k} = {v:?}, want {want:?}"));
                }
            }
        }
        if let Some(Value::String(want)) = obj.get("origin") {
            if *want != u.origin() {
                failures.push(format!("{input:?}: origin = {:?}, want {want:?}", u.origin()));
            }
        }
    }
    for f in &failures {
        eprintln!("{f}");
    }
    eprintln!("{} cases, {} failures", n, failures.len());
    assert!(failures.is_empty());
}

#[test]
fn toascii() {
    let data = load("toascii.json");
    let mut failures = Vec::new();
    for case in data.as_array().unwrap() {
        let Some(obj) = case.as_object() else { continue };
        let input = obj["input"].as_str().unwrap();
        let want = obj["output"].as_str();
        for (url, getter) in [(format!("https://{input}/x"), true), (format!("http://x/?{input}"), false)] {
            let _ = getter;
            let got = Url::parse(&url, None);
            if url.starts_with("https") {
                match (want, &got) {
                    (Some(w), Some(u)) if u.hostname() == w => {}
                    (None, None) => {}
                    _ => failures.push(format!(
                        "{input:?}: host {:?}, want {want:?}",
                        got.as_ref().map(|u| u.hostname().to_string())
                    )),
                }
            }
        }
    }
    for f in &failures {
        eprintln!("{f}");
    }
    assert!(failures.is_empty());
}

fn apply(u: &mut Url, setter: &str, v: &str) {
    match setter {
        "href" => {
            u.set_href(v);
        }
        "protocol" => {
            u.set_protocol(v);
        }
        "username" => {
            u.set_username(v);
        }
        "password" => {
            u.set_password(v);
        }
        "host" => {
            u.set_host(v);
        }
        "hostname" => {
            let mut h = Vec::new();
            let short = u.hostname_host(v, &mut h);
            let ok = u.set_hostname(v);
            match short {
                None => {}
                Some(None) => assert!(!ok, "hostname_host fails where set_hostname succeeds"),
                Some(Some(_)) => assert!(ok && u.hostname().as_bytes() == h.as_slice(), "hostname_host disagrees"),
            }
        }
        "port" => {
            u.set_port(v);
        }
        "pathname" => {
            u.set_pathname(v);
        }
        "search" => u.set_search(v),
        "hash" => u.set_hash(v),
        _ => panic!("unknown setter {setter}"),
    }
}

#[test]
fn setters() {
    let data = load("setters_tests.json");
    let mut failures = Vec::new();
    let mut n = 0;
    for (setter, cases) in data.as_object().unwrap() {
        if setter == "comment" {
            continue;
        }
        for case in cases.as_array().unwrap() {
            n += 1;
            let href = case["href"].as_str().unwrap();
            let v = case["new_value"].as_str().unwrap();
            let Some(mut u) = Url::parse(href, None) else {
                failures.push(format!("{href:?} failed to parse"));
                continue;
            };
            apply(&mut u, setter, v);
            for (k, want) in case["expected"].as_object().unwrap() {
                let got = match k.as_str() {
                    "href" => u.href().to_string(),
                    "protocol" => u.protocol().to_string(),
                    "username" => u.username().to_string(),
                    "password" => u.password().to_string(),
                    "host" => u.host().to_string(),
                    "hostname" => u.hostname().to_string(),
                    "port" => port_str(&u),
                    "pathname" => u.pathname().to_string(),
                    "search" => u.search().to_string(),
                    "hash" => u.hash().to_string(),
                    _ => continue,
                };
                if want.as_str() != Some(&got) {
                    failures.push(format!("{setter} {href:?} <- {v:?}: {k} = {got:?}, want {want}"));
                }
            }
        }
    }
    for f in &failures {
        eprintln!("{f}");
    }
    eprintln!("{} cases, {} failures", n, failures.len());
    assert!(failures.is_empty());
}

/// UTF-8 decode turns ill-formed UTF-8 into U+FFFD, which UTS #46
/// disallows, so the host fails, whether the bytes arrive raw or
/// percent-encoded, as U+FFFD itself does.
#[test]
fn ill_formed_host() {
    for host in [
        &b"%FF.com"[..],
        b"a%C3.com",
        b"%E2%82.com",
        b"%F0%9F%98.com",
        b"%ED%A0%80.com",
        b"%C0%80.com",
        b"%EF%BF%BD.com",
        b"\xff.com",
        b"\xc3a.com",
        b"\xe2\x82.com",
    ] {
        let mut input = b"http://".to_vec();
        input.extend_from_slice(host);
        input.push(b'/');
        assert!(Url::parse_bytes(&input, None).is_none(), "{:?}", String::from_utf8_lossy(&input));
    }
    // Well-formed non-ASCII still works, raw and percent-encoded.
    assert_eq!(Url::parse_bytes("http://é.com/".as_bytes(), None).unwrap().href(), "http://xn--9ca.com/");
    assert_eq!(Url::parse_bytes(b"http://%C3%A9.com/", None).unwrap().href(), "http://xn--9ca.com/");
}
