//! UTS #46 against IdnaTestV2.txt and the `idna` crate.
use verilith_text::idna::{to_ascii, to_unicode, Options};

/// `None` for strings with an escaped surrogate, which `&str` cannot hold.
fn unescape(s: &str) -> Option<String> {
    let mut out = String::new();
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        if c == '\\' && it.peek() == Some(&'u') {
            it.next();
            let h: String = (0..4).map(|_| it.next().unwrap()).collect();
            out.push(char::from_u32(u32::from_str_radix(&h, 16).unwrap())?);
        } else if c == '\\' && it.peek() == Some(&'x') {
            it.next();
            assert_eq!(it.next(), Some('{'));
            let h: String = it.by_ref().take_while(|&c| c != '}').collect();
            out.push(char::from_u32(u32::from_str_radix(&h, 16).unwrap())?);
        } else {
            out.push(c);
        }
    }
    Some(out)
}

struct Case {
    line: usize,
    source: String,
    to_unicode: String,
    to_unicode_status: Vec<String>,
    to_ascii_n: String,
    to_ascii_n_status: Vec<String>,
    to_ascii_t: String,
    to_ascii_t_status: Vec<String>,
}

fn status(s: &str) -> Option<Vec<String>> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    let s = s.trim_start_matches('[').trim_end_matches(']');
    Some(s.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect())
}

fn field(s: &str, default: &str) -> Option<String> {
    let s = s.trim();
    if s.is_empty() {
        Some(default.to_string())
    } else if s == "\"\"" {
        Some(String::new())
    } else {
        unescape(s)
    }
}

fn cases() -> Vec<Case> {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/IdnaTestV2.txt")).unwrap();
    let mut v = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap();
        if line.trim().is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split(';').collect();
        let Some(source) = field(f[0], "") else { continue };
        let Some(to_unicode) = field(f[1], &source) else { continue };
        let us = status(f[2]).unwrap_or_default();
        let Some(to_ascii_n) = field(f[3], &to_unicode) else { continue };
        let ns = status(f[4]).unwrap_or_else(|| us.clone());
        let Some(to_ascii_t) = field(f[5], &to_ascii_n) else { continue };
        let ts = status(f[6]).unwrap_or_else(|| ns.clone());
        v.push(Case {
            line: i + 1,
            source,
            to_unicode,
            to_unicode_status: us,
            to_ascii_n,
            to_ascii_n_status: ns,
            to_ascii_t,
            to_ascii_t_status: ts,
        });
    }
    v
}

/// Whether an error remains once the codes of the flags that are off are
/// ignored.
fn expect_error(codes: &[String], o: Options) -> bool {
    codes.iter().any(|c| {
        !((!o.verify_dns_length && c.starts_with("A4"))
            || (!o.check_hyphens && (c == "V2" || c == "V3"))
            || (!o.check_joiners && c.starts_with('C'))
            || (!o.check_bidi && c.starts_with('B'))
            || (!o.use_std3_ascii_rules && c == "U1")
            // X4_2 is an empty label in ToUnicode's bidi check, which
            // UTS #46 now leaves to ToASCII's lengths.
            || c == "X4_2")
    })
}

fn run(o: Options) -> Vec<String> {
    let mut fails = Vec::new();
    for c in cases() {
        let (u, ue) = to_unicode(&c.source, o);
        let want_ue = expect_error(&c.to_unicode_status, o);
        if ue.is_err() != want_ue || (!want_ue && u != c.to_unicode) {
            fails.push(format!("{}: toUnicode {:?} -> {:?} {:?}, want {:?} {:?}", c.line, c.source, u, ue, c.to_unicode, c.to_unicode_status));
        }
        for (t, want, codes) in [(false, &c.to_ascii_n, &c.to_ascii_n_status), (true, &c.to_ascii_t, &c.to_ascii_t_status)] {
            let ot = Options { transitional: t, ..o };
            let a = to_ascii(&c.source, ot);
            let want_err = expect_error(codes, ot);
            let ok = match &a {
                Ok(a) => !want_err && a == want,
                Err(_) => want_err,
            };
            if !ok {
                fails.push(format!("{}: toAscii{} {:?} -> {:?}, want {:?} {:?}", c.line, if t { "T" } else { "N" }, c.source, a, want, codes));
            }
        }
    }
    fails
}

#[test]
fn idna_test_v2_strict() {
    let fails = run(Options::STRICT);
    for f in fails.iter().take(40) {
        eprintln!("{f}");
    }
    assert!(fails.is_empty(), "{} failures", fails.len());
}

#[test]
fn idna_test_v2_url() {
    let fails = run(Options::URL);
    for f in fails.iter().take(40) {
        eprintln!("{f}");
    }
    assert!(fails.is_empty(), "{} failures", fails.len());
}

fn random_domain(rng: &mut impl rand::Rng) -> String {
    const PIECES: &[&str] = &[
        "a", "b", "z", "A", "Q", "0", "9", "-", ".", ".", "xn--", "XN--", "xn--a", "xn--ls8h", "xn--fa-hia", "xn--0ca24w",
        "ß", "ẞ", "ς", "\u{200C}", "\u{200D}", "\u{094D}", "\u{0915}", "\u{0628}", "\u{0644}", "\u{064B}", "\u{05D0}",
        "\u{0660}", "\u{06F0}", "\u{0308}", "\u{0301}", "à", "ü", "。", "．", "｡", "\u{00AD}", "_", "%", " ", "ｶ", "①",
        "\u{FB01}", "\u{1F600}", "\u{E0100}", "\u{FFFD}", "\u{0640}", "\u{0627}", "1", "\u{0BCD}", "\u{0B95}",
    ];
    let n = rng.gen_range(0..10);
    let mut s = String::new();
    for _ in 0..n {
        match rng.gen_range(0..10) {
            0 => s.push(rng.gen::<char>()),
            1 => s.push(char::from_u32(rng.gen_range(0x80..0x3000)).unwrap_or('a')),
            _ => s.push_str(PIECES[rng.gen_range(0..PIECES.len())]),
        }
    }
    s
}

#[test]
fn differential_idna_crate() {
    use rand::SeedableRng;
    let mut rng = rand::rngs::StdRng::seed_from_u64(46);
    let mut fails = 0;
    let mut known = 0;
    for _ in 0..300_000 {
        let d = random_domain(&mut rng);
        // The idna crate does not apply UTS #46 criterion V4 (a decoded
        // label must not begin with "xn--") when CheckHyphens is false;
        // IdnaTestV2 expects V4 regardless (it lists V4 apart from V2/V3).
        let (u, _) = verilith_text::idna::domain_to_unicode(&d);
        if u.split('.').any(|l| l.starts_with("xn--") && !l.is_ascii()) {
            known += 1;
            continue;
        }
        // The idna crate runs UTS #46 on ASCII domains too, so compare
        // with ToASCII under the URL flags rather than domain_to_ascii.
        let ours = verilith_text::idna::to_ascii(&d, Options::URL).ok();
        let theirs = idna::domain_to_ascii(&d).ok();
        if ours != theirs {
            fails += 1;
            if fails < 30 {
                eprintln!("domain_to_ascii {d:?} ({:?}): {ours:?} vs {theirs:?}", d.chars().map(|c| c as u32).collect::<Vec<_>>());
            }
        }
        let ours = verilith_text::idna::domain_to_ascii_strict(&d).ok();
        let theirs = idna::domain_to_ascii_strict(&d).ok();
        if ours != theirs {
            fails += 1;
            if fails < 30 {
                eprintln!("strict {d:?}: {ours:?} vs {theirs:?}");
            }
        }
        let (ou, oe) = verilith_text::idna::domain_to_unicode(&d);
        let (tu, te) = idna::domain_to_unicode(&d);
        if oe.is_ok() != te.is_ok() || (oe.is_ok() && ou != tu) {
            fails += 1;
            if fails < 30 {
                eprintln!("domain_to_unicode {d:?}: {ou:?} {oe:?} vs {tu:?} {te:?}");
            }
        }
    }
    eprintln!("{known} inputs with a decoded label beginning with xn-- skipped");
    assert_eq!(fails, 0);
}

/// WPT's toascii.json (from vurl's copy of the URL Standard's tests), with
/// the host parser's checks after domain to ASCII.
#[test]
fn wpt_toascii() {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/toascii.json")).unwrap();
    let mut fails = Vec::new();
    for (input, output) in json_pairs(&text) {
        let got = verilith_text::idna::domain_to_ascii(&input).ok().filter(|r| {
            !r.is_empty()
                && !r.bytes().any(|b| {
                    b <= 0x20 || b == 0x7F || b"#/:<>?@[\\]^|%".contains(&b)
                })
        });
        if got != output {
            fails.push(format!("{input:?}: {got:?}, want {output:?}"));
        }
    }
    for f in &fails {
        eprintln!("{f}");
    }
    assert!(fails.is_empty());
}

/// The `input` and `output` (`None` for null) of each test object.
fn json_pairs(text: &str) -> Vec<(String, Option<String>)> {
    let v: serde_json::Value = serde_json::from_str(text).unwrap();
    v.as_array()
        .unwrap()
        .iter()
        .filter_map(|e| {
            let o = e.as_object()?;
            Some((o["input"].as_str()?.to_string(), o["output"].as_str().map(str::to_string)))
        })
        .collect()
}
