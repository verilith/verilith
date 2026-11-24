//! The W3C XML Conformance Test Suite (20130923), when `XMLCONF` names its
//! `xmlconf` directory (`ci.sh` fetches it).
//!
//! Every test that applies to XML 1.0, Fifth Edition, without namespaces
//! is run: `valid`, `invalid` (well-formed but not valid) and the output
//! tests must be accepted, `not-wf` must be rejected. Tests whose verdict
//! depends on reading an external entity, which this processor does not
//! (§5.1 lets a non-validating processor skip them), and documents in
//! encodings other than UTF-8, which it rejects (§4.3.3), are counted
//! apart; each is listed in `EXPECTED` with the reason.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

struct Case {
    id: String,
    ty: String,
    entities: String,
    path: PathBuf,
}

fn cases(root: &Path) -> Vec<Case> {
    let cat = root.join("../cleaned/xmlconf-flattened.xml");
    let text = std::fs::read_to_string(&cat).expect("xmlconf-flattened.xml");
    let opt = roxmltree::ParsingOptions { allow_dtd: true, ..Default::default() };
    let doc = roxmltree::Document::parse_with_options(&text, opt).expect("catalog");
    let mut out = Vec::new();
    for t in doc.descendants().filter(|n| n.has_tag_name("TEST")) {
        let a = |k: &str| t.attribute(k).unwrap_or("").to_string();
        if a("VERSION") == "1.1" || a("RECOMMENDATION").ends_with("1.1") {
            continue;
        }
        if a("EDITION") != "" && !a("EDITION").split(' ').any(|e| e == "5") {
            continue;
        }
        if a("NAMESPACE") == "yes" || a("RECOMMENDATION").starts_with("NS") {
            continue;
        }
        // xml:base from the enclosing TESTCASES elements, innermost last.
        let mut base = PathBuf::new();
        let mut bases: Vec<String> = t
            .ancestors()
            .filter_map(|n| n.attribute(("http://www.w3.org/XML/1998/namespace", "base")).map(|b| b.to_string()))
            .collect();
        bases.reverse();
        for b in bases {
            base.push(b);
        }
        out.push(Case { id: a("ID"), ty: a("TYPE"), entities: a("ENTITIES"), path: root.join(base).join(a("URI")) });
    }
    out
}

/// Tests whose result here differs from the catalog's, and why. Each is
/// a choice the Recommendation leaves to a non-validating processor.
const EXPECTED: &[(&str, &str)] = &[];

/// The `error` tests that are rejected: an error is not a fatal error, so
/// the document is well-formed and every other `error` test must be
/// accepted. These are in encodings this processor does not read, which
/// §4.3.3 makes a fatal error ("an encoding that it is unable to
/// process"); only UTF-8 and UTF-16 are required.
const REJECTED_ERRORS: &[&str] = &[
    "pr-xml-euc-jp",
    "pr-xml-iso-2022-jp",
    "pr-xml-shift_jis",
    "weekly-euc-jp",
    "weekly-iso-2022-jp",
    "weekly-shift_jis",
];

#[test]
fn xmlconf() {
    run(false);
}

/// The suite again, reading external entities from the suite's files.
#[test]
fn xmlconf_external() {
    run(true);
}

fn run(ext: bool) {
    let Some(root) = std::env::var("XMLCONF").ok().filter(|r| !r.is_empty()) else {
        eprintln!("XMLCONF not set; skipping the W3C conformance suite");
        return;
    };
    let root = PathBuf::from(root);
    let expected: BTreeMap<&str, &str> = EXPECTED.iter().cloned().collect();
    let mut tape = verilith_xml::tape::Tape::new();
    let (mut pass, mut ext_ok, mut fail) = (0, 0, Vec::new());
    let mut seen_expected = 0;
    for c in cases(&root) {
        let Ok(data) = std::fs::read(&c.path) else {
            fail.push(format!("{}: cannot read {}", c.id, c.path.display()));
            continue;
        };
        let ok = if ext {
            let dir = c.path.parent().unwrap().to_path_buf();
            let mut ld = verilith_xml::pe::Loader::new(move |base: &[u8], sys: &[u8], _pubid: &[u8]| {
                let from = if base.is_empty() {
                    dir.clone()
                } else {
                    PathBuf::from(String::from_utf8_lossy(base).into_owned()).parent()?.to_path_buf()
                };
                let p = from.join(String::from_utf8_lossy(sys).into_owned());
                let b = std::fs::read(&p).ok()?;
                Some((b, p.to_string_lossy().into_owned().into_bytes()))
            });
            verilith_xml::check_with(&data, &mut tape, &mut ld)
        } else {
            verilith_xml::check(&data, &mut tape)
        };
        let want = match c.ty.as_str() {
            "not-wf" => Some(false),
            "valid" | "invalid" => Some(true),
            // "error": well-formed, so accepted, but for the encodings.
            _ => Some(!REJECTED_ERRORS.contains(&c.id.as_str())),
        };
        let Some(want) = want else { continue };
        if ok == want {
            if expected.contains_key(c.id.as_str()) {
                fail.push(format!("{}: listed in EXPECTED but now passes", c.id));
            }
            pass += 1;
        } else if let Some(why) = expected.get(c.id.as_str()) {
            let _ = why;
            seen_expected += 1;
        } else if !ext && !want && c.entities != "none" && c.entities != "" {
            // A not-wf test that may only be detectable in an external
            // entity, which is not read (they are all read, and every such
            // test rejected, in `xmlconf_external`).
            ext_ok += 1;
            eprintln!("external? {} ({}) {}", c.id, c.entities, c.path.display());
        } else {
            fail.push(format!(
                "{}: {} ({}), got {} — {}",
                c.id,
                c.ty,
                c.entities,
                if ok { "accepted" } else { "rejected" },
                c.path.display()
            ));
        }
    }
    eprintln!(
        "xmlconf: {pass} as expected, {seen_expected} listed differences, {ext_ok} not-wf only through external entities, {} failures",
        fail.len()
    );
    for f in &fail {
        eprintln!("  {f}");
    }
    assert!(fail.is_empty(), "{} conformance failures", fail.len());
}
