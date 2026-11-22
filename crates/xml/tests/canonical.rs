//! The W3C suite's output tests through the Rust API: every test that has
//! an expected output, applies to XML 1.0 Fifth Edition without
//! namespaces, and needs no external entity, is read through
//! `verilith_xml::parse` and written in James Clark's canonical form,
//! which must be the expected output byte for byte. This checks what the
//! API gives a document: character references and entities expanded,
//! attribute values normalized, attribute defaults from the DTD supplied,
//! line ends normalized.
use std::path::{Path, PathBuf};
use verilith_xml::{Child, Document, Element};

fn esc(out: &mut Vec<u8>, s: &str) {
    for c in s.bytes() {
        match c {
            b'&' => out.extend_from_slice(b"&amp;"),
            b'<' => out.extend_from_slice(b"&lt;"),
            b'>' => out.extend_from_slice(b"&gt;"),
            b'"' => out.extend_from_slice(b"&quot;"),
            b'\t' => out.extend_from_slice(b"&#9;"),
            b'\n' => out.extend_from_slice(b"&#10;"),
            b'\r' => out.extend_from_slice(b"&#13;"),
            _ => out.push(c),
        }
    }
}

fn pi(out: &mut Vec<u8>, t: &str, d: &str) {
    out.extend_from_slice(b"<?");
    out.extend_from_slice(t.as_bytes());
    out.push(b' ');
    out.extend_from_slice(d.as_bytes());
    out.extend_from_slice(b"?>");
}

fn element(out: &mut Vec<u8>, e: Element) {
    out.push(b'<');
    out.extend_from_slice(e.name().as_bytes());
    let mut attrs = e.attributes();
    attrs.sort_by(|a, b| a.name.cmp(b.name));
    for a in attrs {
        out.push(b' ');
        out.extend_from_slice(a.name.as_bytes());
        out.extend_from_slice(b"=\"");
        esc(out, &a.value);
        out.push(b'"');
    }
    out.push(b'>');
    for c in e.children() {
        match c {
            Child::Element(c) => element(out, c),
            Child::Text(t) | Child::CData(t) => esc(out, &t),
            Child::PI(t, d) => pi(out, t, &d),
            Child::Comment(_) | Child::Unexpanded(_) => {}
        }
    }
    out.extend_from_slice(b"</");
    out.extend_from_slice(e.name().as_bytes());
    out.push(b'>');
}

pub fn canonical(doc: &Document) -> Vec<u8> {
    let mut out = Vec::new();
    let (before, after) = doc.outer_pis();
    for (t, d) in before {
        pi(&mut out, t, &d);
    }
    let mut nots = doc.notations();
    if !nots.is_empty() {
        nots.sort_by(|a, b| a.0.cmp(b.0));
        out.extend_from_slice(format!("<!DOCTYPE {} [\n", doc.doctype_name().unwrap_or("")).as_bytes());
        for (n, p, s) in nots {
            let ids = match (p, s) {
                (Some(p), Some(s)) => format!("PUBLIC '{p}' '{s}'"),
                (Some(p), None) => format!("PUBLIC '{p}'"),
                (None, Some(s)) => format!("SYSTEM '{s}'"),
                (None, None) => String::new(),
            };
            out.extend_from_slice(format!("<!NOTATION {n} {ids}>\n").as_bytes());
        }
        out.extend_from_slice(b"]>\n");
    }
    element(&mut out, doc.root());
    for (t, d) in after {
        pi(&mut out, t, &d);
    }
    out
}

struct Case {
    id: String,
    path: PathBuf,
    output: PathBuf,
}

fn cases(root: &Path) -> Vec<Case> {
    let text = std::fs::read_to_string(root.join("../cleaned/xmlconf-flattened.xml")).unwrap();
    let opt = roxmltree::ParsingOptions { allow_dtd: true, ..Default::default() };
    let doc = roxmltree::Document::parse_with_options(&text, opt).unwrap();
    let mut out = Vec::new();
    for t in doc.descendants().filter(|n| n.has_tag_name("TEST")) {
        let a = |k: &str| t.attribute(k).unwrap_or("").to_string();
        if a("OUTPUT").is_empty() || a("VERSION") == "1.1" || a("RECOMMENDATION").ends_with("1.1") {
            continue;
        }
        if a("EDITION") != "" && !a("EDITION").split(' ').any(|e| e == "5") {
            continue;
        }
        if a("NAMESPACE") == "yes" || a("RECOMMENDATION").starts_with("NS") {
            continue;
        }
        if a("ENTITIES") != "none" && a("ENTITIES") != "" {
            continue;
        }
        let mut base = PathBuf::new();
        let mut bases: Vec<String> = t
            .ancestors()
            .filter_map(|n| n.attribute(("http://www.w3.org/XML/1998/namespace", "base")).map(|b| b.to_string()))
            .collect();
        bases.reverse();
        for b in bases {
            base.push(b);
        }
        let dir = root.join(base);
        out.push(Case { id: a("ID"), path: dir.join(a("URI")), output: dir.join(a("OUTPUT")) });
    }
    out
}

#[test]
fn canonical_outputs() {
    let Some(root) = std::env::var("XMLCONF").ok().filter(|r| !r.is_empty()) else {
        eprintln!("XMLCONF not set; skipping the W3C output tests");
        return;
    };
    let root = PathBuf::from(root);
    let (mut pass, mut fail) = (0, Vec::new());
    for c in cases(&root) {
        let data = std::fs::read(&c.path).unwrap();
        let want = std::fs::read(&c.output).unwrap();
        match verilith_xml::parse(&data) {
            Err(e) => fail.push(format!("{}: rejected: {e}", c.id)),
            Ok(doc) => {
                let got = canonical(&doc);
                if got == want {
                    pass += 1;
                } else {
                    fail.push(format!(
                        "{}: {}\n    got  {:?}\n    want {:?}",
                        c.id,
                        c.path.display(),
                        String::from_utf8_lossy(&got),
                        String::from_utf8_lossy(&want)
                    ));
                }
            }
        }
    }
    eprintln!("canonical outputs: {pass} match, {} differ", fail.len());
    for f in &fail {
        eprintln!("  {f}");
    }
    assert!(fail.is_empty());
}
