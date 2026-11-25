//! Parameter entities, the external subset and external parsed entities
//! (`pe_spec`, read by `parse` and `parse_with`).

use std::collections::HashMap;
use verilith_xml::pe::Loader;
use verilith_xml::{parse, parse_with, Child, ErrorKind};

/// A loader that reads from `files` by system identifier.
fn files(files: &[(&str, &str)]) -> Loader {
    let m: HashMap<Vec<u8>, Vec<u8>> = files.iter().map(|(k, v)| (k.as_bytes().to_vec(), v.as_bytes().to_vec())).collect();
    Loader::new(move |_base, sys, _pubid| m.get(sys).map(|b| (b.clone(), sys.to_vec())))
}

fn text(s: &[u8]) -> String {
    parse(s).expect("well-formed").root().text()
}

#[test]
fn internal_pe_declares() {
    // A general entity declared by a parameter entity's text (libxml2's
    // xml2 test), and an attribute default.
    let s = br#"<!DOCTYPE test [
<!ELEMENT test (#PCDATA) >
<!ENTITY % xx '&#37;zz;'>
<!ENTITY % zz '&#60;!ENTITY tricky "error-prone" >' >
%xx;
<!ENTITY % att "<!ATTLIST test a CDATA 'x'>">
%att;
]>
<test>This sample shows a &tricky; method.</test>"#;
    let d = parse(s).unwrap();
    assert_eq!(d.root().text(), "This sample shows a error-prone method.");
    assert_eq!(d.root().attribute("a").as_deref(), Some("x"));
}

#[test]
fn pe_errors() {
    // An incomplete declaration in a parameter entity.
    assert!(parse(b"<!DOCTYPE d [<!ENTITY % a \"<!ELEMENT d ANY\"> %a; >]><d/>").is_err());
    // Recursion.
    assert!(parse(b"<!DOCTYPE d [<!ENTITY % a \"&#37;a;\"> %a;]><d/>").is_err());
    // Markup in a general entity declared by a parameter entity.
    assert!(parse(b"<!DOCTYPE d [<!ENTITY % a \"<!ENTITY x '<a>'>\"> %a;]><d>&x;</d>").is_err());
    // A reference in a declaration in the internal subset.
    assert!(parse(b"<!DOCTYPE d [<!ENTITY % n \"d\"><!ELEMENT %n; ANY>]><d/>").is_err());
}

#[test]
fn undeclared_pe_stops_processing() {
    // After a reference to a parameter entity that is not read, later
    // declarations are not processed (§5.1): `x` may be declared outside.
    let s = b"<!DOCTYPE d [%u;<!ENTITY x 'y'>]><d>&x;</d>";
    let d = parse(s).unwrap();
    assert!(d.root().children().any(|c| matches!(c, Child::Unexpanded("x"))));
}

#[test]
fn laughs_hit_the_limit() {
    let mut s = b"<!DOCTYPE d [<!ENTITY % e \"\"><!ENTITY % a0 \"".to_vec();
    s.extend("&#37;e;".repeat(10).as_bytes());
    s.extend(b"\">");
    for i in 1..12 {
        s.extend(format!("<!ENTITY % a{i} \"{}\">", format!("&#37;a{};", i - 1).repeat(10)).as_bytes());
    }
    s.extend(b"%a11;]><d/>");
    assert_eq!(parse(&s).unwrap_err().kind, ErrorKind::Limit);
}

#[test]
fn external_subset() {
    let s = b"<!DOCTYPE d SYSTEM 'd.dtd'><d>&x;</d>";
    // Not read by `parse`: the reference is left.
    assert!(parse(s).is_ok());
    let mut ld = files(&[("d.dtd", "<?xml encoding='UTF-8'?><!ENTITY % p '<!ENTITY x \"y\">'>%p;<![INCLUDE[<!ELEMENT d ANY>]]><![IGNORE[ <!x ]]>")]);
    let d = parse_with(s, &mut ld).unwrap();
    assert_eq!(d.root().text(), "y");
    // A malformed external subset.
    let mut ld = files(&[("d.dtd", "<!ELEMENT d ANY")]);
    assert!(parse_with(s, &mut ld).is_err());
    // A text declaration of another version (erratum E38).
    let mut ld = files(&[("d.dtd", "<?xml version='1.1' encoding='UTF-8'?><!ENTITY x 'y'>")]);
    assert!(parse_with(s, &mut ld).is_err());
}

#[test]
fn external_entities() {
    let s = b"<!DOCTYPE d [<!ENTITY e SYSTEM 'e.xml'><!ENTITY f SYSTEM 'f.xml'>]><d>&e;</d>";
    assert_eq!(text(s), "");
    let mut ld = files(&[("e.xml", "<?xml encoding='UTF-8'?><a>one</a>&f;"), ("f.xml", "two")]);
    let d = parse_with(s, &mut ld).unwrap();
    assert_eq!(d.root().text(), "onetwo");
    // Not content.
    let mut ld = files(&[("e.xml", "<a>"), ("f.xml", "")]);
    assert!(parse_with(s, &mut ld).is_err());
    // Referring to itself, through another.
    let mut ld = files(&[("e.xml", "&f;"), ("f.xml", "&e;")]);
    assert!(parse_with(s, &mut ld).is_err());
    // An entity that is not there is left unread.
    let mut ld = files(&[]);
    assert!(parse_with(s, &mut ld).is_ok());
}
