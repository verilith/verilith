//! The Rust API, and inputs the conformance suite does not stress.
use std::time::Instant;
use verilith_xml::{parse, Child, ErrorKind};

#[test]
fn readme_example() {
    let doc = parse(br#"<?xml version="1.0"?>
<book id="b1" lang='en'>
  <title>Verified &amp; fast</title>
  <price currency="EUR">12.50</price>
</book>"#)
    .unwrap();
    let book = doc.root();
    assert_eq!(book.name(), "book");
    assert_eq!(book.attribute("id").as_deref(), Some("b1"));
    let title = book.elements().next().unwrap();
    assert_eq!(title.text(), "Verified & fast");
    let price = book.elements().nth(1).unwrap();
    assert_eq!(price.attribute("currency").as_deref(), Some("EUR"));
}

#[test]
fn errors_have_positions() {
    let e = parse(b"<a>\n  <b></c>\n</a>").unwrap_err();
    assert_eq!(e.kind, ErrorKind::Syntax);
    assert_eq!((e.line, e.column), (2, 6));
    let e = parse(b"<a x='1' x='2'/>").unwrap_err();
    assert_eq!(e.kind, ErrorKind::Syntax);
    let e = parse(b"<a>\x01</a>").unwrap_err();
    assert_eq!(e.kind, ErrorKind::Encoding);
    assert_eq!(e.offset, 3);
    let e = parse(b"<a>\xff</a>").unwrap_err();
    assert_eq!(e.kind, ErrorKind::Encoding);
    assert!(parse(b"").is_err());
    assert!(parse(b"<a/><b/>").is_err());
    assert!(parse(b"<a>]]></a>").is_err());
    assert!(parse(b"<a>&undeclared;</a>").is_err());
}

#[test]
fn entities_expand_in_place() {
    let doc = parse(
        br#"<!DOCTYPE d [
<!ENTITY who "<b>world</b>">
<!ENTITY greet "hello, &who;!">
<!ATTLIST d kind CDATA "greeting" n NMTOKENS "  1   2 ">
]><d>&greet;</d>"#,
    )
    .unwrap();
    let d = doc.root();
    assert_eq!(d.text(), "hello, world!");
    assert_eq!(d.elements().next().unwrap().name(), "b");
    assert_eq!(d.attribute("kind").as_deref(), Some("greeting"));
    assert_eq!(d.attribute("n").as_deref(), Some("1 2"));
}

#[test]
fn attribute_normalization() {
    let doc = parse(b"<!DOCTYPE a [<!ENTITY d '&#xD;'><!ENTITY s 'x y'>]><a v='&d;&d;A\r\nB\t&s;&#x20;&#xA;'/>").unwrap();
    assert_eq!(doc.root().attribute("v").as_deref(), Some("  A B x y \n"));
}

#[test]
fn utf16_and_latin1() {
    let mut u16 = vec![0xFF, 0xFE];
    for c in "<?xml version='1.0' encoding='UTF-16'?><a b='é'>€</a>".encode_utf16() {
        u16.extend_from_slice(&c.to_le_bytes());
    }
    let doc = parse(&u16).unwrap();
    assert_eq!(doc.root().text(), "€");
    assert_eq!(doc.root().attribute("b").as_deref(), Some("é"));
    let l1 = b"<?xml version='1.0' encoding='ISO-8859-1'?><a>\xe9</a>";
    assert_eq!(parse(l1).unwrap().root().text(), "é");
    // Declared UTF-16, but UTF-8.
    assert!(parse(b"<?xml version='1.0' encoding='UTF-16'?><a/>").is_err());
}

#[test]
fn billion_laughs_parses_without_expanding() {
    let mut s = String::from("<!DOCTYPE lolz [<!ENTITY lol0 'lol'>");
    for i in 1..10 {
        s.push_str(&format!("<!ENTITY lol{i} '{}'>", format!("&lol{};", i - 1).repeat(10)));
    }
    s.push_str("]><lolz a='&lol9;'>&lol9;</lolz>");
    let t = Instant::now();
    let doc = parse(s.as_bytes()).unwrap();
    assert!(t.elapsed().as_millis() < 1000);
    // Reading the attribute is 3 GB: with a limit, it is refused.
    assert!(doc.root().try_attributes(1 << 24).is_err());
    // The children are produced lazily; taking a few costs little.
    assert_eq!(doc.root().children().take(5).count(), 5);
}

#[test]
fn attribute_values_have_no_length_limit() {
    // Ten levels of four references: 4^10 copies of "lol", 3 MiB, read whole.
    let mut s = String::from("<!DOCTYPE lolz [<!ENTITY lol0 'lol'>");
    for i in 1..=10 {
        s.push_str(&format!("<!ENTITY lol{i} '{}'>", format!("&lol{};", i - 1).repeat(4)));
    }
    s.push_str("]><lolz a='&lol10;'/>");
    let doc = parse(s.as_bytes()).unwrap();
    let want = 3 << 20;
    assert_eq!(doc.root().attribute("a").map(|v| v.len()), Some(want));
    assert_eq!(doc.root().attrs().next().map(|a| a.value.len()), Some(want));
    assert!(doc.root().try_attributes(want).is_ok());
    assert!(doc.root().try_attributes(want / 2).is_err());
}

#[test]
fn reference_cycles_are_rejected() {
    assert!(parse(b"<!DOCTYPE a [<!ENTITY x '&y;'><!ENTITY y '&x;'>]><a>&x;</a>").is_err());
    assert!(parse(b"<!DOCTYPE a [<!ENTITY x '&y;'><!ENTITY y '&x;'>]><a/>").is_ok());
}

/// `<!DOCTYPE a [<!ENTITY e0 'x'><!ENTITY e1 '&e0;'>...]>` with `n`
/// entities, each referring to the one before, declared in the order
/// `order` gives, then `body`.
fn chain(n: usize, last_first: bool, body: &str) -> String {
    let mut s = String::from("<!DOCTYPE a [");
    let decl = |i: usize| {
        if i == 0 { "<!ENTITY e0 'x'>".to_string() } else { format!("<!ENTITY e{i} '&e{};'>", i - 1) }
    };
    if last_first {
        for i in (0..n).rev() {
            s.push_str(&decl(i));
        }
    } else {
        for i in 0..n {
            s.push_str(&decl(i));
        }
    }
    s.push_str("]>");
    s.push_str(body);
    s
}

#[test]
fn entity_nesting_has_no_limit() {
    // XML 1.0 sets no depth: 65 deep was rejected before, as libxml2 does
    // past 40.
    for n in [64, 65, 1000] {
        let top = n - 1;
        let s = chain(n, false, &format!("<a>&e{top};</a>"));
        let doc = parse(s.as_bytes()).unwrap();
        assert_eq!(doc.root().text(), "x");
        let s = chain(n, true, &format!("<a v='&e{top};'/>"));
        let doc = parse(s.as_bytes()).unwrap();
        assert_eq!(doc.root().attribute("v").as_deref(), Some("x"));
    }
    // A cycle is still recursion, however long, and an entity that is not
    // referred to may be in one.
    let mut s = chain(1000, false, "<a>&e999;</a>");
    s = s.replacen("<!ENTITY e0 'x'>", "<!ENTITY e0 '&e999;'>", 1);
    assert!(parse(s.as_bytes()).is_err());
    assert!(parse(s.replace("<a>&e999;</a>", "<a/>").as_bytes()).is_ok());
}

#[test]
fn long_entity_chains_are_linear() {
    // A chain declared from its end, the worst order for checking level
    // by level: 100 000 entities, each referring to the next.
    let n = 100_000;
    let top = n - 1;
    for body in [format!("<a>&e{top};</a>"), format!("<a v='&e{top};'/>")] {
        let s = chain(n, true, &body);
        let t = Instant::now();
        let doc = parse(s.as_bytes()).unwrap();
        let ms = t.elapsed().as_millis();
        assert!(ms < 2000, "{ms} ms for a chain of {n}");
        // Reading it expands all 100 000 levels without recursion.
        assert_eq!(doc.root().text() + &doc.root().attribute("v").unwrap_or_default(), "x");
    }
}

#[test]
fn deep_nesting_needs_no_stack() {
    let n = 1_000_000;
    let mut s = Vec::with_capacity(8 * n);
    for _ in 0..n {
        s.extend_from_slice(b"<a>");
    }
    for _ in 0..n {
        s.extend_from_slice(b"</a>");
    }
    let doc = parse(&s).unwrap();
    let mut e = doc.root();
    let mut depth = 1;
    while let Some(c) = e.elements().next() {
        e = c;
        depth += 1;
    }
    assert_eq!(depth, n);
}

#[test]
fn many_attributes() {
    let n = 50_000;
    let mut s = String::from("<a");
    for i in 0..n {
        s.push_str(&format!(" a{i}='{i}'"));
    }
    s.push_str("/>");
    let t = Instant::now();
    let doc = parse(s.as_bytes()).unwrap();
    let ms = t.elapsed().as_millis();
    assert_eq!(doc.root().attributes().len(), n);
    assert!(ms < 2000, "{ms} ms for {n} attributes");
    s.insert_str(2, " a7='x'");
    assert!(parse(s.as_bytes()).is_err());
}

#[test]
fn children_in_order() {
    let doc = parse(b"<r>a<!--c--><?p d?><![CDATA[<x>]]>&#65;<e/></r>").unwrap();
    let kinds: Vec<String> = doc
        .root()
        .children()
        .map(|c| match c {
            Child::Text(t) => format!("T{t}"),
            Child::CData(t) => format!("C{t}"),
            Child::Comment(t) => format!("!{t}"),
            Child::PI(t, d) => format!("?{t} {d}"),
            Child::Element(e) => format!("<{}", e.name()),
            Child::Unexpanded(n) => format!("&{n}"),
        })
        .collect();
    assert_eq!(kinds, ["Ta", "!c", "?p d", "C<x>", "TA", "<e"]);
}

#[test]
fn unread_entities() {
    let doc = parse(b"<!DOCTYPE a SYSTEM 'a.dtd'><a>&nbsp;</a>").unwrap();
    assert!(matches!(doc.root().children().next(), Some(Child::Unexpanded("nbsp"))));
}

#[test]
fn many_entities_and_references() {
    // Entity lookup goes through an index: time stays linear with many
    // declarations and many references to them.
    let n = 20_000;
    let mut s = String::from("<!DOCTYPE a [");
    for i in 0..n {
        s.push_str(&format!("<!ENTITY entity{i:06} 'v{i}'>"));
    }
    s.push_str("]><a>");
    for i in 0..100_000 {
        s.push_str(&format!("&entity{:06};", (i * 7919) % n));
    }
    s.push_str("</a>");
    let t = Instant::now();
    let doc = parse(s.as_bytes()).unwrap();
    assert!(doc.root().text().starts_with("v0v7919"));
    let ms = t.elapsed().as_millis();
    assert!(ms < 2000, "{ms} ms for {n} entities");
    // The first declaration of a name is binding.
    let doc = parse(b"<!DOCTYPE a [<!ENTITY e 'one'><!ENTITY e 'two'>]><a>&e;</a>").unwrap();
    assert_eq!(doc.root().text(), "one");
}

#[test]
fn undeclared_parameter_entities_are_not_fatal() {
    // [69] PEReference carries the VC "Entity Declared", not the WFC: a
    // reference to a parameter entity declared later, or not at all, is
    // well-formed even in a standalone document (the W3C suite's
    // ibm69n05, an `error` test). Declarations after it are processed.
    let d = b"<?xml version='1.0' standalone='yes'?><!DOCTYPE a [%p;<!ENTITY % p 'x'><!ENTITY e 'v'>%q;]><a>&e;</a>";
    let doc = parse(d).unwrap();
    assert!(!doc.has_unread_declarations());
    assert_eq!(doc.root().text(), "v");
}

#[test]
fn entity_declared_depends_on_the_whole_subset() {
    // A parameter entity reference anywhere in the internal subset lifts
    // "Entity Declared", also for an attribute default before it (expat
    // decides it at the default and rejects this; found by fuzzing).
    let d = b"<!DOCTYPE doc [\r\n<!ELEMENT doc (#PCDATA)>\r\n<!ATTLIST doc a CDATA \"&foo;\">\r\n%paaa;\r\n]>\r\n<doc></doc>\r\n";
    let doc = parse(d).unwrap();
    assert!(doc.has_unread_declarations());
    assert_eq!(doc.root().attribute("a").as_deref(), Some("&foo;"));
    // Without the parameter entity reference, it applies.
    assert!(parse(b"<!DOCTYPE doc [<!ATTLIST doc a CDATA \"&foo;\">]><doc/>").is_err());
}

#[test]
fn token_size() {
    // `tape::Tok`: 48-bit positions on a 64-bit target, 32-bit ones on a
    // 32-bit target (or with `narrow-tokens`).
    let narrow = cfg!(any(not(target_pointer_width = "64"), feature = "narrow-tokens"));
    assert_eq!(std::mem::size_of::<verilith_xml::tape::Tok>(), if narrow { 16 } else { 20 });
    assert_eq!(std::mem::align_of::<verilith_xml::tape::Tok>(), 4);
}
