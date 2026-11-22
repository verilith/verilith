//! XML through verilith-xml's own API, the jobs of suites/xml/expat.c:
//!
//!   vxml-run read    cases read/FILE: parse, then visit every element,
//!                    every attribute (name and normalized value) and every
//!                    run of character data
//!   vxml-run check   cases check/FILE: the verified well-formedness check
//!                    alone (`verilith_xml::check`, into a reused tape)
//!
//! The check values are expat's: counts and byte totals.
use verilith_xml::{Child, Element};

#[derive(Default)]
struct Acc {
    elems: u64,
    attrs: u64,
    text: u64,
    values: u64,
}

fn walk(e: Element, a: &mut Acc) {
    a.elems += 1;
    for at in e.attrs() {
        a.attrs += 1;
        a.values += at.value.len() as u64;
    }
    for c in e.children() {
        match c {
            Child::Element(c) => walk(c, a),
            Child::Text(t) | Child::CData(t) => a.text += t.len() as u64,
            _ => {}
        }
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "read".into());
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let Some(stem) = [".xml", ".svg", ".plist"].iter().find_map(|x| name.strip_suffix(x)) else { continue };
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = data.len() as u64;
        if mode == "check" {
            let mut tape = verilith_xml::tape::Tape::new();
            r.case(format!("check/{stem}"), len, move || verilith_xml::check(std::hint::black_box(&data), &mut tape) as u64);
        } else {
            r.case(format!("read/{stem}"), len, move || {
                let doc = verilith_xml::parse(std::hint::black_box(&data)).unwrap();
                let mut a = Acc::default();
                walk(doc.root(), &mut a);
                a.elems * 1000003 + a.attrs * 1009 + a.text * 31 + a.values
            });
        }
    }
    r.main();
}
