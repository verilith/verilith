//! The comparison of verilith-xml with libexpat: the verdict on a
//! document, and when both accept it, its canonical form (James Clark's:
//! elements, attributes with the DTD's defaults, character data, PIs).
use verilith_xml::{Child, Document, Element};

extern "C" {
    fn expat_canon(p: *const u8, n: usize, out: *mut *mut u8, outn: *mut usize, code: *mut i32) -> i32;
    fn expat_error(code: i32) -> *const std::os::raw::c_char;
    fn free(p: *mut u8);
}

/// expat's message for the error it reports on `data`.
pub fn expat_reason(data: &[u8]) -> String {
    let (mut p, mut n, mut code) = (std::ptr::null_mut(), 0, 0);
    unsafe {
        if expat_canon(data.as_ptr(), data.len(), &mut p, &mut n, &mut code) == 1 {
            free(p);
            return "accepted".into();
        }
        std::ffi::CStr::from_ptr(expat_error(code)).to_string_lossy().into_owned()
    }
}

/// expat's canonical form of `data`, or `None` if it rejects it.
pub fn expat(data: &[u8]) -> Option<Vec<u8>> {
    if data.len() > i32::MAX as usize {
        return None;
    }
    let mut p = std::ptr::null_mut();
    let mut n = 0;
    let mut code = 0;
    unsafe {
        if expat_canon(data.as_ptr(), data.len(), &mut p, &mut n, &mut code) == 0 {
            return None;
        }
        let v = if p.is_null() { Vec::new() } else { std::slice::from_raw_parts(p, n).to_vec() };
        free(p);
        Some(v)
    }
}

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

/// verilith-xml's canonical form of a document.
pub fn ours(doc: &Document) -> Vec<u8> {
    let mut out = Vec::new();
    let (before, after) = doc.outer_pis();
    for (t, d) in before {
        pi(&mut out, t, &d);
    }
    element(&mut out, doc.root());
    for (t, d) in after {
        pi(&mut out, t, &d);
    }
    out
}

/// How the two parsers disagree on `data`, if they do.
#[derive(Debug, PartialEq, Eq)]
pub enum Diff {
    /// verilith-xml accepts and expat rejects.
    OnlyOurs,
    /// expat accepts and verilith-xml rejects.
    OnlyExpat,
    /// Both accept, with different canonical forms.
    Infoset(Vec<u8>, Vec<u8>),
}

pub fn compare(data: &[u8]) -> Option<Diff> {
    let o = verilith_xml::parse(data);
    let e = expat(data);
    match (o, e) {
        (Ok(doc), Some(c)) => {
            // Where declarations were not read, a reference to an entity
            // that was not declared stays in an attribute value here and
            // is dropped by expat.
            if doc.has_unread_declarations() {
                return None;
            }
            let m = ours(&doc);
            if m == c { None } else { Some(Diff::Infoset(m, c)) }
        }
        (Ok(_), None) => Some(Diff::OnlyOurs),
        (Err(_), Some(_)) => Some(Diff::OnlyExpat),
        (Err(_), None) => None,
    }
}

/// `compare`, less the differences that are known and are expat's, each
/// a rule of XML 1.0 that expat does not check:
///
/// * names: expat's name tables are those of XML 1.0 before its Fifth
///   Edition (from Unicode 2.0), give or take (it takes `µ`, U+00B5, for
///   a letter, which no edition does), so verdicts differ either way on
///   names outside ASCII. Allowed where the document has a character
///   outside ASCII or makes one with a character reference.
/// * the version number, `'1.' [0-9]+`: expat accepts `"1"`, `""`, `"1.Y"`.
///   Allowed where the declaration's version is not one.
/// * a byte order mark that disagrees with the declared encoding (the W3C
///   suite's hst-lhs-007 and -008 are not well-formed).
/// * UTF-16 without a byte order mark, which §4.3.3 requires.
/// * a parameter entity referenced before it is declared, in a standalone
///   document (WFC: Entity Declared; the suite's ibm69n05).
/// * the declarations after a parameter entity reference that is not read,
///   which expat stops processing and also stops checking (a `<` in an
///   attribute default there is still not well-formed).
/// * whether an entity must be declared (WFC: Entity Declared), which
///   depends on whether the internal subset has a parameter entity
///   reference anywhere: expat decides it for an attribute default when it
///   reads the default, before a later reference. Allowed where expat
///   reports an undefined entity in a document whose declarations are not
///   all read.
pub fn unexplained(data: &[u8]) -> Option<Diff> {
    let d = compare(data)?;
    let non_ascii = data.iter().any(|&c| c >= 0x80) || data.windows(2).any(|w| w == b"&#");
    match d {
        Diff::OnlyOurs | Diff::OnlyExpat if non_ascii => None,
        Diff::OnlyOurs
            if expat_reason(data) == "undefined entity"
                && verilith_xml::parse(data).map_or(false, |doc| doc.has_unread_declarations()) =>
        {
            None
        }
        Diff::OnlyExpat => {
            let e = verilith_xml::parse(data).err()?;
            let bom8 = data.starts_with(b"\xEF\xBB\xBF");
            let bom16 = data.starts_with(b"\xFF\xFE") || data.starts_with(b"\xFE\xFF");
            let body = if bom8 { &data[3..] } else { data };
            let decl = body.starts_with(b"<?xml") && body.get(5).map_or(false, |c| b" \t\r\n".contains(c));
            let bad_version = decl && verilith_xml::dtd::ex_version_info(body, 5).is_none();
            let declared = verilith_xml::enc::ex_declared_enc(data).map(|(a, b)| data[a..b].to_ascii_uppercase());
            let bom_conflict = (bom8 && declared.as_deref().map_or(false, |n| n != b"UTF-8"))
                || (bom16 && declared.as_deref().map_or(false, |n| n != b"UTF-16"));
            let utf16_text = bom16 || (e.kind == verilith_xml::ErrorKind::Encoding && data.contains(&0));
            let at = |lit: &[u8]| data.get(e.offset..).map_or(false, |r| r.starts_with(lit));
            let pe_first = at(b"%");
            let after_pe = (at(b"<!ATTLIST") || at(b"<!ENTITY"))
                && data[..e.offset].windows(1).any(|w| w == b"%")
                && !data.windows(16).any(|w| w == b"standalone=\"yes\"" || w == b"standalone='yes'");
            if bad_version || bom_conflict || utf16_text || pe_first || after_pe {
                None
            } else {
                Some(Diff::OnlyExpat)
            }
        }
        d => Some(d),
    }
}
