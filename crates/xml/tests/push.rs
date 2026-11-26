//! The push parser (`reader::Reader`, over `push::Stream`) against the
//! whole-document parse: fed any way the input can be cut into chunks, it
//! must reach the same verdict and emit the same items, and keep only a
//! bounded window of the input, in every encoding it reads.
//!
//! The documents: the ones here, and with `XMLCONF` set (`ci.sh` sets it)
//! every file of the W3C XML Conformance Test Suite.
use std::path::Path;
use verilith_xml::push::{R_ERR, R_LIMIT, R_MORE, R_OK, R_WHOLE};
use verilith_xml::reader::Reader;
use verilith_xml::stream::{P_CR, P_FIRST, P_LAST};
use verilith_xml::tape::{Kind, Tape, Tok};

/// An item, without positions: what both parses must agree on.
#[derive(Debug, PartialEq, Eq, Clone)]
enum Ev {
    /// A token, with the text its span covers (or its numbers, where they
    /// are not a span).
    Tok(Kind, Vec<u8>),
    /// An end tag.
    End,
    /// Character data, and a CDATA section's, merged.
    Text(Vec<u8>),
    CData(Vec<u8>),
}

fn kind_ev(text: &[u8], t: &Tok) -> Ev {
    let (a, b) = (t.a(), t.b());
    match t.kind {
        Kind::ETag => Ev::End,
        // A character reference carries its code point.
        Kind::CharRef => Ev::Tok(Kind::CharRef, format!("{b}").into_bytes()),
        k if a <= b && b <= text.len() => Ev::Tok(k, text[a..b].to_vec()),
        k => Ev::Tok(k, format!("{a},{b}").into_bytes()),
    }
}

/// The events of the whole document's tape.
fn whole_events(text: &[u8], tape: &Tape) -> Vec<Ev> {
    let mut out = Vec::new();
    for t in &tape.toks {
        match t.kind {
            Kind::Text => match out.last_mut() {
                Some(Ev::Text(v)) => v.extend_from_slice(&text[t.a()..t.b()]),
                _ => out.push(Ev::Text(text[t.a()..t.b()].to_vec())),
            },
            Kind::CData => out.push(Ev::CData(text[t.a()..t.b()].to_vec())),
            _ => out.push(kind_ev(text, t)),
        }
    }
    out
}

/// Pushes `doc` in the chunks `cut` gives; the verdict, the events, and the
/// largest window the stream kept.
fn pushed(doc: &[u8], cut: &mut dyn FnMut() -> usize) -> (u8, Vec<Ev>, usize) {
    let mut st = Reader::new();
    let mut out: Vec<Ev> = Vec::new();
    let mut in_cdata = false;
    let mut at = 0;
    let mut max = 0;
    loop {
        let n = cut().max(1).min(doc.len() - at);
        let last = at + n == doc.len();
        let r = st.feed(&doc[at..at + n], last);
        at += n;
        let tape = st.take_out();
        let w = st.window();
        max = max.max(w.len());
        for t in &tape.toks {
            if matches!(t.kind, Kind::Text | Kind::CData) {
                // The flags the proof is about: P_CR exactly when the piece
                // has a carriage return, P_FIRST and P_LAST only on CDATA.
                assert_eq!(t.f & P_CR != 0, w[t.a()..t.b()].contains(&b'\r'));
                assert!(t.f < 8 && (t.kind == Kind::CData || t.f & (P_FIRST | P_LAST) == 0));
            }
            match t.kind {
                Kind::Text => match out.last_mut() {
                    Some(Ev::Text(v)) => v.extend_from_slice(&w[t.a()..t.b()]),
                    _ => out.push(Ev::Text(w[t.a()..t.b()].to_vec())),
                },
                Kind::CData => {
                    if t.f & P_FIRST != 0 || !in_cdata {
                        out.push(Ev::CData(Vec::new()));
                    }
                    if let Some(Ev::CData(v)) = out.last_mut() {
                        v.extend_from_slice(&w[t.a()..t.b()]);
                    }
                    in_cdata = t.f & P_LAST == 0;
                }
                _ => out.push(kind_ev(w, t)),
            }
        }
        match r {
            R_MORE => assert!(!last, "more asked for after the last chunk"),
            R_OK | R_ERR | R_WHOLE | R_LIMIT => return (r, out, max),
            _ => unreachable!(),
        }
        assert!(at < doc.len());
    }
}

/// A small generator of chunk sizes, the same on every run.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, m: usize) -> usize {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % m + 1
    }
}

/// Checks `doc` pushed in chunks of every kind against its whole parse;
/// whether it was read as it came (and accepted).
fn check(name: &str, doc: &[u8]) -> bool {
    if doc.is_empty() {
        return false;
    }
    let mut accepted = false;
    let mut tape = Tape::new();
    let whole = verilith_xml::enc::ex_parse(doc, &mut tape);
    // The items are in the text: the input, or the input decoded.
    let text: Vec<u8> = match &whole {
        Some((Some(v), _)) => v.clone(),
        _ => doc.to_vec(),
    };
    let expect = whole.as_ref().map(|_| whole_events(&text, &tape));
    let mut sizes: Vec<Box<dyn FnMut() -> usize>> = vec![
        Box::new(|| 1),
        Box::new(|| 2),
        Box::new(|| 3),
        Box::new(|| 7),
        Box::new(|| 64),
        Box::new(|| 4096),
        Box::new(|| usize::MAX),
    ];
    for seed in 1..4u64 {
        let mut g = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15) ^ doc.len() as u64);
        sizes.push(Box::new(move || g.next(40)));
    }
    for (k, cut) in sizes.iter_mut().enumerate() {
        let (r, evs, _) = pushed(doc, cut.as_mut());
        match r {
            R_WHOLE => {
                // Only a document whose encoding is not known from its
                // first bytes and declaration is handed back, before
                // anything is emitted; that is not a document read here.
                assert!(evs.is_empty(), "{name} (cut {k}): events before the input was handed back");
                assert!(whole.is_none(), "{name} (cut {k}): a document read here handed back");
            }
            R_OK => {
                assert!(whole.is_some(), "{name} (cut {k}): accepted, rejected whole");
                assert_eq!(Some(&evs), expect.as_ref(), "{name} (cut {k}): other events than the whole parse's");
                accepted = true;
            }
            R_ERR => {
                assert!(whole.is_none(), "{name} (cut {k}): rejected, accepted whole");
            }
            _ => panic!("{name} (cut {k}): verdict {r}"),
        }
    }
    accepted
}

const DOCS: &[&str] = &[
    "<a/>",
    "<?xml version='1.0'?><a/>",
    "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone='yes'?>\n<!-- c --><?pi x?><a b='1' c=\"&amp;\">t&#x41;<![CDATA[x]]y]]>z</a>\n<!--e-->",
    "\u{FEFF}<a>\r\n\r</a>",
    "<!DOCTYPE a [<!ENTITY e 'v<b/>'><!ATTLIST a x CDATA 'd'><!-- ] > --><?p ]>?>]><a>&e;&e;</a>",
    "<!DOCTYPE a SYSTEM 'x.dtd'><a>&undeclared;</a>",
    "<a>]]></a>",
    "<a></b>",
    "<a>",
    "<a/><b/>",
    "<a><b><c>deep</c></b>text<b/></a>   ",
    "<a x='1' x='2'/>",
    "<a>\u{10000}\u{FFFD}é</a>",
    "<a>\u{1}</a>",
    "<?xml version='1.0' encoding='ISO-8859-1'?><a>\u{e9}</a>",
    "<a><![CDATA[]]></a>",
    "<a><![CDATA[]]]]></a>",
    "<a>x]]y]</a>",
];

#[test]
fn chunks_agree_with_the_whole_parse() {
    let n = DOCS.iter().filter(|d| check(d, d.as_bytes())).count();
    assert_eq!(n, 12, "documents read as they came and accepted");
    // A cut inside every multi-byte character, and a byte that is not
    // UTF-8 at the end of a chunk.
    assert!(!check("bad utf-8", b"<a>\xe2\x82</a>"));
    assert!(!check("latin-1 bytes", b"<a>\xe9</a>"));
}

/// `s` in UTF-16, after a byte order mark.
fn utf16(s: &str, le: bool) -> Vec<u8> {
    let mut v = if le { vec![0xFF, 0xFE] } else { vec![0xFE, 0xFF] };
    for u in s.encode_utf16() {
        let b = if le { u.to_le_bytes() } else { u.to_be_bytes() };
        v.extend_from_slice(&b);
    }
    v
}

#[test]
fn other_encodings_as_they_come() {
    let doc = "<?xml version='1.0' encoding='UTF-16'?>\n<a b='\u{e9}'>t\u{10000}\u{FFFD}<![CDATA[\u{4e2d}]]>&#x41;</a>";
    for le in [true, false] {
        assert!(check("utf-16", &utf16(doc, le)));
        assert!(check("utf-16, no declaration", &utf16("<a>\u{1F600}</a>", le)));
        // Cut short: an odd byte, half of a pair.
        let mut v = utf16("<a/>", le);
        v.push(b' ');
        assert!(!check("utf-16, an odd byte", &v));
        let mut v = utf16("<a/>", le);
        v.extend_from_slice(if le { &[0x3D, 0xD8] } else { &[0xD8, 0x3D] });
        assert!(!check("utf-16, half a pair at the end", &v));
        let v = utf16("<a>\u{1F600}</a>", le);
        let mut w = v.clone();
        // The low half of the pair turned into a letter.
        let k = 2 + 2 * 3 + 2;
        w[k..k + 2].copy_from_slice(if le { &[0x41, 0] } else { &[0, 0x41] });
        assert!(!check("utf-16, a lone surrogate", &w));
        // Declared as another encoding.
        assert!(!check("utf-16, declared UTF-8", &utf16("<?xml version='1.0' encoding='UTF-8'?><a/>", le)));
    }
    let l1 = b"<?xml version='1.0' encoding='iso-8859-1'?>\n<a b='\xe9\xff'>\xe9\x80\xa0<![CDATA[\xfe]]></a>\n";
    assert!(check("iso-8859-1", l1));
    let asc = b"<?xml version=\"1.0\" encoding=\"US-ASCII\"?><a b='x'>text</a>";
    assert!(check("us-ascii", asc));
    assert!(!check("us-ascii, a byte above 0x7F", b"<?xml version='1.0' encoding='US-ASCII'?><a>\xe9</a>"));
    assert!(!check("us-ascii, one at the end", b"<?xml version='1.0' encoding='US-ASCII'?><a/>\x80"));
    // An encoding not read here, and a byte order mark alone.
    assert!(!check("koi8-r", b"<?xml version='1.0' encoding='KOI8-R'?><a/>"));
    assert!(!check("a byte order mark alone", b"\xff\xfe"));
    assert!(!check("half a byte order mark", b"\xfe"));
}

#[test]
fn the_window_stays_small() {
    // Many items, each small: the window holds about one of them.
    let mut doc = b"<?xml version='1.0'?><!DOCTYPE r [<!ENTITY e 'x'>]><r>".to_vec();
    for i in 0..20_000 {
        doc.extend_from_slice(format!("<item n='{i}'>text &e; <![CDATA[cd]]><!--c--></item>\n").as_bytes());
    }
    doc.extend_from_slice(b"</r>");
    // And the same in UTF-16, decoded as it comes.
    let doc16 = utf16(std::str::from_utf8(&doc).unwrap(), true);
    for d in [&doc, &doc16] {
        for chunk in [1, 100, 4096] {
            let mut c = || chunk;
            let (r, _, max) = pushed(d, &mut c);
            assert_eq!(r, R_OK);
            assert!(max < 200 + chunk, "chunks of {chunk}: a window of {max} bytes");
        }
    }
}

#[test]
fn conformance_suite() {
    let Some(root) = std::env::var_os("XMLCONF") else { return };
    let (mut n, mut ok) = (0, 0);
    let mut stack = vec![Path::new(&root).to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "xml") {
                let b = std::fs::read(&p).unwrap();
                if b.len() <= 1 << 16 {
                    ok += check(&p.display().to_string(), &b) as usize;
                    n += 1;
                }
            }
        }
    }
    assert!(n > 1000 && ok > 1000, "{n} files, {ok} read as they came");
    eprintln!("{n} files, {ok} read as they came and accepted");
}
