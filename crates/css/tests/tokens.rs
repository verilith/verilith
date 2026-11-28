//! Tokens of small inputs, worked out by hand from CSS Syntax Level 3 §4.
use verilith_css::{Kind, tokenize_str};

/// The tokens of `css` as (kind, value, text).
fn toks(css: &str) -> Vec<(Kind, String, String)> {
    let t = tokenize_str(css);
    t.tokens.iter().map(|k| (k.kind, t.value(k), t.text(k))).collect()
}

fn kinds(css: &str) -> Vec<Kind> {
    toks(css).into_iter().map(|t| t.0).collect()
}

#[test]
fn a_rule() {
    use Kind::*;
    assert_eq!(
        kinds("a { color: red; }"),
        vec![Ident, Whitespace, LeftBrace, Whitespace, Ident, Colon, Whitespace, Ident, Semicolon, Whitespace, RightBrace]
    );
}

#[test]
fn comments_are_not_tokens_and_split_whitespace() {
    use Kind::*;
    assert_eq!(kinds("a/**/b"), vec![Ident, Ident]);
    assert_eq!(kinds("a /* x */ b"), vec![Ident, Whitespace, Whitespace, Ident]);
    assert_eq!(kinds("/* unterminated"), vec![]);
    assert_eq!(kinds("/"), vec![Delim('/' as u32)]);
}

#[test]
fn numbers() {
    let t = tokenize_str("12 +1.5 -.5e2 1e 3% 4px 5--x");
    let got: Vec<_> = t
        .tokens
        .iter()
        .filter(|k| k.kind != Kind::Whitespace)
        .map(|k| (k.kind, t.number(k), t.sign(k), t.value(k)))
        .collect();
    assert_eq!(
        got,
        vec![
            (Kind::Number { integer: true }, Some(12.0), None, "".into()),
            (Kind::Number { integer: false }, Some(1.5), Some('+'), "".into()),
            (Kind::Number { integer: false }, Some(-50.0), Some('-'), "".into()),
            // "1e" is the number 1 and the unit "e".
            (Kind::Dimension { integer: true }, Some(1.0), None, "e".into()),
            (Kind::Percentage { integer: true }, Some(3.0), None, "".into()),
            (Kind::Dimension { integer: true }, Some(4.0), None, "px".into()),
            (Kind::Dimension { integer: true }, Some(5.0), None, "--x".into()),
        ]
    );
}

#[test]
fn hashes_and_at_keywords() {
    assert_eq!(toks("#id")[0].0, Kind::Hash { id: true });
    // Starts with a digit: a hash, but not an id.
    assert_eq!(toks("#123")[0].0, Kind::Hash { id: false });
    assert_eq!(toks("#")[0].0, Kind::Delim('#' as u32));
    assert_eq!(toks("@media")[0], (Kind::AtKeyword, "media".into(), "@media".into()));
    assert_eq!(toks("@1")[0].0, Kind::Delim('@' as u32));
}

#[test]
fn escapes() {
    // Hex escapes take up to six digits and one whitespace after them.
    assert_eq!(toks("\\41 B")[0], (Kind::Ident, "AB".into(), "\\41 B".into()));
    assert_eq!(toks("\\0000414")[0].1, "A4");
    // Zero, surrogates and values past U+10FFFF become U+FFFD.
    assert_eq!(toks("\\0")[0].1, "\u{FFFD}");
    assert_eq!(toks("\\D800")[0].1, "\u{FFFD}");
    assert_eq!(toks("\\110000")[0].1, "\u{FFFD}");
    // A backslash before a newline is not an escape.
    assert_eq!(toks("\\\n")[0].0, Kind::Delim('\\' as u32));
    // A backslash at the end of the input escapes to U+FFFD.
    assert_eq!(toks("a\\")[0].1, "a\u{FFFD}");
}

#[test]
fn strings() {
    assert_eq!(toks("\"a\\\"b\"")[0], (Kind::String, "a\"b".into(), "\"a\\\"b\"".into()));
    // An escaped newline continues the string and adds nothing.
    assert_eq!(toks("'a\\\nb'")[0].1, "ab");
    // A raw newline makes a bad string; the newline is the next token.
    assert_eq!(kinds("'a\nb'")[..2], [Kind::BadString, Kind::Whitespace]);
    // End of input closes a string.
    assert_eq!(toks("'abc")[0], (Kind::String, "abc".into(), "'abc".into()));
}

#[test]
fn urls() {
    assert_eq!(toks("url(  a.png  )")[0], (Kind::Url, "a.png".into(), "url(  a.png  )".into()));
    assert_eq!(toks("URL(x)")[0].0, Kind::Url);
    // "url" written with an escape is still url.
    assert_eq!(toks("u\\72l(x)")[0].0, Kind::Url);
    // Quoted: a function, then a string.
    assert_eq!(kinds("url( \"x\")"), vec![Kind::Function, Kind::Whitespace, Kind::String, Kind::RightParen]);
    assert_eq!(toks("url(a b)")[0].0, Kind::BadUrl);
    assert_eq!(toks("url(a\"b)")[0].0, Kind::BadUrl);
    // An escaped parenthesis does not end the remnants of a bad url.
    assert_eq!(kinds("url(a b\\)c)d"), vec![Kind::BadUrl, Kind::Ident]);
    assert_eq!(toks("url(a\\)b)")[0].1, "a)b");
}

#[test]
fn cdo_cdc_and_hyphens() {
    use Kind::*;
    assert_eq!(kinds("<!-- -->"), vec![Cdo, Whitespace, Cdc]);
    assert_eq!(kinds("--x"), vec![Ident]);
    assert_eq!(kinds("-x"), vec![Ident]);
    assert_eq!(kinds("-1"), vec![Number { integer: true }]);
    assert_eq!(kinds("- "), vec![Delim('-' as u32), Whitespace]);
    // `-\` then a newline: not an ident (the escape is not valid).
    assert_eq!(kinds("-\\\n")[..2], [Delim('-' as u32), Delim('\\' as u32)]);
}

#[test]
fn preprocessing() {
    use Kind::*;
    // CR LF is one newline: one whitespace token, and positions count it once.
    let t = tokenize_str("a\r\nb");
    assert_eq!(t.input, vec!['a' as u32, 0x0A, 'b' as u32]);
    assert_eq!(t.tokens.iter().map(|k| k.kind).collect::<Vec<_>>(), vec![Ident, Whitespace, Ident]);
    assert_eq!(toks("a\u{0}b")[0].1, "a\u{FFFD}b");
    assert_eq!(kinds("'a\u{c}"), vec![BadString, Whitespace]);
}

#[test]
fn non_ascii_idents() {
    assert_eq!(toks("é日本😀")[0], (Kind::Ident, "é日本😀".into(), "é日本😀".into()));
    assert_eq!(toks("\u{80}")[0].0, Kind::Ident);
}

#[test]
fn positions_cover_the_input() {
    // Without comments, tokens tile the input exactly.
    let css = "a{b:url(x) 1.5em 'q' #h @k -->}";
    let t = tokenize_str(css);
    let mut at = 0;
    for k in &t.tokens {
        assert_eq!(k.start, at);
        assert!(k.end > k.start);
        at = k.end;
    }
    assert_eq!(at, t.input.len());
}
