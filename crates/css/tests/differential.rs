//! Compares the tokens with Servo's cssparser (the tokenizer Firefox
//! uses), on hand-picked stylesheets and on random input.
//!
//! cssparser does not hand out a flat token stream: it nests blocks and
//! swallows the token that closes one, and it still has CSS 2.1's combined
//! match tokens (`~=`, `|=`, `^=`, `$=`, `*=`, `||`), which CSS Syntax
//! Level 3 tokenizes as two delims. Both sides are normalized to the same
//! form below before comparing: blocks are flattened, closing tokens that
//! close a block are dropped, and the match tokens are split.
use cssparser::{Parser, ParserInput, Token as CTok};
use verilith_css::{Kind, Tokens, tokenize_str};

#[derive(Debug, Clone, PartialEq)]
struct N {
    what: String,
    num: Option<f64>,
}

fn n(what: String) -> N {
    N { what, num: None }
}

fn close_of(k: &str) -> Option<&'static str> {
    match k {
        "(" => Some(")"),
        "[" => Some("]"),
        "{" => Some("}"),
        _ => None,
    }
}

/// Ours: flat tokens, with block-closing tokens dropped as cssparser does.
fn ours(css: &str) -> Vec<N> {
    let t: Tokens = tokenize_str(css);
    let mut out = Vec::new();
    let mut stack: Vec<&'static str> = Vec::new();
    for tok in &t.tokens {
        let v = t.value(tok);
        let num = t.number(tok);
        let sg = t.sign(tok).is_some();
        let item = match tok.kind {
            Kind::Ident => n(format!("ident:{v}")),
            Kind::Function => {
                stack.push(")");
                n(format!("function:{v}"))
            }
            Kind::AtKeyword => n(format!("at:{v}")),
            Kind::Hash { id } => n(format!("hash:{id}:{v}")),
            Kind::String => n(format!("string:{v}")),
            Kind::BadString => n("bad-string".into()),
            Kind::Url => n(format!("url:{v}")),
            Kind::BadUrl => n("bad-url".into()),
            Kind::Delim(c) => n(format!("delim:{}", char::from_u32(c).unwrap())),
            Kind::Number { integer } => N { what: format!("number:{integer}:{sg}"), num },
            Kind::Percentage { integer } => N { what: format!("percentage:{integer}:{sg}"), num },
            Kind::Dimension { integer } => N { what: format!("dimension:{integer}:{sg}:{v}"), num },
            Kind::Whitespace => n("ws".into()),
            Kind::Cdo => n("cdo".into()),
            Kind::Cdc => n("cdc".into()),
            Kind::Colon => n(":".into()),
            Kind::Semicolon => n(";".into()),
            Kind::Comma => n(",".into()),
            Kind::LeftBracket | Kind::LeftParen | Kind::LeftBrace => {
                let o = match tok.kind {
                    Kind::LeftBracket => "[",
                    Kind::LeftParen => "(",
                    _ => "{",
                };
                stack.push(close_of(o).unwrap());
                n(o.into())
            }
            Kind::RightBracket | Kind::RightParen | Kind::RightBrace => {
                let c = match tok.kind {
                    Kind::RightBracket => "]",
                    Kind::RightParen => ")",
                    _ => "}",
                };
                if stack.last() == Some(&c) {
                    stack.pop();
                    continue;
                }
                n(c.into())
            }
        };
        out.push(item);
    }
    out
}

fn theirs_into(p: &mut Parser, out: &mut Vec<N>) {
    loop {
        let tok = match p.next_including_whitespace_and_comments() {
            Ok(t) => t.clone(),
            Err(_) => return,
        };
        let nested = matches!(
            tok,
            CTok::Function(_) | CTok::ParenthesisBlock | CTok::SquareBracketBlock | CTok::CurlyBracketBlock
        );
        let two = |a: &str, b: &str| vec![n(format!("delim:{a}")), n(format!("delim:{b}"))];
        let items: Vec<N> = match &tok {
            CTok::Ident(v) => vec![n(format!("ident:{v}"))],
            CTok::Function(v) => vec![n(format!("function:{v}"))],
            CTok::AtKeyword(v) => vec![n(format!("at:{v}"))],
            CTok::Hash(v) => vec![n(format!("hash:false:{v}"))],
            CTok::IDHash(v) => vec![n(format!("hash:true:{v}"))],
            CTok::QuotedString(v) => vec![n(format!("string:{v}"))],
            CTok::BadString(_) => vec![n("bad-string".into())],
            CTok::UnquotedUrl(v) => vec![n(format!("url:{v}"))],
            CTok::BadUrl(_) => vec![n("bad-url".into())],
            CTok::Delim(c) => vec![n(format!("delim:{c}"))],
            CTok::Number { value, int_value, has_sign } => {
                vec![N { what: format!("number:{}:{has_sign}", int_value.is_some()), num: Some(*value as f64) }]
            }
            CTok::Percentage { unit_value, int_value, has_sign } => vec![N {
                what: format!("percentage:{}:{has_sign}", int_value.is_some()),
                num: Some(*unit_value as f64 * 100.0),
            }],
            CTok::Dimension { value, int_value, unit, has_sign } => vec![N {
                what: format!("dimension:{}:{has_sign}:{unit}", int_value.is_some()),
                num: Some(*value as f64),
            }],
            CTok::WhiteSpace(_) => vec![n("ws".into())],
            CTok::Comment(_) => vec![],
            CTok::CDO => vec![n("cdo".into())],
            CTok::CDC => vec![n("cdc".into())],
            CTok::Colon => vec![n(":".into())],
            CTok::Semicolon => vec![n(";".into())],
            CTok::Comma => vec![n(",".into())],
            CTok::IncludeMatch => two("~", "="),
            CTok::DashMatch => two("|", "="),
            CTok::PrefixMatch => two("^", "="),
            CTok::SuffixMatch => two("$", "="),
            CTok::SubstringMatch => two("*", "="),
            CTok::ParenthesisBlock => vec![n("(".into())],
            CTok::SquareBracketBlock => vec![n("[".into())],
            CTok::CurlyBracketBlock => vec![n("{".into())],
            CTok::CloseParenthesis => vec![n(")".into())],
            CTok::CloseSquareBracket => vec![n("]".into())],
            CTok::CloseCurlyBracket => vec![n("}".into())],
        };
        out.extend(items);
        if nested {
            let _ = p.parse_nested_block(|p| -> Result<(), cssparser::ParseError<'_, ()>> {
                theirs_into(p, out);
                Ok(())
            });
        }
    }
}

fn theirs(css: &str) -> Vec<N> {
    let mut input = ParserInput::new(css);
    let mut p = Parser::new(&mut input);
    let mut out = Vec::new();
    theirs_into(&mut p, &mut out);
    out
}

/// cssparser keeps numbers as f32; ours are f64. They agree to f32
/// precision, and both are infinite (or huge) together.
fn same_num(a: Option<f64>, b: Option<f64>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => {
            let (x, y) = (x as f32 as f64, y as f32 as f64);
            if !x.is_finite() || !y.is_finite() || x.abs() > 1e30 || y.abs() > 1e30 {
                return x.signum() == y.signum();
            }
            x == y || (x - y).abs() <= 1e-6 * x.abs().max(y.abs()) || (x - y).abs() < 1e-30
        }
        _ => false,
    }
}

/// Where cssparser departs from CSS Syntax Level 3, so the comparison
/// skips the input:
///
/// - `-` then `\` then a newline: §4.3.9 says this does not start an ident
///   sequence (the backslash and newline are not a valid escape), so `-` is
///   a delim; cssparser looks for the newline one place too early and
///   returns an ident `-`.
/// - An unquoted url with whitespace followed by `\`: after the
///   whitespace, §4.3.6 only looks at the next code point before consuming
///   the remnants of a bad url (§4.3.15), where `\)` is an escape that
///   does not end the bad url. cssparser consumes that code point first, so
///   for `url(a \)b` it ends the bad url at the `)`.
fn known_difference(css: &str) -> bool {
    ["-\\\n", "-\\\r", "-\\\u{c}"].iter().any(|p| css.contains(p))
        || (css.to_ascii_lowercase().contains("url(")
            && [" \\", "\n\\", "\t\\", "\r\\", "\u{c}\\"].iter().any(|p| css.contains(p)))
}

fn check(css: &str) -> Result<(), String> {
    if known_difference(css) {
        return Ok(());
    }
    let a = ours(css);
    let b = theirs(css);
    let ok = a.len() == b.len() && a.iter().zip(&b).all(|(x, y)| x.what == y.what && same_num(x.num, y.num));
    if ok {
        Ok(())
    } else {
        let i = a.iter().zip(&b).position(|(x, y)| x.what != y.what || !same_num(x.num, y.num)).unwrap_or(a.len().min(b.len()));
        Err(format!(
            "input {css:?}\n first difference at token {i}\n ours:   {:?}\n theirs: {:?}",
            a.get(i.saturating_sub(1)..(i + 2).min(a.len())),
            b.get(i.saturating_sub(1)..(i + 2).min(b.len()))
        ))
    }
}

const CORPUS: &[&str] = &[
    "",
    "a{color:red}",
    "body { margin: 0 auto; padding: 1.5em 2px; }",
    "@media (max-width: 600px) { .x > p:first-child::before { content: \"\\201C\" } }",
    "a[href^='http'], a[href$=\".pdf\"] { background: url(  img/i.png  ) no-repeat }",
    "div { width: calc(100% - 2*var(--gap, 10px)); }",
    "@import url(\"foo.css\") screen;",
    "#id.cls #123 #-x #\\31 23 #- #\\",
    "<!-- a --> -->",
    "url(a b) url(a\"b) url(a\\)b) url( \"x\" ) URL(x) u\\72l(x) url(",
    "\"abc\ndef\" 'x\\\ny' 'unterminated",
    "/* c */ a /* b */ /* unterminated",
    "1 +1 -1 .5 +.5 -.5 1e3 1E+3 1e-3 1.5e 1.e3 1e 12px 1.5% -2.5em 3--x 4\\70x",
    "-- --x -\\41 -> -1 - -.",
    "\\0 \\D800 \\110000 \\41 B \\00004142 \\\n",
    "@-- @-x @1 @\\40 @",
    "U+26 u+0-7F U+?? u+1???",
    "a\u{0}b \r\n \u{c} \r",
    "é ñ 日本 \u{80} \u{2028} 😀px",
    "~= |= ^= $= *= || | ~",
    "( [ { ) ] } ( ] ) [ ) ] { ( }",
    "f(a,b) g( ) h(\"x\")",
];

#[test]
fn corpus_agrees_with_cssparser() {
    let mut failures = Vec::new();
    for css in CORPUS {
        if let Err(e) = check(css) {
            failures.push(e);
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// A small deterministic generator (xorshift), so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

const PIECES: &[&str] = &[
    "\\", "/", "*", "/*", "*/", "(", ")", "[", "]", "{", "}", "\"", "'", "#", "@", "-", "--", "+", ".", "e", "E",
    "%", "url(", "URL(", "u", "r", "l", "0", "1", "9", "a", "f", "F", "z", "_", " ", "  ", "\n", "\t", "\r", "\r\n",
    "\u{c}", "!", "<", ">", "<!--", "-->", ",", ";", ":", "=", "~", "|", "^", "$", "\u{0}", "é", "\u{80}", "\u{ffff}",
    "😀", "\u{7f}", "\u{1}", "\u{b}", "\\0", "\\41", "\\D800", "\\110000", "\\\n", "px", "em", "1e3", ".5", "+.",
];

#[test]
fn random_input_agrees_with_cssparser() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut failures = Vec::new();
    let (mut compared, mut skipped) = (0u32, 0u32);
    for _ in 0..2_000_000 {
        let len = (rng.next() % 12) as usize;
        let mut css = String::new();
        for _ in 0..len {
            css.push_str(PIECES[(rng.next() % PIECES.len() as u64) as usize]);
        }
        if known_difference(&css) {
            skipped += 1;
            continue;
        }
        compared += 1;
        if let Err(e) = check(&css) {
            failures.push(e);
            if failures.len() >= 10 {
                break;
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    // The known differences must not hide much of the comparison.
    assert!(skipped * 50 < compared, "{skipped} skipped, {compared} compared");
    eprintln!("{compared} random inputs compared, {skipped} skipped as known differences");
}
