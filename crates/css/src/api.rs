//! Plain Rust convenience over the verified tokenizer. Nothing here is
//! verified: it converts between `&str` and code points, and reads a
//! number token's text with Rust's own float parser.
use crate::lex::{Token, preprocess, tokenize};
use crate::spec::Kind;

/// A stylesheet's preprocessed code points and its tokens. Token positions
/// index `input`.
#[derive(Debug, Clone)]
pub struct Tokens {
    /// The preprocessed input (§3.3).
    pub input: Vec<u32>,
    /// The tokens, without the final `<EOF-token>`.
    pub tokens: Vec<Token>,
}

/// Preprocesses and tokenizes a stylesheet.
pub fn tokenize_str(css: &str) -> Tokens {
    let cps: Vec<u32> = css.chars().map(|c| c as u32).collect();
    let input = preprocess(&cps);
    let tokens = tokenize(&input);
    Tokens { input, tokens }
}

fn to_string(cps: &[u32]) -> String {
    // Preprocessing and escapes leave only Unicode scalar values when the
    // input was a `&str`; anything else would show as U+FFFD.
    cps.iter().map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}')).collect()
}

impl Tokens {
    /// The source text a token was consumed from.
    pub fn text(&self, t: &Token) -> String {
        to_string(&self.input[t.start..t.end])
    }

    /// The token's value as a string: the name of an ident, function,
    /// at-keyword or hash, the contents of a string or url, a dimension's
    /// unit. Empty for other kinds.
    pub fn value(&self, t: &Token) -> String {
        to_string(&t.value)
    }

    /// A number, percentage or dimension token's sign character: `'+'` or
    /// `'-'` if its text starts with one. `None` for other kinds and for
    /// unsigned numbers.
    pub fn sign(&self, t: &Token) -> Option<char> {
        match t.kind {
            Kind::Number { .. } | Kind::Percentage { .. } | Kind::Dimension { .. } => match self.input[t.start] {
                0x2B => Some('+'),
                0x2D => Some('-'),
                _ => None,
            },
            _ => None,
        }
    }

    /// A number, percentage or dimension token's numeric value. CSS Syntax
    /// §4.3.13 defines it as the exact decimal value; this is the nearest
    /// `f64` (Rust's correctly rounded parse of the number's text), and an
    /// out-of-range value is infinite. `None` for other kinds.
    pub fn number(&self, t: &Token) -> Option<f64> {
        match t.kind {
            Kind::Number { .. } | Kind::Percentage { .. } | Kind::Dimension { .. } => {
                to_string(&self.input[t.start..t.repr_end]).parse::<f64>().ok()
            }
            _ => None,
        }
    }
}
