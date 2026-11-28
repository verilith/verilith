//! Plain Rust convenience over the verified tokenizer. Nothing here is
//! verified: it converts between `&str` and code points, and reads a
//! number token's text with Rust's own float parser.
use crate::lex::{Token, preprocess, tokenize};
use crate::parse::{ComponentValue, Declaration, Item, parse_block_contents, parse_component_values, parse_stylesheet};
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

/// A parse went deeper than `MAX_DEPTH` levels of nested blocks,
/// functions and rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TooDeep;

impl std::fmt::Display for TooDeep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CSS nested deeper than {} levels", crate::MAX_DEPTH)
    }
}

impl std::error::Error for TooDeep {}

/// Parsed CSS: its tokens and what was parsed from them. Indices in the
/// tree are positions in `tokens.tokens`.
#[derive(Debug, Clone)]
pub struct Parsed<T> {
    /// The tokens, and the preprocessed input their positions refer to.
    pub tokens: Tokens,
    /// The rules, declarations or component values.
    pub tree: T,
}

/// Parses a stylesheet (§5.4.4): its rules.
pub fn parse_stylesheet_str(css: &str) -> Result<Parsed<Vec<Item>>, TooDeep> {
    let tokens = tokenize_str(css);
    let tree = parse_stylesheet(&tokens.tokens).ok_or(TooDeep)?;
    Ok(Parsed { tokens, tree })
}

/// Parses a block's contents (§5.4.5), such as a `style` attribute: lists
/// of declarations, and any rules among them.
pub fn parse_block_contents_str(css: &str) -> Result<Parsed<Vec<Item>>, TooDeep> {
    let tokens = tokenize_str(css);
    let tree = parse_block_contents(&tokens.tokens).ok_or(TooDeep)?;
    Ok(Parsed { tokens, tree })
}

/// Parses a list of component values (§5.4.9).
pub fn parse_component_values_str(css: &str) -> Result<Parsed<Vec<ComponentValue>>, TooDeep> {
    let tokens = tokenize_str(css);
    let tree = parse_component_values(&tokens.tokens).ok_or(TooDeep)?;
    Ok(Parsed { tokens, tree })
}

impl Tokens {
    /// The name of a declaration.
    pub fn name(&self, d: &Declaration) -> String {
        self.value(&self.tokens[d.name])
    }

    /// The name of an at-rule (the at-keyword without `@`), or `None` for
    /// a qualified rule or a list of declarations.
    pub fn at_rule_name(&self, item: &Item) -> Option<String> {
        match item {
            Item::Rule { at: true, start, .. } => Some(self.value(&self.tokens[*start])),
            _ => None,
        }
    }

    /// The source text of the tokens `start..end`, comments between them
    /// included. For a declaration, `value_start..value_end` gives its value
    /// as written (the "original text" of a custom property).
    pub fn source(&self, start: usize, end: usize) -> String {
        if start >= end || end > self.tokens.len() {
            return String::new();
        }
        to_string(&self.input[self.tokens[start].start..self.tokens[end - 1].end])
    }
}
