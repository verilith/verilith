//! Random input: parsing never panics, and the trees it returns are
//! well-formed (positions in order and within the tokens).
use verilith_css::{ComponentValue, Declaration, Item, parse_block_contents_str, parse_component_values_str, parse_stylesheet_str};

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
    "a", "b", "--x", "-", ":", ";", "{", "}", "(", ")", "[", "]", "f(", "url(x)", "@m", "@import", " ", "\n", "!",
    "important", "IMPORTANT", "1px", "'s'", "\"", "\\", "/*c*/", "<!--", "-->", ",", "&", ".", "#h", "%",
];

/// Checks a component value covers `[from, to)` in order; returns its end.
fn check_cv(c: &ComponentValue, from: usize, n: usize) -> usize {
    match c {
        ComponentValue::Token(i) => {
            assert!(*i >= from && *i < n);
            i + 1
        }
        ComponentValue::Block { start, end, value } | ComponentValue::Function { start, end, value } => {
            assert!(*start >= from && start < end && *end <= n);
            let mut at = start + 1;
            for v in value {
                at = check_cv(v, at, n);
            }
            assert!(at <= *end);
            *end
        }
    }
}

fn check_decl(d: &Declaration, from: usize, n: usize) -> usize {
    assert!(d.start >= from && d.name == d.start && d.start < d.end && d.end <= n);
    assert!(d.start < d.value_start && d.value_start <= d.value_end && d.value_end <= d.end);
    let mut at = d.value_start;
    for v in &d.value {
        at = check_cv(v, at, n);
    }
    assert!(at <= d.value_end);
    d.end
}

fn check_items(items: &[Item], mut from: usize, n: usize) {
    for it in items {
        match it {
            Item::Declarations(ds) => {
                assert!(!ds.is_empty());
                for d in ds {
                    from = check_decl(d, from, n);
                }
            }
            Item::Rule { at, start, end, prelude, block, declarations, children } => {
                assert!(*start >= from && start < end && *end <= n);
                let mut k = if *at { start + 1 } else { *start };
                for v in prelude {
                    k = check_cv(v, k, n);
                }
                assert!(*block || (declarations.is_empty() && children.is_empty()));
                for d in declarations {
                    k = check_decl(d, k, n);
                }
                check_items(children, k, n);
                from = *end;
            }
        }
    }
}

#[test]
fn random_input_parses_to_well_formed_trees() {
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    for _ in 0..300_000 {
        let len = (rng.next() % 24) as usize;
        let css: String = (0..len).map(|_| PIECES[(rng.next() % PIECES.len() as u64) as usize]).collect();
        let p = parse_stylesheet_str(&css).unwrap();
        check_items(&p.tree, 0, p.tokens.tokens.len());
        let p = parse_block_contents_str(&css).unwrap();
        check_items(&p.tree, 0, p.tokens.tokens.len());
        let p = parse_component_values_str(&css).unwrap();
        let mut at = 0;
        for v in &p.tree {
            at = check_cv(v, at, p.tokens.tokens.len());
        }
    }
}
