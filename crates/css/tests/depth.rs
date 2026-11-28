//! The nesting limit, and the stack a parse at the limit needs.
use verilith_css::{MAX_DEPTH, TooDeep, parse_block_contents_str, parse_component_values_str, parse_stylesheet_str};

#[test]
fn limit_is_exact() {
    for (open, close) in [("(", ")"), ("[", "]"), ("{", "}"), ("f(", ")")] {
        let ok = open.repeat(MAX_DEPTH) + &close.repeat(MAX_DEPTH);
        let deep = open.repeat(MAX_DEPTH + 1) + &close.repeat(MAX_DEPTH + 1);
        assert!(parse_component_values_str(&ok).is_ok(), "{open}");
        assert_eq!(parse_component_values_str(&deep).unwrap_err(), TooDeep, "{open}");
    }
    // Nested rules: each rule's block is a level.
    assert!(parse_stylesheet_str(&"a{".repeat(MAX_DEPTH)).is_ok());
    assert_eq!(parse_stylesheet_str(&"a{".repeat(MAX_DEPTH + 1)).unwrap_err(), TooDeep);
    assert!(parse_block_contents_str(&"a{".repeat(MAX_DEPTH)).is_ok());
    // Blocks inside a declaration's value count too.
    assert!(parse_stylesheet_str(&format!("a{{b:{}}}", "(".repeat(MAX_DEPTH - 1))).is_ok());
    assert_eq!(parse_stylesheet_str(&format!("a{{b:{}}}", "(".repeat(MAX_DEPTH))).unwrap_err(), TooDeep);
}

/// Parses the deepest inputs on a thread with a small stack.
fn on_small_stack(kib: usize) {
    std::thread::Builder::new()
        .stack_size(kib * 1024)
        .spawn(|| {
            let mixed: String = (0..MAX_DEPTH).map(|k| ["a{", "(", "[", "f(", "{"][k % 5]).collect();
            assert!(parse_stylesheet_str(&"a{".repeat(MAX_DEPTH)).is_ok());
            assert!(parse_stylesheet_str(&mixed).is_ok());
            assert!(parse_component_values_str(&"f(".repeat(MAX_DEPTH)).is_ok());
            assert!(parse_block_contents_str(&"a{".repeat(MAX_DEPTH)).is_ok());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn fits_in_a_small_stack() {
    // Optimized builds need far less; debug builds keep every local.
    on_small_stack(if cfg!(debug_assertions) { 1024 } else { 256 });
}
