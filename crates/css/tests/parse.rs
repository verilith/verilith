//! Parses of small inputs, worked out by hand from CSS Syntax Level 3 §5.
//!
//! Trees are shown compactly: a qualified rule as `Q(prelude){...}`, an
//! at-rule as `@name(prelude){...}` or `@name(prelude);` without a block,
//! a list of declarations as `D[...]`, a declaration as `name:value`
//! (`!` after it when important), and component values as their tokens'
//! text, blocks and functions with their brackets.
use verilith_css::{
    ComponentValue, Declaration, Item, Kind, MAX_DEPTH, TooDeep, Tokens, parse_block_contents_str,
    parse_component_values_str, parse_stylesheet_str,
};

fn cv(t: &Tokens, c: &ComponentValue) -> String {
    match c {
        ComponentValue::Token(i) => t.text(&t.tokens[*i]),
        ComponentValue::Block { start, value, .. } => {
            let (o, e) = match t.tokens[*start].kind {
                Kind::LeftBrace => ("{", "}"),
                Kind::LeftBracket => ("[", "]"),
                _ => ("(", ")"),
            };
            format!("{o}{}{e}", cvs(t, value))
        }
        ComponentValue::Function { start, value, .. } => format!("{}({})", t.value(&t.tokens[*start]), cvs(t, value)),
    }
}

fn cvs(t: &Tokens, v: &[ComponentValue]) -> String {
    v.iter().map(|c| cv(t, c)).collect()
}

fn decl(t: &Tokens, d: &Declaration) -> String {
    format!("{}:{}{}", t.name(d), cvs(t, &d.value), if d.important { "!" } else { "" })
}

fn decls(t: &Tokens, v: &[Declaration]) -> String {
    v.iter().map(|d| decl(t, d)).collect::<Vec<_>>().join(";")
}

fn item(t: &Tokens, it: &Item) -> String {
    match it {
        Item::Declarations(v) => format!("D[{}]", decls(t, v)),
        Item::Rule { at, prelude, block, declarations, children, .. } => {
            let head = if *at {
                format!("@{}({})", t.at_rule_name(it).unwrap(), cvs(t, prelude))
            } else {
                format!("Q({})", cvs(t, prelude))
            };
            if !block {
                return format!("{head};");
            }
            let mut body: Vec<String> = Vec::new();
            if !declarations.is_empty() {
                body.push(decls(t, declarations));
            }
            body.extend(children.iter().map(|c| item(t, c)));
            format!("{head}{{{}}}", body.join(" "))
        }
    }
}

fn sheet(css: &str) -> String {
    let p = parse_stylesheet_str(css).unwrap();
    p.tree.iter().map(|i| item(&p.tokens, i)).collect::<Vec<_>>().join(" ")
}

fn block(css: &str) -> String {
    let p = parse_block_contents_str(css).unwrap();
    p.tree.iter().map(|i| item(&p.tokens, i)).collect::<Vec<_>>().join(" ")
}

const CASES: &[(&str, &str)] = &[
    ("a{color:red}", "Q(a){color:red}"),
    ("a { color: red; }", "Q(a ){color:red}"),
    ("a{color:red !important}", "Q(a){color:red!}"),
    ("a{color: red ! IMPORTANT ;}", "Q(a){color:red!}"),
    ("a{x:!important}", "Q(a){x:!}"),
    ("a{x: a !important b}", "Q(a){x:a !important b}"),
    ("a{;color:red;;}", "Q(a){color:red}"),
    ("a{color:red", "Q(a){color:red}"),
    ("a{b: f(1, [2]) (3)}", "Q(a){b:f(1, [2]) (3)}"),
    ("a{--x: { a b } ; y: 1}", "Q(a){--x:{ a b };y:1}"),
    ("a{--x:}", "Q(a){--x:}"),
    // Not a declaration (a {} block among other values): reparsed as a
    // nested rule, and " b" is a rule with no block, which is dropped.
    ("a{width: {a} b}", "Q(a){Q(width: ){}}"),
    ("a{width:{a}}", "Q(a){width:{a}}"),
    ("a{color red; margin:0}", "Q(a){margin:0}"),
    ("a{color:red; &:hover{color:blue} margin:0}", "Q(a){color:red Q(&:hover){color:blue} D[margin:0]}"),
    ("a{b{c{d:e}}}", "Q(a){Q(b){Q(c){d:e}}}"),
    ("@media screen{a{color:red}}", "@media( screen){Q(a){color:red}}"),
    ("@import url(x.css);", "@import( url(x.css));"),
    ("@import \"x.css\"", "@import( \"x.css\");"),
    ("a{@x y}", "Q(a){@x( y);}"),
    ("@page{margin:1in; @top-left{content:'x'}}", "@page(){D[margin:1in] @top-left(){D[content:'x']}}"),
    ("<!-- a{} -->", "Q(a){}"),
    ("} a{}", "Q(} a){}"),
    ("--x:{a} b{}", "Q(b){}"),
    ("a{--x:{a} b{}}", "Q(a){--x:{a} b{}}"),
    ("a", ""),
    ("a{} ;", "Q(a){}"),
];

#[test]
fn stylesheets() {
    let bad: Vec<String> = CASES
        .iter()
        .filter(|(css, want)| sheet(css) != *want)
        .map(|(css, want)| format!("{css:?}: got {:?}, want {want:?}", sheet(css)))
        .collect();
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn block_contents() {
    // A style attribute.
    assert_eq!(block("color: red; background: blue"), "D[color:red;background:blue]");
    // A `}` ends a block's contents.
    assert_eq!(block("a:b} c:d"), "D[a:b]");
    assert_eq!(block("x; y:1 !important; @m{}"), "D[y:1!] @m(){}");
    assert_eq!(block(""), "");
}

#[test]
fn component_values() {
    let p = parse_component_values_str("a (b [c) d").unwrap();
    // `)` does not close `[`; the end of the input closes both.
    assert_eq!(cvs(&p.tokens, &p.tree), "a (b [c) d])");
    assert_eq!(p.tree.len(), 3);
    let p = parse_component_values_str("} ) ]").unwrap();
    assert_eq!(p.tree.len(), 5);
}

#[test]
fn positions() {
    let p = parse_stylesheet_str("a { --x : /* c */ 1px  2px ; b: c !important }").unwrap();
    let Item::Rule { declarations, start, end, .. } = &p.tree[0] else { panic!() };
    assert_eq!((*start, *end), (0, p.tokens.tokens.len()));
    // The custom property's original text: its value as written.
    let d = &declarations[0];
    assert_eq!(p.tokens.source(d.value_start, d.value_end), "1px  2px");
    assert_eq!(p.tokens.name(&declarations[1]), "b");
    assert_eq!(p.tokens.source(declarations[1].value_start, declarations[1].value_end), "c");
}

#[test]
fn too_deep_is_an_error() {
    assert_eq!(parse_stylesheet_str(&"(".repeat(MAX_DEPTH + 1)).unwrap_err(), TooDeep);
}
