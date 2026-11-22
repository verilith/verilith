//! Prints `accept` or `reject` for each file: `cargo run --example accepts FILE...`
fn main() {
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        let one = verilith_json::parser::parse_document(&data, true).is_ok();
        let two = verilith_json::parse(&data).is_ok();
        assert_eq!(one, two, "{path}");
        println!("{} {path}", if one { "accept" } else { "reject" });
    }
}
