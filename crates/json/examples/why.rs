//! Prints why each file fails to parse: `cargo run --example why FILE...`
fn main() {
    for path in std::env::args().skip(1) {
        let data = std::fs::read(&path).unwrap();
        match verilith_json::parse(&data) {
            Ok(_) => println!("{path}: ok"),
            Err(e) => println!("{path}: {e}"),
        }
    }
}
