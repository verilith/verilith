fn main() {
    let data = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    for _ in 0..3 {
        assert!(verilith_json::parser::parse_document(std::hint::black_box(&data), true).is_ok());
    }
}
