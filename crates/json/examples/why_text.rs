//! Prints how vjson reads each argument, as a complete text and as a
//! prefix: `cargo run --example why_text -- '01' '[1,]'`
fn main() {
    for t in std::env::args().skip(1) {
        let full = match verilith_json::parse(t.as_bytes()) {
            Ok(d) => format!("ok {:?}", d),
            Err(e) => e.to_string(),
        };
        let prefix = match verilith_json::parse_prefix(t.as_bytes()) {
            Ok((d, end)) => format!("ok {:?}, ends at {end}", d),
            Err(e) => e.to_string(),
        };
        println!("{t:?}\n  parse:        {full}\n  parse_prefix: {prefix}");
    }
}
