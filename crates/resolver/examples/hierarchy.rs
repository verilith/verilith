//! Runs the test hierarchy (tests/hier) on 127.0.0.2-9, for benchmarks:
//!   cargo run --release --example hierarchy -- [PORT]
#[path = "../tests/hier/mod.rs"]
mod hier;

fn main() {
    let port = std::env::args().nth(1).map(|p| p.parse().expect("PORT")).unwrap_or(53);
    hier::start(port);
    eprintln!("hierarchy: root at 127.0.0.2:{port}");
    loop {
        std::thread::park();
    }
}
