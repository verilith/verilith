//! Runs the signed test hierarchy (tests/sec) on 127.0.1.2-11, for the
//! DNSSEC benchmark, with 10000 more names in example.com:
//!   cargo run --release --example signed_hierarchy -- [PORT]
//! Prints the root's trust anchor: key tag, algorithm, digest type, digest.
#[path = "../tests/sec/mod.rs"]
mod sec;

fn main() {
    let port = std::env::args().nth(1).map(|p| p.parse().expect("PORT")).unwrap_or(53);
    let ds = sec::start_with(port, 10000);
    let hex: String = ds[4..].iter().map(|b| format!("{b:02X}")).collect();
    println!("{} {} {} {hex}", u16::from_be_bytes([ds[0], ds[1]]), ds[2], ds[3]);
    eprintln!("signed hierarchy: root at 127.0.1.2:{port}");
    loop {
        std::thread::park();
    }
}
