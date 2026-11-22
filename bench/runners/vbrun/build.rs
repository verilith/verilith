// The timer and counters are the C code every C runner uses too.
fn main() {
    let h = concat!(env!("CARGO_MANIFEST_DIR"), "/../../harness");
    cc::Build::new().file(format!("{h}/counters.c")).include(h).opt_level(2).compile("vbcounters");
    println!("cargo::rerun-if-changed={h}/counters.c");
    println!("cargo::rerun-if-changed={h}/counters.h");
}
