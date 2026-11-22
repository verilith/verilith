// The c-ares rows need a c-ares static library built with optimizations:
// set CARES_LIB_DIR to its lib directory (see the README).
fn main() {
    println!("cargo::rerun-if-env-changed=CARES_LIB_DIR");
    let dir = std::env::var("CARES_LIB_DIR").expect("set CARES_LIB_DIR to a c-ares Release build's lib directory");
    println!("cargo::rustc-link-search=native={dir}");
    println!("cargo::rustc-link-lib=static=cares");
}
