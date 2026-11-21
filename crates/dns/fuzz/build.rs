// The ares_dns_parse target needs c-ares (its records are built with
// c-ares's setters): set CARES_LIB_DIR to a directory with libcares.a.
fn main() {
    println!("cargo::rerun-if-env-changed=CARES_LIB_DIR");
    let dir = std::env::var("CARES_LIB_DIR").expect("set CARES_LIB_DIR to a c-ares build's lib directory");
    println!("cargo::rustc-link-search=native={dir}");
    println!("cargo::rustc-link-lib=static=cares");
}
