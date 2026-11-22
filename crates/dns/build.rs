// Links a c-ares static library for the differential test when
// CARES_LIB_DIR is set; otherwise that test is compiled out.
fn main() {
    println!("cargo::rustc-check-cfg=cfg(have_cares)");
    println!("cargo::rerun-if-env-changed=CARES_LIB_DIR");
    if let Ok(dir) = std::env::var("CARES_LIB_DIR") {
        println!("cargo::rustc-link-search=native={dir}");
        println!("cargo::rustc-cfg=have_cares");
    }
}
