// The mbedtls target links mbedTLS built with the vx509 patch: set
// MBEDTLS_LIB_DIR to its library/ directory (see the README; build it with
// -fsanitize=address so the C side is checked too).
fn main() {
    println!("cargo::rerun-if-env-changed=MBEDTLS_LIB_DIR");
    let Ok(dir) = std::env::var("MBEDTLS_LIB_DIR") else { return };
    println!("cargo::rustc-link-search=native={dir}");
    println!("cargo::rustc-link-lib=static=mbedx509");
    println!("cargo::rustc-link-lib=static=mbedcrypto");
}
