// Links the system zlib and libdeflate (Debian/Ubuntu: zlib1g-dev,
// libdeflate-dev or libdeflate0). zlib-ng is built by libz-ng-sys.
fn main() {
    println!("cargo::rustc-link-lib=z");
    match std::env::var("LIBDEFLATE") {
        Ok(p) => println!("cargo::rustc-link-arg={p}"),
        Err(_) => println!("cargo::rustc-link-lib=deflate"),
    }
}
