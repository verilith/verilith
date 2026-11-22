// Compiles ada (single-header amalgamation from a clone at $EXT/ada,
// default ~/ext) and a shim that also drives libcurl's URL API.
fn main() {
    let ext = std::env::var("EXT").unwrap_or_else(|_| format!("{}/ext", std::env::var("HOME").unwrap()));
    let ada = format!("{ext}/ada/singleheader");
    let mut b = cc::Build::new();
    if std::env::var("NO_NATIVE").is_err() {
        b.flag(&std::env::var("MARCH").map(|m| format!("-march={m}")).unwrap_or("-march=x86-64-v3".into()));
    }
    println!("cargo:rerun-if-env-changed=NO_NATIVE");
    b.cpp(true)
        .std("c++20")
        .opt_level(3)
        .flag("-DNDEBUG")
        .include(&ada)
        .file(format!("{ada}/ada.cpp"))
        .file("shim.cpp")
        .compile("adashim");
    println!("cargo:rustc-link-arg=/usr/lib/x86_64-linux-gnu/libcurl.so.4");
    println!("cargo:rerun-if-changed=shim.cpp");
}
