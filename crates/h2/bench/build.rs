// Compiles nghttp2's lib/ (NGHTTP2_LIB, the directory) with ngwrap.c.
fn main() {
    let lib = std::env::var("NGHTTP2_LIB").expect("set NGHTTP2_LIB to nghttp2's lib/ directory");
    println!("cargo:rerun-if-changed=ngwrap.c");
    println!("cargo:rerun-if-env-changed=NGHTTP2_LIB");
    let mut b = cc::Build::new();
    b.opt_level(2)
        .define("NDEBUG", None)
        .define("NGHTTP2_STATICLIB", None)
        .define("HAVE_ARPA_INET_H", None)
        .define("HAVE_NETINET_IN_H", None)
        .include(format!("{lib}/includes"))
        .include(&lib)
        .warnings(false)
        .file("ngwrap.c");
    for e in std::fs::read_dir(&lib).unwrap() {
        let p = e.unwrap().path();
        if p.extension().is_some_and(|x| x == "c") {
            b.file(p);
        }
    }
    b.compile("ngwrap");
}
