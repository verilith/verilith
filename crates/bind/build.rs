// With the `http` feature, compiles llhttp's api.c and http.c (vhttp keeps
// copies in compat/llhttp) into the library, so that it holds the whole of
// llhttp's ABI: those two files are llhttp's public functions and callback
// plumbing, and vhttp supplies the parser they call.
fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    if std::env::var_os("CARGO_FEATURE_HTTP").is_some() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../http/compat/llhttp");
        for f in ["src/api.c", "src/http.c", "include/llhttp.h"] {
            println!("cargo::rerun-if-changed={}", dir.join(f).display());
        }
        cc::Build::new()
            .file(dir.join("src/api.c"))
            .file(dir.join("src/http.c"))
            .include(dir.join("include"))
            .opt_level(2)
            .compile("vbind_llhttp");
    }
}
