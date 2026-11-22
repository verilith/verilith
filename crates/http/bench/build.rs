// Builds picohttpparser and llhttp from clones at $EXT (default ./ext, as
// fetched by run.sh),
// with -O3 -march=native so each gets its best SIMD path.
fn main() {
    let ext = std::env::var("EXT").unwrap_or_else(|_| format!("{}/ext", std::env::var("CARGO_MANIFEST_DIR").unwrap()));
    cc::Build::new()
        .file(format!("{ext}/picohttpparser/picohttpparser.c"))
        .opt_level(3)
        .flag("-march=native")
        .compile("pico");
    cc::Build::new()
        .files(["api.c", "http.c", "llhttp.c"].map(|f| format!("{ext}/llhttp/src/{f}")))
        .file("llwrap.c")
        .include(format!("{ext}/llhttp/include"))
        .opt_level(3)
        .flag("-march=native")
        .compile("llhttp");
    println!("cargo::rerun-if-env-changed=EXT");
}
