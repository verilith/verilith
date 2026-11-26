// Builds nghttp2's lib/ (the release at $EXT/nghttp2, as fetched by run.sh)
// with -O3 -march=native, for its HPACK deflater.
fn main() {
    let ext = std::env::var("EXT").unwrap_or_else(|_| format!("{}/ext", std::env::var("CARGO_MANIFEST_DIR").unwrap()));
    let lib = format!("{ext}/nghttp2/lib");
    let files: Vec<String> = std::fs::read_dir(&lib)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().map_or(false, |x| x == "c"))
        .map(|p| p.display().to_string())
        .collect();
    cc::Build::new()
        .files(files)
        .include(format!("{lib}/includes"))
        .include(&lib)
        .define("NGHTTP2_STATICLIB", None)
        .define("HAVE_ARPA_INET_H", None)
        .define("HAVE_NETINET_IN_H", None)
        .define("NDEBUG", None)
        .opt_level(3)
        .flag_if_supported(if std::env::var("NO_NATIVE").is_ok() { "-O3" } else { "-march=native" })
        .warnings(false)
        .compile("nghttp2");
    println!("cargo::rerun-if-env-changed=EXT");
    println!("cargo::rerun-if-env-changed=NO_NATIVE");
}
