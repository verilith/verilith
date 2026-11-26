// Builds ls-qpack from a clone at $EXT (default ./ext, as fetched by
// run.sh), with -O3 -march=native, and the wrapper the benchmark calls.
fn main() {
    let ext = std::env::var("EXT").unwrap_or_else(|_| format!("{}/ext", std::env::var("CARGO_MANIFEST_DIR").unwrap()));
    let mut b = cc::Build::new();
    if std::env::var("BENCH_PORTABLE").is_err() {
        b.flag("-march=native");
    }
    b.file(format!("{ext}/ls-qpack/lsqpack.c"))
        .file(format!("{ext}/ls-qpack/deps/xxhash/xxhash.c"))
        .file("lsq.c")
        .include(format!("{ext}/ls-qpack"))
        .include(format!("{ext}/ls-qpack/deps/xxhash"))
        .define("NDEBUG", None)
        .opt_level(3)
        .flag("-w")
        .compile("lsqpack");
    println!("cargo::rerun-if-env-changed=EXT");
    println!("cargo::rerun-if-env-changed=BENCH_PORTABLE");
    println!("cargo::rerun-if-changed=lsq.c");
}
