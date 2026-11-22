// Builds the C shim against libpng and libspng. Set LIBPNG_DIR (source
// tree with a `build/` directory holding libpng16.a and pnglibconf.h) and
// LIBSPNG_DIR (source tree with `build/libspng_static.a`).
fn main() {
    let home = std::env::var("HOME").unwrap();
    let lp = std::env::var("LIBPNG_DIR").unwrap_or(format!("{home}/ext/lp16"));
    let sp = std::env::var("LIBSPNG_DIR").unwrap_or(format!("{home}/ext/libspng"));
    cc::Build::new()
        .file("cshim.c")
        .include(&lp)
        .include(format!("{lp}/build"))
        .include(format!("{sp}/spng"))
        .define("SPNG_STATIC", None)
        .opt_level(3)
        .compile("cshim");
    println!("cargo:rustc-link-search=native={lp}/build");
    println!("cargo:rustc-link-search=native={sp}/build");
    println!("cargo:rustc-link-lib=static=png16");
    println!("cargo:rustc-link-lib=static=spng_static");
    println!("cargo:rustc-link-lib=z");
    println!("cargo:rustc-link-lib=m");
    println!("cargo:rerun-if-changed=cshim.c");
}
