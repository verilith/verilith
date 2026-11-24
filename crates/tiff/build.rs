// Compiles capi/tiffshim.c, the variadic half of the libtiff C API
// (TIFFGetField, TIFFError, ...), which stable Rust cannot define. With the
// tiff-abi feature it also defines them under libtiff's names. Not on
// WebAssembly, which has no C library: the C API is left out there.
fn main() {
    println!("cargo::rerun-if-changed=capi/tiffshim.c");
    if std::env::var("CARGO_CFG_TARGET_FAMILY").is_ok_and(|f| f.split(',').any(|x| x == "wasm")) {
        return;
    }
    let mut b = cc::Build::new();
    b.file("capi/tiffshim.c").warnings(true);
    if std::env::var_os("CARGO_FEATURE_TIFF_ABI").is_some() {
        b.define("VTIFF_ABI", None);
    }
    b.compile("vtiffshim");
}
