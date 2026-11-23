// Compiles capi/tiffshim.c, the variadic half of the libtiff C API
// (TIFFGetField, TIFFError, ...), which stable Rust cannot define. With the
// tiff-abi feature it also defines them under libtiff's names.
fn main() {
    println!("cargo::rerun-if-changed=capi/tiffshim.c");
    let mut b = cc::Build::new();
    b.file("capi/tiffshim.c").warnings(true);
    if std::env::var_os("CARGO_FEATURE_TIFF_ABI").is_some() {
        b.define("VTIFF_ABI", None);
    }
    b.compile("vtiffshim");
}
