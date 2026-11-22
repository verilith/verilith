//! Compiles upstream libexpat (fetched by `scripts/fetch-expat.sh` into
//! `target/upstream/libexpat`), and the C side of the comparison.
use std::{env, fs, path::PathBuf};

fn main() {
    let root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let up = root.join("../target/upstream/libexpat/expat");
    let lib = up.join("lib");
    assert!(lib.join("xmlparse.c").exists(), "run scripts/fetch-expat.sh first to fetch libexpat");
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    fs::write(
        out.join("expat_config.h"),
        "#define XML_DTD 1\n#define XML_GE 1\n#define XML_NS 1\n#define XML_CONTEXT_BYTES 1024\n\
         #define BYTEORDER 1234\n#define HAVE_MEMMOVE 1\n#define HAVE_GETRANDOM 1\n#define HAVE_SYSCALL_GETRANDOM 1\n\
         #define XML_DEV_URANDOM 1\n",
    )
    .unwrap();
    let asan = env::var("CARGO_ENCODED_RUSTFLAGS").map_or(false, |f| f.contains("sanitizer=address"));
    let mut b = cc::Build::new();
    if asan {
        b.flag("-fsanitize=address");
    }
    b
        .files(["xmlparse.c", "xmltok.c", "xmlrole.c"].iter().map(|f| lib.join(f)))
        .file(root.join("src/expat_canon.c"))
        .include(&out)
        .include(&lib)
        .define("HAVE_EXPAT_CONFIG_H", None)
        .warnings(false)
        .compile("upexpat");
    println!("cargo:rerun-if-changed=src/expat_canon.c");
    println!("cargo:rerun-if-changed=build.rs");
}
