//! Compiles upstream cJSON (fetched by `scripts/test-c.sh` into
//! `target/upstream/cJSON`) with every public symbol renamed from `cJSON_x`
//! to `up_cJSON_x`, so it links next to vjson's C ABI for differential
//! fuzzing.
use std::{env, fs, path::PathBuf};

fn main() {
    let up = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("../target/upstream/cJSON");
    let header = fs::read_to_string(up.join("cJSON.h")).expect("run scripts/test-c.sh first to fetch cJSON");
    let mut names: Vec<&str> = Vec::new();
    for line in header.lines().filter(|l| l.starts_with("CJSON_PUBLIC(")) {
        if let Some(i) = line.find(" cJSON_").or_else(|| line.find("*cJSON_")).or_else(|| line.find(")cJSON_")) {
            let rest = &line[i + 1..];
            let end = rest.find('(').unwrap();
            names.push(&rest[..end]);
        }
    }
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let defs: String = names.iter().map(|n| format!("#define {n} up_{n}\n")).collect();
    fs::write(out.join("rename.h"), defs).unwrap();
    cc::Build::new()
        .file(up.join("cJSON.c"))
        .flag("-include")
        .flag(out.join("rename.h").to_str().unwrap())
        .flag_if_supported("-fsanitize=address")
        .warnings(false)
        .compile("upcjson");
    println!("cargo:rerun-if-changed={}", up.join("cJSON.c").display());
    println!("cargo:rerun-if-changed=build.rs");
}
