//! verilith-serverless: serves WebAssembly functions over HTTP.
//!
//!   verilith-serverless --http PORT [--threads N] [--fuel N] [--max-memory MIB]
//!                       --fn NAME=FILE.wasm [--fn NAME=FILE.wasm ...]
//!
//! `GET|POST /fn/NAME[/...]` runs function NAME; anything else is 404.
// Verus checks the library's proofs; this binary is plain Rust over it.
#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
fn main() {}

#[cfg(not(verus_keep_ghost))]
fn main() {
    use std::sync::Arc;
    use verilith_serverless::{Functions, Options};

    let mut port = 8080u16;
    let mut threads = 0usize;
    let mut opts = Options::default();
    let mut fns: Vec<(String, String)> = Vec::new();
    let mut args = std::env::args().skip(1);
    let usage = || -> ! {
        eprintln!("usage: verilith-serverless --http PORT [--threads N] [--fuel N] [--max-memory MIB] --fn NAME=FILE.wasm ...");
        std::process::exit(2)
    };
    while let Some(a) = args.next() {
        let mut val = || args.next().unwrap_or_else(|| usage());
        match a.as_str() {
            "--http" => port = val().parse().unwrap_or_else(|_| usage()),
            "--threads" => threads = val().parse().unwrap_or_else(|_| usage()),
            "--fuel" => opts.fuel = val().parse().unwrap_or_else(|_| usage()),
            "--max-memory" => opts.max_memory = val().parse::<u64>().unwrap_or_else(|_| usage()) << 20,
            "--fn" => {
                let v = val();
                let Some((n, f)) = v.split_once('=') else { usage() };
                fns.push((n.to_string(), f.to_string()));
            }
            _ => usage(),
        }
    }
    if fns.is_empty() {
        usage();
    }
    let mut functions = Functions::new();
    for (name, file) in &fns {
        let wasm = std::fs::read(file).unwrap_or_else(|e| {
            eprintln!("{file}: {e}");
            std::process::exit(1)
        });
        if let Err(e) = functions.add(name, &wasm, opts) {
            eprintln!("{file}: {e}");
            std::process::exit(1);
        }
        eprintln!("/fn/{name} -> {file}");
    }
    let mut cfg = verilith_server::Config { port, ..verilith_server::Config::default() };
    if threads > 0 {
        cfg.threads = threads;
    }
    if let Err(e) = verilith_server::serve(cfg, Arc::new(functions)) {
        eprintln!("verilith-serverless: {e}");
        std::process::exit(1);
    }
}
