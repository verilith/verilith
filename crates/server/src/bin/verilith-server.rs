//! verilith-server: the routes bench/server compares every server on.
//!
//!   verilith-server --threads N --http PORT [--h2c PORT] [--root DIR] [--protocols]
//!                   [--tls PORT --cert PEM --key PEM]   (built with --features tls)
//!
//!   GET /plaintext       "Hello, World!", text/plain
//!   GET /static/<name>   a file under DIR, read at start; sent with
//!                        sendfile from a sealed copy (Linux, 16-112 KiB)
//!
//! `--protocols` prints which of bench/server's ports this build serves.
// Verus checks the library's proofs; this binary is plain Rust over it.
#[cfg(verus_keep_ghost)]
fn main() {}

#[cfg(not(verus_keep_ghost))]
use std::collections::HashMap;
#[cfg(not(verus_keep_ghost))]
use std::sync::Arc;

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(not(verus_keep_ghost))]
use verilith_server::{serve, Config, Field, Fields, Request, Response, StaticBody};

#[cfg(not(verus_keep_ghost))]
fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

#[cfg(not(verus_keep_ghost))]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--protocols") {
        println!("{}", if cfg!(feature = "tls") { "http h2c tls" } else { "http h2c" });
        return;
    }
    let mut files: HashMap<Vec<u8>, StaticBody> = HashMap::new();
    if let Some(root) = arg(&args, "--root") {
        for e in std::fs::read_dir(&root).expect("--root") {
            let e = e.unwrap();
            if e.file_type().unwrap().is_file() {
                let name = format!("/static/{}", e.file_name().into_string().unwrap());
                files.insert(name.into_bytes(), StaticBody::new(std::fs::read(e.path()).unwrap()));
            }
        }
    }
    let cfg = Config {
        port: arg(&args, "--http").map_or(8080, |p| p.parse().unwrap()),
        h2c_port: arg(&args, "--h2c").map(|p| p.parse().unwrap()),
        threads: arg(&args, "--threads").map_or(0, |t| t.parse().unwrap()),
        spin: arg(&args, "--spin").map_or(0, |t| t.parse().unwrap()),
        #[cfg(feature = "tls")]
        tls: arg(&args, "--tls").map(|p| {
            let c = verilith_server::tls::config(&arg(&args, "--cert").expect("--cert"), &arg(&args, "--key").expect("--key")).expect("TLS configuration");
            (p.parse().unwrap(), c)
        }),
        ..Config::default()
    };
    let files = Arc::new(files);
    let text = Fields::new(&[Field { name: b"Content-Type", value: b"text/plain" }]).unwrap();
    let octet = Fields::new(&[Field { name: b"Content-Type", value: b"application/octet-stream" }]).unwrap();
    let h = move |req: &Request, res: &mut Response| {
        let path = req.path();
        if path == b"/plaintext" {
            let _ = res.send_prepared(200, &text, b"Hello, World!");
        } else if let Some(b) = files.get(path) {
            let _ = res.send_static(200, &octet, b);
        } else {
            res.error(404);
        }
    };
    serve(cfg, Arc::new(h)).expect("serve");
}
