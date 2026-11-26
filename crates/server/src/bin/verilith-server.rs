//! verilith-server: the routes bench/server compares every server on.
//!
//!   verilith-server --threads N --http PORT [--h2c PORT] [--root DIR] [--protocols]
//!                   [--tls PORT --cert PEM --key PEM]   (built with --features tls)
//!                   [--tls-backend verilith|rustls]     (rustls: --features tls-rustls)
//!                   [--h3 PORT --cert PEM --key PEM]    (UDP; built with --features h3)
//!                   [--h3-backend verilith|quinn]       (QUIC: verilith-quic-conn, or quinn-proto)
//!                   [--io-uring]                        (Linux: io_uring instead of epoll)
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
#[cfg(not(verus_keep_ghost))]
use std::sync::Arc;

#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(not(verus_keep_ghost))]
use verilith_server::{serve, Config, Field, Fields, Request, Response};

#[cfg(not(verus_keep_ghost))]
fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

#[cfg(not(verus_keep_ghost))]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--protocols") {
        let mut p = vec!["http", "h2c"];
        if cfg!(feature = "tls") {
            p.push("tls");
        }
        if cfg!(feature = "tls-rustls") {
            p.push("tls-rustls");
        }
        if cfg!(feature = "h3") {
            p.push("h3");
        }
        if cfg!(target_os = "linux") {
            p.push("io-uring");
        }
        println!("{}", p.join(" "));
        return;
    }
    // `--root DIR` is served under /static/ (verified path resolution,
    // openat2 beneath DIR; see files.rs).
    let files = arg(&args, "--root").map(|r| verilith_server::files::Files::new(&r).expect("--root"));
    let cfg = Config {
        port: arg(&args, "--http").map_or(8080, |p| p.parse().unwrap()),
        h2c_port: arg(&args, "--h2c").map(|p| p.parse().unwrap()),
        threads: arg(&args, "--threads").map_or(0, |t| t.parse().unwrap()),
        spin: arg(&args, "--spin").map_or(0, |t| t.parse().unwrap()),
        io_uring: args.iter().any(|a| a == "--io-uring"),
        #[cfg(feature = "tls")]
        tls: arg(&args, "--tls").map(|p| {
            let (cert, key) = (arg(&args, "--cert").expect("--cert"), arg(&args, "--key").expect("--key"));
            let c = match arg(&args, "--tls-backend").as_deref() {
                // `--early-data N`: take up to N bytes of 0-RTT data.
                None | Some("verilith") => verilith_server::tls::config_early(&cert, &key, arg(&args, "--early-data").map_or(0, |n| n.parse().unwrap())),
                #[cfg(feature = "tls-rustls")]
                Some("rustls") => verilith_server::tls::rustls_config(&cert, &key),
                Some(b) => panic!("unknown --tls-backend {b}"),
            }
            .expect("TLS configuration");
            (p.parse().unwrap(), c)
        }),
        #[cfg(feature = "h3")]
        h3: arg(&args, "--h3").map(|p| {
            let (cert, key) = (arg(&args, "--cert").expect("--cert"), arg(&args, "--key").expect("--key"));
            use verilith_server::h3::Backend;
            let b = match arg(&args, "--h3-backend").as_deref() {
                None | Some("verilith") => Backend::Verilith,
                Some("quinn") => Backend::Quinn,
                Some(b) => panic!("unknown --h3-backend {b}"),
            };
            let c = verilith_server::h3::server_config_on(b, &cert, &key, Default::default()).expect("QUIC configuration");
            (p.parse().unwrap(), c)
        }),
        ..Config::default()
    };
    let text = Fields::new(&[Field { name: b"Content-Type", value: b"text/plain" }]).unwrap();
    let h = move |req: &Request, res: &mut Response| {
        let path = req.path();
        if path == b"/plaintext" {
            let _ = res.send_prepared(200, &text, b"Hello, World!");
        } else if let (Some(f), Some(rest)) = (&files, path.strip_prefix(b"/static")) {
            if !f.serve(req, res, rest) {
                res.error(404);
            }
        } else {
            res.error(404);
        }
    };
    serve(cfg, Arc::new(h)).expect("serve");
}
