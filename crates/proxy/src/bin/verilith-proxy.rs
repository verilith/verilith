//! verilith-proxy: a reverse proxy on verilith-server.
//!
//!   verilith-proxy --upstream NAME=HOST:PORT[,HOST:PORT...]   (one or more)
//!                  --route [HOST]/PREFIX=NAME                 (one or more; first match
//!                                                             by host, then longest prefix)
//!                  [--http PORT] [--h2c PORT] [--listen ADDR] [--threads N]
//!                  [--tls PORT --cert PEM --key PEM]   (built with --features tls)
//!                  [--h3 PORT --cert PEM --key PEM]    (built with --features h3)
//!                  [--cache-mb N] (0: no cache; default 64) [--no-compress]
//!
//! For example, everything to two backends, and /api on example.com to a
//! third:
//!
//!   verilith-proxy --http 8080 --upstream web=127.0.0.1:9001,127.0.0.1:9002 \
//!       --upstream api=10.0.0.5:8000 --route /=web --route example.com/api=api
//!
//! Upstream host names are resolved once, at start (IPv4).
// Verus checks the library's proofs; this binary is plain Rust over it.
#[cfg(verus_keep_ghost)]
fn main() {}

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
fn main() {
    use std::net::ToSocketAddrs;
    use std::sync::Arc;
    use verilith_proxy::proxy::{Config as ProxyConfig, Proxy, Server};
    use verilith_proxy::route::Route;
    use verilith_server::{serve, Config};

    let args: Vec<String> = std::env::args().collect();
    let arg = |k: &str| args.iter().position(|a| a == k).map(|i| args.get(i + 1).cloned().unwrap_or_else(|| die(&format!("{k} needs a value"))));
    let all = |k: &str| -> Vec<String> {
        args.iter().enumerate().filter(|(_, a)| *a == k).map(|(i, _)| args.get(i + 1).cloned().unwrap_or_else(|| die(&format!("{k} needs a value")))).collect()
    };
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{}", include_str!("verilith-proxy.rs").lines().take_while(|l| l.starts_with("//!")).map(|l| l.trim_start_matches("//!").strip_prefix(' ').unwrap_or("")).collect::<Vec<_>>().join("\n"));
        return;
    }

    let mut names: Vec<String> = Vec::new();
    let mut upstreams: Vec<Vec<Server>> = Vec::new();
    for u in all("--upstream") {
        let (name, list) = u.split_once('=').unwrap_or_else(|| die("--upstream NAME=HOST:PORT[,HOST:PORT...]"));
        let mut servers = Vec::new();
        for hp in list.split(',') {
            let a = hp
                .to_socket_addrs()
                .ok()
                .and_then(|mut it| it.find_map(|a| match a {
                    std::net::SocketAddr::V4(v) => Some(v),
                    _ => None,
                }))
                .unwrap_or_else(|| die(&format!("cannot resolve {hp} to an IPv4 address")));
            servers.push(Server { addr: a.ip().octets(), port: a.port() });
        }
        names.push(name.to_string());
        upstreams.push(servers);
    }
    let mut routes = Vec::new();
    for r in all("--route") {
        let (spec, name) = r.rsplit_once('=').unwrap_or_else(|| die("--route [HOST]/PREFIX=NAME"));
        let upstream = names.iter().position(|n| n == name).unwrap_or_else(|| die(&format!("--route: no upstream named {name}")));
        let slash = spec.find('/').unwrap_or_else(|| die("--route: the prefix starts with /"));
        let (host, prefix) = spec.split_at(slash);
        let prefix: Vec<Vec<u8>> = prefix.split('/').filter(|c| !c.is_empty()).map(|c| c.as_bytes().to_vec()).collect();
        routes.push(Route { host: (!host.is_empty()).then(|| host.as_bytes().to_vec()), prefix, upstream });
    }
    if routes.is_empty() {
        if upstreams.len() == 1 {
            routes.push(Route { host: None, prefix: Vec::new(), upstream: 0 });
        } else {
            die("give at least one --route");
        }
    }
    let mut pc = ProxyConfig { routes, upstreams, ..ProxyConfig::default() };
    if let Some(mb) = arg("--cache-mb") {
        pc.cache_bytes = mb.parse::<usize>().unwrap_or_else(|_| die("--cache-mb N")) << 20;
    }
    pc.compress = !args.iter().any(|a| a == "--no-compress");

    let listen: [u8; 4] = arg("--listen").map_or([127, 0, 0, 1], |a| a.parse::<std::net::Ipv4Addr>().unwrap_or_else(|_| die("--listen IPv4")).octets());
    let cfg = Config {
        addr: listen,
        port: arg("--http").map_or(8080, |p| p.parse().unwrap_or_else(|_| die("--http PORT"))),
        h2c_port: arg("--h2c").map(|p| p.parse().unwrap_or_else(|_| die("--h2c PORT"))),
        threads: arg("--threads").map_or(0, |t| t.parse().unwrap_or_else(|_| die("--threads N"))),
        server: b"verilith-proxy",
        #[cfg(feature = "tls")]
        tls: arg("--tls").map(|p| {
            let (cert, key) = (arg("--cert").unwrap_or_else(|| die("--tls needs --cert")), arg("--key").unwrap_or_else(|| die("--tls needs --key")));
            let c = verilith_server::tls::config(&cert, &key).unwrap_or_else(|e| die(&format!("TLS configuration: {e:?}")));
            (p.parse().unwrap_or_else(|_| die("--tls PORT")), c)
        }),
        #[cfg(feature = "h3")]
        h3: arg("--h3").map(|p| {
            let (cert, key) = (arg("--cert").unwrap_or_else(|| die("--h3 needs --cert")), arg("--key").unwrap_or_else(|| die("--h3 needs --key")));
            let c = verilith_server::h3::server_config(&cert, &key, Default::default()).unwrap_or_else(|e| die(&format!("QUIC configuration: {e:?}")));
            (p.parse().unwrap_or_else(|_| die("--h3 PORT")), c)
        }),
        ..Config::default()
    };
    serve(cfg, Arc::new(Proxy::new(pc))).unwrap_or_else(|e| die(&format!("serve: {e}")));
}

#[cfg(not(verus_keep_ghost))]
fn die(msg: &str) -> ! {
    eprintln!("verilith-proxy: {msg}");
    std::process::exit(2)
}
