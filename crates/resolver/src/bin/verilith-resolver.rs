//! verilith-resolver: a recursive, caching DNS resolver.
//!
//!   verilith-resolver [--listen ADDR] [--port 53] [--threads N]
//!                     [--dot PORT --doh PORT --http PORT --cert PEM --key PEM]   (built with --features tls)
//!                     [--root IP]... [--upstream-port PORT]
//!                     [--trust-anchor "TAG ALG DIGEST-TYPE HEX"]... [--no-dnssec]
//!
//! DNSSEC validation is on, from the IANA root anchors, unless
//! `--no-dnssec` or other anchors are given.
#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
fn main() {}

#[cfg(not(verus_keep_ghost))]
fn main() {
    use std::net::{IpAddr, SocketAddr, TcpListener};
    use std::sync::Arc;
    use verilith_resolver::service::{self, Options, Resolver};

    let mut o = Options::default();
    let mut listen: IpAddr = "127.0.0.1".parse().unwrap();
    let mut port: u16 = 53;
    let mut threads: usize = 0;
    let mut roots: Vec<Vec<u8>> = Vec::new();
    let mut anchors: Vec<Vec<u8>> = Vec::new();
    let mut dnssec = true;
    #[allow(unused_mut)]
    let (mut dot, mut doh, mut http, mut cert, mut key): (Option<u16>, Option<u16>, Option<u16>, Option<String>, Option<String>) =
        (None, None, None, None, None);
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut v = || args.next().unwrap_or_else(|| panic!("{a} needs a value"));
        match a.as_str() {
            "--listen" => listen = v().parse().expect("--listen"),
            "--port" => port = v().parse().expect("--port"),
            "--threads" => threads = v().parse().expect("--threads"),
            "--root" => {
                roots.push(match v().parse::<IpAddr>().expect("--root") {
                    IpAddr::V4(x) => x.octets().to_vec(),
                    IpAddr::V6(x) => x.octets().to_vec(),
                })
            }
            "--trust-anchor" => anchors.push(service::parse_ds(&v()).expect("--trust-anchor: TAG ALG DIGEST-TYPE HEX")),
            "--no-dnssec" => dnssec = false,
            "--upstream-port" => o.upstream_port = v().parse().expect("--upstream-port"),
            "--timeout-ms" => o.timeout = std::time::Duration::from_millis(v().parse().expect("--timeout-ms")),
            "--dot" => dot = Some(v().parse().expect("--dot")),
            "--doh" => doh = Some(v().parse().expect("--doh")),
            "--http" => http = Some(v().parse().expect("--http")),
            "--cert" => cert = Some(v()),
            "--key" => key = Some(v()),
            _ => panic!("unknown argument {a}"),
        }
    }
    if !roots.is_empty() {
        o.roots = roots;
    }
    if !anchors.is_empty() {
        o.trust_anchors = anchors;
    }
    if !dnssec {
        o.trust_anchors = Vec::new();
    }
    if threads == 0 {
        threads = (std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1) * 8).max(32);
    }
    let r = Arc::new(Resolver::new(&o));
    let at = SocketAddr::new(listen, port);
    let sock = service::bind_udp(at).expect("UDP bind");
    let mut hs = service::udp(r.clone(), sock, threads).expect("UDP");
    hs.push(service::tcp(r.clone(), TcpListener::bind(at).expect("TCP bind")));
    eprintln!(
        "verilith-resolver: UDP and TCP on {at}, DNSSEC validation {}",
        if o.trust_anchors.is_empty() { "off" } else { "on" }
    );
    #[cfg(feature = "tls")]
    {
        if let Some(p) = dot {
            let (c, k) = (cert.as_deref().expect("--cert"), key.as_deref().expect("--key"));
            let d = Arc::new(service::tls::dot_config(c, k).expect("DoT certificate"));
            hs.push(service::tls::dot(r.clone(), d, TcpListener::bind(SocketAddr::new(listen, p)).expect("DoT bind")));
            eprintln!("verilith-resolver: DNS over TLS on {}", SocketAddr::new(listen, p));
        }
        if let Some(p) = doh {
            let IpAddr::V4(v4) = listen else { panic!("--doh needs an IPv4 --listen") };
            let (c, k) = (cert.clone().expect("--cert"), key.clone().expect("--key"));
            let hp = http.unwrap_or(0);
            let r2 = r.clone();
            eprintln!("verilith-resolver: DNS over HTTPS on https://{}:{p}/dns-query", listen);
            hs.push(std::thread::spawn(move || {
                service::tls::doh(r2, v4.octets(), hp, p, &c, &k, threads).expect("DoH");
            }));
        }
    }
    #[cfg(not(feature = "tls"))]
    if dot.is_some() || doh.is_some() || http.is_some() || cert.is_some() || key.is_some() {
        panic!("built without --features tls: no DNS over TLS or HTTPS");
    }
    for h in hs {
        let _ = h.join();
    }
}
