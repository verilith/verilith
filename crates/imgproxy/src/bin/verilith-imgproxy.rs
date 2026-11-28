//! verilith-imgproxy: an image proxy and thumbnailer that answers
//! imgproxy's URLs.
//!
//!   verilith-imgproxy [--http PORT] [--threads N] [--local-root DIR]
//!                     [--no-http-sources] [--allowed-source PREFIX]...
//!                     [--max-src-resolution MEGAPIXELS] [--level 0-9] [--ttl SECONDS]
//!                     [--tls PORT --cert PEM --key PEM]   (built with --features tls)
//!                     [--ca-bundle PEM]                    (built with --features tls)
//!                     [--watermark IMAGE]
//!
//! Built with `--features tls`, `https://` sources are fetched with the
//! verified TLS 1.3 client, trusting the certificates in --ca-bundle, or
//! else $SSL_CERT_FILE, or else the system's bundle.
//!
//! The settings imgproxy reads from the environment are read too, under
//! the same names: IMGPROXY_KEY and IMGPROXY_SALT (hex; with no key, URLs
//! need no signature), IMGPROXY_BIND's port, IMGPROXY_LOCAL_FILESYSTEM_ROOT,
//! IMGPROXY_ALLOWED_SOURCES (comma-separated), IMGPROXY_MAX_SRC_RESOLUTION,
//! IMGPROXY_MAX_SRC_FILE_SIZE, IMGPROXY_DOWNLOAD_TIMEOUT, IMGPROXY_TTL,
//! IMGPROXY_WATERMARK_PATH and IMGPROXY_WATERMARK_DATA (base64).
//! A flag wins over the environment.
//!
//!   GET  /%signature/%options/plain/%url[@png]
//!   GET  /%signature/%options/%base64url[.png]
//!   POST /%signature/%options/upload[@png]     (the image is the body)
//!   GET  /health
// Verus checks the library's proofs; this binary is plain Rust over it.
#[cfg(verus_keep_ghost)]
fn main() {}

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
fn main() {
    use std::sync::Arc;
    use verilith_imgproxy::handler::Proxy;
    use verilith_imgproxy::proxy::{unhex, Keys, Limits};
    use verilith_server::{serve, Config, Request, Response};

    let args: Vec<String> = std::env::args().collect();
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let env = |k: &str| std::env::var(k).ok().filter(|v| !v.is_empty());
    let die = |m: &str| -> ! {
        eprintln!("verilith-imgproxy: {m}");
        std::process::exit(2)
    };

    let keys = Keys {
        key: env("IMGPROXY_KEY").map(|k| unhex(&k).unwrap_or_else(|| die("IMGPROXY_KEY is not hex"))).unwrap_or_default(),
        salt: env("IMGPROXY_SALT").map(|k| unhex(&k).unwrap_or_else(|| die("IMGPROXY_SALT is not hex"))).unwrap_or_default(),
    };
    let mut limits = Limits::default();
    if let Some(m) = arg("--max-src-resolution").or_else(|| env("IMGPROXY_MAX_SRC_RESOLUTION")) {
        let mp: f64 = m.parse().unwrap_or_else(|_| die("bad max source resolution"));
        limits.max_src_px = (mp * 1e6) as u64;
        limits.max_out_px = limits.max_src_px.max(limits.max_out_px);
    }
    if let Some(n) = env("IMGPROXY_MAX_SRC_FILE_SIZE").and_then(|v| v.parse::<usize>().ok()).filter(|&n| n > 0) {
        limits.max_src_bytes = n;
    }
    if let Some(t) = env("IMGPROXY_DOWNLOAD_TIMEOUT").and_then(|v| v.parse().ok()) {
        limits.timeout = t;
    }
    if let Some(l) = arg("--level") {
        limits.level = l.parse().ok().filter(|&l| l <= 9).unwrap_or_else(|| die("--level is 0 to 9"));
    }
    let local_root = arg("--local-root").or_else(|| env("IMGPROXY_LOCAL_FILESYSTEM_ROOT")).map(|r| {
        let f = std::fs::File::open(&r).unwrap_or_else(|e| die(&format!("{r}: {e}")));
        if !f.metadata().map(|m| m.is_dir()).unwrap_or(false) {
            die(&format!("{r} is not a directory"));
        }
        f
    });
    let mut allowed: Vec<Vec<u8>> = args.iter().enumerate().filter(|(_, a)| *a == "--allowed-source").filter_map(|(i, _)| args.get(i + 1)).map(|s| s.as_bytes().to_vec()).collect();
    if let Some(v) = env("IMGPROXY_ALLOWED_SOURCES") {
        allowed.extend(v.split(',').map(|s| s.trim().as_bytes().to_vec()).filter(|s| !s.is_empty()));
    }
    let ttl = arg("--ttl").or_else(|| env("IMGPROXY_TTL")).map_or(31_536_000, |t| t.parse().unwrap_or_else(|_| die("bad TTL")));
    let port = arg("--http")
        .or_else(|| env("IMGPROXY_BIND").and_then(|b| b.rsplit(':').next().map(str::to_string)))
        .map_or(8080, |p| p.parse().unwrap_or_else(|_| die("bad port")));
    let http_sources = !args.iter().any(|a| a == "--no-http-sources");
    #[cfg(feature = "tls")]
    let tls = if !http_sources {
        None
    } else {
        match verilith_imgproxy::proxy::load_roots(arg("--ca-bundle").as_deref()) {
            Ok((_, roots)) => Some(verilith_imgproxy::proxy::tls_config(roots)),
            Err(e) if arg("--ca-bundle").is_some() => die(&format!("--ca-bundle: {e}")),
            Err(e) => {
                eprintln!("verilith-imgproxy: https sources are off: {e}");
                None
            }
        }
    };
    #[cfg(not(feature = "tls"))]
    let tls = None;
    // The watermark: a file, or the image itself in base64.
    let wm_data = match (arg("--watermark").or_else(|| env("IMGPROXY_WATERMARK_PATH")), env("IMGPROXY_WATERMARK_DATA")) {
        (Some(p), _) => Some(std::fs::read(&p).unwrap_or_else(|e| die(&format!("{p}: {e}")))),
        (None, Some(d)) => Some(
            verilith_text::base64::STANDARD
                .decode(d.trim().as_bytes())
                .unwrap_or_else(|_| die("IMGPROXY_WATERMARK_DATA is not base64")),
        ),
        (None, None) => None,
    };
    let watermark = wm_data.map(|d| {
        verilith_imgproxy::proxy::decode_shrunk(&d, limits.max_src_px, 1).unwrap_or_else(|e| die(&format!("watermark: {}", e.message())))
    });
    let proxy = Proxy { keys, limits, local_root, http_sources, tls, allowed, ttl, watermark };

    let mut srv_limits = verilith_server::Limits::default();
    srv_limits.max_body = proxy.limits.max_src_bytes;
    let cfg = Config {
        port,
        threads: arg("--threads").map_or(0, |t| t.parse().unwrap_or_else(|_| die("bad --threads"))),
        limits: srv_limits,
        #[cfg(feature = "tls")]
        tls: arg("--tls").map(|p| {
            let (cert, key) = (arg("--cert").unwrap_or_else(|| die("--tls needs --cert")), arg("--key").unwrap_or_else(|| die("--tls needs --key")));
            let c = verilith_server::tls::config(&cert, &key).unwrap_or_else(|e| die(&format!("TLS: {e}")));
            (p.parse().unwrap_or_else(|_| die("bad --tls port")), c)
        }),
        ..Config::default()
    };
    let h = move |req: &Request, res: &mut Response| proxy.handle(req, res);
    serve(cfg, Arc::new(h)).unwrap_or_else(|e| die(&format!("serve: {e}")));
}
