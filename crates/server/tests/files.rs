//! Static files: paths that try to leave the root, conditional and range
//! requests, directories, and the verified path and range functions.
use std::sync::OnceLock;

use verilith_server::files::Files;
use verilith_server::h1::{Conn, Ctx, Limits};
use verilith_server::path::resolve_exec;
use verilith_server::range::{parse_range, Rng};
use verilith_server::{Request, Response};

fn root() -> &'static (std::path::PathBuf, Files) {
    static R: OnceLock<(std::path::PathBuf, Files)> = OnceLock::new();
    R.get_or_init(|| {
        let base = std::env::temp_dir().join(format!("verilith-files-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let root = base.join("root");
        std::fs::create_dir_all(root.join("sub")).unwrap();
        std::fs::create_dir_all(root.join(".git")).unwrap();
        std::fs::create_dir_all(base.join("outside")).unwrap();
        std::fs::write(base.join("outside/secret"), b"secret").unwrap();
        std::fs::write(root.join("index.html"), b"<h1>hi</h1>").unwrap();
        std::fs::write(root.join("sub/index.html"), b"sub").unwrap();
        std::fs::write(root.join("a.txt"), b"hello world").unwrap();
        std::fs::write(root.join("sp ace.txt"), b"space").unwrap();
        std::fs::write(root.join(".git/config"), b"cfg").unwrap();
        let big: Vec<u8> = (0..100_000u32).map(|i| (i * 7 + 3) as u8).collect();
        std::fs::write(root.join("big.bin"), &big).unwrap();
        std::os::unix::fs::symlink("../outside/secret", root.join("link-out")).unwrap();
        std::os::unix::fs::symlink("a.txt", root.join("link-in")).unwrap();
        let f = Files::new(root.to_str().unwrap()).unwrap();
        (root, f)
    })
}

fn handler(req: &Request, res: &mut Response) {
    if !root().1.serve(req, res, req.path()) {
        res.error(404);
    }
}

/// Status, the head, and the body of one GET with `extra` header lines.
fn get(method: &str, target: &str, extra: &str) -> (u16, String, Vec<u8>) {
    let req = format!("{method} {target} HTTP/1.1\r\nHost: x\r\n{extra}\r\n");
    let mut c = Conn::new(Limits::default());
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let b = c.read_buf();
    b[..req.len()].copy_from_slice(req.as_bytes());
    c.filled(req.len());
    c.process(&handler, &ctx);
    let mut out = Vec::new();
    loop {
        let mut v: [&[u8]; 8] = [&[]; 8];
        let k = c.pending(&mut v);
        if k == 0 {
            break;
        }
        let mut n = 0;
        for s in &v[..k] {
            out.extend_from_slice(s);
            n += s.len();
        }
        c.wrote(n);
    }
    let end = out.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
    let head = String::from_utf8(out[..end].to_vec()).unwrap();
    let status = head[9..12].parse().unwrap();
    (status, head, out[end..].to_vec())
}

fn header(head: &str, name: &str) -> Option<String> {
    head.lines().find_map(|l| {
        let (n, v) = l.split_once(':')?;
        n.eq_ignore_ascii_case(name).then(|| v.trim().to_string())
    })
}

#[test]
fn nothing_outside_the_root() {
    for t in [
        "/../outside/secret",
        "/%2e%2e/outside/secret",
        "/%2E%2E/outside/secret",
        "/sub/../../outside/secret",
        "/sub/..%2f..%2foutside/secret",
        "/sub%2f..%2f..%2foutside%2fsecret",
        "/..%5coutside%5csecret",
        "/a.txt%00",
        "/link-out",
        "/.git/config",
        "/%2egit/config",
        "/nope",
        "a.txt",
    ] {
        let (s, _, body) = get("GET", t, "");
        assert_eq!(s, 404, "{t}");
        assert_ne!(body, b"secret", "{t}");
    }
}

#[test]
fn files_and_directories() {
    let (s, h, b) = get("GET", "/a.txt", "");
    assert_eq!((s, &b[..]), (200, &b"hello world"[..]));
    assert_eq!(header(&h, "content-type").unwrap(), "text/plain; charset=utf-8");
    assert_eq!(header(&h, "accept-ranges").unwrap(), "bytes");
    assert_eq!(get("GET", "/sub/../a.txt", "").2, b"hello world");
    assert_eq!(get("GET", "/./a.txt", "").2, b"hello world");
    assert_eq!(get("GET", "//a.txt", "").2, b"hello world");
    assert_eq!(get("GET", "/sp%20ace.txt", "").2, b"space");
    assert_eq!(get("GET", "/a.txt?x=1", "").2, b"hello world");
    assert_eq!(get("GET", "/link-in", "").2, b"hello world");
    assert_eq!(get("GET", "/", "").2, b"<h1>hi</h1>");
    assert_eq!(get("GET", "/sub/", "").2, b"sub");
    assert_eq!(get("GET", "/sub/.", "").2, b"sub");
    let (s, h, _) = get("GET", "/sub?q", "");
    assert_eq!((s, header(&h, "location").unwrap()), (301, "/sub/?q".to_string()));
    let (s, h, b) = get("HEAD", "/a.txt", "");
    assert_eq!((s, header(&h, "content-length").unwrap(), b.len()), (200, "11".to_string(), 0));
    assert_eq!(get("POST", "/a.txt", "").0, 404);
    let big = get("GET", "/big.bin", "").2;
    assert_eq!(big, std::fs::read(root().0.join("big.bin")).unwrap());
}

#[test]
fn conditional_requests() {
    let (_, h, _) = get("GET", "/a.txt", "");
    let etag = header(&h, "etag").unwrap();
    let lm = header(&h, "last-modified").unwrap();
    let (s, h2, b) = get("GET", "/a.txt", &format!("If-None-Match: {etag}\r\n"));
    assert_eq!((s, b.len()), (304, 0));
    assert_eq!(header(&h2, "etag").unwrap(), etag);
    assert_eq!(get("GET", "/a.txt", &format!("If-None-Match: \"x\", W/{etag}\r\n")).0, 304);
    assert_eq!(get("GET", "/a.txt", "If-None-Match: *\r\n").0, 304);
    assert_eq!(get("GET", "/a.txt", "If-None-Match: \"other\"\r\n").0, 200);
    assert_eq!(get("GET", "/a.txt", &format!("If-Modified-Since: {lm}\r\n")).0, 304);
    // If-None-Match wins over If-Modified-Since.
    assert_eq!(get("GET", "/a.txt", &format!("If-None-Match: \"other\"\r\nIf-Modified-Since: {lm}\r\n")).0, 200);
}

#[test]
fn range_requests() {
    let (s, h, b) = get("GET", "/a.txt", "Range: bytes=0-4\r\n");
    assert_eq!((s, &b[..]), (206, &b"hello"[..]));
    assert_eq!(header(&h, "content-range").unwrap(), "bytes 0-4/11");
    assert_eq!(get("GET", "/a.txt", "Range: bytes=6-\r\n").2, b"world");
    assert_eq!(get("GET", "/a.txt", "Range: bytes=-5\r\n").2, b"world");
    assert_eq!(get("GET", "/a.txt", "Range: bytes=-50\r\n").2, b"hello world");
    assert_eq!(get("GET", "/a.txt", "Range: bytes=6-100\r\n").2, b"world");
    let (s, h, _) = get("GET", "/a.txt", "Range: bytes=11-\r\n");
    assert_eq!((s, header(&h, "content-range").unwrap()), (416, "bytes */11".to_string()));
    // Ignored: several ranges, another unit, a backwards range.
    for r in ["bytes=0-1,3-4", "items=0-1", "bytes=5-2", "bytes=x-1"] {
        assert_eq!(get("GET", "/a.txt", &format!("Range: {r}\r\n")).0, 200, "{r}");
    }
    // If-Range with another validator: the whole file.
    assert_eq!(get("GET", "/a.txt", "Range: bytes=0-4\r\nIf-Range: \"old\"\r\n").0, 200);
    // A range of a file sent with sendfile.
    let whole = std::fs::read(root().0.join("big.bin")).unwrap();
    let (s, _, b) = get("GET", "/big.bin", "Range: bytes=1000-70000\r\n");
    assert_eq!((s, &b[..]), (206, &whole[1000..70001]));
}

#[test]
fn resolve_cases() {
    let r = |p: &str| resolve_exec(p.as_bytes()).map(|(v, d)| (v.iter().map(|c| String::from_utf8(c.clone()).unwrap()).collect::<Vec<_>>().join("|"), d));
    assert_eq!(r("/"), Some((String::new(), true)));
    assert_eq!(r("/a/b"), Some(("a|b".into(), false)));
    assert_eq!(r("/a/./b/../c/"), Some(("a|c".into(), true)));
    assert_eq!(r("/a/%2e%2E"), Some((String::new(), true)));
    assert_eq!(r("/a%20b"), Some(("a b".into(), false)));
    assert_eq!(r("/.."), None);
    assert_eq!(r("/a/../.."), None);
    assert_eq!(r("/a%2fb"), None);
    assert_eq!(r("/a%5cb"), None);
    assert_eq!(r("/a%00"), None);
    assert_eq!(r(""), None);
    assert_eq!(r("a"), None);
}

#[test]
fn range_cases() {
    let p = |v: &str, n: u64| match parse_range(v.as_bytes(), n) {
        Rng::Whole => "whole".to_string(),
        Rng::Unsat => "416".to_string(),
        Rng::Part(s, l) => format!("{s}+{l}"),
    };
    assert_eq!(p("bytes=0-0", 10), "0+1");
    assert_eq!(p("bytes=9-", 10), "9+1");
    assert_eq!(p("bytes=10-", 10), "416");
    assert_eq!(p("bytes=-0", 10), "416");
    assert_eq!(p("bytes=-3", 10), "7+3");
    assert_eq!(p("bytes=0-999999999999999999", 10), "0+10");
    assert_eq!(p("bytes=0-9999999999999999999", 10), "whole");
    assert_eq!(p("bytes=0-", 0), "416");
    assert_eq!(p("bytes=-", 10), "whole");
    assert_eq!(p("bytes= 0-1", 10), "whole");
}
