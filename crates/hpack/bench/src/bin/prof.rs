// For profiling (valgrind --tool=callgrind): many new connections, each
// encoding the first static file response.
use verilith_hpack::{Encoder, Header};
fn main() {
    let h = |n: &'static str, v: &'static str| Header { name: n.as_bytes(), value: v.as_bytes(), sensitive: false };
    let block = [
        h(":status", "200"), h("content-type", "text/html; charset=utf-8"), h("content-length", "12345"),
        h("date", "Thu, 26 Nov 2026 06:00:10 GMT"), h("server", "verilith"), h("etag", "\"0123456789abcdef\""),
        h("last-modified", "Tue, 24 Nov 2026 10:00:00 GMT"), h("cache-control", "public, max-age=31536000, immutable"),
        h("accept-ranges", "bytes"), h("vary", "accept-encoding"), h("content-encoding", "br"),
        h("strict-transport-security", "max-age=63072000; includeSubDomains; preload"),
    ];
    let n: usize = std::env::args().nth(1).map_or(100000, |s| s.parse().unwrap());
    let mut out = Vec::with_capacity(4096);
    let mut total = 0;
    for _ in 0..n {
        let mut e = Encoder::new().unwrap();
        out.clear();
        assert!(e.encode(&block, &mut out));
        out.clear();
        assert!(e.encode(&block, &mut out));
        total += out.len();
    }
    println!("{total}");
}
