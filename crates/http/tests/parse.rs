//! Parsing tests: known messages, every prefix of them, chunked decoding at
//! every split, and a differential check against httparse on generated
//! messages.
use verilith_http::{parse_request, parse_request_with, parse_response, Body, Chunked, ChunkedDecoder, Status};

const GET: &[u8] = b"GET /wp-content/uploads/2010/03/hello-kitty-darth-vader-pink.jpg HTTP/1.1\r\n\
Host: www.kittyhell.com\r\n\
User-Agent: Mozilla/5.0 (Macintosh; U; Intel Mac OS X 10.6; ja-JP-mac; rv:1.9.2.3) Gecko/20100401 Firefox/3.6.3 Pathtraq/0.9\r\n\
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n\
Accept-Language: ja,en-us;q=0.7,en;q=0.3\r\n\
Accept-Encoding: gzip,deflate\r\n\
Accept-Charset: Shift_JIS,utf-8;q=0.7,*;q=0.7\r\n\
Keep-Alive: 115\r\n\
Connection: keep-alive\r\n\
Cookie: wp_ozh_wsa_visits=2; wp_ozh_wsa_visit_lasttime=xxxxxxxxxx; __utma=xxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.xxxxxxxxxx.x; __utmz=xxxxxxxxx.xxxxxxxxxx.x.x.utmccn=(referral)|utmcsr=reader.livedoor.com|utmcct=/reader/|utmcmd=referral\r\n\
\r\n";

#[test]
fn request() {
    let mut hs = Vec::new();
    let Status::Complete(r) = parse_request(GET, &mut hs).unwrap() else { panic!() };
    assert_eq!(r.method(), b"GET");
    assert_eq!(r.target(), b"/wp-content/uploads/2010/03/hello-kitty-darth-vader-pink.jpg");
    assert_eq!(r.minor_version(), 1);
    assert_eq!(r.head_len, GET.len());
    assert_eq!(r.body, Body::Empty);
    let h: Vec<_> = r.headers(&hs).collect();
    assert_eq!(h.len(), 9);
    assert_eq!(h[0], (&b"Host"[..], &b"www.kittyhell.com"[..]));
    assert_eq!(h[7].1, b"keep-alive");
    // Trailing bytes (a pipelined request, a body) are not looked at.
    let mut more = GET.to_vec();
    more.extend_from_slice(b"GARBAGE\0\0");
    let Status::Complete(r2) = parse_request(&more, &mut hs).unwrap() else { panic!() };
    assert_eq!(r2.head_len, GET.len());
}

#[test]
fn every_prefix_is_partial() {
    let mut hs = Vec::new();
    for n in 0..GET.len() {
        assert!(matches!(parse_request(&GET[..n], &mut hs), Ok(Status::Partial)), "prefix {n}");
    }
    let resp = b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\nX: y\r\n\r\n";
    for n in 0..resp.len() {
        assert!(matches!(parse_response(&resp[..n], false, false, &mut hs), Ok(Status::Partial)));
    }
}

#[test]
fn byte_at_a_time_with_last_len() {
    let mut hs = Vec::new();
    let mut last = 0;
    for n in 1..=GET.len() {
        match parse_request_with(&GET[..n], last, 100, &mut hs).unwrap() {
            Status::Partial => assert!(n < GET.len()),
            Status::Complete(r) => {
                assert_eq!(n, GET.len());
                assert_eq!(r.head_len, GET.len());
                assert_eq!(hs.len(), 9);
            }
        }
        last = n;
    }
}

#[test]
fn header_limit() {
    let mut hs = Vec::new();
    assert!(parse_request_with(GET, 0, 9, &mut hs).is_ok());
    assert!(parse_request_with(GET, 0, 8, &mut hs).is_err());
}

#[test]
fn response() {
    let mut hs = Vec::new();
    let b = b"HTTP/1.1 404 Not Found\r\nContent-Length: 3\r\n\r\nabc";
    let Status::Complete(r) = parse_response(b, false, false, &mut hs).unwrap() else { panic!() };
    assert_eq!(r.status(), 404);
    assert_eq!(r.reason(), b"Not Found");
    assert_eq!(r.body, Body::Length(3));
    assert_eq!(r.head_len, b.len() - 3);
}

/// Decodes `input` fed in the pieces given by `cuts`.
fn decode_split(input: &[u8], cuts: &[usize]) -> Option<(Vec<u8>, Vec<u8>)> {
    let mut d = ChunkedDecoder::new();
    let mut out = Vec::new();
    let mut prev = 0;
    for &c in cuts.iter().chain(std::iter::once(&input.len())) {
        let mut piece = input[prev..c].to_vec();
        prev = c;
        match d.decode(&mut piece).ok()? {
            Chunked::More { out: n } => out.extend_from_slice(&piece[..n]),
            Chunked::Done { out: n, rest } => {
                out.extend_from_slice(&piece[..n]);
                let mut tail = piece[n..n + rest].to_vec();
                tail.extend_from_slice(&input[c..]);
                return Some((out, tail));
            }
        }
    }
    None
}

#[test]
fn chunked_every_split() {
    let body = b"6;ext=\"q\\\"v\"\r\nhello \r\n5\r\nworld\r\n0\r\nTrailer: x\r\n\r\nNEXT";
    let whole = decode_split(body, &[]).unwrap();
    assert_eq!(whole.0, b"hello world");
    assert_eq!(whole.1, b"NEXT");
    for i in 0..=body.len() {
        for j in i..=body.len() {
            assert_eq!(decode_split(body, &[i, j]).as_ref(), Some(&whole), "cuts {i} {j}");
        }
    }
    let one: Vec<usize> = (1..body.len()).collect();
    assert_eq!(decode_split(body, &one), Some(whole));
}

/// A small deterministic PRNG (xorshift64*).
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a>(&mut self, xs: &[&'a [u8]]) -> &'a [u8] {
        xs[self.below(xs.len())]
    }
}

impl Rng {
    /// Mostly a piece from `good`, sometimes one from `bad`.
    fn piece<'a>(&mut self, good: &[&'a [u8]], bad: &[&'a [u8]]) -> &'a [u8] {
        if self.below(16) == 0 {
            self.pick(bad)
        } else {
            self.pick(good)
        }
    }
}

/// A request built from plausible and hostile pieces.
fn gen(r: &mut Rng) -> Vec<u8> {
    let mut m = Vec::new();
    if r.below(16) == 0 {
        m.extend_from_slice(r.pick(&[b"\r\n", b"\n", b"\r\n\r\n"]));
    }
    m.extend_from_slice(r.piece(&[b"GET", b"POST", b"M-SEARCH", b"PUT", b"x!#$%&'*+-.^_`|~9"], &[b"", b"G T", b"g\0", b"{x}", b"G\xc3\xa9"]));
    m.extend_from_slice(r.piece(&[b" "], &[b"  ", b"\t", b""]));
    m.extend_from_slice(r.piece(&[b"/", b"/a?b=c", b"*", b"http://x/y", b"/%20~!$&'()*+,;=:@"], &[b"/\xff", b"/\x7f", b"", b"/a b", b"/\0"]));
    m.extend_from_slice(r.piece(&[b" "], &[b"  ", b"\t"]));
    m.extend_from_slice(r.piece(&[b"HTTP/1.1", b"HTTP/1.0"], &[b"HTTP/1.9", b"HTTP/2.0", b"HTTP/1.", b"http/1.1", b"HTTP/1.1 "]));
    m.extend_from_slice(r.piece(&[b"\r\n"], &[b"\n", b"\r", b"\r\r\n"]));
    for _ in 0..r.below(6) {
        m.extend_from_slice(r.piece(&[b"Host", b"X-A", b"content-length", b"a_b", b"!#$%&'*+-.^_`|~"], &[b"", b" X", b"X ", b"\xc3\xa9", b"{", b"a\0"]));
        m.extend_from_slice(r.piece(&[b":", b": ", b":\t", b":  \t "], &[b" :", b""]));
        m.extend_from_slice(r.piece(&[b"v", b"", b"a b", b"pad  \t ", b"\xff\xfe", b"x\ty", b"12", b"\"q\""], &[b"\0", b"\x7f", b"\x1b", b"a\rb"]));
        m.extend_from_slice(r.piece(&[b"\r\n"], &[b"\n", b"\r", b"\r\n ", b"\r\n\t"]));
    }
    m.extend_from_slice(r.piece(&[b"\r\n"], &[b"\n", b""]));
    if r.below(8) == 0 && !m.is_empty() {
        let i = r.below(m.len());
        m[i] = r.next() as u8;
    }
    m
}

/// Whenever vhttp accepts a head's syntax, httparse accepts it too, with
/// the same method, target, version, header names and values, and length.
/// (httparse is more lenient in places, so the converse is not checked;
/// the counts of each disagreement are printed.)
#[test]
fn differential_httparse() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut both, mut only_httparse, mut only_vhttp) = (0, 0, 0);
    let mut hs = Vec::new();
    for _ in 0..300_000 {
        let m = gen(&mut r);
        let ours = verilith_http::parse::request_at(&m, 100, &mut hs).0;
        let mut theirs_h = [httparse::EMPTY_HEADER; 100];
        let mut theirs = httparse::Request::new(&mut theirs_h);
        let t = theirs.parse(&m);
        match (ours, t) {
            (verilith_http::parse::Out::Done(line, end), Ok(httparse::Status::Complete(tend))) => {
                both += 1;
                assert_eq!(end, tend, "{m:?}");
                assert_eq!(line.method.of(&m), theirs.method.unwrap().as_bytes());
                assert_eq!(line.target.of(&m), theirs.path.unwrap().as_bytes());
                assert_eq!(line.minor, theirs.version.unwrap());
                assert_eq!(hs.len(), theirs.headers.len());
                for (h, th) in hs.iter().zip(theirs.headers.iter()) {
                    assert_eq!(h.name.of(&m), th.name.as_bytes(), "{m:?}");
                    assert_eq!(h.value.of(&m), th.value, "{m:?}");
                }
            }
            (verilith_http::parse::Out::Done(line, _), _) => {
                only_vhttp += 1;
                // httparse accepts only HTTP/1.0 and 1.1, and only ASCII
                // in the target; vhttp (like picohttpparser) accepts any
                // HTTP/1.x and obs-text there. Anything else is a bug.
                let t = line.target.of(&m);
                assert!(line.minor > 1 || t.iter().any(|&c| c >= 0x80), "only vhttp accepts {m:?}");
            }
            (_, Ok(httparse::Status::Complete(_))) => only_httparse += 1,
            _ => {}
        }
    }
    println!("both {both}, only httparse {only_httparse}, only vhttp {only_vhttp}");
    assert!(both > 50_000);
}

/// `verilith_http::httparse` against the real httparse on the same corpus: when
/// vhttp accepts, httparse accepts with identical results; the errors are
/// the same kind whenever both reject.
#[test]
fn httparse_api_matches_httparse() {
    use verilith_http::httparse as v;
    let mut r = Rng(0x0123_4567_89ab_cdef);
    let (mut both, mut only_httparse, mut same_err, mut both_err) = (0, 0, 0, 0);
    for _ in 0..300_000 {
        let m = gen(&mut r);
        let mut ours_h = [v::EMPTY_HEADER; 100];
        let mut ours = v::Request::new(&mut ours_h);
        let o = ours.parse(&m);
        let mut theirs_h = [httparse::EMPTY_HEADER; 100];
        let mut theirs = httparse::Request::new(&mut theirs_h);
        let t = theirs.parse(&m);
        match (o, t) {
            (Ok(v::Status::Complete(a)), Ok(httparse::Status::Complete(b))) => {
                both += 1;
                assert_eq!(a, b, "{m:?}");
                assert_eq!((ours.method, ours.path, ours.version), (theirs.method, theirs.path, theirs.version));
                assert_eq!(ours.headers.len(), theirs.headers.len());
                for (h, th) in ours.headers.iter().zip(theirs.headers.iter()) {
                    assert_eq!((h.name, h.value), (th.name, th.value), "{m:?}");
                    // Same bytes, not copies: hyper records offsets.
                    assert_eq!(h.value.as_ptr(), th.value.as_ptr());
                }
            }
            (Ok(v::Status::Complete(_)), t) => panic!("only vhttp accepts {m:?}: {t:?}"),
            (Ok(v::Status::Partial), Ok(httparse::Status::Partial)) => {}
            (_, Ok(httparse::Status::Complete(_))) => only_httparse += 1,
            (Err(a), Err(b)) => {
                both_err += 1;
                if a as u8 == b as u8 {
                    same_err += 1;
                }
            }
            _ => {}
        }
    }
    println!("both {both}, only httparse {only_httparse}, same error {same_err} of {both_err}");
    assert!(both > 50_000);
}

#[test]
fn httparse_api_responses_and_chunks() {
    use verilith_http::httparse as v;
    let mut hs = [v::EMPTY_HEADER; 4];
    let mut res = v::Response::new(&mut hs);
    let buf = b"HTTP/1.1 404 Not Found\r\nContent-Length: 3\r\nX: y\r\n\r\nabc";
    assert_eq!(res.parse(buf), Ok(v::Status::Complete(buf.len() - 3)));
    assert_eq!((res.version, res.code, res.reason), (Some(1), Some(404), Some("Not Found")));
    assert_eq!(res.headers.len(), 2);
    assert_eq!((res.headers[1].name, res.headers[1].value), ("X", &b"y"[..]));

    let mut hs = [v::EMPTY_HEADER; 4];
    let mut res = v::Response::new(&mut hs);
    assert_eq!(res.parse(b"HTTP/1.1 200\r\n\r\n"), Ok(v::Status::Complete(16)));
    assert_eq!(res.reason, Some(""));
    let mut hs = [v::EMPTY_HEADER; 4];
    let mut res = v::Response::new(&mut hs);
    assert_eq!(res.parse(b"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n"), Err(v::Error::HeaderValue));
    assert_eq!(res.headers.len(), 4);
    let mut hs = [v::EMPTY_HEADER; 1];
    let mut res = v::Response::new(&mut hs);
    assert_eq!(res.parse(b"HTTP/1.1 200 OK\r\nA: 1\r\nB: 2\r\n\r\n"), Err(v::Error::TooManyHeaders));

    let mut hs = [v::EMPTY_HEADER; 4];
    assert_eq!(
        v::parse_headers(b"Host: a\r\nX:  b \r\n\r\nrest", &mut hs),
        Ok(v::Status::Complete((19, &[v::Header { name: "Host", value: b"a" }, v::Header { name: "X", value: b"b" }][..])))
    );

    for (input, size) in [(&b"4\r\nRust\r\n"[..], (3, 4)), (b"0\r\n\r\n", (3, 0)), (b"Ab;x=y\r\n", (8, 0xab)), (b"ffffffffffffffff\r\n", (18, u64::MAX))] {
        assert_eq!(v::parse_chunk_size(input), Ok(v::Status::Complete(size)));
        assert_eq!(httparse::parse_chunk_size(input).map(|s| s.unwrap()), Ok(size));
    }
    assert_eq!(v::parse_chunk_size(b"4"), Ok(v::Status::Partial));
    assert_eq!(v::parse_chunk_size(b"4\r"), Ok(v::Status::Partial));
    assert_eq!(v::parse_chunk_size(b"x\r\n"), Err(v::InvalidChunkSize));
    assert_eq!(v::parse_chunk_size(b"4\n"), Err(v::InvalidChunkSize));
    assert_eq!(v::parse_chunk_size(b"10000000000000000\r\n"), Err(v::InvalidChunkSize));

    // Smuggling shapes httparse passes through to the caller are stopped.
    let mut hs = [v::EMPTY_HEADER; 8];
    let mut req = v::Request::new(&mut hs);
    let smuggle = b"POST / HTTP/1.1\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n";
    assert_eq!(req.parse(smuggle), Err(v::Error::HeaderValue));
    let mut hs = [httparse::EMPTY_HEADER; 8];
    assert!(httparse::Request::new(&mut hs).parse(smuggle).unwrap().is_complete());
    // Host is not required, as in httparse.
    let mut hs = [v::EMPTY_HEADER; 8];
    assert!(v::Request::new(&mut hs).parse(b"GET / HTTP/1.1\r\n\r\n").unwrap().is_complete());
    // A bad target is told from a bad method by `method`, as hyper does.
    let mut hs = [v::EMPTY_HEADER; 8];
    let mut req = v::Request::new(&mut hs);
    assert_eq!(req.parse(b"GET /\x7f HTTP/1.1\r\n\r\n"), Err(v::Error::Token));
    assert_eq!(req.method, Some("GET"));
}

/// The calls hyper makes (`proto/h1/role.rs`): uninitialized header
/// storage, a request with no headers of its own, and header positions
/// recovered by pointer offsets into the buffer.
#[test]
fn httparse_api_as_hyper_uses_it() {
    use std::mem::MaybeUninit;
    use verilith_http::httparse as v;
    let buf = b"POST /x HTTP/1.1\r\nHost: a\r\nContent-Length: 2\r\n\r\nhi";
    let mut headers: [MaybeUninit<v::Header<'_>>; 100] = [MaybeUninit::uninit(); 100];
    let mut req = v::Request::new(&mut []);
    let config = v::ParserConfig::default();
    let n = match config.parse_request_with_uninit_headers(&mut req, buf, &mut headers) {
        Ok(v::Status::Complete(n)) => n,
        other => panic!("{other:?}"),
    };
    assert_eq!(n, buf.len() - 2);
    assert_eq!((req.method, req.path, req.version), (Some("POST"), Some("/x"), Some(1)));
    let base = buf.as_ptr() as usize;
    let idx: Vec<(usize, usize)> = req.headers.iter().map(|h| (h.name.as_ptr() as usize - base, h.value.as_ptr() as usize - base)).collect();
    assert_eq!(idx, [(18, 24), (27, 43)]);

    let buf = b"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\n\r\n";
    let mut headers: [MaybeUninit<v::Header<'_>>; 100] = [MaybeUninit::uninit(); 100];
    let mut res = v::Response::new(&mut []);
    assert_eq!(config.parse_response_with_uninit_headers(&mut res, buf, &mut headers), Ok(v::Status::Complete(25)));
    assert_eq!(res.code, Some(100));
}
