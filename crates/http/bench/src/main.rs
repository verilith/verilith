use std::hint::black_box;
use std::os::raw::{c_char, c_int};
use std::time::Instant;

#[repr(C)]
#[derive(Clone, Copy)]
struct PhrHeader {
    name: *const c_char,
    name_len: usize,
    value: *const c_char,
    value_len: usize,
}

unsafe extern "C" {
    fn phr_parse_request(
        buf: *const c_char, len: usize, method: *mut *const c_char, method_len: *mut usize,
        path: *mut *const c_char, path_len: *mut usize, minor: *mut c_int,
        headers: *mut PhrHeader, num: *mut usize, last_len: usize,
    ) -> c_int;
    fn phr_parse_response(
        buf: *const c_char, len: usize, minor: *mut c_int, status: *mut c_int,
        msg: *mut *const c_char, msg_len: *mut usize,
        headers: *mut PhrHeader, num: *mut usize, last_len: usize,
    ) -> c_int;
    fn llwrap_parse(buf: *const c_char, len: usize, response: c_int) -> c_int;
}

/// Runs one parser on one message, unless `BENCH_ONLY` names another
/// parser (`run.sh` runs each parser in a process of its own).
fn bench<F: FnMut() -> usize>(name: &str, msg: &str, mut f: F) {
    if std::env::var("BENCH_ONLY").map_or(false, |o| o != name) {
        return;
    }
    for _ in 0..2000 {
        black_box(f());
    }
    let mut best = f64::MAX;
    for _ in 0..15 {
        let iters = 50000;
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    println!("{msg}\t{name}\t{:.1}", best * 1e9);
}

const SMALL: &[u8] = b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";

/// The request from picohttpparser's bench.c.
const PICO: &[u8] = b"GET /wp-content/uploads/2010/03/hello-kitty-darth-vader-pink.jpg HTTP/1.1\r\n\
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

/// A current browser navigation request.
const BROWSER: &[u8] = b"GET /search?q=formal+verification+http+parser&source=hp&ei=AbCdEfGhIjKlMnOp&iflsig=AL9hbdgAAAAAZ HTTP/1.1\r\n\
Host: www.example.com\r\n\
Connection: keep-alive\r\n\
sec-ch-ua: \"Chromium\";v=\"130\", \"Google Chrome\";v=\"130\", \"Not?A_Brand\";v=\"99\"\r\n\
sec-ch-ua-mobile: ?0\r\n\
sec-ch-ua-platform: \"macOS\"\r\n\
Upgrade-Insecure-Requests: 1\r\n\
User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36\r\n\
Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7\r\n\
Sec-Fetch-Site: same-origin\r\n\
Sec-Fetch-Mode: navigate\r\n\
Sec-Fetch-User: ?1\r\n\
Sec-Fetch-Dest: document\r\n\
Referer: https://www.example.com/\r\n\
Accept-Encoding: gzip, deflate, br, zstd\r\n\
Accept-Language: en-US,en;q=0.9,fr;q=0.8\r\n\
Cookie: AEC=AVYB7cqVxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; NID=518=Zxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; SID=g.a000xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx; __Secure-1PSID=g.a000yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy; 1P_JAR=2026-10-26-03\r\n\
\r\n";

const RESPONSE: &[u8] = b"HTTP/1.1 200 OK\r\n\
Date: Mon, 26 Oct 2026 03:38:48 GMT\r\n\
Content-Type: text/html; charset=utf-8\r\n\
Content-Length: 34567\r\n\
Connection: keep-alive\r\n\
Cache-Control: private, max-age=0\r\n\
Expires: -1\r\n\
Server: nginx/1.27.2\r\n\
Strict-Transport-Security: max-age=31536000; includeSubDomains\r\n\
X-Content-Type-Options: nosniff\r\n\
X-Frame-Options: SAMEORIGIN\r\n\
Vary: Accept-Encoding\r\n\
Set-Cookie: session=abcdef0123456789; Path=/; Secure; HttpOnly; SameSite=Lax\r\n\
\r\n";

fn pico_req(b: &[u8], hs: &mut [PhrHeader; 100]) -> usize {
    let (mut m, mut ml, mut p, mut pl, mut minor, mut n) = (std::ptr::null(), 0, std::ptr::null(), 0, 0, 100);
    let r = unsafe {
        phr_parse_request(b.as_ptr() as _, b.len(), &mut m, &mut ml, &mut p, &mut pl, &mut minor, hs.as_mut_ptr(), &mut n, 0)
    };
    assert!(r > 0);
    black_box(&*hs);
    n
}

fn pico_resp(b: &[u8], hs: &mut [PhrHeader; 100]) -> usize {
    let (mut minor, mut st, mut m, mut ml, mut n) = (0, 0, std::ptr::null(), 0, 100);
    let r = unsafe {
        phr_parse_response(b.as_ptr() as _, b.len(), &mut minor, &mut st, &mut m, &mut ml, hs.as_mut_ptr(), &mut n, 0)
    };
    assert!(r > 0);
    black_box(&*hs);
    n
}

fn main() {
    let mut hs = Vec::with_capacity(100);
    // Header arrays are allocated once and reused, as a server would.
    let mut ph = [PhrHeader { name: std::ptr::null(), name_len: 0, value: std::ptr::null(), value_len: 0 }; 100];
    let mut hh = [httparse::EMPTY_HEADER; 100];
    let mut vh = [verilith_http::httparse::EMPTY_HEADER; 100];
    println!("message\tparser\tns/msg");
    for (name, msg) in [("small", SMALL), ("pico-bench", PICO), ("browser", BROWSER)] {
        println!("# {name}: {} bytes", msg.len());
        bench("vhttp (head + framing)", name, || match verilith_http::parse_request(msg, &mut hs).unwrap() {
            verilith_http::Status::Complete(r) => r.head_len + hs.len(),
            _ => unreachable!(),
        });
        bench("vhttp (head only)", name, || match verilith_http::parse::request_at(msg, 100, &mut hs).0 {
            verilith_http::parse::Out::Done(_, e) => e + hs.len(),
            _ => unreachable!(),
        });
        bench("vhttp::httparse", name, || {
            let mut r = verilith_http::httparse::Request::new(&mut vh);
            match r.parse(msg).unwrap() {
                verilith_http::httparse::Status::Complete(n) => n + r.headers.len(),
                _ => unreachable!(),
            }
        });
        bench("httparse", name, || {
            let mut r = httparse::Request::new(&mut hh);
            match r.parse(msg).unwrap() {
                httparse::Status::Complete(n) => n + r.headers.len(),
                _ => unreachable!(),
            }
        });
        bench("picohttpparser", name, || pico_req(msg, &mut ph));
        bench("llhttp", name, || {
            let k = unsafe { llwrap_parse(msg.as_ptr() as _, msg.len(), 0) };
            assert!(k > 0);
            k as usize
        });
    }
    let name = "response";
    println!("# response: {} bytes", RESPONSE.len());
    bench("vhttp (head + framing)", name, || match verilith_http::parse_response(RESPONSE, false, false, &mut hs).unwrap() {
        verilith_http::Status::Complete(r) => r.head_len + hs.len(),
        _ => unreachable!(),
    });
    bench("vhttp (head only)", name, || match verilith_http::parse::response_at(RESPONSE, 100, &mut hs).0 {
        verilith_http::parse::Out::Done(_, e) => e + hs.len(),
        _ => unreachable!(),
    });
    bench("vhttp::httparse", name, || {
        let mut r = verilith_http::httparse::Response::new(&mut vh);
        match r.parse(RESPONSE).unwrap() {
            verilith_http::httparse::Status::Complete(n) => n + r.headers.len(),
            _ => unreachable!(),
        }
    });
    bench("httparse", name, || {
        let mut r = httparse::Response::new(&mut hh);
        match r.parse(RESPONSE).unwrap() {
            httparse::Status::Complete(n) => n + r.headers.len(),
            _ => unreachable!(),
        }
    });
    bench("picohttpparser", name, || pico_resp(RESPONSE, &mut ph));
    bench("llhttp", name, || {
        let k = unsafe { llwrap_parse(RESPONSE.as_ptr() as _, RESPONSE.len(), 1) };
        assert!(k > 0);
        k as usize
    });
}
