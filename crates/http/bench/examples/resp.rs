fn main() {
    let msg: &[u8] = b"HTTP/1.1 200 OK\r\nDate: Mon, 26 Oct 2026 03:38:48 GMT\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: 34567\r\nConnection: keep-alive\r\nCache-Control: private, max-age=0\r\nExpires: -1\r\nServer: nginx/1.27.2\r\nStrict-Transport-Security: max-age=31536000; includeSubDomains\r\nX-Content-Type-Options: nosniff\r\nX-Frame-Options: SAMEORIGIN\r\nVary: Accept-Encoding\r\nSet-Cookie: session=abcdef0123456789; Path=/; Secure; HttpOnly; SameSite=Lax\r\n\r\n";
    let mut hs = Vec::with_capacity(100);
    let mut t = 0;
    for _ in 0..100000 {
        if let verilith_http::parse::Out::Done(_, e) = verilith_http::parse::response_at(std::hint::black_box(msg), 100, &mut hs).0 { t += e + hs.len(); }
    }
    println!("{t}");
}
