//! Request smuggling and parser-disagreement shapes. Each is a message some
//! widely used parser accepted with framing different from another's.
//! vhttp must reject every one of them (or, where noted, accept it with
//! the one unambiguous framing).
use verilith_http::{parse_request, parse_response, Body, ChunkedDecoder, Error, Status};

fn req(s: &str) -> Result<Body, Error> {
    let mut hs = Vec::new();
    match parse_request(s.as_bytes(), &mut hs)? {
        Status::Complete(r) => Ok(r.body),
        Status::Partial => panic!("partial: {s:?}"),
    }
}

fn rejected(s: &str) {
    assert!(req(s).is_err(), "accepted: {s:?}");
}

#[test]
fn cl_te_conflicts() {
    // CL.TE / TE.CL: both headers present.
    rejected("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 6\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nG");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\nContent-Length: 4\r\n\r\n");
    // Header names are case-insensitive.
    rejected("POST / HTTP/1.1\r\nHost: a\r\ncontent-length: 6\r\nTRANSFER-ENCODING: chunked\r\n\r\n");
}

#[test]
fn obfuscated_transfer_encoding() {
    // TE.TE: the variants one hop ignores and the next honours.
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding : chunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: xchunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, identity\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: x\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, chunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding:\x0bchunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: \"chunked\"\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked;q=1\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\n Transfer-Encoding: chunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nX: y\r\n Transfer-Encoding: chunked\r\n\r\n"); // obs-fold
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding\r\n : chunked\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chu\r\n nked\r\n\r\n");
    // Look-alike names, which CGI-style software reads as the real ones.
    assert_eq!(
        req("POST / HTTP/1.1\r\nHost: a\r\nTransfer_Encoding: chunked\r\nContent-Length: 1\r\n\r\nx"),
        Err(Error::TransferEncoding)
    );
    assert_eq!(req("POST / HTTP/1.1\r\nHost: a\r\nContent_Length: 1\r\n\r\nx"), Err(Error::ContentLength));
    // Other names with `_` are fine.
    assert_eq!(req("POST / HTTP/1.1\r\nHost: a\r\nX_Y: 1\r\n\r\n"), Ok(Body::Empty));
    // TE in HTTP/1.0.
    rejected("POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n");
    // Only `chunked` last is accepted in a request.
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: \r\n\r\n");
}

#[test]
fn accepted_transfer_encodings() {
    let te = |v: &str| req(&format!("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: {v}\r\n\r\n"));
    assert_eq!(te("chunked"), Ok(Body::Chunked));
    assert_eq!(te("CHUNKED"), Ok(Body::Chunked));
    assert_eq!(te("gzip, chunked"), Ok(Body::Chunked));
    assert_eq!(te(" , gzip ,, chunked , "), Ok(Body::Chunked));
    // One Transfer-Encoding line only: parsers that read only the first
    // or only the last would disagree.
    assert_eq!(
        req("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\nTransfer-Encoding: chunked\r\n\r\n"),
        Err(Error::TransferEncoding)
    );
}

#[test]
fn content_length() {
    let cl = |v: &str| req(&format!("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: {v}\r\n\r\n"));
    assert_eq!(cl("0"), Ok(Body::Length(0)));
    assert_eq!(cl("42"), Ok(Body::Length(42)));
    assert_eq!(cl("007"), Ok(Body::Length(7)));
    assert_eq!(cl("  13  "), Ok(Body::Length(13)));
    assert_eq!(cl("9999999999999999999"), Ok(Body::Length(9999999999999999999)));
    for bad in ["", "+5", "-1", "5 5", "5,5", "5, 5", "0x10", "1e3", "5\t5", "18446744073709551616", "99999999999999999999", "٣"] {
        assert_eq!(cl(bad), Err(Error::ContentLength), "{bad:?}");
    }
    // Repeated lines must agree on the number (RFC 9112 §6.3).
    assert_eq!(
        req("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\ncontent-length: 05\r\n\r\n"),
        Ok(Body::Length(5))
    );
    assert_eq!(
        req("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\n"),
        Err(Error::ContentLength)
    );
    rejected("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\nContent-Length: 5\r\nContent-Length: x\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\n");
    rejected("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 5\r\ncontent-length: 6\r\n\r\n");
    // Whitespace before the colon.
    rejected("POST / HTTP/1.1\r\nHost: a\r\nContent-Length : 5\r\n\r\n");
}

#[test]
fn host() {
    assert_eq!(req("GET / HTTP/1.1\r\nHost: a\r\n\r\n"), Ok(Body::Empty));
    assert_eq!(req("GET / HTTP/1.0\r\n\r\n"), Ok(Body::Empty));
    assert_eq!(req("GET / HTTP/1.1\r\n\r\n"), Err(Error::Host));
    assert_eq!(req("GET / HTTP/1.1\r\nHost: a\r\nHost: b\r\n\r\n"), Err(Error::Host));
    assert_eq!(req("GET / HTTP/1.0\r\nHost: a\r\nhost: a\r\n\r\n"), Err(Error::Host));
}

#[test]
fn line_endings() {
    // Bare LF and bare CR, in every position.
    rejected("GET / HTTP/1.1\nHost: a\r\n\r\n");
    rejected("GET / HTTP/1.1\r\nHost: a\n\r\n");
    rejected("GET / HTTP/1.1\r\nHost: a\r\n\n");
    rejected("GET / HTTP/1.1\r\nHost: a\rX: b\r\n\r\n");
    rejected("GET / HTTP/1.1\r\nHost: a\r\nX: b\rc\r\n\r\n");
    rejected("GET / HTTP/1.1\r\r\nHost: a\r\n\r\n");
    // NUL and other controls.
    rejected("GET / HTTP/1.1\r\nHost: a\r\nX: a\0b\r\n\r\n");
    rejected("GET / HTTP/1.1\r\nHost: a\r\nX: a\x7fb\r\n\r\n");
    rejected("GET /\0 HTTP/1.1\r\nHost: a\r\n\r\n");
    // Request line shape.
    rejected("GET  / HTTP/1.1\r\nHost: a\r\n\r\n");
    rejected("GET / HTTP/1.1 \r\nHost: a\r\n\r\n");
    rejected("GET\t/ HTTP/1.1\r\nHost: a\r\n\r\n");
    rejected("GET / HTTP/2.0\r\nHost: a\r\n\r\n");
    rejected("GET / http/1.1\r\nHost: a\r\n\r\n");
    rejected("GET / HTTP/1.10\r\nHost: a\r\n\r\n");
    rejected("GET /\r\n\r\n"); // HTTP/0.9
    // Leading empty lines are skipped (RFC 9112 §2.2).
    assert_eq!(req("\r\n\r\nGET / HTTP/1.1\r\nHost: a\r\n\r\n"), Ok(Body::Empty));
    rejected("\nGET / HTTP/1.1\r\nHost: a\r\n\r\n");
}

fn chunked(body: &[u8]) -> Result<Vec<u8>, Error> {
    let mut buf = body.to_vec();
    let mut d = ChunkedDecoder::new();
    match d.decode(&mut buf)? {
        verilith_http::Chunked::Done { out, .. } => Ok(buf[..out].to_vec()),
        verilith_http::Chunked::More { .. } => Err(Error::Chunked),
    }
}

#[test]
fn chunk_framing() {
    assert_eq!(chunked(b"5\r\nhello\r\n0\r\n\r\n").unwrap(), b"hello");
    assert_eq!(chunked(b"5;a=b;c=\"d\\\"e\"\r\nhello\r\n0\r\n\r\n").unwrap(), b"hello");
    assert_eq!(chunked(b"5 ; a = b\r\nhello\r\n0\r\nX: y\r\n\r\n").unwrap(), b"hello");
    for bad in [
        &b"5\nhello\r\n0\r\n\r\n"[..],          // bare LF after size
        b"5\r\nhello\n0\r\n\r\n",                 // bare LF after data
        b"5\r\nhelloXX0\r\n\r\n",                 // data longer than size
        b"5;a\nb\r\nhello\r\n0\r\n\r\n",          // LF inside an extension (TERM.SRV / funky chunks)
        b"5;a=\"b\nc\"\r\nhello\r\n0\r\n\r\n",    // LF inside a quoted extension
        b"5;a\rb\r\nhello\r\n0\r\n\r\n",          // bare CR inside an extension
        b"5 \r\nhello\r\n0\r\n\r\n",              // BWS not followed by ';'
        b"-5\r\nhello\r\n0\r\n\r\n",
        b"0x5\r\nhello\r\n0\r\n\r\n",
        b"+5\r\nhello\r\n0\r\n\r\n",
        b"\r\n5\r\nhello\r\n0\r\n\r\n",
        b"10000000000000000\r\n",                 // 2^64: overflows
        b"5\r\nhello\r\n0\r\n\n",                 // bare LF at the end
        b"5\r\nhello\r\n0\r\nX: y\n\r\n",
        b"5\r\nhello\r\n0\r\nX : y\r\n\r\n",
    ] {
        assert!(chunked(bad).is_err(), "accepted {:?}", String::from_utf8_lossy(bad));
    }
    // The largest chunk size is fine (the decoder just wants more data).
    let mut buf = b"ffffffffffffffff\r\nab".to_vec();
    assert!(matches!(ChunkedDecoder::new().decode(&mut buf), Ok(verilith_http::Chunked::More { out: 2 })));
}

#[test]
fn response_framing() {
    let resp = |s: &str, head: bool| {
        let mut hs = Vec::new();
        match parse_response(s.as_bytes(), head, false, &mut hs)? {
            Status::Complete(r) => Ok(r.body),
            Status::Partial => panic!(),
        }
    };
    assert_eq!(resp("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n", false), Ok(Body::Length(5)));
    assert_eq!(resp("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n", true), Ok(Body::Empty));
    assert_eq!(resp("HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n", false), Ok(Body::Empty));
    assert_eq!(resp("HTTP/1.1 200 OK\r\n\r\n", false), Ok(Body::Close));
    assert_eq!(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n", false), Ok(Body::Close));
    assert_eq!(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n", false), Ok(Body::Chunked));
    assert_eq!(
        resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n", false),
        Err(Error::ContentLengthAndTransferEncoding)
    );
    assert_eq!(
        resp("HTTP/1.1 304 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n", false),
        Err(Error::ContentLengthAndTransferEncoding)
    );
    assert_eq!(resp("HTTP/1.1 200X\r\n\r\n", false), Err(Error::Status));
    assert_eq!(resp("HTTP/1.1 200\r\n\r\n", false), Ok(Body::Close));
}

#[test]
fn error_reasons() {
    let e = |s: &str| req(s).unwrap_err();
    assert_eq!(e("GE(T / HTTP/1.1\r\nHost: a\r\n\r\n"), Error::Method);
    assert_eq!(e("GET  / HTTP/1.1\r\nHost: a\r\n\r\n"), Error::Target);
    assert_eq!(e("GET /\0 HTTP/1.1\r\nHost: a\r\n\r\n"), Error::Target);
    assert_eq!(e("GET / HTTP/2.0\r\nHost: a\r\n\r\n"), Error::Version);
    assert_eq!(e("GET / HTTP/1.1\nHost: a\r\n\r\n"), Error::NewLine);
    assert_eq!(e("GET / HTTP/1.1\r\nHost: a\n\r\n"), Error::NewLine);
    assert_eq!(e("GET / HTTP/1.1\r\nHost: a\rX: b\r\n\r\n"), Error::NewLine);
    assert_eq!(e("GET / HTTP/1.1\r\nHost : a\r\n\r\n"), Error::HeaderName);
    assert_eq!(e("GET / HTTP/1.1\r\nHost: a\r\n b\r\n\r\n"), Error::HeaderName);
    assert_eq!(e("GET / HTTP/1.1\r\nHost: a\x7f\r\n\r\n"), Error::HeaderValue);
    assert_eq!(e("POST / HTTP/1.1\r\nHost: a\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n"), Error::ContentLengthAndTransferEncoding);
    assert_eq!(e("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: gzip\r\n\r\n"), Error::TransferEncoding);
    assert_eq!(e("POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked, gzip\r\n\r\n"), Error::TransferEncoding);
    assert_eq!(e("POST / HTTP/1.0\r\nTransfer-Encoding: chunked\r\n\r\n"), Error::TransferEncodingHttp10);
    let many = format!("GET / HTTP/1.1\r\nHost: a\r\n{}\r\n", "X: y\r\n".repeat(100));
    assert_eq!(e(&many), Error::TooManyHeaders);
    assert!(Error::Host.is_framing() && !Error::NewLine.is_framing());
}
