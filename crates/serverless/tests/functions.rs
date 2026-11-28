//! Guests that use the ABI as intended, and guests that try to get out of
//! it: out-of-bounds pointers, response splitting, framing fields, state
//! carried between requests, memory exhaustion, endless loops.
use std::io::{Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use verilith_serverless::abi::{Limits, Req};
use verilith_serverless::host::{Func, Outcome};
use verilith_serverless::{load, Functions, LoadError, Options};
use verilith_wasm::ast::Trap;

const IMPORTS: &str = r#"
  (import "vl" "req_size" (func $size (param i32) (result i32)))
  (import "vl" "req_read" (func $read (param i32 i32 i32 i32) (result i32)))
  (import "vl" "resp_status" (func $status (param i32) (result i32)))
  (import "vl" "resp_header" (func $header (param i32 i32 i32 i32) (result i32)))
  (import "vl" "resp_write" (func $write (param i32 i32) (result i32)))
"#;

/// A module with the ABI imports, then `body`.
fn guest(body: &str) -> Vec<u8> {
    wat::parse_str(format!("(module {IMPORTS} {body})")).unwrap()
}

/// A guest whose `handle` runs `calls`, a sequence of `(call ...)`
/// expressions returning i32, and writes the results as 4-byte
/// little-endian words: the guest's view of what each call returned.
fn probe(calls: &[&str], data: &str, mem: &str) -> Vec<u8> {
    let mut body = String::new();
    for (i, c) in calls.iter().enumerate() {
        body += &format!("(i32.store (i32.const {}) {c})\n", 60000 + 4 * i);
    }
    guest(&format!(
        "(memory {mem}) {data}
         (func (export \"handle\")
           {body}
           (drop (call $write (i32.const 60000) (i32.const {}))))",
        4 * calls.len()
    ))
}

fn words(b: &[u8]) -> Vec<i32> {
    b.chunks(4).map(|c| i32::from_le_bytes(c.try_into().unwrap())).collect()
}

fn lim() -> Limits {
    Limits { max_body: 1 << 16, max_fields: 4, max_field_bytes: 256 }
}

fn req<'a>(body: &'a [u8]) -> Req<'a> {
    Req { method: b"POST", target: b"/fn/x/y?z=1", fields: b"host: example\r\n", body }
}

struct Reply {
    status: u16,
    fields: Vec<(Vec<u8>, Vec<u8>)>,
    body: Vec<u8>,
}

/// Serves one request on `f`.
fn call(f: Func, q: Req) -> (Func, Result<Reply, Option<Trap>>) {
    let (f, out, _) = f.serve(q, lim());
    let r = match out {
        Outcome::Done(rep) => {
            let fields = (0..rep.n_fields()).map(|i| {
                let (n, v) = rep.field(i);
                (n.to_vec(), v.to_vec())
            }).collect();
            Ok(Reply { status: rep.status(), fields, body: rep.body().to_vec() })
        }
        Outcome::Trap(t) => Err(Some(t)),
        Outcome::Fault => Err(None),
    };
    (f, r)
}

fn opts() -> Options {
    Options { fuel: 1_000_000, max_memory: 1 << 20, ..Options::default() }
}

const ECHO: &str = r#"
  (memory 1)
  (data (i32.const 0) "content-type")
  (data (i32.const 16) "text/plain")
  (data (i32.const 32) " ")
  (func (export "handle") (local $n i32)
    (drop (call $header (i32.const 0) (i32.const 12) (i32.const 16) (i32.const 10)))
    (local.set $n (call $read (i32.const 0) (i32.const 0) (i32.const 1024) (i32.const 4096)))
    (drop (call $write (i32.const 1024) (local.get $n)))
    (drop (call $write (i32.const 32) (i32.const 1)))
    (local.set $n (call $read (i32.const 1) (i32.const 0) (i32.const 1024) (i32.const 4096)))
    (drop (call $write (i32.const 1024) (local.get $n)))
    (drop (call $write (i32.const 32) (i32.const 1)))
    (local.set $n (call $read (i32.const 3) (i32.const 0) (i32.const 8192) (i32.const 40000)))
    (drop (call $write (i32.const 8192) (local.get $n))))
"#;

#[test]
fn echo() {
    let f = load(&guest(ECHO), &opts()).unwrap();
    let (f, r) = call(f, req(b"hello"));
    let r = r.unwrap();
    assert_eq!(r.status, 200);
    assert_eq!(r.fields, vec![(b"content-type".to_vec(), b"text/plain".to_vec())]);
    assert_eq!(r.body, b"POST /fn/x/y?z=1 hello");
    // The next request gets a new reply, not this one's fields and body.
    let (_, r) = call(f, req(b"again"));
    let r = r.unwrap();
    assert_eq!(r.fields.len(), 1);
    assert_eq!(r.body, b"POST /fn/x/y?z=1 again");
}

#[test]
fn reads_in_pieces() {
    // req_size, then a read from an offset, a read that is cut short at the
    // end of the part, a read at the end, and parts that do not exist.
    let g = probe(&[
        "(call $size (i32.const 3))",
        "(call $size (i32.const 2))",
        "(call $read (i32.const 3) (i32.const 2) (i32.const 0) (i32.const 3))",
        "(call $read (i32.const 3) (i32.const 8) (i32.const 0) (i32.const 100))",
        "(call $read (i32.const 3) (i32.const 10) (i32.const 0) (i32.const 100))",
        "(call $read (i32.const 3) (i32.const 11) (i32.const 0) (i32.const 1))",
        "(call $size (i32.const 4))",
        "(call $size (i32.const -1))",
        "(call $read (i32.const 4) (i32.const 0) (i32.const 0) (i32.const 1))",
    ], "", "1");
    let f = load(&g, &opts()).unwrap();
    let (_, r) = call(f, req(b"0123456789"));
    assert_eq!(words(&r.unwrap().body), vec![10, 15, 3, 2, 0, -1, -1, -1, -1]);
}

#[test]
fn out_of_bounds_pointers() {
    // One page: 65536 bytes. Every range that does not fit is refused,
    // including ones whose end wraps around 2^32.
    let g = probe(&[
        "(call $read (i32.const 3) (i32.const 0) (i32.const 65535) (i32.const 2))",
        "(call $read (i32.const 3) (i32.const 0) (i32.const 65536) (i32.const 0))",
        "(call $read (i32.const 3) (i32.const 0) (i32.const 65537) (i32.const 0))",
        "(call $read (i32.const 3) (i32.const 0) (i32.const -1) (i32.const 2))",
        "(call $read (i32.const 3) (i32.const 0) (i32.const 16) (i32.const -16))",
        "(call $write (i32.const 65530) (i32.const 7))",
        "(call $write (i32.const -1) (i32.const 1))",
        "(call $write (i32.const 1) (i32.const -1))",
        "(call $header (i32.const -4) (i32.const 8) (i32.const 0) (i32.const 1))",
        "(call $header (i32.const 0) (i32.const 1) (i32.const 65535) (i32.const 2))",
        "(call $read (i32.const 3) (i32.const 0) (i32.const 65535) (i32.const 1))",
    ], "", "1");
    let f = load(&g, &opts()).unwrap();
    let (_, r) = call(f, req(b"ab"));
    let w = words(&r.unwrap().body);
    assert_eq!(w, vec![-1, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1]);
}

#[test]
fn response_splitting_and_framing() {
    let data = r#"
      (data (i32.const 0) "x-ok")
      (data (i32.const 8) "fine")
      (data (i32.const 16) "a\0d\0aSet-Cookie: s=1")
      (data (i32.const 48) "Content-Length")
      (data (i32.const 64) "transfer_encoding")
      (data (i32.const 96) "Connection")
      (data (i32.const 112) "x y")
      (data (i32.const 120) "99")
      (data (i32.const 128) " lead")
      (data (i32.const 136) "nul\00")
      (data (i32.const 144) "TE")
    "#;
    let g = probe(&[
        "(call $header (i32.const 0) (i32.const 4) (i32.const 8) (i32.const 4))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 16) (i32.const 20))",
        "(call $header (i32.const 48) (i32.const 14) (i32.const 120) (i32.const 2))",
        "(call $header (i32.const 64) (i32.const 17) (i32.const 8) (i32.const 4))",
        "(call $header (i32.const 96) (i32.const 10) (i32.const 8) (i32.const 4))",
        "(call $header (i32.const 112) (i32.const 3) (i32.const 8) (i32.const 4))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 128) (i32.const 5))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 136) (i32.const 4))",
        "(call $header (i32.const 144) (i32.const 2) (i32.const 8) (i32.const 4))",
        "(call $header (i32.const 0) (i32.const 0) (i32.const 8) (i32.const 4))",
        "(call $status (i32.const 199))",
        "(call $status (i32.const 600))",
        "(call $status (i32.const 101))",
        "(call $status (i32.const 418))",
    ], data, "1");
    let f = load(&g, &opts()).unwrap();
    let (_, r) = call(f, req(b""));
    let r = r.unwrap();
    assert_eq!(words(&r.body), vec![0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0]);
    assert_eq!(r.status, 418);
    assert_eq!(r.fields, vec![(b"x-ok".to_vec(), b"fine".to_vec())]);
}

#[test]
fn reply_limits() {
    // lim(): 4 fields, 256 field bytes, 64 KiB body.
    let g = probe(&[
        "(call $header (i32.const 0) (i32.const 4) (i32.const 0) (i32.const 200))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 0) (i32.const 60))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 0) (i32.const 1))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 0) (i32.const 1))",
        "(call $header (i32.const 0) (i32.const 4) (i32.const 0) (i32.const 1))",
        "(call $write (i32.const 0) (i32.const 65536))",
        "(call $write (i32.const 0) (i32.const 65500))",
        "(call $write (i32.const 0) (i32.const 36))",
        "(call $write (i32.const 0) (i32.const 1))",
    ], r#"(data (i32.const 0) "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz")"#, "1");
    let f = load(&g, &opts()).unwrap();
    let (_, r) = call(f, req(b""));
    let r = r.unwrap();
    // The results are written after the body is full, so they do not fit:
    // the body is the 65536 bytes the guest wrote.
    assert_eq!(r.body.len(), 65536);
    assert_eq!(r.fields.len(), 4);
}

const COUNTER: &str = r#"
  (memory 1 4)
  (global $g (mut i32) (i32.const 0))
  (func (export "handle")
    (global.set $g (i32.add (global.get $g) (i32.const 1)))
    (i32.store (i32.const 100) (i32.add (i32.load (i32.const 100)) (i32.const 1)))
    (i32.store8 (i32.const 200) (i32.add (i32.const 48) (global.get $g)))
    (i32.store8 (i32.const 201) (i32.add (i32.const 48) (i32.load (i32.const 100))))
    (i32.store8 (i32.const 202) (i32.add (i32.const 48) (memory.size)))
    (drop (memory.grow (i32.const 1)))
    (drop (call $write (i32.const 200) (i32.const 3))))
"#;

#[test]
fn no_state_between_requests() {
    let mut f = load(&guest(COUNTER), &opts()).unwrap();
    for _ in 0..5 {
        let (g, r) = call(f, req(b""));
        f = g;
        // Global and memory counters are 1, and memory is back to one page.
        assert_eq!(r.unwrap().body, b"111");
    }
}

/// Writes in several 4 KiB chunks of a memory that does not grow: a
/// store across a chunk boundary, the last byte, `memory.fill`,
/// `memory.copy` and the host's `req_read`. Each request reports what it
/// found before writing, so a chunk not put back shows on the next one.
const SCATTER: &str = r#"
  (memory 2)
  (data (i32.const 8000) "abcd")
  (func (export "handle")
    (i32.store8 (i32.const 60000) (i32.add (i32.const 48) (i32.load8_u (i32.const 19999))))
    (i32.store8 (i32.const 60001) (i32.add (i32.const 48) (i32.load8_u (i32.const 40003))))
    (i32.store8 (i32.const 60002) (i32.add (i32.const 48) (i32.load8_u (i32.const 100000))))
    (i32.store (i32.const 4094) (i32.add (i32.load (i32.const 4094)) (i32.const 0x01010101)))
    (i32.store8 (i32.const 60003) (i32.add (i32.const 48) (i32.load8_u (i32.const 4097))))
    (i32.store8 (i32.const 131071) (i32.add (i32.load8_u (i32.const 131071)) (i32.const 1)))
    (i32.store8 (i32.const 60004) (i32.add (i32.const 48) (i32.load8_u (i32.const 131071))))
    (memory.fill (i32.const 12000) (i32.const 1) (i32.const 8000))
    (memory.copy (i32.const 40000) (i32.const 8000) (i32.const 4))
    (drop (call $read (i32.const 3) (i32.const 0) (i32.const 100000) (i32.const 16)))
    (drop (call $write (i32.const 60000) (i32.const 5))))
"#;

#[test]
fn no_state_between_requests_in_any_chunk() {
    let mut f = load(&guest(SCATTER), &opts()).unwrap();
    for _ in 0..4 {
        let (g, r) = call(f, req(b"\x05"));
        f = g;
        assert_eq!(r.unwrap().body, b"00011");
    }
}

#[test]
fn state_from_the_start_function_is_kept() {
    // What instantiation leaves is the snapshot every request starts from.
    let g = guest(r#"
      (memory 1)
      (global $g (mut i32) (i32.const 0))
      (func $init (global.set $g (i32.const 7)) (i32.store8 (i32.const 0) (i32.const 65)))
      (start $init)
      (func (export "handle")
        (i32.store8 (i32.const 1) (i32.add (i32.const 48) (global.get $g)))
        (global.set $g (i32.const 0))
        (i32.store8 (i32.const 0) (i32.const 66))
        (drop (call $write (i32.const 0) (i32.const 2))))
    "#);
    let mut f = load(&g, &opts()).unwrap();
    for _ in 0..3 {
        let (g, r) = call(f, req(b""));
        f = g;
        assert_eq!(r.unwrap().body, b"B7");
    }
}

#[test]
fn memory_cap() {
    // Grow one page at a time until refused: the cap is 1 MiB = 16 pages.
    let g = guest(r#"
      (memory 1)
      (func (export "handle") (local $n i32)
        (block $done (loop $l
          (br_if $done (i32.eq (memory.grow (i32.const 1)) (i32.const -1)))
          (local.set $n (i32.add (local.get $n) (i32.const 1)))
          (br $l)))
        (i32.store (i32.const 0) (memory.size))
        (drop (call $write (i32.const 0) (i32.const 4))))
    "#);
    let mut f = load(&g, &opts()).unwrap();
    for _ in 0..3 {
        let (g, r) = call(f, req(b""));
        f = g;
        assert_eq!(words(&r.unwrap().body), vec![16]);
    }
    // A module whose memory starts above the cap is refused.
    let big = guest(r#"(memory 17) (func (export "handle"))"#);
    assert!(load(&big, &opts()).is_err());
}

#[test]
fn endless_loop_runs_out_of_fuel() {
    let g = guest(r#"(func (export "handle") (loop $l (br $l)))"#);
    let f = load(&g, &opts()).unwrap();
    let (f, r) = call(f, req(b""));
    assert!(matches!(r, Err(Some(Trap::Exhausted))));
    // Each request gets the full fuel again.
    let (_, r) = call(f, req(b""));
    assert!(matches!(r, Err(Some(Trap::Exhausted))));
}

#[test]
fn trap_then_recover() {
    // A guest that traps after writing: its partial reply is dropped, and
    // the next request starts clean.
    let g = guest(r#"
      (memory 1)
      (global $n (mut i32) (i32.const 0))
      (func (export "handle")
        (drop (call $write (i32.const 0) (i32.const 1)))
        (i32.store8 (i32.const 0) (i32.const 88))
        (unreachable))
    "#);
    let f = load(&g, &opts()).unwrap();
    let (f, r) = call(f, req(b""));
    assert!(matches!(r, Err(Some(Trap::Unreachable))));
    let (_, r) = call(f, req(b""));
    assert!(matches!(r, Err(Some(Trap::Unreachable))));
}

#[test]
fn refused_modules() {
    let bad_import = wat::parse_str(r#"(module (import "env" "open" (func)) (func (export "handle")))"#).unwrap();
    assert!(matches!(load(&bad_import, &opts()), Err(LoadError::Import(_))));
    let bad_type = wat::parse_str(r#"(module (import "vl" "resp_status" (func (param i64) (result i32))) (func (export "handle")))"#).unwrap();
    assert!(load(&bad_type, &opts()).is_err());
    let mem_import = wat::parse_str(r#"(module (import "vl" "mem" (memory 1)) (func (export "handle")))"#).unwrap();
    assert!(matches!(load(&mem_import, &opts()), Err(LoadError::Import(_))));
    let no_entry = guest(r#"(func (export "run"))"#);
    assert!(matches!(load(&no_entry, &opts()), Err(LoadError::NoEntry)));
    let entry_type = guest(r#"(func (export "handle") (param i32))"#);
    assert!(matches!(load(&entry_type, &opts()), Err(LoadError::NoEntry)));
    // A start function that calls the ABI traps, so instantiation fails.
    let start = guest(r#"(func $s (drop (call $status (i32.const 200)))) (start $s) (func (export "handle"))"#);
    assert!(load(&start, &opts()).is_err());
    let endless_start = guest(r#"(func $s (loop $l (br $l))) (start $s) (func (export "handle"))"#);
    assert!(load(&endless_start, &opts()).is_err());
    assert!(load(b"\0asm\x01\0\0\0garbage", &opts()).is_err());
}

// ---------------------------------------------------------------------------
// Through the server
// ---------------------------------------------------------------------------

fn server() -> u16 {
    static P: OnceLock<u16> = OnceLock::new();
    *P.get_or_init(|| {
        let port = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let mut fns = Functions::new();
        fns.add("echo", &guest(ECHO), opts()).unwrap();
        fns.add("counter", &guest(COUNTER), opts()).unwrap();
        fns.add("spin", &guest(r#"(func (export "handle") (loop $l (br $l)))"#), opts()).unwrap();
        let split = probe(&["(call $header (i32.const 0) (i32.const 4) (i32.const 16) (i32.const 20))"],
            r#"(data (i32.const 0) "x-ok") (data (i32.const 16) "a\0d\0aSet-Cookie: s=1")"#, "1");
        fns.add("split", &split, opts()).unwrap();
        let cfg = verilith_server::Config { port, threads: 2, pin: false, ..verilith_server::Config::default() };
        std::thread::spawn(move || verilith_server::serve(cfg, Arc::new(fns)));
        for _ in 0..200 {
            if TcpStream::connect(("127.0.0.1", port)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        port
    })
}

fn exchange(req: &[u8]) -> String {
    let mut s = TcpStream::connect(("127.0.0.1", server())).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    s.write_all(req).unwrap();
    s.shutdown(Shutdown::Write).unwrap();
    let mut out = Vec::new();
    s.read_to_end(&mut out).unwrap();
    String::from_utf8_lossy(&out).into_owned()
}

#[test]
fn http_echo() {
    let r = exchange(b"POST /fn/echo/a?b HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello");
    assert!(r.starts_with("HTTP/1.1 200 OK\r\n"), "{r}");
    assert!(r.contains("\r\ncontent-type: text/plain\r\n"), "{r}");
    assert!(r.ends_with("\r\n\r\nPOST /fn/echo/a?b hello"), "{r}");
}

#[test]
fn http_pipelined_requests_are_isolated() {
    let one = "GET /fn/counter HTTP/1.1\r\nHost: x\r\n\r\n";
    let r = exchange(one.repeat(4).as_bytes());
    assert_eq!(r.matches("HTTP/1.1 200").count(), 4, "{r}");
    assert_eq!(r.matches("\r\n\r\n111").count(), 4, "{r}");
}

#[test]
fn http_errors() {
    let r = exchange(b"GET /fn/spin HTTP/1.1\r\nHost: x\r\n\r\n");
    assert!(r.starts_with("HTTP/1.1 503"), "{r}");
    let r = exchange(b"GET /fn/nope HTTP/1.1\r\nHost: x\r\n\r\n");
    assert!(r.starts_with("HTTP/1.1 404"), "{r}");
    let r = exchange(b"GET /other HTTP/1.1\r\nHost: x\r\n\r\n");
    assert!(r.starts_with("HTTP/1.1 404"), "{r}");
    let r = exchange(b"GET /fn/split HTTP/1.1\r\nHost: x\r\n\r\n");
    assert!(r.starts_with("HTTP/1.1 200"), "{r}");
    assert!(!r.contains("Set-Cookie"), "{r}");
}
