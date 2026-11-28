//! A function for verilith-serverless, in Rust: `GET /fn/hello?name=you`
//! answers "Hello, you!"; `POST` echoes the body back, upper-cased.
//!
//!   cargo build --release    (wasm32-unknown-unknown, from .cargo/config.toml)
#![no_std]

/// The guest side of the ABI (`vl` imports; see the crate README).
mod vl {
    #[link(wasm_import_module = "vl")]
    unsafe extern "C" {
        fn req_size(part: i32) -> i32;
        fn req_read(part: i32, off: i32, dst: *mut u8, len: i32) -> i32;
        fn resp_status(code: i32) -> i32;
        fn resp_header(name: *const u8, name_len: i32, value: *const u8, value_len: i32) -> i32;
        fn resp_write(ptr: *const u8, len: i32) -> i32;
    }

    pub const METHOD: i32 = 0;
    pub const TARGET: i32 = 1;
    pub const BODY: i32 = 3;

    /// Reads request part `part` into `buf`; returns the bytes read.
    pub fn read(part: i32, buf: &mut [u8]) -> &[u8] {
        let n = unsafe { req_read(part, 0, buf.as_mut_ptr(), buf.len() as i32) };
        &buf[..n.max(0) as usize]
    }

    pub fn size(part: i32) -> usize {
        unsafe { req_size(part) }.max(0) as usize
    }

    pub fn status(code: u16) -> bool {
        unsafe { resp_status(code as i32) == 0 }
    }

    pub fn header(name: &[u8], value: &[u8]) -> bool {
        unsafe { resp_header(name.as_ptr(), name.len() as i32, value.as_ptr(), value.len() as i32) == 0 }
    }

    pub fn write(b: &[u8]) -> bool {
        unsafe { resp_write(b.as_ptr(), b.len() as i32) == 0 }
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

static mut BUF: [u8; 16384] = [0; 16384];

#[unsafe(no_mangle)]
pub extern "C" fn handle() {
    // SAFETY: one request at a time, and nothing else touches BUF.
    let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
    let (m, rest) = buf.split_at_mut(16);
    let method = vl::read(vl::METHOD, m);
    if method == b"POST" {
        if vl::size(vl::BODY) > rest.len() {
            vl::status(413);
            vl::write(b"too large\n");
            return;
        }
        let n = vl::read(vl::BODY, rest).len();
        rest[..n].make_ascii_uppercase();
        vl::header(b"content-type", b"text/plain");
        vl::write(&rest[..n]);
        return;
    }
    let target = vl::read(vl::TARGET, rest);
    let name = query(target, b"name").unwrap_or(b"world");
    vl::header(b"content-type", b"text/plain; charset=utf-8");
    vl::write(b"Hello, ");
    vl::write(name);
    vl::write(b"!\n");
}

/// The raw value of `key` in the target's query string.
fn query<'a>(target: &'a [u8], key: &[u8]) -> Option<&'a [u8]> {
    let q = &target[target.iter().position(|&c| c == b'?')? + 1..];
    for pair in q.split(|&c| c == b'&') {
        let (k, v) = match pair.iter().position(|&c| c == b'=') {
            Some(i) => (&pair[..i], &pair[i + 1..]),
            None => (pair, &pair[..0]),
        };
        if k == key {
            return Some(v);
        }
    }
    None
}
