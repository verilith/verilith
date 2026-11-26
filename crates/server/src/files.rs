//! Static files from a directory (DESIGN.md, "Static files").
//!
//! A request path becomes a file path only through `path::resolve_exec`
//! (verified: no component is empty, `.`, `..`, or holds `/`, `\` or NUL),
//! and the file is opened with `sys::open_beneath` (`openat2` with
//! `RESOLVE_BENEATH`: no symlink leads out of the root). Ranges go through
//! `range::parse_range` (verified: the bytes served lie inside the file).
//!
//! Each worker keeps the files it has served in memory, keyed by request
//! path, and checks each against the disk (open, `fstat`) at most once a
//! second: a hit costs a hash lookup and no system call, as with nginx's
//! `open_file_cache` plus the page cache, but without the read.
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::os::unix::fs::MetadataExt;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::h1::{Fields, StaticBody};
use crate::range::{parse_range, Rng};
use crate::{Field, Request, Response};

/// A directory served as static files.
pub struct Files {
    root: std::fs::File,
    id: usize,
    /// Files longer than this are read for each request, not kept.
    pub max_cached: usize,
    /// The bytes of files each worker keeps, at most.
    pub cache_budget: usize,
}

struct Entry {
    rel: Vec<u8>,
    body: StaticBody,
    fields: Fields,
    etag: Vec<u8>,
    last_modified: [u8; 29],
    ino: u64,
    dev: u64,
    mtime: (i64, i64),
    checked: Cell<i64>,
}

#[derive(Default)]
struct Cache {
    map: HashMap<Box<[u8]>, Rc<Entry>>,
    bytes: usize,
}

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static CACHES: RefCell<Vec<Cache>> = const { RefCell::new(Vec::new()) };
}

fn now() -> i64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs() as i64)
}

/// The media type for a file name's extension.
pub fn content_type(name: &[u8]) -> &'static [u8] {
    let ext = match name.iter().rposition(|&b| b == b'.') {
        Some(i) => &name[i + 1..],
        None => return b"application/octet-stream",
    };
    let mut e = [0u8; 8];
    if ext.len() > e.len() {
        return b"application/octet-stream";
    }
    for (d, s) in e.iter_mut().zip(ext) {
        *d = s.to_ascii_lowercase();
    }
    match &e[..ext.len()] {
        b"html" | b"htm" => b"text/html; charset=utf-8",
        b"css" => b"text/css; charset=utf-8",
        b"js" | b"mjs" => b"text/javascript; charset=utf-8",
        b"json" | b"map" => b"application/json",
        b"txt" => b"text/plain; charset=utf-8",
        b"md" => b"text/markdown; charset=utf-8",
        b"csv" => b"text/csv; charset=utf-8",
        b"xml" => b"application/xml",
        b"svg" => b"image/svg+xml",
        b"png" => b"image/png",
        b"jpg" | b"jpeg" => b"image/jpeg",
        b"gif" => b"image/gif",
        b"webp" => b"image/webp",
        b"avif" => b"image/avif",
        b"ico" => b"image/x-icon",
        b"wasm" => b"application/wasm",
        b"woff" => b"font/woff",
        b"woff2" => b"font/woff2",
        b"ttf" => b"font/ttf",
        b"otf" => b"font/otf",
        b"pdf" => b"application/pdf",
        b"zip" => b"application/zip",
        b"gz" => b"application/gzip",
        b"mp4" => b"video/mp4",
        b"webm" => b"video/webm",
        b"mp3" => b"audio/mpeg",
        b"ogg" => b"audio/ogg",
        b"wav" => b"audio/wav",
        _ => b"application/octet-stream",
    }
}

/// Whether an If-None-Match value matches `etag` (weak comparison, §13.1.2).
fn etag_matches(inm: &[u8], etag: &[u8]) -> bool {
    let strip = |t: &[u8]| -> Vec<u8> {
        let t = t.trim_ascii();
        t.strip_prefix(b"W/").unwrap_or(t).to_vec()
    };
    let ours = strip(etag);
    inm.split(|&b| b == b',').any(|t| {
        let t = t.trim_ascii();
        t == b"*" || strip(t) == ours
    })
}

enum Found {
    File(Rc<Entry>),
    /// A directory named without its trailing `/`.
    Redirect,
    None,
}

impl Files {
    pub fn new(root: &str) -> std::io::Result<Files> {
        let f = std::fs::File::open(root)?;
        if !f.metadata()?.is_dir() {
            return Err(std::io::Error::other(format!("{root} is not a directory")));
        }
        Ok(Files { root: f, id: NEXT_ID.fetch_add(1, Ordering::Relaxed), max_cached: 16 << 20, cache_budget: 256 << 20 })
    }

    /// Serves the file `path` (a request path, `/` first) names, answering
    /// GET and HEAD. False if there is none (nothing was sent: the caller
    /// sends its 404, or tries something else).
    pub fn serve(&self, req: &Request, res: &mut Response, path: &[u8]) -> bool {
        if req.method != b"GET" && req.method != b"HEAD" {
            return false;
        }
        let e = match self.find(path) {
            Found::File(e) => e,
            Found::Redirect => {
                // The path as the client sent it (a router may have
                // stripped a prefix from `path`).
                let mut loc = req.path().to_vec();
                loc.push(b'/');
                if let Some(q) = req.target.iter().position(|&b| b == b'?') {
                    loc.extend_from_slice(&req.target[q..]);
                }
                let _ = res.send(301, &[Field { name: b"Location", value: &loc }], b"");
                return true;
            }
            Found::None => return false,
        };
        let len = e.body.len();
        // §13.2.2: If-None-Match first, else If-Modified-Since (an exact
        // match of our own date, as nginx does by default).
        let fresh = match req.header(b"If-None-Match") {
            Some(v) => etag_matches(v, &e.etag),
            None => req.header(b"If-Modified-Since").is_some_and(|v| v.trim_ascii() == e.last_modified),
        };
        if fresh {
            let _ = res.send_static_part(304, &e.fields, &[], &e.body, 0, 0);
            return true;
        }
        if req.method == b"GET" {
            if let Some(v) = req.header(b"Range") {
                let if_range_ok = match req.header(b"If-Range") {
                    None => true,
                    Some(ir) => {
                        let ir = ir.trim_ascii();
                        ir == e.etag || ir == e.last_modified
                    }
                };
                if if_range_ok {
                    match parse_range(v, len as u64) {
                        Rng::Whole => {}
                        Rng::Part(start, n) => {
                            let cr = format!("bytes {}-{}/{}", start, start + n - 1, len);
                            let _ = res.send_static_part(206, &e.fields, &[Field { name: b"Content-Range", value: cr.as_bytes() }], &e.body, start as usize, n as usize);
                            return true;
                        }
                        Rng::Unsat => {
                            let cr = format!("bytes */{len}");
                            let _ = res.send(416, &[Field { name: b"Content-Range", value: cr.as_bytes() }], b"");
                            return true;
                        }
                    }
                }
            }
        }
        let _ = res.send_static_part(200, &e.fields, &[], &e.body, 0, len);
        true
    }

    fn find(&self, path: &[u8]) -> Found {
        let t = now();
        let hit = CACHES.with(|c| {
            let c = c.borrow();
            c.get(self.id).and_then(|m| m.map.get(path).cloned())
        });
        if let Some(e) = hit {
            if e.checked.get() == t {
                return Found::File(e);
            }
            // Still the same file?
            if let Ok(f) = crate::sys::open_beneath(&self.root, &e.rel) {
                if let Ok(m) = f.metadata() {
                    if m.is_file() && m.ino() == e.ino && m.dev() == e.dev && m.len() == e.body.len() as u64 && (m.mtime(), m.mtime_nsec()) == e.mtime {
                        e.checked.set(t);
                        return Found::File(e);
                    }
                }
            }
            self.forget(path);
        }
        self.load(path, t)
    }

    fn forget(&self, path: &[u8]) {
        CACHES.with(|c| {
            let mut c = c.borrow_mut();
            if let Some(m) = c.get_mut(self.id) {
                if let Some(e) = m.map.remove(path) {
                    m.bytes -= e.body.len();
                }
            }
        });
    }

    fn load(&self, path: &[u8], t: i64) -> Found {
        let Some((comps, dir)) = crate::path::resolve_exec(path) else { return Found::None };
        if comps.iter().any(|c| crate::path::hidden(c)) {
            return Found::None;
        }
        let mut rel = Vec::with_capacity(path.len() + 11);
        crate::path::join_to(&comps, &mut rel);
        if dir {
            if !rel.is_empty() {
                rel.push(b'/');
            }
            rel.extend_from_slice(b"index.html");
        }
        let Ok(mut f) = crate::sys::open_beneath(&self.root, &rel) else { return Found::None };
        let Ok(m) = f.metadata() else { return Found::None };
        if m.is_dir() {
            return if dir { Found::None } else { Found::Redirect };
        }
        if !m.is_file() || m.len() > usize::MAX as u64 / 2 {
            return Found::None;
        }
        let mut bytes = Vec::with_capacity(m.len() as usize);
        use std::io::Read;
        if f.read_to_end(&mut bytes).is_err() || bytes.len() as u64 != m.len() {
            return Found::None;
        }
        let etag = format!("\"{:x}-{:x}\"", m.mtime(), m.len()).into_bytes();
        let last_modified = crate::date::imf_fixdate(m.mtime());
        let name = comps.last().map_or(&b"index.html"[..], |c| if dir { &b"index.html"[..] } else { c });
        let Some(fields) = Fields::new(&[
            Field { name: b"Content-Type", value: content_type(name) },
            Field { name: b"Last-Modified", value: &last_modified },
            Field { name: b"ETag", value: &etag },
            Field { name: b"Accept-Ranges", value: b"bytes" },
        ]) else {
            return Found::None;
        };
        let len = bytes.len();
        let e = Rc::new(Entry {
            rel,
            body: StaticBody::new(bytes),
            fields,
            etag,
            last_modified,
            ino: m.ino(),
            dev: m.dev(),
            mtime: (m.mtime(), m.mtime_nsec()),
            checked: Cell::new(t),
        });
        if len <= self.max_cached {
            CACHES.with(|c| {
                let mut c = c.borrow_mut();
                if c.len() <= self.id {
                    c.resize_with(self.id + 1, Cache::default);
                }
                let m = &mut c[self.id];
                while m.bytes + len > self.cache_budget && !m.map.is_empty() {
                    let k = m.map.keys().next().unwrap().clone();
                    if let Some(old) = m.map.remove(&k) {
                        m.bytes -= old.body.len();
                    }
                }
                if m.bytes + len <= self.cache_budget {
                    m.bytes += len;
                    if let Some(old) = m.map.insert(path.into(), e.clone()) {
                        m.bytes -= old.body.len();
                    }
                }
            });
        }
        Found::File(e)
    }
}
