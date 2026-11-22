//! URL parsing throughput: vurl, the url crate, ada and libcurl.
//!
//! usage: urlbench [FILE] [ITERS] [ONLY]   (FILE: one URL per line; default
//! ~/ext/url-dataset/out.txt; ONLY: run just the parsers whose names start
//! with one of these comma-separated prefixes, e.g. "ada" or "vurl,curl")
use std::ffi::CString;
use std::hint::black_box;
use std::time::Instant;

unsafe extern "C" {
    fn ada_loop(p: *const *const u8, l: *const usize, n: usize, ok: *mut usize) -> usize;
    fn curl_loop(p: *const *const i8, n: usize, ok: *mut usize, get: i32) -> usize;
}

fn time<F: FnMut() -> (usize, usize)>(name: &str, iters: usize, bytes: usize, n: usize, mut f: F) {
    if let Some(only) = std::env::args().nth(3) {
        if !only.split(',').any(|p| name.starts_with(p)) {
            return;
        }
    }
    let mut best = f64::MAX;
    let mut ok = 0;
    let mut href = 0;
    let mut runs = Vec::new();
    for _ in 0..iters {
        let t = Instant::now();
        let (o, h) = black_box(f());
        let dt = t.elapsed().as_secs_f64();
        runs.push(dt);
        best = best.min(dt);
        ok = o;
        href = h;
    }
    runs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = runs[runs.len() / 2];
    println!(
        "{name:<14} {:>8.1} ns/url (median {:>8.1})  {:>7.1} MB/s  ok {ok}  href bytes {href}",
        best * 1e9 / n as f64,
        med * 1e9 / n as f64,
        bytes as f64 / best / 1e6
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).cloned().unwrap_or_else(|| {
        format!("{}/ext/url-dataset/out.txt", std::env::var("HOME").unwrap())
    });
    let iters: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(20);
    let text = std::fs::read_to_string(&path).unwrap();
    let urls: Vec<&str> = text.lines().filter(|l| !l.is_empty()).collect();
    let n = urls.len();
    let bytes: usize = urls.iter().map(|u| u.len()).sum();
    println!("{path}: {n} URLs, {bytes} bytes, best of {iters}");

    time("vurl", iters, bytes, n, || {
        let (mut ok, mut h) = (0, 0);
        for u in &urls {
            if let Some(x) = verilith_url::Url::parse(black_box(u), None) {
                ok += 1;
                h += x.href().len();
            }
        }
        (ok, h)
    });
    time("url (servo)", iters, bytes, n, || {
        let (mut ok, mut h) = (0, 0);
        for u in &urls {
            if let Ok(x) = url::Url::parse(black_box(u)) {
                ok += 1;
                h += x.as_str().len();
            }
        }
        (ok, h)
    });
    let ptrs: Vec<*const u8> = urls.iter().map(|u| u.as_ptr()).collect();
    let lens: Vec<usize> = urls.iter().map(|u| u.len()).collect();
    time("ada", iters, bytes, n, || {
        let mut ok = 0;
        let h = unsafe { ada_loop(ptrs.as_ptr(), lens.as_ptr(), n, &mut ok) };
        (ok, h)
    });
    let cs: Vec<CString> = urls.iter().map(|u| CString::new(*u).unwrap()).collect();
    let cp: Vec<*const i8> = cs.iter().map(|c| c.as_ptr()).collect();
    time("curl (set)", iters, bytes, n, || {
        let mut ok = 0;
        let h = unsafe { curl_loop(cp.as_ptr(), n, &mut ok, 0) };
        (ok, h)
    });
    time("curl (set+get)", iters, bytes, n, || {
        let mut ok = 0;
        let h = unsafe { curl_loop(cp.as_ptr(), n, &mut ok, 1) };
        (ok, h)
    });
}
