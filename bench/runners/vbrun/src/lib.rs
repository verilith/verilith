//! The runner side of the vbench protocol for Rust contenders; see
//! `harness/runner.h` for the protocol. Timing and counters go through the
//! same C code (`harness/counters.c`) as the C runners.
use std::io::{BufRead, Write};

unsafe extern "C" {
    fn vb_counters_init() -> i32;
    fn vb_now_ns() -> u64;
    fn vb_counters_read(ins: *mut i64, cyc: *mut i64);
}

pub struct Runner {
    cases: Vec<(String, u64, Box<dyn FnMut() -> u64>)>,
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}

impl Runner {
    pub fn new() -> Self {
        Runner { cases: Vec::new() }
    }

    /// Registers a case. `bytes` is the input size of one call (0 if none);
    /// `f` returns a check value the harness compares across contenders.
    pub fn case(&mut self, name: impl Into<String>, bytes: u64, f: impl FnMut() -> u64 + 'static) {
        self.cases.push((name.into(), bytes, Box::new(f)));
    }

    pub fn main(mut self) {
        let have = unsafe { vb_counters_init() };
        let stdin = std::io::stdin();
        let mut out = std::io::stdout().lock();
        for line in stdin.lock().lines() {
            let line = line.unwrap();
            if line == "quit" {
                break;
            } else if line == "info" {
                writeln!(out, "counters {have}").unwrap();
            } else if line == "cases" {
                for (n, b, _) in &self.cases {
                    writeln!(out, "{n}\t{b}").unwrap();
                }
                writeln!(out, ".").unwrap();
            } else if let Some(rest) = line.strip_prefix("run ") {
                let (name, iters) = rest.rsplit_once(' ').unwrap();
                let iters: u64 = iters.parse().unwrap();
                let Some((_, _, f)) = self.cases.iter_mut().find(|c| c.0 == name) else {
                    writeln!(out, "error unknown case {name}").unwrap();
                    continue;
                };
                let (mut i0, mut c0, mut i1, mut c1) = (0i64, 0i64, 0i64, 0i64);
                let mut check = 0u64;
                unsafe { vb_counters_read(&mut i0, &mut c0) };
                let t0 = unsafe { vb_now_ns() };
                for _ in 0..iters {
                    check = std::hint::black_box(f());
                }
                let t1 = unsafe { vb_now_ns() };
                unsafe { vb_counters_read(&mut i1, &mut c1) };
                let d = |a: i64, b: i64| if a < 0 || b < 0 { -1 } else { b - a };
                writeln!(out, "{}\t{}\t{}\t{check}", t1 - t0, d(i0, i1), d(c0, c1)).unwrap();
            } else {
                writeln!(out, "error unknown command").unwrap();
            }
            out.flush().unwrap();
        }
    }
}

/// `$VBENCH_DATA`, or "data".
pub fn data_dir() -> String {
    std::env::var("VBENCH_DATA").ok().filter(|s| !s.is_empty()).unwrap_or_else(|| "data".into())
}

/// Sorted regular files in `dir` whose names don't start with '.'.
pub fn list_dir(dir: &str) -> Vec<String> {
    let mut v: Vec<String> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("vbench: cannot open directory {dir}: {e}"))
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|t| t.is_file()).unwrap_or(false))
        .map(|e| e.file_name().into_string().unwrap())
        .filter(|n| !n.starts_with('.'))
        .collect();
    v.sort();
    v
}

/// The drivers' cheap digest (`mix` in suites/*/*.c): about 64 bytes spread
/// over `p`, so a check value depends on the bytes and not only their count.
pub fn mix(mut h: u64, p: &[u8]) -> u64 {
    let step = p.len() / 64 + 1;
    let mut i = 0;
    while i < p.len() {
        h = (h ^ p[i] as u64).wrapping_mul(0x100000001b3);
        i += step;
    }
    h
}

/// The image drivers' check value (`strided_sum` in suites/webp/webp.c and
/// suites/jpeg/jpeg.c).
pub fn strided_sum(p: &[u8]) -> u64 {
    let mut s = p.len() as u64;
    for i in (0..p.len()).step_by(61) {
        s = s.wrapping_mul(31).wrapping_add(p[i] as u64);
    }
    s
}

/// The `mode` argument (argv[1]), or `default`.
pub fn mode(default: &str) -> String {
    std::env::args().nth(1).unwrap_or_else(|| default.into())
}
