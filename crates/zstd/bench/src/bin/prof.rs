//! Decodes each file N times with vzstd only and prints the best time, for
//! profilers and A/B runs.
//! Usage: prof [--stream | --reuse | --capi] [--rounds N] FILE.zst...
//! `--capi` calls the C API's one-shot `ZSTD_decompress` into a buffer
//! kept between rounds, as libzstd is measured.
//! `--reuse` decodes one-shot into a vector kept between rounds.
//! `--stream` goes through the C API's streaming decoder with 128 KiB
//! input and output pieces, as `vzstd-bench` does.
#![allow(unsafe_op_in_unsafe_fn)]
use std::ffi::c_void;
use std::time::Instant;
use verilith_zstd::capi::{InBuffer, OutBuffer};

/// Streams `c` into `out`; returns the output size.
unsafe fn stream(ctx: *mut c_void, c: &[u8], out: &mut Vec<u8>, chunk: &mut [u8]) -> usize {
    let mut ip = 0;
    out.clear();
    loop {
        let n = (c.len() - ip).min(128 * 1024);
        let mut i = InBuffer { src: c[ip..].as_ptr() as *const c_void, size: n, pos: 0 };
        let mut o = OutBuffer { dst: chunk.as_mut_ptr() as *mut c_void, size: chunk.len(), pos: 0 };
        let r = verilith_zstd::capi::zstd_decompress_stream(ctx as *mut _, &mut o, &mut i);
        assert!(r < usize::MAX - 200, "stream error");
        out.extend_from_slice(&chunk[..o.pos]);
        ip += i.pos;
        if ip == c.len() && o.pos < chunk.len() && (r == 0 || i.pos == 0) {
            return out.len();
        }
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut rounds = 1;
    let mut streaming = false;
    let mut reuse = false;
    let mut capi = false;
    let mut dst: Vec<u8> = Vec::new();
    let mut keep: Vec<u8> = Vec::new();
    loop {
        match args.first().map(|s| s.as_str()) {
            Some("--rounds") => {
                rounds = args[1].parse().unwrap();
                args.drain(..2);
            }
            Some("--capi") => {
                capi = true;
                args.remove(0);
            }
            Some("--reuse") => {
                reuse = true;
                args.remove(0);
            }
            Some("--stream") => {
                streaming = true;
                args.remove(0);
            }
            _ => break,
        }
    }
    let ctx = unsafe { verilith_zstd::capi::zstd_create_dctx() } as *mut c_void;
    let mut chunk = vec![0u8; 128 * 1024];
    let mut sink = Vec::new();
    for f in &args {
        let c = std::fs::read(f).unwrap();
        let mut best = f64::MAX;
        let mut n = 0;
        for _ in 0..rounds {
            let t = Instant::now();
            if streaming {
                n = unsafe {
                    verilith_zstd::capi::zstd_dctx_reset(ctx as *mut _, 1);
                    stream(ctx, &c, &mut sink, &mut chunk)
                };
            } else if capi {
                if dst.is_empty() {
                    let want = unsafe { verilith_zstd::capi::zstd_get_frame_content_size(c.as_ptr() as *const c_void, c.len()) } as usize;
                    dst = vec![1u8; want + 64];
                }
                n = unsafe { verilith_zstd::capi::zstd_decompress(dst.as_mut_ptr() as *mut c_void, dst.len(), c.as_ptr() as *const c_void, c.len()) };
            } else if reuse {
                keep = verilith_zstd::frame::decompress_reuse(&c, 1 << 40, std::mem::take(&mut keep)).expect("vzstd rejects the file");
                n = keep.len();
            } else {
                n = verilith_zstd::frame::decompress_exec(&c, 1 << 40).expect("vzstd rejects the file").len();
            }
            best = best.min(t.elapsed().as_secs_f64());
        }
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy();
        println!("{:<20} {:>10} bytes {:>9.3} ms {:>7.0} MB/s", name, n, best * 1e3, n as f64 / 1e6 / best);
    }
}
