//! Decompression throughput of vzstd against libzstd, loaded with dlopen.
//! Usage: vzstd-bench [--rounds N] FILE.zst...
//! libzstd is found via VZSTD_LIBZSTD, else the usual names.
use std::ffi::{c_char, c_int, c_void, CString};
use std::time::Instant;
use verilith_zstd::capi::{InBuffer, OutBuffer};

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(h: *mut c_void, name: *const c_char) -> *mut c_void;
}

type Decompress = unsafe extern "C" fn(*mut u8, usize, *const u8, usize) -> usize;
type IsError = unsafe extern "C" fn(usize) -> u32;
type Create = unsafe extern "C" fn() -> *mut c_void;
type Stream = unsafe extern "C" fn(*mut c_void, *mut OutBuffer, *mut InBuffer) -> usize;
type Reset = unsafe extern "C" fn(*mut c_void, c_int) -> usize;
type Version = unsafe extern "C" fn() -> *const c_char;

struct Lib {
    decompress: Decompress,
    is_error: IsError,
    create: Create,
    stream: Stream,
    reset: Reset,
    version: Version,
}

fn load() -> Lib {
    let mut names: Vec<String> = std::env::var("VZSTD_LIBZSTD").into_iter().collect();
    names.extend(
        ["libzstd.so.1", "libzstd.1.dylib", "/opt/homebrew/lib/libzstd.1.dylib", "/usr/local/lib/libzstd.1.dylib"]
            .iter()
            .map(|s| s.to_string()),
    );
    for n in names {
        let h = unsafe { dlopen(CString::new(n.clone()).unwrap().as_ptr(), 2) };
        if h.is_null() {
            continue;
        }
        let sym = |s: &str| {
            let p = unsafe { dlsym(h, CString::new(s).unwrap().as_ptr()) };
            assert!(!p.is_null(), "{s} missing in {n}");
            p
        };
        unsafe {
            return Lib {
                decompress: std::mem::transmute(sym("ZSTD_decompress")),
                is_error: std::mem::transmute(sym("ZSTD_isError")),
                create: std::mem::transmute(sym("ZSTD_createDCtx")),
                stream: std::mem::transmute(sym("ZSTD_decompressStream")),
                reset: std::mem::transmute(sym("ZSTD_DCtx_reset")),
                version: std::mem::transmute(sym("ZSTD_versionString")),
            };
        }
    }
    panic!("libzstd not found; set VZSTD_LIBZSTD");
}

/// Best time in seconds of `rounds` runs of `f`.
fn best(rounds: usize, mut f: impl FnMut()) -> f64 {
    f();
    let mut b = f64::MAX;
    for _ in 0..rounds {
        let t = Instant::now();
        f();
        b = b.min(t.elapsed().as_secs_f64());
    }
    b
}

/// Streams `c` with 128 KiB input and output pieces, like Node does.
unsafe fn stream(ctx: *mut c_void, f: Stream, c: &[u8], out: &mut [u8], chunk: &mut [u8]) -> usize {
    let mut ip = 0;
    let mut total = 0;
    loop {
        let n = (c.len() - ip).min(128 * 1024);
        let mut i = InBuffer { src: c[ip..].as_ptr() as *const c_void, size: n, pos: 0 };
        let mut o = OutBuffer { dst: chunk.as_mut_ptr() as *mut c_void, size: chunk.len(), pos: 0 };
        let r = f(ctx, &mut o, &mut i);
        assert!(r < usize::MAX - 200, "stream error");
        out[total..total + o.pos].copy_from_slice(&chunk[..o.pos]);
        total += o.pos;
        ip += i.pos;
        if ip == c.len() && o.pos < chunk.len() && (r == 0 || i.pos == 0) {
            return total;
        }
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut rounds = 10;
    if args.first().map(|s| s.as_str()) == Some("--rounds") {
        rounds = args[1].parse().unwrap();
        args.drain(..2);
    }
    let lib = load();
    let _lock = Lock::take();
    let v = unsafe { std::ffi::CStr::from_ptr((lib.version)()) };
    println!("libzstd {}", v.to_string_lossy());
    println!("{:<28} {:>10} {:>9} {:>9} {:>7} {:>9} {:>9} {:>7} {:>9} {:>7}", "file", "MB", "zstd MB/s", "vz MB/s", "ratio", "zstd strm", "vz strm", "ratio", "vz reuse", "ratio");
    let (mut tz, mut tv, mut tzs, mut tvs, mut tvr, mut bytes) = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0);
    for f in &args {
        let c = std::fs::read(f).unwrap();
        let want = verilith_zstd::frame::decompress_exec(&c, 1 << 40).expect("vzstd rejects the file");
        let n = want.len();
        let mut out = vec![0u8; n + 64];
        let t_z = best(rounds, || unsafe {
            let r = (lib.decompress)(out.as_mut_ptr(), out.len(), c.as_ptr(), c.len());
            assert!((lib.is_error)(r) == 0 && r == n);
        });
        assert_eq!(&out[..n], &want[..]);
        let t_v = best(rounds, || {
            let r = verilith_zstd::frame::decompress_exec(&c, out.len()).unwrap();
            assert_eq!(r.len(), n);
        });
        // One-shot into a buffer kept between calls, as libzstd is given.
        let mut keep: Vec<u8> = Vec::new();
        let t_vr = best(rounds, || {
            let r = verilith_zstd::frame::decompress_reuse(&c, out.len(), std::mem::take(&mut keep)).unwrap();
            assert_eq!(r.len(), n);
            keep = r;
        });
        drop(keep);
        let mut chunk = vec![0u8; 128 * 1024];
        let zc = unsafe { (lib.create)() };
        let t_zs = best(rounds, || unsafe {
            (lib.reset)(zc, 1);
            assert_eq!(stream(zc, lib.stream, &c, &mut out, &mut chunk), n);
        });
        let vc = unsafe { verilith_zstd::capi::zstd_create_dctx() } as *mut c_void;
        let vs: Stream = unsafe { std::mem::transmute(verilith_zstd::capi::zstd_decompress_stream as *const ()) };
        let t_vs = best(rounds, || unsafe {
            verilith_zstd::capi::zstd_dctx_reset(vc as *mut _, 1);
            assert_eq!(stream(vc, vs, &c, &mut out, &mut chunk), n);
        });
        assert_eq!(&out[..n], &want[..]);
        let mb = n as f64 / 1e6;
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy();
        println!(
            "{:<28} {:>10.2} {:>9.0} {:>9.0} {:>7.2} {:>9.0} {:>9.0} {:>7.2} {:>9.0} {:>7.2}",
            name, mb, mb / t_z, mb / t_v, t_z / t_v, mb / t_zs, mb / t_vs, t_zs / t_vs, mb / t_vr, t_z / t_vr
        );
        tvr += t_vr;
        tz += t_z;
        tv += t_v;
        tzs += t_zs;
        tvs += t_vs;
        bytes += mb;
    }
    println!(
        "{:<28} {:>10.2} {:>9.0} {:>9.0} {:>7.2} {:>9.0} {:>9.0} {:>7.2} {:>9.0} {:>7.2}",
        "TOTAL", bytes, bytes / tz, bytes / tv, tz / tv, bytes / tzs, bytes / tvs, tzs / tvs, bytes / tvr, tz / tvr
    );
}

/// The shared benchmark machine's lock (`~/vf-bench.lock`): timings are
/// taken only while it is held, so runs from other projects do not skew
/// them. Removed on exit, including on panic.
struct Lock(std::path::PathBuf);

impl Lock {
    fn take() -> Lock {
        let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
        let p = std::path::PathBuf::from(home).join("vf-bench.lock");
        let mut said = false;
        while std::fs::create_dir(&p).is_err() {
            if !said {
                eprintln!("waiting for {} (another benchmark is running)", p.display());
                said = true;
            }
            std::thread::sleep(std::time::Duration::from_secs(5));
        }
        // Who holds it, so a stale lock can be traced.
        let _ = std::fs::write(p.join("pid"), format!("{} vzstd-bench\n", std::process::id()));
        Lock(p)
    }
}

impl Drop for Lock {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(self.0.join("pid"));
        let _ = std::fs::remove_dir(&self.0);
    }
}
