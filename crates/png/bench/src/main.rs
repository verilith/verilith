//! Times one PNG decoder over a directory of files: a warm-up round, then
//! the best of `rounds`. Run one decoder per process (see `run.sh`).
//! Usage: vpng-bench DECODER rgba8|native DIR [ROUNDS]
//! DECODER: vpng, libpng, spng, png, zune
use std::time::Instant;

extern "C" {
    fn libpng_decode(data: *const u8, len: usize, rgba: i32, out: *mut *mut u8) -> usize;
    fn spng_decode(data: *const u8, len: usize, rgba: i32, out: *mut *mut u8) -> usize;
    fn free(p: *mut u8);
}

fn c_decode(f: unsafe extern "C" fn(*const u8, usize, i32, *mut *mut u8) -> usize, d: &[u8], rgba: bool) -> usize {
    let mut p = std::ptr::null_mut();
    unsafe {
        let n = f(d.as_ptr(), d.len(), rgba as i32, &mut p);
        let first = if n > 0 { *p } else { 0 };
        free(p);
        n + first as usize % 1
    }
}

fn png_crate(d: &[u8], rgba: bool) -> usize {
    let mut dec = png::Decoder::new(std::io::Cursor::new(d));
    if rgba {
        dec.set_transformations(png::Transformations::EXPAND | png::Transformations::STRIP_16 | png::Transformations::ALPHA);
    } else {
        dec.set_transformations(png::Transformations::IDENTITY);
    }
    let mut r = dec.read_info().unwrap();
    let mut buf = vec![0; r.output_buffer_size().unwrap()];
    let info = r.next_frame(&mut buf).unwrap();
    // png's ALPHA leaves grey images as grey-alpha; converting those to
    // RGBA is not counted, so its numbers are a little optimistic there.
    info.buffer_size()
}

fn zune(d: &[u8], rgba: bool) -> usize {
    use zune_core::options::DecoderOptions;
    let opts = if rgba {
        DecoderOptions::default().png_set_strip_to_8bit(true).png_set_add_alpha_channel(true)
    } else {
        DecoderOptions::default()
    };
    let mut dec = zune_png::PngDecoder::new_with_options(zune_core::bytestream::ZCursor::new(d), opts);
    match dec.decode().unwrap() {
        zune_core::result::DecodingResult::U8(v) => v.len(),
        zune_core::result::DecodingResult::U16(v) => v.len() * 2,
        _ => 0,
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].as_str();
    let rgba = a[2] == "rgba8";
    let rounds: usize = a.get(4).map(|s| s.parse().unwrap()).unwrap_or(10);
    let mut files: Vec<_> = std::fs::read_dir(&a[3]).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().map_or(false, |e| e == "png")).collect();
    files.sort();
    for f in files {
        let d = std::fs::read(&f).unwrap();
        let run = |d: &[u8]| -> usize {
            match which {
                "vpng" => {
                    let fmt = if rgba { verilith_png::top::PixelFormat::Rgba8 } else { verilith_png::top::PixelFormat::Native };
                    verilith_png::top::decode(d, fmt, 1 << 34).map(|r| r.1.len()).unwrap_or(0)
                }
                "libpng" => c_decode(libpng_decode, d, rgba),
                "spng" => c_decode(spng_decode, d, rgba),
                "png" => png_crate(d, rgba),
                "zune" => zune(d, rgba),
                _ => panic!("unknown decoder"),
            }
        };
        let n = run(&d);
        let (w, h) = (u32::from_be_bytes(d[16..20].try_into().unwrap()), u32::from_be_bytes(d[20..24].try_into().unwrap()));
        let mut best = f64::MAX;
        // Enough iterations per round for at least ~50 ms.
        let t0 = Instant::now();
        run(&d);
        let iters = ((0.05 / t0.elapsed().as_secs_f64()).ceil() as usize).max(1);
        for _ in 0..rounds {
            let t = Instant::now();
            for _ in 0..iters {
                std::hint::black_box(run(std::hint::black_box(&d)));
            }
            best = best.min(t.elapsed().as_secs_f64() / iters as f64);
        }
        let mpx = (w as f64 * h as f64) / 1e6;
        println!("{}\t{}\t{}\t{}\t{:.3}\t{:.1}", f.file_name().unwrap().to_string_lossy(), which, a[2], n, best * 1e3, mpx / best);
    }
}
