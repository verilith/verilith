//! Encodes a PAM or PPM image to WebP (like `cwebp`).
//!
//! Usage: vcwebp input.pam output.webp [-q quality] [-lossless]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: vcwebp input.pam output.webp [-q quality] [-lossless]");
        std::process::exit(2);
    }
    let data = std::fs::read(&args[1]).expect("read input");
    let mut q = 75u32;
    let mut lossless = false;
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "-q" => {
                q = args[i + 1].parse().expect("quality");
                i += 1;
            }
            "-lossless" => lossless = true,
            a => panic!("unknown option {a}"),
        }
        i += 1;
    }
    let (w, h, px) = read_pnm(&data);
    let out = if lossless {
        verilith_webp::enc_vp8l::encode_lossless(&px, w as u32, h as u32)
    } else {
        verilith_webp::enc_vp8::encode_lossy(&px, w, h, q)
    }
    .expect("encodes");
    std::fs::write(&args[2], out).expect("write output");
}

/// A binary PPM (P6) or PAM (P7, RGB or RGB_ALPHA) image as ARGB.
fn read_pnm(d: &[u8]) -> (usize, usize, Vec<u32>) {
    let mut pos = 0;
    let mut tok = || {
        while d[pos].is_ascii_whitespace() {
            pos += 1;
        }
        let s = pos;
        while !d[pos].is_ascii_whitespace() {
            pos += 1;
        }
        String::from_utf8_lossy(&d[s..pos]).into_owned()
    };
    let magic = tok();
    let (w, h, depth);
    if magic == "P6" {
        w = tok().parse().unwrap();
        h = tok().parse().unwrap();
        let _max = tok();
        depth = 3;
    } else {
        let (mut ww, mut hh, mut dd) = (0, 0, 0);
        loop {
            match tok().as_str() {
                "WIDTH" => ww = tok().parse().unwrap(),
                "HEIGHT" => hh = tok().parse().unwrap(),
                "DEPTH" => dd = tok().parse().unwrap(),
                "ENDHDR" => break,
                _ => {}
            }
        }
        w = ww;
        h = hh;
        depth = dd;
    }
    pos += 1;
    let px = d[pos..pos + w * h * depth]
        .chunks(depth)
        .map(|c| {
            let a = if depth == 4 { c[3] as u32 } else { 255 };
            (a << 24) | ((c[0] as u32) << 16) | ((c[1] as u32) << 8) | c[2] as u32
        })
        .collect();
    (w, h, px)
}
