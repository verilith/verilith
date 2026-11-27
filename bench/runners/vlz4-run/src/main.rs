//! LZ4, verilith-lz4's Rust API against liblz4's (suites/lz4/lz4.c), the
//! same cases and check values, into reused buffers:
//!   decompress/FILE        `decompress_block` (FILE.block)
//!   compress/FILE          `compress_block`, acceleration 1
//!   frame-decompress/FILE  `frame::decode_frame_into` (FILE.frame)
//!   frame-compress/FILE    `fcompress::compress_into`, liblz4's default
//!                          frame (64 KiB linked blocks, no checksums)
use verilith_lz4::Prefs;

const DEFAULT_FRAME: Prefs = Prefs { block_id: 4, indep: false, bsum: false, csum: false, csize: false, accel: 1 };

fn main() {
    let mode = vbrun::mode("decompress");
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let orig = std::fs::read(format!("{dir}/{name}")).unwrap();
        let len = orig.len();
        let case = format!("{mode}/{name}");
        match mode.as_str() {
            "decompress" => {
                let z = std::fs::read(format!("{dir}/lz4/{name}.block")).unwrap();
                let mut out = vec![0u8; len + 1];
                let n = verilith_lz4::decompress_block(&z, &mut out).unwrap();
                assert!(out[..n] == orig[..], "{case}");
                r.case(case, len as u64, move || {
                    let n = verilith_lz4::decompress_block(std::hint::black_box(&z), &mut out).unwrap();
                    vbrun::mix(n as u64, &out[..n])
                });
            }
            "frame-decompress" => {
                let z = std::fs::read(format!("{dir}/lz4/{name}.frame")).unwrap();
                let mut out = vec![0u8; len + 1];
                let (_, n) = verilith_lz4::frame::decode_frame_into(&z, 0, &mut out, 0).unwrap();
                assert!(out[..n] == orig[..], "{case}");
                r.case(case, len as u64, move || {
                    let (_, n) = verilith_lz4::frame::decode_frame_into(std::hint::black_box(&z), 0, &mut out, 0).unwrap();
                    vbrun::mix(n as u64, &out[..n])
                });
            }
            "compress" => {
                let mut out = vec![0u8; verilith_lz4::compress_bound(len)];
                let m = verilith_lz4::compress_block(&orig, &mut out, 1).unwrap();
                let mut back = vec![0u8; len + 1];
                assert!(verilith_lz4::decompress_block(&out[..m], &mut back) == Some(len) && back[..len] == orig[..], "{case}");
                r.case(case, len as u64, move || verilith_lz4::compress_block(std::hint::black_box(&orig), &mut out, 1).unwrap() as u64);
            }
            "frame-compress" => {
                let mut out = vec![0u8; len + len / 128 + (1 << 16) + 64];
                let m = verilith_lz4::fcompress::compress_into(&orig, &mut out, &DEFAULT_FRAME).unwrap();
                assert!(verilith_lz4::decompress(&out[..m], len + 1).unwrap() == orig, "{case}");
                r.case(case, len as u64, move || {
                    verilith_lz4::fcompress::compress_into(std::hint::black_box(&orig), &mut out, &DEFAULT_FRAME).unwrap() as u64
                });
            }
            m => panic!("unknown mode {m}"),
        }
    }
    r.main();
}
