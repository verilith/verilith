//! The compression C ABI against zlib's inflate.
mod common;
use common::{text, zinflate, zinflate_end, zinflate_init, zinflate_step, Rng};
use std::os::raw::{c_int, c_uint, c_ulong};
use verilith_zlib::capi::*;

fn new_stream() -> ZStream {
    unsafe { std::mem::zeroed() }
}

fn init(s: &mut ZStream, level: c_int, wbits: c_int) {
    unsafe {
        assert_eq!(
            vz_deflateInit2_(s, level, Z_DEFLATED, wbits, 8, 0, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int),
            Z_OK
        );
    }
}

/// Compresses `data` through `deflate()` in random input and output
/// pieces with random flushes; returns the stream and the final `adler`.
fn deflate_pieces(data: &[u8], level: c_int, wbits: c_int, rng: &mut Rng) -> (Vec<u8>, c_ulong) {
    let mut s = new_stream();
    init(&mut s, level, wbits);
    let mut out = Vec::new();
    let mut ip = 0;
    unsafe {
        loop {
            let n = if rng.below(4) == 0 { rng.below(100) } else { rng.below(70_000) } as usize;
            let n = n.min(data.len() - ip);
            let last = ip + n == data.len();
            let flush = if last {
                Z_FINISH
            } else {
                [Z_NO_FLUSH, Z_NO_FLUSH, Z_NO_FLUSH, Z_SYNC_FLUSH, Z_FULL_FLUSH, Z_PARTIAL_FLUSH, Z_BLOCK][rng.below(7) as usize]
            };
            s.next_in = data.as_ptr().add(ip);
            s.avail_in = n as c_uint;
            // Call until the input is taken and, for a flush, the output fits.
            loop {
                let mut buf = vec![0u8; 1 + rng.below(40_000) as usize];
                s.next_out = buf.as_mut_ptr();
                s.avail_out = buf.len() as c_uint;
                let r = vz_deflate(&mut s, flush);
                let made = buf.len() - s.avail_out as usize;
                out.extend_from_slice(&buf[..made]);
                if r == Z_STREAM_END {
                    assert!(last);
                    break;
                }
                assert!(r == Z_OK || r == Z_BUF_ERROR, "deflate returned {r}");
                if s.avail_in == 0 && s.avail_out > 0 && flush != Z_FINISH {
                    break;
                }
            }
            ip += n;
            if last {
                break;
            }
        }
        assert_eq!(s.total_in as usize, data.len());
        assert_eq!(s.total_out as usize, out.len());
        let adler = s.adler;
        assert_eq!(vz_deflateEnd(&mut s), Z_OK);
        (out, adler)
    }
}

#[test]
fn deflate_streaming_round_trip() {
    let mut rng = Rng(5);
    let inputs = [Vec::new(), b"x".to_vec(), text(&mut rng, 300_000), (0..200_000).map(|_| rng.next() as u8).collect(), vec![7u8; 500_000]];
    for d in &inputs {
        for (level, wbits) in [(-1, 15), (0, 15), (1, -15), (6, 31), (9, 15), (6, 9), (3, -9), (6, 25)] {
            let (c, adler) = deflate_pieces(d, level, wbits, &mut rng);
            let (out, used) = zinflate(&c, wbits).expect("zlib rejected the stream");
            assert_eq!(out, *d, "level {level} wbits {wbits}");
            assert_eq!(used, c.len());
            let want = match wbits {
                24..=31 => unsafe { vz_crc32(0, d.as_ptr(), d.len() as c_uint) },
                8..=15 => unsafe { vz_adler32(1, d.as_ptr(), d.len() as c_uint) },
                _ => adler,
            };
            assert_eq!(adler, want);
        }
    }
}

#[test]
fn sync_flush_makes_input_decodable() {
    let d = text(&mut Rng(9), 100_000);
    unsafe {
        let mut s = new_stream();
        init(&mut s, 6, 15);
        let mut z: common::ZStream = std::mem::zeroed();
        common::zinflate_init(&mut z, 15);
        let mut buf = vec![0u8; 200_000];
        let mut got = vec![0u8; 200_000];
        let mut have = 0;
        for piece in d.chunks(7_777) {
            s.next_in = piece.as_ptr();
            s.avail_in = piece.len() as c_uint;
            s.next_out = buf.as_mut_ptr();
            s.avail_out = buf.len() as c_uint;
            assert_eq!(vz_deflate(&mut s, Z_SYNC_FLUSH), Z_OK);
            let made = buf.len() - s.avail_out as usize;
            assert!(made >= 4 && buf[made - 4..made] == [0, 0, 0xff, 0xff]);
            let (r, used, n) = common::zinflate_step(&mut z, &buf[..made], &mut got[have..]);
            assert_eq!((r, used), (0, made));
            have += n;
            assert_eq!(&got[..have], &d[..s.total_in as usize]);
        }
        common::zinflate_end(&mut z);
        vz_deflateEnd(&mut s);
    }
}

#[test]
fn compress_and_bounds() {
    let mut rng = Rng(11);
    let inputs = [Vec::new(), text(&mut rng, 100_000), (0..300_000).map(|_| rng.next() as u8).collect::<Vec<u8>>()];
    for d in &inputs {
        for level in [-1, 0, 1, 9] {
            let bound = vz_compressBound(d.len() as c_ulong) as usize;
            let mut c = vec![0u8; bound];
            let mut n = bound as c_ulong;
            assert_eq!(unsafe { vz_compress2(c.as_mut_ptr(), &mut n, d.as_ptr(), d.len() as c_ulong, level) }, Z_OK);
            assert_eq!(zinflate(&c[..n as usize], 15).unwrap().0, *d);
            let mut back = vec![0u8; d.len() + 1];
            let mut m = back.len() as c_ulong;
            assert_eq!(unsafe { vz_uncompress(back.as_mut_ptr(), &mut m, c.as_ptr(), n) }, Z_OK);
            assert_eq!(&back[..m as usize], &d[..]);
            // One deflate(Z_FINISH) call with deflateBound's room finishes.
            for wbits in [15, -15, 31] {
                let mut s = new_stream();
                init(&mut s, level, wbits);
                let b = unsafe { vz_deflateBound(&mut s, d.len() as c_ulong) } as usize;
                let mut out = vec![0u8; b];
                s.next_in = d.as_ptr();
                s.avail_in = d.len() as c_uint;
                s.next_out = out.as_mut_ptr();
                s.avail_out = b as c_uint;
                assert_eq!(unsafe { vz_deflate(&mut s, Z_FINISH) }, Z_STREAM_END);
                let made = b - s.avail_out as usize;
                assert_eq!(zinflate(&out[..made], wbits).unwrap().0, *d);
                unsafe { vz_deflateEnd(&mut s) };
            }
        }
    }
    // Too small a buffer.
    let d = text(&mut rng, 10_000);
    let mut c = vec![0u8; 10];
    let mut n = 10 as c_ulong;
    assert_eq!(unsafe { vz_compress(c.as_mut_ptr(), &mut n, d.as_ptr(), d.len() as c_ulong) }, Z_BUF_ERROR);
}

#[test]
fn params_copy_reset_pending() {
    let d = text(&mut Rng(13), 200_000);
    unsafe {
        let mut s = new_stream();
        init(&mut s, 1, 15);
        let mut out = vec![0u8; 400_000];
        s.next_in = d.as_ptr();
        s.avail_in = 100_000;
        s.next_out = out.as_mut_ptr();
        s.avail_out = out.len() as c_uint;
        assert_eq!(vz_deflate(&mut s, Z_NO_FLUSH), Z_OK);
        assert_eq!(vz_deflateParams(&mut s, 9, 0), Z_OK);
        let mut pending: c_uint = 0;
        let mut bits: c_int = 0;
        assert_eq!(vz_deflatePending(&mut s, &mut pending, &mut bits), Z_OK);
        assert!(bits < 8);
        // A copy finishes the same stream independently.
        let mut s2 = new_stream();
        assert_eq!(vz_deflateCopy(&mut s2, &mut s), Z_OK);
        let mut out2 = out.clone();
        let done = s.total_out as usize;
        s2.next_out = out2.as_mut_ptr().add(done);
        s2.next_in = d.as_ptr().add(100_000);
        s2.avail_in = 100_000;
        assert_eq!(vz_deflate(&mut s2, Z_FINISH), Z_STREAM_END);
        assert_eq!(zinflate(&out2[..s2.total_out as usize], 15).unwrap().0, d);
        assert_eq!(vz_deflateEnd(&mut s2), Z_OK);
        s.next_in = d.as_ptr().add(100_000);
        s.avail_in = 100_000;
        assert_eq!(vz_deflate(&mut s, Z_FINISH), Z_STREAM_END);
        assert_eq!(zinflate(&out[..s.total_out as usize], 15).unwrap().0, d);
        // Reset and reuse; ending early reports Z_DATA_ERROR as zlib does.
        assert_eq!(vz_deflateReset(&mut s), Z_OK);
        assert_eq!(s.total_in, 0);
        s.next_in = d.as_ptr();
        s.avail_in = 10;
        s.next_out = out.as_mut_ptr();
        s.avail_out = out.len() as c_uint;
        assert_eq!(vz_deflate(&mut s, Z_NO_FLUSH), Z_OK);
        assert_eq!(vz_deflateEnd(&mut s), Z_DATA_ERROR);
    }
}

/// Decompresses with zlib, 100 bytes of output at a time, so that matches
/// are copied from zlib's own window of `2^wbits` bytes. (With one big
/// output buffer zlib copies from the buffer and does not notice a match
/// from farther back.)
fn zinflate_windowed(data: &[u8], wbits: c_int) -> Option<Vec<u8>> {
    // zlib's own z_stream (the tests' copy of its layout).
    let mut s = unsafe { std::mem::zeroed() };
    let mut out = Vec::new();
    let mut ip = 0;
    unsafe {
        zinflate_init(&mut s, wbits);
        loop {
            let mut buf = [0u8; 100];
            let (r, used, made) = zinflate_step(&mut s, &data[ip..], &mut buf);
            ip += used;
            out.extend_from_slice(&buf[..made]);
            if r == 1 {
                zinflate_end(&mut s);
                return Some(out);
            }
            if r != 0 {
                zinflate_end(&mut s);
                return None;
            }
        }
    }
}

#[test]
fn matches_stay_inside_the_window() {
    // A block repeated at distances from 300 bytes to 30 KiB: with a
    // window of 2^wbits, only the nearer copies may be matched. zlib's
    // inflate, given the same windowBits, rejects any match from farther
    // back ("invalid distance too far back").
    let mut rng = Rng(21);
    let block: Vec<u8> = (0..200).map(|_| rng.next() as u8).collect();
    let mut d = Vec::new();
    for gap in [300, 700, 1500, 3000, 6000, 12_000, 30_000] {
        d.extend_from_slice(&block);
        d.extend((0..gap).map(|_| rng.next() as u8));
    }
    d.extend_from_slice(&block);
    for bits in 9..=15 {
        for wbits in [bits, -bits, bits + 16] {
            for level in [1, 4, 6, 9] {
                // One shot (the stream's first block is its last) and in
                // pieces.
                let mut s = new_stream();
                init(&mut s, level, wbits);
                let mut c = vec![0u8; d.len() * 2 + 100];
                unsafe {
                    s.next_in = d.as_ptr();
                    s.avail_in = d.len() as c_uint;
                    s.next_out = c.as_mut_ptr();
                    s.avail_out = c.len() as c_uint;
                    assert_eq!(vz_deflate(&mut s, Z_FINISH), Z_STREAM_END);
                    c.truncate(s.total_out as usize);
                    assert_eq!(vz_deflateEnd(&mut s), Z_OK);
                }
                let out = zinflate_windowed(&c, wbits);
                assert!(out.as_deref() == Some(&d[..]), "one shot: level {level} wbits {wbits}");
                let (c, _) = deflate_pieces(&d, level, wbits, &mut rng);
                let out = zinflate_windowed(&c, wbits);
                assert!(out.as_deref() == Some(&d[..]), "pieces: level {level} wbits {wbits}");
            }
        }
    }
}

/// Decompresses `c` with the system zlib, giving it `dict` when it asks
/// (zlib streams: `Z_NEED_DICT`) or up front (raw).
fn zinflate_dict(c: &[u8], wbits: c_int, dict: &[u8]) -> Vec<u8> {
    unsafe {
        let mut z: common::ZStream = std::mem::zeroed();
        common::zinflate_init(&mut z, wbits);
        if wbits < 0 {
            assert_eq!(common::inflateSetDictionary(&mut z, dict.as_ptr(), dict.len() as c_uint), 0);
        }
        let mut out = vec![0u8; 4_000_000];
        let (mut ip, mut op) = (0, 0);
        loop {
            let (r, used, n) = common::zinflate_step(&mut z, &c[ip..], &mut out[op..]);
            ip += used;
            op += n;
            match r {
                1 => break,
                2 => {
                    // Z_NEED_DICT: the header names the dictionary's Adler-32.
                    assert_eq!(z.adler, vz_adler32(1, dict.as_ptr(), dict.len() as c_uint));
                    assert_eq!(common::inflateSetDictionary(&mut z, dict.as_ptr(), dict.len() as c_uint), 0);
                },
                0 => assert!(used > 0 || n > 0, "zlib made no progress"),
                _ => panic!("zlib inflate returned {r}"),
            }
        }
        assert_eq!(ip, c.len());
        common::zinflate_end(&mut z);
        out.truncate(op);
        out
    }
}

/// Compresses `data` after `dict` (if any) in one `deflate(Z_FINISH)`, or in
/// pieces of `piece` bytes with no flush, then finishing.
fn deflate_with_dict(data: &[u8], dict: Option<&[u8]>, level: c_int, wbits: c_int, piece: usize) -> Vec<u8> {
    let mut s = new_stream();
    init(&mut s, level, wbits);
    let mut out = Vec::new();
    unsafe {
        if let Some(d) = dict {
            assert_eq!(vz_deflateSetDictionary(&mut s, d.as_ptr(), d.len() as c_uint), Z_OK);
            if wbits > 0 {
                assert_eq!(s.adler, vz_adler32(1, d.as_ptr(), d.len() as c_uint));
            }
        }
        let mut buf = vec![0u8; 1 << 16];
        let mut ip = 0;
        loop {
            let n = piece.min(data.len() - ip);
            let last = ip + n == data.len();
            s.next_in = data.as_ptr().add(ip);
            s.avail_in = n as c_uint;
            loop {
                s.next_out = buf.as_mut_ptr();
                s.avail_out = buf.len() as c_uint;
                let r = vz_deflate(&mut s, if last { Z_FINISH } else { Z_NO_FLUSH });
                out.extend_from_slice(&buf[..buf.len() - s.avail_out as usize]);
                if r == Z_STREAM_END {
                    break;
                }
                assert!(r == Z_OK || r == Z_BUF_ERROR, "deflate returned {r}");
                if !last && s.avail_in == 0 && s.avail_out > 0 {
                    break;
                }
            }
            ip += n;
            if last {
                break;
            }
        }
        // A dictionary once compression has begun is refused.
        if let Some(d) = dict {
            assert_eq!(vz_deflateSetDictionary(&mut s, d.as_ptr(), d.len() as c_uint), Z_STREAM_ERROR);
        }
        assert_eq!(vz_deflateEnd(&mut s), Z_OK);
    }
    out
}

#[test]
fn deflate_set_dictionary() {
    let mut rng = Rng(21);
    let base = text(&mut rng, 120_000);
    // Dictionaries shorter and longer than the window; data that repeats
    // the dictionary, so matches into it pay off, and data that does not.
    let dicts: Vec<Vec<u8>> = vec![b"q".to_vec(), base[..300].to_vec(), base[..20_000].to_vec(), base[..50_000].to_vec()];
    for dict in &dicts {
        let mut data = dict[dict.len().saturating_sub(5_000)..].to_vec();
        data.extend_from_slice(&text(&mut rng, 30_000));
        let datas = [Vec::new(), b"abc".to_vec(), data.clone(), (0..40_000).map(|_| rng.next() as u8).collect::<Vec<u8>>()];
        for d in &datas {
            for (level, wbits) in [(0, 15), (1, 15), (6, 15), (9, 15), (6, -15), (1, -15), (6, 12), (4, -9)] {
                for piece in [usize::MAX, 777] {
                    let c = deflate_with_dict(d, Some(dict), level, wbits, piece);
                    let back = zinflate_dict(&c, wbits, dict);
                    assert_eq!(back, *d, "dict {} level {level} wbits {wbits} piece {piece}", dict.len());
                    if wbits > 0 {
                        assert_eq!(c[1] & 0x20, 0x20, "FDICT not set");
                    }
                }
            }
        }
        // The matches into the dictionary make the output smaller.
        if dict.len() >= 20_000 {
            let with = deflate_with_dict(&data, Some(dict), 6, 15, usize::MAX);
            let without = deflate_with_dict(&data, None, 6, 15, usize::MAX);
            assert!(with.len() + 500 < without.len(), "{} vs {}", with.len(), without.len());
        }
    }
    // zlib's own dictionary streams decode to the same through vzlib.
    let dict = &dicts[2];
    let z = common::compress_ex(&base[10_000..60_000], 6, 15, 0, 0, Some(dict), std::ptr::null_mut());
    let mut s: ZStream = new_stream();
    unsafe {
        assert_eq!(vz_inflateInit_(&mut s, vz_zlibVersion(), std::mem::size_of::<ZStream>() as c_int), Z_OK);
        let mut out = vec![0u8; 100_000];
        s.next_in = z.as_ptr();
        s.avail_in = z.len() as c_uint;
        s.next_out = out.as_mut_ptr();
        s.avail_out = out.len() as c_uint;
        assert_eq!(vz_inflate(&mut s, Z_NO_FLUSH), Z_NEED_DICT);
        assert_eq!(vz_inflateSetDictionary(&mut s, dict.as_ptr(), dict.len() as c_uint), Z_OK);
        assert_eq!(vz_inflate(&mut s, Z_NO_FLUSH), Z_STREAM_END);
        assert_eq!(&out[..s.total_out as usize], &base[10_000..60_000]);
        vz_inflateEnd(&mut s);
    }
    // Gzip streams have no dictionaries; an empty one means none.
    let mut s = new_stream();
    init(&mut s, 6, 31);
    unsafe {
        assert_eq!(vz_deflateSetDictionary(&mut s, b"abc".as_ptr(), 3), Z_STREAM_ERROR);
        vz_deflateEnd(&mut s);
    }
    let c = deflate_with_dict(b"hello hello", Some(b""), 6, 15, usize::MAX);
    assert_eq!(c[1] & 0x20, 0);
    assert_eq!(zinflate(&c, 15).unwrap().0, b"hello hello");
}

#[test]
fn custom_gzip_header() {
    let data = text(&mut Rng(12), 30_000);
    let mut extra = b"AB\x02\x00hi".to_vec();
    let mut name = b"a.txt\0".to_vec();
    let mut comment = b"note\0".to_vec();
    let mut h = GzHeader {
        text: 1,
        time: 0x0102_0304,
        xflags: 0,
        os: 3,
        extra: extra.as_mut_ptr(),
        extra_len: extra.len() as c_uint,
        extra_max: 0,
        name: name.as_mut_ptr(),
        name_max: 0,
        comment: comment.as_mut_ptr(),
        comm_max: 0,
        hcrc: 1,
        done: 0,
    };
    for out_room in [1usize, 7, 1 << 20] {
        let mut s = new_stream();
        init(&mut s, 6, 31);
        let mut c = Vec::new();
        unsafe {
            assert_eq!(vz_deflateSetHeader(&mut s, &mut h), Z_OK);
            s.next_in = data.as_ptr();
            s.avail_in = data.len() as c_uint;
            loop {
                let mut buf = vec![0u8; out_room];
                s.next_out = buf.as_mut_ptr();
                s.avail_out = buf.len() as c_uint;
                let r = vz_deflate(&mut s, Z_FINISH);
                c.extend_from_slice(&buf[..out_room - s.avail_out as usize]);
                if r == Z_STREAM_END {
                    break;
                }
                assert!(r == Z_OK || r == Z_BUF_ERROR, "deflate returned {r}");
            }
            // Too late once the stream has started.
            assert_eq!(vz_deflateSetHeader(&mut s, &mut h), Z_STREAM_ERROR);
            vz_deflateEnd(&mut s);
        }
        let mut want = vec![31u8, 139, 8, 1 | 2 | 4 | 8 | 16, 4, 3, 2, 1, 0, 3, 6, 0];
        want.extend_from_slice(&extra);
        want.extend_from_slice(&name);
        want.extend_from_slice(&comment);
        let crc = unsafe { vz_crc32(0, want.as_ptr(), want.len() as c_uint) } as u16;
        want.extend_from_slice(&crc.to_le_bytes());
        assert_eq!(&c[..want.len()], &want[..]);
        assert_eq!(zinflate(&c, 31), Some((data.clone(), c.len())));
    }
    // Only gzip streams take a header.
    let mut s = new_stream();
    init(&mut s, 6, 15);
    unsafe {
        assert_eq!(vz_deflateSetHeader(&mut s, &mut h), Z_STREAM_ERROR);
        vz_deflateEnd(&mut s);
    }
}
