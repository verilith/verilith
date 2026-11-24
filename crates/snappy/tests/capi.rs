//! The C API against the system libsnappy's (loaded with `dlopen`): the
//! same status and the same lengths for every call.
mod common;
use common::{sample, sizes, Rng, Snappy, KINDS};
use std::ffi::c_char;
use verilith_snappy::capi;

/// `snappy_uncompress` through our API: the status and the length left
/// in the length argument.
fn our_uncompress(src: &[u8], out: &mut [u8]) -> Result<usize, i32> {
    let mut n = out.len();
    let r = unsafe { capi::uncompress(src.as_ptr() as *const c_char, src.len(), out.as_mut_ptr() as *mut c_char, &mut n) };
    if r == 0 {
        Ok(n)
    } else {
        Err(r)
    }
}

fn our_length(src: &[u8]) -> Option<usize> {
    let mut n = 0;
    let r = unsafe { capi::uncompressed_length_c(src.as_ptr() as *const c_char, src.len(), &mut n) };
    (r == 0).then_some(n)
}

fn our_validate(src: &[u8]) -> bool {
    unsafe { capi::validate_compressed_buffer(src.as_ptr() as *const c_char, src.len()) == 0 }
}

#[test]
fn compress_and_uncompress() {
    let Some(l) = Snappy::load() else {
        eprintln!("libsnappy not found: skipped");
        return;
    };
    let mut rng = Rng(0x9e3779b97f4a7c15);
    // 2^33, or on 32-bit targets the largest usize.
    for n in [0usize, 1, 5, 6, 100, 65536, 1 << 20, 0xffff_ffff, (1u64 << 33).min(usize::MAX as u64) as usize] {
        assert_eq!(unsafe { capi::max_compressed_length_c(n) }, l.max_len(n), "max length {n}");
    }
    for size in sizes() {
        for kind in 0..KINDS {
            let input = sample(&mut rng, size, kind);
            let cap = l.max_len(size);
            // Compress: enough room is OK, one byte less is "too small".
            let mut c = vec![0xAAu8; cap + 8];
            let mut n = cap;
            let r = unsafe { capi::compress(input.as_ptr() as *const c_char, size, c.as_mut_ptr() as *mut c_char, &mut n) };
            assert_eq!(r, 0, "size {size} kind {kind}");
            assert!(c[cap..].iter().all(|&b| b == 0xAA));
            c.truncate(n);
            assert_eq!(l.uncompress(&c).as_deref(), Some(&input[..]), "size {size} kind {kind}");
            let mut small = cap - 1;
            let mut d = vec![0u8; cap];
            let r = unsafe { capi::compress(input.as_ptr() as *const c_char, size, d.as_mut_ptr() as *mut c_char, &mut small) };
            assert_eq!(r, 2);
            // Uncompress what libsnappy wrote: room to spare, exact, short.
            let c = l.compress(&input);
            assert_eq!(our_length(&c), Some(size));
            assert!(our_validate(&c));
            for cap in [size + 50, size, size.saturating_sub(1 + rng.below(9))] {
                let mut a = vec![0xAAu8; cap + 8];
                let mut b = vec![0xAAu8; cap + 8];
                let x = our_uncompress(&c, &mut a[..cap]);
                let y = l.uncompress_into(&c, &mut b[..cap]);
                assert_eq!(x, y, "size {size} kind {kind} cap {cap}");
                if cap >= size {
                    assert_eq!(x, Ok(size));
                    assert_eq!(&a[..size], &input[..]);
                    // Nothing after the result is touched.
                    assert!(a[size..].iter().all(|&b| b == 0xAA), "size {size} kind {kind} cap {cap}");
                } else {
                    assert_eq!(x, Err(2));
                }
            }
        }
    }
}

#[test]
fn corrupted_agree() {
    let Some(l) = Snappy::load() else {
        eprintln!("libsnappy not found: skipped");
        return;
    };
    let mut rng = Rng(0xbf58476d1ce4e5b9);
    let (mut ok, mut bad) = (0, 0);
    for round in 0..40000 {
        let size = [0usize, 3, 20, 300, 5000, 70000][round % 6];
        let input = sample(&mut rng, size, round % KINDS);
        let mut c = l.compress(&input);
        for _ in 0..1 + rng.below(2) {
            let at = rng.below(c.len());
            match rng.below(4) {
                0 => c[at] ^= 1 << rng.below(8),
                1 => c[at] = rng.next() as u8,
                2 => c.truncate(at),
                _ => c.insert(at, rng.next() as u8),
            }
            if c.is_empty() {
                break;
            }
        }
        // The same length, the same verdict, the same status and bytes.
        let len = our_length(&c);
        assert_eq!(len, l.uncompressed_length(&c), "round {round}");
        assert_eq!(our_validate(&c), l.validate(&c), "round {round}");
        let cap = match len {
            Some(n) if n <= 1 << 24 => n + rng.below(3),
            Some(_) => 100,
            None => 100,
        };
        let cap = if rng.below(8) == 0 { cap.saturating_sub(1 + rng.below(4)) } else { cap };
        let mut a = vec![0u8; cap];
        let mut b = vec![0u8; cap];
        let x = our_uncompress(&c, &mut a);
        let y = l.uncompress_into(&c, &mut b);
        assert_eq!(x, y, "round {round}");
        if let Ok(n) = x {
            assert_eq!(a[..n], b[..n], "round {round}");
            assert!(our_validate(&c), "round {round}");
            ok += 1;
        } else {
            bad += 1;
        }
    }
    eprintln!("accepted by both {ok}, refused by both {bad}");
}
