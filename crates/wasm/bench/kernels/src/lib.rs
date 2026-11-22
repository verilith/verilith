//! Benchmark kernels, compiled to wasm32 (see bench/README.md).
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

const N: usize = 1 << 22;
static mut BUF: [u8; N] = [0; N];
static mut WORDS: [u32; N / 4] = [0; N / 4];
static mut MAT: [f64; 3 * 256 * 256] = [0.0; 3 * 256 * 256];

/// Calls: naive recursive Fibonacci.
#[no_mangle]
pub extern "C" fn fib(n: i64) -> i64 {
    if n < 2 { n } else { fib(n - 1) + fib(n - 2) }
}

/// Loops and byte memory: primes below `n` (at most 4M), `reps` times.
#[no_mangle]
pub extern "C" fn sieve(n: u32, reps: u32) -> u32 {
    let n = (n as usize).min(N);
    let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
    let mut count = 0;
    for _ in 0..reps {
        buf[..n].fill(1);
        count = 0;
        let mut i = 2;
        while i < n {
            if buf[i] != 0 {
                count += 1;
                let mut j = i * i;
                while j < n {
                    buf[j] = 0;
                    j += i;
                }
            }
            i += 1;
        }
    }
    count
}

/// Floating point: `n`x`n` matrix product (n at most 256), `reps` times.
#[no_mangle]
pub extern "C" fn matmul(n: u32, reps: u32) -> f64 {
    let n = (n as usize).min(256);
    let m = unsafe { &mut *core::ptr::addr_of_mut!(MAT) };
    let (a, rest) = m.split_at_mut(256 * 256);
    let (b, c) = rest.split_at_mut(256 * 256);
    for i in 0..n * n {
        a[i] = (i % 7) as f64 * 0.5;
        b[i] = (i % 5) as f64 * 0.25;
    }
    let mut s = 0.0;
    for _ in 0..reps {
        for i in 0..n {
            for j in 0..n {
                let mut x = 0.0;
                for k in 0..n {
                    x += a[i * n + k] * b[k * n + j];
                }
                c[i * n + j] = x;
            }
        }
        for x in c[..n * n].iter() {
            s += *x;
        }
    }
    s
}

fn lcg(x: &mut u32) -> u32 {
    *x = x.wrapping_mul(1664525).wrapping_add(1013904223);
    *x
}

/// Integer compares and swaps: sorts `n` (at most 1M) pseudo-random words, `reps` times.
#[no_mangle]
pub extern "C" fn sort(n: u32, reps: u32) -> u32 {
    let n = (n as usize).min(N / 4);
    let w = unsafe { &mut *core::ptr::addr_of_mut!(WORDS) };
    let mut seed = 1;
    let mut s = 0u32;
    for _ in 0..reps {
        for x in w[..n].iter_mut() {
            *x = lcg(&mut seed);
        }
        w[..n].sort_unstable();
        s = s.wrapping_add(w[n / 2]);
    }
    s
}

/// Table lookups and shifts: CRC-32 of a 4 MiB buffer, `reps` times.
#[no_mangle]
pub extern "C" fn crc32(reps: u32) -> u32 {
    let mut table = [0u32; 256];
    for i in 0..256u32 {
        let mut c = i;
        for _ in 0..8 {
            c = if c & 1 != 0 { 0xedb88320 ^ (c >> 1) } else { c >> 1 };
        }
        table[i as usize] = c;
    }
    let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
    let mut seed = 7;
    for b in buf.iter_mut() {
        *b = lcg(&mut seed) as u8;
    }
    let mut crc = 0;
    for _ in 0..reps {
        crc = !0u32;
        for &b in buf.iter() {
            crc = table[((crc ^ b as u32) & 0xff) as usize] ^ (crc >> 8);
        }
        crc = !crc;
    }
    crc
}

/// 32-bit arithmetic: SHA-256 of a 4 MiB buffer, `reps` times.
#[no_mangle]
pub extern "C" fn sha256(reps: u32) -> u32 {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let buf = unsafe { &mut *core::ptr::addr_of_mut!(BUF) };
    let mut seed = 11;
    for b in buf.iter_mut() {
        *b = lcg(&mut seed) as u8;
    }
    let mut out: u32 = 0;
    for _ in 0..reps {
        let mut h: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
        ];
        for chunk in buf.chunks_exact(64) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([chunk[4 * i], chunk[4 * i + 1], chunk[4 * i + 2], chunk[4 * i + 3]]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
            }
            let mut v = h;
            for i in 0..64 {
                let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
                let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
                let t1 = v[7].wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
                let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
                let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
                let t2 = s0.wrapping_add(maj);
                v = [t1.wrapping_add(t2), v[0], v[1], v[2], v[3].wrapping_add(t1), v[4], v[5], v[6]];
            }
            for i in 0..8 {
                h[i] = h[i].wrapping_add(v[i]);
            }
        }
        out = out.rotate_left(5) ^ h[0];
    }
    out
}
