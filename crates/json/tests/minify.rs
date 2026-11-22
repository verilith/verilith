//! `cJSON_Minify` (the verified `minify::minify_in_place`) against a
//! direct port of cJSON 1.7.19's `cJSON_Minify`, on random text made of the
//! bytes that matter to it.
#![cfg(feature = "cjson")]
use std::os::raw::c_char;

/// cJSON's minify, ported as it is.
fn reference(input: &[u8]) -> Vec<u8> {
    let mut p = input.to_vec();
    p.push(0);
    let (mut i, mut o) = (0usize, 0usize);
    while p[i] != 0 {
        match p[i] {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b'/' if p[i + 1] == b'/' => {
                i += 2;
                while p[i] != 0 {
                    let c = p[i];
                    i += 1;
                    if c == b'\n' {
                        break;
                    }
                }
            }
            b'/' if p[i + 1] == b'*' => {
                i += 2;
                while p[i] != 0 {
                    if p[i] == b'*' && p[i + 1] == b'/' {
                        i += 2;
                        break;
                    }
                    i += 1;
                }
            }
            b'/' => i += 1,
            b'"' => {
                p[o] = b'"';
                i += 1;
                o += 1;
                while p[i] != 0 {
                    let c = p[i];
                    p[o] = c;
                    if c == b'"' {
                        i += 1;
                        o += 1;
                        break;
                    }
                    if c == b'\\' && p[i + 1] == b'"' {
                        p[o + 1] = b'"';
                        i += 1;
                        o += 1;
                    }
                    i += 1;
                    o += 1;
                }
            }
            c => {
                p[o] = c;
                i += 1;
                o += 1;
            }
        }
    }
    p.truncate(o);
    p
}

#[test]
fn minify_matches_cjson() {
    let alphabet = b" \t\r\n/*\"\\ax{}:,1";
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    for _ in 0..200_000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        let n = (x % 24) as usize;
        let mut s = Vec::with_capacity(n + 1);
        let mut y = x;
        for _ in 0..n {
            y = y.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s.push(alphabet[(y >> 33) as usize % alphabet.len()]);
        }
        let want = reference(&s);
        let mut buf = s.clone();
        buf.push(0);
        unsafe { verilith_json::ffi::cJSON_Minify(buf.as_mut_ptr() as *mut c_char) };
        let end = buf.iter().position(|&b| b == 0).unwrap();
        assert_eq!(&buf[..end], &want[..], "input {:?}", String::from_utf8_lossy(&s));
    }
}
