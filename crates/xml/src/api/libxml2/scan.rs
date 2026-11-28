//! Byte scanners for the second pass over the tape: runs of libxml2's
//! "plain" character data, and the line ends and UTF-8 continuation bytes
//! that line and column tracking counts. On x86-64 these are the verified
//! SSE2 scans in `crate::lscan` (through verilith-simd); elsewhere, eight
//! bytes at a time in plain Rust.

/// The bytes of libxml2's fast path for character data (`xmlParseCharData`):
/// tab, and 0x20 to 0x7F but for `<`, `&` and `]`.
#[inline]
pub fn plain_char(c: u8) -> bool {
    c == 0x09 || (0x20..0x80).contains(&c) && c != b'<' && c != b'&' && c != b']'
}

/// The first index from `i` whose byte is not `plain_char` (or `s.len()`).
#[inline]
pub fn plain_run(s: &[u8], i: usize) -> usize {
    if i >= s.len() {
        return i;
    }
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::plain_run(s, i)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let mut i = i;
        while i < s.len() && plain_char(s[i]) {
            i += 1;
        }
        i
    }
}

/// `plain_run(&buf[..n], i)`, reading 16 bytes at a time while they are
/// in `buf`, past `n` as well.
#[inline]
pub fn plain_run_in(buf: &[u8], i: usize, n: usize) -> usize {
    assert!(n <= buf.len());
    if i >= n {
        return n;
    }
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::plain_run_in(buf, i, n)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        plain_run(&buf[..n], i)
    }
}

/// Whether every byte of `s` is tab, line feed or 0x20 to 0x7F (what
/// libxml2's fast path for character data takes whole, `<` and `&` aside,
/// which a run of text does not hold), and whether every byte is a space
/// or a line feed.
#[inline]
pub fn text_class(s: &[u8]) -> (bool, bool) {
    text_class_in(s, 0, s.len())
}

/// `text_class(&buf[a..b])`; on x86-64 the last part of the run is read as
/// the 16 bytes that end it when they are in `buf`, the bytes before `a`
/// masked out.
#[inline]
pub fn text_class_in(buf: &[u8], a: usize, b: usize) -> (bool, bool) {
    assert!(a <= b && b <= buf.len());
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::text_class_in(buf, a, b)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let mut ws = true;
        for &c in &buf[a..b] {
            if c == b' ' || c == b'\n' {
                continue;
            }
            if !(c == 9 || (0x20..0x80).contains(&c)) {
                return (false, false);
            }
            ws = false;
        }
        (true, ws)
    }
}

/// The first `:` in `s`: names are short, so a word at a time and no
/// call.
#[inline(always)]
pub fn colon(s: &[u8]) -> Option<usize> {
    const ONES: u64 = 0x0101_0101_0101_0101;
    let n = s.len();
    let mut i = 0;
    while i + 8 <= n {
        let w = u64::from_le_bytes(s[i..i + 8].try_into().unwrap()) ^ (ONES * b':' as u64);
        // The lowest set bit is at the first zero byte of `w`.
        let z = w.wrapping_sub(ONES) & !w & (ONES << 7);
        if z != 0 {
            return Some(i + z.trailing_zeros() as usize / 8);
        }
        i += 8;
    }
    while i < n {
        if s[i] == b':' {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// The first `&` in `s`.
#[inline]
pub fn find_amp(s: &[u8]) -> Option<usize> {
    let (q, _) = verilith_simd::find::find_byte(s, 0, b'&');
    if q < s.len() {
        Some(q)
    } else {
        None
    }
}

/// Whether `s` has no `&` and no byte below 0x20: an attribute value that
/// libxml2 passes as it is in the input (unless it is normalized).
#[inline]
pub fn att_plain(s: &[u8]) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::att_plain(s)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        s.iter().all(|&c| c >= 0x20 && c != b'&')
    }
}

/// Bytes of `b` equal to `\n`.
#[inline]
pub fn count_newlines(b: &[u8]) -> usize {
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::count_newlines(b)
    }
    #[cfg(not(target_arch = "x86_64"))]
    count_where(b, |w| {
        let x = w ^ 0x0A0A_0A0A_0A0A_0A0A;
        !(((x & 0x7F7F_7F7F_7F7F_7F7F).wrapping_add(0x7F7F_7F7F_7F7F_7F7F)) | x | 0x7F7F_7F7F_7F7F_7F7F)
    }, |c| c == b'\n')
}

/// UTF-8 continuation bytes (`10xxxxxx`) in `b`.
#[inline]
pub fn count_continuations(b: &[u8]) -> usize {
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::count_continuations(b)
    }
    #[cfg(not(target_arch = "x86_64"))]
    count_where(b, |w| w & !(w << 1) & 0x8080_8080_8080_8080, |c| c & 0xC0 == 0x80)
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn count_where(b: &[u8], mask: impl Fn(u64) -> u64, one: impl Fn(u8) -> bool) -> usize {
    let mut c = b.chunks_exact(8);
    let mut n = 0usize;
    for w in &mut c {
        n += (mask(u64::from_le_bytes(w.try_into().unwrap())) & 0x8080_8080_8080_8080).count_ones() as usize;
    }
    n + c.remainder().iter().filter(|&&x| one(x)).count()
}

/// The offsets of every `\n` in `s`, and whether `s` is all ASCII.
pub fn line_index(s: &[u8]) -> (Vec<usize>, bool) {
    #[cfg(target_arch = "x86_64")]
    {
        crate::lscan::line_index(s)
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let mut v = Vec::with_capacity(s.len() / 32);
        let mut hi = 0u32;
        for (k, &c) in s.iter().enumerate() {
            hi |= (c >> 7) as u32;
            if c == b'\n' {
                v.push(k);
            }
        }
        (v, hi == 0)
    }
}

/// The line and column after `run`, starting from `line` and `col`
/// (columns count characters, from 1).
#[inline]
pub fn advance(run: &[u8], mut line: i32, mut col: i32) -> (i32, i32) {
    if run.len() < 16 {
        for &c in run {
            if c == b'\n' {
                line += 1;
                col = 1;
            } else {
                col += (c & 0xC0 != 0x80) as i32;
            }
        }
        return (line, col);
    }
    match count_newlines(run) {
        0 => (line, col + (run.len() - count_continuations(run)) as i32),
        nl => {
            let last = run.iter().rposition(|&c| c == b'\n').unwrap_or(0);
            let tail = &run[last + 1..];
            (line + nl as i32, 1 + (tail.len() - count_continuations(tail)) as i32)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scanners_match_bytewise() {
        let mut x: u64 = 0x1234_5678_9abc_def1;
        for len in 0..200 {
            for _ in 0..20 {
                let s: Vec<u8> = (0..len)
                    .map(|_| {
                        x ^= x << 13;
                        x ^= x >> 7;
                        x ^= x << 17;
                        // Mostly plain text, some of every kind of stop.
                        [b'a', b' ', b'\t', b'\n', b'\r', b'<', b'&', b']', 0x7F, 0x80, 0xC3, 0xBF, 0x01, b'z', b'0', b'.'][(x % 16) as usize]
                    })
                    .collect();
                for i in 0..=len {
                    let want = (i..len).find(|&k| !plain_char(s[k])).unwrap_or(len);
                    assert_eq!(plain_run(&s, i), want);
                    for m in i..=len {
                        assert_eq!(plain_run_in(&s, i, m), want.min(m));
                    }
                }
                assert_eq!(find_amp(&s), s.iter().position(|&c| c == b'&'));
                for a in 0..=len.min(20) {
                    let r: Vec<u8> = s[a..].iter().map(|&c| if c == b'&' { b':' } else { c }).collect();
                    assert_eq!(colon(&r), r.iter().position(|&c| c == b':'));
                }
                assert_eq!(att_plain(&s), s.iter().all(|&c| c >= 0x20 && c != b'&'));
                let ok = s.iter().all(|&c| c == 9 || c == 10 || (0x20..0x80).contains(&c));
                let ws = s.iter().all(|&c| c == b' ' || c == b'\n');
                assert_eq!(text_class(&s), if ok { (true, ws) } else { (false, false) });
                // Text that is mostly plain, cut at every place.
                let t: Vec<u8> = s.iter().map(|&c| if c == 0x80 || c == b'\r' { c } else if c & 1 == 0 { b' ' } else if c & 2 == 0 { b'\n' } else { b'a' }).collect();
                for a in 0..=len.min(40) {
                    for b in a..=len {
                        let r = &t[a..b];
                        let ok = r.iter().all(|&c| c == 9 || c == 10 || (0x20..0x80).contains(&c));
                        let ws = r.iter().all(|&c| c == b' ' || c == b'\n');
                        assert_eq!(text_class_in(&t, a, b), if ok { (true, ws) } else { (false, false) });
                    }
                }
                assert_eq!(count_newlines(&s), s.iter().filter(|&&c| c == b'\n').count());
                assert_eq!(count_continuations(&s), s.iter().filter(|&&c| c & 0xC0 == 0x80).count());
                let (mut l, mut c) = (1, 1);
                for &b in &s {
                    if b == b'\n' {
                        l += 1;
                        c = 1;
                    } else if b & 0xC0 != 0x80 {
                        c += 1;
                    }
                }
                assert_eq!(advance(&s, 1, 1), (l, c));
                let (nl, ascii) = line_index(&s);
                assert_eq!(nl, (0..len).filter(|&k| s[k] == b'\n').collect::<Vec<_>>());
                assert_eq!(ascii, s.iter().all(|&b| b < 0x80));
            }
        }
    }
}
