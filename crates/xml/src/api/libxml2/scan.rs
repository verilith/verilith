//! Byte scanners for the second pass over the tape: runs of libxml2's
//! "plain" character data, and the line ends and UTF-8 continuation bytes
//! that line and column tracking counts. SSE2 on x86-64 (always there),
//! eight bytes at a time elsewhere.

/// The bytes of libxml2's fast path for character data (`xmlParseCharData`):
/// tab, and 0x20 to 0x7F but for `<`, `&` and `]`.
#[inline]
pub fn plain_char(c: u8) -> bool {
    c == 0x09 || (0x20..0x80).contains(&c) && c != b'<' && c != b'&' && c != b']'
}

/// The first index from `i` whose byte is not `plain_char` (or `s.len()`).
#[inline]
pub fn plain_run(s: &[u8], mut i: usize) -> usize {
    let n = s.len();
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let lt = _mm_set1_epi8((0x20u8 ^ 0x80) as i8); // c < 0x20, compared signed after the flip
        let flip = _mm_set1_epi8(0x80u8 as i8);
        let (lab, amp, rsq, tab) = (_mm_set1_epi8(b'<' as i8), _mm_set1_epi8(b'&' as i8), _mm_set1_epi8(b']' as i8), _mm_set1_epi8(9));
        while i + 16 <= n {
            let v = _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i);
            // Signed compare of c ^ 0x80 against 0x20 ^ 0x80: c < 0x20 as
            // unsigned bytes; c >= 0x80 sets the sign bit, caught by movemask.
            let low = _mm_andnot_si128(_mm_cmpeq_epi8(v, tab), _mm_cmplt_epi8(_mm_xor_si128(v, flip), lt));
            let stop = _mm_or_si128(
                _mm_or_si128(low, v),
                _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, lab), _mm_cmpeq_epi8(v, amp)), _mm_cmpeq_epi8(v, rsq)),
            );
            let m = _mm_movemask_epi8(stop) as u32;
            if m != 0 {
                return i + m.trailing_zeros() as usize;
            }
            i += 16;
        }
    }
    while i < n && plain_char(s[i]) {
        i += 1;
    }
    i
}

/// `plain_run(&buf[..n], i)`, reading 16 bytes at a time while they are
/// in `buf`, past `n` as well.
#[inline]
pub fn plain_run_in(buf: &[u8], mut i: usize, n: usize) -> usize {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let lt = _mm_set1_epi8((0x20u8 ^ 0x80) as i8);
        let flip = _mm_set1_epi8(0x80u8 as i8);
        let (lab, amp, rsq, tab) = (_mm_set1_epi8(b'<' as i8), _mm_set1_epi8(b'&' as i8), _mm_set1_epi8(b']' as i8), _mm_set1_epi8(9));
        while i < n && i + 16 <= buf.len() {
            let v = _mm_loadu_si128(buf.as_ptr().add(i) as *const __m128i);
            let low = _mm_andnot_si128(_mm_cmpeq_epi8(v, tab), _mm_cmplt_epi8(_mm_xor_si128(v, flip), lt));
            let stop = _mm_or_si128(
                _mm_or_si128(low, v),
                _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, lab), _mm_cmpeq_epi8(v, amp)), _mm_cmpeq_epi8(v, rsq)),
            );
            let m = _mm_movemask_epi8(stop) as u32;
            if m != 0 {
                return (i + m.trailing_zeros() as usize).min(n);
            }
            i += 16;
        }
        if i >= n {
            return n;
        }
    }
    plain_run(&buf[..n], i)
}

/// Whether every byte of `s` is tab, line feed or 0x20 to 0x7F (what
/// libxml2's fast path for character data takes whole, `<` and `&` aside,
/// which a run of text does not hold), and whether every byte is a space
/// or a line feed.
#[inline]
pub fn text_class(s: &[u8]) -> (bool, bool) {
    text_class_in(s, 0, s.len())
}

/// `text_class(&buf[a..b])`; the last part of the run is read as the 16
/// bytes that end it when they are in `buf`, the bytes before `a` masked
/// out.
#[inline]
pub fn text_class_in(buf: &[u8], a: usize, b: usize) -> (bool, bool) {
    let s = &buf[a..b];
    let mut ws = true;
    let mut i = 0;
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let flip = _mm_set1_epi8(0x80u8 as i8);
        let lt = _mm_set1_epi8((0x20u8 ^ 0x80) as i8);
        let (tab, lf, sp) = (_mm_set1_epi8(9), _mm_set1_epi8(10), _mm_set1_epi8(32));
        // Bit k: byte k is outside tab, LF, 0x20..0x7F; and is not space or LF.
        let class = |v: __m128i| -> (u32, u32) {
            let tl = _mm_or_si128(_mm_cmpeq_epi8(v, tab), _mm_cmpeq_epi8(v, lf));
            let low = _mm_andnot_si128(tl, _mm_cmplt_epi8(_mm_xor_si128(v, flip), lt));
            let bad = _mm_movemask_epi8(_mm_or_si128(low, v)) as u32;
            let blank = _mm_movemask_epi8(_mm_or_si128(_mm_cmpeq_epi8(v, sp), _mm_cmpeq_epi8(v, lf))) as u32;
            (bad, !blank & 0xFFFF)
        };
        while i + 16 <= s.len() {
            let (bad, other) = class(_mm_loadu_si128(s.as_ptr().add(i) as *const __m128i));
            if bad != 0 {
                return (false, false);
            }
            if other != 0 {
                ws = false;
            }
            i += 16;
        }
        let r = s.len() - i;
        if r > 0 && b >= 16 {
            let (bad, other) = class(_mm_loadu_si128(buf.as_ptr().add(b - 16) as *const __m128i));
            let keep = 0xFFFFu32 << (16 - r) & 0xFFFF;
            if bad & keep != 0 {
                return (false, false);
            }
            return (true, ws && other & keep == 0);
        }
    }
    for &c in &s[i..] {
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
    let mut i = 0;
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let amp = _mm_set1_epi8(b'&' as i8);
        while i + 16 <= s.len() {
            let v = _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i);
            let m = _mm_movemask_epi8(_mm_cmpeq_epi8(v, amp)) as u32;
            if m != 0 {
                return Some(i + m.trailing_zeros() as usize);
            }
            i += 16;
        }
    }
    s[i..].iter().position(|&c| c == b'&').map(|k| i + k)
}

/// Whether `s` has no `&` and no byte below 0x20: an attribute value that
/// libxml2 passes as it is in the input (unless it is normalized).
#[inline]
pub fn att_plain(s: &[u8]) -> bool {
    let mut i = 0;
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let flip = _mm_set1_epi8(0x80u8 as i8);
        let lt = _mm_set1_epi8((0x20u8 ^ 0x80) as i8);
        let amp = _mm_set1_epi8(b'&' as i8);
        while i + 16 <= s.len() {
            let v = _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i);
            let bad = _mm_or_si128(_mm_cmplt_epi8(_mm_xor_si128(v, flip), lt), _mm_cmpeq_epi8(v, amp));
            if _mm_movemask_epi8(bad) != 0 {
                return false;
            }
            i += 16;
        }
    }
    s[i..].iter().all(|&c| c >= 0x20 && c != b'&')
}

#[cfg(target_arch = "x86_64")]
#[inline]
unsafe fn count16(s: &[u8], f: impl Fn(std::arch::x86_64::__m128i) -> std::arch::x86_64::__m128i, one: impl Fn(u8) -> bool) -> usize {
    use std::arch::x86_64::*;
    let mut n = 0usize;
    let mut i = 0;
    unsafe {
        while i + 16 <= s.len() {
            let v = _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i);
            n += (_mm_movemask_epi8(f(v)) as u32).count_ones() as usize;
            i += 16;
        }
    }
    n + s[i..].iter().filter(|&&c| one(c)).count()
}

/// Bytes of `b` equal to `\n`.
#[inline]
pub fn count_newlines(b: &[u8]) -> usize {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        count16(b, |v| _mm_cmpeq_epi8(v, _mm_set1_epi8(b'\n' as i8)), |c| c == b'\n')
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
    unsafe {
        use std::arch::x86_64::*;
        // c & 0xC0 == 0x80: as a signed byte, c < -64 (0x80..0xBF).
        count16(b, |v| _mm_cmplt_epi8(v, _mm_set1_epi8(-64)), |c| c & 0xC0 == 0x80)
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
    let mut v = Vec::with_capacity(s.len() / 32);
    let mut hi = 0u32;
    let mut i = 0;
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let nl = _mm_set1_epi8(b'\n' as i8);
        while i + 16 <= s.len() {
            let x = _mm_loadu_si128(s.as_ptr().add(i) as *const __m128i);
            hi |= _mm_movemask_epi8(x) as u32;
            let mut m = _mm_movemask_epi8(_mm_cmpeq_epi8(x, nl)) as u32;
            while m != 0 {
                v.push(i + m.trailing_zeros() as usize);
                m &= m - 1;
            }
            i += 16;
        }
    }
    for (k, &c) in s[i..].iter().enumerate() {
        hi |= (c >> 7) as u32;
        if c == b'\n' {
            v.push(i + k);
        }
    }
    (v, hi == 0)
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
