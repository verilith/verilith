//! Unverified prototype of a two-pass (simdjson-style) parser, to measure how
//! fast the design gets before proving it. Stage 1 finds structural
//! characters 64 bytes at a time; stage 2 walks them and builds the same tape
//! as the verified parser.
//!
//! `cargo run --release --example proto2 -- FILE...` checks that the tape
//! matches `verilith_json::parser::parse_document` and prints throughput. Build with
//! `RUSTFLAGS="-C target-cpu=native"`; `P512=1` uses AVX-512 for stage 1.
//! x86_64 with AVX2 only.
use std::arch::x86_64::*;
use std::time::Instant;
use verilith_json::parser::{ex_escape_end, Kind, Tok};

const SLOW_ESC: bool = false;
const CLMUL: bool = cfg!(target_feature = "pclmulqdq");

struct Stage1 {
    /// Positions of structural bytes: brackets, commas, colons, both quotes
    /// of each string, and the first byte of each scalar.
    idx: Vec<u32>,
    /// One word per 64-byte block: backslashes inside strings.
    bs: Vec<u64>,
    /// Offset of the first block (3 after a BOM).
    start: usize,
}

#[inline(always)]
fn prefix_xor(x: u64) -> u64 {
    if CLMUL {
        unsafe {
            let r = _mm_clmulepi64_si128(_mm_set_epi64x(0, x as i64), _mm_set1_epi8(-1), 0);
            _mm_cvtsi128_si64(r) as u64
        }
    } else {
        prefix_xor_shift(x)
    }
}

#[inline(always)]
fn prefix_xor_shift(mut x: u64) -> u64 {
    x ^= x << 1;
    x ^= x << 2;
    x ^= x << 4;
    x ^= x << 8;
    x ^= x << 16;
    x ^= x << 32;
    x
}

/// Characters escaped by a backslash, given the backslash mask and whether
/// the first byte is escaped by the previous block. Rare, so scalar.
#[inline(never)]
fn escaped_slow(bs: u64, prev: &mut u64) -> u64 {
    let mut esc = 0u64;
    let mut i = 0;
    let mut e = *prev != 0;
    while i < 64 {
        if e {
            esc |= 1 << i;
            e = false;
        } else if bs >> i & 1 == 1 {
            e = true;
        }
        i += 1;
    }
    *prev = e as u64;
    esc
}

#[inline(always)]
unsafe fn mm2(lo: __m256i, hi: __m256i) -> u64 {
    let mut m = (_mm256_movemask_epi8(lo) as u32 as u64) | ((_mm256_movemask_epi8(hi) as u32 as u64) << 32);
    // Opaque to LLVM, which otherwise turns later bit arithmetic on the mask
    // into per-bit vector code.
    core::arch::asm!("/* {0} */", inout(reg) m, options(pure, nomem, nostack));
    m
}

#[inline(always)]
unsafe fn eq2(lo: __m256i, hi: __m256i, c: u8) -> (__m256i, __m256i) {
    let k = _mm256_set1_epi8(c as i8);
    (_mm256_cmpeq_epi8(lo, k), _mm256_cmpeq_epi8(hi, k))
}

#[inline(always)]
unsafe fn or2(a: (__m256i, __m256i), b: (__m256i, __m256i)) -> (__m256i, __m256i) {
    (_mm256_or_si256(a.0, b.0), _mm256_or_si256(a.1, b.1))
}

#[target_feature(enable = "avx2")]
#[inline]
unsafe fn masks(p: *const u8) -> (u64, u64, u64, u64, u64) {
    let lo = _mm256_loadu_si256(p as *const __m256i);
    let hi = _mm256_loadu_si256(p.add(32) as *const __m256i);
    let q = eq2(lo, hi, b'"');
    let b = eq2(lo, hi, b'\\');
    let ws = or2(or2(eq2(lo, hi, 0x20), eq2(lo, hi, 0x0A)), or2(eq2(lo, hi, 0x0D), eq2(lo, hi, 0x09)));
    let k20 = _mm256_set1_epi8(0x20);
    let (flo, fhi) = (_mm256_or_si256(lo, k20), _mm256_or_si256(hi, k20));
    let op = or2(or2(eq2(flo, fhi, 0x7B), eq2(flo, fhi, 0x7D)), or2(eq2(lo, hi, 0x2C), eq2(lo, hi, 0x3A)));
    let k1f = _mm256_set1_epi8(0x1F);
    let ctrl = (
        _mm256_cmpeq_epi8(_mm256_max_epu8(lo, k1f), k1f),
        _mm256_cmpeq_epi8(_mm256_max_epu8(hi, k1f), k1f),
    );
    (mm2(q.0, q.1), mm2(b.0, b.1), mm2(ws.0, ws.1), mm2(op.0, op.1), mm2(ctrl.0, ctrl.1))
}

/// Escaped characters, branch-free (the odd-length-run trick).
#[inline(always)]
fn escaped_fast(bs: u64, prev: &mut u64) -> u64 {
    const ODD: u64 = 0xAAAAAAAAAAAAAAAA;
    if bs == 0 {
        let e = *prev;
        *prev = 0;
        return e;
    }
    let potential = bs & !*prev;
    let code = (((potential << 1) | ODD).wrapping_sub(potential)) ^ ODD;
    let escaped = code ^ (bs | *prev);
    let escape = code & bs;
    *prev = escape >> 63;
    escaped
}

/// Writes the positions of the set bits of `m` (plus `base`) to `w`, using
/// VBMI2 compress. May write up to 64 entries; the first `cnt` are valid.
#[target_feature(enable = "avx512bw,avx512vbmi2,avx512f")]
#[inline]
unsafe fn write512(w: *mut u32, m: u64, cnt: usize, base: u32) {
    let ids = _mm512_set_epi8(
        63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35,
        34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5,
        4, 3, 2, 1, 0,
    );
    let packed = _mm512_maskz_compress_epi8(m, ids);
    let b = _mm512_set1_epi32(base as i32);
    let q0 = _mm512_castsi512_si128(packed);
    _mm512_storeu_si512(w as *mut _, _mm512_add_epi32(_mm512_cvtepu8_epi32(q0), b));
    if cnt > 16 {
        let q1 = _mm512_extracti32x4_epi32::<1>(packed);
        _mm512_storeu_si512(w.add(16) as *mut _, _mm512_add_epi32(_mm512_cvtepu8_epi32(q1), b));
        if cnt > 32 {
            let q2 = _mm512_extracti32x4_epi32::<2>(packed);
            let q3 = _mm512_extracti32x4_epi32::<3>(packed);
            _mm512_storeu_si512(w.add(32) as *mut _, _mm512_add_epi32(_mm512_cvtepu8_epi32(q2), b));
            _mm512_storeu_si512(w.add(48) as *mut _, _mm512_add_epi32(_mm512_cvtepu8_epi32(q3), b));
        }
    }
}

#[target_feature(enable = "avx512bw")]
unsafe fn masks512(p: *const u8) -> (u64, u64, u64, u64, u64) {
    let v = _mm512_loadu_si512(p as *const _);
    let eq = |c: u8| _mm512_cmpeq_epi8_mask(v, _mm512_set1_epi8(c as i8));
    let q = eq(b'"');
    let b = eq(b'\\');
    let ws = eq(0x20) | eq(0x0A) | eq(0x0D) | eq(0x09);
    let f = _mm512_or_si512(v, _mm512_set1_epi8(0x20));
    let op = _mm512_cmpeq_epi8_mask(f, _mm512_set1_epi8(0x7B)) | _mm512_cmpeq_epi8_mask(f, _mm512_set1_epi8(0x7D)) | eq(0x2C) | eq(0x3A);
    let ctrl = _mm512_cmple_epu8_mask(v, _mm512_set1_epi8(0x1F));
    (q, b, ws, op, ctrl)
}

#[cfg_attr(not(prof), target_feature(enable = "avx2,avx512bw,avx512vbmi2,avx512f"))]
#[cfg_attr(prof, target_feature(enable = "avx2"))]
unsafe fn stage1_w<const USE512: bool>(s: &[u8], out: &mut Stage1) -> bool {
    out.idx.clear();
    out.bs.clear();
    out.idx.reserve(s.len() + 72);
    out.start = if s.starts_with(&[0xEF, 0xBB, 0xBF]) { 3 } else { 0 };
    let mut in_str = 0u64; // all ones if inside a string at the block start
    let mut prev_esc = 0u64;
    let mut prev_scalar = 0u64;
    let mut err = 0u64;
    let mut buf = [0x20u8; 64];
    let mut base = out.start;
    let mut idx_ptr = out.idx.as_mut_ptr();
    let idx_start = idx_ptr;
    while base < s.len() {
        let p = if s.len() - base >= 64 {
            s.as_ptr().add(base)
        } else {
            buf[..s.len() - base].copy_from_slice(&s[base..]);
            buf.as_ptr()
        };
        let (q, b, ws, op, ctrl) = if USE512 { masks512(p) } else { masks(p) };
        let esc = if SLOW_ESC { if b == 0 && prev_esc == 0 { 0 } else { escaped_slow(b, &mut prev_esc) } } else { escaped_fast(b, &mut prev_esc) };
        let uq = q & !esc;
        let r = prefix_xor(uq) ^ in_str;
        in_str = ((r as i64) >> 63) as u64;
        let inside = r & !uq; // string bodies
        err |= ctrl & inside;
        let strs = r | uq; // bodies plus both quotes
        let scalar = !(ws | op | strs);
        let starts = scalar & !((scalar << 1) | prev_scalar);
        prev_scalar = scalar >> 63;
        // Escape-starting backslashes are listed too, so stage 2 finds and
        // checks escapes without looking at the rest of the string.
        let mut st = (op & !strs) | uq | starts | (b & inside & !esc);
        // Write positions eight at a time; extra writes are overwritten.
        let cnt = st.count_ones() as usize;
        if USE512 {
            write512(idx_ptr, st, cnt, base as u32);
            idx_ptr = idx_ptr.add(cnt);
            base += 64;
            continue;
        }
        let mut w = idx_ptr;
        while st != 0 {
            for _ in 0..8 {
                *w = base as u32 + st.trailing_zeros();
                w = w.add(1);
                st &= st.wrapping_sub(1);
            }
        }
        idx_ptr = idx_ptr.add(cnt);
        base += 64;
        let _ = w;
    }
    let n = idx_ptr.offset_from(idx_start) as usize;
    out.idx.set_len(n);
    err == 0 && in_str == 0
}

static mut W512: bool = false;

unsafe fn stage1(s: &[u8], out: &mut Stage1) -> bool {
    if W512 { stage1_w::<true>(s, out) } else { stage1_w::<false>(s, out) }
}

#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Arr,
    Obj,
}

const DELIM: [bool; 256] = {
    let mut t = [false; 256];
    let mut i = 0;
    let d = b" \n\r\t,]}:[{\"";
    while i < d.len() {
        t[d[i] as usize] = true;
        i += 1;
    }
    t
};

#[inline(always)]
fn is_delim(s: &[u8], e: usize) -> bool {
    match s.get(e) {
        Some(&c) => DELIM[c as usize],
        None => true,
    }
}

/// Leading ASCII digits of the 8 bytes at `p` (fewer near the end).
#[inline(always)]
fn digits8(s: &[u8], p: usize) -> usize {
    if s.len() - p >= 8 {
        let w = u64::from_le_bytes(s[p..p + 8].try_into().unwrap());
        let a = w & 0x7F7F7F7F7F7F7F7F;
        let m = (a.wrapping_add(0x4646464646464646) | !((a | 0x8080808080808080).wrapping_sub(0x3030303030303030)) | w)
            & 0x8080808080808080;
        (m.trailing_zeros() / 8) as usize
    } else {
        s[p..].iter().take_while(|c| c.is_ascii_digit()).count()
    }
}

#[inline(always)]
fn digits(s: &[u8], mut p: usize) -> usize {
    loop {
        let d = digits8(s, p);
        p += d;
        if d < 8 {
            return p;
        }
    }
}

/// End of the number starting at `p`, if it is one.
#[inline(always)]
fn number_end(s: &[u8], p: usize) -> Option<usize> {
    let mut j = p + (s[p] == b'-') as usize;
    let d = if j < s.len() && s[j] == b'0' { j + 1 } else { digits(s, j) };
    if d == j {
        return None;
    }
    j = d;
    if j < s.len() && s[j] == b'.' {
        let d = digits(s, j + 1);
        if d == j + 1 {
            return None;
        }
        j = d;
    }
    if j < s.len() && (s[j] | 0x20) == b'e' {
        j += 1;
        if j < s.len() && (s[j] == b'+' || s[j] == b'-') {
            j += 1;
        }
        let d = digits(s, j);
        if d == j {
            return None;
        }
        j = d;
    }
    Some(j)
}


fn stage2(s: &[u8], st: &Stage1, toks: &mut Vec<Tok>, stack: &mut Vec<(Ctx, u32)>) -> bool {
    let idx = &st.idx[..];
    let n = idx.len();
    if n == 0 {
        return false;
    }
    if !s[st.start..idx[0] as usize].iter().all(|c| matches!(c, b' ' | b'\n' | b'\r' | b'\t')) {
        return false;
    }
    let blank = Tok { kind: Kind::Null, escaped: false, a: 0, b: 0, x: verilith_json::parser::NO };
    toks.clear();
    toks.reserve(n + 1);
    stack.clear();
    let mut t = 0usize;
    let mut k = 0usize;
    // Index n is a sentinel: reading it means running out of structurals.
    let at = |k: usize| -> u8 { if k < n { s[idx[k] as usize] } else { 0 } };
    // Open containers: tape index of the start token, with bit 31 set for
    // objects.
    let mut open = [0u32; 1001];
    let mut depth = 0usize;
    const OBJ: u32 = 1 << 31;
    macro_rules! emit {
        ($tok:expr) => {{
            toks.push($tok);
            t += 1;
        }};
    }
    macro_rules! string {
        ($kind:expr) => {{
            let p = idx[k - 1] as usize;
            if k >= n {
                return false;
            }
            let mut e = idx[k] as usize;
            k += 1;
            let mut any = false;
            // Escapes end here or later; a listed backslash before this was
            // consumed by the previous escape (a surrogate pair).
            let mut done = 0usize;
            while s[e] == b'\\' {
                any = true;
                if e >= done {
                    match ex_escape_end(s, e) {
                        Some(x) => done = x,
                        None => return false,
                    }
                }
                if k >= n {
                    return false;
                }
                e = idx[k] as usize;
                k += 1;
            }
            if done > e {
                return false;
            }
            emit!(Tok { kind: $kind, escaped: any, a: (p + 1) as u32, b: e as u32, x: verilith_json::parser::NO });
        }};
    }
    macro_rules! key {
        () => {{
            if at(k) != b'"' {
                return false;
            }
            k += 1;
            string!(Kind::Key);
            if at(k) != b':' {
                return false;
            }
            k += 1;
        }};
    }
    'value: loop {
        // A value is due.
        if k >= n {
            return false;
        }
        let p = idx[k] as usize;
        k += 1;
        match s[p] {
            b'{' => {
                if depth >= 1000 {
                    return false;
                }
                if at(k) == b'}' {
                    k += 1;
                    emit!(Tok { kind: Kind::ObjStart, a: t as u32 + 1, ..blank });
                    emit!(Tok { kind: Kind::ObjEnd, ..blank });
                } else {
                    open[depth] = t as u32 | OBJ;
                    depth += 1;
                    emit!(Tok { kind: Kind::ObjStart, ..blank });
                    key!();
                    continue 'value;
                }
            }
            b'[' => {
                if depth >= 1000 {
                    return false;
                }
                if at(k) == b']' {
                    k += 1;
                    emit!(Tok { kind: Kind::ArrStart, a: t as u32 + 1, ..blank });
                    emit!(Tok { kind: Kind::ArrEnd, ..blank });
                } else {
                    open[depth] = t as u32;
                    depth += 1;
                    emit!(Tok { kind: Kind::ArrStart, ..blank });
                    continue 'value;
                }
            }
            b'"' => string!(Kind::Str),
            b't' | b'f' | b'n' => {
                let (lit, kind): (&[u8], _) = match s[p] {
                    b't' => (b"true", Kind::True),
                    b'f' => (b"false", Kind::False),
                    _ => (b"null", Kind::Null),
                };
                if s.get(p..p + lit.len()) != Some(lit) || !is_delim(s, p + lit.len()) {
                    return false;
                }
                emit!(Tok { kind, ..blank });
            }
            _ => match number_end(s, p) {
                Some(e) if is_delim(s, e) => emit!(Tok { kind: Kind::Num, escaped: false, a: p as u32, b: e as u32, x: verilith_json::parser::NO }),
                _ => return false,
            },
        }
        // After a value: commas and closing brackets.
        loop {
            if depth == 0 {
                break 'value;
            }
            let top = open[depth - 1];
            let c = at(k);
            k += 1;
            if c == b',' {
                if top & OBJ != 0 {
                    key!();
                }
                continue 'value;
            }
            if c != (if top & OBJ != 0 { b'}' } else { b']' }) {
                return false;
            }
            depth -= 1;
            toks[(top & !OBJ) as usize].a = t as u32;
            emit!(Tok { kind: if top & OBJ != 0 { Kind::ObjEnd } else { Kind::ArrEnd }, ..blank });
        }
    }
    let _ = stack;
    k == n
}

pub fn main() {
    let mut st = Stage1 { idx: Vec::new(), bs: Vec::new(), start: 0 };
    let mut toks = Vec::new();
    let mut stack = Vec::new();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.first().map(|a| a == "--check").unwrap_or(false);
    if check {
        args.remove(0);
    }
    if args.first().map(|a| a == "--fuzz").unwrap_or(false) {
        args.remove(0);
        unsafe { W512 = std::env::var("P512").is_ok() };
        fuzz(&args, &mut st, &mut toks, &mut stack);
        return;
    }
    unsafe { W512 = std::env::var("P512").is_ok() };
    let mut disagree = 0;
    // Branch-free escapes agree with the scalar walk.
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let (mut pa, mut pb) = (0u64, 0u64);
    for _ in 0..(if std::env::var("ONCE").is_ok() || std::env::var("ONLY").is_ok() { 0 } else { 1_000_000 }) {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        let bs = x & (x >> 3) & (x >> 5); // sparse-ish, with runs
        let bs = if x & 1 == 0 { bs | (bs << 1) | (bs << 2) } else { bs };
        assert_eq!(escaped_fast(bs, &mut pa), escaped_slow(bs, &mut pb));
        assert_eq!(pa, pb);
    }
    for path in &args {
        let data = std::fs::read(path).unwrap();
        // Profiling modes: run one parser 3 times and nothing else.
        if std::env::var("ONLY").as_deref() == Ok("proto") {
            for _ in 0..3 {
                assert!(unsafe { stage1(&data, &mut st) } && stage2(&data, &st, &mut toks, &mut stack));
            }
            continue;
        }
        if std::env::var("ONLY").as_deref() == Ok("core") {
            let mut parser = verilith_json::Parser::new();
            for _ in 0..3 {
                assert!(parser.parse(&data).is_ok());
            }
            continue;
        }
        let ok = unsafe { stage1(&data, &mut st) } && stage2(&data, &st, &mut toks, &mut stack);
        let want = verilith_json::parser::parse_document(&data, true);
        let same = match (&want, ok) {
            (Ok((t, _)), true) => {
                t.toks.len() == toks.len()
                    && t.toks.iter().zip(&toks).all(|(x, y)| {
                        x.kind == y.kind
                            && x.escaped == y.escaped
                            && (matches!(x.kind, Kind::ArrEnd | Kind::ObjEnd | Kind::Null | Kind::True | Kind::False) || (x.a, x.b) == (y.a, y.b))
                    })
            }
            (Err(_), false) => true,
            _ => false,
        };
        if !same {
            disagree += 1;
            println!("DISAGREE {path}: core ok={} proto ok={ok}", want.is_ok());
        }
        if check {
            continue;
        }
        if std::env::var("ONCE").is_ok() {
            for _ in 0..3 {
                assert!(unsafe { stage1(&data, &mut st) } && stage2(&data, &st, &mut toks, &mut stack));
            }
            continue;
        }
        // Best of many short samples, alternating parsers, which is robust
        // to a noisy machine.
        let iters = (2_000_000 / data.len()).max(1);
        let (mut best2, mut best1, mut bestc, mut bestv) = (0f64, 0f64, 0f64, 0f64);
        let mut vidx = Vec::new();
        let mut parser = verilith_json::Parser::new();
        let rate = |t: Instant| data.len() as f64 * iters as f64 / t.elapsed().as_secs_f64() / 1e6;
        for _ in 0..200 {
            let t = Instant::now();
            for _ in 0..iters {
                let d = std::hint::black_box(&data);
                assert!(unsafe { stage1(d, &mut st) } && stage2(d, &st, &mut toks, &mut stack));
            }
            best2 = best2.max(rate(t));
            let t = Instant::now();
            for _ in 0..iters {
                assert!(unsafe { stage1(std::hint::black_box(&data), &mut st) });
            }
            best1 = best1.max(rate(t));
            let t = Instant::now();
            for _ in 0..iters {
                assert!(verilith_json::index::index(std::hint::black_box(&data), st.start, &mut vidx).1);
            }
            bestv = bestv.max(rate(t));
            let t = Instant::now();
            for _ in 0..iters {
                assert!(parser.parse(std::hint::black_box(&data)).is_ok());
            }
            bestc = bestc.max(rate(t));
        }
        assert!(vidx[..st.idx.len()] == st.idx[..]);
        println!("{path}: two-pass {best2:.0} MB/s (stage 1 alone {best1:.0}, verified stage 1 {bestv:.0}), core {bestc:.0} MB/s, {} structurals", st.idx.len());
    }
    println!("{disagree} disagreements");
}

fn same_tape(a: &[Tok], b: &[Tok]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| {
            x.kind == y.kind
                && x.escaped == y.escaped
                && (matches!(x.kind, Kind::ArrEnd | Kind::ObjEnd | Kind::Null | Kind::True | Kind::False) || (x.a, x.b) == (y.a, y.b))
        })
}

/// Mutates small inputs and checks that the prototype agrees with the
/// verified parser on acceptance and on the tape.
fn fuzz(paths: &[String], st: &mut Stage1, toks: &mut Vec<Tok>, stack: &mut Vec<(Ctx, u32)>) {
    let seeds: Vec<Vec<u8>> = paths.iter().map(|p| std::fs::read(p).unwrap()).filter(|d| d.len() < 300).collect();
    let alphabet = b"[]{},:\"\\ \t\n0123456789.eE+-utrfalsnUD8dDcC\x00\x1f\x7f\xc3\xa9\xff/bx";
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let mut rnd = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let (mut n, mut acc) = (0, 0);
    for _ in 0..2_000_000 {
        let mut d = seeds[(rnd() as usize) % seeds.len()].clone();
        for _ in 0..(1 + rnd() % 4) {
            let pos = if d.is_empty() { 0 } else { (rnd() as usize) % d.len() };
            let c = alphabet[(rnd() as usize) % alphabet.len()];
            match rnd() % 4 {
                0 if !d.is_empty() => d[pos] = c,
                1 => d.insert(pos, c),
                2 if !d.is_empty() => {
                    d.remove(pos);
                }
                _ => {
                    // Insert an escape sequence.
                    let esc: &[&[u8]] = &[b"\\u00e9", b"\\ud83d\\ude00", b"\\ud83d", b"\\ude00", b"\\\\", b"\\\"", b"\\n", b"\\uDFFF\\uD800", b"\\u12"];
                    let e = esc[(rnd() as usize) % esc.len()];
                    for (i, &b) in e.iter().enumerate() {
                        d.insert((pos + i).min(d.len()), b);
                    }
                }
            }
        }
        // Pad some inputs past a block boundary.
        if rnd() % 3 == 0 {
            let pad = (rnd() % 130) as usize;
            let at = (rnd() as usize) % (d.len() + 1);
            for _ in 0..pad {
                d.insert(at, b' ');
            }
        }
        let ok1 = unsafe { stage1(&d, st) };
        let mut vidx = Vec::new();
        let (vn, vok, _) = verilith_json::index::index(&d, st.start, &mut vidx);
        if vok != ok1 || vidx[..vn] != st.idx[..] {
            println!("STAGE1 DISAGREE ok {vok} vs {ok1}: {:?}", String::from_utf8_lossy(&d));
            std::process::exit(1);
        }
        // The prototype does not check UTF-8.
        let ok = ok1 && stage2(&d, st, toks, stack) && std::str::from_utf8(&d).is_ok();
        let want = verilith_json::parser::parse_document(&d, true);
        let mut t2 = verilith_json::parser::Tape::with_capacity(16);
        let r2 = verilith_json::stage2::parse2_into(&d, &mut t2, &mut vidx);
        let agree2 = match (&want, &r2) {
            (Ok((t, e)), Ok(e2)) => e == e2 && t.toks.len() == t2.toks.len() && same_tape(&t.toks, &t2.toks),
            (Err(_), Err(_)) => true,
            _ => false,
        };
        if !agree2 {
            println!("TWO-PASS DISAGREE: {:?}", String::from_utf8_lossy(&d));
            std::process::exit(1);
        }
        let agree = match (&want, ok) {
            (Ok((t, _)), true) => same_tape(&t.toks, toks),
            (Err(_), false) => true,
            _ => false,
        };
        if !agree {
            println!("DISAGREE core ok={} proto ok={ok}: {:?}", want.is_ok(), String::from_utf8_lossy(&d));
            std::process::exit(1);
        }
        n += 1;
        acc += ok as usize;
    }
    println!("{n} inputs, {acc} accepted, all agree");
}
