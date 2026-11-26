use verilith_core::cursor::Cursor;
use verilith_core::num::{parse_u64_dec, push_decimal};
use verilith_core::utf8::utf8_valid_scalar;

#[test]
fn cursor() {
    let buf = [1u8, 2, 3, 4, 5, 6, 7];
    let mut c = Cursor::new(&buf);
    assert_eq!(c.read_u8(), Some(1));
    assert_eq!(c.read_u16_be(), Some(0x0203));
    assert_eq!(c.peek_u8(), Some(4));
    assert_eq!(c.read_u32_be(), Some(0x0405_0607));
    assert_eq!(c.read_u8(), None);
    assert!(c.is_empty());
    let mut c = Cursor::new(&buf);
    assert_eq!(c.take(8), None);
    assert_eq!(c.position(), 0);
    let mut inner = c.split(3).unwrap();
    assert_eq!(inner.read_u16_be(), Some(0x0102));
    assert_eq!(inner.remaining(), 1);
    assert_eq!(c.slice_from(1), Some(&buf[1..3]));
    assert!(c.skip(4));
    assert!(!c.skip(1));
}

#[test]
fn utf8() {
    for s in ["", "abc", "é", "日本語", "😀", "\u{10FFFF}"] {
        assert!(utf8_valid_scalar(s.as_bytes(), 0));
    }
    for b in [&[0xC0u8, 0x80][..], &[0xED, 0xA0, 0x80], &[0xF4, 0x90, 0x80, 0x80], &[0xE2, 0x82], &[0x80]] {
        assert!(!utf8_valid_scalar(b, 0));
    }
    // Agrees with std on every 1-3 byte input over an interesting alphabet.
    let alpha = [0x00u8, 0x41, 0x7F, 0x80, 0x9F, 0xA0, 0xBF, 0xC0, 0xC2, 0xDF, 0xE0, 0xED, 0xEF, 0xF0, 0xF4, 0xF5, 0xFF];
    for &a in &alpha {
        for &b in &alpha {
            for &c in &alpha {
                for v in [vec![a], vec![a, b], vec![a, b, c]] {
                    assert_eq!(utf8_valid_scalar(&v, 0), std::str::from_utf8(&v).is_ok(), "{v:x?}");
                }
            }
        }
    }
}

#[test]
fn numbers() {
    assert_eq!(parse_u64_dec(b"x12345y", 1, 6), Some(12345));
    assert_eq!(parse_u64_dec(b"", 0, 0), Some(0));
    assert_eq!(parse_u64_dec(b"18446744073709551615", 0, 20), Some(u64::MAX));
    assert_eq!(parse_u64_dec(b"18446744073709551616", 0, 20), None);
    assert_eq!(parse_u64_dec(b"12a", 0, 3), None);
    let mut v = Vec::new();
    push_decimal(&mut v, 0);
    push_decimal(&mut v, 4294967295);
    assert_eq!(v, b"04294967295");
}

#[test]
fn alloc_u32_zeroed() {
    assert_eq!(verilith_core::prims::alloc_u32(0), Some(vec![]));
    let v = verilith_core::prims::alloc_u32(100_000).unwrap();
    assert_eq!(v.len(), 100_000);
    assert!(v.iter().all(|&x| x == 0));
    assert_eq!(verilith_core::prims::alloc_u32(usize::MAX), None);
}

#[test]
fn sparse_build_matches_build() {
    use verilith_core::htable::{build, build_sparse, reverse, reverse_fast, sparse_push};
    use vstd::prelude::Ghost;
    // The table-driven reversal against the loop, on every input it allows.
    for l in 1u32..=15 {
        for c in 0u32..(1 << l) {
            assert_eq!(reverse_fast(c, l), reverse(c, l).0);
        }
    }
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut some = 0;
    for round in 0..4000 {
        let n = 1 + (next() % 704) as usize;
        let mut lens = vec![0u8; n];
        if round % 2 == 0 {
            // A complete code: split leaves at random until there are enough.
            let want = 1 + (next() % n as u64) as usize;
            let mut leaves: Vec<u8> = vec![0];
            while leaves.len() < want {
                let i = (next() % leaves.len() as u64) as usize;
                if leaves[i] >= 15 {
                    break;
                }
                leaves[i] += 1;
                let d = leaves[i];
                leaves.push(d);
            }
            let mut at = 0;
            for d in leaves {
                at += (next() % 3) as usize;
                while at < n && lens[at] != 0 {
                    at += 1;
                }
                if at >= n {
                    at = lens.iter().position(|&x| x == 0).unwrap();
                }
                lens[at] = d;
            }
        } else {
            for x in lens.iter_mut() {
                *x = if next() % 4 == 0 { (next() % 16) as u8 } else { 0 };
            }
        }
        let mut used: Vec<(u16, u8)> = Vec::new();
        let mut cnts = [0u16; 16];
        for (i, &c) in lens.iter().enumerate() {
            if c != 0 {
                sparse_push(Ghost::assume_new(), i, &mut used, &mut cnts, c);
            }
        }
        for root in [1u32, 8, 10] {
            let a = build(&lens, root).0;
            let b = build_sparse(Ghost::assume_new(), n, &used, &cnts, root).0;
            assert_eq!(a.is_some(), b.is_some());
            if let (Some(a), Some(b)) = (a, b) {
                some += 1;
                assert_eq!(a.table, b.table);
                assert_eq!(a.tbits, b.tbits);
                assert_eq!(a.count, b.count);
                assert_eq!(a.first, b.first);
                assert_eq!(a.offs, b.offs);
                assert_eq!(a.sorted, b.sorted);
            }
        }
    }
    assert!(some > 3000);
}

#[test]
fn tail_appends() {
    use verilith_core::tail::Tail;
    let src: Vec<u8> = (0..300u32).map(|x| (x * 7 + 3) as u8).collect();
    for start in [0usize, 1, 15, 16, 17, 40, 200] {
        for n in 0..=100usize {
            // From a slice, at every distance from the slice's end.
            for i in [0usize, 1, 100, 300 - n, 299usize.saturating_sub(n), 268usize.saturating_sub(n)] {
                if i + n > src.len() {
                    continue;
                }
                let mut v: Vec<u8> = src[..start].to_vec();
                let mut want = v.clone();
                want.extend_from_slice(&src[i..i + n]);
                let mut t = Tail::take(&mut v, n + 32);
                assert!(v.is_empty());
                assert_eq!(t.len(), start);
                t.append_from(&src, i, n);
                if n <= 32 && i + 32 <= src.len() {
                    let mut v2 = Vec::new();
                    t.put_back(&mut v2);
                    assert_eq!(v2, want);
                    v2.truncate(start);
                    t = Tail::take(&mut v2, 32);
                    t.append_from32(&src, i, n);
                }
                t.put_back(&mut v);
                assert_eq!(v, want, "from start={start} n={n} i={i}");
            }
            // From the contents, at every offset back that does not overlap.
            for back in n.max(1)..=start {
                let s0 = start - back;
                let mut v: Vec<u8> = src[..start].to_vec();
                let mut want = v.clone();
                want.extend_from_within(s0..s0 + n);
                let mut t = Tail::take(&mut v, n + 32);
                t.append_within(s0, n);
                if n <= 32 && back >= 16 {
                    let mut v2 = Vec::new();
                    t.put_back(&mut v2);
                    assert_eq!(v2, want);
                    v2.truncate(start);
                    t = Tail::take(&mut v2, 32);
                    t.append_within32(s0, n);
                }
                t.put_back(&mut v);
                assert_eq!(v, want, "within start={start} n={n} back={back}");
            }
        }
    }
    // Many appends into one reservation.
    let mut v = Vec::new();
    let mut want = Vec::new();
    let mut t = Tail::take(&mut v, 10_000 + 32);
    for k in 0..100usize {
        t.append_from(&src, k, k);
        want.extend_from_slice(&src[k..2 * k]);
        if t.len() >= 2 * k {
            let s0 = t.len() - 2 * k;
            t.append_within(s0, k);
            want.extend_from_within(s0..s0 + k);
        }
    }
    t.put_back(&mut v);
    assert_eq!(v, want);
}

/// `lz::copy_match` against a byte-by-byte copy, for every offset, length
/// and amount of room after the match up to 40, and `copy_lits` and
/// `eq_len` against the obvious loops.
#[test]
fn lz_copies() {
    let mut seed = 0x1234_5678_9abc_def0u64;
    let mut rnd = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for off in 1..=40usize {
        for n in 0..=70usize {
            for room in [0usize, 1, 7, 8, 15, 16, 17, 31, 32, 40] {
                let op = 40;
                let total = op + n + room;
                let base: Vec<u8> = (0..total).map(|_| rnd() as u8).collect();
                let mut want = base.clone();
                for k in 0..n {
                    want[op + k] = want[op + k - off];
                }
                let mut got = base.clone();
                verilith_core::lz::copy_match(&mut got, op, off, n);
                assert_eq!(got[..op + n], want[..op + n], "off {off} n {n} room {room}");
            }
        }
    }
    for off in 8..=40usize {
        for n in 0..=24usize {
            let op = 40;
            let base: Vec<u8> = (0..op + 24 + 3).map(|_| rnd() as u8).collect();
            let mut want = base.clone();
            for k in 0..n {
                want[op + k] = want[op + k - off];
            }
            let mut got = base.clone();
            verilith_core::lz::copy_match24(&mut got, op, off, n);
            assert_eq!(got[..op + n], want[..op + n], "24: off {off} n {n}");
            assert_eq!(got[op + 24..], base[op + 24..]);
            if n <= 16 {
                let mut got = base.clone();
                verilith_core::lz::copy_match16(&mut got, op, off, n);
                assert_eq!(got[..op + n], want[..op + n], "16: off {off} n {n}");
                assert_eq!(got[op + 16..], base[op + 16..]);
            }
        }
    }
    // The 32-bytes-at-a-time copies: right for every offset and length,
    // and never more than 32 bytes past the end.
    for off in 16..=70usize {
        for n in (0..=100usize).chain([127, 128, 129, 191, 192, 193, 300]) {
            let op = 70;
            let base: Vec<u8> = (0..op + n + 32 + 5).map(|_| rnd() as u8).collect();
            let mut want = base.clone();
            for k in 0..n {
                want[op + k] = want[op + k - off];
            }
            let mut got = base.clone();
            verilith_core::lz::copy_match_wild(&mut got, op, off, n);
            assert_eq!(got[..op + n], want[..op + n], "wild: off {off} n {n}");
            assert_eq!(got[op + n + 32..], base[op + n + 32..]);
        }
    }
    for n in (0..=100usize).chain([127, 128, 129, 191, 192, 193, 300]) {
        let src: Vec<u8> = (0..7 + n + 32).map(|_| rnd() as u8).collect();
        let mut out: Vec<u8> = (0..9 + n + 32 + 5).map(|_| rnd() as u8).collect();
        let before = out.clone();
        verilith_core::lz::copy_lits_wild(&mut out, 9, &src, 7, n);
        assert_eq!(out[..9], before[..9]);
        assert_eq!(out[9..9 + n], src[7..7 + n], "wild literals: n {n}");
        assert_eq!(out[9 + n + 32..], before[9 + n + 32..]);
    }
    for n in (0..=70usize).chain([100, 191, 192, 193, 250, 1000]) {
        for room in [0usize, 5, 16, 20, 31, 32, 40] {
            for slack in [0usize, 5, 16, 20, 31, 32, 40] {
                let src: Vec<u8> = (0..7 + n + slack).map(|_| rnd() as u8).collect();
                let mut out: Vec<u8> = (0..9 + n + room).map(|_| rnd() as u8).collect();
                let before = out.clone();
                verilith_core::lz::copy_lits(&mut out, 9, &src, 7, n);
                assert_eq!(out[..9], before[..9]);
                assert_eq!(out[9..9 + n], src[7..7 + n], "literals: n {n} room {room} slack {slack}");
            }
        }
    }
    for same in 0..=40usize {
        for max in same..=41usize {
            let mut d: Vec<u8> = vec![7; 100];
            for i in 0..50 {
                d[i] = rnd() as u8;
                d[50 + i] = d[i];
            }
            if same < 50 {
                d[50 + same] = d[same] ^ 0x10;
            }
            let k = verilith_core::lz::eq_len(&d, 0, 50, max);
            assert_eq!(k, same.min(max));
        }
    }
    let b = [1u8, 2, 3, 4, 5];
    assert_eq!(verilith_core::lz::load32(&b, 1), 0x05040302);
}

/// The three-lane kernel against the table kernel, at every length around
/// its tier boundaries and from several starting registers. On AArch64 this
/// runs the `crc32x` instruction; elsewhere the lanes run over table code.

#[test]
fn picks() {
    use verilith_core::prims::{copy16_pick, pick};
    assert_eq!(pick(true, 3, 9), 3);
    assert_eq!(pick(false, 3, 9), 9);
    let input: Vec<u8> = (0..64u8).map(|x| x.wrapping_mul(7).wrapping_add(1)).collect();
    for dst in 16..40usize {
        for src_in in 0..40usize {
            // From the input; the other source is out of range on purpose.
            let mut out: Vec<u8> = (0..64u8).collect();
            let before = out.clone();
            copy16_pick(&mut out, dst, &input, src_in, usize::MAX - 3, true);
            for k in 0..64 {
                let want = if (dst..dst + 16).contains(&k) { input[k - dst + src_in] } else { before[k] };
                assert_eq!(out[k], want);
            }
        }
        for src_out in 0..=dst - 16 {
            // From earlier in the output; the input offset is out of range.
            let mut out: Vec<u8> = (0..64u8).map(|x| x ^ 0x5a).collect();
            let before = out.clone();
            copy16_pick(&mut out, dst, &input, usize::MAX - 3, src_out, false);
            for k in 0..64 {
                let want = if (dst..dst + 16).contains(&k) { before[k - dst + src_out] } else { before[k] };
                assert_eq!(out[k], want);
            }
        }
    }
}
