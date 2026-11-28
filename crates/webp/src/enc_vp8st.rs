//! Token statistics for the lossy encoder: the same walk over the levels
//! as the token writer, counting the bits each tree probability would
//! code, and the probabilities that code them in the fewest bits. Only
//! the size of the file depends on these choices.
use crate::vp8tables::*;
use vstd::prelude::*;

verus! {

/// `-log2(p / 256)` in 1/256 bits.
pub const COST: [u16; 256] = [
    0, 2048, 1792, 1642, 1536, 1454, 1386, 1329, 1280, 1236, 1198, 1162, 1130, 1101, 1073, 1048,
    1024, 1002, 980, 961, 942, 924, 906, 890, 874, 859, 845, 831, 817, 804, 792, 780,
    768, 757, 746, 735, 724, 714, 705, 695, 686, 676, 668, 659, 650, 642, 634, 626,
    618, 611, 603, 596, 589, 582, 575, 568, 561, 555, 548, 542, 536, 530, 524, 518,
    512, 506, 501, 495, 490, 484, 479, 474, 468, 463, 458, 453, 449, 444, 439, 434,
    430, 425, 420, 416, 412, 407, 403, 399, 394, 390, 386, 382, 378, 374, 370, 366,
    362, 358, 355, 351, 347, 343, 340, 336, 333, 329, 326, 322, 319, 315, 312, 309,
    305, 302, 299, 296, 292, 289, 286, 283, 280, 277, 274, 271, 268, 265, 262, 259,
    256, 253, 250, 247, 245, 242, 239, 236, 234, 231, 228, 226, 223, 220, 218, 215,
    212, 210, 207, 205, 202, 200, 197, 195, 193, 190, 188, 185, 183, 181, 178, 176,
    174, 171, 169, 167, 164, 162, 160, 158, 156, 153, 151, 149, 147, 145, 143, 140,
    138, 136, 134, 132, 130, 128, 126, 124, 122, 120, 118, 116, 114, 112, 110, 108,
    106, 104, 102, 101, 99, 97, 95, 93, 91, 89, 87, 86, 84, 82, 80, 78,
    77, 75, 73, 71, 70, 68, 66, 64, 63, 61, 59, 58, 56, 54, 53, 51,
    49, 48, 46, 44, 43, 41, 40, 38, 36, 35, 33, 32, 30, 28, 27, 25,
    24, 22, 21, 19, 18, 16, 15, 13, 12, 10, 9, 7, 6, 4, 3, 1,
];

fn inc(st: &mut Vec<u32>, i: usize, bit: bool)
    requires
        i < 1056,
        old(st)@.len() == 2112,
    ensures
        final(st)@.len() == 2112,
{
    let k = 2 * i + bit as usize;
    if st[k] < u32::MAX {
        st.set(k, st[k] + 1);
    }
}

fn pidx(t: usize, n: usize, ctx: usize) -> (r: usize)
    requires
        t < 4,
        n <= 16,
        ctx < 3,
    ensures
        r + 10 < 1056,
{
    let b = BANDS[n] as usize;
    ((t * 8 + b) * 3 + ctx) * 11
}

/// Counts block `b`'s tokens as `put_block` writes them; returns where
/// they end.
fn count_block(st: &mut Vec<u32>, t: usize, first: usize, ctx: usize, lv: &[i16], b: usize) -> (end: usize)
    requires
        old(st)@.len() == 2112,
        t < 4,
        first <= 1,
        ctx < 3,
        lv@.len() == 400,
        b < 25,
    ensures
        final(st)@.len() == 2112,
        end <= 16,
{
    let at = 16 * b;
    let mut last: usize = 16;
    while last > first && lv[at + last - 1] == 0
        invariant
            first <= last <= 16,
            at == 16 * b,
            b < 25,
            lv@.len() == 400,
        decreases last,
    {
        last = last - 1;
    }
    let mut n: usize = first;
    let mut c: usize = ctx;
    let mut ce: bool = true;
    while n < 16
        invariant
            first <= n <= 16,
            c < 3,
            t < 4,
            at == 16 * b,
            b < 25,
            lv@.len() == 400,
            st@.len() == 2112,
        decreases 16 - n,
    {
        let p = pidx(t, n, c);
        if ce && n >= last {
            inc(st, p, false);
            return n;
        }
        if ce {
            inc(st, p, true);
        }
        let v = lv[at + n];
        if v == 0 {
            inc(st, p + 1, false);
            c = 0;
        } else {
            inc(st, p + 1, true);
            let a: i32 = if v < 0 {
                -(v as i32)
            } else {
                v as i32
            };
            if a == 1 {
                inc(st, p + 2, false);
                c = 1;
            } else {
                inc(st, p + 2, true);
                if a <= 4 {
                    inc(st, p + 3, false);
                    inc(st, p + 4, a != 2);
                    if a != 2 {
                        inc(st, p + 5, a == 4);
                    }
                } else if a <= 10 {
                    inc(st, p + 3, true);
                    inc(st, p + 6, false);
                    inc(st, p + 7, a > 6);
                } else {
                    inc(st, p + 3, true);
                    inc(st, p + 6, true);
                    inc(st, p + 8, a > 34);
                    if a <= 34 {
                        inc(st, p + 9, a > 18);
                    } else {
                        inc(st, p + 10, a > 66);
                    }
                }
                c = 2;
            }
        }
        ce = v != 0;
        n = n + 1;
    }
    16
}

/// Counts a macroblock's tokens as `put_mb` writes them, with the same
/// context flags.
pub fn count_mb(st: &mut Vec<u32>, lv: &[i16], top: &mut Vec<bool>, left: &mut Vec<bool>)
    requires
        old(st)@.len() == 2112,
        lv@.len() == 400,
        old(top)@.len() == 9,
        old(left)@.len() == 9,
    ensures
        final(st)@.len() == 2112,
        final(top)@.len() == 9,
        final(left)@.len() == 9,
{
    let ctx = (if left[8] { 1usize } else { 0 }) + (if top[8] { 1usize } else { 0 });
    let end = count_block(st, 1, 0, ctx, lv, 24);
    top.set(8, end > 0);
    left.set(8, end > 0);
    let mut k: usize = 0;
    while k < 24
        invariant
            k <= 24,
            st@.len() == 2112,
            lv@.len() == 400,
            top@.len() == 9,
            left@.len() == 9,
        decreases 24 - k,
    {
        let (t, first, base, off, wd) = if k < 16 {
            (0usize, 1usize, 0usize, 0usize, 4usize)
        } else if k < 20 {
            (2, 0, 16, 4, 2)
        } else {
            (2, 0, 20, 6, 2)
        };
        let i = k - base;
        proof {
            if k < 16 {
                assert(i / 4 < 4 && i % 4 < 4);
            } else {
                assert(i < 4);
                assert(i / 2 < 2 && i % 2 < 2);
            }
        }
        let y = off + i / wd;
        let x = off + i % wd;
        let ctx = (if left[y] { 1usize } else { 0 }) + (if top[x] { 1usize } else { 0 });
        let end = count_block(st, t, first, ctx, lv, k);
        top.set(x, end > first);
        left.set(y, end > first);
        k = k + 1;
    }
}

fn cost(p: u8, n0: u32, n1: u32) -> (r: u64)
    ensures
        r <= 2 * 65535 * 0xffff_ffff,
{
    let c0 = COST[p as usize] as u64;
    let c1 = COST[255 - p as usize] as u64;
    proof {
        assert(c0 * (n0 as u64) <= 65535 * 0xffff_ffff) by (nonlinear_arith)
            requires
                c0 <= 65535,
        ;
        assert(c1 * (n1 as u64) <= 65535 * 0xffff_ffff) by (nonlinear_arith)
            requires
                c1 <= 65535,
        ;
    }
    c0 * n0 as u64 + c1 * n1 as u64
}

/// The token probabilities that code the counted bits in the fewest bits,
/// counting what each update costs.
pub fn best_probs(st: &Vec<u32>) -> (r: Vec<u8>)
    requires
        st@.len() == 2112,
    ensures
        r@.len() == 1056,
{
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < 1056
        invariant
            k <= 1056,
            out@.len() == k,
            st@.len() == 2112,
        decreases 1056 - k,
    {
        let n0 = st[2 * k];
        let n1 = st[2 * k + 1];
        let p0 = coeffs_proba0(k);
        let up = coeffs_update_proba(k);
        let tot = n0 as u64 + n1 as u64;
        let mut p = p0;
        if tot > 0 {
            proof {
                assert((n1 as int * 255) / (tot as int) <= 255) by (nonlinear_arith)
                    requires
                        n1 as int <= tot as int,
                        tot as int > 0,
                ;
            }
            let q = 255 - (n1 as u64 * 255) / tot;
            let np: u8 = if q < 1 {
                1
            } else {
                q as u8
            };
            let old = cost(p0, n0, n1) + cost(up, 1, 0);
            let new = cost(np, n0, n1) + cost(up, 0, 1) + 8 * 256;
            if new < old {
                p = np;
            }
        }
        out.push(p);
        k = k + 1;
    }
    out
}

} // verus!
