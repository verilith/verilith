//! Verified scalar implementations of the NEON-only `ops` functions, the
//! oracle for `tests/neon.rs` (with `crate::refs` for the shared ones).
use crate::lanes::*;
use crate::ops::*;
#[allow(unused_imports)]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

pub fn ref_shr8(a: &[u8], n: u32) -> (r: Vec<u8>)
    requires
        1 <= n <= 8,
    ensures
        r@ == shr8(a@, n as int),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost p = pow2_spec(n as nat);
    proof {
        reveal_with_fuel(pow2_spec, 9);
        assert(p == if n == 1 { 2nat } else if n == 2 { 4 } else if n == 3 { 8 } else if n == 4 { 16 } else if n == 5 {
            32
        } else if n == 6 { 64 } else if n == 7 { 128 } else { 256 });
    }
    let d: u32 = if n == 1 { 2 } else if n == 2 { 4 } else if n == 3 { 8 } else if n == 4 { 16 } else if n == 5 {
        32
    } else if n == 6 { 64 } else if n == 7 { 128 } else { 256 };
    while i < a.len()
        invariant
            i <= a@.len(),
            r@.len() == i,
            d as nat == p,
            p == pow2_spec(n as nat),
            d >= 2,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] shr8(a@, n as int)[j],
        decreases a.len() - i,
    {
        r.push((a[i] as u32 / d) as u8);
        i = i + 1;
    }
    assert(r@ =~= shr8(a@, n as int));
    r
}

pub fn ref_abd_u8(a: &[u8], b: &[u8]) -> (r: Vec<u8>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == abd_u8(a@, b@),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] abd_u8(a@, b@)[j],
        decreases a.len() - i,
    {
        let v = if a[i] >= b[i] { a[i] - b[i] } else { b[i] - a[i] };
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= abd_u8(a@, b@));
    r
}

/// One lane of `sra8`.
fn sra1(b: u8, n: u32) -> (v: u8)
    requires
        1 <= n <= 8,
    ensures
        v as int == (s8(b) / pow2_spec(n as nat) as int) % 256,
{
    let ghost p = pow2_spec(n as nat);
    proof {
        reveal_with_fuel(pow2_spec, 9);
    }
    // The signed byte plus 256 is not negative, 256 is a multiple of
    // `d`, and so the quotient is the floor plus `256 / d`.
    let x: i32 = if b < 128 { b as i32 } else { b as i32 - 256 };
    let q: i32 = if n == 1 {
        (x + 256) / 2 - 128
    } else if n == 2 {
        (x + 256) / 4 - 64
    } else if n == 3 {
        (x + 256) / 8 - 32
    } else if n == 4 {
        (x + 256) / 16 - 16
    } else if n == 5 {
        (x + 256) / 32 - 8
    } else if n == 6 {
        (x + 256) / 64 - 4
    } else if n == 7 {
        (x + 256) / 128 - 2
    } else {
        (x + 256) / 256 - 1
    };
    proof {
        assert(x == s8(b));
        if n == 1 {
            assert(p == 2 && q == (x as int) / 2);
        } else if n == 2 {
            assert(p == 4 && q == (x as int) / 4);
        } else if n == 3 {
            assert(p == 8 && q == (x as int) / 8);
        } else if n == 4 {
            assert(p == 16 && q == (x as int) / 16);
        } else if n == 5 {
            assert(p == 32 && q == (x as int) / 32);
        } else if n == 6 {
            assert(p == 64 && q == (x as int) / 64);
        } else if n == 7 {
            assert(p == 128 && q == (x as int) / 128);
        } else {
            assert(p == 256 && q == (x as int) / 256);
        }
        assert(q == (x as int) / (p as int));
        assert(-128 <= q <= 127);
    }
    if q < 0 { (q + 256) as u8 } else { q as u8 }
}

pub fn ref_sra8(a: &[u8], n: u32) -> (r: Vec<u8>)
    requires
        1 <= n <= 8,
    ensures
        r@ == sra8(a@, n as int),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            r@.len() == i,
            1 <= n <= 8,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] sra8(a@, n as int)[j],
        decreases a.len() - i,
    {
        r.push(sra1(a[i], n));
        i = i + 1;
    }
    assert(r@ =~= sra8(a@, n as int));
    r
}

pub fn ref_tbl1(t: &[u8], idx: &[u8]) -> (r: Vec<u8>)
    requires
        t@.len() == 16,
    ensures
        r@ == tbl1(t@, idx@),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < idx.len()
        invariant
            t@.len() == 16,
            i <= idx@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] tbl1(t@, idx@)[j],
        decreases idx.len() - i,
    {
        let k = idx[i];
        r.push(if k < 16 { t[k as usize] } else { 0 });
        i = i + 1;
    }
    assert(r@ =~= tbl1(t@, idx@));
    r
}

pub fn ref_uzp1_8(a: &[u8], b: &[u8]) -> (r: Vec<u8>)
    requires
        a@.len() == b@.len(),
        a@.len() % 2 == 0,
        a@.len() <= 0x1000_0000,
    ensures
        r@ == uzp1_8(a@, b@),
{
    let n = a.len();
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len(),
            a@.len() == b@.len(),
            n % 2 == 0,
            n <= 0x1000_0000,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] uzp1_8(a@, b@)[j],
        decreases n - i,
    {
        r.push(if i < n / 2 { a[2 * i] } else { b[2 * i - n] });
        i = i + 1;
    }
    assert(r@ =~= uzp1_8(a@, b@));
    r
}

/// The largest element and an index where it occurs (the specs of `vmaxvq`).
pub fn ref_max8(a: &[u8]) -> (r: u8)
    requires
        a@.len() > 0,
    ensures
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i] <= r,
        exists|i: int| 0 <= i < a@.len() && #[trigger] a@[i] == r,
{
    let mut m = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= m,
            exists|j: int| 0 <= j < i && #[trigger] a@[j] == m,
        decreases a.len() - i,
    {
        if a[i] > m {
            m = a[i];
        }
        i = i + 1;
    }
    m
}

pub fn ref_max16(a: &[u16]) -> (r: u16)
    requires
        a@.len() > 0,
    ensures
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i] <= r,
        exists|i: int| 0 <= i < a@.len() && #[trigger] a@[i] == r,
{
    let mut m = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] <= m,
            exists|j: int| 0 <= j < i && #[trigger] a@[j] == m,
        decreases a.len() - i,
    {
        if a[i] > m {
            m = a[i];
        }
        i = i + 1;
    }
    m
}

pub fn ref_padd8(a: &[u8], b: &[u8]) -> (r: Vec<u8>)
    requires
        a@.len() == b@.len(),
        a@.len() % 2 == 0,
        a@.len() <= 0x1000_0000,
    ensures
        r@ == padd8(a@, b@),
{
    let n = a.len();
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len(),
            a@.len() == b@.len(),
            n % 2 == 0,
            n <= 0x1000_0000,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] padd8(a@, b@)[j],
        decreases n - i,
    {
        let v = if i < n / 2 {
            ((a[2 * i] as u16 + a[2 * i + 1] as u16) % 256) as u8
        } else {
            ((b[2 * i - n] as u16 + b[2 * i - n + 1] as u16) % 256) as u8
        };
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= padd8(a@, b@));
    r
}

pub fn ref_mullo8(a: &[u8], b: &[u8]) -> (r: Vec<u8>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == mullo8(a@, b@),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mullo8(a@, b@)[j],
        decreases a.len() - i,
    {
        let (x, y) = (a[i], b[i]);
        proof {
            assert(x * y <= u8::MAX * u8::MAX) by (nonlinear_arith)
                requires
                    x <= u8::MAX,
                    y <= u8::MAX,
            ;
        }
        let v = ((x as u32 * y as u32) % 256) as u8;
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= mullo8(a@, b@));
    r
}

pub fn ref_mullo32(a: &[u32], b: &[u32]) -> (r: Vec<u32>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == mullo32(a@, b@),
{
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mullo32(a@, b@)[j],
        decreases a.len() - i,
    {
        let (x, y) = (a[i], b[i]);
        proof {
            assert(x * y <= u32::MAX * u32::MAX) by (nonlinear_arith)
                requires
                    x <= u32::MAX,
                    y <= u32::MAX,
            ;
        }
        let v = ((x as u64 * y as u64) % 0x1_0000_0000) as u32;
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= mullo32(a@, b@));
    r
}

pub fn ref_paddl8(a: &[u8]) -> (r: Vec<u16>)
    requires
        a@.len() % 2 == 0,
    ensures
        r@ == paddl8(a@),
{
    let n = a.len() / 2;
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len() / 2,
            a@.len() % 2 == 0,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] paddl8(a@)[j],
        decreases n - i,
    {
        let v = a[2 * i] as u16 + a[2 * i + 1] as u16;
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= paddl8(a@));
    r
}

pub fn ref_paddl16(a: &[u16]) -> (r: Vec<u32>)
    requires
        a@.len() % 2 == 0,
    ensures
        r@ == paddl16(a@),
{
    let n = a.len() / 2;
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len() / 2,
            a@.len() % 2 == 0,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] paddl16(a@)[j],
        decreases n - i,
    {
        let v = a[2 * i] as u32 + a[2 * i + 1] as u32;
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= paddl16(a@));
    r
}

pub fn ref_paddl32(a: &[u32]) -> (r: Vec<u64>)
    requires
        a@.len() % 2 == 0,
    ensures
        r@ == paddl32(a@),
{
    let n = a.len() / 2;
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len() / 2,
            a@.len() % 2 == 0,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] paddl32(a@)[j],
        decreases n - i,
    {
        let v = a[2 * i] as u64 + a[2 * i + 1] as u64;
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= paddl32(a@));
    r
}

// ---------------------------------------------------------------------------
// Integer transforms
// ---------------------------------------------------------------------------

pub fn ref_abs16(a: &[u16]) -> (r: Vec<u16>)
    ensures
        r@ == abs16(a@),
{
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] abs16(a@)[j],
        decreases a.len() - i,
    {
        r.push(if a[i] <= 0x8000 { a[i] } else { (0x10000u32 - a[i] as u32) as u16 });
        i = i + 1;
    }
    assert(r@ =~= abs16(a@));
    r
}

pub fn ref_max_u16(a: &[u16], b: &[u16]) -> (r: Vec<u16>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == max_u16(a@, b@),
{
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] max_u16(a@, b@)[j],
        decreases a.len() - i,
    {
        r.push(if a[i] >= b[i] { a[i] } else { b[i] });
        i = i + 1;
    }
    assert(r@ =~= max_u16(a@, b@));
    r
}

/// `x mod 2^32` of a value within 2^32 of zero.
fn wrap32e(x: i64) -> (r: u32)
    requires
        -0x1_0000_0000 <= x < 0x1_0000_0000,
    ensures
        r as int == x % 0x1_0000_0000,
{
    if x < 0 {
        proof {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(x as int, 0x1_0000_0000);
            vstd::arithmetic::div_mod::lemma_small_mod((x + 0x1_0000_0000) as nat, 0x1_0000_0000);
        }
        (x + 0x1_0000_0000) as u32
    } else {
        proof {
            vstd::arithmetic::div_mod::lemma_small_mod(x as nat, 0x1_0000_0000);
        }
        x as u32
    }
}

/// The signed product of two 16-bit lanes, as a 32-bit lane.
fn smul1(x: u16, y: u16) -> (r: u32)
    ensures
        r as int == (s16(x) * s16(y)) % 0x1_0000_0000,
{
    let (sx, sy) = (crate::refs::s16e(x) as i64, crate::refs::s16e(y) as i64);
    assert(-0x4000_0000 <= sx * sy <= 0x4000_0000) by (nonlinear_arith)
        requires
            -0x8000 <= sx < 0x8000,
            -0x8000 <= sy < 0x8000,
    ;
    wrap32e(sx * sy)
}

pub fn ref_mull_lo_s16(a: &[u16], b: &[u16]) -> (r: Vec<u32>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == mull_lo_s16(a@, b@),
{
    let n = a.len() / 2;
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a@.len() == b@.len(),
            n == a@.len() / 2,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mull_lo_s16(a@, b@)[j],
        decreases n - i,
    {
        r.push(smul1(a[i], b[i]));
        i = i + 1;
    }
    assert(r@ =~= mull_lo_s16(a@, b@));
    r
}

pub fn ref_mull_hi_s16(a: &[u16], b: &[u16]) -> (r: Vec<u32>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == mull_hi_s16(a@, b@),
{
    let n = a.len() / 2;
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a@.len() == b@.len(),
            n == a@.len() / 2,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mull_hi_s16(a@, b@)[j],
        decreases n - i,
    {
        r.push(smul1(a[n + i], b[n + i]));
        i = i + 1;
    }
    assert(r@ =~= mull_hi_s16(a@, b@));
    r
}

/// `2^n` for `n <= 31`.
fn pow2i(n: u32) -> (r: i64)
    requires
        n <= 31,
    ensures
        r as nat == pow2_spec(n as nat),
        1 <= r <= 0x8000_0000,
{
    let mut p: i64 = 1;
    let mut k: u32 = 0;
    while k < n
        invariant
            k <= n <= 31,
            p as nat == pow2_spec(k as nat),
            1 <= p,
            p <= 0x8000_0000,
            k < 31 ==> p <= 0x4000_0000,
        decreases n - k,
    {
        proof {
            reveal_with_fuel(pow2_spec, 2);
            lemma_pow2i_bound(k as nat);
            lemma_pow2i_bound((k + 1) as nat);
        }
        p = p * 2;
        k = k + 1;
    }
    p
}

proof fn lemma_pow2i_bound(k: nat)
    requires
        k <= 31,
    ensures
        pow2_spec(k) <= 0x8000_0000,
        k < 31 ==> pow2_spec(k) <= 0x4000_0000,
{
    reveal_with_fuel(pow2_spec, 33);
}

/// One lane of `rshr_s32`.
fn rshr1(x: u32, n: u32) -> (r: u32)
    requires
        1 <= n <= 31,
    ensures
        r as int == ((s32(x) + pow2_spec((n - 1) as nat)) / pow2_spec(n as nat) as int) % 0x1_0000_0000,
{
    let h = pow2i(n - 1);
    let p = pow2i(n);
    let y = crate::refs::s32e(x) + h;
    let k: i64 = 0x8000_0000;
    assert(0 <= k * p <= 0x8000_0000 * 0x8000_0000) by (nonlinear_arith)
        requires
            1 <= p <= 0x8000_0000,
            k == 0x8000_0000,
    ;
    assert(0 <= y + k * p && y + k * p < 3 * k * p) by (nonlinear_arith)
        requires
            -0x8000_0000 <= y < 0x1_0000_0000,
            1 <= p,
            k == 0x8000_0000,
    ;
    let z = y + k * p;
    let q0 = z / p;
    proof {
        vstd::arithmetic::div_mod::lemma_hoist_over_denominator(y as int, k as int, p as nat);
        assert(q0 == y as int / p as int + k);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(z as int, p as int);
        assert(0 <= q0 < 3 * k) by (nonlinear_arith)
            requires
                z == p * q0 + (z % p),
                0 <= z % p < p,
                0 <= z,
                z < 3 * k * p,
                p >= 1,
        ;
    }
    wrap32e(q0 - k)
}

pub fn ref_rshr_s32(a: &[u32], n: u32) -> (r: Vec<u32>)
    requires
        1 <= n <= 31,
    ensures
        r@ == rshr_s32(a@, n as int),
{
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            1 <= n <= 31,
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] rshr_s32(a@, n as int)[j],
        decreases a.len() - i,
    {
        r.push(rshr1(a[i], n));
        i = i + 1;
    }
    assert(r@ =~= rshr_s32(a@, n as int));
    r
}

pub fn ref_uzp2_16(a: &[u16], b: &[u16]) -> (r: Vec<u16>)
    requires
        a@.len() == b@.len(),
        a@.len() % 2 == 0,
        a@.len() <= 0x1000_0000,
    ensures
        r@ == uzp2_16(a@, b@),
{
    let n = a.len();
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len(),
            a@.len() == b@.len(),
            n % 2 == 0,
            n <= 0x1000_0000,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] uzp2_16(a@, b@)[j],
        decreases n - i,
    {
        r.push(if i < n / 2 { a[2 * i + 1] } else { b[2 * i + 1 - n] });
        i = i + 1;
    }
    assert(r@ =~= uzp2_16(a@, b@));
    r
}


pub fn ref_interleave3(a: &[u8], b: &[u8], c: &[u8]) -> (r: Vec<u8>)
    requires
        a@.len() == b@.len(),
        a@.len() == c@.len(),
        a@.len() <= 0x1000_0000,
    ensures
        r@ == interleave3(a@, b@, c@),
{
    let n = a.len();
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 3 * n
        invariant
            n == a@.len(),
            a@.len() == b@.len(),
            a@.len() == c@.len(),
            n <= 0x1000_0000,
            i <= 3 * n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] interleave3(a@, b@, c@)[j],
        decreases 3 * n - i,
    {
        r.push(if i % 3 == 0 { a[i / 3] } else if i % 3 == 1 { b[i / 3] } else { c[i / 3] });
        i = i + 1;
    }
    assert(r@ =~= interleave3(a@, b@, c@));
    r
}

// ---------------------------------------------------------------------------
// The 16-bit inverse DCT
// ---------------------------------------------------------------------------

pub fn ref_mull_lo_lane_s16(a: &[u16], c: &[u16], l: usize) -> (r: Vec<u32>)
    requires
        l < c@.len(),
    ensures
        r@ == mull_lo_lane_s16(a@, c@, l as int),
{
    let n = a.len() / 2;
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            l < c@.len(),
            n == a@.len() / 2,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mull_lo_lane_s16(a@, c@, l as int)[j],
        decreases n - i,
    {
        r.push(smul1(a[i], c[l]));
        i = i + 1;
    }
    assert(r@ =~= mull_lo_lane_s16(a@, c@, l as int));
    r
}

pub fn ref_mull_hi_lane_s16(a: &[u16], c: &[u16], l: usize) -> (r: Vec<u32>)
    requires
        l < c@.len(),
    ensures
        r@ == mull_hi_lane_s16(a@, c@, l as int),
{
    let n = a.len() / 2;
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            l < c@.len(),
            n == a@.len() / 2,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mull_hi_lane_s16(a@, c@, l as int)[j],
        decreases n - i,
    {
        r.push(smul1(a[n + i], c[l]));
        i = i + 1;
    }
    assert(r@ =~= mull_hi_lane_s16(a@, c@, l as int));
    r
}

/// `acc` plus the signed product of two 16-bit lanes, as a 32-bit lane.
fn smla1(acc: u32, x: u16, y: u16) -> (r: u32)
    ensures
        r as int == (acc + s16(x) * s16(y)) % 0x1_0000_0000,
{
    let (sx, sy) = (crate::refs::s16e(x) as i64, crate::refs::s16e(y) as i64);
    assert(-0x4000_0000 <= sx * sy <= 0x4000_0000) by (nonlinear_arith)
        requires
            -0x8000 <= sx < 0x8000,
            -0x8000 <= sy < 0x8000,
    ;
    let t = acc as i64 + sx * sy;
    if t >= 0x1_0000_0000 {
        proof {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(t - 0x1_0000_0000, 0x1_0000_0000);
        }
        wrap32e(t - 0x1_0000_0000)
    } else {
        wrap32e(t)
    }
}

pub fn ref_mlal_lo_lane_s16(acc: &[u32], a: &[u16], c: &[u16], l: usize) -> (r: Vec<u32>)
    requires
        l < c@.len(),
        acc@.len() <= a@.len(),
    ensures
        r@ == mlal_lo_lane_s16(acc@, a@, c@, l as int),
{
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < acc.len()
        invariant
            l < c@.len(),
            acc@.len() <= a@.len(),
            i <= acc@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mlal_lo_lane_s16(acc@, a@, c@, l as int)[j],
        decreases acc.len() - i,
    {
        r.push(smla1(acc[i], a[i], c[l]));
        i = i + 1;
    }
    assert(r@ =~= mlal_lo_lane_s16(acc@, a@, c@, l as int));
    r
}

pub fn ref_mlal_hi_lane_s16(acc: &[u32], a: &[u16], c: &[u16], l: usize) -> (r: Vec<u32>)
    requires
        l < c@.len(),
        2 * acc@.len() <= a@.len(),
    ensures
        r@ == mlal_hi_lane_s16(acc@, a@, c@, l as int),
{
    let n = acc.len();
    let al = a.len();
    let mut r: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            l < c@.len(),
            n == acc@.len(),
            al == a@.len(),
            2 * n <= al,
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] mlal_hi_lane_s16(acc@, a@, c@, l as int)[j],
        decreases n - i,
    {
        r.push(smla1(acc[i], a[n + i], c[l]));
        i = i + 1;
    }
    assert(r@ =~= mlal_hi_lane_s16(acc@, a@, c@, l as int));
    r
}

pub fn ref_rshrn_s32(a: &[u32], n: u32) -> (r: Vec<u16>)
    requires
        1 <= n <= 16,
    ensures
        r@ == rshrn_s32(a@, n as int),
{
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            1 <= n <= 16,
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] rshrn_s32(a@, n as int)[j],
        decreases a.len() - i,
    {
        let w = rshr1(a[i], n);
        proof {
            let q = (s32(a@[i as int]) + pow2_spec((n - 1) as nat)) / pow2_spec(n as nat) as int;
            vstd::arithmetic::div_mod::lemma_mod_mod(q, 0x1_0000, 0x1_0000);
        }
        r.push((w % 0x1_0000) as u16);
        i = i + 1;
    }
    assert(r@ =~= rshrn_s32(a@, n as int));
    r
}

pub fn ref_adds_u16(a: &[u16], b: &[u16]) -> (r: Vec<u16>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == adds_u16(a@, b@),
{
    let mut r: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == #[trigger] adds_u16(a@, b@)[j],
        decreases a.len() - i,
    {
        let v = if a[i] as u32 + b[i] as u32 > 0xffff { 0xffffu16 } else { a[i] + b[i] };
        r.push(v);
        i = i + 1;
    }
    assert(r@ =~= adds_u16(a@, b@));
    r
}

pub fn ref_sum_u16(a: &[u16]) -> (r: u64)
    requires
        a@.len() <= 0x1_0000,
    ensures
        r as int == sum_u16(a@),
{
    let mut r: u64 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() <= 0x1_0000,
            i <= a@.len(),
            r as int == sum_u16(a@.take(i as int)),
            r <= 0xffff * i,
        decreases a.len() - i,
    {
        proof {
            assert(a@.take(i + 1).drop_last() =~= a@.take(i as int));
        }
        r = r + a[i] as u64;
        i = i + 1;
    }
    assert(a@.take(a@.len() as int) =~= a@);
    r
}

} // verus!
