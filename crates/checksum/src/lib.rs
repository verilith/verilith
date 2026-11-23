#![doc = include_str!("../README.md")]
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
#![cfg_attr(not(feature = "std"), no_std)]
// Adler-32 (RFC 1950), CRC-32 (RFC 1952) and CRC-32C (RFC 3720), proven
// to compute `spec::adler32`, `spec::crc32` and `spec::crc32c`.
//
// [`adler32`], [`crc32`] and [`crc32c()`] pick the fastest kernel this CPU
// has (see [`cpu`]); [`adler32_update`], [`crc32_update`] and
// [`crc32c_update`] are the portable verified kernels.
pub mod adlerv;
pub mod cpu;
pub mod fold;
pub mod crc32c;
pub mod lanes;
pub mod spec;
mod tables;

pub use crc32c::{crc32c, crc32c_update};
use tables::*;
#[cfg(verus_only)]
pub use verilith_simd::dot::add32 as vdot_add32;
use vstd::prelude::*;

verus! {

/// Adler-32's sums after `d`, starting from sums `a` and `b`.
pub open spec fn adler_from(a: nat, b: nat, d: Seq<u8>) -> (nat, nat)
    decreases d.len(),
{
    if d.len() == 0 {
        (a, b)
    } else {
        let (a1, b1) = adler_from(a, b, d.drop_last());
        let a2 = (a1 + d.last() as nat) % spec::ADLER_MOD;
        (a2, (b1 + a2) % spec::ADLER_MOD)
    }
}

/// The CRC register after `d`, starting from `c`.
pub open spec fn crc_from(c: u32, d: Seq<u8>) -> u32
    decreases d.len(),
{
    if d.len() == 0 {
        c
    } else {
        spec::crc_byte(crc_from(c, d.drop_last()), d.last())
    }
}

pub proof fn lemma_adler_from(d: Seq<u8>)
    ensures
        adler_from(1, 0, d) == (spec::adler_a(d), spec::adler_b(d)),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_adler_from(d.drop_last());
    }
}

pub proof fn lemma_crc_from(d: Seq<u8>)
    ensures
        crc_from(0xffff_ffff, d) == spec::crc_reg(d),
    decreases d.len(),
{
    if d.len() > 0 {
        lemma_crc_from(d.drop_last());
    }
}

pub const ADLER_MOD: u32 = 65521;


/// Most bytes that can be summed before the sums must be reduced: the
/// largest `n` with `255 * n * (n + 1) / 2 + (n + 1) * (ADLER_MOD - 1)`
/// below 2^32 (zlib's NMAX).
pub const NMAX: usize = 5552;

/// Bytes per Adler-32 block: 32 lanes, 1024 rows. Per lane, the row sums
/// stay below 255 * 1024 and their running total below 255 * 1024 * 1024,
/// so `u32` lanes cannot overflow.
pub const LANES: usize = 32;

pub const ROWS: usize = 1024;

pub const BLOCK: usize = LANES * ROWS;

// ---------------------------------------------------------------------------
// Adler-32 proofs
// ---------------------------------------------------------------------------

/// The sum of the bytes.
pub open spec fn sum(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        sum(d.drop_last()) + d.last() as nat
    }
}

/// The sum of the prefix sums: what the bytes add to B.
pub open spec fn wsum(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        wsum(d.drop_last()) + sum(d)
    }
}

/// The sum of each byte times its index.
pub open spec fn jsum(d: Seq<u8>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        jsum(d.drop_last()) + (d.len() - 1) as nat * d.last() as nat
    }
}

/// Adler-32's sums in closed form.
pub proof fn lemma_adler_closed(a: nat, b: nat, d: Seq<u8>)
    requires
        a < spec::ADLER_MOD,
        b < spec::ADLER_MOD,
    ensures
        adler_from(a, b, d) == ((a + sum(d)) % spec::ADLER_MOD, (b + d.len() * a + wsum(d))
            % spec::ADLER_MOD),
    decreases d.len(),
{
    let m = spec::ADLER_MOD as int;
    if d.len() == 0 {
        vstd::arithmetic::div_mod::lemma_small_mod(a, m as nat);
        vstd::arithmetic::div_mod::lemma_small_mod(b, m as nat);
    } else {
        let e = d.drop_last();
        let x = d.last() as int;
        lemma_adler_closed(a, b, e);
        let n = e.len() as int;
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a + sum(e) as int, x, m);
        vstd::arithmetic::div_mod::lemma_small_mod(x as nat, m as nat);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(b + n * a + wsum(e) as int, a + sum(d) as int, m);
        assert((n + 1) * a == n * a + a) by (nonlinear_arith);
        assert(d.len() == n + 1);
    }
}

/// Continuing the sums over `x` then `y`.
pub proof fn lemma_adler_append(a: nat, b: nat, x: Seq<u8>, y: Seq<u8>)
    ensures
        adler_from(a, b, x + y) == adler_from(adler_from(a, b, x).0, adler_from(a, b, x).1, y),
    decreases y.len(),
{
    if y.len() > 0 {
        lemma_adler_append(a, b, x, y.drop_last());
        assert((x + y).drop_last() =~= x + y.drop_last());
    } else {
        assert(x + y =~= x);
    }
}

pub proof fn lemma_sum_append(x: Seq<u8>, y: Seq<u8>)
    ensures
        sum(x + y) == sum(x) + sum(y),
        wsum(x + y) == wsum(x) + y.len() * sum(x) + wsum(y),
    decreases y.len(),
{
    if y.len() > 0 {
        let z = y.drop_last();
        lemma_sum_append(x, z);
        assert((x + y).drop_last() =~= x + z);
        assert(y.len() * sum(x) == z.len() * sum(x) + sum(x)) by (nonlinear_arith)
            requires
                y.len() == z.len() + 1,
        ;
    } else {
        assert(x + y =~= x);
    }
}

/// `wsum` weighs byte `j` by `n - j`.
pub proof fn lemma_wsum_jsum(d: Seq<u8>)
    ensures
        wsum(d) + jsum(d) == d.len() * sum(d),
    decreases d.len(),
{
    if d.len() > 0 {
        let e = d.drop_last();
        lemma_wsum_jsum(e);
        let n = e.len() as int;
        let x = d.last() as int;
        assert((n + 1) * (sum(e) + x) == n * sum(e) + sum(e) + n * x + x) by (nonlinear_arith);
    }
}

pub proof fn lemma_sum_bound(d: Seq<u8>)
    ensures
        sum(d) <= 255 * d.len(),
        wsum(d) <= 255 * d.len() * (d.len() + 1) / 2,
    decreases d.len(),
{
    if d.len() > 0 {
        let e = d.drop_last();
        lemma_sum_bound(e);
        let n = e.len() as int;
        assert(255 * n * (n + 1) / 2 + 255 * (n + 1) == 255 * (n + 1) * (n + 2) / 2) by (nonlinear_arith);
    }
}

/// The sum of `v[j]` and of `j * v[j]` over lanes `j < m`.
pub open spec fn lsum(v: Seq<u32>, m: nat) -> nat
    decreases m,
{
    if m == 0 {
        0
    } else {
        lsum(v, (m - 1) as nat) + v[m - 1] as nat
    }
}

pub open spec fn ljsum(v: Seq<u32>, m: nat) -> nat
    decreases m,
{
    if m == 0 {
        0
    } else {
        ljsum(v, (m - 1) as nat) + (m - 1) as nat * v[m - 1] as nat
    }
}

/// Adding `row` to the lanes `u` gives lanes `v`.
pub proof fn lemma_lanes_add(u: Seq<u32>, v: Seq<u32>, row: Seq<u8>, m: nat)
    requires
        m <= row.len(),
        m <= u.len(),
        m <= v.len(),
        forall|j: int| 0 <= j < m ==> #[trigger] v[j] as nat == u[j] as nat + row[j] as nat,
    ensures
        lsum(v, m) == lsum(u, m) + sum(row.subrange(0, m as int)),
        ljsum(v, m) == ljsum(u, m) + jsum(row.subrange(0, m as int)),
    decreases m,
{
    if m > 0 {
        lemma_lanes_add(u, v, row, (m - 1) as nat);
        assert(row.subrange(0, m as int).drop_last() =~= row.subrange(0, m - 1));
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(
            (m - 1) as int,
            u[m - 1] as int,
            row[m - 1] as int,
        );
    } else {
        assert(row.subrange(0, 0) =~= Seq::<u8>::empty());
    }
}

/// Lanes `v` are `u` plus lanes `w`.
pub proof fn lemma_lanes_sum(u: Seq<u32>, v: Seq<u32>, w: Seq<u32>, m: nat)
    requires
        m <= u.len(),
        m <= v.len(),
        m <= w.len(),
        forall|j: int| 0 <= j < m ==> #[trigger] v[j] as nat == u[j] as nat + w[j] as nat,
    ensures
        lsum(v, m) == lsum(u, m) + lsum(w, m),
    decreases m,
{
    if m > 0 {
        lemma_lanes_sum(u, v, w, (m - 1) as nat);
    }
}

pub proof fn lemma_lanes_bound(v: Seq<u32>, m: nat, c: nat)
    requires
        m <= v.len(),
        forall|j: int| 0 <= j < m ==> #[trigger] v[j] as nat <= c,
    ensures
        lsum(v, m) <= m * c,
        ljsum(v, m) <= m * m * c,
    decreases m,
{
    if m > 0 {
        let k = (m - 1) as nat;
        lemma_lanes_bound(v, k, c);
        assert(k * v[k as int] as nat <= k * c) by (nonlinear_arith)
            requires
                v[k as int] as nat <= c,
        ;
        assert(k * k * c + k * c <= m * m * c) by (nonlinear_arith)
            requires
                m == k + 1,
        ;
        assert(k * c + c == m * c) by (nonlinear_arith)
            requires
                m == k + 1,
        ;
    }
}

/// Sums `rows` rows of 32 bytes in 32 independent lanes (so the compiler
/// vectorizes it):
/// `s[j]` is the sum of the bytes in lane `j`, and `t[j]` the sum over rows
/// of `s[j]` as it stood after that row. The block then adds `sum(s)` to A
/// and `32 * rows * a + 32 * sum(t) - sum(j * s[j])` to B.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn adler32_block(a: u32, b: u32, d: &[u8], i: usize, rows: usize) -> (r: (u32, u32))
    requires
        a < ADLER_MOD,
        b < ADLER_MOD,
        rows <= ROWS,
        i + 32 * rows <= d@.len() <= usize::MAX,
    ensures
        r.0 < ADLER_MOD,
        r.1 < ADLER_MOD,
        (r.0 as nat, r.1 as nat) == adler_from(
            a as nat,
            b as nat,
            d@.subrange(i as int, i + 32 * rows),
        ),
{
    let mut s = [0u32; LANES];
    let mut t = [0u32; LANES];
    let mut r: usize = 0;
    proof {
        assert(d@.subrange(i as int, i + 32 * 0) =~= Seq::<u8>::empty());
        lemma_lanes_bound(s@, 32, 0);
        lemma_lanes_bound(t@, 32, 0);
    }
    while r < rows
        invariant
            i + 32 * rows <= d@.len() <= usize::MAX,
            r <= rows <= ROWS,
            s@.len() == 32,
            t@.len() == 32,
            forall|j: int| 0 <= j < 32 ==> #[trigger] s@[j] <= 255 * r,
            forall|j: int| 0 <= j < 32 ==> #[trigger] t@[j] <= 261120 * r,
            lsum(s@, 32) == sum(d@.subrange(i as int, i + 32 * r)),
            32 * lsum(t@, 32) == wsum(d@.subrange(i as int, i + 32 * r)) + ljsum(s@, 32),
        decreases rows - r,
    {
        let row = i + r * LANES;
        let ghost s0 = s@;
        let ghost t0 = t@;
        let ghost rw = d@.subrange(row as int, row + 32);
        let mut j: usize = 0;
        while j < LANES
            invariant
                j <= 32,
                row + 32 <= d@.len() <= usize::MAX,
                row == i + 32 * r,
                r < rows <= ROWS,
                s@.len() == 32,
                t@.len() == 32,
                rw == d@.subrange(row as int, row + 32),
                forall|k: int|
                    0 <= k < j ==> #[trigger] s@[k] as nat == s0[k] as nat + rw[k] as nat && t@[k] as nat
                        == t0[k] as nat + s@[k] as nat,
                forall|k: int| j <= k < 32 ==> #[trigger] s@[k] == s0[k] && t@[k] == t0[k],
                forall|k: int| 0 <= k < 32 ==> #[trigger] s0[k] <= 255 * r,
                forall|k: int| 0 <= k < 32 ==> #[trigger] t0[k] <= 261120 * r,
            decreases 32 - j,
        {
            let x = d[row + j];
            proof {
                assert(rw[j as int] == x);
            }
            s[j] = s[j] + x as u32;
            t[j] = t[j] + s[j];
            j = j + 1;
        }
        proof {
            lemma_lanes_add(s0, s@, rw, 32);
            lemma_lanes_sum(t0, t@, s@, 32);
            let p = d@.subrange(i as int, i + 32 * r);
            assert(d@.subrange(i as int, i + 32 * (r + 1)) =~= p + rw);
            lemma_sum_append(p, rw);
            lemma_wsum_jsum(rw);
            assert(rw.subrange(0, 32) =~= rw);
            assert(rw.len() == 32);
            let q = d@.subrange(i as int, i + 32 * (r + 1));
            assert(lsum(s@, 32) == lsum(s0, 32) + sum(rw));
            assert(ljsum(s@, 32) == ljsum(s0, 32) + jsum(rw));
            assert(lsum(t@, 32) == lsum(t0, 32) + lsum(s@, 32));
            assert(wsum(q) == wsum(p) + 32 * sum(p) + wsum(rw));
            assert(wsum(rw) + jsum(rw) == 32 * sum(rw));
            assert(32 * lsum(t@, 32) == wsum(q) + ljsum(s@, 32));
            assert forall|k: int| 0 <= k < 32 implies #[trigger] s@[k] <= 255 * (r + 1) by {
                assert(s@[k] as nat == s0[k] as nat + rw[k] as nat);
            }
            assert forall|k: int| 0 <= k < 32 implies #[trigger] t@[k] <= 261120 * (r + 1) by {
                assert(s@[k] as nat == s0[k] as nat + rw[k] as nat);
                assert(t@[k] as nat == t0[k] as nat + s@[k] as nat);
            }
        }
        r = r + 1;
    }
    let ghost blk = d@.subrange(i as int, i + 32 * rows);
    proof {
        assert(d@.subrange(i as int, i + 32 * r) == blk);
        lemma_lanes_bound(s@, 32, 261120);
        lemma_lanes_bound(t@, 32, 267386880);
    }
    let mut sa: u64 = 0;
    let mut st: u64 = 0;
    let mut sj: u64 = 0;
    let mut j: usize = 0;
    while j < LANES
        invariant
            j <= 32,
            s@.len() == 32,
            t@.len() == 32,
            forall|k: int| 0 <= k < 32 ==> #[trigger] s@[k] <= 261120,
            forall|k: int| 0 <= k < 32 ==> #[trigger] t@[k] <= 267386880,
            sa == lsum(s@, j as nat),
            st == lsum(t@, j as nat),
            sj == ljsum(s@, j as nat),
        decreases 32 - j,
    {
        proof {
            lemma_lanes_bound(s@, j as nat, 261120);
            lemma_lanes_bound(t@, j as nat, 267386880);
            assert(j * j * 261120 <= 32 * 32 * 261120) by (nonlinear_arith)
                requires
                    j <= 32,
            ;
            assert(j * s@[j as int] <= 32 * 261120) by (nonlinear_arith)
                requires
                    j <= 32,
                    s@[j as int] <= 261120,
            ;
        }
        sa = sa + s[j] as u64;
        st = st + t[j] as u64;
        sj = sj + (j as u64) * s[j] as u64;
        j = j + 1;
    }
    let m = ADLER_MOD as u64;
    // sj < 32 * 32 * 255 * 1024 < 1024 * m * m, so adding that keeps it
    // non-negative.
    proof {
        lemma_lanes_bound(s@, 32, 261120);
        lemma_lanes_bound(t@, 32, 267386880);
        lemma_adler_closed(a as nat, b as nat, blk);
        assert(blk.len() == 32 * rows);
        assert(32 * rows * a <= 32 * 1024 * 65520) by (nonlinear_arith)
            requires
                rows <= 1024,
                a < 65521,
        ;
        let x = b as int + blk.len() * a as int + wsum(blk) as int;
        assert(32 * st == wsum(blk) + sj);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1024 * 65521int, x, 65521int);
        assert(1024 * 65521 * 65521 + x == 65521 * (1024 * 65521) + x) by (nonlinear_arith);
    }
    let nb = (b as u64 + (32 * rows as u64) * a as u64 + 32 * st + 1024 * m * m - sj) % m;
    let na = (a as u64 + sa) % m;
    (na as u32, nb as u32)
}

/// Continues an Adler-32 from sums `a` and `b` (each below `ADLER_MOD`).
#[inline(always)]
#[verifier::spinoff_prover]
pub fn adler32_update(a0: u32, b0: u32, d: &[u8]) -> (r: (u32, u32))
    requires
        a0 < ADLER_MOD,
        b0 < ADLER_MOD,
    ensures
        (r.0 as nat, r.1 as nat) == adler_from(a0 as nat, b0 as nat, d@),
{
    let mut a = a0;
    let mut b = b0;
    let n = d.len();
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= LANES
        invariant
            n == d@.len(),
            i <= n,
            a < ADLER_MOD,
            b < ADLER_MOD,
            (a as nat, b as nat) == adler_from(a0 as nat, b0 as nat, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let rows = if n - i >= BLOCK {
            ROWS
        } else {
            (n - i) / LANES
        };
        let (x, y) = adler32_block(a, b, d, i, rows);
        proof {
            lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, i as int), d@.subrange(i as int, i + 32 * rows));
            assert(d@.subrange(0, i as int) + d@.subrange(i as int, i + 32 * rows) =~= d@.subrange(0, i + 32 * rows));
        }
        a = x;
        b = y;
        i = i + LANES * rows;
    }
    while i < n
        invariant
            n == d@.len(),
            i <= n,
            a < ADLER_MOD,
            b < ADLER_MOD,
            (a as nat, b as nat) == adler_from(a0 as nat, b0 as nat, d@.subrange(0, i as int)),
        decreases n - i,
    {
        let end = if n - i > NMAX {
            i + NMAX
        } else {
            n
        };
        let ghost start = i as int;
        let ghost ar = a as nat;
        let ghost br = b as nat;
        proof {
            assert(d@.subrange(start, start) =~= Seq::<u8>::empty());
        }
        while i < end
            invariant
                0 <= start <= i <= end <= n,
                n == d@.len(),
                end - start <= NMAX,
                ar < 65521,
                br < 65521,
                a as nat == ar + sum(d@.subrange(start, i as int)),
                b as nat == br + (i - start) * ar + wsum(d@.subrange(start, i as int)),
            decreases end - i,
        {
            let ghost c1 = d@.subrange(start, i + 1);
            proof {
                assert(c1.drop_last() =~= d@.subrange(start, i as int));
                lemma_sum_bound(c1);
                let k = c1.len() as int;
                assert(255 * k <= 255 * 5552) by (nonlinear_arith)
                    requires
                        k <= 5552,
                ;
                assert(255 * k * (k + 1) / 2 <= 3930857640) by (nonlinear_arith)
                    requires
                        0 <= k <= 5552,
                ;
                assert(k * ar <= 5552 * 65520) by (nonlinear_arith)
                    requires
                        0 <= k <= 5552,
                        ar < 65521,
                ;
                assert((i - start) * ar + ar == k * ar) by (nonlinear_arith)
                    requires
                        k == i - start + 1,
                ;
            }
            a = a + d[i] as u32;
            b = b + a;
            i = i + 1;
        }
        let ghost chunk = d@.subrange(start, i as int);
        proof {
            lemma_adler_closed(ar, br, chunk);
            lemma_adler_append(a0 as nat, b0 as nat, d@.subrange(0, start), chunk);
            assert(d@.subrange(0, start) + chunk =~= d@.subrange(0, i as int));
        }
        a = a % ADLER_MOD;
        b = b % ADLER_MOD;
    }
    proof {
        assert(d@.subrange(0, n as int) =~= d@);
    }
    (a, b)
}

pub fn adler32(d: &[u8]) -> (r: u32)
    ensures
        r as nat == spec::adler32(d@),
{
    let (a, b) = cpu::adler32_update(1, 0, d);
    proof {
        lemma_adler_from(d@);
        assert((b << 16u32) | a == b * 65536 + a) by (bit_vector)
            requires
                a < 65521,
                b < 65521,
        ;
    }
    (b << 16) | a
}

// ---------------------------------------------------------------------------
// CRC-32 proofs
// ---------------------------------------------------------------------------

/// The CRC update is linear (over GF(2)): a step of an XOR is the XOR of
/// the steps.
pub proof fn lemma_step_xor(a: u32, b: u32)
    ensures
        spec::crc_step(a ^ b) == spec::crc_step(a) ^ spec::crc_step(b),
{
    assert((if (a ^ b) & 1 == 1 {
        ((a ^ b) >> 1u32) ^ 0xedb88320u32
    } else {
        (a ^ b) >> 1u32
    }) == (if a & 1 == 1 {
        (a >> 1u32) ^ 0xedb88320u32
    } else {
        a >> 1u32
    }) ^ (if b & 1 == 1 {
        (b >> 1u32) ^ 0xedb88320u32
    } else {
        b >> 1u32
    })) by (bit_vector);
}

pub proof fn lemma_steps_xor(a: u32, b: u32, n: nat)
    ensures
        spec::crc_steps(a ^ b, n) == spec::crc_steps(a, n) ^ spec::crc_steps(b, n),
    decreases n,
{
    if n > 0 {
        lemma_step_xor(a, b);
        lemma_steps_xor(spec::crc_step(a), spec::crc_step(b), (n - 1) as nat);
    }
}

pub proof fn lemma_steps_add(a: u32, m: nat, n: nat)
    ensures
        spec::crc_steps(spec::crc_steps(a, m), n) == spec::crc_steps(a, m + n),
    decreases m,
{
    if m > 0 {
        lemma_steps_add(spec::crc_step(a), (m - 1) as nat, n);
        assert((m - 1) as nat + n == (m + n - 1) as nat);
    }
}

/// Steps on a register whose low `n` bits are zero just shift it.
pub proof fn lemma_steps_even(y: u32, n: nat)
    requires
        n < 32,
        y & ((1u32 << n as u32) - 1) as u32 == 0,
    ensures
        spec::crc_steps(y, n) == y >> n as u32,
    decreases n,
{
    if n == 0 {
        assert(y >> 0u32 == y) by (bit_vector);
    } else {
        let nu = n as u32;
        assert(y & 1 == 0 && (y >> 1u32) & ((1u32 << (nu - 1) as u32) - 1) as u32 == 0 && (y >> 1u32)
            >> (nu - 1) as u32 == y >> nu) by (bit_vector)
            requires
                0 < nu < 32,
                y & ((1u32 << nu) - 1) as u32 == 0,
        ;
        lemma_steps_even(y >> 1u32, (n - 1) as nat);
    }
}

/// `n >= 8` steps: the low byte's, and the rest's from 8 steps on.
pub proof fn lemma_byte_split(y: u32, n: nat)
    requires
        n >= 8,
    ensures
        spec::crc_steps(y, n) == spec::crc_steps(y & 0xff, n) ^ spec::crc_steps(y >> 8u32, (n
            - 8) as nat),
{
    let hi = y & 0xffff_ff00u32;
    assert(y == (y & 0xff) ^ hi && hi & ((1u32 << 8u32) - 1) as u32 == 0 && hi >> 8u32 == y >> 8u32)
        by (bit_vector)
        requires
            hi == y & 0xffff_ff00u32,
    ;
    lemma_steps_xor(y & 0xff, hi, n);
    lemma_steps_even(hi, 8);
    lemma_steps_add(hi, 8, (n - 8) as nat);
    assert(8 + (n - 8) as nat == n);
}

/// Table `k` is `8 * (k + 1)` steps from the byte.
pub proof fn lemma_tables()
    ensures
        forall|k: int, x: int|
            0 <= k < 16 && 0 <= x < 256 ==> #[trigger] tab(k, x) == spec::crc_steps(
                x as u32,
                (8 * (k + 1)) as nat,
            ),
{
    lemma_entries();
    assert forall|k: int, x: int| 0 <= k < 16 && 0 <= x < 256 implies #[trigger] tab(k, x)
        == spec::crc_steps(x as u32, (8 * (k + 1)) as nat) by {
        lemma_table(k, x);
    }
}

proof fn lemma_table(k: int, x: int)
    requires
        0 <= k < 16,
        0 <= x < 256,
    ensures
        tab(k, x) == spec::crc_steps(x as u32, (8 * (k + 1)) as nat),
    decreases k,
{
    lemma_entries();
    if k == 0 {
        reveal(tab);
        assert(T0[x] == spec::crc_steps(x as u32, 8));
    } else {
        lemma_table(k - 1, x);
        let y = tab(k - 1, x);
        let z = y & 0xff;
        assert(z < 256 && (z as int) as u32 == z) by (bit_vector)
            requires
                z == y & 0xff,
        ;
        assert(tab(k, x) == (tab(k - 1, x) >> 8u32) ^ T0[(tab(k - 1, x) & 0xff) as int]);
        assert(T0[z as int] == spec::crc_steps(z, 8));
        lemma_byte_split(y, 8);
        assert(spec::crc_steps(y >> 8u32, 0) == y >> 8u32);
        let u = y >> 8u32;
        let v = T0[z as int];
        assert(v ^ u == u ^ v) by (bit_vector);
        lemma_steps_add(x as u32, (8 * k) as nat, 8);
        assert((8 * k) as nat + 8 == (8 * (k + 1)) as nat);
    }
}

/// The CRC of `a` then `b`.
pub proof fn lemma_crc_append(c: u32, a: Seq<u8>, b: Seq<u8>)
    ensures
        crc_from(c, a + b) == crc_from(crc_from(c, a), b),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_crc_append(c, a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
    } else {
        assert(a + b =~= a);
    }
}

/// The XOR over `j < m` of `d[j]` stepped to the end of `d`.
pub open spec fn tsum(d: Seq<u8>, m: nat) -> u32
    decreases m,
{
    if m == 0 {
        0
    } else {
        tsum(d, (m - 1) as nat) ^ spec::crc_steps(d[m - 1] as u32, (8 * (d.len() - (m - 1))) as nat)
    }
}

proof fn lemma_tsum_step(d: Seq<u8>, m: nat)
    requires
        d.len() > 0,
        m <= d.len() - 1,
    ensures
        spec::crc_steps(tsum(d.drop_last(), m), 8) == tsum(d, m),
    decreases m,
{
    if m == 0 {
        assert(spec::crc_steps(0, 8) == 0) by (compute_only);
    } else {
        lemma_tsum_step(d, (m - 1) as nat);
        let e = d.drop_last();
        let t = tsum(e, (m - 1) as nat);
        let v = spec::crc_steps(e[m - 1] as u32, (8 * (e.len() - (m - 1))) as nat);
        lemma_steps_xor(t, v, 8);
        lemma_steps_add(e[m - 1] as u32, (8 * (e.len() - (m - 1))) as nat, 8);
        assert((8 * (e.len() - (m - 1))) as nat + 8 == (8 * (d.len() - (m - 1))) as nat);
    }
}

/// The CRC of `d` from register `c`: `c` stepped past `d`, XOR each byte
/// stepped to the end.
pub proof fn lemma_crc_sum(c: u32, d: Seq<u8>)
    ensures
        crc_from(c, d) == spec::crc_steps(c, (8 * d.len()) as nat) ^ tsum(d, d.len()),
    decreases d.len(),
{
    if d.len() == 0 {
        assert(c ^ 0 == c) by (bit_vector);
    }
    if d.len() > 0 {
        let e = d.drop_last();
        let x = d.last();
        lemma_crc_sum(c, e);
        lemma_tsum_step(d, e.len());
        let s = spec::crc_steps(c, (8 * e.len()) as nat);
        let t = tsum(e, e.len());
        lemma_steps_xor(s ^ t, x as u32, 8);
        lemma_steps_xor(s, t, 8);
        lemma_steps_add(c, (8 * e.len()) as nat, 8);
        assert((8 * e.len()) as nat + 8 == (8 * d.len()) as nat);
        assert(d[d.len() - 1] == x);
        assert((8 * (d.len() - (d.len() - 1))) == 8);
        let p = spec::crc_steps(s, 8);
        let q = spec::crc_steps(t, 8);
        let r = spec::crc_steps(x as u32, 8);
        assert((p ^ q) ^ r == p ^ (q ^ r)) by (bit_vector);
        assert(crc_from(c, d) == spec::crc_steps(crc_from(c, e) ^ x as u32, 8));
        assert(crc_from(c, d) == (p ^ q) ^ r);
        assert(tsum(d, d.len()) == tsum(d, e.len()) ^ r);
        assert(q == tsum(d, e.len()));
    }
}

/// One byte with table 0.
proof fn lemma_crc_byte(c: u32, x: u8)
    ensures
        spec::crc_byte(c, x) == (c >> 8u32) ^ T0[((c ^ x as u32) & 0xff) as int],
{
    lemma_entries();
    let y = c ^ x as u32;
    let z = y & 0xff;
    lemma_byte_split(y, 8);
    assert(y >> 8u32 == c >> 8u32 && z < 256 && (z as int) as u32 == z) by (bit_vector)
        requires
            y == c ^ x as u32,
            z == y & 0xff,
            x < 256,
    ;
    assert(T0[z as int] == spec::crc_steps(z, 8));
    assert(spec::crc_steps(y >> 8u32, 0) == y >> 8u32);
    let u = y >> 8u32;
    let v = T0[z as int];
    assert(v ^ u == u ^ v) by (bit_vector);
}

/// Sixteen bytes with the sixteen tables.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
proof fn lemma_crc16(c: u32, d: Seq<u8>, w: u32)
    requires
        d.len() == 16,
        w == c ^ (d[0] as u32 | (d[1] as u32) << 8u32 | (d[2] as u32) << 16u32 | (d[3] as u32)
            << 24u32),
    ensures
        crc_from(c, d) == T15[(w & 0xff) as int] ^ T14[((w >> 8u32) & 0xff) as int] ^ T13[((w
            >> 16u32) & 0xff) as int] ^ T12[(w >> 24u32) as int] ^ T11[d[4] as int] ^ T10[d[5] as int]
            ^ T9[d[6] as int] ^ T8[d[7] as int] ^ T7[d[8] as int] ^ T6[d[9] as int] ^ T5[d[10] as int]
            ^ T4[d[11] as int] ^ T3[d[12] as int] ^ T2[d[13] as int] ^ T1[d[14] as int] ^ T0[d[15] as int],
{
    reveal(tab);
    lemma_crc_sum(c, d);
    // The register's four bytes, stepped past the 16 bytes.
    let b0 = c & 0xff;
    let b1 = (c >> 8u32) & 0xff;
    let b2 = (c >> 16u32) & 0xff;
    let b3 = c >> 24u32;
    let c1 = c >> 8u32;
    let c2 = c >> 16u32;
    let c3 = c >> 24u32;
    assert(c1 & 0xff == b1 && c2 & 0xff == b2 && c1 >> 8u32 == c2 && c2 >> 8u32 == c3) by (bit_vector)
        requires
            c1 == c >> 8u32,
            c2 == c >> 16u32,
            c3 == c >> 24u32,
            b1 == (c >> 8u32) & 0xff,
            b2 == (c >> 16u32) & 0xff,
    ;
    lemma_byte_split(c, 128);
    lemma_byte_split(c1, 120);
    lemma_byte_split(c2, 112);
    let s0 = spec::crc_steps(b0, 128);
    let s1 = spec::crc_steps(b1, 120);
    let s2 = spec::crc_steps(b2, 112);
    let s3 = spec::crc_steps(b3, 104);
    let cs = spec::crc_steps(c, 128);
    let r1 = spec::crc_steps(c1, 120);
    let r2 = spec::crc_steps(c2, 112);
    assert(cs == s0 ^ s1 ^ s2 ^ s3) by (bit_vector)
        requires
            cs == s0 ^ r1,
            r1 == s1 ^ r2,
            r2 == s2 ^ s3,
    ;
    let x0 = d[0] as u32;
    let x1 = d[1] as u32;
    let x2 = d[2] as u32;
    let x3 = d[3] as u32;
    let w0 = w & 0xff;
    let w1 = (w >> 8u32) & 0xff;
    let w2 = (w >> 16u32) & 0xff;
    let w3 = w >> 24u32;
    assert(w0 == b0 ^ x0 && w1 == b1 ^ x1 && w2 == b2 ^ x2 && w3 == b3 ^ x3 && w0 < 256 && w1 < 256
        && w2 < 256 && w3 < 256 && (w0 as int) as u32 == w0 && (w1 as int) as u32 == w1 && (
        w2 as int) as u32 == w2 && (w3 as int) as u32 == w3) by (bit_vector)
        requires
            w == c ^ (x0 | x1 << 8u32 | x2 << 16u32 | x3 << 24u32),
            x0 < 256,
            x1 < 256,
            x2 < 256,
            x3 < 256,
            b0 == c & 0xff,
            b1 == (c >> 8u32) & 0xff,
            b2 == (c >> 16u32) & 0xff,
            b3 == c >> 24u32,
            w0 == w & 0xff,
            w1 == (w >> 8u32) & 0xff,
            w2 == (w >> 16u32) & 0xff,
            w3 == w >> 24u32,
    ;
    lemma_steps_xor(b0, x0, 128);
    lemma_steps_xor(b1, x1, 120);
    lemma_steps_xor(b2, x2, 112);
    lemma_steps_xor(b3, x3, 104);
    let y0 = spec::crc_steps(x0, 128);
    let y1 = spec::crc_steps(x1, 120);
    let y2 = spec::crc_steps(x2, 112);
    let y3 = spec::crc_steps(x3, 104);
    let l15 = T15[w0 as int];
    let l14 = T14[w1 as int];
    let l13 = T13[w2 as int];
    let l12 = T12[w3 as int];
    lemma_table(15, w0 as int);
    lemma_table(14, w1 as int);
    lemma_table(13, w2 as int);
    lemma_table(12, w3 as int);
    let c4 = spec::crc_steps(d[4] as u32, 96);
    let c5 = spec::crc_steps(d[5] as u32, 88);
    let c6 = spec::crc_steps(d[6] as u32, 80);
    let c7 = spec::crc_steps(d[7] as u32, 72);
    let c8 = spec::crc_steps(d[8] as u32, 64);
    let c9 = spec::crc_steps(d[9] as u32, 56);
    let c10 = spec::crc_steps(d[10] as u32, 48);
    let c11 = spec::crc_steps(d[11] as u32, 40);
    let c12 = spec::crc_steps(d[12] as u32, 32);
    let c13 = spec::crc_steps(d[13] as u32, 24);
    let c14 = spec::crc_steps(d[14] as u32, 16);
    let c15 = spec::crc_steps(d[15] as u32, 8);
    let l11 = T11[d[4] as int];
    lemma_table(11, d[4] as int);
    let l10 = T10[d[5] as int];
    lemma_table(10, d[5] as int);
    let l9 = T9[d[6] as int];
    lemma_table(9, d[6] as int);
    let l8 = T8[d[7] as int];
    lemma_table(8, d[7] as int);
    let l7 = T7[d[8] as int];
    lemma_table(7, d[8] as int);
    let l6 = T6[d[9] as int];
    lemma_table(6, d[9] as int);
    let l5 = T5[d[10] as int];
    lemma_table(5, d[10] as int);
    let l4 = T4[d[11] as int];
    lemma_table(4, d[11] as int);
    let l3 = T3[d[12] as int];
    lemma_table(3, d[12] as int);
    let l2 = T2[d[13] as int];
    lemma_table(2, d[13] as int);
    let l1 = T1[d[14] as int];
    lemma_table(1, d[14] as int);
    let l0 = T0[d[15] as int];
    lemma_table(0, d[15] as int);
    reveal_with_fuel(tsum, 17);
    let ts = tsum(d, 16);
    assert(ts == ((((((((((((((((0u32 ^ y0) ^ y1) ^ y2) ^ y3) ^ c4) ^ c5) ^ c6) ^ c7) ^ c8) ^ c9) ^ c10) ^ c11) ^ c12) ^ c13) ^ c14) ^ c15));
    assert(cs ^ ts == l15 ^ l14 ^ l13 ^ l12 ^ l11 ^ l10 ^ l9 ^ l8 ^ l7 ^ l6 ^ l5 ^ l4 ^ l3 ^ l2 ^ l1 ^ l0) by (bit_vector)
        requires
            cs == s0 ^ s1 ^ s2 ^ s3,
            ts == ((((((((((((((((0u32 ^ y0) ^ y1) ^ y2) ^ y3) ^ c4) ^ c5) ^ c6) ^ c7) ^ c8) ^ c9) ^ c10) ^ c11) ^ c12) ^ c13) ^ c14) ^ c15),
            l15 == s0 ^ y0,
            l14 == s1 ^ y1,
            l13 == s2 ^ y2,
            l12 == s3 ^ y3,
            l11 == c4,
            l10 == c5,
            l9 == c6,
            l8 == c7,
            l7 == c8,
            l6 == c9,
            l5 == c10,
            l4 == c11,
            l3 == c12,
            l2 == c13,
            l1 == c14,
            l0 == c15,
    ;
}

/// The register `c` stepped past four zero bytes, with four tables
/// (slicing-by-4 with no data).
#[inline(always)]
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub(crate) fn crc_shift32(c: u32) -> (r: u32)
    ensures
        r == spec::crc_steps(c, 32),
{
    let b0 = c & 0xff;
    let b1 = (c >> 8) & 0xff;
    let b2 = (c >> 16) & 0xff;
    let b3 = c >> 24;
    proof {
        reveal(tab);
        let c1 = c >> 8u32;
        let c2 = c >> 16u32;
        let c3 = c >> 24u32;
        assert(c1 & 0xff == b1 && c2 & 0xff == b2 && c1 >> 8u32 == c2 && c2 >> 8u32 == c3 && b0 < 256
            && b1 < 256 && b2 < 256 && b3 < 256 && c3 == b3) by (bit_vector)
            requires
                c1 == c >> 8u32,
                c2 == c >> 16u32,
                c3 == c >> 24u32,
                b0 == c & 0xff,
                b1 == (c >> 8u32) & 0xff,
                b2 == (c >> 16u32) & 0xff,
                b3 == c >> 24u32,
        ;
        lemma_byte_split(c, 32);
        lemma_byte_split(c1, 24);
        lemma_byte_split(c2, 16);
        lemma_table(3, b0 as int);
        lemma_table(2, b1 as int);
        lemma_table(1, b2 as int);
        lemma_table(0, b3 as int);
        assert((b0 as int) as u32 == b0 && (b1 as int) as u32 == b1 && (b2 as int) as u32 == b2 && (
        b3 as int) as u32 == b3);
        let s0 = spec::crc_steps(b0, 32);
        let s1 = spec::crc_steps(b1, 24);
        let s2 = spec::crc_steps(b2, 16);
        let s3 = spec::crc_steps(b3, 8);
        let r1 = spec::crc_steps(c1, 24);
        let r2 = spec::crc_steps(c2, 16);
        let cs = spec::crc_steps(c, 32);
        assert(cs == ((s0 ^ s1) ^ s2) ^ s3) by (bit_vector)
            requires
                cs == s0 ^ r1,
                r1 == s1 ^ r2,
                r2 == s2 ^ s3,
        ;
    }
    T3[b0 as usize] ^ T2[b1 as usize] ^ T1[b2 as usize] ^ T0[b3 as usize]
}

/// The register after the 16 bytes at `i`.
#[inline(always)]
pub(crate) fn crc_step16(c: u32, d: &[u8], i: usize) -> (r: u32)
    requires
        i + 16 <= d@.len(),
    ensures
        r == crc_from(c, d@.subrange(i as int, i + 16)),
{
    let w = c ^ (d[i] as u32 | (d[i + 1] as u32) << 8 | (d[i + 2] as u32) << 16 | (d[i + 3] as u32)
        << 24);
    proof {
        let blk = d@.subrange(i as int, i + 16);
        lemma_crc16(c, blk, w);
        assert((w & 0xff) < 256 && ((w >> 8u32) & 0xff) < 256 && ((w >> 16u32) & 0xff) < 256 && (w
            >> 24u32) < 256) by (bit_vector);
    }
    T15[(w & 0xff) as usize] ^ T14[((w >> 8) & 0xff) as usize] ^ T13[((w >> 16) & 0xff) as usize]
        ^ T12[(w >> 24) as usize] ^ T11[d[i + 4] as usize] ^ T10[d[i + 5] as usize] ^ T9[d[i + 6] as usize]
        ^ T8[d[i + 7] as usize] ^ T7[d[i + 8] as usize] ^ T6[d[i + 9] as usize] ^ T5[d[i + 10] as usize]
        ^ T4[d[i + 11] as usize] ^ T3[d[i + 12] as usize] ^ T2[d[i + 13] as usize] ^ T1[d[i + 14] as usize]
        ^ T0[d[i + 15] as usize]
}

/// The register after byte `x`.
#[inline(always)]
fn crc_step1(c: u32, x: u8) -> (r: u32)
    ensures
        r == spec::crc_byte(c, x),
{
    proof {
        lemma_crc_byte(c, x);
        assert(((c ^ x as u32) & 0xff) < 256) by (bit_vector);
    }
    (c >> 8) ^ T0[((c ^ x as u32) & 0xff) as usize]
}

/// Continues a CRC-32 register over `d`, 16 bytes at a time
/// (slicing-by-16).
#[verifier::spinoff_prover]
pub fn crc32_update(reg: u32, d: &[u8]) -> (r: u32)
    ensures
        r == crc_from(reg, d@),
{
    let mut c = reg;
    let n = d.len();
    let mut i: usize = 0;
    proof {
        assert(d@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while n - i >= 16
        invariant
            n == d@.len(),
            i <= n,
            c == crc_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        proof {
            let blk = d@.subrange(i as int, i + 16);
            lemma_crc_append(reg, d@.subrange(0, i as int), blk);
            assert(d@.subrange(0, i as int) + blk =~= d@.subrange(0, i + 16));
        }
        c = crc_step16(c, d, i);
        i = i + 16;
    }
    while i < n
        invariant
            n == d@.len(),
            i <= n,
            c == crc_from(reg, d@.subrange(0, i as int)),
        decreases n - i,
    {
        proof {
            assert(d@.subrange(0, i + 1).drop_last() =~= d@.subrange(0, i as int));
            assert(d@.subrange(0, i + 1).last() == d@[i as int]);
        }
        c = crc_step1(c, d[i]);
        i = i + 1;
    }
    proof {
        assert(d@.subrange(0, n as int) =~= d@);
    }
    c
}

pub fn crc32(d: &[u8]) -> (r: u32)
    ensures
        r == spec::crc32(d@),
{
    proof {
        lemma_crc_from(d@);
    }
    !cpu::crc32_update(0xffff_ffff, d)
}

} // verus!
