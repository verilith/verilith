//! Huffman tree descriptions, Huffman-coded streams and the literals
//! section (RFC 8878 §4.2, §3.1.1.3.1).
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
use crate::fse::*;
use crate::prims::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[allow(unused_imports)]
use verilith_core::prims::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Weights compressed with FSE
// ---------------------------------------------------------------------------

/// The interleaved two-state loop (`fw_run`).
fn fw_run_exec(s: &[u8], t: &FseTab, p0: usize, s10: u32, s20: u32, Ghost(st): Ghost<FseTable>) -> (r: Option<
    Vec<u8>,
>)
    requires
        tab_is(t, st),
        tab_wf(t, 256),
        p0 <= 8 * s@.len(),
        s@.len() < 0x1_0000_0000,
    ensures
        match fw_run(s@, st, p0 as int, s10 as nat, s20 as nat, Seq::empty()) {
            None => r is None,
            Some(o) => r is Some && r.unwrap()@ == o,
        },
{
    let mut out: Vec<u8> = Vec::new();
    let mut p = p0;
    let mut s1 = s10;
    let mut s2 = s20;
    let ghost full = fw_run(s@, st, p0 as int, s10 as nat, s20 as nat, Seq::empty());
    let n = t.rows.len();
    loop
        invariant
            tab_is(t, st),
            tab_wf(t, 256),
            n == t.rows@.len(),
            p <= 8 * s@.len(),
            out@.len() <= 254,
            fw_run(s@, st, p as int, s1 as nat, s2 as nat, out@) == full,
            full == fw_run(s@, st, p0 as int, s10 as nat, s20 as nat, Seq::empty()),
            s@.len() < 0x1_0000_0000,
        decreases 256 - out@.len(),
    {
        if out.len() > 253 || s1 as usize >= n || s2 as usize >= n {
            return None;
        }
        let e1 = t.rows[s1 as usize];
        out.push(e1.sym);
        if e1.nb as usize > p {
            out.push(t.rows[s2 as usize].sym);
            return Some(out);
        }
        proof {
            lemma_pow2_le(e1.nb as nat, 9);
            assert(pow2(9) == 512) by {
                lemma2_to64();
            }
        }
        let n1 = e1.base as u32 + rd(s, p, e1.nb as u32) as u32;
        p = p - e1.nb as usize;
        if out.len() > 253 || n1 as usize >= n {
            return None;
        }
        let e2 = t.rows[s2 as usize];
        out.push(e2.sym);
        if e2.nb as usize > p {
            out.push(t.rows[n1 as usize].sym);
            return Some(out);
        }
        proof {
            lemma_pow2_le(e2.nb as nat, 9);
        }
        let n2 = e2.base as u32 + rd(s, p, e2.nb as u32) as u32;
        p = p - e2.nb as usize;
        s1 = n1;
        s2 = n2;
    }
}

/// The weights loop yields at most 255 weights.
proof fn lemma_fw_run_len(s: Seq<u8>, t: FseTable, p: int, s1: nat, s2: nat, out: Seq<u8>)
    requires
        out.len() <= 254,
    ensures
        fw_run(s, t, p, s1, s2, out) is Some ==> fw_run(s, t, p, s1, s2, out).unwrap().len() <= 255,
    decreases 256 - out.len(),
{
    if out.len() <= 253 && s1 < t.rows.len() && s2 < t.rows.len() {
        let e1 = t.rows[s1 as int];
        if e1.nb <= p {
            let n1 = e1.base + bits(s, p - e1.nb, e1.nb);
            let p1 = p - e1.nb;
            let e2 = t.rows[s2 as int];
            if out.len() + 1 <= 253 && n1 < t.rows.len() && e2.nb <= p1 {
                let n2 = e2.base + bits(s, p1 - e2.nb, e2.nb);
                lemma_fw_run_len(s, t, p1 - e2.nb, n1, n2, out.push(e1.sym as u8).push(e2.sym as u8));
            }
        }
    }
}

/// Weights compressed with FSE (`fse_weights`).
pub fn fse_weights_exec(b: &[u8]) -> (r: Option<Vec<u8>>)
    requires
        b@.len() < 0x1_0000_0000,
    ensures
        match fse_weights(b@) {
            None => r is None,
            Some(o) => r is Some && r.unwrap()@ == o && o.len() <= 255,
        },
{
    match read_ncount(b, 255, 6) {
        None => None,
        Some((log, norm, used)) => {
            let t = build_table(norm.as_slice(), log);
            let ghost st = fse_table(iseq(norm@), log as nat);
            let s = slice_subrange(b, used, b.len());
            match bstart_exec(s) {
                None => None,
                Some(p) => {
                    if p < 2 * log as usize {
                        return None;
                    }
                    proof {
                        lemma_pow2_le(log as nat, 9);
                        assert(pow2(9) == 512) by {
                            lemma2_to64();
                        }
                    }
                    let s1 = rd(s, p, log) as u32;
                    let s2 = rd(s, p - log as usize, log) as u32;
                    proof {
                        assert(p - log - log == p - 2 * log);
                    }
                    proof {
                        lemma_fw_run_len(s@, st, p - 2 * log, s1 as nat, s2 as nat, Seq::empty());
                    }
                    fw_run_exec(s, &t, p - 2 * log as usize, s1, s2, Ghost(st))
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Tree descriptions
// ---------------------------------------------------------------------------

/// The listed weights (`huf_listed`).
pub fn huf_listed_exec(b: &[u8]) -> (r: Option<(Vec<u8>, usize)>)
    requires
        b@.len() < 0x1_0000_0000,
    ensures
        match huf_listed(b@) {
            None => r is None,
            Some((w, used)) => r is Some && r.unwrap().0@ == w && r.unwrap().1 as int == used && used
                <= b@.len() && w.len() <= 255,
        },
{
    if b.len() == 0 {
        return None;
    }
    let hb = b[0] as usize;
    if hb >= 128 {
        let n = hb - 127;
        let nbytes = (n + 1) / 2;
        if 1 + nbytes > b.len() {
            return None;
        }
        let mut w: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == hb - 127,
                n <= 128,
                1 + (n + 1) / 2 <= b@.len(),
                w@.len() == i,
                forall|j: int|
                    0 <= j < i ==> #[trigger] w@[j] == if j % 2 == 0 {
                        b@[1 + j / 2] / 16
                    } else {
                        b@[1 + j / 2] % 16
                    },
            decreases n - i,
        {
            let c = b[1 + i / 2];
            if i % 2 == 0 {
                w.push(c / 16);
            } else {
                w.push(c % 16);
            }
            i = i + 1;
        }
        proof {
            let ghost sw = Seq::new(
                n as nat,
                |i: int|
                    if i % 2 == 0 {
                        b@[1 + i / 2] / 16
                    } else {
                        b@[1 + i / 2] % 16
                    },
            );
            assert(w@ =~= sw);
        }
        Some((w, 1 + nbytes))
    } else {
        if 1 + hb > b.len() {
            return None;
        }
        let region = slice_subrange(b, 1, 1 + hb);
        match fse_weights_exec(region) {
            None => None,
            Some(w) => Some((w, 1 + hb)),
        }
    }
}

/// `wsum` one weight further.
proof fn lemma_wsum_step(w: Seq<u8>, n: int)
    requires
        n >= 0,
    ensures
        wsum(w, n + 1) == wsum(w, n) + if w[n] == 0 {
            0
        } else {
            pow2((w[n] - 1) as nat)
        },
{
}

proof fn lemma_wsum_bound(w: Seq<u8>, n: int)
    requires
        0 <= n <= w.len(),
        forall|i: int| 0 <= i < n ==> w[i] <= 12,
    ensures
        wsum(w, n) <= 2048 * n,
    decreases n,
{
    if n > 0 {
        lemma_wsum_bound(w, n - 1);
        if w[n - 1] != 0 {
            lemma_pow2_le((w[n - 1] - 1) as nat, 11);
            assert(pow2(11) == 2048) by {
                lemma2_to64();
            }
        }
    }
}

/// `wsum` and `wcount` over a prefix of a longer sequence.
proof fn lemma_wsum_prefix(w: Seq<u8>, v: Seq<u8>, n: int)
    requires
        0 <= n <= w.len(),
        n <= v.len(),
        forall|i: int| 0 <= i < n ==> w[i] == v[i],
    ensures
        wsum(w, n) == wsum(v, n),
    decreases n,
{
    if n > 0 {
        lemma_wsum_prefix(w, v, n - 1);
    }
}

/// Sum of `2^(x-1)` over the first `n` weights equal to `x`.
pub open spec fn lsum(w: Seq<u8>, x: nat, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        lsum(w, x, n - 1) + if w[n - 1] as nat == x {
            pow2((x - 1) as nat)
        } else {
            0
        }
    }
}

/// `lsum` over the weights from `y` to `log`.
pub open spec fn above(w: Seq<u8>, log: nat, y: nat, n: int) -> nat
    decreases log + 1 - y,
{
    if y > log {
        0
    } else {
        lsum(w, y, n) + above(w, log, y + 1, n)
    }
}

proof fn lemma_above_zero(w: Seq<u8>, log: nat, y: nat)
    ensures
        above(w, log, y, 0) == 0,
    decreases log + 1 - y,
{
    if y <= log {
        lemma_above_zero(w, log, y + 1);
    }
}

/// `above` one weight further.
proof fn lemma_above_step(w: Seq<u8>, log: nat, y: nat, n: int)
    requires
        n >= 0,
        y >= 1,
    ensures
        above(w, log, y, n + 1) == above(w, log, y, n) + if y <= w[n] as nat <= log {
            pow2((w[n] - 1) as nat)
        } else {
            0
        },
    decreases log + 1 - y,
{
    if y <= log {
        lemma_above_step(w, log, y + 1, n);
    }
}

/// Summing level by level is summing weight by weight.
proof fn lemma_above_wsum(w: Seq<u8>, log: nat, n: int)
    requires
        n >= 0,
        forall|i: int| 0 <= i < n ==> w[i] as nat <= log,
    ensures
        above(w, log, 1, n) == wsum(w, n),
    decreases n,
{
    if n <= 0 {
        lemma_above_zero(w, log, 1);
    } else {
        lemma_above_wsum(w, log, n - 1);
        lemma_above_step(w, log, 1, n - 1);
    }
}

/// The number of rows from `(x, s)` on.
proof fn lemma_rows_len(c: HufCode, x: nat, s: int)
    requires
        1 <= x <= c.log,
        0 <= s <= c.w.len(),
    ensures
        huf_rows_from(c, x, s).len() + lsum(c.w, x, s) == lsum(c.w, x, c.w.len() as int) + above(
            c.w,
            c.log,
            x + 1,
            c.w.len() as int,
        ),
    decreases c.log + 1 - x, c.w.len() - s,
{
    if s >= c.w.len() {
        if x + 1 <= c.log {
            lemma_rows_len(c, x + 1, 0);
        }
    } else {
        lemma_rows_len(c, x, s + 1);
    }
}

/// A term of `wsum` is at most the sum.
proof fn lemma_wsum_term(w: Seq<u8>, n: int, i: int)
    requires
        0 <= i < n,
        w[i] != 0,
    ensures
        pow2((w[i] - 1) as nat) <= wsum(w, n),
    decreases n,
{
    if i < n - 1 {
        lemma_wsum_term(w, n - 1, i);
    }
}

/// The table of a code the spec accepts is full: `2^log` rows.
pub proof fn lemma_huf_full(listed: Seq<u8>)
    requires
        huf_code(listed) is Some,
    ensures
        huf_rows(huf_code(listed).unwrap()).len() == pow2(huf_code(listed).unwrap().log),
{
    let c = huf_code(listed).unwrap();
    let n = listed.len() as int;
    let total = wsum(listed, n);
    let log = highbit(total) + 1;
    let rest = (pow2(log) - total) as nat;
    let hb = highbit(rest);
    assert(c.log == log);
    assert(c.w == listed.push((hb + 1) as u8));
    lemma_highbit(total);
    assert(1 <= rest);
    lemma_highbit(rest);
    lemma_pow2_pos(log);
    if hb >= log {
        lemma_pow2_le(log, hb);
    }
    assert(hb < log);
    assert(c.w[n] as nat == hb + 1);
    // The weights sum to `2^log`.
    lemma_wsum_prefix(c.w, listed, n);
    lemma_wsum_step(c.w, n);
    assert(wsum(c.w, n + 1) == pow2(log));
    // No weight is above `log`.
    assert forall|i: int| 0 <= i < n + 1 implies c.w[i] as nat <= log by {
        if i < n && listed[i] != 0 {
            lemma_wsum_term(listed, n, i);
            if listed[i] as nat - 1 >= log {
                lemma_pow2_le(log, (listed[i] - 1) as nat);
            }
        }
    }
    lemma_above_wsum(c.w, log, n + 1);
    lemma_rows_len(c, 1, 0);
}

/// The full code from the listed weights (`huf_code`).
fn huf_code_exec(listed: Vec<u8>) -> (r: Option<(Vec<u8>, u32)>)
    requires
        listed@.len() <= 255,
    ensures
        match huf_code(listed@) {
            None => r is None,
            Some(c) => r is Some && r.unwrap().0@ == c.w && r.unwrap().1 as nat == c.log && 1 <= c.log
                <= 12 && c.w.len() <= 256,
        },
{
    let n = listed.len();
    let mut total: u32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == listed@.len(),
            n <= 255,
            forall|j: int| 0 <= j < i ==> listed@[j] <= 12,
            total as nat == wsum(listed@, i as int),
            total <= 2048 * i,
        decreases n - i,
    {
        let x = listed[i];
        if x > 12 {
            proof {
                assert(exists|j: int| 0 <= j < listed@.len() && listed@[j] > 12) by {
                    assert(listed@[i as int] > 12);
                }
            }
            return None;
        }
        proof {
            lemma_wsum_step(listed@, i as int);
            if x != 0 {
                lemma_pow2_le((x - 1) as nat, 11);
                assert(pow2(11) == 2048) by {
                    lemma2_to64();
                }
                lemma_u32_pow2_no_overflow((x - 1) as nat);
                lemma_u32_shl_is_mul(1, (x - 1) as u32);
            }
        }
        if x != 0 {
            total = total + (1u32 << (x - 1) as u32);
        }
        i = i + 1;
    }
    if total == 0 {
        return None;
    }
    let hb = highbit32(total);
    let log = hb + 1;
    if log > 12 {
        return None;
    }
    proof {
        lemma_pow2_unfold(log as nat);
        lemma_u32_pow2_no_overflow(log as nat);
        lemma_u32_shl_is_mul(1, log);
    }
    let rest = (1u32 << log) - total;
    let hr = highbit32(rest);
    proof {
        lemma_u32_pow2_no_overflow(hr as nat);
        lemma_u32_shl_is_mul(1, hr);
    }
    if (1u32 << hr) != rest {
        return None;
    }
    let mut w = listed;
    let ghost l0 = w@;
    proof {
        assert(rest >= 1);
        lemma_highbit(rest as nat);
        assert(pow2(12) == 4096) by {
            lemma2_to64();
        }
        lemma_pow2_le(log as nat, 12);
        if hr >= 12 {
            lemma_pow2_le(12, hr as nat);
        }
    }
    w.push((hr + 1) as u8);
    let mut ones: usize = 0;
    let mut j: usize = 0;
    while j < w.len()
        invariant
            j <= w@.len(),
            w@.len() == n + 1,
            ones as nat == wcount(w@, 1, j as int),
            ones <= j,
        decreases w@.len() - j,
    {
        if w[j] == 1 {
            ones = ones + 1;
        }
        j = j + 1;
    }
    if ones < 2 || ones % 2 == 1 {
        return None;
    }
    proof {
        assert(!(exists|j: int| 0 <= j < l0.len() && l0[j] > 12));
    }
    Some((w, log))
}

/// A decoding table: the code, and the table rows.
pub struct HufTab {
    pub log: u32,
    pub w: Vec<u8>,
    /// The rows' symbols and code lengths (ghost: `x1` holds them).
    pub syms: Ghost<Seq<u8>>,
    pub lens: Ghost<Seq<u8>>,
    /// The two-symbol table (`x2_wf`), or empty.
    pub x2: Vec<X2e>,
    /// Each row's length and symbol in one word (`x1_ok`).
    pub x1: Vec<u16>,
}

/// A row as one word: the code length in the low byte, the symbol above.
pub open spec fn x1e(sym: u8, len: u8) -> u16 {
    (len as u16) | ((sym as u16) << 8)
}

/// `x1` is the rows packed with `x1e`.
pub open spec fn x1_rows(x1: Seq<u16>, syms: Seq<u8>, lens: Seq<u8>) -> bool {
    &&& x1.len() == syms.len()
    &&& forall|v: int| 0 <= v < x1.len() ==> #[trigger] x1[v] == x1e(syms[v], lens[v])
}

/// `x1_rows`, and the table is full: it has a row for every `log` bits, so
/// a lookup needs no bounds test.
pub open spec fn x1_ok(x1: Seq<u16>, syms: Seq<u8>, lens: Seq<u8>, log: u32) -> bool {
    &&& x1_rows(x1, syms, lens)
    &&& x1.len() == pow2(log as nat)
}

/// Unpacking `x1e`.
pub proof fn lemma_x1e(sym: u8, len: u8)
    ensures
        x1e(sym, len) & 255 == len as u16,
        (x1e(sym, len) >> 8) as u8 == sym,
{
    assert(((len as u16) | ((sym as u16) << 8)) & 255 == len as u16) by (bit_vector);
    assert(((((len as u16) | ((sym as u16) << 8))) >> 8) as u8 == sym) by (bit_vector);
}

impl HufTab {
    /// Row `v`'s symbol.
    #[inline(always)]
    pub fn sym(&self, v: usize) -> (r: u8)
        requires
            x1_ok(self.x1@, self.syms@, self.lens@, self.log),
            v < self.x1@.len(),
        ensures
            r == self.syms@[v as int],
    {
        proof {
            lemma_x1e(self.syms@[v as int], self.lens@[v as int]);
        }
        (row(self.x1.as_slice(), v) >> 8) as u8
    }

    /// Row `v`'s code length.
    #[inline(always)]
    pub fn len(&self, v: usize) -> (r: u8)
        requires
            x1_ok(self.x1@, self.syms@, self.lens@, self.log),
            v < self.x1@.len(),
        ensures
            r == self.lens@[v as int],
    {
        proof {
            lemma_x1e(self.syms@[v as int], self.lens@[v as int]);
            let e = self.x1@[v as int];
            assert((e & 255) as u8 as u16 == e & 255) by (bit_vector);
        }
        (row(self.x1.as_slice(), v) & 255) as u8
    }
}

/// The top `k` bits of `x` are the `k` bits below `q`.
pub open spec fn top_is(x: u64, s: Seq<u8>, q: int, k: nat) -> bool {
    &&& 1 <= k <= 64
    &&& k <= q
    &&& (x >> ((64 - k) as u64)) as nat == bits(s, q - k, k)
}

/// A word loaded so that its last byte holds bit `p - 1`, shifted to put
/// that bit on top, has the 57 bits below `p` on top.
pub proof fn lemma_top_init(s: Seq<u8>, i: int, w: u64, p: int)
    requires
        0 <= i,
        i + 8 <= s.len(),
        w as nat == le_word(s, i),
        8 * i + 57 <= p <= 8 * i + 64,
    ensures
        top_is(w << ((8 * i + 64 - p) as u64), s, p, 57),
{
    let sh = (8 * i + 64 - p) as u64;
    let r = (7 - sh) as u64;
    let x = w << sh;
    assert(x >> 7 == (w >> r) & 0x01FF_FFFF_FFFF_FFFFu64) by (bit_vector)
        requires
            sh <= 7,
            r == 7 - sh,
            x == w << sh,
    ;
    lemma_le_bytes_bits(s, i, 8);
    lemma_u64_shr_is_div(w, r);
    lemma_bits_divmod(s, 8 * i, r as nat, 64);
    lemma_and_mask(w >> r, 57);
    assert(lowmask(57) == 0x01FF_FFFF_FFFF_FFFFu64) by (compute);
    lemma_bits_divmod(s, 8 * i + r, 57, (64 - r) as nat);
}

/// The top `j <= k` bits of a word whose top `k` bits are known.
pub proof fn lemma_top_peek(x: u64, s: Seq<u8>, q: int, k: nat, j: nat)
    requires
        top_is(x, s, q, k),
        1 <= j <= k,
    ensures
        (x >> ((64 - j) as u64)) as nat == bits(s, q - j, j),
{
    let a = (64 - k) as u64;
    let b = (k - j) as u64;
    assert((x >> a) >> b == x >> ((a + b) as u64)) by (bit_vector)
        requires
            a + b < 64,
    ;
    lemma_u64_shr_is_div(x >> a, b);
    lemma_bits_divmod(s, q - k, (k - j) as nat, k);
}

/// Shifting out the top `l` bits leaves the next `k - l` on top.
pub proof fn lemma_top_shift(x: u64, s: Seq<u8>, q: int, k: nat, l: nat)
    requires
        top_is(x, s, q, k),
        l < k,
    ensures
        top_is(x << (l as u64), s, q - l, (k - l) as nat),
{
    let l64 = l as u64;
    if l > 0 {
        let a = (64 - k) as u64;
        let m = (k - l) as u64;
        assert((x << l64) >> ((a + l64) as u64) == (x >> a) & (((1u64 << m) - 1) as u64)) by (bit_vector)
            requires
                a + l64 < 64,
                m == 64 - a - l64,
                1 <= l64,
        ;
        lemma_and_mask(x >> a, m);
        lemma_bits_divmod(s, q - k, (k - l) as nat, k);
    } else {
        assert(x << l64 == x) by (bit_vector)
            requires
                l64 == 0,
        ;
    }
}

/// A two-symbol table entry: for the `log` bits `v` at a position, the
/// next `n` symbols (`a`, then `b`) and the bits they use, `tot`. `n == 0`
/// where the one-symbol table has no row.
#[derive(Clone, Copy)]
pub struct X2e {
    pub a: u8,
    pub b: u8,
    pub n: u8,
    pub tot: u8,
}

/// The row index the next lookup lands on after a code of `l1` bits, when
/// the bits it has not seen yet are `f`.
pub open spec fn x2_next(log: nat, v: int, l1: nat, f: int) -> int {
    (v % pow2((log - l1) as nat) as int) * pow2(l1) as int + f
}

/// Entry `e` for the bits `v`: one symbol, or two when the second one's
/// row is the same whatever the bits after `v`.
pub open spec fn x2_ok(rows: Seq<(u8, u8)>, log: nat, v: int, e: X2e) -> bool {
    if v >= rows.len() {
        e.n == 0
    } else {
        let l1 = rows[v].1 as nat;
        &&& e.a == rows[v].0
        &&& l1 <= log
        &&& ((e.n == 1 && e.tot as nat == l1) || (e.n == 2 && l1 <= e.tot <= log && forall|f: int|
            #![trigger x2_next(log, v, l1, f)]
            0 <= f < pow2(l1) ==> 0 <= x2_next(log, v, l1, f) < rows.len() && rows[x2_next(log, v, l1, f)] == (
                e.b,
                (e.tot - l1) as u8,
            )))
    }
}

/// The two-symbol table of `t`, if it has one.
pub open spec fn x2_wf(t: &HufTab) -> bool {
    t.x2@.len() == 0 || (t.x2@.len() == pow2(t.log as nat) && forall|v: int|
        #![trigger t.x2@[v]]
        0 <= v < t.x2@.len() ==> x2_ok(zip(t.syms@, t.lens@), t.log as nat, v, t.x2@[v]))
}

pub open spec fn zip(a: Seq<u8>, b: Seq<u8>) -> Seq<(u8, u8)> {
    Seq::new(a.len(), |i: int| (a[i], b[i]))
}

pub open spec fn huf_code_of(t: &HufTab) -> HufCode {
    HufCode { w: t.w@, log: t.log as nat }
}

/// `t` is the table of a code the spec accepts.
pub open spec fn huf_wf(t: &HufTab) -> bool {
    &&& 1 <= t.log <= 12
    &&& t.w@.len() <= 256
    &&& t.syms@.len() == t.lens@.len()
    &&& lens_le(t.lens@, t.log)
    &&& x2_wf(t)
    &&& x1_ok(t.x1@, t.syms@, t.lens@, t.log)
    &&& zip(t.syms@, t.lens@) == huf_rows(huf_code_of(t))
    &&& huf_code(t.w@.drop_last()) == Some(huf_code_of(t))
}

/// Every code length is at most `log`.
pub open spec fn lens_le(lens: Seq<u8>, log: u32) -> bool {
    forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= log
}

/// The first symbol at or after `s` with weight `x`, or the number of
/// symbols.
pub open spec fn first_w(w: Seq<u8>, x: nat, s: int) -> int
    decreases w.len() - s,
{
    if s >= w.len() || s < 0 {
        w.len() as int
    } else if w[s] as nat == x {
        s
    } else {
        first_w(w, x, s + 1)
    }
}

proof fn lemma_first_w(w: Seq<u8>, x: nat, s: int)
    requires
        0 <= s <= w.len(),
    ensures
        s <= first_w(w, x, s) <= w.len(),
        first_w(w, x, s) < w.len() ==> w[first_w(w, x, s)] as nat == x,
    decreases w.len() - s,
{
    if s < w.len() && w[s] as nat != x {
        lemma_first_w(w, x, s + 1);
    }
}

/// The rows from `s` are the rows from the next symbol of weight `x`.
proof fn lemma_rows_skip(c: HufCode, x: nat, s: int)
    requires
        0 <= s <= c.w.len(),
        1 <= x <= c.log,
    ensures
        huf_rows_from(c, x, s) == huf_rows_from(c, x, first_w(c.w, x, s)),
    decreases c.w.len() - s,
{
    if s < c.w.len() && c.w[s] as nat != x {
        lemma_rows_skip(c, x, s + 1);
    }
}

/// Builds the rows of a code (`huf_rows`).
fn huf_build(w: Vec<u8>, log: u32) -> (r: HufTab)
    requires
        1 <= log <= 12,
        w@.len() <= 256,
    ensures
        r.log == log,
        r.w@ == w@,
        r.x2@.len() == 0,
        r.syms@.len() == r.lens@.len(),
        lens_le(r.lens@, log),
        x1_rows(r.x1@, r.syms@, r.lens@),
        zip(r.syms@, r.lens@) == huf_rows(HufCode { w: w@, log: log as nat }),
{
    let ghost c = HufCode { w: w@, log: log as nat };
    let ghost mut syms: Seq<u8> = Seq::empty();
    let ghost mut lens: Seq<u8> = Seq::empty();
    let mut x1: Vec<u16> = Vec::with_capacity(4096);
    let n = w.len();
    // The symbols of each weight as a chain in increasing order, so the
    // table is filled without scanning all symbols once per weight.
    let mut head: [u16; 16] = [n as u16;16];
    let mut nxt: [u16; 256] = [0u16;256];
    let mut j: usize = n;
    while j > 0
        invariant
            j <= n,
            n == w@.len(),
            n <= 256,
            forall|x: int| 0 <= x < 16 ==> #[trigger] head@[x] as int == first_w(w@, x as nat, j as int),
            forall|i: int| j <= i < n && w@[i] < 16 ==> #[trigger] nxt@[i] as int == first_w(w@, w@[i] as nat, i + 1),
        decreases j,
    {
        j = j - 1;
        let wv = w[j] as usize;
        if wv < 16 {
            nxt[j] = head[wv];
            head[wv] = j as u16;
        }
        proof {
            assert forall|x: int| 0 <= x < 16 implies #[trigger] head@[x] as int == first_w(w@, x as nat, j as int) by {
                reveal_with_fuel(first_w, 2);
            }
        }
    }
    let mut x: u32 = 1;
    proof {
        assert(zip(syms, lens) =~= Seq::<(u8, u8)>::empty());
        lemma_rows_skip(c, 1, 0);
    }
    while x <= log
        invariant
            1 <= x <= log + 1,
            1 <= log <= 12,
            n == w@.len(),
            n <= 256,
            c == (HufCode { w: w@, log: log as nat }),
            syms.len() == lens.len(),
            syms.len() <= (x - 1) * 256 * 2048,
            lens_le(lens, log),
            x1_rows(x1@, syms, lens),
            forall|x: int| 0 <= x < 16 ==> #[trigger] head@[x] as int == first_w(w@, x as nat, 0),
            forall|i: int| 0 <= i < n && w@[i] < 16 ==> #[trigger] nxt@[i] as int == first_w(w@, w@[i] as nat, i + 1),
            zip(syms, lens) + huf_rows_from(c, x as nat, 0) == huf_rows(c),
        decreases log + 1 - x,
    {
        let mut s: usize = head[x as usize] as usize;
        proof {
            lemma_rows_skip(c, x as nat, 0);
            lemma_first_w(w@, x as nat, 0);
        }
        while s < n
            invariant
                1 <= x <= log,
                1 <= log <= 12,
                s <= n,
                n == w@.len(),
                n <= 256,
                c == (HufCode { w: w@, log: log as nat }),
                syms.len() == lens.len(),
                syms.len() <= (x - 1) * 256 * 2048 + s * 2048,
                lens_le(lens, log),
                x1_rows(x1@, syms, lens),
                s < n ==> w@[s as int] as nat == x,
                forall|i: int| 0 <= i < n && w@[i] < 16 ==> #[trigger] nxt@[i] as int == first_w(w@, w@[i] as nat, i + 1),
                zip(syms, lens) + huf_rows_from(c, x as nat, s as int) == huf_rows(c),
            decreases n - s,
        {
            let ghost s_in = s;
            {

                proof {
                    lemma_u32_pow2_no_overflow((x - 1) as nat);
                    lemma_u32_shl_is_mul(1, (x - 1) as u32);
                    lemma_pow2_le((x - 1) as nat, 11);
                    assert(pow2(11) == 2048) by {
                        lemma2_to64();
                    }
                }
                let cnt: u32 = 1u32 << (x - 1);
                let len = (log + 1 - x) as u8;
                let ghost z0 = zip(syms, lens);
                let n0 = x1.len();
                let ghost s0 = syms;
                let ghost l0 = lens;
                proof {
                    syms = s0 + Seq::new(cnt as nat, |i: int| s as u8);
                    lens = l0 + Seq::new(cnt as nat, |i: int| len);
                }
                let ghost e0 = x1@;
                let e: u16 = (len as u16) | ((s as u8 as u16) << 8);
                x1.resize(n0 + cnt as usize, e);
                let k = cnt;
                proof {
                    assert forall|i: int| 0 <= i < x1@.len() implies #[trigger] x1@[i] == x1e(syms[i], lens[i]) by {
                        if i < n0 {
                            assert(x1@[..n0 as int][i] == e0[i]);
                            
                            
                        } else {
                            assert(cloned::<u16>(e, x1@[i]));
                            
                        }
                    }
                }
                proof {
                    assert forall|i: int| n0 <= i < n0 + cnt implies syms[i] == s as u8 && lens[i] == len by {
                        
                    }
                    assert forall|i: int| 0 <= i < n0 implies syms[i] == s0[i] && lens[i] == l0[i] by {
                        
                        
                    }
                    assert(zip(syms, lens) =~= z0 + Seq::new(k as nat, |i: int| (s as u8, len)));
                    assert forall|i: int| 0 <= i < lens.len() implies #[trigger] lens[i] <= log by {
                        if i < n0 {
                            assert(l0[i] <= log);
                        }
                    }
                }
                proof {
                    let blk = Seq::new(pow2((x - 1) as nat), |i: int| (s as u8, (c.log + 1 - x) as u8));
                    assert(Seq::new(k as nat, |i: int| (s as u8, len)) =~= blk);
                    assert(huf_rows_from(c, x as nat, s as int) == blk + huf_rows_from(c, x as nat, s + 1));
                    assert(z0 + (blk + huf_rows_from(c, x as nat, s + 1)) =~= (z0 + blk) + huf_rows_from(
                        c,
                        x as nat,
                        s + 1,
                    ));
                    lemma_rows_skip(c, x as nat, s + 1);
                    lemma_first_w(w@, x as nat, s + 1);
                }
            }
            s = nxt[s] as usize;
        }
        proof {
            assert(huf_rows_from(c, x as nat, n as int) == huf_rows_from(c, (x + 1) as nat, 0));
        }
        x = x + 1;
    }
    proof {
        assert(huf_rows_from(c, x as nat, 0) == Seq::<(u8, u8)>::empty());
        assert(zip(syms, lens) + Seq::<(u8, u8)>::empty() =~= zip(syms, lens));
    }
    HufTab { log: log, w: w, syms: Ghost(syms), lens: Ghost(lens), x2: Vec::new(), x1 }
}

/// A tree description at the start of `b` (`huf_desc`).
pub fn huf_desc_exec(b: &[u8]) -> (r: Option<(HufTab, usize)>)
    requires
        b@.len() < 0x1_0000_0000,
    ensures
        match huf_desc(b@) {
            None => r is None,
            Some((c, used)) => {
                &&& r is Some
                &&& huf_code_of(&r.unwrap().0) == c
                &&& huf_wf(&r.unwrap().0)
                &&& r.unwrap().1 as int == used
                &&& used <= b@.len()
            },
        },
{
    match huf_listed_exec(b) {
        None => None,
        Some((listed, used)) => {
            let ghost l = listed@;
            match huf_code_exec(listed) {
                None => None,
                Some((w, log)) => {
                    let t = huf_build(w, log);
                    proof {
                        let c = huf_code(l).unwrap();
                        assert(t.w@.drop_last() =~= l);
                        lemma_huf_full(l);
                        assert(zip(t.syms@, t.lens@).len() == t.syms@.len());
                    }
                    Some((t, used))
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Huffman-coded streams
// ---------------------------------------------------------------------------

/// Decoding after a prefix is decoding, with the prefix in front.
proof fn lemma_huf_run_prefix(
    rows: Seq<(u8, u8)>,
    log: nat,
    s: Seq<u8>,
    p: int,
    n: nat,
    pre: Seq<u8>,
    out: Seq<u8>,
)
    ensures
        huf_run(rows, log, s, p, n, pre + out) == match huf_run(rows, log, s, p, n, out) {
            None => None,
            Some((o, q)) => Some((pre + o, q)),
        },
    decreases n,
{
    if n > 0 {
        let v = bpeek(s, p, log);
        if v < rows.len() {
            let (sym, len) = rows[v as int];
            if len as int <= p {
                assert((pre + out).push(sym) =~= pre + out.push(sym));
                lemma_huf_run_prefix(rows, log, s, p - len, (n - 1) as nat, pre, out.push(sym));
            }
        }
    } else {
        assert(pre + out == pre + out);
    }
}

/// Decodes `n` symbols from position `p0` (`huf_run`), appending to `out`.
#[inline(always)]
fn huf_run_exec(t: &HufTab, s: &[u8], p0: usize, n: usize, out: &mut Vec<u8>) -> (r: Option<usize>)
    requires
        1 <= t.log <= 12,
        t.syms@.len() == t.lens@.len(),
        x1_ok(t.x1@, t.syms@, t.lens@, t.log),
        p0 <= 8 * s@.len(),
    ensures
        match huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, p0 as int, n as nat, old(out)@) {
            None => r is None,
            Some((o, q)) => r is Some && final(out)@ == o && r.unwrap() as int == q,
        },
        r is Some ==> r.unwrap() <= p0,
{
    let ghost rows = zip(t.syms@, t.lens@);
    let ghost full = huf_run(rows, t.log as nat, s@, p0 as int, n as nat, out@);
    let ghost out0 = out@;
    let mut p = p0;
    let mut i: usize = 0;
    let m = t.x1.len();
    while i < n
        invariant
            i <= n,
            1 <= t.log <= 12,
            m == t.syms@.len(),
            t.syms@.len() == t.lens@.len(),
            rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
            p <= 8 * s@.len(),
            p <= p0,
            huf_run(rows, t.log as nat, s@, p as int, (n - i) as nat, out@) == full,
            full == huf_run(rows, t.log as nat, s@, p0 as int, n as nat, out0),
            out0 == old(out)@,
        decreases n - i,
    {
        if n - i >= 4 && p >= 56 {
            // Four symbols from one 56-bit read.
            let lo = p - 56;
            let w = bits_at(s, lo, 56);
            let mut j: usize = 0;
            let mut fast = true;
            let ghost i0 = i;
            while j < 4 && fast
                invariant
                    i + 4 - j <= n,
                    j <= 4,
                    1 <= t.log <= 12,
                    m == t.syms@.len(),
                    t.syms@.len() == t.lens@.len(),
                    rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
                    p <= 8 * s@.len(),
                    p <= p0,
                    fast ==> lo + 12 * (4 - j) <= p && p - lo <= 56,
                    i == i0 + j,
                    !fast ==> j > 0,
                    w as nat == bits(s@, lo as int, 56),
                    huf_run(rows, t.log as nat, s@, p as int, (n - i) as nat, out@) == full,
                    full == huf_run(rows, t.log as nat, s@, p0 as int, n as nat, out0),
                    out0 == old(out)@,
                decreases 4 - j,
            {
                let v = field(w, (p - lo) as u32 - t.log, t.log, Ghost(s@), Ghost(lo as int), Ghost(56)) as usize;
                if v >= m {
                    return None;
                }
                let len = t.len(v) as usize;
                if len > p {
                    return None;
                }
                p = p - len;
                out.push(t.sym(v));
                i = i + 1;
                j = j + 1;
                if len > 12 {
                    fast = false;
                }
            }
        } else {
            let v = peek(s, p, t.log) as usize;
            if v >= m {
                return None;
            }
            let len = t.len(v) as usize;
            if len > p {
                return None;
            }
            p = p - len;
            out.push(t.sym(v));
            i = i + 1;
        }
    }
    Some(p)
}

/// One lookup in the two-symbol table at `q`, from a word `x` whose top
/// `k` bits are the bits below `q`: the entry, the new position and the
/// word shifted past the entry's bits. After `o`, its symbols are the next
/// one or two of the run.
#[inline(always)]
fn x2_sym(t: &HufTab, s: &[u8], x: u64, q: usize, Ghost(k): Ghost<nat>, Ghost(n): Ghost<nat>, Ghost(o): Ghost<Seq<u8>>) -> (r: Option<(X2e, usize, u64)>)
    requires
        huf_wf(t),
        t.x2@.len() > 0,
        top_is(x, s@, q as int, k),
        k >= 13,
        q >= 24,
        n >= 2,
    ensures
        match r {
            None => huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, q as int, n, o) is None,
            Some((e, q2, x2)) => {
                &&& 1 <= e.n <= 2
                &&& q2 <= q
                &&& q2 + 12 >= q
                &&& top_is(x2, s@, q2 as int, (k - (q - q2)) as nat)
                &&& huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, q as int, n, o) == huf_run(
                    zip(t.syms@, t.lens@),
                    t.log as nat,
                    s@,
                    q2 as int,
                    (n - e.n) as nat,
                    o + pair(e.a, e.b, e.n),
                )
            },
        },
{
    proof {
        lemma_top_peek(x, s@, q as int, k, t.log as nat);
        lemma_bits_bound(s@, q - t.log, t.log as nat);
    }
    let v = (x >> (64 - t.log) as u64) as usize;
    proof {
        assert(v < t.x2@.len());
        assert(v == bpeek(s@, q as int, t.log as nat));
    }
    let e = row(t.x2.as_slice(), v);
    proof {
        assert(x2_ok(zip(t.syms@, t.lens@), t.log as nat, v as int, e));
    }
    if e.n == 0 {
        return None;
    }
    proof {
        lemma_x2_step(zip(t.syms@, t.lens@), t.log as nat, s@, q as int, n, o, e);
        assert(o.push(e.a) =~= o + pair(e.a, e.b, e.n) || e.n == 2);
        assert(o.push(e.a).push(e.b) =~= o + pair(e.a, e.b, e.n) || e.n == 1);
        assert(e.tot <= t.log);
        lemma_top_shift(x, s@, q as int, k, e.tot as nat);
    }
    Some((e, q - e.tot as usize, x << (e.tot as u64)))
}

/// Four lookups in the two-symbol table from one load: four to eight
/// symbols, stored at once at `out[at..]`, after the symbols `d` of the run
/// so far. The position and the count.
#[inline(always)]
fn x2_dec4(t: &HufTab, s: &[u8], p: usize, out: &mut Vec<u8>, at: usize, Ghost(n): Ghost<nat>, Ghost(d): Ghost<Seq<u8>>) -> (r: Option<(usize, usize)>)
    requires
        huf_wf(t),
        t.x2@.len() > 0,
        64 <= p <= 8 * s@.len(),
        n >= 8,
        at + 8 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        kept(old(out)@, final(out)@, at as int, at + 8),
        match r {
            None => huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, p as int, n, d) is None,
            Some((q, c)) => {
                &&& 4 <= c <= 8
                &&& q <= p
                &&& huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, p as int, n, d) == huf_run(
                    zip(t.syms@, t.lens@),
                    t.log as nat,
                    s@,
                    q as int,
                    (n - c) as nat,
                    d + final(out)@.subrange(at as int, at + c),
                )
            },
        },
{
    let ghost o0 = d;
    proof {
        lemma_kept_refl(out@, at as int, at + 8);
    }
    let i = (p - 1) / 8 - 7;
    assert(8 * i + 57 <= p <= 8 * i + 64 && i + 8 <= s@.len());
    let w = load_u64_le(s, i);
    proof {
        lemma_top_init(s@, i as int, w, p as int);
    }
    let sh = (64 - (p - 8 * i)) as u64;
    assert(sh == (8 * i + 64 - p) as u64);
    let x0 = w << sh;
    let (e1, q1, x1) = match x2_sym(t, s, x0, p, Ghost(57), Ghost(n), Ghost(o0)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ghost o1 = o0 + pair(e1.a, e1.b, e1.n);
    let ghost n1 = (n - e1.n) as nat;
    let (e2, q2, x2) = match x2_sym(t, s, x1, q1, Ghost((57 - (p - q1)) as nat), Ghost(n1), Ghost(o1)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ghost o2 = o1 + pair(e2.a, e2.b, e2.n);
    let ghost n2 = (n1 - e2.n) as nat;
    let (e3, q3, x3) = match x2_sym(t, s, x2, q2, Ghost((57 - (p - q2)) as nat), Ghost(n2), Ghost(o2)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ghost o3 = o2 + pair(e3.a, e3.b, e3.n);
    let ghost n3 = (n2 - e3.n) as nat;
    let (e4, q4, x4) = match x2_sym(t, s, x3, q3, Ghost((57 - (p - q3)) as nat), Ghost(n3), Ghost(o3)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let es: [(u8, u8, u8); 4] = [(e1.a, e1.b, e1.n), (e2.a, e2.b, e2.n), (e3.a, e3.b, e3.n), (e4.a, e4.b, e4.n)];
    proof {
        assert(es@[0] == (e1.a, e1.b, e1.n));
        assert(es@[1] == (e2.a, e2.b, e2.n));
        assert(es@[2] == (e3.a, e3.b, e3.n));
        assert(es@[3] == (e4.a, e4.b, e4.n));
    }
    put_pairs4(out, at, es);
    let c = (e1.n + e2.n + e3.n + e4.n) as usize;
    proof {
        assert(pairs4(es) =~= pair(e1.a, e1.b, e1.n) + pair(e2.a, e2.b, e2.n) + pair(e3.a, e3.b, e3.n) + pair(e4.a, e4.b, e4.n));
        assert(pairs4(es).len() == c);
        assert(o3 + pair(e4.a, e4.b, e4.n) =~= d + out@.subrange(at as int, at + c));
        assert((n3 - e4.n) as nat == (n - c) as nat);
    }
    Some((q4, c))
}

/// One symbol of `huf_run` at `q`, from a word `x` whose top `k` bits are
/// the bits below `q`: the symbol, the new position and the word shifted
/// past the code.
#[inline(always)]
fn huf_symx(t: &HufTab, s: &[u8], x: u64, q: usize, Ghost(k): Ghost<nat>) -> (r: Option<(u8, usize, u64)>)
    requires
        1 <= t.log <= 12,
        t.syms@.len() == t.lens@.len(),
        lens_le(t.lens@, t.log),
        x1_ok(t.x1@, t.syms@, t.lens@, t.log),
        top_is(x, s@, q as int, k),
        k >= 13,
    ensures
        ({
            let rows = zip(t.syms@, t.lens@);
            let v = bpeek(s@, q as int, t.log as nat);
            match r {
                None => v >= rows.len(),
                Some((sym, q2, x2)) => v < rows.len() && rows[v as int].0 == sym && q2 as int == q - rows[v as int].1
                    && rows[v as int].1 as int <= q && q2 + 12 >= q && top_is(
                    x2,
                    s@,
                    q2 as int,
                    (k - rows[v as int].1) as nat,
                ),
            }
        }),
{
    proof {
        lemma_top_peek(x, s@, q as int, k, t.log as nat);
    }
    let v = (x >> (64 - t.log) as u64) as usize;
    let x1 = t.x1.as_slice();
    // The table is full, so the row is there without a test.
    proof {
        let lg = t.log as u64;
        assert(x >> ((64 - lg) as u64) < (1u64 << lg)) by (bit_vector)
            requires
                1 <= lg <= 12,
        ;
        lemma_u64_pow2_no_overflow(t.log as nat);
        lemma_u64_shl_is_mul(1, lg);
    }
    let e = row(x1, v);
    let len = (e & 255) as u64;
    proof {
        lemma_x1e(t.syms@[v as int], t.lens@[v as int]);
        assert(t.lens@[v as int] <= t.log);
        lemma_top_shift(x, s@, q as int, k, len as nat);
    }
    Some(((e >> 8) as u8, q - len as usize, x << len))
}

/// Four symbols of `huf_run` from one load, stored at once at
/// `out[at..]` after the symbols `d` of the run so far: every code length
/// is at most 12, so the four fit in the 57 bits loaded and no length check
/// is needed. Each lookup is a shift of the word and one table load.
#[inline(always)]
fn huf_dec4(t: &HufTab, s: &[u8], p: usize, out: &mut Vec<u8>, at: usize, Ghost(d): Ghost<Seq<u8>>) -> (r: Option<usize>)
    requires
        1 <= t.log <= 12,
        t.syms@.len() == t.lens@.len(),
        lens_le(t.lens@, t.log),
        x1_ok(t.x1@, t.syms@, t.lens@, t.log),
        57 <= p <= 8 * s@.len(),
        at + 4 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        kept(old(out)@, final(out)@, at as int, at + 4),
        match huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, p as int, 4, d) {
            None => r is None,
            Some((o, q)) => r is Some && o == d + final(out)@.subrange(at as int, at + 4) && r.unwrap() as int == q,
        },
        r is Some ==> r.unwrap() <= p,
{
    let ghost rows = zip(t.syms@, t.lens@);
    let ghost o = d;
    proof {
        lemma_kept_refl(out@, at as int, at + 4);
    }
    let i = (p - 1) / 8 - 7;
    assert(8 * i + 57 <= p <= 8 * i + 64 && i + 8 <= s@.len());
    let w = load_u64_le(s, i);
    proof {
        lemma_top_init(s@, i as int, w, p as int);
    }
    let sh = (64 - (p - 8 * i)) as u64;
    assert(sh == (8 * i + 64 - p) as u64);
    let x0 = w << sh;
    // Straight-line, with the four symbols stored at once.
    let (a0, q1, x1) = match huf_symx(t, s, x0, p, Ghost(57)) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ghost k1 = (57 - (p - q1)) as nat;
    let (a1, q2, x2) = match huf_symx(t, s, x1, q1, Ghost(k1)) {
        Some(x) => x,
        None => {
            proof {
                assert(huf_run(rows, t.log as nat, s@, p as int, 4, o) == huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)));
            }
            return None;
        },
    };
    let ghost k2 = (57 - (p - q2)) as nat;
    let (a2, q3, x3) = match huf_symx(t, s, x2, q2, Ghost(k2)) {
        Some(x) => x,
        None => {
            proof {
                assert(huf_run(rows, t.log as nat, s@, p as int, 4, o) == huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)));
                assert(huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)) == huf_run(rows, t.log as nat, s@, q2 as int, 2, o.push(a0).push(a1)));
            }
            return None;
        },
    };
    let ghost k3 = (57 - (p - q3)) as nat;
    let (a3, q4, _x4) = match huf_symx(t, s, x3, q3, Ghost(k3)) {
        Some(x) => x,
        None => {
            proof {
                assert(huf_run(rows, t.log as nat, s@, p as int, 4, o) == huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)));
                assert(huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)) == huf_run(rows, t.log as nat, s@, q2 as int, 2, o.push(a0).push(a1)));
                assert(huf_run(rows, t.log as nat, s@, q2 as int, 2, o.push(a0).push(a1)) == huf_run(rows, t.log as nat, s@, q3 as int, 1, o.push(a0).push(a1).push(a2)));
            }
            return None;
        },
    };
    let four: [u8; 4] = [a0, a1, a2, a3];
    put4(out, at, four);
    proof {
        assert(huf_run(rows, t.log as nat, s@, p as int, 4, o) == huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)));
        assert(huf_run(rows, t.log as nat, s@, q1 as int, 3, o.push(a0)) == huf_run(rows, t.log as nat, s@, q2 as int, 2, o.push(a0).push(a1)));
        assert(huf_run(rows, t.log as nat, s@, q2 as int, 2, o.push(a0).push(a1)) == huf_run(rows, t.log as nat, s@, q3 as int, 1, o.push(a0).push(a1).push(a2)));
        assert(huf_run(rows, t.log as nat, s@, q3 as int, 1, o.push(a0).push(a1).push(a2)) == huf_run(rows, t.log as nat, s@, q4 as int, 0, o.push(a0).push(a1).push(a2).push(a3)));
        assert(four@ =~= seq![a0, a1, a2, a3]);
        assert(d + out@.subrange(at as int, at + 4) =~= o.push(a0).push(a1).push(a2).push(a3));
    }
    Some(q4)
}

/// A whole stream of exactly `n` symbols (`huf_stream`), appended to `out`.
#[inline(always)]
pub fn huf_stream_exec(t: &HufTab, s: &[u8], n: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        huf_wf(t),
        s@.len() < 0x1_0000_0000,
    ensures
        match huf_stream(huf_code_of(t), s@, n as nat) {
            None => !ok,
            Some(o) => ok && final(out)@ == old(out)@ + o,
        },
{
    match bstart_exec(s) {
        None => false,
        Some(p) => {
            let ghost pre = out@;
            proof {
                lemma_huf_run_prefix(
                    zip(t.syms@, t.lens@),
                    t.log as nat,
                    s@,
                    p as int,
                    n as nat,
                    pre,
                    Seq::empty(),
                );
                assert(pre + Seq::<u8>::empty() =~= pre);
            }
            match huf_run_exec(t, s, p, n, out) {
                None => false,
                Some(q) => q == 0,
            }
        },
    }
}

/// `v` holds `d` from `at`.
#[verifier::opaque]
pub open spec fn holds(v: Seq<u8>, at: int, d: Seq<u8>) -> bool {
    &&& 0 <= at
    &&& at + d.len() <= v.len()
    &&& forall|j: int| 0 <= j < d.len() ==> v[at + j] == #[trigger] d[j]
}

/// A write elsewhere keeps what `v` holds.
proof fn lemma_holds_kept(a: Seq<u8>, b: Seq<u8>, lo: int, hi: int, at: int, d: Seq<u8>)
    requires
        holds(a, at, d),
        kept(a, b, lo, hi),
        at + d.len() <= lo || hi <= at,
    ensures
        holds(b, at, d),
{
    reveal(holds);
    reveal(kept);
    assert forall|j: int| 0 <= j < d.len() implies b[at + j] == #[trigger] d[j] by {
        assert(a[at + j] == d[j]);
    }
}

/// A write just after what `v` holds extends it.
proof fn lemma_holds_grow(a: Seq<u8>, b: Seq<u8>, at: int, d: Seq<u8>, w: int, c: int)
    requires
        holds(a, at, d),
        kept(a, b, at + d.len(), at + d.len() + w),
        0 <= c <= w,
        at + d.len() + w <= a.len(),
    ensures
        holds(b, at, d + b.subrange(at + d.len(), at + d.len() + c)),
{
    reveal(holds);
    reveal(kept);
    let e = d + b.subrange(at + d.len(), at + d.len() + c);
    assert forall|j: int| 0 <= j < e.len() implies b[at + j] == #[trigger] e[j] by {
        if j < d.len() {
            assert(a[at + j] == d[j]);
        }
    }
}

/// Four parts held back to back are the whole.
proof fn lemma_holds4(v: Seq<u8>, o1: Seq<u8>, o2: Seq<u8>, o3: Seq<u8>, o4: Seq<u8>)
    requires
        holds(v, 0, o1),
        holds(v, o1.len() as int, o2),
        holds(v, (o1.len() + o2.len()) as int, o3),
        holds(v, (o1.len() + o2.len() + o3.len()) as int, o4),
        v.len() == o1.len() + o2.len() + o3.len() + o4.len(),
    ensures
        v == o1 + o2 + o3 + o4,
{
    reveal(holds);
    let w = o1 + o2 + o3 + o4;
    assert forall|j: int| 0 <= j < v.len() implies v[j] == w[j] by {
        if j < o1.len() {
            assert(v[0 + j] == o1[j]);
        } else if j < o1.len() + o2.len() {
            let k = j - o1.len();
            assert(v[o1.len() + k] == o2[k]);
        } else if j < o1.len() + o2.len() + o3.len() {
            let k = j - o1.len() - o2.len();
            assert(v[o1.len() + o2.len() + k] == o3[k]);
        } else {
            let k = j - o1.len() - o2.len() - o3.len();
            assert(v[o1.len() + o2.len() + o3.len() + k] == o4[k]);
        }
    }
    assert(v =~= w);
}

/// Makes `v` exactly `n` bytes long, keeping its storage: the contents are
/// whatever was there, or what `grow` adds.
#[inline(always)]
fn set_len(v: &mut Vec<u8>, n: usize)
    ensures
        final(v)@.len() == n,
{
    let len = v.len();
    if len >= n {
        v.truncate(n);
    } else {
        grow(v, n - len);
    }
}

/// Four streams after a jump table (`huf_4streams`), into an empty `out`.
/// Each stream is decoded straight into its part of the output.
#[inline(always)]
pub fn huf_4streams_exec(t: &HufTab, b: &[u8], n: usize, out: &mut Vec<u8>) -> (ok: bool)
    requires
        huf_wf(t),
        b@.len() < 0x1_0000_0000,
        n < 0x1_0000_0000,
    ensures
        match huf_4streams(huf_code_of(t), b@, n as nat) {
            None => !ok,
            Some(o) => ok && final(out)@ == o,
        },
{
    if b.len() < 10 {
        return false;
    }
    let l1 = b[0] as usize + 256 * b[1] as usize;
    let l2 = b[2] as usize + 256 * b[3] as usize;
    let l3 = b[4] as usize + 256 * b[5] as usize;
    proof {
        reveal_with_fuel(le, 3);
    }
    let seg = (n + 3) / 4;
    if 6 + l1 + l2 + l3 > b.len() || 3 * seg > n {
        return false;
    }
    let a1: usize = 6;
    let a2 = a1 + l1;
    let a3 = a2 + l2;
    let a4 = a3 + l3;
    let n4 = n - 3 * seg;
    let ghost c = huf_code_of(t);
    let ghost rows = zip(t.syms@, t.lens@);
    let s1 = slice_subrange(b, a1, a2);
    let s2 = slice_subrange(b, a2, a3);
    let s3 = slice_subrange(b, a3, a4);
    let s4 = slice_subrange(b, a4, b.len());
    proof {
        assert(s1@ == b@.subrange(a1 as int, a2 as int));
        assert(s4@ == b@.subrange(a4 as int, b@.len() as int));
    }
    let (mut p1, mut p2, mut p3, mut p4) = match (bstart_exec(s1), bstart_exec(s2), bstart_exec(s3), bstart_exec(s4)) {
        (Some(x1), Some(x2), Some(x3), Some(x4)) => (x1, x2, x3, x4),
        _ => {
            return false;
        },
    };
    let ghost f1 = huf_run(rows, t.log as nat, s1@, p1 as int, seg as nat, Seq::empty());
    let ghost f2 = huf_run(rows, t.log as nat, s2@, p2 as int, seg as nat, Seq::empty());
    let ghost f3 = huf_run(rows, t.log as nat, s3@, p3 as int, seg as nat, Seq::empty());
    let ghost f4 = huf_run(rows, t.log as nat, s4@, p4 as int, n4 as nat, Seq::empty());
    proof {
        assert(huf_stream(c, s1@, seg as nat) == huf_fin(f1));
        assert(huf_stream(c, s2@, seg as nat) == huf_fin(f2));
        assert(huf_stream(c, s3@, seg as nat) == huf_fin(f3));
        assert(huf_stream(c, s4@, n4 as nat) == huf_fin(f4));
        assert(huf_4streams(c, b@, n as nat) == huf_join(huf_fin(f1), huf_fin(f2), huf_fin(f3), huf_fin(f4)));
    }
    // The output, with stream k decoded into [bk, bk + its count). What
    // `out` held is dropped; all `n` bytes are written below.
    set_len(out, n);
    let b2 = seg;
    let b3 = 2 * seg;
    let b4 = 3 * seg;
    let ghost mut d1: Seq<u8> = Seq::empty();
    let ghost mut d2: Seq<u8> = Seq::empty();
    let ghost mut d3: Seq<u8> = Seq::empty();
    let ghost mut d4: Seq<u8> = Seq::empty();
    proof {
        reveal(holds);
    }
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    let mut i3: usize = 0;
    let mut i4: usize = 0;
    if t.x2.len() > 0 {
        // Two-symbol lookups, four per stream per step.
        while seg - i1 >= 8 && seg - i2 >= 8 && seg - i3 >= 8 && n4 - i4 >= 8 && p1 >= 64 && p2 >= 64 && p3 >= 64
            && p4 >= 64
            invariant
                huf_wf(t),
                t.x2@.len() > 0,
                rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
                out@.len() == n,
                b2 == seg,
                b3 == 2 * seg,
                b4 == 3 * seg,
                b4 + n4 == n,
                i1 <= seg,
                i2 <= seg,
                i3 <= seg,
                i4 <= n4,
                d1.len() == i1,
                d2.len() == i2,
                d3.len() == i3,
                d4.len() == i4,
                holds(out@, 0, d1),
                holds(out@, b2 as int, d2),
                holds(out@, b3 as int, d3),
                holds(out@, b4 as int, d4),
                p1 <= 8 * s1@.len(),
                p2 <= 8 * s2@.len(),
                p3 <= 8 * s3@.len(),
                p4 <= 8 * s4@.len(),
                huf_run(rows, t.log as nat, s1@, p1 as int, (seg - i1) as nat, d1) == f1,
                huf_run(rows, t.log as nat, s2@, p2 as int, (seg - i2) as nat, d2) == f2,
                huf_run(rows, t.log as nat, s3@, p3 as int, (seg - i3) as nat, d3) == f3,
                huf_run(rows, t.log as nat, s4@, p4 as int, (n4 - i4) as nat, d4) == f4,
                huf_4streams(c, b@, n as nat) == huf_join(huf_fin(f1), huf_fin(f2), huf_fin(f3), huf_fin(f4)),
                c == huf_code_of(t),
            decreases seg - i1,
        {
            let ghost o0 = out@;
            let r1 = x2_dec4(t, s1, p1, out, i1, Ghost((seg - i1) as nat), Ghost(d1));
            let ghost oa = out@;
            let r2 = x2_dec4(t, s2, p2, out, b2 + i2, Ghost((seg - i2) as nat), Ghost(d2));
            let ghost ob = out@;
            let r3 = x2_dec4(t, s3, p3, out, b3 + i3, Ghost((seg - i3) as nat), Ghost(d3));
            let ghost oc = out@;
            let r4 = x2_dec4(t, s4, p4, out, b4 + i4, Ghost((n4 - i4) as nat), Ghost(d4));
            match (r1, r2, r3, r4) {
                (Some((x1, c1)), Some((x2, c2)), Some((x3, c3)), Some((x4, c4))) => {
                    proof {
                        let w1 = (i1 as int, i1 + 8);
                        let w2 = (b2 + i2, b2 + i2 + 8);
                        let w3 = (b3 + i3, b3 + i3 + 8);
                        let w4 = (b4 + i4, b4 + i4 + 8);
                        lemma_holds_grow(o0, oa, 0, d1, 8, c1 as int);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b2 as int, d2);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b3 as int, d3);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b4 as int, d4);
                        d1 = d1 + oa.subrange(i1 as int, i1 + c1);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, 0, d1);
                        lemma_holds_grow(oa, ob, b2 as int, d2, 8, c2 as int);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, b3 as int, d3);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, b4 as int, d4);
                        d2 = d2 + ob.subrange(b2 + i2, b2 + i2 + c2);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, 0, d1);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, b2 as int, d2);
                        lemma_holds_grow(ob, oc, b3 as int, d3, 8, c3 as int);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, b4 as int, d4);
                        d3 = d3 + oc.subrange(b3 + i3, b3 + i3 + c3);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, 0, d1);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, b2 as int, d2);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, b3 as int, d3);
                        lemma_holds_grow(oc, out@, b4 as int, d4, 8, c4 as int);
                        d4 = d4 + out@.subrange(b4 + i4, b4 + i4 + c4);
                    }
                    p1 = x1;
                    p2 = x2;
                    p3 = x3;
                    p4 = x4;
                    i1 = i1 + c1;
                    i2 = i2 + c2;
                    i3 = i3 + c3;
                    i4 = i4 + c4;
                },
                _ => {
                    return false;
                },
            }
        }
    } else {
        let both = if n4 < seg {
            n4
        } else {
            seg
        };
        let mut i: usize = 0;
        // The four streams in lockstep, four symbols each per step (one read
        // per stream), for instruction-level parallelism.
        while both - i >= 4 && p1 >= 57 && p2 >= 57 && p3 >= 57 && p4 >= 57
            invariant
                huf_wf(t),
                rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
                out@.len() == n,
                b2 == seg,
                b3 == 2 * seg,
                b4 == 3 * seg,
                b4 + n4 == n,
                i <= both,
                both <= seg,
                both <= n4,
                d1.len() == i,
                d2.len() == i,
                d3.len() == i,
                d4.len() == i,
                holds(out@, 0, d1),
                holds(out@, b2 as int, d2),
                holds(out@, b3 as int, d3),
                holds(out@, b4 as int, d4),
                p1 <= 8 * s1@.len(),
                p2 <= 8 * s2@.len(),
                p3 <= 8 * s3@.len(),
                p4 <= 8 * s4@.len(),
                huf_run(rows, t.log as nat, s1@, p1 as int, (seg - i) as nat, d1) == f1,
                huf_run(rows, t.log as nat, s2@, p2 as int, (seg - i) as nat, d2) == f2,
                huf_run(rows, t.log as nat, s3@, p3 as int, (seg - i) as nat, d3) == f3,
                huf_run(rows, t.log as nat, s4@, p4 as int, (n4 - i) as nat, d4) == f4,
                huf_4streams(c, b@, n as nat) == huf_join(huf_fin(f1), huf_fin(f2), huf_fin(f3), huf_fin(f4)),
                c == huf_code_of(t),
            decreases both - i,
        {
            proof {
                lemma_huf_run_split(rows, t.log as nat, s1@, p1 as int, 4, (seg - i - 4) as nat, d1);
                lemma_huf_run_split(rows, t.log as nat, s2@, p2 as int, 4, (seg - i - 4) as nat, d2);
                lemma_huf_run_split(rows, t.log as nat, s3@, p3 as int, 4, (seg - i - 4) as nat, d3);
                lemma_huf_run_split(rows, t.log as nat, s4@, p4 as int, 4, (n4 - i - 4) as nat, d4);
            }
            let ghost o0 = out@;
            let q1 = huf_dec4(t, s1, p1, out, i, Ghost(d1));
            let ghost oa = out@;
            let q2 = huf_dec4(t, s2, p2, out, b2 + i, Ghost(d2));
            let ghost ob = out@;
            let q3 = huf_dec4(t, s3, p3, out, b3 + i, Ghost(d3));
            let ghost oc = out@;
            let q4 = huf_dec4(t, s4, p4, out, b4 + i, Ghost(d4));
            match (q1, q2, q3, q4) {
                (Some(x1), Some(x2), Some(x3), Some(x4)) => {
                    proof {
                        let w1 = (i as int, i + 4);
                        let w2 = (b2 + i, b2 + i + 4);
                        let w3 = (b3 + i, b3 + i + 4);
                        let w4 = (b4 + i, b4 + i + 4);
                        lemma_holds_grow(o0, oa, 0, d1, 4, 4);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b2 as int, d2);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b3 as int, d3);
                        lemma_holds_kept(o0, oa, w1.0, w1.1, b4 as int, d4);
                        d1 = d1 + oa.subrange(i as int, i + 4);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, 0, d1);
                        lemma_holds_grow(oa, ob, b2 as int, d2, 4, 4);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, b3 as int, d3);
                        lemma_holds_kept(oa, ob, w2.0, w2.1, b4 as int, d4);
                        d2 = d2 + ob.subrange(b2 + i, b2 + i + 4);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, 0, d1);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, b2 as int, d2);
                        lemma_holds_grow(ob, oc, b3 as int, d3, 4, 4);
                        lemma_holds_kept(ob, oc, w3.0, w3.1, b4 as int, d4);
                        d3 = d3 + oc.subrange(b3 + i, b3 + i + 4);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, 0, d1);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, b2 as int, d2);
                        lemma_holds_kept(oc, out@, w4.0, w4.1, b3 as int, d3);
                        lemma_holds_grow(oc, out@, b4 as int, d4, 4, 4);
                        d4 = d4 + out@.subrange(b4 + i, b4 + i + 4);
                    }
                    p1 = x1;
                    p2 = x2;
                    p3 = x3;
                    p4 = x4;
                },
                _ => {
                    return false;
                },
            }
            i = i + 4;
        }
        i1 = i;
        i2 = i;
        i3 = i;
        i4 = i;
    }
    // The ends of the streams, one symbol at a time.
    let mut tail: Vec<u8> = Vec::new();
    let ghost o0 = out@;
    if !huf_tail(t, s1, p1, seg - i1, out, 0, i1, &mut tail, Ghost(d1)) {
        return false;
    }
    let ghost oa = out@;
    proof {
        lemma_holds_kept(o0, oa, i1 as int, b2 as int, b2 as int, d2);
        lemma_holds_kept(o0, oa, i1 as int, b2 as int, b3 as int, d3);
        lemma_holds_kept(o0, oa, i1 as int, b2 as int, b4 as int, d4);
    }
    if !huf_tail(t, s2, p2, seg - i2, out, b2, i2, &mut tail, Ghost(d2)) {
        return false;
    }
    let ghost ob = out@;
    proof {
        lemma_holds_kept(oa, ob, b2 + i2, b3 as int, b3 as int, d3);
        lemma_holds_kept(oa, ob, b2 + i2, b3 as int, b4 as int, d4);
    }
    if !huf_tail(t, s3, p3, seg - i3, out, b3, i3, &mut tail, Ghost(d3)) {
        return false;
    }
    proof {
        lemma_holds_kept(ob, out@, b3 + i3, b4 as int, b4 as int, d4);
    }
    let ghost oc = out@;
    if !huf_tail(t, s4, p4, n4 - i4, out, b4, i4, &mut tail, Ghost(d4)) {
        return false;
    }
    proof {
        let o1 = huf_fin(f1).unwrap();
        let o2 = huf_fin(f2).unwrap();
        let o3 = huf_fin(f3).unwrap();
        let o4 = huf_fin(f4).unwrap();
        lemma_holds_kept(oa, ob, b2 + i2, b3 as int, 0, o1);
        lemma_holds_kept(ob, oc, b3 + i3, b4 as int, 0, o1);
        lemma_holds_kept(oc, out@, b4 + i4, n as int, 0, o1);
        lemma_holds_kept(ob, oc, b3 + i3, b4 as int, b2 as int, o2);
        lemma_holds_kept(oc, out@, b4 + i4, n as int, b2 as int, o2);
        lemma_holds_kept(oc, out@, b4 + i4, n as int, b3 as int, o3);
        lemma_holds4(out@, o1, o2, o3, o4);
    }
    true
}

/// The last `m` symbols of a stream that has decoded `d` (`k` symbols)
/// into `out[b..]`, decoded one at a time into `tail` and then stored after
/// `d`. True if the stream then ends exactly.
#[inline(always)]
fn huf_tail(t: &HufTab, s: &[u8], p: usize, m: usize, out: &mut Vec<u8>, b: usize, k: usize, tail: &mut Vec<u8>, Ghost(d): Ghost<Seq<u8>>) -> (ok: bool)
    requires
        huf_wf(t),
        p <= 8 * s@.len(),
        d.len() == k,
        b + k + m <= old(out)@.len(),
        old(out)@.len() < 0x1_0000_0000,
        holds(old(out)@, b as int, d),
    ensures
        final(out)@.len() == old(out)@.len(),
        kept(old(out)@, final(out)@, b + k, b + k + m),
        match huf_fin(huf_run(zip(t.syms@, t.lens@), t.log as nat, s@, p as int, m as nat, d)) {
            None => !ok,
            Some(o) => ok && o.len() == k + m && holds(final(out)@, b as int, o),
        },
{
    let ghost rows = zip(t.syms@, t.lens@);
    proof {
        lemma_kept_refl(out@, b + k, b + k + m);
    }
    tail.clear();
    proof {
        lemma_huf_run_prefix(rows, t.log as nat, s@, p as int, m as nat, d, Seq::empty());
        assert(d + Seq::<u8>::empty() =~= d);
        lemma_huf_run_len(rows, t.log as nat, s@, p as int, m as nat, Seq::empty());
    }
    match huf_run_exec(t, s, p, m, tail) {
        Some(0) => {
            proof {
                assert(tail@.len() == m);
            }
            put(out, b + k, tail.as_slice(), 0, m);
            proof {
                assert(tail@.subrange(0, m as int) =~= tail@);
                lemma_holds_grow(old(out)@, out@, b as int, d, m as int, m as int);
                assert(out@.subrange(b + k, b + k + m) == tail@);
            }
            true
        },
        _ => false,
    }
}

/// The end of a stream's run: its output if every bit was used.
pub open spec fn huf_fin(f: Option<(Seq<u8>, int)>) -> Option<Seq<u8>> {
    match f {
        None => None,
        Some((o, q)) => if q == 0 { Some(o) } else { None },
    }
}

/// The four streams' outputs, joined (`huf_4streams`).
pub open spec fn huf_join(
    a: Option<Seq<u8>>,
    b: Option<Seq<u8>>,
    c: Option<Seq<u8>>,
    d: Option<Seq<u8>>,
) -> Option<Seq<u8>> {
    match (a, b, c, d) {
        (Some(o1), Some(o2), Some(o3), Some(o4)) => Some(o1 + o2 + o3 + o4),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The literals section
// ---------------------------------------------------------------------------

/// `t` holds the code `c`, if any.
pub open spec fn huf_opt_is(t: Option<HufTab>, c: Option<HufCode>) -> bool {
    match t {
        None => c is None,
        Some(tt) => c is Some && huf_code_of(&tt) == c.unwrap() && huf_wf(&tt),
    }
}

/// Raw and RLE literals (`lit_section`, types 0 and 1).
fn lit_plain(b: &[u8], bmax: usize, lits: &mut Vec<u8>, Ghost(hc): Ghost<Option<HufCode>>) -> (r: Option<usize>)
    requires
        b@.len() < 0x1_0000_0000,
        b@.len() >= 2,
        b@[0] % 4 <= 1,
        bmax <= 131072,
    ensures
        match lit_section(b@, bmax as nat, hc) {
            None => r is None,
            Some(l) => {
                &&& r is Some
                &&& r.unwrap() as int == l.used
                &&& final(lits)@ == l.lits
                &&& l.huf == hc
                &&& l.used <= b@.len()
                &&& l.lits.len() <= bmax
            },
        },
{
    proof {
        reveal_with_fuel(le, 5);
        reveal(lit_section);
    }
    let ty = b[0] % 4;
    let sf = (b[0] / 4) % 4;
    let lh: usize = if sf == 1 {
        2
    } else if sf == 3 {
        3
    } else {
        1
    };
    let n: usize = if sf == 1 {
        (b[0] as usize + 256 * b[1] as usize) / 16
    } else if sf == 3 {
        if b.len() < 3 {
            0
        } else {
            (b[0] as usize + 256 * b[1] as usize + 65536 * b[2] as usize) / 16
        }
    } else {
        b[0] as usize / 8
    };
    if b.len() < lh || n > bmax {
        return None;
    }
    lits.clear();
    if ty == 0 {
        if lh + n > b.len() {
            return None;
        }
        let src = slice_subrange(b, lh, lh + n);
        lits.extend_from_slice(src);
        proof {
            assert(lits@ =~= b@.subrange(lh as int, lh + n));
        }
        Some(lh + n)
    } else {
        if lh + 1 > b.len() {
            return None;
        }
        let c = b[lh];
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                lits@ == Seq::new(k as nat, |i: int| c),
            decreases n - k,
        {
            lits.push(c);
            k = k + 1;
            proof {
                assert(lits@ =~= Seq::new(k as nat, |i: int| c));
            }
        }
        Some(lh + 1)
    }
}

/// The sizes in a Huffman-coded literals header: header size, literals,
/// compressed size.
pub fn lit_huf_sizes(b: &[u8]) -> (r: (usize, usize, usize))
    requires
        b@.len() >= 5,
    ensures
        ({
            let sf = (b@[0] / 4) % 4;
            let lhc = le(b@, 0, 4) as int;
            &&& r.0 as int == if sf <= 1 {
                3int
            } else if sf == 2 {
                4
            } else {
                5
            }
            &&& r.1 as int == if sf <= 1 {
                (lhc / 16) % 1024
            } else if sf == 2 {
                (lhc / 16) % 16384
            } else {
                (lhc / 16) % 262144
            }
            &&& r.2 as int == if sf <= 1 {
                (lhc / 16384) % 1024
            } else if sf == 2 {
                lhc / 262144
            } else {
                lhc / 4194304 + b@[4] as int * 1024
            }
        }),
        r.1 < 262144,
        r.2 < 0x1_0000_0000,
{
    proof {
        reveal_with_fuel(le, 5);
    }
    let sf = (b[0] / 4) % 4;
    let lhc: usize = b[0] as usize + 256 * b[1] as usize + 65536 * b[2] as usize + 16777216 * b[3] as usize;
    let lh: usize = if sf <= 1 {
        3
    } else if sf == 2 {
        4
    } else {
        5
    };
    let n: usize = if sf <= 1 {
        (lhc / 16) % 1024
    } else if sf == 2 {
        (lhc / 16) % 16384
    } else {
        (lhc / 16) % 262144
    };
    let c: usize = if sf <= 1 {
        (lhc / 16384) % 1024
    } else if sf == 2 {
        lhc / 262144
    } else {
        lhc / 4194304 + b[4] as usize * 1024
    };
    (lh, n, c)
}

/// Compressed and treeless literals (`lit_section`, types 2 and 3).
fn lit_huf(b: &[u8], bmax: usize, huf: &mut Option<HufTab>, lits: &mut Vec<u8>) -> (r: Option<usize>)
    requires
        b@.len() < 0x1_0000_0000,
        b@.len() >= 2,
        b@[0] % 4 >= 2,
        bmax <= 131072,
        huf_opt_is(*old(huf), old_huf_code(old(huf))),
    ensures
        match lit_section(b@, bmax as nat, old_huf_code(old(huf))) {
            None => r is None,
            Some(l) => {
                &&& r is Some
                &&& r.unwrap() as int == l.used
                &&& final(lits)@ == l.lits
                &&& huf_opt_is(*final(huf), l.huf)
                &&& l.used <= b@.len()
                &&& l.lits.len() <= bmax
            },
        },
{
    let ghost hc = old_huf_code(huf);
    proof {
        reveal(lit_section);
    }
    if b.len() < 5 {
        return None;
    }
    let ty = b[0] % 4;
    let sf = (b[0] / 4) % 4;
    if ty == 3 && huf.is_none() {
        return None;
    }
    let (lh, n, c) = lit_huf_sizes(b);
    if n > bmax || (sf != 0 && n < 6) || lh + c > b.len() {
        return None;
    }
    let region = slice_subrange(b, lh, lh + c);
    let ghost code: Option<(HufCode, int)> = if ty == 2 {
        huf_desc(region@)
    } else {
        Some((hc.unwrap(), 0))
    };
    let tu: usize;
    if ty == 2 {
        match huf_desc_exec(region) {
            None => {
                return None;
            },
            Some((t, u)) => {
                let mut t = t;
                // The two-symbol table pays for its building only on long
                // 4-stream literals: at eight times the table size it is
                // level with the one-symbol table on Silesia, and below
                // that it costs 3 to 5% of the whole decode.
                if sf != 0 && n >= (8usize << t.log) {
                    huf_add_x2(&mut t);
                }
                *huf = Some(t);
                tu = u;
            },
        }
    } else {
        tu = 0;
    }
    let ghost hcode = code.unwrap().0;
    let streams = slice_subrange(region, tu, region.len());
    let ok = match huf {
        Some(t) => {
            proof {
                assert(huf_code_of(t) == hcode);
                assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
            }
            if sf == 0 {
                lits.clear();
                crate::cpu::run_huf1(t, streams, n, lits)
            } else {
                crate::cpu::run_huf4(t, streams, n, lits)
            }
        },
        None => false,
    };
    proof {
        let out = if sf == 0 {
            huf_stream(hcode, streams@, n as nat)
        } else {
            huf_4streams(hcode, streams@, n as nat)
        };
        if ok {
            assert(lits@ =~= out.unwrap());
            lemma_huf_len(hcode, streams@, n as nat, sf == 0);
        }
    }
    if !ok {
        return None;
    }
    Some(lh + c)
}

/// The literals section at the start of `b` (`lit_section`). The decoded
/// literals replace `lits`; `huf` is updated to the code to keep. Returns
/// the bytes used.
pub fn lit_section_exec(b: &[u8], bmax: usize, huf: &mut Option<HufTab>, lits: &mut Vec<u8>) -> (r: Option<
    usize,
>)
    requires
        b@.len() < 0x1_0000_0000,
        bmax <= 131072,
        huf_opt_is(*old(huf), old_huf_code(old(huf))),
    ensures
        match lit_section(b@, bmax as nat, old_huf_code(old(huf))) {
            None => r is None,
            Some(l) => {
                &&& r is Some
                &&& r.unwrap() as int == l.used
                &&& final(lits)@ == l.lits
                &&& huf_opt_is(*final(huf), l.huf)
                &&& l.used <= b@.len()
                &&& l.lits.len() <= bmax
            },
        },
{
    if b.len() < 2 {
        proof {
            reveal(lit_section);
        }
        return None;
    }
    if b[0] % 4 <= 1 {
        let ghost hc = old_huf_code(huf);
        lit_plain(b, bmax, lits, Ghost(hc))
    } else {
        lit_huf(b, bmax, huf, lits)
    }
}

/// One lookup in the two-symbol table is one or two steps of `huf_run`.
proof fn lemma_x2_step(rows: Seq<(u8, u8)>, log: nat, s: Seq<u8>, q: int, n: nat, o: Seq<u8>, e: X2e)
    requires
        1 <= log <= 12,
        q >= 2 * log,
        x2_ok(rows, log, bpeek(s, q, log) as int, e),
        1 <= e.n <= 2,
        n >= e.n,
    ensures
        huf_run(rows, log, s, q, n, o) == huf_run(
            rows,
            log,
            s,
            q - e.tot,
            (n - e.n) as nat,
            if e.n == 1 {
                o.push(e.a)
            } else {
                o.push(e.a).push(e.b)
            },
        ),
{
    let v = bpeek(s, q, log);
    let l1 = rows[v as int].1 as nat;
    let q1 = q - l1;
    assert(huf_run(rows, log, s, q, n, o) == huf_run(rows, log, s, q1, (n - 1) as nat, o.push(e.a)));
    if e.n == 2 {
        let m = (log - l1) as nat;
        lemma_bits_split(s, q1 - log, l1, m);
        assert(l1 + m == log);
        assert(q1 - log + l1 == q - log);
        lemma_bits_divmod(s, q - log, m, log);
        lemma_bits_bound(s, q1 - log, l1);
        let f = bits(s, q1 - log, l1) as int;
        let v2 = bpeek(s, q1, log);
        assert(v2 == bits(s, q1 - log, log));
        assert(v == bits(s, q - log, log));
        lemma_mul_is_commutative(pow2(l1) as int, (v % pow2(m)) as int);
        assert(v2 as int == x2_next(log, v as int, l1, f));
        assert(rows[v2 as int] == (e.b, (e.tot - l1) as u8));
        assert((n - 1 - 1) as nat == (n - 2) as nat);
        assert(huf_run(rows, log, s, q1, (n - 1) as nat, o.push(e.a)) == huf_run(
            rows,
            log,
            s,
            q1 - (e.tot - l1),
            (n - 2) as nat,
            o.push(e.a).push(e.b),
        ));
    }
}

/// Adds the two-symbol table to `t`.
pub fn huf_add_x2(t: &mut HufTab)
    requires
        huf_wf(old(t)),
    ensures
        huf_wf(final(t)),
        huf_code_of(final(t)) == huf_code_of(old(t)),
        final(t).syms@ == old(t).syms@,
        final(t).lens@ == old(t).lens@,
        final(t).x1@ == old(t).x1@,
        final(t).log == old(t).log,
{
    let ghost rows = zip(t.syms@, t.lens@);
    let r = t.x1.len();
    let log = t.log;
    proof {
        lemma_u32_pow2_no_overflow(log as nat);
        lemma_pow2_le(log as nat, 12);
        assert(pow2(12) == 4096) by {
            lemma2_to64();
        }
    }
    if r > 4096 {
        return;
    }
    // Pairs are common only where codes average at most about half the
    // table log: skip the table otherwise.
    let mut sum: usize = 0;
    let mut j: usize = 0;
    while j < r
        invariant
            j <= r,
            r <= 4096,
            r == t.lens@.len(),
            r == t.x1@.len(),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
            sum <= 255 * j,
        decreases r - j,
    {
        sum = sum + t.len(j) as usize;
        j = j + 1;
    }
    proof {
        assert(1 <= log <= 12);
        lemma_mul_inequality(log as int + 1, 13, r as int);
    }
    if 2 * sum > (log as usize + 1) * r {
        return;
    }
    // runend[x]: the end of the run of equal rows that holds x.
    let mut runend: Vec<usize> = vec![0usize; r];
    let mut k: usize = r;
    while k > 0
        invariant
            k <= r,
            r == t.syms@.len(),
            t.syms@.len() == t.lens@.len(),
            rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
            runend@.len() == r,
            forall|x: int|
                #![trigger runend@[x]]
                k <= x < r ==> x < runend@[x] <= r && forall|y: int| x <= y < runend@[x] ==> #[trigger] rows[y] == rows[x],
        decreases k,
    {
        k = k - 1;
        let e = if k + 1 < r && t.sym(k) == t.sym(k + 1) && t.len(k) == t.len(k + 1) {
            runend[k + 1]
        } else {
            k + 1
        };
        proof {
            if k + 1 < r && t.syms@[k as int] == t.syms@[k + 1] && t.lens@[k as int] == t.lens@[k + 1] {
                assert(rows[k as int] == rows[k + 1]);
                assert forall|y: int| k <= y < e implies #[trigger] rows[y] == rows[k as int] by {
                    if y > k {
                        assert(rows[y] == rows[k + 1]);
                    }
                }
            }
        }
        runend.set(k, e);
    }
    proof {
        lemma_u32_pow2_no_overflow(log as nat);
        lemma_u32_shl_is_mul(1, log);
        lemma_pow2_le(log as nat, 12);
        assert(pow2(12) == 4096) by {
            lemma2_to64();
        }
    }
    let size: usize = (1u32 << log) as usize;
    let mut x2: Vec<X2e> = Vec::with_capacity(size);
    let mut pairs: usize = 0;
    let mut v: usize = 0;
    while v < size
        invariant
            v <= size,
            size == pow2(log as nat),
            size <= 4096,
            1 <= log <= 12,
            log == t.log,
            r == t.syms@.len(),
            t.syms@.len() == t.lens@.len(),
            lens_le(t.lens@, t.log),
            rows == zip(t.syms@, t.lens@),
            x1_ok(t.x1@, t.syms@, t.lens@, t.log),
            runend@.len() == r,
            forall|x: int|
                #![trigger runend@[x]]
                0 <= x < r ==> x < runend@[x] <= r && forall|y: int| x <= y < runend@[x] ==> #[trigger] rows[y] == rows[x],
            x2@.len() == v,
            pairs <= v,
            forall|j: int| #![trigger x2@[j]] 0 <= j < v ==> x2_ok(rows, log as nat, j, x2@[j]),
        decreases size - v,
    {
        let ent = if v >= r {
            X2e { a: 0, b: 0, n: 0, tot: 0 }
        } else {
            let a = t.sym(v);
            let l1 = t.len(v) as u32;
            proof {
                assert(t.lens@[v as int] <= log);
            }
            let m = log - l1;
            proof {
                lemma_u32_pow2_no_overflow(m as nat);
                lemma_u32_shl_is_mul(1, m);
                lemma_u32_low_bits_mask_is_mod(v as u32, m as nat);
                lemma_pow2_pos(m as nat);
                lemma_pow2_pos(l1 as nat);
                lemma_pow2_adds(m as nat, l1 as nat);
                assert(low_bits_mask(m as nat) == pow2(m as nat) - 1);
            }
            let lo = (v as u32) & ((1u32 << m) - 1);
            proof {
                assert(lo as nat == (v as nat) % pow2(m as nat));
                assert(lo < pow2(m as nat));
                lemma_mul_inequality(lo as int, pow2(m as nat) - 1, pow2(l1 as nat) as int);
                lemma_mul_is_distributive_sub_other_way(pow2(l1 as nat) as int, pow2(m as nat) as int, 1);
                assert((lo as int) * pow2(l1 as nat) + pow2(l1 as nat) <= pow2(log as nat));
                lemma_u32_shl_is_mul(lo, l1);
                lemma_u32_pow2_no_overflow(l1 as nat);
                lemma_u32_shl_is_mul(1, l1);
            }
            let u = (lo << l1) as usize;
            let span = (1u32 << l1) as usize;
            if u < r && u + span <= runend[u] && l1 + t.len(u) as u32 <= log {
                let b = t.sym(u);
                let tot = l1 + t.len(u) as u32;
                proof {
                    assert forall|f: int| 0 <= f < pow2(l1 as nat) implies 0 <= #[trigger] x2_next(log as nat, v as int, l1 as nat, f) < rows.len()
                        && rows[x2_next(log as nat, v as int, l1 as nat, f)] == (b, (tot - l1) as u8) by {
                        assert(x2_next(log as nat, v as int, l1 as nat, f) == u + f);
                        assert(rows[u + f] == rows[u as int]);
                    }
                }
                X2e { a: a, b: b, n: 2, tot: tot as u8 }
            } else {
                X2e { a: a, b: 0, n: 1, tot: l1 as u8 }
            }
        };
        if ent.n == 2 {
            pairs = pairs + 1;
        }
        x2.push(ent);
        v = v + 1;
    }
    // Kept only where a good share of lookups give two symbols: otherwise
    // the one-symbol loop is faster.
    if pairs * 8 >= size * 3 {
        t.x2 = x2;
    }
}

/// The code `huf` holds, as the spec sees it.
pub open spec fn old_huf_code(h: &Option<HufTab>) -> Option<HufCode> {
    match *h {
        None => None,
        Some(t) => Some(huf_code_of(&t)),
    }
}

/// A stream decodes to exactly the symbols asked for.
/// A run of `a + b` symbols is a run of `a`, then one of `b`.
proof fn lemma_huf_run_split(rows: Seq<(u8, u8)>, log: nat, s: Seq<u8>, p: int, a: nat, b: nat, out: Seq<u8>)
    ensures
        huf_run(rows, log, s, p, a + b, out) == match huf_run(rows, log, s, p, a, out) {
            None => None,
            Some((o, q)) => huf_run(rows, log, s, q, b, o),
        },
    decreases a,
{
    if a > 0 {
        let v = bpeek(s, p, log);
        if v < rows.len() {
            let (sym, len) = rows[v as int];
            if len as int <= p {
                lemma_huf_run_split(rows, log, s, p - len, (a - 1) as nat, b, out.push(sym));
                assert((a - 1) as nat + b == (a + b - 1) as nat);
            }
        }
    }
}

proof fn lemma_huf_run_len(rows: Seq<(u8, u8)>, log: nat, s: Seq<u8>, p: int, n: nat, out: Seq<u8>)
    ensures
        huf_run(rows, log, s, p, n, out) is Some ==> huf_run(rows, log, s, p, n, out).unwrap().0.len()
            == out.len() + n,
    decreases n,
{
    if n > 0 {
        let v = bpeek(s, p, log);
        if v < rows.len() {
            let (sym, len) = rows[v as int];
            lemma_huf_run_len(rows, log, s, p - len, (n - 1) as nat, out.push(sym));
        }
    }
}

proof fn lemma_huf_stream_len(c: HufCode, b: Seq<u8>, n: nat)
    ensures
        huf_stream(c, b, n) is Some ==> huf_stream(c, b, n).unwrap().len() == n,
{
    if let Some(p) = bstart(b) {
        lemma_huf_run_len(huf_rows(c), c.log, b, p, n, Seq::empty());
    }
}

proof fn lemma_huf_len(c: HufCode, b: Seq<u8>, n: nat, one: bool)
    ensures
        one && huf_stream(c, b, n) is Some ==> huf_stream(c, b, n).unwrap().len() == n,
        !one && huf_4streams(c, b, n) is Some ==> huf_4streams(c, b, n).unwrap().len() == n,
{
    if one {
        lemma_huf_stream_len(c, b, n);
    } else if huf_4streams(c, b, n) is Some {
        let l1 = le(b, 0, 2) as int;
        let l2 = le(b, 2, 2) as int;
        let l3 = le(b, 4, 2) as int;
        let seg = (n + 3) / 4;
        let a2 = 6 + l1;
        let a3 = a2 + l2;
        let a4 = a3 + l3;
        lemma_huf_stream_len(c, b.subrange(6, a2), seg as nat);
        lemma_huf_stream_len(c, b.subrange(a2, a3), seg as nat);
        lemma_huf_stream_len(c, b.subrange(a3, a4), seg as nat);
        lemma_huf_stream_len(c, b.subrange(a4, b.len() as int), (n - 3 * seg) as nat);
    }
}

} // verus!
