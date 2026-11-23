//! Canonical prefix code decoding tables: the table builder and slow-path
//! decoder shared by vwebp (WebP lossless) and vbrotli (Brotli prefix codes,
//! the same canonical codes). `MAX_ALPHA` is WebP's largest alphabet, an
//! upper bound for Brotli's.
//!
//! A table is indexed by the next `tbits` input bits (first bit least
//! significant). Entry `i` holds the symbol whose code is the shortest
//! prefix of `i`'s bits, with its length, if that code is at most `tbits`
//! long. Codes longer than `tbits` (at most `MAX_ROOT`) are rare; their
//! entries say `LONG` and the decoder falls back to `decode_slow`, which
//! walks the canonical code one length at a time exactly as
//! `spec::decode` does. A code with a single symbol has a one-entry table
//! (`tbits == 0`) whose entry takes zero bits.
//!
//! Tables are filled from the longest code to the shortest, so a shorter
//! match overwrites a longer one and every entry ends up holding the
//! shortest match. That is the spec's definition, so the proof never needs
//! the (true, but harder) fact that valid codes are prefix-free.
#[cfg(verus_only)]
use crate::huffman::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
pub use crate::huffman::{reverse, reverse_fast};
use crate::prims::set32;
use vstd::prelude::*;
use alloc::vec;
use alloc::vec::Vec;

verus! {

/// The longest code length, in bits.
pub const MAX_LEN: usize = 15;

/// Largest alphabet: 256 + 24 + 2048 (11 color cache bits).
pub const MAX_ALPHA: usize = 2328;

/// Most table bits.
pub const MAX_ROOT: u32 = 10;

/// Entry layout: bits 0..12 hold the symbol, bits 16..20 the code length.
/// `LONG`: no code of at most `tbits` bits matches.
pub const LONG: u32 = 0x8000_0000;

pub open spec fn ent(s: nat, l: nat) -> u32 {
    (l * 0x1_0000 + s) as u32
}

/// Everything `decode_slow` needs about a canonical code, by code length:
/// how many symbols have it, the first code, and where its symbols start in
/// `sorted` (all symbols with a code, ordered by length, then value).
pub struct HCode {
    /// The lookup table: `1 << tbits` entries, indexed by the next `tbits` bits (bit-reversed), each the symbol and its length, or `LONG`.
    pub table: Vec<u32>,
    /// The table's index width, at most `MAX_ROOT`.
    pub tbits: u32,
    /// How many symbols have a code of each length.
    pub count: [u16; 16],
    /// The first canonical code of each length.
    pub first: [u32; 16],
    /// Where the symbols of each length start in `sorted`.
    pub offs: [u16; 16],
    /// Every symbol with a code, ordered by code length, then by value.
    pub sorted: Vec<u16>,
}

// ---------------------------------------------------------------------------
// Specification of the tables
// ---------------------------------------------------------------------------

/// What `decode_slow` returns for the number `x` of which `avail` bits
/// are known.
pub open spec fn slow_result(lens: Seq<u8>, x: nat, avail: nat) -> Option<u32> {
    match decode_num(lens, x, avail, 1) {
        Some((s, k)) => Some(ent(s, k)),
        None => None,
    }
}

/// `code` describes the canonical code of `lens` at length `l`.
pub open spec fn len_ok(code: HCode, lens: Seq<u8>, l: nat) -> bool {
    let li = l as int;
    &&& code.count@[li] as nat == count(lens, l)
    &&& code.first@[li] as nat == first_code(lens, l)
    &&& code.offs@[li] as nat + count(lens, l) <= code.sorted@.len()
    &&& forall|r: nat|
        r < count(lens, l) ==> code.sorted@[code.offs@[li] as int + r] as int
            == #[trigger] nth_with_len(lens, l, r, 0)
}

pub open spec fn code_ok(code: HCode, lens: Seq<u8>) -> bool {
    forall|l: nat| 1 <= l <= 15 ==> #[trigger] len_ok(code, lens, l)
}

/// Entry `x` of a `t`-bit table: the shortest code that is a prefix of
/// `x`'s bits, or `LONG` if there is none of at most `t` bits.
pub open spec fn tab_entry(lens: Seq<u8>, x: nat, t: nat) -> u32 {
    match decode_num(lens, x, t, 1) {
        Some((s, k)) => ent(s, k),
        None => LONG,
    }
}

pub open spec fn table_ok(table: Seq<u32>, lens: Seq<u8>, t: nat) -> bool {
    &&& pow2(t) <= table.len()
    &&& forall|i: int| 0 <= i < pow2(t) ==> #[trigger] table[i] == tab_entry(lens, i as nat, t)
}

/// A built code for the code lengths `lens`.
pub open spec fn hcode_ok(h: HCode, lens: Seq<u8>) -> bool {
    &&& valid_code(lens)
    &&& lens.len() <= MAX_ALPHA
    &&& h.tbits <= MAX_ROOT
    &&& h.table@.len() == pow2(h.tbits as nat)
    &&& if used(lens) == 1 {
        &&& h.tbits == 0
        &&& 0 <= first_used(lens, 0) < lens.len()
        &&& h.table@[0] == ent(first_used(lens, 0) as nat, 0)
    } else {
        &&& 1 <= h.tbits
        &&& table_ok(h.table@, lens, h.tbits as nat)
        &&& code_ok(h, lens)
    }
}

/// While filling: entries are right for every length from `l` up.
pub open spec fn fill_ok(e: u32, lens: Seq<u8>, x: nat, t: nat, l: nat, init: bool) -> bool {
    match decode_num(lens, x, t, l) {
        Some((s, k)) => e == ent(s, k),
        None => init ==> e == LONG,
    }
}

/// While filling length `l`: the first `r` codes of length `l` are in.
pub open spec fn mid_ok(e: u32, old_e: u32, lens: Seq<u8>, x: nat, l: nat, r: nat) -> bool {
    let v = rev(x, l);
    let f = first_code(lens, l);
    if f <= v && v < f + r {
        e == ent(nth_with_len(lens, l, (v - f) as nat, 0) as nat, l)
    } else {
        e == old_e
    }
}

// ---------------------------------------------------------------------------
// Entries
// ---------------------------------------------------------------------------

/// The table entry of symbol `s` with a code `l` bits long.
#[inline(always)]
pub fn entry(s: u32, l: u32) -> (r: u32)
    requires
        s < 0x1_0000,
        l <= 15,
    ensures
        r == ent(s as nat, l as nat),
        r & LONG == 0,
        r >> 16u32 == l,
        r & 0xffff == s,
{
    assert(((l << 16u32) | s) == l * 0x1_0000 + s && ((l << 16u32) | s) & 0x8000_0000 == 0 && ((l
        << 16u32) | s) >> 16u32 == l && ((l << 16u32) | s) & 0xffff == s) by (bit_vector)
        requires
            s < 0x1_0000,
            l <= 15,
    ;
    (l << 16) | s
}

// ---------------------------------------------------------------------------
// Building
// ---------------------------------------------------------------------------

/// If no length below `s` is set, the first symbol with a code is at `s`
/// or later.
pub proof fn lemma_first_used_skip(lens: Seq<u8>, s: int)
    requires
        0 <= s <= lens.len(),
        forall|j: int| 0 <= j < s ==> lens[j] == 0,
    ensures
        first_used(lens, 0) == first_used(lens, s),
    decreases s,
{
    if s > 0 {
        lemma_first_used_skip_from(lens, 0, s);
    }
}

proof fn lemma_first_used_skip_from(lens: Seq<u8>, a: int, s: int)
    requires
        0 <= a <= s <= lens.len(),
        forall|j: int| a <= j < s ==> lens[j] == 0,
    ensures
        first_used(lens, a) == first_used(lens, s),
    decreases s - a,
{
    if a < s {
        lemma_first_used_skip_from(lens, a + 1, s);
    }
}

/// With no length set among the first `n`, they all count as length 0.
pub proof fn lemma_count_zeros(lens: Seq<u8>, n: int)
    requires
        0 <= n <= lens.len(),
        forall|j: int| 0 <= j < n ==> lens[j] == 0,
    ensures
        count_below(lens, 0, n) == n,
    decreases n,
{
    if n > 0 {
        lemma_count_zeros(lens, n - 1);
    }
}

/// Builds the decoding structures from code lengths, with at most
/// `max_root` table bits. Returns `None` iff the lengths are not
/// `spec::valid_code`. Also returns the number of loop iterations it ran,
/// at most `build_cost(lens.len(), max_root)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn build(lens: &[u8], max_root: u32) -> (r: (Option<HCode>, Ghost<nat>))
    requires
        1 <= max_root <= MAX_ROOT,
        1 <= lens@.len() <= MAX_ALPHA,
    ensures
        r.0 is Some == valid_code(lens@),
        r.0 matches Some(h) ==> hcode_ok(h, lens@) && h.tbits <= max_root,
        r.1@ <= build_cost(lens@.len(), max_root as nat),
{
    let ghost ls = lens@;
    let n = lens.len();
    let ghost mut w: nat = 0;
    proof {
        lemma2_to64();
    }
    // Count the symbols of each length.
    let mut cnts = [0u16; 16];
    let mut s: usize = 0;
    while s < n
        invariant
            ls == lens@,
            n == ls.len(),
            n <= MAX_ALPHA,
            s <= n,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count_below(ls, l as nat, s as int),
            forall|i: int| 0 <= i < s ==> #[trigger] ls[i] as nat <= 15,
            w == s,
        decreases n - s,
    {
        proof {
            w = w + 1;
        }
        let l = lens[s] as usize;
        if l > MAX_LEN {
            proof {
                assert(!(ls[s as int] as nat <= MAX_BITS));
            }
            return (None, Ghost(w));
        }
        proof {
            lemma_count_below_le(ls, l as nat, s as int);
        }
        cnts[l] = cnts[l] + 1;
        s = s + 1;
    }
    assert(forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat));
    proof {
        lemma_count_below_le(ls, 0, n as int);
    }
    let nz = n - cnts[0] as usize;
    assert(nz == used(ls));
    if nz == 0 {
        return (None, Ghost(w));
    }
    if nz == 1 {
        // A single symbol: a one-entry table whose code takes no bits.
        let mut s: usize = 0;
        while s < n && lens[s] == 0
            invariant
                ls == lens@,
                n == ls.len(),
                n <= MAX_ALPHA,
                s <= n,
                forall|j: int| 0 <= j < s ==> ls[j] == 0,
                w <= 2 * n,
                w == n + s,
            decreases n - s,
        {
            proof {
                w = w + 1;
            }
            s = s + 1;
        }
        if s == n {
            proof {
                lemma_count_zeros(ls, n as int);
            }
            assert(false);
            return (None, Ghost(w));
        }
        proof {
            lemma_first_used_skip(ls, s as int);
        }
        let mut table: Vec<u32> = Vec::new();
        table.push(entry(s as u32, 0));
        proof {
            assert(pow2(0) == 1);
        }
        let h = HCode {
            table,
            tbits: 0,
            count: [0u16; 16],
            first: [0u32; 16],
            offs: [0u16; 16],
            sorted: Vec::new(),
        };
        return (Some(h), Ghost(w));
    }
    // Kraft: `rem` codes of length `l` remain unassigned.
    let mut rem: i32 = 1;
    let mut l: usize = 1;
    while l <= MAX_LEN
        invariant
            ls == lens@,
            1 <= l <= 16,
            rem as int == left(ls, (l - 1) as nat),
            0 <= rem <= pow2((l - 1) as nat),
            pow2(14) == 16384,
            forall|k: nat| 1 <= k < l ==> #[trigger] left(ls, k) >= 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            n == ls.len(),
            n <= MAX_ALPHA,
            nz == used(ls),
            nz >= 2,
            w == n + l - 1,
        decreases 16 - l,
    {
        proof {
            w = w + 1;
            if l - 1 < 14 {
                lemma_pow2_strictly_increases((l - 1) as nat, 14);
            }
            lemma_pow2_unfold(l as nat);
            assert(cnts@[l as int] as nat == count(ls, l as nat));
        }
        rem = 2 * rem - cnts[l] as i32;
        if rem < 0 {
            proof {
                assert(left(ls, l as nat) < 0);
                assert(1 <= l as nat <= MAX_BITS);
                assert(used(ls) != 1);
                assert(!valid_code(ls));
            }
            return (None, Ghost(w));
        }
        l = l + 1;
    }
    if rem != 0 {
        return (None, Ghost(w));
    }
    assert(valid_code(ls));
    let mut sorted: Vec<u16> = vec![0u16; n];
    // Where each length's symbols start in `sorted`.
    let mut offs = [0u16; 16];
    proof {
        lemma_csum_all(ls, n as int);
        assert(csum(ls, 1, n as int) == count(ls, 0)) by {
            assert(csum(ls, 0, n as int) == 0);
        }
    }
    let mut l: usize = 1;
    while l < MAX_LEN
        invariant
            ls == lens@,
            1 <= l <= 15,
            n == ls.len(),
            n <= MAX_ALPHA,
            csum(ls, 16, n as int) == n,
            left(ls, 15) == 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 1 <= k <= l ==> #[trigger] offs@[k] as nat + count(ls, 0) == csum(ls, k as nat, n as int),
            w == n + 15 + l - 1,
        decreases 15 - l,
    {
        proof {
            w = w + 1;
            lemma_csum_mono(ls, (l + 1) as nat, 16, n as int);
            assert(cnts@[l as int] as nat == count(ls, l as nat));
            assert(offs@[l as int] as nat + count(ls, 0) == csum(ls, l as nat, n as int));
        }
        offs[l + 1] = offs[l] + cnts[l];
        l = l + 1;
    }
    assert forall|k: int| 1 <= k <= 15 implies #[trigger] offs@[k] as nat + count(ls, k as nat) <= n
        - count(ls, 0) by {
        lemma_csum_mono(ls, (k + 1) as nat, 16, n as int);
        assert(offs@[k] as nat + count(ls, 0) == csum(ls, k as nat, n as int));
    }
    assert forall|a: int, b: int| 1 <= a < b <= 15 implies #[trigger] offs@[a] as nat + count(
        ls,
        a as nat,
    ) <= #[trigger] offs@[b] as nat by {
        lemma_csum_mono(ls, (a + 1) as nat, b as nat, n as int);
        assert(offs@[a] as nat + count(ls, 0) == csum(ls, a as nat, n as int));
        assert(offs@[b] as nat + count(ls, 0) == csum(ls, b as nat, n as int));
    }
    // Counting sort of the symbols by length.
    let mut next = offs;
    let mut s: usize = 0;
    while s < n
        invariant
            ls == lens@,
            n == ls.len(),
            n <= MAX_ALPHA,
            sorted@.len() == n,
            left(ls, 15) == 0,
            s <= n,
            forall|i: int| 0 <= i < n ==> #[trigger] ls[i] as nat <= 15,
            forall|k: int| 1 <= k <= 15 ==> #[trigger] offs@[k] as nat + count(ls, k as nat) <= n
                - count(ls, 0),
            forall|a: int, b: int|
                1 <= a < b <= 15 ==> #[trigger] offs@[a] as nat + count(ls, a as nat)
                    <= #[trigger] offs@[b] as nat,
            forall|k: int|
                1 <= k <= 15 ==> #[trigger] next@[k] as nat == offs@[k] as nat + count_below(
                    ls,
                    k as nat,
                    s as int,
                ),
            forall|k: nat, r: nat|
                1 <= k <= 15 && r < count_below(ls, k, s as int) ==> sorted@[offs@[k as int]
                    as int + r] as int == #[trigger] nth_with_len(ls, k, r, 0),
            w == n + 29 + s,
        decreases n - s,
    {
        proof {
            w = w + 1;
        }
        let l = lens[s] as usize;
        assert forall|k: nat| 1 <= k <= 15 implies #[trigger] count_below(ls, k, s + 1) <= count(
            ls,
            k,
        ) by {
            lemma_count_below_mono(ls, k, s + 1, n as int);
        }
        if l != 0 {
            proof {
                lemma_nth_rank(ls, l as nat, s as int, 0);
                assert(count_below(ls, l as nat, s + 1) <= count(ls, l as nat));
                assert(next@[l as int] as nat == offs@[l as int] as nat + count_below(
                    ls,
                    l as nat,
                    s as int,
                ));
                assert(offs@[l as int] as nat + count(ls, l as nat) <= n - count(ls, 0));
            }
            let ghost old_sorted = sorted@;
            sorted.set(next[l] as usize, s as u16);
            next[l] = next[l] + 1;
            assert forall|k: nat, r: nat|
                1 <= k <= 15 && r < count_below(ls, k, s + 1) implies sorted@[offs@[k as int]
                as int + r] as int == #[trigger] nth_with_len(ls, k, r, 0) by {
                if k == l as nat && r == count_below(ls, k, s as int) {
                } else {
                    assert(count_below(ls, k, s + 1) <= count(ls, k));
                    assert(offs@[k as int] as nat + count(ls, k) <= n - count(ls, 0));
                    if (k as int) < l as int {
                        assert(offs@[k as int] as nat + count(ls, k) <= offs@[l as int] as nat);
                    } else if (k as int) > l as int {
                        assert(offs@[l as int] as nat + count(ls, l as nat) <= offs@[k as int] as nat);
                    }
                    assert(old_sorted[offs@[k as int] as int + r] as int == nth_with_len(ls, k, r, 0));
                }
            }
        }
        s = s + 1;
    }
    proof {
        lemma_csum_all(ls, n as int);
    }
    // The first code of each length.
    let mut first = [0u32; 16];
    let mut l: usize = 2;
    while l <= MAX_LEN
        invariant
            ls == lens@,
            2 <= l <= 16,
            pow2(14) == 16384,
            forall|k: nat| 1 <= k <= 15 ==> #[trigger] left(ls, k) >= 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 0 <= k < l ==> #[trigger] first@[k] as nat == first_code(ls, k as nat),
            n == ls.len(),
            w == 2 * n + 29 + l - 2,
            left(ls, 15) == 0,
            csum(ls, 16, n as int) == n,
        decreases 16 - l,
    {
        proof {
            w = w + 1;
            assert(left(ls, (l - 1) as nat) >= 0);
            lemma_codes_fit(ls, (l - 1) as nat);
            if l - 1 < 14 {
                lemma_pow2_strictly_increases((l - 1) as nat, 14);
            }
            assert(first@[l - 1] as nat == first_code(ls, (l - 1) as nat));
            assert(cnts@[l - 1] as nat == count(ls, (l - 1) as nat));
        }
        first[l] = 2 * (first[l - 1] + cnts[l - 1] as u32);
        l = l + 1;
    }
    let mut code = HCode { table: Vec::new(), tbits: 0, count: cnts, first, offs, sorted };
    assert forall|l: nat| 1 <= l <= 15 implies #[trigger] len_ok(code, ls, l) by {
        assert(cnts@[l as int] as nat == count(ls, l));
        assert(first@[l as int] as nat == first_code(ls, l));
        assert(offs@[l as int] as nat + count(ls, l) <= n - count(ls, 0));
    }
    assert(code_ok(code, ls));
    // The table needs as many bits as the longest code, up to `max_root`.
    // Without longer codes it is complete; otherwise entries no code fills
    // say `LONG`.
    let mut longest: usize = MAX_LEN;
    while longest > 0 && cnts[longest] == 0
        invariant
            ls == lens@,
            longest <= 15,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: nat| longest < k <= 15 ==> #[trigger] count(ls, k) == 0,
            n == ls.len(),
            w == 2 * n + 43 + 15 - longest,
            left(ls, 15) == 0,
            csum(ls, 16, n as int) == n,
        decreases longest,
    {
        proof {
            w = w + 1;
        }
        assert(cnts@[longest as int] as nat == count(ls, longest as nat));
        longest = longest - 1;
    }
    if longest == 0 {
        // Every length is unused, but `used(ls) >= 2`.
        proof {
            assert forall|k: nat| 0 < k <= 15 implies #[trigger] count(ls, k) == 0 by {}
            lemma_left_tail(ls, 0, 15);
            lemma_pow2_pos(15);
            assert(left(ls, 0) == 1);
        }
        assert(false);
        return (None, Ghost(w));
    }
    let tbits: u32 = if longest as u32 > max_root {
        max_root
    } else {
        longest as u32
    };
    proof {
        lemma_usize_shl_is_mul(1, tbits as usize);
        lemma_pow2_strictly_increases(tbits as nat, 16);
        lemma_pow2_strictly_increases(tbits as nat, 11);
    }
    let size = 1usize << (tbits as usize);
    let init = longest > tbits as usize;
    let mut table: Vec<u32> = vec![LONG; size];
    assert(forall|j: int| 0 <= j < size ==> #[trigger] table@[j] == LONG);
    let ghost w6 = w;
    proof {
        w = w + size as nat;
    }
    // Longest first, so shorter matches win.
    let ghost w7 = w;
    assert(w7 <= 2 * n + 58 + size);
    proof {
        lemma_csum_mono(ls, 1, (tbits + 1) as nat, n as int);
        lemma_csum_mono(ls, (tbits + 1) as nat, 16, n as int);
    }
    let mut l = tbits as usize;
    while l >= 1
        invariant
            ls == lens@,
            n == ls.len(),
            w <= w7 + (tbits - l) + 16 * (csum(ls, (tbits + 1) as nat, n as int) - csum(
                ls,
                (l + 1) as nat,
                n as int,
            )) + fill_cost(ls, tbits as nat, l as nat),
            csum(ls, (l + 1) as nat, n as int) <= csum(ls, (tbits + 1) as nat, n as int),
            csum(ls, (tbits + 1) as nat, n as int) <= n,
            l <= tbits <= MAX_ROOT,
            1 <= tbits,
            code.sorted@.len() == n,
            n <= MAX_ALPHA,
            size == pow2(tbits as nat),
            size <= 1024,
            table@.len() == size,
            code_ok(code, ls),
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 0 <= k < 16 ==> #[trigger] first@[k] as nat == first_code(ls, k as nat),
            forall|k: int| 0 <= k < 16 ==> #[trigger] offs@[k] == code.offs@[k],
            forall|k: nat| 1 <= k <= 15 ==> #[trigger] left(ls, k) >= 0,
            forall|i: int|
                0 <= i < size ==> #[trigger] fill_ok(
                    table@[i],
                    ls,
                    i as nat,
                    tbits as nat,
                    (l + 1) as nat,
                    init,
                ),
        decreases l,
    {
        let base = offs[l] as usize;
        let cnt = cnts[l] as usize;
        proof {
            w = w + 1;
            lemma_pow2_pos(l as nat);
            if l < 15 {
                lemma_pow2_strictly_increases(l as nat, 15);
            }
            lemma2_to64();
            lemma_usize_shl_is_mul(1, l);
            assert(len_ok(code, ls, l as nat));
            assert(left(ls, l as nat) >= 0);
            lemma_codes_fit(ls, l as nat);
        }
        let step = 1usize << l;
        let ghost tl = table@;
        let ghost q = pow2((tbits - l) as nat);
        let ghost wl = w;
        proof {
            lemma_pow2_adds(l as nat, (tbits - l) as nat);
            lemma_pow2_pos((tbits - l) as nat);
            assert(size == step * q);
        }
        let mut r: usize = 0;
        while r < cnt
            invariant
                ls == lens@,
                size == step * q,
                q >= 1,
                w <= wl + 16 * r + r * q,
                1 <= l <= tbits <= 15,
                r <= cnt,
                cnt == count(ls, l as nat),
                base == code.offs@[l as int],
                len_ok(code, ls, l as nat),
                code.sorted@.len() == n,
                n <= MAX_ALPHA,
                first@[l as int] as nat == first_code(ls, l as nat),
                first_code(ls, l as nat) + count(ls, l as nat) <= pow2(l as nat),
                step == pow2(l as nat),
                step <= 32768,
                size == pow2(tbits as nat),
                size <= 1024,
                table@.len() == size,
                forall|i: int|
                    0 <= i < size ==> #[trigger] mid_ok(
                        table@[i],
                        tl[i],
                        ls,
                        i as nat,
                        l as nat,
                        r as nat,
                    ),
            decreases cnt - r,
        {
            let sym = code.sorted[base + r] as u32;
            assert(sym as int == nth_with_len(ls, l as nat, r as nat, 0));
            let c = first[l] + r as u32;
            let e = entry(sym, l as u32);
            let (rv, Ghost(rw)) = reverse(c, l as u32);
            let rc = rv as usize;
            proof {
                w = w + 1 + rw;
                lemma_rev_bound(c as nat, l as nat);
                lemma_small_mod(rc as nat, step as nat);
            }
            let mut i = rc;
            let ghost tr = table@;
            let ghost wr = w;
            let ghost mut k: nat = 0;
            assert forall|j: int| 0 <= j < size implies #[trigger] table@[j] == (if j % (
            step as int) == rc && j < i {
                e
            } else {
                tr[j]
            }) by {
                if j < rc {
                    lemma_small_mod(j as nat, step as nat);
                }
            }
            while i < size
                invariant
                    ls == lens@,
                    rc < step,
                    step == pow2(l as nat),
                    step <= 32768,
                    size <= 1024,
                    i % step == rc,
                    i <= size + step,
                    size == step * q,
                    i == rc + k * step,
                    k <= q,
                    w == wr + k,
                    table@.len() == size,
                    forall|j: int|
                        0 <= j < size ==> #[trigger] table@[j] == (if j % (step as int) == rc && j
                            < i {
                            e
                        } else {
                            tr[j]
                        }),
                decreases size + step - i,
            {
                set32(&mut table, i, e);
                proof {
                    w = w + 1;
                    assert(k < q) by (nonlinear_arith)
                        requires
                            rc + k * step < step * q,
                            step > 0,
                    ;
                    assert(rc + k * step + step == rc + (k + 1) * step) by (nonlinear_arith);
                    k = k + 1;
                    lemma_mod_add_multiples_vanish(i as int, step as int);
                    assert forall|j: int| 0 <= j < size implies #[trigger] table@[j] == (if j % (
                    step as int) == rc && j < i + step {
                        e
                    } else {
                        tr[j]
                    }) by {
                        if j % (step as int) == rc && i <= j < i + step {
                            lemma_same_residue(i as int, j, step as int);
                        }
                    }
                }
                i = i + step;
            }
            proof {
                assert forall|j: int| 0 <= j < size implies #[trigger] mid_ok(
                    table@[j],
                    tl[j],
                    ls,
                    j as nat,
                    l as nat,
                    (r + 1) as nat,
                ) by {
                    lemma_rev_iff(j as nat, c as nat, l as nat);
                    assert(mid_ok(tr[j], tl[j], ls, j as nat, l as nat, r as nat));
                }
                assert(r * q + q == (r + 1) * q) by (nonlinear_arith);
            }
            r = r + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < size implies #[trigger] fill_ok(
                table@[j],
                ls,
                j as nat,
                tbits as nat,
                l as nat,
                init,
            ) by {
                assert(mid_ok(table@[j], tl[j], ls, j as nat, l as nat, r as nat));
                assert(fill_ok(tl[j], ls, j as nat, tbits as nat, (l + 1) as nat, init));
            }
            assert(fill_cost(ls, tbits as nat, (l - 1) as nat) == fill_cost(ls, tbits as nat, l as nat)
                + count(ls, l as nat) * q);
            assert(csum(ls, (l + 1) as nat, n as int) == csum(ls, l as nat, n as int) + cnt);
        }
        l = l - 1;
    }
    proof {
        if !init {
            assert forall|k: nat| tbits < k <= 15 implies #[trigger] count(ls, k) == 0 by {}
            lemma_left_tail(ls, tbits as nat, 15);
            lemma_pow2_pos((15 - tbits) as nat);
            let p = pow2((15 - tbits) as nat) as int;
            assert(left(ls, tbits as nat) == 0) by (nonlinear_arith)
                requires
                    p > 0,
                    0 == p * left(ls, tbits as nat),
            ;
        }
        assert forall|i: int| 0 <= i < pow2(tbits as nat) implies #[trigger] table@[i] == tab_entry(
            ls,
            i as nat,
            tbits as nat,
        ) by {
            assert(fill_ok(table@[i], ls, i as nat, tbits as nat, (l + 1) as nat, init));
            assert((l + 1) as nat == 1);
            if !init {
                lemma_complete_decodes(ls, i as nat, tbits as nat);
            }
        }
        assert(left(ls, tbits as nat) >= 0);
        lemma_fill_bound(ls, tbits as nat);
    }
    code.table = table;
    code.tbits = tbits;
    assert(code_ok(code, ls));
    (Some(code), Ghost(w))
}

// --- sparse build: begin
/// `used` lists, in order, the symbols of `lens` that have a code.
pub open spec fn sparse_ok(lens: Seq<u8>, used: Seq<(u16, u8)>) -> bool {
    &&& used.len() + count(lens, 0) == lens.len()
    &&& forall|i: int|
        0 <= i < used.len() ==> ((#[trigger] used[i]).0 as int) < lens.len() && lens[used[i].0 as int] != 0
            && lens[used[i].0 as int] == used[i].1 && used[i].0 - count_below(lens, 0, used[i].0 as int) == i
}

/// Symbols `a..b` have no code when all of them count as length 0.
pub proof fn lemma_zero_gap(lens: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= lens.len(),
        count_below(lens, 0, b) - count_below(lens, 0, a) == b - a,
    ensures
        forall|j: int| a <= j < b ==> lens[j] == 0,
    decreases b - a,
{
    if a < b {
        lemma_count_below_mono(lens, 0, a, b - 1);
        lemma_count_below_le_from(lens, a, b - 1);
        lemma_zero_gap(lens, a, b - 1);
    }
}

/// At most `b - a` of the symbols `a..b` have length 0.
pub proof fn lemma_count_below_le_from(lens: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        count_below(lens, 0, b) - count_below(lens, 0, a) <= b - a,
    decreases b - a,
{
    if a < b {
        lemma_count_below_le_from(lens, a, b - 1);
    }
}

/// Symbols without a code add nothing to the count of a length `k >= 1`.
pub proof fn lemma_zero_gap_count(lens: Seq<u8>, k: nat, a: int, b: int)
    requires
        0 <= a <= b <= lens.len(),
        k >= 1,
        count_below(lens, 0, b) - count_below(lens, 0, a) == b - a,
    ensures
        count_below(lens, k, b) == count_below(lens, k, a),
    decreases b - a,
{
    if a < b {
        lemma_count_below_mono(lens, 0, a, b - 1);
        lemma_count_below_le_from(lens, a, b - 1);
        lemma_zero_gap_count(lens, k, a, b - 1);
    }
}

/// No symbol before the first listed one has a code.
pub proof fn lemma_zero_prefix(lens: Seq<u8>, s: int)
    requires
        0 <= s <= lens.len(),
        s - count_below(lens, 0, s) == 0,
    ensures
        forall|j: int| 0 <= j < s ==> lens[j] == 0,
{
    lemma_zero_gap(lens, 0, s);
}

/// Between one listed symbol and the next (or the end) no symbol has a code.
pub proof fn lemma_sparse_next(lens: Seq<u8>, used: Seq<(u16, u8)>, i: int)
    requires
        sparse_ok(lens, used),
        0 <= i < used.len(),
    ensures
        ({
            let a = used[i].0 as int + 1;
            let b = if i + 1 < used.len() { used[i + 1].0 as int } else { lens.len() as int };
            a <= b <= lens.len() && count_below(lens, 0, b) - count_below(lens, 0, a) == b - a
        }),
{
    let a = used[i].0 as int + 1;
    let b = if i + 1 < used.len() { used[i + 1].0 as int } else { lens.len() as int };
    assert(count_below(lens, 0, a) == count_below(lens, 0, a - 1));
    if i + 1 < used.len() {
        if b < a {
            lemma_count_below_mono(lens, 0, b, a - 1);
            lemma_count_below_le_from(lens, b, a - 1);
        }
    } else {
        lemma_count_below_le(lens, 0, a - 1);
    }
}

/// What a caller keeps while it reads code lengths one by one, to hand
/// them to `build_sparse`: the symbols with a code, each with its length,
/// and the count of each length.
pub open spec fn sparse_inv(lens: Seq<u8>, used: Seq<(u16, u8)>, cnts: [u16; 16]) -> bool {
    &&& lens.len() <= MAX_ALPHA
    &&& sparse_ok(lens, used)
    &&& forall|l: int| 1 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(lens, l as nat)
}

/// Counting among the first `m` symbols only looks at those.
pub proof fn lemma_count_below_prefix(a: Seq<u8>, b: Seq<u8>, l: nat, m: int)
    requires
        0 <= m <= a.len(),
        m <= b.len(),
        forall|j: int| 0 <= j < m ==> a[j] == b[j],
    ensures
        count_below(a, l, m) == count_below(b, l, m),
    decreases m,
{
    if m > 0 {
        lemma_count_below_prefix(a, b, l, m - 1);
    }
}

/// Nothing read yet.
pub proof fn lemma_sparse_empty(cnts: [u16; 16])
    requires
        forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] == 0,
    ensures
        sparse_inv(Seq::<u8>::empty(), Seq::<(u16, u8)>::empty(), cnts),
{
}

/// `k` more symbols without a code change nothing.
pub proof fn lemma_sparse_zeros(lens: Seq<u8>, used: Seq<(u16, u8)>, cnts: [u16; 16], k: nat)
    requires
        sparse_inv(lens, used, cnts),
        lens.len() + k <= MAX_ALPHA,
    ensures
        sparse_inv(lens + Seq::new(k, |i: int| 0u8), used, cnts),
    decreases k,
{
    let b = lens + Seq::new(k, |i: int| 0u8);
    if k == 0 {
        assert(b =~= lens);
    } else {
        let a = lens + Seq::new((k - 1) as nat, |i: int| 0u8);
        lemma_sparse_zeros(lens, used, cnts, (k - 1) as nat);
        assert(b =~= a.push(0u8));
        let n = a.len() as int;
        assert forall|l: nat| #[trigger] count(b, l) == count(a, l) + if l == 0 { 1nat } else { 0nat } by {
            lemma_count_below_prefix(a, b, l, n);
        }
        assert forall|i: int| 0 <= i < used.len() implies count_below(b, 0, (#[trigger] used[i]).0 as int) == count_below(a, 0, used[i].0 as int) by {
            lemma_count_below_prefix(a, b, 0, used[i].0 as int);
        }
    }
}

/// Symbol `n`, the next one, has the code length `c`, which is not 0.
#[inline]
pub fn sparse_push(Ghost(lens): Ghost<Seq<u8>>, n: usize, used: &mut Vec<(u16, u8)>, cnts: &mut [u16; 16], c: u8)
    requires
        sparse_inv(lens, old(used)@, *old(cnts)),
        1 <= c <= 15,
        n == lens.len(),
        lens.len() < MAX_ALPHA,
    ensures
        sparse_inv(lens.push(c), final(used)@, *final(cnts)),
{
    let ghost a = lens;
    let ghost u = used@;
    let ghost b = a.push(c);
    proof {
        assert forall|l: nat| #[trigger] count(b, l) == count(a, l) + if c as nat == l { 1nat } else { 0nat } by {
            lemma_count_below_prefix(a, b, l, n as int);
        }
        assert forall|i: int| 0 <= i < u.len() implies count_below(b, 0, (#[trigger] u[i]).0 as int) == count_below(a, 0, u[i].0 as int) by {
            lemma_count_below_prefix(a, b, 0, u[i].0 as int);
        }
        lemma_count_below_prefix(a, b, 0, n as int);
        lemma_count_below_le(a, c as nat, n as int);
        lemma_count_below_le(a, 0, n as int);
    }
    used.push((n as u16, c));
    let k = c as usize;
    cnts[k] = cnts[k] + 1;
}

/// `build` for a caller that already knows which symbols have a code and
/// how many there are of each length: the work is in proportion to the
/// symbols with a code, not to the alphabet.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn build_sparse(Ghost(lens): Ghost<Seq<u8>>, n: usize, used_syms: &[(u16, u8)], cnts_in: &[u16; 16], max_root: u32) -> (r: Option<HCode>)
    requires
        1 <= max_root <= MAX_ROOT,
        1 <= lens.len() <= MAX_ALPHA,
        n == lens.len(),
        forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= 15,
        sparse_ok(lens, used_syms@),
        forall|l: int| 1 <= l < 16 ==> #[trigger] cnts_in@[l] as nat == count(lens, l as nat),
    ensures
        r is Some == valid_code(lens),
        r matches Some(h) ==> hcode_ok(h, lens) && h.tbits <= max_root,
{
    let ghost ls = lens;
    proof {
        lemma2_to64();
    }
    let m = used_syms.len();
    let ghost us = used_syms@;
    proof {
        lemma_count_below_le(ls, 0, n as int);
    }
    let mut cnts = *cnts_in;
    cnts[0] = (n - m) as u16;
    assert(forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat));
    let nz = n - cnts[0] as usize;
    assert(nz == used(ls));
    if nz == 0 {
        return None;
    }
    if nz == 1 {
        // A single symbol: a one-entry table whose code takes no bits.
        let s = used_syms[0].0 as usize;
        proof {
            lemma_zero_prefix(ls, s as int);
            lemma_first_used_skip(ls, s as int);
        }
        let mut table: Vec<u32> = Vec::new();
        table.push(entry(s as u32, 0));
        proof {
            assert(pow2(0) == 1);
        }
        let h = HCode {
            table,
            tbits: 0,
            count: [0u16; 16],
            first: [0u32; 16],
            offs: [0u16; 16],
            sorted: Vec::new(),
        };
        return Some(h);
    }
    // Kraft: `rem` codes of length `l` remain unassigned.
    let mut rem: i32 = 1;
    let mut l: usize = 1;
    while l <= MAX_LEN
        invariant
            ls == lens,
            1 <= l <= 16,
            rem as int == left(ls, (l - 1) as nat),
            0 <= rem <= pow2((l - 1) as nat),
            pow2(14) == 16384,
            forall|k: nat| 1 <= k < l ==> #[trigger] left(ls, k) >= 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            n == ls.len(),
            n <= MAX_ALPHA,
            nz == used(ls),
            nz >= 2,
        decreases 16 - l,
    {
        proof {
            if l - 1 < 14 {
                lemma_pow2_strictly_increases((l - 1) as nat, 14);
            }
            lemma_pow2_unfold(l as nat);
            assert(cnts@[l as int] as nat == count(ls, l as nat));
        }
        rem = 2 * rem - cnts[l] as i32;
        if rem < 0 {
            proof {
                assert(left(ls, l as nat) < 0);
                assert(1 <= l as nat <= MAX_BITS);
                assert(used(ls) != 1);
                assert(!valid_code(ls));
            }
            return None;
        }
        l = l + 1;
    }
    if rem != 0 {
        return None;
    }
    assert(valid_code(ls));
    let mut sorted: Vec<u16> = vec![0u16; n];
    // Where each length's symbols start in `sorted`.
    let mut offs = [0u16; 16];
    proof {
        lemma_csum_all(ls, n as int);
        assert(csum(ls, 1, n as int) == count(ls, 0)) by {
            assert(csum(ls, 0, n as int) == 0);
        }
    }
    let mut l: usize = 1;
    while l < MAX_LEN
        invariant
            ls == lens,
            1 <= l <= 15,
            n == ls.len(),
            n <= MAX_ALPHA,
            csum(ls, 16, n as int) == n,
            left(ls, 15) == 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 1 <= k <= l ==> #[trigger] offs@[k] as nat + count(ls, 0) == csum(ls, k as nat, n as int),
        decreases 15 - l,
    {
        proof {
            lemma_csum_mono(ls, (l + 1) as nat, 16, n as int);
            assert(cnts@[l as int] as nat == count(ls, l as nat));
            assert(offs@[l as int] as nat + count(ls, 0) == csum(ls, l as nat, n as int));
        }
        offs[l + 1] = offs[l] + cnts[l];
        l = l + 1;
    }
    assert forall|k: int| 1 <= k <= 15 implies #[trigger] offs@[k] as nat + count(ls, k as nat) <= n
        - count(ls, 0) by {
        lemma_csum_mono(ls, (k + 1) as nat, 16, n as int);
        assert(offs@[k] as nat + count(ls, 0) == csum(ls, k as nat, n as int));
    }
    assert forall|a: int, b: int| 1 <= a < b <= 15 implies #[trigger] offs@[a] as nat + count(
        ls,
        a as nat,
    ) <= #[trigger] offs@[b] as nat by {
        lemma_csum_mono(ls, (a + 1) as nat, b as nat, n as int);
        assert(offs@[a] as nat + count(ls, 0) == csum(ls, a as nat, n as int));
        assert(offs@[b] as nat + count(ls, 0) == csum(ls, b as nat, n as int));
    }
    // Counting sort of the symbols by length.
    let mut next = offs;
    let mut i: usize = 0;
    let ghost mut s: int = if m == 0 { n as int } else { us[0].0 as int };
    proof {
        if m > 0 {
            lemma_zero_gap(ls, 0, s);
        } else {
            lemma_zero_gap(ls, 0, n as int);
        }
        assert forall|k: nat| 1 <= k <= 15 implies count_below(ls, k, s) == 0 by {
            lemma_zero_gap_count(ls, k, 0, s);
        }
    }
    while i < m
        invariant
            ls == lens,
            n == ls.len(),
            n <= MAX_ALPHA,
            sorted@.len() == n,
            left(ls, 15) == 0,
            0 <= s <= n,
            i <= m,
            m == us.len(),
            us == used_syms@,
            sparse_ok(ls, us),
            s == (if i < m { us[i as int].0 as int } else { n as int }),
            forall|i: int| 0 <= i < n ==> #[trigger] ls[i] as nat <= 15,
            forall|k: int| 1 <= k <= 15 ==> #[trigger] offs@[k] as nat + count(ls, k as nat) <= n
                - count(ls, 0),
            forall|a: int, b: int|
                1 <= a < b <= 15 ==> #[trigger] offs@[a] as nat + count(ls, a as nat)
                    <= #[trigger] offs@[b] as nat,
            forall|k: int|
                1 <= k <= 15 ==> #[trigger] next@[k] as nat == offs@[k] as nat + count_below(
                    ls,
                    k as nat,
                    s,
                ),
            forall|k: nat, r: nat|
                1 <= k <= 15 && r < count_below(ls, k, s) ==> sorted@[offs@[k as int]
                    as int + r] as int == #[trigger] nth_with_len(ls, k, r, 0),
        decreases m - i,
    {
        proof {
        }
        let su = used_syms[i].0 as usize;
        assert(su == s);
        let l = used_syms[i].1 as usize;
        assert forall|k: nat| 1 <= k <= 15 implies #[trigger] count_below(ls, k, s + 1) <= count(
            ls,
            k,
        ) by {
            lemma_count_below_mono(ls, k, s + 1, n as int);
        }
        {
            proof {
                lemma_nth_rank(ls, l as nat, s, 0);
                assert(count_below(ls, l as nat, s + 1) <= count(ls, l as nat));
                assert(next@[l as int] as nat == offs@[l as int] as nat + count_below(
                    ls,
                    l as nat,
                    s,
                ));
                assert(offs@[l as int] as nat + count(ls, l as nat) <= n - count(ls, 0));
            }
            let ghost old_sorted = sorted@;
            sorted.set(next[l] as usize, su as u16);
            next[l] = next[l] + 1;
            assert forall|k: nat, r: nat|
                1 <= k <= 15 && r < count_below(ls, k, s + 1) implies sorted@[offs@[k as int]
                as int + r] as int == #[trigger] nth_with_len(ls, k, r, 0) by {
                if k == l as nat && r == count_below(ls, k, s) {
                } else {
                    assert(count_below(ls, k, s + 1) <= count(ls, k));
                    assert(offs@[k as int] as nat + count(ls, k) <= n - count(ls, 0));
                    if (k as int) < l as int {
                        assert(offs@[k as int] as nat + count(ls, k) <= offs@[l as int] as nat);
                    } else if (k as int) > l as int {
                        assert(offs@[l as int] as nat + count(ls, l as nat) <= offs@[k as int] as nat);
                    }
                    assert(old_sorted[offs@[k as int] as int + r] as int == nth_with_len(ls, k, r, 0));
                }
            }
        }
        i = i + 1;
        proof {
            let s2: int = if i < m { us[i as int].0 as int } else { n as int };
            lemma_sparse_next(ls, us, (i - 1) as int);
            assert forall|k: nat| 1 <= k <= 15 implies count_below(ls, k, s2) == count_below(ls, k, s + 1) by {
                lemma_zero_gap_count(ls, k, s + 1, s2);
            }
            s = s2;
        }
    }
    proof {
        lemma_csum_all(ls, n as int);
    }
    // The first code of each length.
    let mut first = [0u32; 16];
    let mut l: usize = 2;
    while l <= MAX_LEN
        invariant
            ls == lens,
            2 <= l <= 16,
            pow2(14) == 16384,
            forall|k: nat| 1 <= k <= 15 ==> #[trigger] left(ls, k) >= 0,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 0 <= k < l ==> #[trigger] first@[k] as nat == first_code(ls, k as nat),
            n == ls.len(),
            left(ls, 15) == 0,
            csum(ls, 16, n as int) == n,
        decreases 16 - l,
    {
        proof {
            assert(left(ls, (l - 1) as nat) >= 0);
            lemma_codes_fit(ls, (l - 1) as nat);
            if l - 1 < 14 {
                lemma_pow2_strictly_increases((l - 1) as nat, 14);
            }
            assert(first@[l - 1] as nat == first_code(ls, (l - 1) as nat));
            assert(cnts@[l - 1] as nat == count(ls, (l - 1) as nat));
        }
        first[l] = 2 * (first[l - 1] + cnts[l - 1] as u32);
        l = l + 1;
    }
    let mut code = HCode { table: Vec::new(), tbits: 0, count: cnts, first, offs, sorted };
    assert forall|l: nat| 1 <= l <= 15 implies #[trigger] len_ok(code, ls, l) by {
        assert(cnts@[l as int] as nat == count(ls, l));
        assert(first@[l as int] as nat == first_code(ls, l));
        assert(offs@[l as int] as nat + count(ls, l) <= n - count(ls, 0));
    }
    assert(code_ok(code, ls));
    // The table needs as many bits as the longest code, up to `max_root`.
    // Without longer codes it is complete; otherwise entries no code fills
    // say `LONG`.
    let mut longest: usize = MAX_LEN;
    while longest > 0 && cnts[longest] == 0
        invariant
            ls == lens,
            longest <= 15,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: nat| longest < k <= 15 ==> #[trigger] count(ls, k) == 0,
            n == ls.len(),
            left(ls, 15) == 0,
            csum(ls, 16, n as int) == n,
        decreases longest,
    {
        proof {
        }
        assert(cnts@[longest as int] as nat == count(ls, longest as nat));
        longest = longest - 1;
    }
    if longest == 0 {
        // Every length is unused, but `used(ls) >= 2`.
        proof {
            assert forall|k: nat| 0 < k <= 15 implies #[trigger] count(ls, k) == 0 by {}
            lemma_left_tail(ls, 0, 15);
            lemma_pow2_pos(15);
            assert(left(ls, 0) == 1);
        }
        assert(false);
        return None;
    }
    let tbits: u32 = if longest as u32 > max_root {
        max_root
    } else {
        longest as u32
    };
    proof {
        lemma_usize_shl_is_mul(1, tbits as usize);
        lemma_pow2_strictly_increases(tbits as nat, 16);
        lemma_pow2_strictly_increases(tbits as nat, 11);
    }
    let size = 1usize << (tbits as usize);
    let init = longest > tbits as usize;
    let mut table: Vec<u32> = vec![LONG; size];
    assert(forall|j: int| 0 <= j < size ==> #[trigger] table@[j] == LONG);
    proof {
    }
    // Longest first, so shorter matches win.
    proof {
        lemma_csum_mono(ls, 1, (tbits + 1) as nat, n as int);
        lemma_csum_mono(ls, (tbits + 1) as nat, 16, n as int);
    }
    let mut l = tbits as usize;
    while l >= 1
        invariant
            ls == lens,
            n == ls.len(),
            csum(ls, (l + 1) as nat, n as int) <= csum(ls, (tbits + 1) as nat, n as int),
            csum(ls, (tbits + 1) as nat, n as int) <= n,
            l <= tbits <= MAX_ROOT,
            1 <= tbits,
            code.sorted@.len() == n,
            n <= MAX_ALPHA,
            size == pow2(tbits as nat),
            size <= 1024,
            table@.len() == size,
            code_ok(code, ls),
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat),
            forall|k: int| 0 <= k < 16 ==> #[trigger] first@[k] as nat == first_code(ls, k as nat),
            forall|k: int| 0 <= k < 16 ==> #[trigger] offs@[k] == code.offs@[k],
            forall|k: nat| 1 <= k <= 15 ==> #[trigger] left(ls, k) >= 0,
            forall|i: int|
                0 <= i < size ==> #[trigger] fill_ok(
                    table@[i],
                    ls,
                    i as nat,
                    tbits as nat,
                    (l + 1) as nat,
                    init,
                ),
        decreases l,
    {
        let base = offs[l] as usize;
        let cnt = cnts[l] as usize;
        proof {
            lemma_pow2_pos(l as nat);
            if l < 15 {
                lemma_pow2_strictly_increases(l as nat, 15);
            }
            lemma2_to64();
            lemma_usize_shl_is_mul(1, l);
            assert(len_ok(code, ls, l as nat));
            assert(left(ls, l as nat) >= 0);
            lemma_codes_fit(ls, l as nat);
        }
        let step = 1usize << l;
        let ghost tl = table@;
        let ghost q = pow2((tbits - l) as nat);
        proof {
            lemma_pow2_adds(l as nat, (tbits - l) as nat);
            lemma_pow2_pos((tbits - l) as nat);
            assert(size == step * q);
        }
        let mut r: usize = 0;
        while r < cnt
            invariant
                ls == lens,
                size == step * q,
                q >= 1,
                1 <= l <= tbits <= 15,
                r <= cnt,
                cnt == count(ls, l as nat),
                base == code.offs@[l as int],
                len_ok(code, ls, l as nat),
                code.sorted@.len() == n,
                n <= MAX_ALPHA,
                first@[l as int] as nat == first_code(ls, l as nat),
                first_code(ls, l as nat) + count(ls, l as nat) <= pow2(l as nat),
                step == pow2(l as nat),
                step <= 32768,
                size == pow2(tbits as nat),
                size <= 1024,
                table@.len() == size,
                forall|i: int|
                    0 <= i < size ==> #[trigger] mid_ok(
                        table@[i],
                        tl[i],
                        ls,
                        i as nat,
                        l as nat,
                        r as nat,
                    ),
            decreases cnt - r,
        {
            let sym = code.sorted[base + r] as u32;
            assert(sym as int == nth_with_len(ls, l as nat, r as nat, 0));
            let c = first[l] + r as u32;
            let e = entry(sym, l as u32);
            assert(c < pow2(l as nat));
            let rv = reverse_fast(c, l as u32);
            let rc = rv as usize;
            proof {
                lemma_rev_bound(c as nat, l as nat);
                lemma_small_mod(rc as nat, step as nat);
            }
            let mut i = rc;
            let ghost tr = table@;
            let ghost mut k: nat = 0;
            assert forall|j: int| 0 <= j < size implies #[trigger] table@[j] == (if j % (
            step as int) == rc && j < i {
                e
            } else {
                tr[j]
            }) by {
                if j < rc {
                    lemma_small_mod(j as nat, step as nat);
                }
            }
            while i < size
                invariant
                    ls == lens,
                    rc < step,
                    step == pow2(l as nat),
                    step <= 32768,
                    size <= 1024,
                    i % step == rc,
                    i <= size + step,
                    size == step * q,
                    i == rc + k * step,
                    k <= q,
                    table@.len() == size,
                    forall|j: int|
                        0 <= j < size ==> #[trigger] table@[j] == (if j % (step as int) == rc && j
                            < i {
                            e
                        } else {
                            tr[j]
                        }),
                decreases size + step - i,
            {
                set32(&mut table, i, e);
                proof {
                    assert(k < q) by (nonlinear_arith)
                        requires
                            rc + k * step < step * q,
                            step > 0,
                    ;
                    assert(rc + k * step + step == rc + (k + 1) * step) by (nonlinear_arith);
                    k = k + 1;
                    lemma_mod_add_multiples_vanish(i as int, step as int);
                    assert forall|j: int| 0 <= j < size implies #[trigger] table@[j] == (if j % (
                    step as int) == rc && j < i + step {
                        e
                    } else {
                        tr[j]
                    }) by {
                        if j % (step as int) == rc && i <= j < i + step {
                            lemma_same_residue(i as int, j, step as int);
                        }
                    }
                }
                i = i + step;
            }
            let ghost r0 = r;
            r = r + 1;
            proof {
                assert forall|j: int| 0 <= j < size implies #[trigger] mid_ok(
                    table@[j],
                    tl[j],
                    ls,
                    j as nat,
                    l as nat,
                    r as nat,
                ) by {
                    lemma_rev_iff(j as nat, c as nat, l as nat);
                    assert(mid_ok(tr[j], tl[j], ls, j as nat, l as nat, r0 as nat));
                    assert(r as nat == r0 as nat + 1);
                }
            }
        }
        proof {
            assert forall|j: int| 0 <= j < size implies #[trigger] fill_ok(
                table@[j],
                ls,
                j as nat,
                tbits as nat,
                l as nat,
                init,
            ) by {
                assert(mid_ok(table@[j], tl[j], ls, j as nat, l as nat, r as nat));
                assert(fill_ok(tl[j], ls, j as nat, tbits as nat, (l + 1) as nat, init));
            }
            assert(fill_cost(ls, tbits as nat, (l - 1) as nat) == fill_cost(ls, tbits as nat, l as nat)
                + count(ls, l as nat) * q);
            assert(csum(ls, (l + 1) as nat, n as int) == csum(ls, l as nat, n as int) + cnt);
        }
        l = l - 1;
    }
    proof {
        if !init {
            assert forall|k: nat| tbits < k <= 15 implies #[trigger] count(ls, k) == 0 by {}
            lemma_left_tail(ls, tbits as nat, 15);
            lemma_pow2_pos((15 - tbits) as nat);
            let p = pow2((15 - tbits) as nat) as int;
            assert(left(ls, tbits as nat) == 0) by (nonlinear_arith)
                requires
                    p > 0,
                    0 == p * left(ls, tbits as nat),
            ;
        }
        assert forall|i: int| 0 <= i < pow2(tbits as nat) implies #[trigger] table@[i] == tab_entry(
            ls,
            i as nat,
            tbits as nat,
        ) by {
            assert(fill_ok(table@[i], ls, i as nat, tbits as nat, (l + 1) as nat, init));
            assert((l + 1) as nat == 1);
            if !init {
                lemma_complete_decodes(ls, i as nat, tbits as nat);
            }
        }
        assert(left(ls, tbits as nat) >= 0);
        lemma_fill_bound(ls, tbits as nat);
    }
    code.table = table;
    code.tbits = tbits;
    assert(code_ok(code, ls));
    Some(code)
}
// --- sparse build: end








/// Most loop iterations `build` runs for `n` code lengths and at most
/// `2^root` table entries.
pub open spec fn build_cost(n: nat, root: nat) -> nat {
    18 * n + 3 * pow2(root) + 73
}

// ---------------------------------------------------------------------------
// Decoding
// ---------------------------------------------------------------------------

/// Decodes a symbol bit by bit from the low `cnt` bits of `buf`: at each
/// length `l`, the first `l` bits read as a code (first bit most
/// significant) match a symbol iff they fall in that length's range. The
/// fallback for `LONG` entries. Returns the symbol's entry, or `None` if no
/// code matches within `cnt` bits.
#[inline(never)]
pub fn decode_slow(code: &HCode, buf: u64, cnt: u32, Ghost(lens): Ghost<Seq<u8>>) -> (r:
    (Option<u32>, Ghost<nat>))
    requires
        code_ok(*code, lens),
        lens.len() <= MAX_ALPHA,
    ensures
        r.0 == slow_result(lens, buf as nat, cnt as nat),
        r.1@ <= 15,
{
    let mut v: u32 = 0;
    let mut l: u32 = 1;
    proof {
        lemma2_to64();
    }
    while l <= MAX_LEN as u32
        invariant
            1 <= l <= 16,
            l - 1 <= cnt,
            code_ok(*code, lens),
            lens.len() <= MAX_ALPHA,
            pow2(15) == 32768,
            v as nat == rev(buf as nat, (l - 1) as nat),
            v < pow2((l - 1) as nat),
            decode_num(lens, buf as nat, cnt as nat, 1) == decode_num(
                lens,
                buf as nat,
                cnt as nat,
                l as nat,
            ),
        decreases 16 - l,
    {
        if l > cnt {
            return (None, Ghost(l as nat));
        }
        proof {
            lemma_rev_unfold(buf as nat, l as nat);
            lemma_u64_shr_is_div(buf, (l - 1) as u64);
            let sh = buf >> ((l - 1) as u64);
            assert((sh & 1u64) == sh % 2) by (bit_vector);
            lemma_pow2_unfold(l as nat);
            if l < 15 {
                lemma_pow2_strictly_increases(l as nat, 15);
            }
            assert(len_ok(*code, lens, l as nat));
        }
        v = 2 * v + ((buf >> ((l - 1) as u64)) & 1) as u32;
        let f = code.first[l as usize];
        let c = code.count[l as usize] as u32;
        if v >= f && v - f < c {
            let s = code.sorted[code.offs[l as usize] as usize + (v - f) as usize];
            assert(s as int == nth_with_len(lens, l as nat, (v - f) as nat, 0));
            proof {
                assert(count_below(lens, l as nat, 0) == 0);
                lemma_nth_bound(lens, l as nat, (v - f) as nat, 0);
            }
            return (Some(entry(s as u32, l)), Ghost(l as nat));
        }
        l = l + 1;
    }
    (None, Ghost(15))
}

/// Where the `r`-th symbol of length `l` is.
pub proof fn lemma_nth_bound(lens: Seq<u8>, l: nat, r: nat, from: int)
    requires
        0 <= from <= lens.len(),
        r + count_below(lens, l, from) < count_below(lens, l, lens.len() as int),
    ensures
        from <= nth_with_len(lens, l, r, from) < lens.len(),
    decreases lens.len() - from,
{
    lemma_count_below_mono(lens, l, from, lens.len() as int);
    if from < lens.len() {
        assert(count_below(lens, l, from + 1) == count_below(lens, l, from) + if lens[from] as nat
            == l {
            1nat
        } else {
            0nat
        });
        if lens[from] as nat == l && r == 0 {
        } else if lens[from] as nat == l {
            lemma_nth_bound(lens, l, (r - 1) as nat, from + 1);
        } else {
            lemma_nth_bound(lens, l, r, from + 1);
        }
    }
}

} // verus!
