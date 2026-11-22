//! Canonical Huffman decoding tables.
//!
//! A table is indexed by the next `tbits` input bits (first bit least
//! significant). Entry `i` holds the symbol whose code is the shortest
//! prefix of `i`'s bits, if that code is at most `tbits` long, already
//! translated into what the decoder needs (literal byte, or base value and
//! extra bit count). Codes longer than `tbits` are rare; their entries say
//! `LONG` and the decoder falls back to `decode_slow`, which walks the
//! canonical code one length at a time exactly as `spec::decode` does.
//!
//! Tables are filled from the longest code to the shortest, so a shorter
//! match overwrites a longer one and every entry ends up holding the
//! shortest match. That is the spec's definition, so the proof never needs
//! the (true, but harder) fact that valid codes are prefix-free.
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use crate::spec::{count, count_below, first_code, left, nth_with_len, valid_lens};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
pub use verilith_core::huffman::reverse;
use verilith_core::prims::set32;
use vstd::prelude::*;

verus! {

pub const MAX_LEN: usize = 15;

/// Table bits: literal/length, distance and code length tables.
pub const LIT_BITS: u32 = 11;

pub const DIST_BITS: u32 = 8;

pub const CL_BITS: u32 = 7;

pub const LIT_SIZE: usize = 1 << 11;

pub const DIST_SIZE: usize = 1 << 8;

pub const CL_SIZE: usize = 1 << 7;

/// Entry layout: bits 0..8 hold the bits the symbol takes in total (its
/// code plus extra bits), bits 8..13 the code length, bits 16..31 the value
/// (literal byte, code length symbol, or base length or distance). The flags
/// mark literals and the exceptional entries the fast loop leaves the main
/// path for.
pub const F_LIT: u32 = 1 << 31;

/// End-of-block, a bad symbol, or `LONG`.
pub const F_EXC: u32 = 1 << 15;

pub const F_EOB: u32 = 1 << 14;

/// No code of at most `tbits` bits matches: decode with `decode_slow`.
pub const F_LONG: u32 = 1 << 13;

/// A symbol with a code that never occurs in valid data (literal/length
/// 286, 287 and distance 30, 31 of the fixed code) has `F_EXC` alone.
pub const LONG: u32 = F_EXC | F_LONG;

/// Which alphabet a table decodes.
pub const ALPHA_LIT: u8 = 0;

pub const ALPHA_DIST: u8 = 1;

pub const ALPHA_CL: u8 = 2;

pub const LEN_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];

pub const LEN_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];

pub const DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];

pub const DIST_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];

/// Everything `decode_slow` needs about a canonical code, by code length:
/// how many symbols have it, the first code, and where its symbols start in
/// `sorted` (all symbols with a code, ordered by length, then value).
#[derive(Clone)]
pub struct Code {
    pub count: [u16; 16],
    pub first: [u32; 16],
    pub offs: [u16; 16],
    pub sorted: [u16; 288],
}

impl Code {
    pub fn new() -> Code {
        Code { count: [0; 16], first: [0; 16], offs: [0; 16], sorted: [0; 288] }
    }
}

// ---------------------------------------------------------------------------
// Specification of the tables
// ---------------------------------------------------------------------------

pub open spec fn spec_mk(flags: u32, len: u32, extra: u32, value: u32) -> u32 {
    flags | (value << 16u32) | (len << 8u32) | ((len + extra) as u32)
}

/// The table entry of symbol `s` of alphabet `alpha` with an `l`-bit code.
pub open spec fn ent(alpha: u8, s: nat, l: nat) -> u32 {
    let l = l as u32;
    if alpha == ALPHA_LIT {
        if s < 256 {
            spec_mk(F_LIT, l, 0, s as u32)
        } else if s == 256 {
            spec_mk(F_EXC | F_EOB, l, 0, 0)
        } else if s <= 285 {
            let i = s - 257;
            spec_mk(0, l, LEN_EXTRA@[i] as u32, LEN_BASE@[i] as u32)
        } else {
            spec_mk(F_EXC, l, 0, 0)
        }
    } else if alpha == ALPHA_DIST {
        if s < 30 {
            spec_mk(0, l, DIST_EXTRA@[s as int] as u32, DIST_BASE@[s as int] as u32)
        } else {
            spec_mk(F_EXC, l, 0, 0)
        }
    } else {
        spec_mk(0, l, 0, s as u32)
    }
}

/// What `decode_slow` returns for the number `x` of which `avail` bits
/// are known.
pub open spec fn slow_result(lens: Seq<u8>, alpha: u8, x: nat, avail: nat) -> Option<u32> {
    match decode_num(lens, x, avail, 1) {
        Some((s, k)) => Some(ent(alpha, s, k)),
        None => None,
    }
}

/// `code` describes the canonical code of `lens` at length `l`.
pub open spec fn len_ok(code: Code, lens: Seq<u8>, l: nat) -> bool {
    let li = l as int;
    &&& code.count@[li] as nat == count(lens, l)
    &&& code.first@[li] as nat == first_code(lens, l)
    &&& code.offs@[li] as nat + count(lens, l) <= 288
    &&& forall|r: nat|
        r < count(lens, l) ==> code.sorted@[code.offs@[li] as int + r] as int
            == #[trigger] nth_with_len(lens, l, r, 0)
}

pub open spec fn code_ok(code: Code, lens: Seq<u8>) -> bool {
    forall|l: nat| 1 <= l <= 15 ==> #[trigger] len_ok(code, lens, l)
}

/// Entry `x` of a `t`-bit table: the shortest code that is a prefix of
/// `x`'s bits, or `LONG` if there is none of at most `t` bits.
pub open spec fn tab_entry(lens: Seq<u8>, alpha: u8, x: nat, t: nat) -> u32 {
    match decode_num(lens, x, t, 1) {
        Some((s, k)) => ent(alpha, s, k),
        None => LONG,
    }
}

pub open spec fn table_ok(table: Seq<u32>, lens: Seq<u8>, t: nat, alpha: u8) -> bool {
    &&& pow2(t) <= table.len()
    &&& forall|i: int| 0 <= i < pow2(t) ==> #[trigger] table[i] == tab_entry(lens, alpha, i as nat, t)
}

/// Entry `x` of a table one bit wider than `m`: a code of exactly `m + 1`
/// bits if one matches, otherwise entry `x mod 2^m` of the `m`-bit table.
pub proof fn lemma_tab_entry_grow(lens: Seq<u8>, alpha: u8, x: nat, m: nat)
    requires
        m + 1 <= crate::spec::MAX_BITS,
    ensures
        tab_entry(lens, alpha, x, m + 1) == if matches_at(lens, x, m + 1) {
            ent(alpha, nth_with_len(lens, m + 1, (rev(x, m + 1) - first_code(lens, m + 1)) as nat, 0) as nat, m + 1)
        } else {
            tab_entry(lens, alpha, x % pow2(m), m)
        },
{
    if matches_at(lens, x, m + 1) {
        assert forall|j: nat| 1 <= j < m + 1 implies !#[trigger] matches_at(lens, x, j) by {
            lemma_prefix_free(lens, x, j, m + 1);
        }
        lemma_decode_num_first(lens, x, m + 1, 1, m + 1);
    } else {
        lemma_decode_num_grow(lens, x, m, 1);
        lemma_decode_num_mod(lens, x, m, 1);
    }
}

// ---------------------------------------------------------------------------
// Entries
// ---------------------------------------------------------------------------

#[inline(always)]
pub fn mk(flags: u32, len: u32, extra: u32, value: u32) -> (r: u32)
    requires
        len + extra <= 0xff,
    ensures
        r == spec_mk(flags, len, extra, value),
{
    flags | (value << 16) | (len << 8) | (len + extra)
}

/// Bits a table entry takes in total.
#[inline(always)]
pub fn total_bits(e: u32) -> (r: u32)
    ensures
        r == e & 0xff,
{
    e & 0xff
}

/// The code length of a table entry.
#[inline(always)]
pub fn code_len(e: u32) -> (r: u32)
    ensures
        r == (e >> 8u32) & 0x1f,
{
    (e >> 8) & 0x1f
}

/// The table entry of symbol `s` with a code `l` bits long.
#[inline(always)]
pub fn entry(alpha: u8, s: u32, l: u32) -> (r: u32)
    requires
        l <= 15,
    ensures
        r == ent(alpha, s as nat, l as nat),
{
    if alpha == ALPHA_LIT {
        if s < 256 {
            mk(F_LIT, l, 0, s)
        } else if s == 256 {
            mk(F_EXC | F_EOB, l, 0, 0)
        } else if s <= 285 {
            let i = (s - 257) as usize;
            mk(0, l, LEN_EXTRA[i] as u32, LEN_BASE[i] as u32)
        } else {
            mk(F_EXC, l, 0, 0)
        }
    } else if alpha == ALPHA_DIST {
        if s < 30 {
            let i = s as usize;
            mk(0, l, DIST_EXTRA[i] as u32, DIST_BASE[i] as u32)
        } else {
            mk(F_EXC, l, 0, 0)
        }
    } else {
        mk(0, l, 0, s)
    }
}

// ---------------------------------------------------------------------------
// Building
// ---------------------------------------------------------------------------

/// Builds `code` and `table` (`1 << tbits` entries) from code lengths.
/// Returns false, leaving them unspecified, if the lengths are not
/// `spec::valid_lens(lens, single_ok)`. Also returns the number of loop
/// iterations it ran, at most `build_cost(lens.len(), tbits)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub fn build(
    code: &mut Code,
    table: &mut [u32],
    tbits: u32,
    lens: &[u8],
    alpha: u8,
    single_ok: bool,
) -> (r: (bool, Ghost<nat>))
    requires
        1 <= tbits <= 15,
        pow2(tbits as nat) <= old(table)@.len(),
        lens@.len() <= 288,
    ensures
        r.0 == valid_lens(lens@, single_ok),
        final(table)@.len() == old(table)@.len(),
        r.0 ==> code_ok(*final(code), lens@),
        r.0 ==> table_ok(final(table)@, lens@, tbits as nat, alpha),
        r.1@ <= build_cost(lens@.len(), tbits as nat),
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
            ls == lens@,
            n <= 288,
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
                assert(!(ls[s as int] as nat <= crate::spec::MAX_BITS));
            }
            return (false, Ghost(w));
        }
        proof {
            lemma_count_below_le(ls, l as nat, s as int);
        }
        cnts[l] = cnts[l] + 1;
        s = s + 1;
    }
    assert(forall|l: int| 0 <= l < 16 ==> #[trigger] cnts@[l] as nat == count(ls, l as nat));
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
            }
            return (false, Ghost(w));
        }
        l = l + 1;
    }
    proof {
        lemma_count_below_le(ls, 0, n as int);
    }
    if rem > 0 {
        let used = n - cnts[0] as usize;
        proof {
            lemma_used(ls);
        }
        if !(used == 0 || (single_ok && used == 1 && cnts[1] == 1)) {
            return (false, Ghost(w));
        }
    }
    assert(valid_lens(ls, single_ok));
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
            n <= 288,
            csum(ls, 16, n as int) == n,
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
            ls == lens@,
            n <= 288,
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
                1 <= k <= 15 && r < count_below(ls, k, s as int) ==> code.sorted@[offs@[k as int]
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
            let ghost old_sorted = code.sorted@;
            code.sorted[next[l] as usize] = s as u16;
            next[l] = next[l] + 1;
            assert forall|k: nat, r: nat|
                1 <= k <= 15 && r < count_below(ls, k, s + 1) implies code.sorted@[offs@[k as int]
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
    code.count = cnts;
    code.first = first;
    code.offs = offs;
    assert forall|l: nat| 1 <= l <= 15 implies #[trigger] len_ok(*code, ls, l) by {
        assert(cnts@[l as int] as nat == count(ls, l));
        assert(first@[l as int] as nat == first_code(ls, l));
        assert(offs@[l as int] as nat + count(ls, l) <= n - count(ls, 0));
    }
    assert(code_ok(*code, ls));
    // Fill the table one code length at a time. When its first `2^m`
    // entries are right for an `m`-bit table, copying them up makes the first
    // `2^(m + 1)` right for `m + 1` bits, except where a code of exactly
    // `m + 1` bits matches; those entries are then written one per code.
    let ghost w6 = w;
    set32(table, 0, LONG);
    proof {
        lemma2_to64();
        assert(decode_num(ls, 0, 0, 1) is None);
        lemma_csum_mono(ls, 1, 16, n as int);
    }
    let mut m: usize = 0;
    while m < tbits as usize
        invariant
            ls == lens@,
            n == ls.len(),
            n <= 288,
            m <= tbits <= 15,
            pow2(tbits as nat) <= table@.len(),
            table@.len() == old(table)@.len(),
            code_ok(*code, ls),
            forall|k: nat| 1 <= k <= 15 ==> #[trigger] left(ls, k) >= 0,
            csum(ls, 16, n as int) == n,
            csum(ls, 1, n as int) <= csum(ls, (m + 1) as nat, n as int),
            forall|i: int| 0 <= i < pow2(m as nat) ==> #[trigger] table@[i] == tab_entry(ls, alpha, i as nat, m as nat),
            w <= w6 + m + pow2(m as nat) + 16 * (csum(ls, (m + 1) as nat, n as int) - csum(ls, 1, n as int)),
            w6 == 2 * n + 43,
        decreases tbits - m,
    {
        let l = m + 1;
        proof {
            lemma_pow2_unfold(l as nat);
            lemma_pow2_pos(m as nat);
            if l < tbits {
                lemma_pow2_strictly_increases(l as nat, tbits as nat);
            }
            lemma_pow2_strictly_increases(m as nat, 16);
            lemma_pow2_strictly_increases(l as nat, 16);
            lemma2_to64();
            lemma_usize_shl_is_mul(1, m as usize);
            assert(len_ok(*code, ls, l as nat));
            lemma_codes_fit(ls, l as nat);
            w = w + 1 + pow2(m as nat);
        }
        let half = 1usize << m;
        let ghost t0 = table@;
        table.copy_within(0..half, half);
        let ghost t1 = table@;
        assert forall|i: int| 0 <= i < 2 * half implies #[trigger] table@[i] == tab_entry(ls, alpha, (i % (half as int)) as nat, m as nat) by {
            if i < half {
                lemma_small_mod(i as nat, half as nat);
            } else {
                lemma_mod_sub_multiples_vanish(i, half as int);
                lemma_small_mod((i - half) as nat, half as nat);
            }
        }
        let base = code.offs[l] as usize;
        let cnt = code.count[l] as usize;
        let f = code.first[l];
        let ghost fl = first_code(ls, l as nat);
        let ghost wl = w;
        let mut r: usize = 0;
        while r < cnt
            invariant
                ls == lens@,
                1 <= l <= tbits <= 15,
                l == m + 1,
                half == pow2(m as nat),
                2 * half == pow2(l as nat),
                pow2(l as nat) <= 65536,
                2 * half <= table@.len(),
                table@.len() == old(table)@.len(),
                code_ok(*code, ls),
                len_ok(*code, ls, l as nat),
                base == code.offs@[l as int],
                cnt == count(ls, l as nat),
                f as nat == fl,
                fl == first_code(ls, l as nat),
                fl + count(ls, l as nat) <= pow2(l as nat),
                r <= cnt,
                w <= wl + 16 * r,
                forall|i: int| 0 <= i < 2 * half ==> #[trigger] table@[i] == (if matches_at(ls, i as nat, l as nat)
                    && rev(i as nat, l as nat) < fl + r {
                    ent(alpha, nth_with_len(ls, l as nat, (rev(i as nat, l as nat) - fl) as nat, 0) as nat, l as nat)
                } else {
                    tab_entry(ls, alpha, (i % (half as int)) as nat, m as nat)
                }),
            decreases cnt - r,
        {
            let sym = code.sorted[base + r] as u32;
            assert(sym as int == nth_with_len(ls, l as nat, r as nat, 0));
            let c = f + r as u32;
            let e = entry(alpha, sym, l as u32);
            let (rv, Ghost(rw)) = reverse(c, l as u32);
            proof {
                w = w + 1 + rw;
                lemma_rev_bound(c as nat, l as nat);
            }
            let ghost tr = table@;
            set32(table, rv as usize, e);
            proof {
                assert forall|i: int| 0 <= i < 2 * half implies #[trigger] table@[i] == (if matches_at(ls, i as nat, l as nat)
                    && rev(i as nat, l as nat) < fl + r + 1 {
                    ent(alpha, nth_with_len(ls, l as nat, (rev(i as nat, l as nat) - fl) as nat, 0) as nat, l as nat)
                } else {
                    tab_entry(ls, alpha, (i % (half as int)) as nat, m as nat)
                }) by {
                    lemma_rev_iff(i as nat, c as nat, l as nat);
                    lemma_small_mod(i as nat, pow2(l as nat));
                    assert(tr[i] == (if matches_at(ls, i as nat, l as nat) && rev(i as nat, l as nat) < fl + r {
                        ent(alpha, nth_with_len(ls, l as nat, (rev(i as nat, l as nat) - fl) as nat, 0) as nat, l as nat)
                    } else {
                        tab_entry(ls, alpha, (i % (half as int)) as nat, m as nat)
                    }));
                }
            }
            r = r + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < pow2(l as nat) implies #[trigger] table@[i] == tab_entry(ls, alpha, i as nat, l as nat) by {
                lemma_tab_entry_grow(ls, alpha, i as nat, m as nat);
                assert(table@[i] == (if matches_at(ls, i as nat, l as nat) && rev(i as nat, l as nat) < fl + r {
                    ent(alpha, nth_with_len(ls, l as nat, (rev(i as nat, l as nat) - fl) as nat, 0) as nat, l as nat)
                } else {
                    tab_entry(ls, alpha, (i % (half as int)) as nat, m as nat)
                }));
            }
            assert(csum(ls, (l + 1) as nat, n as int) == csum(ls, l as nat, n as int) + cnt);
            lemma_csum_mono(ls, (l + 1) as nat, 16, n as int);
        }
        m = l;
    }
    proof {
        assert(csum(ls, (m + 1) as nat, n as int) <= n) by {
            lemma_csum_mono(ls, (m + 1) as nat, 16, n as int);
        }
    }
    (true, Ghost(w))
}

/// Most loop iterations `build` runs for `n` code lengths and a table of
/// `2^tbits` entries.
pub open spec fn build_cost(n: nat, tbits: nat) -> nat {
    18 * n + 2 * pow2(tbits) + 73
}

// ---------------------------------------------------------------------------
// Decoding long codes
// ---------------------------------------------------------------------------

/// Decodes a symbol bit by bit from the low `cnt` bits of `buf`: at each
/// length `l`, the first `l` bits read as a code (first bit most
/// significant) match a symbol iff they fall in that length's range. The
/// fallback for `LONG` entries. Returns the symbol's table entry, or `None`
/// if no code matches within `cnt` bits.
#[inline(never)]
pub fn decode_slow(code: &Code, alpha: u8, buf: u64, cnt: u32, Ghost(lens): Ghost<Seq<u8>>) -> (r:
    (Option<u32>, Ghost<nat>))
    requires
        code_ok(*code, lens),
    ensures
        r.0 == slow_result(lens, alpha, buf as nat, cnt as nat),
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
            return (Some(entry(alpha, s as u32, l)), Ghost(l as nat));
        }
        l = l + 1;
    }
    (None, Ghost(15))
}

// Lemmas used by the faster table decoder; the rest of the canonical-code
// proofs are in `verilith_core::huffman`.

/// Canonical codes are prefix-free: when a code of length `m` matches `x`,
/// the first `l < m` bits of `x` read as a number past every code of
/// length `l`.
pub proof fn lemma_prefix_free(lens: Seq<u8>, x: nat, l: nat, m: nat)
    requires
        1 <= l < m,
        matches_at(lens, x, m),
    ensures
        rev(x, l) >= first_code(lens, l) + count(lens, l),
    decreases m - l,
{
    let j = l + 1;
    if j < m {
        lemma_prefix_free(lens, x, j, m);
    }
    lemma_rev_unfold(x, j);
    assert(rev(x, j) >= first_code(lens, j));
    assert(first_code(lens, j) == 2 * (first_code(lens, l) + count(lens, l)));
}

/// Without a code of exactly `m + 1` bits matching, one more available bit
/// does not change what `decode_num` finds.
pub proof fn lemma_decode_num_grow(lens: Seq<u8>, x: nat, m: nat, j: nat)
    requires
        1 <= j <= m + 1,
        m + 1 <= MAX_BITS,
        !matches_at(lens, x, m + 1),
    ensures
        decode_num(lens, x, m + 1, j) == decode_num(lens, x, m, j),
    decreases m + 1 - j,
{
    if j <= m {
        lemma_decode_num_grow(lens, x, m, j + 1);
    } else {
        assert(decode_num(lens, x, m + 1, j + 1) is None);
    }
}

/// `decode_num` with `t` bits available only reads the low `t` bits.
pub proof fn lemma_decode_num_mod(lens: Seq<u8>, x: nat, t: nat, j: nat)
    requires
        1 <= j,
    ensures
        decode_num(lens, x % pow2(t), t, j) == decode_num(lens, x, t, j),
    decreases MAX_BITS + 1 - j,
{
    lemma_pow2_pos(t);
    if j <= MAX_BITS && j <= t {
        lemma_rev_mod(x, j, t);
        lemma_decode_num_mod(lens, x, t, j + 1);
        assert(rev(x % pow2(t), j) == rev(x, j));
    }
}

} // verus!
