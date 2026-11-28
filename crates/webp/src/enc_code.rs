//! Prefix codes for the encoder: code lengths checked the way the
//! specification reads them, their canonical codes, and what it reads when
//! a symbol's code is written (verilith-brotli's `pcode`, reading with
//! WebP's `read_symbol`).
use crate::enc_bw::*;
#[cfg(verus_only)]
use crate::enc_lem::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;

verus! {

/// Code lengths the spec's decoding accepts for the symbols that have one:
/// at most 15 bits, and the code space not over-subscribed.
pub open spec fn lens_ok(lens: Seq<u8>) -> bool {
    &&& forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] as nat <= MAX_BITS
    &&& forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0
}

/// Symbol `s`'s code as written: its canonical code, first bit first, or
/// nothing when it is the only symbol with a code (§3.4).
pub open spec fn code_of(lens: Seq<u8>, s: int) -> Seq<nat> {
    if used(lens) == 1 {
        Seq::empty()
    } else {
        bits_of(rev(canon(lens, s), lens[s] as nat), lens[s] as nat)
    }
}

/// `rsym` reads a written code back.
pub proof fn lemma_sym(b: Seq<u8>, w: Seq<nat>, lens: Seq<u8>, s: int, rest: Seq<nat>)
    requires
        ext(b, w + (code_of(lens, s) + rest)),
        lens_ok(lens),
        0 <= s < lens.len(),
        1 <= lens[s],
        used(lens) == 1 ==> first_used(lens, 0) == s,
    ensures
        read_symbol(lens, b, w.len() as int) == Some((s as nat, (w.len() + code_of(lens, s).len()) as int)),
        code_of(lens, s).len() == if used(lens) == 1 { 0 } else { lens[s] as int },
{
    if used(lens) != 1 {
        let m = lens[s] as nat;
        let c = code_of(lens, s);
        lemma_bits_of(rev(canon(lens, s), m), m);
        lemma_ext2(b, w, c, rest);
        lemma_rev_bound(canon(lens, s), m);
        lemma_ext_bits(b, w + c, w.len() as int, m);
        lemma_bits_of(rev(canon(lens, s), m), m);
        lemma_wbits_suffix(w, c, 0, m);
        assert(w.len() + 0 == w.len());
        vstd::arithmetic::div_mod::lemma_small_mod(rev(canon(lens, s), m), pow2(m));
        lemma_encode(lens, s, b, w.len() as int);
    }
}

/// A prefix code: its lengths, the bit-reversed canonical code of each
/// symbol, the number of symbols with a code and, when that is one, the
/// symbol.
pub struct HCode {
    pub lens: Vec<u8>,
    pub codes: Vec<u16>,
    pub nused: usize,
    pub one: usize,
}

impl HCode {
    pub open spec fn ok(&self) -> bool {
        &&& lens_ok(self.lens@)
        &&& self.codes@.len() == self.lens@.len()
        &&& self.nused == used(self.lens@)
        &&& self.nused >= 1
        &&& self.one < self.lens@.len()
        &&& (self.nused == 1 ==> self.lens@[self.one as int] >= 1 && first_used(self.lens@, 0) == self.one)
        &&& forall|s: int| 0 <= s < self.lens@.len() && 1 <= self.lens@[s] ==> #[trigger] self.codes@[s] as nat == rev(canon(self.lens@, s), self.lens@[s] as nat)
    }

    /// The bits of symbol `s`, as a number and a length.
    #[inline(always)]
    pub fn sym(&self, s: usize) -> (r: (u64, u32))
        requires
            self.ok(),
            s < self.lens@.len(),
            1 <= self.lens@[s as int],
            self.nused == 1 ==> s == self.one,
        ensures
            r.1 <= 15,
            (r.0 as nat) < pow2(r.1 as nat),
            bits_of(r.0 as nat, r.1 as nat) == code_of(self.lens@, s as int),
            r.1 == code_of(self.lens@, s as int).len(),
    {
        if self.nused == 1 {
            proof {
                lemma_pow2_small();
                reveal_with_fuel(bits_of, 1);
            }
            (0, 0)
        } else {
            let l = verilith_core::prims::get(self.lens.as_slice(), s) as u32;
            let c = self.codes[s] as u64;
            proof {
                lemma_rev_bound(canon(self.lens@, s as int), l as nat);
                lemma_bits_of(c as nat, l as nat);
            }
            (c, l)
        }
    }
}

/// `first_used` skips symbols without a code.
proof fn lemma_first_used_skip(lens: Seq<u8>, i: int)
    requires
        0 <= i <= lens.len(),
        forall|j: int| 0 <= j < i ==> lens[j] == 0,
    ensures
        first_used(lens, 0) == first_used(lens, i),
    decreases i,
{
    if i > 0 {
        lemma_first_used_skip_from(lens, 0, i);
    }
}

proof fn lemma_first_used_skip_from(lens: Seq<u8>, a: int, i: int)
    requires
        0 <= a <= i <= lens.len(),
        forall|j: int| a <= j < i ==> lens[j] == 0,
    ensures
        first_used(lens, a) == first_used(lens, i),
    decreases i - a,
{
    if a < i {
        lemma_first_used_skip_from(lens, a + 1, i);
    }
}

/// Checks code lengths and builds the code: `None` unless every length is
/// at most 15, the code space is not over-subscribed and some symbol has a
/// code.
pub fn make_code(lens: Vec<u8>) -> (r: Option<HCode>)
    requires
        lens@.len() <= 1024,
    ensures
        r matches Some(c) ==> c.ok() && c.lens@ == lens@ && valid_code(lens@),
{
    let n = lens.len();
    let ghost ls = lens@;
    // Counts per length.
    let mut cnt: [u32; 16] = [0; 16];
    let mut i: usize = 0;
    let mut first_nz: usize = n;
    while i < n
        invariant
            ls == lens@,
            n == ls.len(),
            n <= 1024,
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] ls[j] as nat <= MAX_BITS,
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnt[l] as nat == count_below(ls, l as nat, i as int),
            forall|l: int| 0 <= l < 16 ==> #[trigger] cnt[l] <= i,
            first_nz <= n,
            first_nz < n ==> first_nz < i && ls[first_nz as int] != 0,
            forall|j: int| 0 <= j < i && j < first_nz ==> ls[j] == 0,
            cnt[0] <= i,
            first_nz < n ==> cnt[0] < i,
        decreases n - i,
    {
        let l = lens[i];
        if l > 15 {
            return None;
        }
        if l != 0 && first_nz == n {
            first_nz = i;
        }
        cnt[l as usize] = cnt[l as usize] + 1;
        proof {
            assert forall|k: int| 0 <= k < 16 implies #[trigger] cnt[k] as nat == count_below(ls, k as nat, i as int + 1) by {
            }
        }
        i = i + 1;
    }
    if first_nz == n {
        return None;
    }
    let nused = n - cnt[0] as usize;
    proof {
        assert forall|l: int| 0 <= l < 16 implies #[trigger] cnt[l] as nat == count(ls, l as nat) by {}
        lemma_first_used_skip(ls, first_nz as int);
        assert(first_used(ls, first_nz as int) == first_nz);
        assert(nused >= 1);
    }
    // Code space left at each length, and the first code of each length.
    let mut first: [u32; 16] = [0; 16];
    let mut lft: i64 = 1;
    let mut fc: u64 = 0;
    let mut l: usize = 1;
    proof {
        lemma_pow2_small();
    }
    while l < 16
        invariant
            1 <= l <= 16,
            forall|k: int| 0 <= k < 16 ==> #[trigger] cnt[k] as nat == count(ls, k as nat),
            forall|k: int| 0 <= k < 16 ==> #[trigger] cnt[k] <= n,
            n <= 1024,
            lft == left(ls, (l - 1) as nat),
            0 <= lft <= pow2((l - 1) as nat),
            fc == first_code(ls, l as nat),
            fc <= pow2(l as nat),
            pow2(16) == 0x10000,
            forall|k: nat| 1 <= k < l ==> #[trigger] left(ls, k) >= 0,
            forall|k: int| 1 <= k < l ==> #[trigger] first[k] as nat == first_code(ls, k as nat),
        decreases 16 - l,
    {
        proof {
            lemma_pow2_strictly_increases((l - 1) as nat, 16);
            if l < 16 { lemma_pow2_strictly_increases(l as nat, 16); }
        }
        let c = cnt[l] as i64;
        let nl = 2 * lft - c;
        if nl < 0 {
            return None;
        }
        first[l] = fc as u32;
        proof {
            assert(left(ls, l as nat) == 2 * left(ls, (l - 1) as nat) - count(ls, l as nat));
            assert(first_code(ls, (l + 1) as nat) == 2 * (first_code(ls, l as nat) + count(ls, l as nat)));
        }
        proof {
            lemma_codes_fit(ls, l as nat);
            lemma_pow2_unfold(l as nat);
            lemma_pow2_unfold((l + 1) as nat);
            lemma_pow2_strictly_increases(l as nat, 16);
            assert(l as nat - 1 + 1 == l as nat);
        }
        fc = 2 * (fc + c as u64);
        lft = nl;
        l = l + 1;
    }
    // Only complete codes (or one symbol) are read back.
    if nused != 1 && lft != 0 {
        return None;
    }
    // Canonical codes, symbol by symbol.
    let mut next = first;
    let mut codes: Vec<u16> = Vec::with_capacity(n);
    let mut s: usize = 0;
    while s < n
        invariant
            ls == lens@,
            n == ls.len(),
            n <= 1024,
            s <= n,
            codes@.len() == s,
            forall|j: int| 0 <= j < n ==> #[trigger] ls[j] as nat <= MAX_BITS,
            forall|k: nat| 1 <= k <= MAX_BITS ==> #[trigger] left(ls, k) >= 0,
            forall|k: int| 1 <= k < 16 ==> #[trigger] next[k] as nat == first_code(ls, k as nat) + count_below(ls, k as nat, s as int),
            forall|i: int| 0 <= i < s && 1 <= ls[i] ==> #[trigger] codes@[i] as nat == rev(canon(ls, i), ls[i] as nat),
        decreases n - s,
    {
        let l = lens[s] as usize;
        if l == 0 {
            codes.push(0);
        } else {
            let ghost ln = l as nat;
            proof {
                lemma_count_below_mono(ls, ln, s as int + 1, n as int);
                assert(count_below(ls, ln, s as int + 1) == count_below(ls, ln, s as int) + 1);
                lemma_codes_fit(ls, ln);
                lemma_pow2_strictly_increases(ln, 16);
                lemma_pow2_small();
                assert(next[l as int] as nat == first_code(ls, ln) + count_below(ls, ln, s as int));
            }
            let c = next[l];
            next[l] = c + 1;
            let (v, _) = verilith_core::huffman::reverse(c, l as u32);
            proof {
                lemma_rev_bound(c as nat, ln);
                lemma_pow2_strictly_increases(ln, 16);
            }
            codes.push(v as u16);
        }
        proof {
            assert forall|k: int| 1 <= k < 16 implies #[trigger] next[k] as nat == first_code(ls, k as nat) + count_below(ls, k as nat, s as int + 1) by {
            }
            assert forall|i: int| 0 <= i < s + 1 && 1 <= ls[i] implies #[trigger] codes@[i] as nat == rev(canon(ls, i), ls[i] as nat) by {
            }
        }
        s = s + 1;
    }
    Some(HCode { lens, codes, nused, one: first_nz })
}

} // verus!
