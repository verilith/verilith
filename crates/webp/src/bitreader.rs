//! The bit reader: a 64-bit window on the input, proven to read exactly
//! `spec::bits` and to decode exactly `spec::read_symbol`.
#[cfg(verus_only)]
use verilith_core::huffman::*;
use crate::huffman::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;
#[cfg(verus_only)]
pub use verilith_core::bits::{lowmask, lemma_mask, lemma_and_mask, lemma_shr_bits, lemma_or_byte};

verus! {

// ---------------------------------------------------------------------------
// Masks
// ---------------------------------------------------------------------------

/// A decoded symbol is one of the alphabet's.
pub proof fn lemma_decode_num_sym(lens: Seq<u8>, x: nat, avail: nat, l: nat)
    ensures
        decode_num(lens, x, avail, l) matches Some((s, k)) ==> s < lens.len() && l <= k <= avail
            && k <= 15,
    decreases 16 - l,
{
    lemma_decode_num_len(lens, x, avail, l);
    if l <= 15 && l <= avail {
        let v = rev(x, l);
        let f = first_code(lens, l);
        if f <= v && v < f + count(lens, l) {
            assert(count_below(lens, l, 0) == 0);
            lemma_nth_bound(lens, l, (v - f) as nat, 0);
        } else {
            lemma_decode_num_sym(lens, x, avail, l + 1);
        }
    }
}

/// The fields of an entry.
pub proof fn lemma_ent_fields(s: nat, k: nat)
    requires
        s < 0x1_0000,
        k <= 15,
    ensures
        ent(s, k) & 0xffff == s,
        ent(s, k) >> 16u32 == k,
        ent(s, k) != LONG,
{
    let su = s as u32;
    let ku = k as u32;
    let e = ent(s, k);
    assert(e == ku * 0x1_0000 + su);
    assert(e & 0xffff == su && e >> 16u32 == ku && e != 0x8000_0000u32) by (bit_vector)
        requires
            e == (ku * 0x1_0000u32 + su) as u32,
            su < 0x1_0000,
            ku <= 15,
    ;
}

// ---------------------------------------------------------------------------
// The reader
// ---------------------------------------------------------------------------

/// Reads the input `data`. `buf` holds the `cnt` bits from bit position
/// `8 * ip - cnt`. `work` counts loop iterations (ghost).
pub struct BitReader {
    pub buf: u64,
    pub cnt: u32,
    pub ip: usize,
    pub work: Ghost<nat>,
}

/// Work charged for refilling.
pub open spec fn refill_cost() -> nat {
    9
}

/// Work charged for reading a symbol, refill included.
pub open spec fn sym_cost() -> nat {
    26
}

/// The table entry for the symbol at `pos`, of which `buf` holds the next
/// `cnt >= 15` bits. Unless it is `LONG`, it is the symbol and its code
/// length: what `spec::read_symbol` reads, with no input checks needed.
#[inline(always)]
pub fn peek(h: &HCode, buf: u64, Ghost(b): Ghost<Seq<u8>>, Ghost(pos): Ghost<int>, Ghost(cnt): Ghost<nat>, Ghost(lens): Ghost<Seq<u8>>) -> (e: u32)
    requires
        hcode_ok(*h, lens),
        15 <= cnt <= 64,
        0 <= pos,
        pos + cnt <= nbits(b),
        buf as nat == bits(b, pos, cnt),
    ensures
        e != LONG ==> {
            &&& e >> 16u32 <= h.tbits
            &&& e & 0xffff < lens.len()
            &&& read_symbol(lens, b, pos) == Some(((e & 0xffff) as nat, pos + (e >> 16u32)))
        },
{
    let t = h.tbits;
    proof {
        lemma_mask(t as u64);
        lemma_and_mask(buf, t as u64);
        lemma_pow2_strictly_increases(t as nat, 11);
        lemma2_to64();
    }
    let idx = (buf & ((1u64 << (t as u64)) - 1)) as usize;
    let e = get32(h.table.as_slice(), idx);
    proof {
        let x = buf as nat;
        if used(lens) == 1 {
            assert(pow2(0) == 1);
            assert(idx == 0);
            lemma_ent_fields(first_used(lens, 0) as nat, 0);
        } else {
            lemma_bits_bound(b, pos, cnt);
            lemma_decode_num(lens, b, pos, cnt, cnt, 1);
            lemma_decode_num_trunc(lens, x, cnt, t as nat, 1);
            lemma_decode_num_sym(lens, x % pow2(t as nat), t as nat, 1);
            lemma_decode_num_sym(lens, x, cnt, 1);
            assert(e == tab_entry(lens, idx as nat, t as nat));
            if let Some((s, k)) = decode_num(lens, x % pow2(t as nat), t as nat, 1) {
                lemma_ent_fields(s, k);
            }
        }
    }
    e
}

impl BitReader {
    pub open spec fn pos(&self) -> int {
        8 * self.ip - self.cnt
    }

    pub open spec fn ok(&self, b: Seq<u8>) -> bool {
        &&& self.cnt <= 64
        &&& self.ip <= b.len()
        &&& self.cnt <= 8 * self.ip
        &&& self.buf as nat == bits(b, self.pos(), self.cnt as nat)
    }

    pub fn new(data: &[u8]) -> (r: BitReader)
        ensures
            r.ok(data@),
            r.pos() == 0,
            r.work@ == 0,
    {
        BitReader { buf: 0, cnt: 0, ip: 0, work: Ghost(0) }
    }

    /// Refills to at least 56 bits, or all the input.
    #[inline(always)]
    pub fn refill(&mut self, data: &[u8])
        requires
            old(self).ok(data@),
        ensures
            final(self).ok(data@),
            final(self).pos() == old(self).pos(),
            final(self).cnt >= old(self).cnt,
            final(self).cnt >= 56 || final(self).ip == data@.len(),
            final(self).work@ <= old(self).work@ + refill_cost(),
    {
        let ghost b = data@;
        if self.cnt < 56 && data.len() >= 8 && self.ip <= data.len() - 8 {
            let w = load_u64_le(data, self.ip);
            let c = self.cnt as u64;
            let adv = ((63 - self.cnt) >> 3) as u64;
            let nc = c + 8 * adv;
            proof {
                assert(adv <= 7 && nc >= 56 && nc <= 63 && 8 * adv + c == nc) by (bit_vector)
                    requires
                        c < 56,
                        adv == ((63 - c) as u64) >> 3u64,
                        nc == c + 8 * adv,
                ;
                let pos = self.pos();
                lemma_le_bytes_bits(b, self.ip as int, 8);
                lemma_bits_bound(b, pos, c as nat);
                lemma_mask(c);
                lemma_mask(nc);
                // buf | (w << c), then the low nc bits.
                let x = self.buf;
                let r = x | (w << c);
                assert(x < (1u64 << c));
                assert((r & lowmask(nc)) == x + ((w & lowmask((nc - c) as u64)) << c)) by (bit_vector)
                    requires
                        x < (1u64 << c),
                        c < 56,
                        c <= nc,
                        nc <= 63,
                        r == x | (w << c),
                ;
                lemma_and_mask(w, (nc - c) as u64);
                lemma_bits_divmod(b, 8 * self.ip, (nc - c) as nat, 64);
                let lo = w & lowmask((nc - c) as u64);
                assert(lo as nat == bits(b, 8 * self.ip, (nc - c) as nat));
                lemma_bits_bound(b, 8 * self.ip, (nc - c) as nat);
                lemma_pow2_adds(c as nat, (nc - c) as nat);
                assert(c as nat + (nc - c) as nat == nc as nat);
                assert(lo * pow2(c as nat) <= u64::MAX) by {
                    lemma_mul_inequality(lo as int, pow2((nc - c) as nat) as int - 1, pow2(c as nat) as int);
                    lemma_pow2_strictly_increases(nc as nat, 64);
                    lemma2_to64();
                    assert((pow2((nc - c) as nat) - 1) * pow2(c as nat) == pow2(nc as nat) - pow2(c as nat))
                        by (nonlinear_arith)
                        requires
                            pow2(c as nat) * pow2((nc - c) as nat) == pow2(nc as nat),
                    ;
                }
                lemma_u64_shl_is_mul(lo, c);
                lemma_bits_split(b, pos, c as nat, (nc - c) as nat);
                assert(pos + c == 8 * self.ip);
                lemma_mul_is_commutative(pow2(c as nat) as int, lo as int);
            }
            self.buf = (self.buf | (w << c)) & ((1u64 << nc) - 1);
            self.ip = self.ip + adv as usize;
            self.cnt = nc as u32;
            self.work = Ghost(self.work@ + 1);
        } else {
            while self.cnt <= 56 && self.ip < data.len()
                invariant
                    self.ok(b),
                    b == data@,
                    self.pos() == old(self).pos(),
                    self.cnt >= old(self).cnt,
                    8 * self.work@ + old(self).cnt == 8 * old(self).work@ + self.cnt,
                decreases data@.len() - self.ip,
            {
                self.work = Ghost(self.work@ + 1);
                proof {
                    lemma_bits_bound(b, self.pos(), self.cnt as nat);
                    lemma_or_byte(self.buf, b[self.ip as int] as u64, self.cnt as u64);
                    lemma_bits_split(b, self.pos(), self.cnt as nat, 8);
                    lemma_bits_byte(b, self.ip as int);
                    assert(self.pos() + self.cnt == 8 * self.ip);
                }
                self.buf = self.buf | ((data[self.ip] as u64) << (self.cnt as u64));
                self.ip = self.ip + 1;
                self.cnt = self.cnt + 8;
            }
        }
    }

    /// `ReadBits(n)` for `n <= 32`: the bits, or `None` if the input ends
    /// first (`spec::rd`).
    #[inline(always)]
    pub fn take(&mut self, data: &[u8], n: u32) -> (r: Option<u32>)
        requires
            old(self).ok(data@),
            n <= 32,
        ensures
            final(self).ok(data@),
            r matches Some(v) ==> rd(data@, old(self).pos(), n as nat) == Some(v as nat)
                && final(self).pos() == old(self).pos() + n,
            r is None ==> rd(data@, old(self).pos(), n as nat) is None,
            final(self).pos() >= old(self).pos(),
            final(self).work@ <= old(self).work@ + refill_cost(),
    {
        let ghost b = data@;
        if self.cnt < n {
            self.refill(data);
            if self.cnt < n {
                return None;
            }
        }
        proof {
            lemma_shr_bits(b, self.pos(), self.cnt as nat, self.buf, n as u64);
            lemma_bits_bound(b, self.pos(), n as nat);
            lemma2_to64();
            if n < 32 {
                lemma_pow2_strictly_increases(n as nat, 32);
            }
            lemma_mask(n as u64);
        }
        let v = (self.buf & ((1u64 << (n as u64)) - 1)) as u32;
        self.buf = self.buf >> (n as u64);
        self.cnt = self.cnt - n;
        Some(v)
    }

    /// `ReadSymbol` with the code `h` for the lengths `lens`
    /// (`spec::read_symbol`).
    #[inline(always)]
    pub fn read_symbol(&mut self, data: &[u8], h: &HCode, Ghost(lens): Ghost<Seq<u8>>) -> (r: Option<u32>)
        requires
            old(self).ok(data@),
            hcode_ok(*h, lens),
        ensures
            final(self).ok(data@),
            match read_symbol(lens, data@, old(self).pos()) {
                Some((s, p)) => s < lens.len() && r == Some(s as u32) && final(self).pos() == p,
                None => r is None,
            },
            r matches Some(s) ==> s < lens.len(),
            final(self).pos() >= old(self).pos(),
            final(self).work@ <= old(self).work@ + sym_cost(),
    {
        let ghost b = data@;
        if self.cnt < 15 {
            self.refill(data);
        }
        let ghost pos = self.pos();
        let t = h.tbits;
        proof {
            lemma_mask(t as u64);
            lemma_and_mask(self.buf, t as u64);
            lemma_pow2_strictly_increases(t as nat, 11);
            lemma2_to64();
        }
        let idx = (self.buf & ((1u64 << (t as u64)) - 1)) as usize;
        let mut e = h.table[idx];
        let ghost x = self.buf as nat;
        let ghost cnt = self.cnt as nat;
        proof {
            if used(lens) == 1 {
                // Single symbol: zero bits.
                assert(pow2(0) == 1);
                assert(idx == 0);
                lemma_ent_fields(first_used(lens, 0) as nat, 0);
            } else {
                lemma_bits_bound(b, pos, self.cnt as nat);
                lemma_decode_num(lens, b, pos, cnt, cnt, 1);
                lemma_decode_num_trunc(lens, x, cnt, t as nat, 1);
                lemma_decode_num_sym(lens, x % pow2(t as nat), t as nat, 1);
                lemma_decode_num_sym(lens, x, cnt, 1);
                assert(e == tab_entry(lens, idx as nat, t as nat));
                if let Some((s, k)) = decode_num(lens, x % pow2(t as nat), t as nat, 1) {
                    lemma_ent_fields(s, k);
                }
            }
        }
        if e == LONG {
            let (r, Ghost(sw)) = decode_slow(h, self.buf, self.cnt, Ghost(lens));
            self.work = Ghost(self.work@ + sw);
            match r {
                None => {
                    return None;
                },
                Some(e2) => {
                    proof {
                        lemma_decode_num_sym(lens, x, cnt, 1);
                        let (s, k) = decode_num(lens, x, cnt, 1)->Some_0;
                        lemma_ent_fields(s, k);
                    }
                    e = e2;
                },
            }
        }
        let k = e >> 16;
        if k > self.cnt {
            return None;
        }
        proof {
            lemma_shr_bits(b, pos, self.cnt as nat, self.buf, k as u64);
        }
        self.buf = self.buf >> (k as u64);
        self.cnt = self.cnt - k;
        Some(e & 0xffff)
    }
}

} // verus!
