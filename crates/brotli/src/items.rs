//! The items of the format, each proven to read what the spec function of
//! the same name reads: `read_wbits`, `read_meta_header`, `varlen8`,
//! `rsym`, `read_blen`, `pad`.
use crate::bitread::*;
use crate::huffman::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use verilith_core::bits::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
use verilith_core::prims::*;
use crate::spec::{MetaHeader, BLEN_BASE, BLEN_EXTRA};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// The result of reading an item: the value and the position after it, or
/// a malformed stream, or the window ends first.
pub enum Res<T> {
    Ok(T, u64),
    Bad,
    Short,
}

/// The window holds bit positions `pos..`: what every reader requires.
pub open spec fn at(src: Seq<u8>, base: u64, pos: u64, b: Seq<u8>) -> bool {
    &&& src_ok(src, base as int, b)
    &&& 8 * base <= pos <= lim(src, base as int)
}

/// `r` reads what `s` does: the same value and position, or `Bad` only if
/// the spec rejects, or `Short` only if the window ends first (and, when
/// the window holds the whole stream, only if the spec runs out too).
pub open spec fn agrees(r: Res<u64>, s: R<int>, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    match r {
        Res::Ok(v, p) => s == R::Ok(v as int, p as int) && p <= lim(src, base as int),
        Res::Bad => s is Bad,
        Res::Short => full(src, base as int, b) ==> s is Short,
    }
}

// ---------------------------------------------------------------------------
// Symbols
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

/// `spec::rsym`: a symbol of the code `h` for the lengths `lens`.
pub fn read_sym(h: &HCode, src: &[u8], base: u64, pos: u64, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        hcode_ok(*h, lens),
        at(src@, base, pos, b),
    ensures
        agrees(r, rsym(lens, b, pos as int), src@, base, b),
        r matches Res::Ok(s, p) ==> s < lens.len() && pos <= p <= pos + 15,
        !(r is Bad),
{
    let (x, c) = peek(src, base, pos, Ghost(b));
    let t = h.tbits;
    proof {
        lemma_mask(t as u64);
        lemma_and_mask(x, t as u64);
        lemma_pow2_strictly_increases(t as nat, 11);
        lemma2_to64();
    }
    let idx = (x & ((1u64 << (t as u64)) - 1)) as usize;
    let e = get32(h.table.as_slice(), idx);
    let ghost xn = x as nat;
    if e != LONG {
        let k = (e >> 16) as u64;
        let s = (e & 0xffff) as u64;
        proof {
            if used(lens) == 1 {
                assert(pow2(0) == 1);
                assert(idx == 0);
                lemma_ent_fields(first_used(lens, 0) as nat, 0);
            } else {
                assert(e == tab_entry(lens, idx as nat, t as nat));
                lemma_decode_num_sym(lens, xn % pow2(t as nat), t as nat, 1);
                if let Some((s0, k0)) = decode_num(lens, xn % pow2(t as nat), t as nat, 1) {
                    lemma_ent_fields(s0, k0);
                }
            }
        }
        if k > c {
            proof {
                if full(src@, base as int, b) && used(lens) != 1 {
                    assert(pos + c == nbits(b));
                    lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                }
            }
            return Res::Short;
        }
        proof {
            if used(lens) != 1 {
                lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
        }
        return Res::Ok(s, pos + k);
    }
    proof {
        if used(lens) == 1 {
            assert(pow2(0) == 1);
            lemma_ent_fields(first_used(lens, 0) as nat, 0);
        }
    }
    let (r, _) = decode_slow(h, x, c as u32, Ghost(lens));
    match r {
        Some(e2) => {
            proof {
                lemma_decode_num_sym(lens, xn, c as nat, 1);
                let (s0, k0) = decode_num(lens, xn, c as nat, 1)->Some_0;
                lemma_ent_fields(s0, k0);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
            Res::Ok((e2 & 0xffff) as u64, pos + (e2 >> 16) as u64)
        },
        None => {
            proof {
                if full(src@, base as int, b) {
                    if c < 56 {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    } else {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    }
                }
            }
            Res::Short
        },
    }
}

/// Entry `j` of tree `tree` in a group's tables laid side by side, each
/// `2^ft` entries.
pub open spec fn fget(f: Seq<u32>, tree: int, ft: u64, j: int) -> u32 {
    f[tree * pow2(ft as nat) + j]
}

/// `f` holds, at tree `tree`, the table of `h` widened to `ft` bits.
pub open spec fn flat_at(f: Seq<u32>, tree: int, ft: u64, h: HCode) -> bool {
    &&& 0 <= tree
    &&& h.tbits <= ft <= 10
    &&& (tree + 1) * pow2(ft as nat) <= f.len()
    &&& f.len() <= 0x1_0000_0000
    &&& forall|j: int| 0 <= j < pow2(ft as nat) ==> #[trigger] fget(f, tree, ft, j) == h.table@[j % (pow2(h.tbits as nat) as int)]
}

/// Appending to `f` keeps what it holds.
pub proof fn lemma_flat_ext(f: Seq<u32>, g: Seq<u32>, tree: int, ft: u64, h: HCode)
    requires
        flat_at(f, tree, ft, h),
        f.is_prefix_of(g),
        g.len() <= 0x1_0000_0000,
    ensures
        flat_at(g, tree, ft, h),
{
    let pf = pow2(ft as nat) as int;
    assert(tree * pf + pf == (tree + 1) * pf) by (nonlinear_arith);
    assert(0 <= tree * pf) by (nonlinear_arith)
        requires
            0 <= tree,
            0 <= pf,
    ;
    assert forall|j: int| 0 <= j < pf implies #[trigger] fget(g, tree, ft, j) == h.table@[j % (pow2(h.tbits as nat) as int)] by {
        assert(fget(f, tree, ft, j) == h.table@[j % (pow2(h.tbits as nat) as int)]);
        assert(g[tree * pf + j] == f[tree * pf + j]);
    }
}

/// `spec::rsym` from a window `x` of `c` bits at `pos`. `Short` means the
/// window ran out; it is the spec's `Short` too when the window is all the
/// stream has left and that is all the stream. `sure` says the window has
/// at least 15 bits, which saves the check.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn sym_win(h: &HCode, x: u64, c: u64, pos: u64, sure: bool, Ghost(src): Ghost<Seq<u8>>, base: u64, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        sure ==> c >= 15,
        hcode_ok(*h, lens),
        src_ok(src, base as int, b),
        8 * base <= pos,
        pos + c <= lim(src, base as int),
        c <= 56,
        x as nat == bits(b, pos as int, c as nat),
        x < pow2(c as nat),
    ensures
        r matches Res::Ok(s, p) ==> rsym(lens, b, pos as int) == R::Ok(s as int, p as int) && s < lens.len()
            && pos <= p <= pos + 15 && p <= pos + c,
        !(r is Bad),
        r is Short ==> (c == 56 || pos + c == lim(src, base as int)) ==> full(src, base as int, b) ==> rsym(lens, b, pos as int) is Short,
{
    let t = h.tbits;
    proof {
        lemma_mask(t as u64);
        lemma_and_mask(x, t as u64);
        lemma_pow2_strictly_increases(t as nat, 11);
        lemma2_to64();
    }
    let idx = (x & ((1u64 << (t as u64)) - 1)) as usize;
    let e = get32(h.table.as_slice(), idx);
    let ghost xn = x as nat;
    if e != LONG {
        let k = (e >> 16) as u64;
        let s = (e & 0xffff) as u64;
        proof {
            if used(lens) == 1 {
                assert(pow2(0) == 1);
                assert(idx == 0);
                lemma_ent_fields(first_used(lens, 0) as nat, 0);
            } else {
                assert(e == tab_entry(lens, idx as nat, t as nat));
                lemma_decode_num_sym(lens, xn % pow2(t as nat), t as nat, 1);
                if let Some((s0, k0)) = decode_num(lens, xn % pow2(t as nat), t as nat, 1) {
                    lemma_ent_fields(s0, k0);
                }
            }
        }
        // With `sure`, the caller has the 15 bits the longest code takes.
        if !sure && k > c {
            proof {
                if full(src, base as int, b) && (c == 56 || pos + c == lim(src, base as int)) && used(lens) != 1 {
                    assert(pos + c == nbits(b));
                    lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                }
            }
            return Res::Short;
        }
        proof {
            if used(lens) != 1 {
                lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
        }
        return Res::Ok(s, pos + k);
    }
    proof {
        if used(lens) == 1 {
            assert(pow2(0) == 1);
            lemma_ent_fields(first_used(lens, 0) as nat, 0);
        }
    }
    let (r, _) = decode_slow(h, x, c as u32, Ghost(lens));
    match r {
        Some(e2) => {
            proof {
                lemma_decode_num_sym(lens, xn, c as nat, 1);
                let (s0, k0) = decode_num(lens, xn, c as nat, 1)->Some_0;
                lemma_ent_fields(s0, k0);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
            Res::Ok((e2 & 0xffff) as u64, pos + (e2 >> 16) as u64)
        },
        None => {
            proof {
                if full(src, base as int, b) && (c == 56 || pos + c == lim(src, base as int)) {
                    if c < 56 {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    } else {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    }
                }
            }
            Res::Short
        },
    }
}

/// `sym_win`, with the table entry taken from `flat` when `on` says so:
/// the tables of a whole group side by side, all `ft` bits wide, so that
/// the entry's address does not wait on a load of the tree's own record.
/// `spec::rsym` from a window `x` of `c` bits at `pos`. `Short` means the
/// window ran out; it is the spec's `Short` too when the window is all the
/// stream has left and that is all the stream. `sure` says the window has
/// at least 15 bits, which saves the check.
#[verifier::spinoff_prover]
#[inline(always)]
pub fn sym_winf(h: &HCode, flat: &[u32], tree: usize, ft: u64, on: bool, x: u64, c: u64, pos: u64, sure: bool, Ghost(src): Ghost<Seq<u8>>, base: u64, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        on ==> flat_at(flat@, tree as int, ft, *h),
        sure ==> c >= 15,
        hcode_ok(*h, lens),
        src_ok(src, base as int, b),
        8 * base <= pos,
        pos + c <= lim(src, base as int),
        c <= 56,
        x as nat == bits(b, pos as int, c as nat),
        x < pow2(c as nat),
    ensures
        r matches Res::Ok(s, p) ==> rsym(lens, b, pos as int) == R::Ok(s as int, p as int) && s < lens.len()
            && pos <= p <= pos + 15 && p <= pos + c,
        !(r is Bad),
        r is Short ==> (c == 56 || pos + c == lim(src, base as int)) ==> full(src, base as int, b) ==> rsym(lens, b, pos as int) is Short,
{
    let t = h.tbits;
    proof {
        lemma_mask(t as u64);
        lemma_and_mask(x, t as u64);
        lemma_pow2_strictly_increases(t as nat, 11);
        lemma2_to64();
    }
    let ghost idx = (x & lowmask(t as u64)) as usize;
    let e = if on {
        proof {
            lemma_mask(ft);
            lemma_pow2_pos(ft as nat);
        }
        let j = x & ((1u64 << ft) - 1);
        proof {
            lemma_and_mask(x, ft);
            lemma_pow2_pos(ft as nat);
            lemma_pow2_pos(t as nat);
            lemma_pow2_strictly_increases(ft as nat, 11);
            let pt = pow2(t as nat) as int;
            let pf = pow2(ft as nat) as int;
            let pd = pow2((ft - t) as nat) as int;
            lemma_pow2_pos((ft - t) as nat);
            lemma_pow2_adds(t as nat, (ft - t) as nat);
            assert(pf == pt * pd);
            lemma_mod_mod(x as int, pt, pd);
            assert((j as int) % pt == idx as int);
            assert(fget(flat@, tree as int, ft, j as int) == h.table@[(j as int) % pt]);
            assert(tree * pf + pf == (tree + 1) * pf) by (nonlinear_arith);
            assert(tree * pf <= flat@.len());
            assert(tree * pf < 0x1_0000_0000_0000);
            lemma_u64_shl_is_mul(tree as u64, ft);
        }
        get32(flat, ((tree as u64) << ft) as usize + j as usize)
    } else {
        get32(h.table.as_slice(), (x & ((1u64 << (t as u64)) - 1)) as usize)
    };
    let ghost xn = x as nat;
    if e != LONG {
        let k = (e >> 16) as u64;
        let s = (e & 0xffff) as u64;
        proof {
            if used(lens) == 1 {
                assert(pow2(0) == 1);
                assert(idx == 0);
                lemma_ent_fields(first_used(lens, 0) as nat, 0);
            } else {
                assert(e == tab_entry(lens, idx as nat, t as nat));
                lemma_decode_num_sym(lens, xn % pow2(t as nat), t as nat, 1);
                if let Some((s0, k0)) = decode_num(lens, xn % pow2(t as nat), t as nat, 1) {
                    lemma_ent_fields(s0, k0);
                }
            }
        }
        // With `sure`, the caller has the 15 bits the longest code takes.
        if !sure && k > c {
            proof {
                if full(src, base as int, b) && (c == 56 || pos + c == lim(src, base as int)) && used(lens) != 1 {
                    assert(pos + c == nbits(b));
                    lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                }
            }
            return Res::Short;
        }
        proof {
            if used(lens) != 1 {
                lemma_decode_num_trunc(lens, xn, c as nat, t as nat, 1);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
        }
        return Res::Ok(s, pos + k);
    }
    proof {
        if used(lens) == 1 {
            assert(pow2(0) == 1);
            lemma_ent_fields(first_used(lens, 0) as nat, 0);
        }
    }
    let (r, _) = decode_slow(h, x, c as u32, Ghost(lens));
    match r {
        Some(e2) => {
            proof {
                lemma_decode_num_sym(lens, xn, c as nat, 1);
                let (s0, k0) = decode_num(lens, xn, c as nat, 1)->Some_0;
                lemma_ent_fields(s0, k0);
                lemma_decode_num_some(lens, b, pos as int, c as nat, c as nat, 1);
            }
            Res::Ok((e2 & 0xffff) as u64, pos + (e2 >> 16) as u64)
        },
        None => {
            proof {
                if full(src, base as int, b) && (c == 56 || pos + c == lim(src, base as int)) {
                    if c < 56 {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    } else {
                        lemma_decode_num(lens, b, pos as int, c as nat, c as nat, 1);
                    }
                }
            }
            Res::Short
        },
    }
}

// ---------------------------------------------------------------------------
// Fields
// ---------------------------------------------------------------------------

/// `spec::read_wbits`.
pub fn read_wbits(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        at(src@, base, pos, b),
    ensures
        agrees(r, crate::spec::read_wbits(b, pos as int), src@, base, b),
        r matches Res::Ok(w, p) ==> 10 <= w <= 24 && pos < p,
{
    match read_bits(src, base, pos, 1, Ghost(b)) {
        None => Res::Short,
        Some(x) => if x == 0 {
            Res::Ok(16, pos + 1)
        } else {
            match read_bits(src, base, pos + 1, 3, Ghost(b)) {
                None => Res::Short,
                Some(n) => if n != 0 {
                    proof { lemma2_to64(); }
                    Res::Ok(17 + n, pos + 4)
                } else {
                    match read_bits(src, base, pos + 4, 3, Ghost(b)) {
                        None => Res::Short,
                        Some(m) => if m == 1 {
                            Res::Bad
                        } else if m != 0 {
                            proof { lemma2_to64(); }
                            Res::Ok(8 + m, pos + 7)
                        } else {
                            Res::Ok(17, pos + 7)
                        },
                    }
                },
            }
        },
    }
}

/// `spec::varlen8`.
pub fn varlen8(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        at(src@, base, pos, b),
    ensures
        agrees(r, crate::spec::varlen8(b, pos as int), src@, base, b),
        r matches Res::Ok(v, p) ==> v <= 255 && pos < p && (v > 0 ==> pos + 4 <= p),
        !(r is Bad),
{
    match read_bits(src, base, pos, 1, Ghost(b)) {
        None => Res::Short,
        Some(x) => if x == 0 {
            Res::Ok(0, pos + 1)
        } else {
            match read_bits(src, base, pos + 1, 3, Ghost(b)) {
                None => Res::Short,
                Some(n) => if n == 0 {
                    Res::Ok(1, pos + 4)
                } else {
                    proof {
                        lemma2_to64();
                    }
                    match read_bits(src, base, pos + 4, n, Ghost(b)) {
                        None => Res::Short,
                        Some(v) => {
                            proof {
                                lemma2_to64();
                                lemma_mask(n);
                                assert(n < 8);
                                lemma_pow2_strictly_increases(n as nat, 8);
                            }
                            Res::Ok((1u64 << n) + v, pos + 4 + n)
                        },
                    }
                },
            }
        },
    }
}

/// `spec::pad`: the bits up to the next byte boundary, which must be zero.
pub fn pad(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        at(src@, base, pos, b),
    ensures
        match r {
            Res::Ok(_, p) => crate::spec::pad(b, pos as int) matches R::Ok(_, q) && q == p && p
                <= lim(src@, base as int) && p % 8 == 0,
            Res::Bad => crate::spec::pad(b, pos as int) is Bad,
            Res::Short => full(src@, base as int, b) ==> crate::spec::pad(b, pos as int) is Short,
        },
{
    let n = (8 - pos % 8) % 8;
    match read_bits(src, base, pos, n, Ghost(b)) {
        None => Res::Short,
        Some(v) => if v == 0 {
            Res::Ok(0, pos + n)
        } else {
            Res::Bad
        },
    }
}

/// `spec::read_blen`: a block count with the block count code `h`.
pub fn read_blen(h: &HCode, src: &[u8], base: u64, pos: u64, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<u64>)
    requires
        hcode_ok(*h, lens),
        lens.len() == 26,
        at(src@, base, pos, b),
    ensures
        agrees(r, crate::spec::read_blen(lens, b, pos as int), src@, base, b),
        r matches Res::Ok(v, p) ==> 1 <= v <= 16625 + 0xff_ffff && pos + 2 <= p,
        !(r is Bad),
{
    match read_sym(h, src, base, pos, Ghost(lens), Ghost(b)) {
        Res::Ok(sym, p) => {
            let n = BLEN_EXTRA[sym as usize] as u64;
            proof {
                assert(forall|i: int| 0 <= i < 26 ==> #[trigger] BLEN_EXTRA[i] >= 2) by (compute);
            }
            match read_bits(src, base, p, n, Ghost(b)) {
                None => Res::Short,
                Some(e) => {
                    proof {
                        assert(n <= 24);
                        lemma_pow2_strictly_increases(n as nat, 25);
                        lemma2_to64();
                        assert(pow2(24) == 0x100_0000) by (compute);
                        if n < 24 {
                            lemma_pow2_strictly_increases(n as nat, 24);
                        }
                    }
                    Res::Ok(BLEN_BASE[sym as usize] as u64 + e, p + n)
                },
            }
        },
        Res::Bad => Res::Bad,
        Res::Short => Res::Short,
    }
}

/// Kinds of meta-block, as `spec::Kind`.
pub const K_EMPTY_LAST: u8 = 0;
pub const K_METADATA: u8 = 1;
pub const K_UNCOMPRESSED: u8 = 2;
pub const K_COMPRESSED: u8 = 3;

pub open spec fn kind_code(k: Kind) -> u8 {
    match k {
        Kind::EmptyLast => K_EMPTY_LAST,
        Kind::Metadata => K_METADATA,
        Kind::Uncompressed => K_UNCOMPRESSED,
        Kind::Compressed => K_COMPRESSED,
    }
}

/// A meta-block header as the decoder holds it.
pub struct MetaHdr {
    pub last: bool,
    pub kind: u8,
    pub len: u32,
}

pub open spec fn hdr_agrees(r: Res<MetaHdr>, s: R<MetaHeader>, src: Seq<u8>, base: u64, b: Seq<u8>) -> bool {
    match r {
        Res::Ok(h, p) => s matches R::Ok(sh, q) && q == p && sh.last == h.last && kind_code(sh.kind)
            == h.kind && sh.len == h.len && p <= lim(src, base as int),
        Res::Bad => s is Bad,
        Res::Short => full(src, base as int, b) ==> s is Short,
    }
}

fn pad_then(src: &[u8], base: u64, pos: u64, h: MetaHdr, Ghost(b): Ghost<Seq<u8>>, Ghost(sh): Ghost<MetaHeader>) -> (r: Res<MetaHdr>)
    requires
        at(src@, base, pos, b),
        sh.last == h.last && kind_code(sh.kind) == h.kind && sh.len == h.len,
    ensures
        hdr_agrees(r, crate::spec::pad_then(b, pos as int, sh), src@, base, b),
        r matches Res::Ok(h2, p) ==> h2 == h && p % 8 == 0,
{
    match pad(src, base, pos, Ghost(b)) {
        Res::Ok(_, p) => Res::Ok(h, p),
        Res::Bad => Res::Bad,
        Res::Short => Res::Short,
    }
}

/// `spec::read_meta_len`.
fn read_meta_len(src: &[u8], base: u64, pos: u64, last: bool, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<MetaHdr>)
    requires
        at(src@, base, pos, b),
    ensures
        hdr_agrees(r, crate::spec::read_meta_len(b, pos as int, last), src@, base, b),
        r matches Res::Ok(h, p) ==> h.len <= 0x100_0000 && h.kind != K_EMPTY_LAST && h.last == last
            && (h.kind == K_METADATA || h.len >= 1) && (h.kind == K_METADATA || h.kind
            == K_UNCOMPRESSED ==> p % 8 == 0) && (h.kind == K_UNCOMPRESSED ==> !last),
{
    proof {
        lemma2_to64();
    }
    match read_bits(src, base, pos, 2, Ghost(b)) {
        None => Res::Short,
        Some(mn) => if mn == 3 {
            match read_bits(src, base, pos + 2, 1, Ghost(b)) {
                None => Res::Short,
                Some(reserved) => if reserved != 0 {
                    Res::Bad
                } else {
                    match read_bits(src, base, pos + 3, 2, Ghost(b)) {
                        None => Res::Short,
                        Some(nbytes) => if nbytes == 0 {
                            let h = MetaHdr { last, kind: K_METADATA, len: 0 };
                            pad_then(src, base, pos + 5, h, Ghost(b), Ghost(MetaHeader { last, kind: Kind::Metadata, len: 0 }))
                        } else {
                            match read_bits(src, base, pos + 5, 8 * nbytes, Ghost(b)) {
                                None => Res::Short,
                                Some(v) => {
                                    let sh = 8 * (nbytes - 1);
                                    proof {
                                        lemma_u64_shr_is_div(v, sh);
                                        lemma_pow2_strictly_increases((8 * nbytes) as nat, 25);
                                        assert(pow2(24) == 0x100_0000) by (compute);
                                        if 8 * nbytes < 24 {
                                            lemma_pow2_strictly_increases((8 * nbytes) as nat, 24);
                                        }
                                    }
                                    if nbytes > 1 && v >> sh == 0 {
                                        Res::Bad
                                    } else {
                                        let h = MetaHdr { last, kind: K_METADATA, len: (v + 1) as u32 };
                                        pad_then(src, base, pos + 5 + 8 * nbytes, h, Ghost(b), Ghost(MetaHeader { last, kind: Kind::Metadata, len: v + 1 }))
                                    }
                                },
                            }
                        },
                    }
                },
            }
        } else {
            let nn = mn + 4;
            match read_bits(src, base, pos + 2, 4 * nn, Ghost(b)) {
                None => Res::Short,
                Some(v) => {
                    let sh = 4 * (nn - 1);
                    proof {
                        lemma_u64_shr_is_div(v, sh);
                        lemma_pow2_strictly_increases((4 * nn) as nat, 25);
                        assert(pow2(24) == 0x100_0000) by (compute);
                        if 4 * nn < 24 {
                            lemma_pow2_strictly_increases((4 * nn) as nat, 24);
                        }
                    }
                    if nn > 4 && v >> sh == 0 {
                        Res::Bad
                    } else {
                        let p = pos + 2 + 4 * nn;
                        if last {
                            Res::Ok(MetaHdr { last, kind: K_COMPRESSED, len: (v + 1) as u32 }, p)
                        } else {
                            match read_bits(src, base, p, 1, Ghost(b)) {
                                None => Res::Short,
                                Some(u) => if u == 1 {
                                    let h = MetaHdr { last, kind: K_UNCOMPRESSED, len: (v + 1) as u32 };
                                    pad_then(src, base, p + 1, h, Ghost(b), Ghost(MetaHeader { last, kind: Kind::Uncompressed, len: v + 1 }))
                                } else {
                                    Res::Ok(MetaHdr { last, kind: K_COMPRESSED, len: (v + 1) as u32 }, p + 1)
                                },
                            }
                        }
                    }
                },
            }
        },
    }
}

/// `spec::read_meta_header`.
pub fn read_meta_header(src: &[u8], base: u64, pos: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: Res<MetaHdr>)
    requires
        at(src@, base, pos, b),
    ensures
        hdr_agrees(r, crate::spec::read_meta_header(b, pos as int), src@, base, b),
        r matches Res::Ok(h, p) ==> h.len <= 0x100_0000 && (h.kind == K_EMPTY_LAST ==> h.last && h.len
            == 0) && (h.kind == K_COMPRESSED || h.kind == K_UNCOMPRESSED ==> h.len >= 1) && (h.kind
            == K_METADATA || h.kind == K_UNCOMPRESSED ==> p % 8 == 0) && (h.kind == K_UNCOMPRESSED
            ==> !h.last) && pos < p,
{
    match read_bits(src, base, pos, 1, Ghost(b)) {
        None => Res::Short,
        Some(islast) => {
            let last = islast == 1;
            if last {
                match read_bits(src, base, pos + 1, 1, Ghost(b)) {
                    None => Res::Short,
                    Some(empty) => if empty == 1 {
                        Res::Ok(MetaHdr { last, kind: K_EMPTY_LAST, len: 0 }, pos + 2)
                    } else {
                        read_meta_len(src, base, pos + 2, last, Ghost(b))
                    },
                }
            } else {
                read_meta_len(src, base, pos + 1, last, Ghost(b))
            }
        },
    }
}

} // verus!
