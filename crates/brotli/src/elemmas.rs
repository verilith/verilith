//! Proofs for the compressor: what it writes, the spec machine reads back.
//!
//! The compressor keeps, next to the bits it has written (`BitWriter::bits`,
//! a ghost sequence of 0s and 1s), a ghost spec state `St`. Its invariant,
//! `good(w, s)`, says that on every stream `b` that starts with the bits `w`
//! the machine gets from `init()` to `s`, and that `s` is at the end of `w`.
//! Each item the compressor writes moves `s` on by the steps the machine
//! takes to read it, proven here once per kind of item.
#[cfg(verus_only)]
use crate::bitwriter::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Streams that start with the written bits
// ---------------------------------------------------------------------------

/// The first bits of `b` are `w`.
pub open spec fn ext(b: Seq<u8>, w: Seq<nat>) -> bool {
    &&& w.len() <= nbits(b)
    &&& forall|k: int| 0 <= k < w.len() ==> #[trigger] bit(b, k) == w[k]
}

/// A stream that starts with `w + u` starts with `w`.
pub proof fn lemma_ext_prefix(b: Seq<u8>, w: Seq<nat>, u: Seq<nat>)
    requires
        ext(b, w + u),
    ensures
        ext(b, w),
{
    assert forall|k: int| 0 <= k < w.len() implies #[trigger] bit(b, k) == w[k] by {
        assert((w + u)[k] == w[k]);
    }
}

/// Bits of `b` inside `w` are bits of `w`.
pub proof fn lemma_ext_bits(b: Seq<u8>, w: Seq<nat>, p: int, n: nat)
    requires
        ext(b, w),
        0 <= p,
        p + n <= w.len(),
    ensures
        bits(b, p, n) == wbits(w, p, n),
    decreases n,
{
    if n > 0 {
        lemma_ext_bits(b, w, p + 1, (n - 1) as nat);
    }
}

/// A field written as the `n` bits of `v` reads back as `v`.
pub proof fn lemma_field(b: Seq<u8>, w: Seq<nat>, v: nat, n: nat)
    requires
        ext(b, w + bits_of(v, n)),
        v < pow2(n),
    ensures
        rd(b, w.len() as int, n) == Some(v as int),
        bits_of(v, n).len() == n,
{
    let u = bits_of(v, n);
    lemma_bits_of(v, n);
    lemma_ext_bits(b, w + u, w.len() as int, n);
    lemma_wbits_suffix(w, u, 0, n);
    assert(w.len() + 0 == w.len());
    lemma_small_mod(v, pow2(n));
}

/// The finished output starts with its bits.
pub proof fn lemma_hold_ext(b: Seq<u8>, w: Seq<nat>)
    requires
        bytes_hold(b, w),
    ensures
        ext(b, w),
{
    assert forall|k: int| 0 <= k < w.len() implies #[trigger] bit(b, k) == w[k] by {
        lemma_written(b, w, k, 1);
        reveal_with_fuel(bits, 2);
        reveal_with_fuel(wbits, 2);
    }
}

// ---------------------------------------------------------------------------
// Runs of the machine
// ---------------------------------------------------------------------------

/// The machine gets from `s` to `t` on `b`.
pub open spec fn leads(b: Seq<u8>, s: St, t: St) -> bool {
    exists|n: nat| run(b, s, n) == Step::Next(t)
}

pub proof fn lemma_leads_refl(b: Seq<u8>, s: St)
    ensures
        leads(b, s, s),
{
    assert(run(b, s, 0) == Step::Next(s));
}

/// One step.
pub proof fn lemma_leads_step(b: Seq<u8>, s: St, t: St)
    requires
        !(s.phase is Done),
        step(b, s) == Step::Next(t),
    ensures
        leads(b, s, t),
{
    assert(run(b, t, 0) == Step::Next(t));
    assert(run(b, s, 1) == Step::Next(t));
}

pub proof fn lemma_leads_trans(b: Seq<u8>, s: St, t: St, u: St)
    requires
        leads(b, s, t),
        leads(b, t, u),
    ensures
        leads(b, s, u),
{
    let m = choose|m: nat| run(b, s, m) == Step::Next(t);
    let n = choose|n: nat| run(b, t, n) == Step::Next(u);
    crate::rank::lemma_run_split(b, s, m, n);
    assert(run(b, s, m + n) == Step::Next(u));
}

/// The compressor's invariant: `s` is where the machine is, at the end of
/// the bits written so far, on any stream that starts with them.
pub open spec fn good(w: Seq<nat>, s: St) -> bool {
    &&& s.pos == w.len()
    &&& forall|b: Seq<u8>| #[trigger] ext(b, w) ==> leads(b, init(), s)
}

/// Writing `u` takes the machine from `s` to `t`.
pub open spec fn moves(w: Seq<nat>, u: Seq<nat>, s: St, t: St) -> bool {
    forall|b: Seq<u8>| #[trigger] ext(b, w + u) ==> leads(b, s, t)
}

pub proof fn lemma_good_moves(w: Seq<nat>, u: Seq<nat>, s: St, t: St)
    requires
        good(w, s),
        moves(w, u, s, t),
        t.pos == w.len() + u.len(),
    ensures
        good(w + u, t),
{
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies leads(b, init(), t) by {
        lemma_ext_prefix(b, w, u);
        lemma_leads_trans(b, init(), s, t);
    }
}

/// The start: no bits, the initial state.
pub proof fn lemma_good_init()
    ensures
        good(Seq::empty(), init()),
{
    assert forall|b: Seq<u8>| #[trigger] ext(b, Seq::empty()) implies leads(b, init(), init()) by {
        lemma_leads_refl(b, init());
    }
}

/// The end: a finished stream decodes to the output of the state it ends
/// in.
pub proof fn lemma_good_decodes(b: Seq<u8>, w: Seq<nat>, s: St)
    requires
        good(w, s),
        bytes_hold(b, w),
        s.phase is Done,
    ensures
        decodes(b, s.out, b.len() as int),
{
    lemma_hold_ext(b, w);
    assert(leads(b, init(), s));
    assert(reaches(b, s));
}

/// `moves` composes.
pub proof fn lemma_moves_trans(w: Seq<nat>, u: Seq<nat>, v: Seq<nat>, s: St, t: St, x: St)
    requires
        moves(w, u, s, t),
        moves(w + u, v, t, x),
    ensures
        moves(w, u + v, s, x),
{
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + (u + v)) implies leads(b, s, x) by {
        assert(w + (u + v) =~= (w + u) + v);
        lemma_ext_prefix(b, w + u, v);
        lemma_leads_trans(b, s, t, x);
    }
}


// ---------------------------------------------------------------------------
// Fields
// ---------------------------------------------------------------------------

/// The state after `n` more bits.
pub open spec fn adv(s: St, n: int) -> St {
    St { pos: s.pos + n, ..s }
}

/// `moves` for one step of the machine reading `u`.
pub proof fn lemma_moves_step(w: Seq<nat>, u: Seq<nat>, s: St, t: St)
    requires
        !(s.phase is Done),
        forall|b: Seq<u8>| #[trigger] ext(b, w + u) ==> step(b, s) == Step::Next(t),
    ensures
        moves(w, u, s, t),
{
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies leads(b, s, t) by {
        lemma_leads_step(b, s, t);
    }
}

/// Fields written one after another: `ext` of the whole gives `ext` of
/// each prefix.
pub proof fn lemma_ext2(b: Seq<u8>, w: Seq<nat>, x: Seq<nat>, y: Seq<nat>)
    requires
        ext(b, w + (x + y)),
    ensures
        ext(b, w + x),
        ext(b, (w + x) + y),
{
    assert(w + (x + y) =~= (w + x) + y);
    lemma_ext_prefix(b, w + x, y);
}

/// The bits of `v` in `n` bits, with `v` below `2^n`.
pub open spec fn fld(v: nat, n: nat) -> Seq<nat> {
    bits_of(v, n)
}

/// Reading a field at position `p` of `w + fld(v, n) + rest`.
pub proof fn lemma_rd(b: Seq<u8>, w: Seq<nat>, v: nat, n: nat, rest: Seq<nat>)
    requires
        ext(b, w + (fld(v, n) + rest)),
        v < pow2(n),
    ensures
        rd(b, w.len() as int, n) == Some(v as int),
        fld(v, n).len() == n,
{
    lemma_ext2(b, w, fld(v, n), rest);
    lemma_field(b, w, v, n);
}

pub proof fn lemma_pow2_small()
    ensures
        pow2(0) == 1,
        pow2(1) == 2,
        pow2(2) == 4,
        pow2(3) == 8,
        pow2(4) == 16,
        pow2(5) == 32,
        pow2(6) == 64,
        pow2(7) == 128,
        pow2(8) == 256,
        pow2(16) == 0x10000,
        pow2(20) == 0x100000,
        pow2(24) == 0x1000000,
{
    lemma2_to64();
}

// ---------------------------------------------------------------------------
// The stream header
// ---------------------------------------------------------------------------

/// The fields that write `WBITS` (16 to 24): `0` for 16, else `1` then
/// `WBITS - 17` in 3 bits, which for 17 is followed by `000`.
pub open spec fn wbits_bits(wb: int) -> Seq<nat> {
    if wb == 16 {
        fld(0, 1)
    } else if wb == 17 {
        fld(1, 1) + (fld(0, 3) + fld(0, 3))
    } else {
        fld(1, 1) + fld((wb - 17) as nat, 3)
    }
}

pub open spec fn after_wbits(s: St, wb: int) -> St {
    St { phase: Phase::MetaHeader, pos: s.pos + wbits_bits(wb).len(), wbits: wb, ..s }
}

pub proof fn lemma_wbits(w: Seq<nat>, s: St, wb: int)
    requires
        s.phase is WBits,
        s.pos == w.len(),
        16 <= wb <= 24,
    ensures
        moves(w, wbits_bits(wb), s, after_wbits(s, wb)),
        wbits_bits(wb).len() == if wb == 16 { 1int } else if wb == 17 { 7int } else { 4int },
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    lemma_bits_of(1, 1);
    lemma_bits_of(0, 3);
    lemma_bits_of((wb - 17) as nat, 3);
    let u = wbits_bits(wb);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(after_wbits(s, wb)) by {
        crate::decoder::lemma_step_wbits(b, s);
        let p = w.len() as int;
        if wb == 16 {
            assert(fld(0, 1) + Seq::<nat>::empty() =~= u);
            lemma_rd(b, w, 0, 1, Seq::empty());
        } else if wb == 17 {
            lemma_rd(b, w, 1, 1, fld(0, 3) + fld(0, 3));
            assert(w + u =~= (w + fld(1, 1)) + (fld(0, 3) + fld(0, 3)));
            lemma_rd(b, w + fld(1, 1), 0, 3, fld(0, 3));
            assert(w + u =~= ((w + fld(1, 1)) + fld(0, 3)) + (fld(0, 3) + Seq::<nat>::empty()));
            lemma_rd(b, (w + fld(1, 1)) + fld(0, 3), 0, 3, Seq::empty());
        } else {
            lemma_rd(b, w, 1, 1, fld((wb - 17) as nat, 3));
            assert(w + u =~= (w + fld(1, 1)) + (fld((wb - 17) as nat, 3) + Seq::<nat>::empty()));
            lemma_rd(b, w + fld(1, 1), (wb - 17) as nat, 3, Seq::empty());
        }
    }
    lemma_moves_step(w, u, s, after_wbits(s, wb));
}

// ---------------------------------------------------------------------------
// Meta-block headers
// ---------------------------------------------------------------------------

/// `MNIBBLES` for a meta-block of `len` bytes (1 to 2^24): the fewest
/// nibbles that hold `len - 1`.
pub open spec fn nibbles(len: int) -> nat {
    if len - 1 < 0x10000 {
        4
    } else if len - 1 < 0x100000 {
        5
    } else {
        6
    }
}

/// `MNIBBLES - 4` and `MLEN - 1`.
pub open spec fn mlen_bits(len: int) -> Seq<nat> {
    fld((nibbles(len) - 4) as nat, 2) + fld((len - 1) as nat, 4 * nibbles(len))
}

/// The header of a meta-block that is not the last: `ISLAST = 0`, the
/// length, and `ISUNCOMPRESSED`.
pub open spec fn meta_bits(len: int, unc: bool) -> Seq<nat> {
    fld(0, 1) + (mlen_bits(len) + fld(if unc { 1nat } else { 0nat }, 1))
}

/// The header of the last meta-block, compressed: `ISLAST = 1`,
/// `ISLASTEMPTY = 0`, the length.
pub open spec fn last_bits(len: int) -> Seq<nat> {
    fld(1, 1) + (fld(0, 1) + mlen_bits(len))
}

#[verifier::spinoff_prover]
proof fn lemma_mlen(b: Seq<u8>, w: Seq<nat>, len: int, rest: Seq<nat>)
    requires
        1 <= len <= 0x1000000,
        ext(b, w + (mlen_bits(len) + rest)),
    ensures
        read_meta_len(b, w.len() as int, false) == (if rest.len() >= 1 && rest[0] == 0 {
            R::Ok(MetaHeader { last: false, kind: Kind::Compressed, len }, (w.len() + mlen_bits(len).len() + 1) as int)
        } else if rest.len() >= 1 && rest[0] == 1 {
            pad_then(b, (w.len() + mlen_bits(len).len() + 1) as int, MetaHeader { last: false, kind: Kind::Uncompressed, len })
        } else {
            read_meta_len(b, w.len() as int, false)
        }),
        read_meta_len(b, w.len() as int, true) == R::Ok(MetaHeader { last: true, kind: Kind::Compressed, len }, (w.len() + mlen_bits(len).len()) as int),
        mlen_bits(len).len() == 2 + 4 * nibbles(len),
{
    lemma_pow2_small();
    let nn = nibbles(len);
    let a = fld((nn - 4) as nat, 2);
    let m = fld((len - 1) as nat, 4 * nn);
    let v = (len - 1) as nat;
    lemma_bits_of((nn - 4) as nat, 2);
    assert(v < pow2(4 * nn)) by {
        if nn == 4 { assert(4 * nn == 16); } else if nn == 5 { assert(4 * nn == 20); } else { assert(4 * nn == 24); }
    }
    assert(w + (mlen_bits(len) + rest) =~= w + (a + (m + rest)));
    lemma_rd(b, w, (nn - 4) as nat, 2, m + rest);
    assert(w + (a + (m + rest)) =~= (w + a) + (m + rest));
    lemma_rd(b, w + a, v, 4 * nn, rest);
    let p = w.len() + 2 + 4 * nn;
    // The last nibble is not zero.
    if nn > 4 {
        let q = pow2((4 * (nn - 1)) as nat);
        if nn == 5 {
            assert((4 * (nn - 1)) as nat == 16);
        } else {
            assert((4 * (nn - 1)) as nat == 20);
        }
        assert(v >= q);
        lemma_div_is_ordered(q as int, v as int, q as int);
        lemma_div_by_self(q as int);
        assert(v as int / q as int >= 1);
    }
    if rest.len() >= 1 {
        let r0 = rest[0];
        assert(w + (mlen_bits(len) + rest) =~= ((w + a) + m) + (rest.subrange(0, 1) + rest.subrange(1, rest.len() as int)));
        if r0 < 2 {
            assert(rest.subrange(0, 1) =~= fld(r0, 1)) by {
                reveal_with_fuel(bits_of, 2);
            }
            lemma_rd(b, (w + a) + m, r0, 1, rest.subrange(1, rest.len() as int));
        }
    }
}

pub open spec fn mheader(s: St, len: int, last: bool) -> St {
    St { pos: s.pos + if last { last_bits(len).len() } else { meta_bits(len, false).len() }, last, mrem: len, ..s }
}

/// A compressed meta-block's header.
#[verifier::spinoff_prover]
pub proof fn lemma_meta_compressed(w: Seq<nat>, s: St, len: int, last: bool)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
        1 <= len <= 0x1000000,
    ensures
        moves(w, if last { last_bits(len) } else { meta_bits(len, false) }, s, begin_compressed(mheader(s, len, last))),
        meta_bits(len, false).len() == 4 + 4 * nibbles(len),
        last_bits(len).len() == 4 + 4 * nibbles(len),
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    lemma_bits_of(1, 1);
    lemma_bits_of((nibbles(len) - 4) as nat, 2);
    lemma_bits_of((len - 1) as nat, 4 * nibbles(len));
    let t = begin_compressed(mheader(s, len, last));
    let u = if last { last_bits(len) } else { meta_bits(len, false) };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_header(b, s);
        let p = w.len() as int;
        if last {
            lemma_rd(b, w, 1, 1, fld(0, 1) + mlen_bits(len));
            assert(w + u =~= (w + fld(1, 1)) + (fld(0, 1) + mlen_bits(len)));
            lemma_rd(b, w + fld(1, 1), 0, 1, mlen_bits(len));
            assert(w + u =~= ((w + fld(1, 1)) + fld(0, 1)) + (mlen_bits(len) + Seq::<nat>::empty()));
            lemma_mlen(b, (w + fld(1, 1)) + fld(0, 1), len, Seq::empty());
        } else {
            lemma_rd(b, w, 0, 1, mlen_bits(len) + fld(0, 1));
            assert(w + u =~= (w + fld(0, 1)) + (mlen_bits(len) + fld(0, 1)));
            lemma_mlen(b, w + fld(0, 1), len, fld(0, 1));
            reveal_with_fuel(bits_of, 2);
        }
    }
    lemma_moves_step(w, u, s, t);
}

/// The last, empty meta-block: `ISLAST = 1`, `ISLASTEMPTY = 1`, then
/// zeros to the byte boundary.
pub open spec fn end_bits(pos: int) -> Seq<nat> {
    fld(1, 1) + (fld(1, 1) + fld(0, ((8 - (pos + 2) % 8) % 8) as nat))
}

proof fn lemma_meta_end_at(b: Seq<u8>, w: Seq<nat>, s: St, k: nat)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
        k == ((8 - (s.pos + 2) % 8) % 8) as nat,
        ext(b, w + end_bits(s.pos)),
    ensures
        step(b, s) == Step::Next(St { phase: Phase::Done, pos: s.pos + 2 + k, last: true, mrem: 0, ..s }),
{
    lemma_pow2_small();
    lemma_bits_of(1, 1);
    lemma_bits_of(0, k);
    lemma_pow2_pos(k);
    let p = w.len() as int;
    lemma_rd(b, w, 1, 1, fld(1, 1) + fld(0, k));
    assert(w + end_bits(s.pos) =~= (w + fld(1, 1)) + (fld(1, 1) + fld(0, k)));
    lemma_rd(b, w + fld(1, 1), 1, 1, fld(0, k));
    assert(w + end_bits(s.pos) =~= ((w + fld(1, 1)) + fld(1, 1)) + (fld(0, k) + Seq::<nat>::empty()));
    lemma_rd(b, (w + fld(1, 1)) + fld(1, 1), 0, k, Seq::empty());
    let h = MetaHeader { last: true, kind: Kind::EmptyLast, len: 0 };
    assert(read_meta_header(b, p) == R::Ok(h, p + 2));
    assert(pad(b, p + 2) == R::<()>::Ok((), p + 2 + k));
    crate::decoder::lemma_step_header(b, s);
}

pub proof fn lemma_meta_end(w: Seq<nat>, s: St)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
    ensures
        moves(w, end_bits(s.pos), s, St { phase: Phase::Done, pos: s.pos + end_bits(s.pos).len(), last: true, mrem: 0, ..s }),
        (s.pos + end_bits(s.pos).len()) % 8 == 0,
{
    let k = ((8 - (s.pos + 2) % 8) % 8) as nat;
    lemma_bits_of(1, 1);
    lemma_bits_of(0, k);
    let u = end_bits(s.pos);
    assert(u.len() == 2 + k);
    let t = St { phase: Phase::Done, pos: s.pos + u.len(), last: true, mrem: 0, ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_meta_end_at(b, w, s, k);
    }
    lemma_moves_step(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Uncompressed meta-blocks
// ---------------------------------------------------------------------------

/// An uncompressed meta-block's header, then zeros to the byte boundary.
pub open spec fn unc_bits(pos: int, len: int) -> Seq<nat> {
    meta_bits(len, true) + fld(0, ((8 - (pos + meta_bits(len, true).len()) % 8) % 8) as nat)
}

pub open spec fn after_unc(s: St, len: int) -> St {
    St { phase: Phase::Uncompressed, pos: s.pos + unc_bits(s.pos, len).len(), last: false, mrem: len, ..s }
}

#[verifier::spinoff_prover]
proof fn lemma_meta_unc_at(b: Seq<u8>, w: Seq<nat>, s: St, len: int, k: nat)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
        1 <= len <= 0x1000000,
        k == ((8 - (s.pos + meta_bits(len, true).len()) % 8) % 8) as nat,
        ext(b, w + unc_bits(s.pos, len)),
    ensures
        step(b, s) == Step::Next(after_unc(s, len)),
{
    lemma_pow2_small();
    lemma_bits_of(0, 1);
    lemma_bits_of(1, 1);
    lemma_bits_of(0, k);
    lemma_pow2_pos(k);
    let p = w.len() as int;
    let u = unc_bits(s.pos, len);
    assert(w + u =~= w + (fld(0, 1) + (mlen_bits(len) + (fld(1, 1) + fld(0, k)))));
    lemma_rd(b, w, 0, 1, mlen_bits(len) + (fld(1, 1) + fld(0, k)));
    assert(w + u =~= (w + fld(0, 1)) + (mlen_bits(len) + (fld(1, 1) + fld(0, k))));
    lemma_mlen(b, w + fld(0, 1), len, fld(1, 1) + fld(0, k));
    reveal_with_fuel(bits_of, 2);
    assert((fld(1, 1) + fld(0, k))[0] == 1);
    let w2 = ((w + fld(0, 1)) + mlen_bits(len)) + fld(1, 1);
    assert(w + u =~= w2 + (fld(0, k) + Seq::<nat>::empty()));
    lemma_rd(b, w2, 0, k, Seq::empty());
    let q = p + 1 + mlen_bits(len).len() + 1;
    assert(w2.len() == q);
    assert(pad(b, q) == R::<()>::Ok((), q + k));
    let h = MetaHeader { last: false, kind: Kind::Uncompressed, len };
    assert(read_meta_len(b, p + 1, false) == pad_then(b, q, h));
    assert(read_meta_header(b, p) == R::Ok(h, q + k));
    crate::decoder::lemma_step_header(b, s);
}

pub proof fn lemma_meta_unc(w: Seq<nat>, s: St, len: int)
    requires
        s.phase is MetaHeader,
        s.pos == w.len(),
        1 <= len <= 0x1000000,
    ensures
        moves(w, unc_bits(s.pos, len), s, after_unc(s, len)),
        (s.pos + unc_bits(s.pos, len).len()) % 8 == 0,
        meta_bits(len, true).len() == 4 + 4 * nibbles(len),
{
    lemma_bits_of(0, 1);
    lemma_bits_of(1, 1);
    lemma_bits_of((nibbles(len) - 4) as nat, 2);
    lemma_bits_of((len - 1) as nat, 4 * nibbles(len));
    let h = meta_bits(len, true);
    let k = ((8 - (s.pos + h.len()) % 8) % 8) as nat;
    lemma_bits_of(0, k);
    let u = unc_bits(s.pos, len);
    let t = after_unc(s, len);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_meta_unc_at(b, w, s, len, k);
    }
    lemma_moves_step(w, u, s, t);
}

/// The bytes of an uncompressed meta-block, then its end.
pub proof fn lemma_unc_bytes(w: Seq<nat>, s: St, d: Seq<u8>)
    requires
        s.phase is Uncompressed,
        s.pos == w.len(),
        s.mrem == d.len(),
    ensures
        moves(w, bytes_bits(d), s, St { phase: Phase::MetaDone, pos: s.pos + 8 * d.len(), mrem: 0, out: s.out + d, ..s }),
    decreases d.len(),
{
    lemma_bytes_bits(d);
    lemma_pow2_small();
    let t = St { phase: Phase::MetaDone, pos: s.pos + 8 * d.len(), mrem: 0, out: s.out + d, ..s };
    if d.len() == 0 {
        assert(s.out + d =~= s.out);
        assert(w + bytes_bits(d) =~= w);
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + bytes_bits(d)) implies step(b, s) == Step::Next(t) by {
            crate::decoder::lemma_step_raw(b, s);
        }
        lemma_moves_step(w, bytes_bits(d), s, t);
    } else {
        let x = d[0];
        let r = d.subrange(1, d.len() as int);
        assert(d =~= seq![x] + r);
        assert(bytes_bits(d) == bits_of(x as nat, 8) + bytes_bits(r));
        let s1 = St { pos: s.pos + 8, mrem: s.mrem - 1, out: s.out.push(x), ..s };
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(x as nat, 8)) implies step(b, s) == Step::Next(s1) by {
            crate::decoder::lemma_step_raw(b, s);
            assert(w + fld(x as nat, 8) =~= w + (fld(x as nat, 8) + Seq::<nat>::empty()));
            lemma_rd(b, w, x as nat, 8, Seq::empty());
        }
        lemma_moves_step(w, fld(x as nat, 8), s, s1);
        lemma_bits_of(x as nat, 8);
        lemma_unc_bytes(w + fld(x as nat, 8), s1, r);
        assert(s1.out + r =~= s.out + d);
        lemma_moves_trans(w, fld(x as nat, 8), bytes_bits(r), s, s1, t);
    }
}

/// The end of a meta-block that is not the last.
pub proof fn lemma_meta_done(w: Seq<nat>, s: St)
    requires
        s.phase is MetaDone,
        !s.last,
    ensures
        moves(w, Seq::empty(), s, St { phase: Phase::MetaHeader, ..s }),
{
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + Seq::empty()) implies step(b, s) == Step::Next(St { phase: Phase::MetaHeader, ..s }) by {
        crate::decoder::lemma_step_metadone(b, s);
    }
    lemma_moves_step(w, Seq::empty(), s, St { phase: Phase::MetaHeader, ..s });
}

/// The end of the last meta-block: zeros to the byte boundary.
pub proof fn lemma_last_done(w: Seq<nat>, s: St)
    requires
        s.phase is MetaDone,
        s.last,
        s.pos == w.len(),
    ensures
        moves(w, fld(0, ((8 - s.pos % 8) % 8) as nat), s, St { phase: Phase::Done, pos: s.pos + ((8 - s.pos % 8) % 8), ..s }),
{
    let k = ((8 - s.pos % 8) % 8) as nat;
    lemma_bits_of(0, k);
    lemma_pow2_pos(k);
    let t = St { phase: Phase::Done, pos: s.pos + k, ..s };
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + fld(0, k)) implies step(b, s) == Step::Next(t) by {
        crate::decoder::lemma_step_metadone(b, s);
        assert(w + fld(0, k) =~= w + (fld(0, k) + Seq::<nat>::empty()));
        lemma_rd(b, w, 0, k, Seq::empty());
    }
    lemma_moves_step(w, fld(0, k), s, t);
}

// ---------------------------------------------------------------------------
// Canonical codes
// ---------------------------------------------------------------------------

/// The canonical code of symbol `s` (§3.2.2 step 3): the codes of length
/// `lens[s]` are handed out in symbol order from `first_code`.
pub open spec fn canon(lens: Seq<u8>, s: int) -> nat {
    first_code(lens, lens[s] as nat) + count_below(lens, lens[s] as nat, s)
}

/// The first `j` bits of a code are its top `j` bits.
pub proof fn lemma_rev_prefix(x: nat, j: nat, m: nat)
    requires
        j <= m,
    ensures
        rev(x, j) == rev(x, m) / pow2((m - j) as nat),
    decreases m - j,
{
    if j == m {
        lemma2_to64();
        assert((m - j) as nat == 0);
    } else {
        lemma_rev_prefix(x, j, (m - 1) as nat);
        lemma_rev_unfold(x, m);
        let r = rev(x, (m - 1) as nat);
        let b = (x / pow2((m - 1) as nat)) % 2;
        lemma_fundamental_div_mod_converse((2 * r + b) as int, 2, r as int, b as int);
        let k = (m - 1 - j) as nat;
        lemma_pow2_pos(k);
        lemma_div_denominator(rev(x, m) as int, 2, pow2(k) as int);
        lemma_pow2_unfold((m - j) as nat);
        assert((m - j) as nat - 1 == k);
    }
}

/// Codes of length `m` start above every code of a shorter length `j`,
/// extended to `m` bits: canonical codes are prefix-free.
pub proof fn lemma_first_code_grows(lens: Seq<u8>, j: nat, m: nat)
    requires
        1 <= j < m,
    ensures
        first_code(lens, m) >= pow2((m - j) as nat) * (first_code(lens, j) + count(lens, j)),
    decreases m - j,
{
    let k = (m - 1) as nat;
    assert(first_code(lens, m) == 2 * (first_code(lens, k) + count(lens, k)));
    lemma_pow2_unfold((m - j) as nat);
    if j == k {
        lemma_pow2_unfold(1);
        lemma2_to64();
        assert((m - j) as nat == 1);
    } else {
        lemma_first_code_grows(lens, j, k);
        let q = pow2((k - j) as nat);
        let v = first_code(lens, j) + count(lens, j);
        assert((m - j) as nat - 1 == (k - j) as nat);
        assert(first_code(lens, k) >= q * v);
        assert(2 * (first_code(lens, k) + count(lens, k)) >= (2 * q) * v) by (nonlinear_arith)
            requires
                first_code(lens, k) >= q * v,
        ;
    }
}

/// The bits of a symbol's canonical code decode, under `spec::decode`, to
/// that symbol. Only the lengths up to the symbol's need to fit the code
/// space.
pub proof fn lemma_encode(lens: Seq<u8>, s: int, b: Seq<u8>, pos: int)
    requires
        0 <= s < lens.len(),
        1 <= lens[s] <= MAX_BITS,
        forall|l: nat| 1 <= l <= MAX_BITS ==> #[trigger] left(lens, l) >= 0,
        0 <= pos,
        pos + lens[s] <= nbits(b),
        bits(b, pos, lens[s] as nat) == rev(canon(lens, s), lens[s] as nat),
    ensures
        decode(lens, b, pos) == Some((s as nat, lens[s] as nat)),
{
    let m = lens[s] as nat;
    let c = canon(lens, s);
    let f = first_code(lens, m);
    let x = bits(b, pos, m);
    // The code is in range for length m, and is s's.
    lemma_count_below_mono(lens, m, s + 1, lens.len() as int);
    assert(count_below(lens, m, s + 1) == count_below(lens, m, s) + 1);
    assert(c < f + count(lens, m));
    lemma_codes_fit(lens, m);
    lemma_rev_bound(c, m);
    lemma_bits_bound(b, pos, m);
    lemma_small_mod(x, pow2(m));
    lemma_rev_iff(x, c, m);
    assert(rev(x, m) == c);
    assert(matches_at(lens, x, m));
    lemma_nth_rank(lens, m, s, 0);
    assert(count_below(lens, m, 0) == 0);
    // No shorter code is a prefix of it.
    assert forall|j: nat| 1 <= j < m implies !#[trigger] matches_at(lens, x, j) by {
        lemma_rev_prefix(x, j, m);
        lemma_first_code_grows(lens, j, m);
        let q = pow2((m - j) as nat);
        let v = first_code(lens, j) + count(lens, j);
        lemma_pow2_pos((m - j) as nat);
        lemma_div_is_ordered((q * v) as int, c as int, q as int);
        lemma_mul_is_commutative(q as int, v as int);
        lemma_div_multiples_vanish(v as int, q as int);
    }
    lemma_decode_num_first(lens, x, m, 1, m);
    lemma_decode_num_some(lens, b, pos, m, m, 1);
}

// ---------------------------------------------------------------------------

} // verus!
