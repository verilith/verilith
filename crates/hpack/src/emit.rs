//! Encoding integers (RFC 7541 §5.1), string literals (§5.2), field
//! representations (§6) and size updates (§6.3), each proven to decode,
//! by the decoder's specification (`spec::rep`, `spec::block`), to exactly
//! what was encoded.
//!
//! The encodings are spec functions (`int_enc`, `str_enc`, `lit_enc`);
//! the `put_*` functions write them, and the `lemma_rep_*` lemmas say what
//! `rep` makes of them.
use crate::hencode;
#[cfg(verus_keep_ghost)]
use crate::hencode::enc_ok;
use crate::lemmas::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Integers (§5.1)
// ---------------------------------------------------------------------------

/// The continuation bytes of `r`: 7 bits each, least significant first,
/// the top bit set on all but the last.
pub open spec fn tail_bytes(r: nat) -> Seq<u8>
    decreases r,
{
    if r < 128 {
        seq![r as u8]
    } else {
        seq![(r % 128 + 128) as u8] + tail_bytes(r / 128)
    }
}

/// `v` as an integer with an `n`-bit prefix, the bits above the prefix in
/// the first byte being `flags`.
pub open spec fn int_enc(flags: nat, n: nat, v: nat) -> Seq<u8> {
    let k = (pow2_8(n) - 1) as nat;
    if v < k {
        seq![(flags + v) as u8]
    } else {
        seq![(flags + k) as u8] + tail_bytes((v - k) as nat)
    }
}

/// The first byte of `int_enc`.
pub open spec fn int_first(flags: nat, n: nat, v: nat) -> nat {
    let k = (pow2_8(n) - 1) as nat;
    if v < k {
        flags + v
    } else {
        flags + k
    }
}

/// The flags and prefix are one of the four the representations use.
pub open spec fn int_form(flags: nat, n: nat) -> bool {
    (flags == 0x80 && n == 7) || (flags == 0 && n == 7) || (flags == 0x40 && n == 6) || (flags == 0x20 && n == 5)
        || (flags == 0 && n == 4) || (flags == 0x10 && n == 4)
}

proof fn lemma_tail_len(r: nat, k: nat)
    requires
        k >= 1,
        r < pow128(k),
    ensures
        1 <= tail_bytes(r).len() <= k,
    decreases r,
{
    assert(pow128(1) == 128 * pow128(0));
    if r >= 128 {
        assert(k >= 2);
        assert(pow128(k) == 128 * pow128((k - 1) as nat));
        lemma_tail_len(r / 128, (k - 1) as nat);
    }
}

proof fn lemma_tail_dec(b: Seq<u8>, pos: int, i: nat, acc: nat, r: nat)
    requires
        0 <= pos,
        pos + tail_bytes(r).len() <= b.len(),
        b.subrange(pos, pos + tail_bytes(r).len()) == tail_bytes(r),
        acc + r * pow128(i) <= 0xFFFF_FFFF,
        i + tail_bytes(r).len() <= 5,
    ensures
        int_tail(b, pos, i, acc) == IntR::Ok(acc + r * pow128(i), pos + tail_bytes(r).len()),
    decreases r,
{
    let t = tail_bytes(r);
    assert(t.len() >= 1);
    assert(b[pos] == b.subrange(pos, pos + t.len())[0]);
    let p = pow128(i);
    if r < 128 {
        assert(b[pos] as nat == r);
    } else {
        let t2 = tail_bytes(r / 128);
        assert(t =~= seq![(r % 128 + 128) as u8] + t2);
        assert(b[pos] as nat == r % 128 + 128);
        assert((b[pos] as nat) % 128 == r % 128);
        assert((r % 128) * p <= r * p) by (nonlinear_arith)
            requires
                r % 128 <= r,
        ;
        assert(pow128(i + 1) == 128 * p);
        assert(acc + (r % 128) * p + (r / 128) * pow128(i + 1) == acc + r * p) by (nonlinear_arith)
            requires
                r == 128 * (r / 128) + r % 128,
                pow128(i + 1) == 128 * p,
        ;
        assert(b.subrange(pos + 1, pos + 1 + t2.len()) =~= b.subrange(pos, pos + t.len()).subrange(1, t.len() as int));
        assert(t.subrange(1, t.len() as int) =~= t2);
        lemma_tail_dec(b, pos + 1, i + 1, acc + (r % 128) * p, r / 128);
    }
}

pub proof fn lemma_int_enc(flags: nat, n: nat, v: nat)
    requires
        int_form(flags, n),
        v <= 0xFFFF_FFFF,
    ensures
        1 <= int_enc(flags, n, v).len() <= 6,
        int_enc(flags, n, v)[0] as nat == int_first(flags, n, v),
        int_first(flags, n, v) < 256,
        v == 0 ==> int_enc(flags, n, v) == seq![flags as u8],
{
    let k = (pow2_8(n) - 1) as nat;
    if v >= k {
        assert(pow128(5) == 34359738368) by (compute);
        lemma_tail_len((v - k) as nat, 5);
    }
}

/// What the decoder makes of `int_enc`, wherever it is in the input.
pub proof fn lemma_int_dec(b: Seq<u8>, pos: int, flags: nat, n: nat, v: nat)
    requires
        int_form(flags, n),
        v <= 0xFFFF_FFFF,
        0 <= pos,
        pos + int_enc(flags, n, v).len() <= b.len(),
        b.subrange(pos, pos + int_enc(flags, n, v).len()) == int_enc(flags, n, v),
    ensures
        int_dec(b, pos, n) == IntR::Ok(v, pos + int_enc(flags, n, v).len()),
        b[pos] as nat == int_first(flags, n, v),
{
    let w = int_enc(flags, n, v);
    let k = (pow2_8(n) - 1) as nat;
    lemma_int_enc(flags, n, v);
    assert(b[pos] == w[0]);
    let x: nat = if v < k { v } else { k };
    assert((flags + x) % pow2_8(n) == x);
    if v >= k {
        let t = tail_bytes((v - k) as nat);
        assert(pow128(5) == 34359738368) by (compute);
        lemma_tail_len((v - k) as nat, 5);
        assert(pow128(0) == 1);
        assert(w =~= seq![(flags + k) as u8] + t);
        assert(b.subrange(pos + 1, pos + 1 + t.len()) =~= w.subrange(1, w.len() as int));
        assert(w.subrange(1, w.len() as int) =~= t);
        lemma_tail_dec(b, pos + 1, 0, k, (v - k) as nat);
    }
}

pub const KMAX: [u32; 8] = [0, 1, 3, 7, 15, 31, 63, 127];

/// Appends `int_enc(flags, n, v)`.
#[inline(always)]
pub fn put_int(out: &mut Vec<u8>, flags: u8, n: u8, v: u32)
    requires
        int_form(flags as nat, n as nat),
    ensures
        final(out)@ == old(out)@ + int_enc(flags as nat, n as nat, v as nat),
{
    let k = KMAX[n as usize];
    assert(k == pow2_8(n as nat) - 1);
    if v < k {
        out.push(flags + v as u8);
        proof {
            assert(final(out)@ =~= old(out)@ + int_enc(flags as nat, n as nat, v as nat));
        }
        return;
    }
    out.push(flags + k as u8);
    let mut r = v - k;
    proof {
        assert(out@ + tail_bytes(r as nat) =~= old(out)@ + int_enc(flags as nat, n as nat, v as nat));
    }
    while r >= 128
        invariant
            out@ + tail_bytes(r as nat) == old(out)@ + int_enc(flags as nat, n as nat, v as nat),
        decreases r,
    {
        let ghost o = out@;
        out.push((r % 128 + 128) as u8);
        proof {
            assert(tail_bytes(r as nat) == seq![(r % 128 + 128) as u8] + tail_bytes((r / 128) as nat));
            assert(out@ + tail_bytes((r / 128) as nat) =~= o + tail_bytes(r as nat));
        }
        r = r / 128;
    }
    let ghost o = out@;
    out.push(r as u8);
    proof {
        assert(out@ =~= o + tail_bytes(r as nat));
    }
}

// ---------------------------------------------------------------------------
// String literals (§5.2)
// ---------------------------------------------------------------------------

/// A string literal: H bit, length, then `raw` (Huffman-coded if `h`).
pub open spec fn str_enc(h: bool, raw: Seq<u8>) -> Seq<u8> {
    int_enc(if h { 128 } else { 0 }, 7, raw.len()) + raw
}

/// `raw` is `s`, Huffman-coded if `h`, and not too long for the decoder.
pub open spec fn str_ok(h: bool, raw: Seq<u8>, s: Seq<u8>) -> bool {
    &&& raw.len() <= MAX_STR
    &&& h ==> hdec(raw, 0) == Some(s)
    &&& !h ==> raw == s
}

pub proof fn lemma_str_dec(b: Seq<u8>, pos: int, h: bool, raw: Seq<u8>, s: Seq<u8>)
    requires
        str_ok(h, raw, s),
        0 <= pos,
        pos + str_enc(h, raw).len() <= b.len(),
        b.subrange(pos, pos + str_enc(h, raw).len()) == str_enc(h, raw),
    ensures
        str_dec(b, pos) == StrR::Ok(s, pos + str_enc(h, raw).len()),
{
    let f: nat = if h { 128 } else { 0 };
    let iw = int_enc(f, 7, raw.len());
    let w = str_enc(h, raw);
    lemma_int_enc(f, 7, raw.len());
    assert(b.subrange(pos, pos + iw.len()) =~= w.subrange(0, iw.len() as int));
    assert(w.subrange(0, iw.len() as int) =~= iw);
    lemma_int_dec(b, pos, f, 7, raw.len());
    let e = pos + iw.len();
    assert(b.subrange(e, e + raw.len()) =~= w.subrange(iw.len() as int, w.len() as int));
    assert(w.subrange(iw.len() as int, w.len() as int) =~= raw);
}

/// Appends `s` as a string literal, Huffman-coded when that is shorter.
/// The result is the H bit and the bytes after the length.
#[inline]
pub fn put_str(out: &mut Vec<u8>, s: &[u8]) -> (r: Ghost<(bool, Seq<u8>)>)
    requires
        enc_ok(),
        s@.len() <= MAX_STR,
    ensures
        final(out)@ == old(out)@ + str_enc(r@.0, r@.1),
        str_ok(r@.0, r@.1, s@),
{
    let n = s.len();
    if n < 127 {
        // One pass: Huffman-code it after a placeholder for the length,
        // which then fits in one byte; if that is not shorter, replace it
        // with the plain string.
        let m = out.len();
        out.push(0);
        let ghost o1 = out@;
        hencode::encode(s, out);
        let hl = out.len() - m - 1;
        let ghost raw = out@.subrange(o1.len() as int, out@.len() as int);
        proof {
            assert(out@ =~= o1 + raw);
        }
        if hl < n {
            out.set(m, 0x80 + hl as u8);
            proof {
                assert(int_enc(128, 7, hl as nat) == seq![(0x80 + hl) as u8]);
                assert(final(out)@ =~= old(out)@ + str_enc(true, raw));
            }
            return Ghost((true, raw));
        }
        out.truncate(m);
        proof {
            assert(out@ =~= old(out)@);
        }
        put_int(out, 0, 7, n as u32);
        verilith_core::prims::extend(out, s);
        proof {
            assert(final(out)@ =~= old(out)@ + str_enc(false, s@));
        }
        return Ghost((false, s@));
    }
    let hl = hencode::encoded_len(s);
    if hl < s.len() {
        put_int(out, 0x80, 7, hl as u32);
        out.reserve(hl);
        let ghost o1 = out@;
        hencode::encode(s, out);
        let ghost raw = out@.subrange(o1.len() as int, out@.len() as int);
        proof {
            assert(out@ =~= o1 + raw);
            assert(final(out)@ =~= old(out)@ + str_enc(true, raw));
        }
        Ghost((true, raw))
    } else {
        put_int(out, 0, 7, s.len() as u32);
        verilith_core::prims::extend(out, s);
        proof {
            assert(final(out)@ =~= old(out)@ + str_enc(false, s@));
        }
        Ghost((false, s@))
    }
}

// ---------------------------------------------------------------------------
// Representations (§6)
// ---------------------------------------------------------------------------

/// The three literal forms: with incremental indexing (§6.2.1), without
/// indexing (§6.2.2), never indexed (§6.2.3).
pub const INCR: u8 = 0;

pub const NOIDX: u8 = 1;

pub const NEVER: u8 = 2;

pub open spec fn kflags(kind: u8) -> nat {
    if kind == INCR {
        0x40
    } else if kind == NOIDX {
        0
    } else {
        0x10
    }
}

pub open spec fn kbits(kind: u8) -> nat {
    if kind == INCR {
        6
    } else {
        4
    }
}

/// A literal field: the name as index `i` (0 for a new name, then given as
/// the literal `rawn`), and the value as the literal `rawv`.
pub open spec fn lit_enc(kind: u8, i: nat, hn: bool, rawn: Seq<u8>, hv: bool, rawv: Seq<u8>) -> Seq<u8> {
    int_enc(kflags(kind), kbits(kind), i) + (if i == 0 {
        str_enc(hn, rawn)
    } else {
        Seq::empty()
    }) + str_enc(hv, rawv)
}

/// The facts about a representation's first byte that `rep` tests.
proof fn lemma_byte(c: u8)
    ensures
        0x80 <= c ==> c & 0xE0 != 0x20,
        (0x40 <= c && c < 0x80) ==> (c & 0xE0 != 0x20 && c & 0x40 != 0 && c & 0xF0 != 0x10),
        c < 0x10 ==> (c & 0xE0 != 0x20 && c & 0x40 == 0 && c & 0xF0 != 0x10),
        (0x10 <= c && c < 0x20) ==> (c & 0xE0 != 0x20 && c & 0x40 == 0 && c & 0xF0 == 0x10),
        (0x20 <= c && c < 0x40) ==> c & 0xE0 == 0x20,
{
    assert(0x80 <= c ==> c & 0xE0 != 0x20) by (bit_vector);
    assert((0x40 <= c && c < 0x80) ==> (c & 0xE0 != 0x20 && c & 0x40 != 0 && c & 0xF0 != 0x10)) by (bit_vector);
    assert(c < 0x10 ==> (c & 0xE0 != 0x20 && c & 0x40 == 0 && c & 0xF0 != 0x10)) by (bit_vector);
    assert((0x10 <= c && c < 0x20) ==> (c & 0xE0 != 0x20 && c & 0x40 == 0 && c & 0xF0 == 0x10)) by (bit_vector);
    assert((0x20 <= c && c < 0x40) ==> c & 0xE0 == 0x20) by (bit_vector);
}

/// An indexed field (§6.1).
pub proof fn lemma_rep_idx(st: DState, i: nat)
    requires
        !st.expect,
        1 <= i <= st.table.len() + 61,
        i <= 0xFFFF_FFFF,
    ensures
        rep(st, int_enc(0x80, 7, i)) == Rep::Field(
            Field { name: entry(st.table, i).0, value: entry(st.table, i).1, never: false },
            after_field(st, st.table),
            int_enc(0x80, 7, i).len() as int,
        ),
{
    let w = int_enc(0x80, 7, i);
    lemma_int_enc(0x80, 7, i);
    assert(w.subrange(0, w.len() as int) =~= w);
    lemma_int_dec(w, 0, 0x80, 7, i);
    lemma_byte(w[0]);
}

/// A literal field (§6.2).
#[verifier::rlimit(60)]
pub proof fn lemma_rep_lit(
    st: DState,
    kind: u8,
    i: nat,
    hn: bool,
    rawn: Seq<u8>,
    name: Seq<u8>,
    hv: bool,
    rawv: Seq<u8>,
    value: Seq<u8>,
)
    requires
        !st.expect,
        kind <= 2,
        i <= 0xFFFF_FFFF,
        i == 0 ==> str_ok(hn, rawn, name),
        i != 0 ==> 1 <= i <= st.table.len() + 61 && entry(st.table, i).0 == name,
        str_ok(hv, rawv, value),
    ensures
        rep(st, lit_enc(kind, i, hn, rawn, hv, rawv)) == Rep::Field(
            Field { name, value, never: kind == NEVER },
            after_field(st, if kind == INCR { insert(st.table, st.max, (name, value)) } else { st.table }),
            lit_enc(kind, i, hn, rawn, hv, rawv).len() as int,
        ),
{
    let f = kflags(kind);
    let n = kbits(kind);
    let iw = int_enc(f, n, i);
    let nw: Seq<u8> = if i == 0 { str_enc(hn, rawn) } else { Seq::empty() };
    let vw = str_enc(hv, rawv);
    let w = lit_enc(kind, i, hn, rawn, hv, rawv);
    assert(w == iw + nw + vw);
    lemma_int_enc(f, n, i);
    assert(w.subrange(0, iw.len() as int) =~= iw);
    lemma_int_dec(w, 0, f, n, i);
    let c = w[0];
    lemma_byte(c);
    let e1 = iw.len() + nw.len();
    if i == 0 {
        assert(iw.len() == 1);
        assert(w.subrange(1, 1 + nw.len() as int) =~= nw);
        lemma_str_dec(w, 1, hn, rawn, name);
    }
    assert(w.subrange(e1 as int, (e1 + vw.len()) as int) =~= vw);
    lemma_str_dec(w, e1 as int, hv, rawv, value);
}

/// A dynamic table size update (§6.3).
pub proof fn lemma_rep_upd(st: DState, v: nat)
    requires
        st.at_start,
        v <= min(st.pending, st.settings),
        v <= 0xFFFF_FFFF,
    ensures
        rep(st, int_enc(0x20, 5, v)) == Rep::Update(
            DState { table: evict(st.table, 0, v), max: v, pending: NO_LIMIT as nat, expect: false, ..st },
            int_enc(0x20, 5, v).len() as int,
        ),
{
    let w = int_enc(0x20, 5, v);
    lemma_int_enc(0x20, 5, v);
    assert(w.subrange(0, w.len() as int) =~= w);
    lemma_int_dec(w, 0, 0x20, 5, v);
    lemma_byte(w[0]);
}

// ---------------------------------------------------------------------------
// Header blocks
// ---------------------------------------------------------------------------

/// Decoding `a` then `c` is decoding `a + c`.
pub proof fn lemma_block_append(st: DState, a: Seq<u8>, c: Seq<u8>)
    requires
        block(st, a) is Some,
    ensures
        block(st, a + c) == match block(block(st, a)->Some_0.1, c) {
            Some((gs, s2)) => Some((block(st, a)->Some_0.0 + gs, s2)),
            None => None::<(Seq<Field>, DState)>,
        },
    decreases a.len(),
{
    hide(rep);
    if a.len() == 0 {
        assert(a + c =~= c);
        match block(st, c) {
            Some((gs, s2)) => {
                assert(Seq::<Field>::empty() + gs =~= gs);
            },
            None => {},
        }
    } else {
        lemma_rep_ext(st, a, c);
        match rep(st, a) {
            Rep::Field(f, s2, e) => {
                assert((a + c).subrange(e, (a + c).len() as int) =~= a.subrange(e, a.len() as int) + c);
                lemma_block_append(s2, a.subrange(e, a.len() as int), c);
                let fs = block(s2, a.subrange(e, a.len() as int))->Some_0.0;
                match block(block(st, a)->Some_0.1, c) {
                    Some((gs, s3)) => {
                        assert(seq![f] + (fs + gs) =~= (seq![f] + fs) + gs);
                    },
                    None => {},
                }
            },
            Rep::Update(s2, e) => {
                assert((a + c).subrange(e, (a + c).len() as int) =~= a.subrange(e, a.len() as int) + c);
                lemma_block_append(s2, a.subrange(e, a.len() as int), c);
            },
            _ => {},
        }
    }
}

/// The empty block.
pub proof fn lemma_block_empty(st: DState)
    ensures
        block(st, Seq::<u8>::empty()) == Some((Seq::<Field>::empty(), st)),
{
}

/// A block of one field.
pub proof fn lemma_block_field(st: DState, w: Seq<u8>, f: Field, s2: DState)
    requires
        rep(st, w) == Rep::Field(f, s2, w.len() as int),
    ensures
        block(st, w) == Some((seq![f], s2)),
{
    assert(w.len() > 0);
    assert(w.subrange(w.len() as int, w.len() as int) =~= Seq::<u8>::empty());
    assert(block(s2, Seq::<u8>::empty()) == Some((Seq::<Field>::empty(), s2)));
    assert(seq![f] + Seq::<Field>::empty() =~= seq![f]);
}

/// A block of one size update.
pub proof fn lemma_block_update(st: DState, w: Seq<u8>, s2: DState)
    requires
        rep(st, w) == Rep::Update(s2, w.len() as int),
    ensures
        block(st, w) == Some((Seq::<Field>::empty(), s2)),
{
    assert(w.len() > 0);
    assert(w.subrange(w.len() as int, w.len() as int) =~= Seq::<u8>::empty());
    assert(block(s2, Seq::<u8>::empty()) == Some((Seq::<Field>::empty(), s2)));
}

} // verus!
