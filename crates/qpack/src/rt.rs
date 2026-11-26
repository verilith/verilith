//! The round trip: what the encoder writes, the decoder (the spec) reads
//! back. The encoder keeps, in ghost state, what each field line and
//! instruction it wrote is (`Item`, `str_ok`); these lemmas show the spec
//! decodes such bytes to exactly those fields and that table.
use crate::integer::*;
use crate::lemmas::*;
use crate::spec::*;
use verilith_hpack::spec::hdec;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// String literals
// ---------------------------------------------------------------------------

/// `x` is the `n`-bit prefix string literal of `s` under `flags`: Huffman
/// coded (`raw` decodes to `s`) or not (`raw` is `s`).
pub open spec fn str_ok(x: Seq<u8>, flags: nat, n: nat, s: Seq<u8>, huff: bool, raw: Seq<u8>) -> bool {
    let hf: nat = if huff { p2((n - 1) as nat) } else { 0 };
    &&& x == int_enc(flags + hf, (n - 1) as nat, raw.len()) + raw
    &&& raw.len() <= MAX_INT
    &&& if huff { hdec(raw, 0) == Some(s) } else { raw == s }
}

/// The powers of two used as prefix sizes.
pub proof fn lemma_p2_vals()
    ensures
        p2(0) == 1, p2(1) == 2, p2(2) == 4, p2(3) == 8, p2(4) == 16,
        p2(5) == 32, p2(6) == 64, p2(7) == 128, p2(8) == 256,
{
    assert(p2(2) == 4) by (compute);
    assert(p2(4) == 16) by (compute);
    assert(p2(6) == 64) by (compute);
    assert(p2(8) == 256) by (compute);
}

proof fn lemma_half_mod(flags: nat, q: nat, hf: nat)
    requires
        q > 0,
        flags % (2 * q) == 0,
        hf == 0 || hf == q,
    ensures
        (flags + hf) % q == 0,
{
    let k = flags / (2 * q);
    assert(flags == (2 * q) * k) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(flags as int, (2 * q) as int);
    }
    assert(flags + hf == q * (2 * k + hf / q)) by (nonlinear_arith)
        requires flags == (2 * q) * k, hf == 0 || hf == q, q > 0;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic((2 * k + hf / q) as int, q as int);
}

/// A string literal written at `b[pos]` decodes.
#[verifier::spinoff_prover]
pub proof fn lemma_str_at(b: Seq<u8>, pos: int, x: Seq<u8>, flags: nat, n: nat, s: Seq<u8>, huff: bool, raw: Seq<u8>, lim: nat)
    requires
        2 <= n <= 8,
        flags % p2(n) == 0,
        flags < 256,
        str_ok(x, flags, n, s, huff, raw),
        raw.len() <= lim,
        0 <= pos,
        pos + x.len() <= b.len(),
        b.subrange(pos, pos + x.len()) == x,
    ensures
        str_dec(b, pos, n, lim) == StrR::Ok(s, pos + x.len()),
        str_end(b, pos, n, lim) == EndR::Ok(pos + x.len()),
        flags <= b[pos] < flags + p2(n),
        x.len() >= 1,
{
    let m = (n - 1) as nat;
    let q = p2(m);
    let hf: nat = if huff { q } else { 0 };
    let fl = flags + hf;
    let ix = int_enc(fl, m, raw.len());
    assert(p2(n) == 2 * q);
    lemma_p2_vals();
    assert(q > 0);
    lemma_half_mod(flags, q, hf);
    lemma_flags(flags, n, hf);
    assert(x == ix + raw);
    assert(b.subrange(pos, pos + ix.len()) =~= ix) by {
        assert(b.subrange(pos, pos + ix.len()) =~= x.subrange(0, ix.len() as int));
        assert(x.subrange(0, ix.len() as int) =~= ix);
    }
    lemma_int_at(b, pos, fl, m, raw.len());
    lemma_int_first(fl, m, raw.len());
    let e = pos + ix.len();
    assert(b.subrange(e, e + raw.len()) =~= raw) by {
        assert(b.subrange(e, e + raw.len()) =~= x.subrange(ix.len() as int, x.len() as int));
        assert(x.subrange(ix.len() as int, x.len() as int) =~= raw);
    }
    let y: nat = (b[pos] as nat - fl) as nat;
    assert(y < q);
    assert(hf + y < p2(n));
    lemma_flags(flags, n, (hf + y) as nat);
    assert(b[pos] as nat == flags + (hf + y));
    assert(hbit(b[pos], n) == huff);
}

// ---------------------------------------------------------------------------
// Field lines
// ---------------------------------------------------------------------------

/// What an encoded field line is.
pub enum Kind {
    /// Indexed Field Line, static table entry `i`.
    IdxStatic(nat),
    /// Indexed Field Line, dynamic, absolute index below Base.
    IdxRel(nat),
    /// Indexed Field Line with Post-Base Index.
    IdxPost(nat),
    /// Literal Field Line with Name Reference to static entry `i`; the
    /// value literal, Huffman-coded or not, and its bytes.
    LitStatic(nat, bool, Seq<u8>),
    /// Literal Field Line with Literal Name: the name's and value's.
    LitLit(bool, Seq<u8>, bool, Seq<u8>),
}

/// An encoded field line: its bytes, the field, and how it is encoded.
pub struct Item {
    pub bytes: Seq<u8>,
    pub field: Field,
    pub kind: Kind,
}

/// The dynamic table entry an item refers to.
pub open spec fn iref(it: Item) -> Option<nat> {
    match it.kind {
        Kind::IdxRel(a) => Some(a),
        Kind::IdxPost(a) => Some(a),
        _ => None,
    }
}

pub open spec fn never_bits(never: bool, bit: nat) -> nat {
    if never { bit } else { 0 }
}

/// `it` is a correct encoding of its field, with Base `base`, given the
/// entries of `t`.
pub open spec fn item_ok(t: Table, base: nat, it: Item) -> bool {
    match it.kind {
        Kind::IdxStatic(i) => {
            &&& i < STATIC_LEN
            &&& it.bytes == int_enc(0xC0, 6, i)
            &&& it.field == Field { name: static_name(i as int), value: static_value(i as int), never: false }
        },
        Kind::IdxRel(a) => {
            &&& a < base
            &&& abs_ok(t, a)
            &&& it.bytes == int_enc(0x80, 6, (base - 1 - a) as nat)
            &&& it.field == Field { name: abs(t, a).0, value: abs(t, a).1, never: false }
        },
        Kind::IdxPost(a) => {
            &&& a >= base
            &&& abs_ok(t, a)
            &&& it.bytes == int_enc(0x10, 4, (a - base) as nat)
            &&& it.field == Field { name: abs(t, a).0, value: abs(t, a).1, never: false }
        },
        Kind::LitStatic(i, h, raw) => {
            let ix = int_enc(0x50 + never_bits(it.field.never, 0x20), 4, i);
            &&& i < STATIC_LEN
            &&& it.field.name == static_name(i as int)
            &&& it.bytes.len() >= ix.len()
            &&& it.bytes.subrange(0, ix.len() as int) == ix
            &&& str_ok(it.bytes.subrange(ix.len() as int, it.bytes.len() as int), 0, 8, it.field.value, h, raw)
        },
        Kind::LitLit(hn, rn, hv, rv) => {
            exists|k: int| 0 <= k <= it.bytes.len()
                && str_ok(#[trigger] it.bytes.subrange(0, k), 0x20 + never_bits(it.field.never, 0x10), 4, it.field.name, hn, rn)
                && str_ok(it.bytes.subrange(k, it.bytes.len() as int), 0, 8, it.field.value, hv, rv)
        },
    }
}

/// The table bounds the decoder works within.
pub open spec fn base_ok(t: Table, base: nat) -> bool {
    base <= icount(t) && icount(t) <= MAX_INT
}

/// The requirements for decoding an item at `b[pos]`.
pub open spec fn at_ok(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int, it: Item) -> bool {
    &&& item_ok(t, base, it)
    &&& base_ok(t, base)
    &&& ric <= icount(t)
    &&& (iref(it) matches Some(a) ==> a < ric)
    &&& 0 <= pos
    &&& pos + it.bytes.len() <= b.len()
    &&& b.subrange(pos, pos + it.bytes.len()) == it.bytes
}

#[verifier::spinoff_prover]
proof fn lemma_line_idx(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int, it: Item)
    requires
        at_ok(t, ric, base, b, pos, it),
        it.kind is IdxStatic || it.kind is IdxRel || it.kind is IdxPost,
    ensures
        line(t, ric, base, b, pos) == Some((it.field, pos + it.bytes.len())),
        it.bytes.len() >= 1,
{
    reveal(line);
    lemma_p2_vals();
    match it.kind {
        Kind::IdxStatic(i) => {
            lemma_int_at(b, pos, 0xC0, 6, i);
            lemma_int_first(0xC0, 6, i);
        },
        Kind::IdxRel(a) => {
            lemma_int_at(b, pos, 0x80, 6, (base - 1 - a) as nat);
            lemma_int_first(0x80, 6, (base - 1 - a) as nat);
        },
        Kind::IdxPost(a) => {
            lemma_int_at(b, pos, 0x10, 4, (a - base) as nat);
            lemma_int_first(0x10, 4, (a - base) as nat);
            assert((base + (a - base)) as int == a);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_line_lits(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int, it: Item, i: nat, h: bool, raw: Seq<u8>)
    requires
        at_ok(t, ric, base, b, pos, it),
        it.kind == Kind::LitStatic(i, h, raw),
    ensures
        line(t, ric, base, b, pos) == Some((it.field, pos + it.bytes.len())),
        it.bytes.len() >= 1,
{
    lemma_p2_vals();
    let lim = b.len() as nat;
    let fl = 0x50 + never_bits(it.field.never, 0x20);
    let ix = int_enc(fl, 4, i);
    assert(fl % p2(4) == 0);
    assert(b.subrange(pos, pos + ix.len()) =~= ix) by {
        assert(b.subrange(pos, pos + ix.len()) =~= it.bytes.subrange(0, ix.len() as int));
    }
    lemma_int_at(b, pos, fl, 4, i);
    lemma_int_first(fl, 4, i);
    let vx = it.bytes.subrange(ix.len() as int, it.bytes.len() as int);
    let e = pos + ix.len();
    assert(b.subrange(e, e + vx.len()) =~= vx) by {
        assert(b.subrange(e, e + vx.len()) =~= it.bytes.subrange(ix.len() as int, it.bytes.len() as int));
    }
    lemma_str_at(b, e, vx, 0, 8, it.field.value, h, raw, lim);
    let c = b[pos];
    assert(0x50 <= c < 0x80);
    assert(c / 32 == 2 || c / 32 == 3);
    reveal(line);
}

#[verifier::spinoff_prover]
proof fn lemma_line_litl(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int, it: Item, hn: bool, rn: Seq<u8>, hv: bool, rv: Seq<u8>)
    requires
        at_ok(t, ric, base, b, pos, it),
        it.kind == Kind::LitLit(hn, rn, hv, rv),
    ensures
        line(t, ric, base, b, pos) == Some((it.field, pos + it.bytes.len())),
        it.bytes.len() >= 1,
{
    lemma_p2_vals();
    let lim = b.len() as nat;
    let fl = 0x20 + never_bits(it.field.never, 0x10);
    let k = choose|k: int| 0 <= k <= it.bytes.len()
        && str_ok(#[trigger] it.bytes.subrange(0, k), fl, 4, it.field.name, hn, rn)
        && str_ok(it.bytes.subrange(k, it.bytes.len() as int), 0, 8, it.field.value, hv, rv);
    let nx = it.bytes.subrange(0, k);
    let vx = it.bytes.subrange(k, it.bytes.len() as int);
    assert(b.subrange(pos, pos + nx.len()) =~= nx);
    assert(b.subrange(pos + k, pos + k + vx.len()) =~= vx);
    assert(fl % p2(4) == 0);
    assert(nx.len() <= lim && vx.len() <= lim);
    lemma_str_at(b, pos, nx, fl, 4, it.field.name, hn, rn, lim);
    lemma_str_at(b, pos + k, vx, 0, 8, it.field.value, hv, rv, lim);
    reveal(line);
}

/// An item written at `b[pos]` decodes to its field.
pub proof fn lemma_line_item(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int, it: Item)
    requires
        at_ok(t, ric, base, b, pos, it),
    ensures
        line(t, ric, base, b, pos) == Some((it.field, pos + it.bytes.len())),
        it.bytes.len() >= 1,
{
    match it.kind {
        Kind::LitStatic(i, h, raw) => lemma_line_lits(t, ric, base, b, pos, it, i, h, raw),
        Kind::LitLit(hn, rn, hv, rv) => lemma_line_litl(t, ric, base, b, pos, it, hn, rn, hv, rv),
        _ => lemma_line_idx(t, ric, base, b, pos, it),
    }
}

} // verus!
