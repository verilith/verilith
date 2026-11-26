//! The round trip: what the encoder writes, the decoder (the spec) reads
//! back. The encoder keeps, in ghost state, what each field line and
//! instruction it wrote is (`Item`, `str_ok`); these lemmas show the spec
//! decodes such bytes to exactly those fields and that table.
use crate::integer::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::table::lemma_evict;
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

// ---------------------------------------------------------------------------
// Field sections
// ---------------------------------------------------------------------------

/// The items' bytes, one after another.
pub open spec fn cat(its: Seq<Item>) -> Seq<u8>
    decreases its.len(),
{
    if its.len() == 0 { Seq::empty() } else { its[0].bytes + cat(its.drop_first()) }
}

/// The items' fields.
pub open spec fn flds(its: Seq<Item>) -> Seq<Field> {
    Seq::new(its.len(), |i: int| its[i].field)
}

/// The sum of the items' field sizes.
pub open spec fn fsum(its: Seq<Item>) -> nat
    decreases its.len(),
{
    if its.len() == 0 { 0 } else { fsize(its[0].field) + fsum(its.drop_first()) }
}

/// Every item is a correct encoding, referring only to entries below `ric`.
pub open spec fn items_ok(t: Table, ric: nat, base: nat, its: Seq<Item>) -> bool {
    forall|i: int| 0 <= i < its.len() ==> {
        &&& item_ok(t, base, #[trigger] its[i])
        &&& (iref(its[i]) matches Some(a) ==> a < ric)
    }
}

pub proof fn lemma_cat_push(its: Seq<Item>, x: Item)
    ensures
        cat(its.push(x)) == cat(its) + x.bytes,
        fsum(its.push(x)) == fsum(its) + fsize(x.field),
    decreases its.len(),
{
    if its.len() == 0 {
        let y = its.push(x);
        assert(y.drop_first() =~= Seq::<Item>::empty());
        assert(cat(y.drop_first()) == Seq::<u8>::empty());
        assert(fsum(y.drop_first()) == 0);
        assert(y[0] == x);
        assert(cat(y) =~= x.bytes);
    } else {
        assert(its.push(x).drop_first() =~= its.drop_first().push(x));
        lemma_cat_push(its.drop_first(), x);
        assert(its.push(x)[0] == its[0]);
        assert(fsum(its.push(x)) == fsize(its[0].field) + fsum(its.drop_first().push(x)));
        assert(cat(its.push(x)) =~= cat(its) + x.bytes);
    }
}

/// Field lines written one after another, to the end of `b`, decode to
/// their fields.
pub proof fn lemma_lines_items(t: Table, ric: nat, base: nat, max_size: nat, b: Seq<u8>, pos: int, size: nat, acc: Seq<Field>, its: Seq<Item>)
    requires
        items_ok(t, ric, base, its),
        base_ok(t, base),
        ric <= icount(t),
        0 <= pos <= b.len(),
        b.subrange(pos, b.len() as int) == cat(its),
        size + fsum(its) <= max_size,
    ensures
        lines(t, ric, base, max_size, b, pos, size, acc) == SecR::Ok(acc + flds(its), ric),
    decreases its.len(),
{
    if its.len() == 0 {
        assert(acc + flds(its) =~= acc);
    } else {
        let x = its[0];
        let rest = its.drop_first();
        let c = cat(its);
        assert(c == x.bytes + cat(rest));
        assert(b.subrange(pos, pos + x.bytes.len()) =~= x.bytes) by {
            assert(b.subrange(pos, pos + x.bytes.len()) =~= c.subrange(0, x.bytes.len() as int));
        }
        assert(item_ok(t, base, its[0]));
        lemma_line_item(t, ric, base, b, pos, x);
        let e = pos + x.bytes.len();
        assert(b.subrange(e, b.len() as int) =~= cat(rest)) by {
            assert(b.subrange(e, b.len() as int) =~= c.subrange(x.bytes.len() as int, c.len() as int));
        }
        assert(items_ok(t, ric, base, rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies item_ok(t, base, #[trigger] rest[i]) && (iref(rest[i]) matches Some(a) ==> a < ric) by {
                assert(rest[i] == its[i + 1]);
            }
        }
        lemma_lines_items(t, ric, base, max_size, b, e, size + fsize(x.field), acc.push(x.field), rest);
        assert(acc.push(x.field) + flds(rest) =~= acc + flds(its));
    }
}

/// The Required Insert Count's encoding decodes back (§4.5.1.1), at an
/// Insert Count `total` no more than MaxEntries past it.
pub proof fn lemma_ric_rt(ric: nat, max_cap: nat, total: nat)
    requires
        ric <= total,
        ric == 0 || (max_entries(max_cap) > 0 && total < ric + max_entries(max_cap)),
    ensures
        decode_ric(encode_ric(ric, max_cap), max_cap, total) == Some(ric),
        encode_ric(ric, max_cap) <= 2 * max_entries(max_cap),
{
    if ric > 0 {
        let me = max_entries(max_cap);
        let full = 2 * me;
        let mv = total + me;
        let q1 = ric / full;
        let r = ric % full;
        let w = mv / full;
        let rm = mv % full;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ric as int, full as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(mv as int, full as int);
        assert(0 <= r < full && 0 <= rm < full);
        assert(q1 == w || q1 + 1 == w) by (nonlinear_arith)
            requires
                ric == full * q1 + r, mv == full * w + rm,
                0 <= r < full, 0 <= rm < full,
                mv < ric + full, ric <= mv, full > 0;
        let mw = w * full;
        vstd::arithmetic::mul::lemma_mul_is_commutative(w as int, full as int);
        let comp = mw + r;
        if q1 == w {
            assert(comp == ric);
        } else {
            assert(full * w == full * q1 + full) by (nonlinear_arith) requires q1 + 1 == w;
            assert(comp == ric + full);
            assert(r > rm);
            assert(comp > mv);
        }
    }
}

/// A field section as the encoder writes it: the prefix (Required Insert
/// Count, Base), then the items.
pub open spec fn sec_bytes(ric: nat, base: nat, max_cap: nat, its: Seq<Item>) -> Seq<u8> {
    let pre = if base >= ric {
        int_enc(0, 7, (base - ric) as nat)
    } else {
        int_enc(0x80, 7, (ric - base - 1) as nat)
    };
    int_enc(0, 8, encode_ric(ric, max_cap)) + pre + cat(its)
}

/// The round trip for a field section: decoded with the table the encoder
/// had, it gives back the fields.
pub proof fn lemma_section_rt(t: Table, max_cap: nat, max_size: nat, ric: nat, base: nat, its: Seq<Item>)
    requires
        items_ok(t, ric, base, its),
        base_ok(t, base),
        ric <= icount(t),
        ric == 0 || (max_entries(max_cap) > 0 && icount(t) < ric + max_entries(max_cap)),
        ric > 0 || base == 0,
        fsum(its) <= max_size,
        max_cap <= MAX_INT,
    ensures
        section(t, max_cap, max_size, sec_bytes(ric, base, max_cap, its)) == SecR::Ok(flds(its), ric),
{
    lemma_p2_vals();
    let b = sec_bytes(ric, base, max_cap, its);
    let enc = encode_ric(ric, max_cap);
    lemma_ric_rt(ric, max_cap, icount(t));
    let x1 = int_enc(0, 8, enc);
    let sign = base < ric;
    let fl: nat = if sign { 0x80 } else { 0 };
    let dv: nat = if sign { (ric - base - 1) as nat } else { (base - ric) as nat };
    let x2 = int_enc(fl, 7, dv);
    assert(b == x1 + x2 + cat(its));
    assert(enc <= MAX_INT) by {
        assert(max_entries(max_cap) * 32 <= max_cap) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(max_cap as int, 32);
        }
    }
    assert(b.subrange(0, x1.len() as int) =~= x1);
    lemma_int_at(b, 0, 0, 8, enc);
    let e1 = x1.len() as int;
    assert(b.subrange(e1, e1 + x2.len()) =~= x2);
    assert(dv <= MAX_INT);
    lemma_int_at(b, e1, fl, 7, dv);
    lemma_int_first(fl, 7, dv);
    assert((b[e1] >= 0x80) == sign);
    let e2 = e1 + x2.len();
    assert(b.subrange(e2, b.len() as int) =~= cat(its));
    let base2: nat = if sign { (ric - dv - 1) as nat } else { ric + dv };
    assert(base2 == base);
    lemma_lines_items(t, ric, base, max_size, b, e2, 0, Seq::empty(), its);
    assert(Seq::<Field>::empty() + flds(its) =~= flds(its));
}

// ---------------------------------------------------------------------------
// Encoder instructions
// ---------------------------------------------------------------------------

/// What an encoder instruction is.
pub enum IKind {
    /// Set Dynamic Table Capacity.
    SetCap(nat),
    /// Insert with Name Reference to static entry `i`; the value literal.
    InsStatic(nat, bool, Seq<u8>),
    /// Insert with Literal Name: the name's and value's literals.
    InsLit(bool, Seq<u8>, bool, Seq<u8>),
    /// Duplicate, by relative index.
    Dup(nat),
}

/// An encoder instruction: its bytes, how it is encoded, and (for an
/// insert) the entry it adds.
pub struct Ins {
    pub bytes: Seq<u8>,
    pub kind: IKind,
    pub entry: Entry,
}

/// `x` is a correct encoding, in table `t` under the decoder's maximum
/// capacity `mc`.
pub open spec fn ins_ok(t: Table, mc: nat, x: Ins) -> bool {
    let lim = str_limit(mc);
    match x.kind {
        IKind::SetCap(c) => {
            &&& c <= mc
            &&& c <= MAX_INT
            &&& x.bytes == int_enc(0x20, 5, c)
        },
        IKind::InsStatic(i, h, raw) => {
            let ix = int_enc(0xC0, 6, i);
            &&& i < STATIC_LEN
            &&& x.entry.0 == static_name(i as int)
            &&& raw.len() <= lim
            &&& x.bytes.len() >= ix.len()
            &&& x.bytes.subrange(0, ix.len() as int) == ix
            &&& str_ok(x.bytes.subrange(ix.len() as int, x.bytes.len() as int), 0, 8, x.entry.1, h, raw)
        },
        IKind::InsLit(hn, rn, hv, rv) => {
            &&& rn.len() <= lim
            &&& rv.len() <= lim
            &&& exists|k: int| 0 <= k <= x.bytes.len()
                && str_ok(#[trigger] x.bytes.subrange(0, k), 0x40, 6, x.entry.0, hn, rn)
                && str_ok(x.bytes.subrange(k, x.bytes.len() as int), 0, 8, x.entry.1, hv, rv)
        },
        IKind::Dup(r) => {
            &&& rel_ok(t, r)
            &&& x.entry == rel(t, r)
            &&& r <= MAX_INT
            &&& x.bytes == int_enc(0, 5, r)
        },
    }
}

/// The table after `x`.
pub open spec fn ins_apply(t: Table, x: Ins) -> Option<Table> {
    match x.kind {
        IKind::SetCap(c) => Some(set_cap(t, c)),
        _ => insert(t, x.entry),
    }
}

#[verifier::spinoff_prover]
proof fn lemma_einst_ins_static(t: Table, mc: nat, x: Ins, i: nat, h: bool, raw: Seq<u8>)
    requires
        ins_ok(t, mc, x),
        x.kind == IKind::InsStatic(i, h, raw),
    ensures
        eframe(x.bytes, mc) == EndR::Ok(x.bytes.len() as int),
        einst(t, mc, x.bytes) == ins_apply(t, x),
{
    lemma_p2_vals();
    let b = x.bytes;
    let lim = str_limit(mc);
    let ix = int_enc(0xC0, 6, i);
    assert(b.subrange(0, ix.len() as int) =~= ix);
    lemma_int_at(b, 0, 0xC0, 6, i);
    lemma_int_first(0xC0, 6, i);
    let vx = b.subrange(ix.len() as int, b.len() as int);
    let e = ix.len() as int;
    assert(b.subrange(e, e + vx.len()) =~= vx);
    lemma_str_at(b, e, vx, 0, 8, x.entry.1, h, raw, lim);
    assert(x.entry == (static_name(i as int), x.entry.1));
    reveal(eframe);
    reveal(einst);
}

#[verifier::spinoff_prover]
proof fn lemma_einst_ins_lit(t: Table, mc: nat, x: Ins, hn: bool, rn: Seq<u8>, hv: bool, rv: Seq<u8>)
    requires
        ins_ok(t, mc, x),
        x.kind == IKind::InsLit(hn, rn, hv, rv),
    ensures
        eframe(x.bytes, mc) == EndR::Ok(x.bytes.len() as int),
        einst(t, mc, x.bytes) == ins_apply(t, x),
{
    lemma_p2_vals();
    let b = x.bytes;
    let lim = str_limit(mc);
    let k = choose|k: int| 0 <= k <= b.len()
        && str_ok(#[trigger] b.subrange(0, k), 0x40, 6, x.entry.0, hn, rn)
        && str_ok(b.subrange(k, b.len() as int), 0, 8, x.entry.1, hv, rv);
    let nx = b.subrange(0, k);
    let vx = b.subrange(k, b.len() as int);
    assert(b.subrange(0, nx.len() as int) =~= nx);
    assert(b.subrange(k, k + vx.len()) =~= vx);
    lemma_str_at(b, 0, nx, 0x40, 6, x.entry.0, hn, rn, lim);
    lemma_str_at(b, k, vx, 0, 8, x.entry.1, hv, rv, lim);
    assert(x.entry == (x.entry.0, x.entry.1));
    reveal(eframe);
    reveal(einst);
}

#[verifier::spinoff_prover]
proof fn lemma_einst_small(t: Table, mc: nat, x: Ins)
    requires
        ins_ok(t, mc, x),
        x.kind is SetCap || x.kind is Dup,
    ensures
        eframe(x.bytes, mc) == EndR::Ok(x.bytes.len() as int),
        einst(t, mc, x.bytes) == ins_apply(t, x),
{
    lemma_p2_vals();
    let b = x.bytes;
    assert(b.subrange(0, b.len() as int) =~= b);
    match x.kind {
        IKind::SetCap(c) => {
            lemma_int_at(b, 0, 0x20, 5, c);
            lemma_int_first(0x20, 5, c);
        },
        IKind::Dup(r) => {
            lemma_int_at(b, 0, 0, 5, r);
            lemma_int_first(0, 5, r);
        },
        _ => {},
    }
    reveal(eframe);
    reveal(einst);
}

/// One whole instruction, on its own, is the encoder stream that applies it.
pub proof fn lemma_erun_ins(t: Table, mc: nat, x: Ins)
    requires
        ins_ok(t, mc, x),
        ins_apply(t, x) is Some,
    ensures
        erun(t, mc, x.bytes) == Run::Ok(ins_apply(t, x)->Some_0, x.bytes.len() as int),
{
    match x.kind {
        IKind::InsStatic(i, h, raw) => lemma_einst_ins_static(t, mc, x, i, h, raw),
        IKind::InsLit(hn, rn, hv, rv) => lemma_einst_ins_lit(t, mc, x, hn, rn, hv, rv),
        _ => lemma_einst_small(t, mc, x),
    }
    let b = x.bytes;
    assert(b.subrange(0, b.len() as int) =~= b);
    let r = b.subrange(b.len() as int, b.len() as int);
    assert(r =~= Seq::<u8>::empty());
    reveal(eframe);
    assert(eframe(r, mc) is Short);
    let t2 = ins_apply(t, x)->Some_0;
    assert(erun(t2, mc, r) == Run::Ok(t2, 0));
    reveal_with_fuel(erun, 2);
}

/// Encoder streams run one after another.
pub proof fn lemma_erun_cat(t: Table, mc: nat, a: Seq<u8>, c: Seq<u8>, t1: Table, t2: Table)
    requires
        erun(t, mc, a) == Run::Ok(t1, a.len() as int),
        erun(t1, mc, c) == Run::Ok(t2, c.len() as int),
    ensures
        erun(t, mc, a + c) == Run::Ok(t2, (a.len() + c.len()) as int),
{
    lemma_erun_split(t, mc, a, c);
    assert(a.subrange(a.len() as int, a.len() as int) + c =~= c);
}

// ---------------------------------------------------------------------------
// Entries stay put
// ---------------------------------------------------------------------------

/// Evicting, inserting or setting the capacity keeps every entry from
/// `t2.dropped` on where it was.
pub open spec fn keeps(t: Table, t2: Table) -> bool {
    &&& t2.dropped >= t.dropped
    &&& icount(t2) >= icount(t)
    &&& forall|a: nat| t2.dropped <= a < icount(t) ==> #[trigger] abs(t2, a) == abs(t, a)
}

pub proof fn lemma_keeps_apply(t: Table, x: Ins)
    requires
        ins_apply(t, x) is Some,
    ensures
        keeps(t, ins_apply(t, x)->Some_0),
        icount(ins_apply(t, x)->Some_0) == icount(t) + (if x.kind is SetCap { 0nat } else { 1nat }),
        x.kind !is SetCap ==> abs(ins_apply(t, x)->Some_0, icount(t)) == x.entry,
{
    match x.kind {
        IKind::SetCap(c) => {
            lemma_evict(t, 0, c);
            let t2 = set_cap(t, c);
            assert forall|a: nat| t2.dropped <= a < icount(t) implies #[trigger] abs(t2, a) == abs(t, a) by {
                assert(t2.ents[a - t2.dropped] == t.ents[(t2.dropped - t.dropped) + (a - t2.dropped)]);
            }
        },
        _ => {
            lemma_evict(t, esize(x.entry), t.cap);
            let t1 = evict(t, esize(x.entry), t.cap);
            let t2 = ins_apply(t, x)->Some_0;
            assert(t2.ents == t1.ents.push(x.entry));
            assert forall|a: nat| t2.dropped <= a < icount(t) implies #[trigger] abs(t2, a) == abs(t, a) by {
                assert(t2.ents[a - t2.dropped] == t1.ents[a - t1.dropped]);
                assert(t1.ents[a - t1.dropped] == t.ents[(t1.dropped - t.dropped) + (a - t1.dropped)]);
            }
            assert(abs(t2, icount(t)) == t2.ents[t1.ents.len() as int]);
        },
    }
}

pub proof fn lemma_keeps_trans(t: Table, t2: Table, t3: Table)
    requires
        keeps(t, t2),
        keeps(t2, t3),
    ensures
        keeps(t, t3),
{
    assert forall|a: nat| t3.dropped <= a < icount(t) implies #[trigger] abs(t3, a) == abs(t, a) by {
        assert(abs(t3, a) == abs(t2, a));
    }
}

/// An item stays correct while the entry it refers to stays.
pub proof fn lemma_item_keeps(t: Table, t2: Table, base: nat, it: Item)
    requires
        item_ok(t, base, it),
        keeps(t, t2),
        iref(it) matches Some(a) ==> t2.dropped <= a,
    ensures
        item_ok(t2, base, it),
{
    match it.kind {
        Kind::IdxRel(a) => { assert(abs(t2, a) == abs(t, a)); },
        Kind::IdxPost(a) => { assert(abs(t2, a) == abs(t, a)); },
        _ => {},
    }
}

} // verus!
