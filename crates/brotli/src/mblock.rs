//! Compressed meta-blocks: from a list of commands (insert lengths, copy
//! lengths and distances) to the bits, with the spec state carried along.
use crate::bitwriter::*;
use crate::spec::{INS_BASE, INS_EXTRA, CPY_BASE, CPY_EXTRA, St};
#[cfg(verus_only)]
use crate::cmeta::*;
#[cfg(verus_only)]
use crate::elemmas::*;
#[cfg(verus_only)]
use crate::pcode::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Length and distance codes
// ---------------------------------------------------------------------------

/// `1 << k`, for `k` up to 32.
#[inline(always)]
pub fn shl1(k: u32) -> (r: u64)
    requires
        k <= 32,
    ensures
        r as nat == pow2(k as nat),
        1 <= r <= 0x1_0000_0000,
{
    proof {
        lemma_pow2_pos(k as nat);
        if k < 32 {
            lemma_pow2_strictly_increases(k as nat, 32);
        }
        lemma2_to64();
        vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
        vstd::bits::lemma_u64_shl_is_mul(1, k as u64);
    }
    1u64 << (k as u64)
}

pub proof fn lemma_tables_small()
    ensures
        forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594,
        forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118,
{
    assert(forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594) by (compute);
    assert(forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118) by (compute);
}

pub proof fn lemma_shl1_24()
    ensures
        forall|k: nat| k <= 24 ==> #[trigger] pow2(k) <= 0x100_0000,
{
    assert forall|k: nat| k <= 24 implies #[trigger] pow2(k) <= 0x100_0000 by {
        if k < 24 {
            lemma_pow2_strictly_increases(k, 24);
        }
        lemma2_to64();
    }
}

/// `floor(log2 x)` for `x >= 1`.
#[inline(always)]
fn log2u(x: u32) -> (r: u32)
    requires
        x >= 1,
    ensures
        r < 32,
{
    let b = crate::pcode::bitlen_exec(x);
    proof {
        if b == 0 {
            reveal_with_fuel(bitlen, 1);
        }
        crate::pcode::lemma_bitlen_bound(x as nat);
    }
    if b == 0 { 0 } else if b > 32 { 31 } else { b - 1 }
}

/// The insert length code for `ilen` (google/brotli's `GetInsertLengthCode`,
/// checked against the table).
pub fn ins_code_of(ilen: u32) -> (r: Option<usize>)
    ensures
        r matches Some(ic) ==> ic < 24 && INS_BASE[ic as int] <= ilen < INS_BASE[ic as int] + pow2(INS_EXTRA[ic as int] as nat),
{
    proof {
        lemma_tables_small();
        lemma_shl1_24();
    }
    let c: usize = if ilen < 6 {
        ilen as usize
    } else if ilen < 130 {
        let nb = log2u(ilen - 2);
        if nb == 0 || nb > 6 {
            0
        } else {
            let nb = nb - 1;
            (nb * 2 + (ilen - 2) / (shl1(nb) as u32) + 2) as usize
        }
    } else if ilen < 2114 {
        (log2u(ilen - 66) + 10) as usize
    } else if ilen < 6210 {
        21
    } else if ilen < 22594 {
        22
    } else {
        23
    };
    if c < 24 && INS_BASE[c] <= ilen && (ilen as u64) < INS_BASE[c] as u64 + shl1(INS_EXTRA[c] as u32) {
        return Some(c);
    }
    // The formula is the table's; this search is not expected to run.
    let mut i: usize = 0;
    while i < 24
        invariant
            i <= 24,
            forall|i: int| 0 <= i < 24 ==> #[trigger] INS_EXTRA[i] <= 24 && INS_BASE[i] <= 22594,
            forall|k: nat| k <= 24 ==> #[trigger] pow2(k) <= 0x100_0000,
        decreases 24 - i,
    {
        if INS_BASE[i] <= ilen && (ilen as u64) < INS_BASE[i] as u64 + shl1(INS_EXTRA[i] as u32) {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// The copy length code for `clen` (google/brotli's `GetCopyLengthCode`,
/// checked against the table).
pub fn cpy_code_of(clen: u32) -> (r: Option<usize>)
    ensures
        r matches Some(cc) ==> cc < 24 && CPY_BASE[cc as int] <= clen < CPY_BASE[cc as int] + pow2(CPY_EXTRA[cc as int] as nat),
{
    proof {
        lemma_tables_small();
        lemma_shl1_24();
    }
    if clen < 2 {
        return None;
    }
    let c: usize = if clen < 10 {
        (clen - 2) as usize
    } else if clen < 134 {
        let nb = log2u(clen - 6);
        if nb == 0 || nb > 6 {
            0
        } else {
            let nb = nb - 1;
            (nb * 2 + (clen - 6) / (shl1(nb) as u32) + 4) as usize
        }
    } else if clen < 2118 {
        (log2u(clen - 70) + 12) as usize
    } else {
        23
    };
    if c < 24 && CPY_BASE[c] <= clen && (clen as u64) < CPY_BASE[c] as u64 + shl1(CPY_EXTRA[c] as u32) {
        return Some(c);
    }
    let mut i: usize = 0;
    while i < 24
        invariant
            i <= 24,
            forall|i: int| 0 <= i < 24 ==> #[trigger] CPY_EXTRA[i] <= 24 && 2 <= CPY_BASE[i] <= 2118,
            forall|k: nat| k <= 24 ==> #[trigger] pow2(k) <= 0x100_0000,
        decreases 24 - i,
    {
        if CPY_BASE[i] <= clen && (clen as u64) < CPY_BASE[i] as u64 + shl1(CPY_EXTRA[i] as u32) {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// The cell for insert range `i` and copy range `c` (0 to 2 each).
pub open spec fn cell_of(i: int, c: int) -> int {
    if i == 0 {
        if c == 0 { 2 } else if c == 1 { 3 } else { 6 }
    } else if i == 1 {
        if c == 0 { 4 } else if c == 1 { 5 } else { 8 }
    } else {
        if c == 0 { 7 } else if c == 1 { 9 } else { 10 }
    }
}

/// The insert-and-copy symbol for codes `ic` and `cc`, in the cells that
/// reuse the last distance when `implicit`.
pub fn cmd_sym(ic: usize, cc: usize, implicit: bool) -> (r: u16)
    requires
        ic < 24,
        cc < 24,
        implicit ==> ic < 8 && cc < 16,
    ensures
        r < 704,
        ins_code(r as int) == ic,
        cpy_code(r as int) == cc,
        (r < 128) == implicit,
{
    let i = ic / 8;
    let c = cc / 8;
    let cell: usize = if implicit {
        c
    } else if i == 0 {
        if c == 0 { 2 } else if c == 1 { 3 } else { 6 }
    } else if i == 1 {
        if c == 0 { 4 } else if c == 1 { 5 } else { 8 }
    } else {
        if c == 0 { 7 } else if c == 1 { 9 } else { 10 }
    };
    let sym = cell * 64 + (ic % 8) * 8 + cc % 8;
    proof {
        let s = sym as int;
        assert(s / 64 == cell) by {
            lemma_fundamental_div_mod_converse(s, 64, cell as int, ((ic % 8) * 8 + cc % 8) as int);
        }
        assert((s / 8) % 8 == ic % 8) by {
            lemma_fundamental_div_mod_converse(s, 8, (cell * 8 + ic % 8) as int, (cc % 8) as int);
            lemma_fundamental_div_mod_converse((cell * 8 + ic % 8) as int, 8, cell as int, (ic % 8) as int);
        }
        assert(s % 8 == cc % 8) by {
            lemma_fundamental_div_mod_converse(s, 8, (cell * 8 + ic % 8) as int, (cc % 8) as int);
        }
        assert(CELL[0] == 0 && CELL[1] == 1 && CELL[2] == 0 && CELL[3] == 1 && CELL[4] == 8 && CELL[5] == 9
            && CELL[6] == 2 && CELL[7] == 16 && CELL[8] == 10 && CELL[9] == 17 && CELL[10] == 18);
    }
    sym as u16
}

pub proof fn lemma_bitlen_lower(x: nat)
    requires
        x >= 1,
    ensures
        bitlen(x) >= 1,
        pow2((bitlen(x) - 1) as nat) <= x,
    decreases x,
{
    if x == 1 {
        reveal_with_fuel(bitlen, 2);
        lemma2_to64();
    } else {
        lemma_bitlen_lower(x / 2);
        lemma_pow2_unfold((bitlen(x) - 1) as nat);
    }
}

/// The distance code (16 and up) and extra bits for distance `d`, with
/// `NPOSTFIX = NDIRECT = 0` (google/brotli's `PrefixEncodeCopyDistance`).
pub fn dist_code(d: u32) -> (r: (u8, u32, u32))
    requires
        1 <= d < 0x100_0000,
    ensures
        16 <= r.0 < 64,
        r.2 == dext(r.0 as int),
        r.2 <= 24,
        (r.1 as nat) < pow2(r.2 as nat),
        dist_value(r.0 as int, r.1 as int, 0, 0) == d,
{
    let dd = d + 3;
    let bl = crate::pcode::bitlen_exec(dd);
    proof {
        lemma_bitlen_lower(dd as nat);
        crate::pcode::lemma_bitlen_bound(dd as nat);
        lemma_bitlen_mono(4, dd as nat);
        reveal_with_fuel(bitlen, 4);
        lemma_bitlen_mono(dd as nat, 0x100_0002);
        lemma_bitlen_25();
    }
    let nb = bl - 2;
    let q = dd >> nb;
    let ghost p = pow2(nb as nat);
    proof {
        vstd::bits::lemma_u32_shr_is_div(dd, nb);
        lemma_pow2_unfold((bl - 1) as nat);
        lemma_pow2_unfold(bl as nat);
        assert((bl - 1) as nat == nb + 1);
        lemma_pow2_unfold((nb + 1) as nat);
        assert(pow2((nb + 1) as nat) == 2 * p);
        assert(pow2(bl as nat) == 4 * p);
        assert(2 * p <= dd < 4 * p);
        lemma_pow2_pos(nb as nat);
        lemma_div_is_ordered((2 * p) as int, dd as int, p as int);
        lemma_div_by_multiple(2, p as int);
        assert(q >= 2);
        assert(q < 4) by {
            if q >= 4 {
                lemma_fundamental_div_mod(dd as int, p as int);
                assert(dd >= q * p) by (nonlinear_arith) requires dd == p * (dd as int / p as int) + dd as int % p as int, dd as int % p as int >= 0, q == dd as int / p as int;
                assert(q * p >= 4 * p) by (nonlinear_arith) requires q >= 4, p >= 1;
            }
        }
    }
    let h = q - 2;
    let base = (q as u64) << (nb as u64);
    proof {
        lemma_fundamental_div_mod(dd as int, p as int);
        assert(q * p <= dd);
        vstd::bits::lemma_u64_shl_is_mul(q as u64, nb as u64);
        assert(dd - q * p < p);
    }
    let extra = (dd as u64 - base) as u32;
    let x = 2 * (nb - 1) + h;
    let dcode = (16 + x) as u8;
    proof {
        let xi = x as int;
        assert(xi / 2 == nb - 1);
        assert(xi % 2 == h);
        lemma2_to64();
        assert(pow2(1) == 2);
        assert(pow2(0) == 1);
        assert(dist_extra(dcode as int, 0, 0) == nb);
        assert(dext(dcode as int) == nb);
        assert(xi / 1 == xi);
        assert(xi % 1 == 0);
        assert(dcode as int - 0 - 16 == xi);
        assert(pow2(dist_extra(dcode as int, 0, 0)) == p);
        assert((2 + h) * p == q * p);
        assert(dist_value(dcode as int, extra as int, 0, 0) == ((2 + xi % 2) * p - 4 + extra) * 1 + 0 + 0 + 1);
        assert(extra == dd - q * p);
    }
    (dcode, extra, nb)
}

proof fn lemma_bitlen_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        bitlen(x) <= bitlen(y),
    decreases y,
{
    if x > 0 {
        lemma_bitlen_mono(x / 2, y / 2);
    }
}

proof fn lemma_bitlen_25()
    ensures
        bitlen(0x100_0002) == 25,
{
    reveal_with_fuel(bitlen, 27);
}


// ---------------------------------------------------------------------------
// Commands, as the meta-block writer takes them
// ---------------------------------------------------------------------------

/// One command: `ins` literals, then `clen` bytes from `dist` back, with
/// the insert-and-copy symbol and distance code (and its extra bits) that
/// write it. A distance with `sym < 128` is implicitly the last one. The
/// last command of a meta-block may end after its literals.
pub struct Cmd {
    pub ins: u32,
    pub clen: u32,
    pub dist: u32,
    pub sym: u16,
    pub dcode: u8,
    pub extra: u32,
}

pub open spec fn zeros(n: nat) -> Seq<u8> {
    Seq::new(n, |i: int| 0u8)
}

pub open spec fn drs(a: [u32; 4]) -> Seq<int> {
    seq![a[0] as int, a[1] as int, a[2] as int, a[3] as int]
}

pub open spec fn lits_coded(l: Seq<u8>, data: Seq<u8>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> #[trigger] coded(l, data[k] as int)
}

/// The distance of command `x` with last distances `dr`.
pub open spec fn cdist(x: Cmd, dr: Seq<int>) -> int {
    if x.sym < 128 {
        dr[0]
    } else {
        dval(x.dcode as int, x.extra as int, dr)
    }
}

/// The last distances after the copy of `x`.
pub open spec fn cdr(x: Cmd, dr: Seq<int>) -> Seq<int> {
    if x.sym < 128 {
        dr
    } else {
        dnext(x.dcode as int, cdist(x, dr), dr)
    }
}

pub open spec fn matches(data: Seq<u8>, p: int, d: int, n: int) -> bool {
    forall|k: int| p <= k < p + n ==> #[trigger] data[k] == data[k - d]
}

/// Where the command starting at `q` ends.
pub open spec fn nq(q: int, x: Cmd, end: int) -> int {
    if q + x.ins == end {
        end
    } else {
        q + x.ins + x.clen
    }
}

pub open spec fn ndr(q: int, x: Cmd, end: int, dr: Seq<int>) -> Seq<int> {
    if q + x.ins == end {
        dr
    } else {
        cdr(x, dr)
    }
}

/// Command `x`, at `q` of a meta-block ending at `end`, writes the right
/// bytes with codes `l`, `c`, `d`.
pub open spec fn one_ok(data: Seq<u8>, q: int, end: int, x: Cmd, dr: Seq<int>, last: bool, wb: int, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> bool {
    let p = q + x.ins;
    &&& q < end
    &&& coded(c, x.sym as int)
    &&& sym_fits(x.sym as int, x.ins as int, x.clen as int)
    &&& p <= end
    &&& lits_coded(l, data, q, p)
    &&& if p == end {
        last
    } else {
        &&& (x.sym >= 128 ==> coded(d, x.dcode as int) && (x.extra as nat) < pow2(dext(x.dcode as int)))
        &&& cdist(x, dr) == x.dist
        &&& 1 <= x.dist <= max_distance(p, wb)
        &&& p + x.clen <= end
        &&& matches(data, p, x.dist as int, x.clen as int)
    }
}

/// The commands `cs`, from `q` with last distances `dr`, write
/// `data[q..end]` and leave the last distances `dro`.
pub open spec fn cmds_ok(data: Seq<u8>, q: int, end: int, cs: Seq<Cmd>, dr: Seq<int>, dro: Seq<int>, wb: int, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> bool
    decreases cs.len(),
{
    if cs.len() == 0 {
        q == end && dr == dro
    } else {
        &&& one_ok(data, q, end, cs[0], dr, cs.len() == 1, wb, l, c, d)
        &&& cmds_ok(data, nq(q, cs[0], end), end, cs.subrange(1, cs.len() as int), ndr(q, cs[0], end, dr), dro, wb, l, c, d)
    }
}

/// The state of a meta-block written with one tree per category.
pub open spec fn cstate(s: St, data: Seq<u8>, q: int, end: int, wb: int, dr: Seq<int>, l: Seq<u8>, c: Seq<u8>, d: Seq<u8>) -> bool {
    &&& s.out == data.subrange(0, q)
    &&& s.mrem == end - q
    &&& s.blen.len() == 3
    &&& s.blen[0] >= s.mrem
    &&& s.blen[1] >= s.mrem
    &&& s.blen[2] >= s.mrem
    &&& s.bt == seq![0int, 0, 0]
    &&& s.lit == seq![l]
    &&& s.cmd == seq![c]
    &&& s.dst == seq![d]
    &&& s.cmap == zeros(64)
    &&& s.dmap == zeros(4)
    &&& s.cmodes == seq![0u8]
    &&& s.npostfix == 0
    &&& s.ndirect == 0
    &&& s.wbits == wb
    &&& s.dr == dr
    &&& !s.last
}

// ---------------------------------------------------------------------------
// Literals with a single tree
// ---------------------------------------------------------------------------

/// The codes of `d`, one after the other.
pub open spec fn lb(l: Seq<u8>, d: Seq<u8>) -> Seq<nat>
    decreases d.len(),
{
    if d.len() == 0 {
        Seq::empty()
    } else {
        code_of(l, d[0] as int) + lb(l, d.subrange(1, d.len() as int))
    }
}

pub proof fn lemma_lb_push(l: Seq<u8>, d: Seq<u8>, x: u8)
    ensures
        lb(l, d.push(x)) == lb(l, d) + code_of(l, x as int),
    decreases d.len(),
{
    let dx = d.push(x);
    assert(dx[0] == if d.len() == 0 { x } else { d[0] });
    assert(lb(l, dx) == code_of(l, dx[0] as int) + lb(l, dx.subrange(1, dx.len() as int)));
    if d.len() == 0 {
        assert(dx.subrange(1, 1) =~= Seq::<u8>::empty());
        assert(lb(l, d) == Seq::<nat>::empty());
        assert(lb(l, Seq::<u8>::empty()) == Seq::<nat>::empty());
        assert(code_of(l, x as int) + Seq::<nat>::empty() =~= code_of(l, x as int));
        assert(Seq::<nat>::empty() + code_of(l, x as int) =~= code_of(l, x as int));
    } else {
        let r = d.subrange(1, d.len() as int);
        assert(d.push(x).subrange(1, d.len() as int + 1) =~= r.push(x));
        lemma_lb_push(l, r, x);
        assert(code_of(l, d[0] as int) + (lb(l, r) + code_of(l, x as int)) =~= (code_of(l, d[0] as int) + lb(l, r)) + code_of(l, x as int));
    }
}

pub proof fn lemma_ctx0(a: u8, b: u8)
    ensures
        0 <= lit_context(0, a, b) < 64,
{
    crate::decoder::lemma_lut();
    let x = CONTEXT_LUT[a as int];
    let y = CONTEXT_LUT[256 + b as int];
    assert(x < 64 && y < 64);
    assert((x | y) < 64) by (bit_vector)
        requires
            x < 64,
            y < 64,
    ;
}

#[verifier::spinoff_prover]
pub proof fn lemma_lits_single(m: LitM, out: Seq<u8>, d: Seq<u8>, l: Seq<u8>)
    requires
        m.cmap == zeros(64),
        m.bt0 == 0,
        m.mode == 0,
        m.lit == seq![l],
        forall|k: int| 0 <= k < d.len() ==> #[trigger] coded(l, d[k] as int),
    ensures
        lits_ok(m, out, d),
        lits_bits(m, out, d) == lb(l, d),
    decreases d.len(),
{
    hide(lit_context);
    if d.len() > 0 {
        lemma_ctx0(p1(out), p2(out));
        let r = d.subrange(1, d.len() as int);
        assert(lit_tree(m, out) == 0);
        assert(coded(l, d[0] as int));
        assert forall|k: int| 0 <= k < r.len() implies #[trigger] coded(l, r[k] as int) by {
            assert(r[k] == d[k + 1]);
        }
        lemma_lits_single(m, out.push(d[0]), r, l);
    }
}

} // verus!
