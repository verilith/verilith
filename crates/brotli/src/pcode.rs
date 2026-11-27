//! Prefix codes for the compressor: code lengths checked the way the spec
//! reads them, their canonical codes, and what the spec reads when a
//! symbol's code is written.
use crate::bitwriter::*;
use crate::spec::{CL_ORDER, St};
#[cfg(verus_only)]
use crate::elemmas::*;
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
        rsym(lens, b, w.len() as int) == R::Ok(s, (w.len() + code_of(lens, s).len()) as int),
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
        r matches Some(c) ==> c.ok() && c.lens@ == lens@,
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

// ---------------------------------------------------------------------------
// Reading a prefix code, without the bits (§3.4, §3.5)
// ---------------------------------------------------------------------------

/// Extra bits after code length symbol `c`.
pub open spec fn xb(c: int) -> nat {
    if c == 16 {
        2
    } else if c == 17 {
        3
    } else {
        0
    }
}

/// The lengths a repeat symbol adds (`pc_step`'s `d`).
pub open spec fn rep_d(pc: Pc, c: int, delta: int) -> int {
    let x = xb(c);
    let newlen = if c == 16 { pc.prev } else { 0 };
    let rep0 = if pc.replen != newlen { 0 } else { pc.rep };
    let rep1 = if rep0 > 0 { (rep0 - 2) * pow2(x) } else { 0 } + delta + 3;
    rep1 - rep0
}

/// `pc_step` after reading code length symbol `c` with extra bits
/// `delta`, when it does not fail.
pub open spec fn pc_tr(pc: Pc, c: int, delta: int) -> Pc {
    if c < 16 {
        Pc {
            lens: pc.lens.push(c as u8),
            rep: 0,
            prev: if c != 0 { c } else { pc.prev },
            space: if c != 0 { pc.space - pow2((15 - c) as nat) } else { pc.space },
            ..pc
        }
    } else {
        let x = xb(c);
        let newlen = if c == 16 { pc.prev } else { 0 };
        let rep0 = if pc.replen != newlen { 0 } else { pc.rep };
        let rep1 = if rep0 > 0 { (rep0 - 2) * pow2(x) } else { 0 } + delta + 3;
        let d = rep1 - rep0;
        Pc {
            lens: pc.lens + Seq::new(d as nat, |i: int| newlen as u8),
            rep: rep1,
            replen: newlen,
            space: if newlen != 0 { pc.space - d * pow2((15 - newlen) as nat) } else { pc.space },
            ..pc
        }
    }
}

/// Symbol `c` with extra bits `delta` can be read in state `pc`.
pub open spec fn pc_ok1(pc: Pc, c: int, delta: int, alpha: int) -> bool {
    &&& 0 <= c < 18
    &&& 0 <= delta < pow2(xb(c))
    &&& (c >= 16 ==> pc.lens.len() + rep_d(pc, c, delta) <= alpha)
}

/// Reading `its` from `pc` reads each, stops after the last, and ends with
/// the code space used up.
pub open spec fn items_valid(pc: Pc, its: Seq<(int, int)>, alpha: int) -> bool
    decreases its.len(),
{
    if its.len() == 0 {
        false
    } else {
        let p2 = pc_tr(pc, its[0].0, its[0].1);
        &&& pc_ok1(pc, its[0].0, its[0].1, alpha)
        &&& (its.len() == 1 ==> pc_done(p2, alpha) && p2.space == 0)
        &&& (its.len() > 1 ==> !pc_done(p2, alpha) && items_valid(p2, its.subrange(1, its.len() as int), alpha))
    }
}

pub open spec fn pc_run(pc: Pc, its: Seq<(int, int)>) -> Pc
    decreases its.len(),
{
    if its.len() == 0 {
        pc
    } else {
        pc_run(pc_tr(pc, its[0].0, its[0].1), its.subrange(1, its.len() as int))
    }
}

/// One item as written: its code length code, then its extra bits.
pub open spec fn item_bits(cl: Seq<u8>, it: (int, int)) -> Seq<nat> {
    code_of(cl, it.0) + fld(it.1 as nat, xb(it.0))
}

pub open spec fn items_bits(cl: Seq<u8>, its: Seq<(int, int)>) -> Seq<nat>
    decreases its.len(),
{
    if its.len() == 0 {
        Seq::empty()
    } else {
        item_bits(cl, its[0]) + items_bits(cl, its.subrange(1, its.len() as int))
    }
}

/// Every item's symbol has a code in `cl`.
pub open spec fn items_coded(cl: Seq<u8>, its: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < its.len() ==> {
        let c = #[trigger] its[i].0;
        &&& 0 <= c < cl.len()
        &&& 1 <= cl[c]
        &&& (used(cl) == 1 ==> first_used(cl, 0) == c)
    }
}

/// One code length symbol.
#[verifier::spinoff_prover]
pub proof fn lemma_pc_sym(b: Seq<u8>, w: Seq<nat>, pc: Pc, c: int, delta: int, alpha: int, rest: Seq<nat>)
    requires
        pc.started,
        lens_ok(pc.cl),
        0 <= c < pc.cl.len(),
        1 <= pc.cl[c],
        used(pc.cl) == 1 ==> first_used(pc.cl, 0) == c,
        pc_ok1(pc, c, delta, alpha),
        ext(b, w + (item_bits(pc.cl, (c, delta)) + rest)),
    ensures
        pc_step(b, w.len() as int, pc, alpha) == pc_next(pc_tr(pc, c, delta), alpha, (w.len() + item_bits(pc.cl, (c, delta)).len()) as int),
{
    let cd = code_of(pc.cl, c);
    let x = xb(c);
    let e = fld(delta as nat, x);
    lemma_bits_of(delta as nat, x);
    assert(w + (item_bits(pc.cl, (c, delta)) + rest) =~= w + (cd + (e + rest)));
    lemma_sym(b, w, pc.cl, c, e + rest);
    let p = w.len() + cd.len();
    assert(w + (cd + (e + rest)) =~= (w + cd) + (e + rest));
    lemma_rd(b, w + cd, delta as nat, x, rest);
    if c < 16 {
        lemma_pow2_small();
        assert(x == 0);
        assert(item_bits(pc.cl, (c, delta)).len() == cd.len());
    }
}

/// The phase that reads the code: `Trees(g)` with a code left to read.
pub open spec fn tree_phase(s: St, g: int, alpha: int) -> bool {
    &&& s.phase == Phase::Trees(g)
    &&& 0 <= g < 3
    &&& nread(s, g) < ntrees(s, g)
    &&& pc_alpha(s) == alpha
}

/// The state once a code has been read in `Trees(g)`.
pub open spec fn tree_fin(s: St, g: int, lens: Seq<u8>, p: int) -> St {
    let s1 = St { pos: p, pc: pc_init(), ..s };
    if g == 0 {
        St { lit: s.lit.push(lens), ..s1 }
    } else if g == 1 {
        St { cmd: s.cmd.push(lens), ..s1 }
    } else {
        St { dst: s.dst.push(lens), ..s1 }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_items_step(b: Seq<u8>, w: Seq<nat>, s: St, g: int, its: Seq<(int, int)>, alpha: int)
    requires
        tree_phase(s, g, alpha),
        s.pos == w.len(),
        s.pc.started,
        lens_ok(s.pc.cl),
        items_coded(s.pc.cl, its),
        items_valid(s.pc, its, alpha),
        ext(b, w + items_bits(s.pc.cl, its)),
    ensures
        ({
            let p2 = pc_tr(s.pc, its[0].0, its[0].1);
            let q = (w.len() + item_bits(s.pc.cl, its[0]).len()) as int;
            if its.len() == 1 {
                step(b, s) == Step::Next(tree_fin(s, g, pad_lens(p2.lens, alpha), q))
            } else {
                step(b, s) == Step::Next(St { pos: q, pc: p2, ..s })
            }
        }),
        items_bits(s.pc.cl, its) == item_bits(s.pc.cl, its[0]) + items_bits(s.pc.cl, its.subrange(1, its.len() as int)),
{
    let c = its[0].0;
    let d = its[0].1;
    assert(items_coded(s.pc.cl, its) ==> 1 <= s.pc.cl[its[0].0]);
    lemma_pc_sym(b, w, s.pc, c, d, alpha, items_bits(s.pc.cl, its.subrange(1, its.len() as int)));
    crate::decoder::lemma_step_trees(b, s, g);
}

/// The code length symbols of a complex code.
#[verifier::spinoff_prover]
pub proof fn lemma_items(w: Seq<nat>, s: St, g: int, its: Seq<(int, int)>, alpha: int)
    requires
        tree_phase(s, g, alpha),
        s.pos == w.len(),
        s.pc.started,
        lens_ok(s.pc.cl),
        items_coded(s.pc.cl, its),
        items_valid(s.pc, its, alpha),
    ensures
        moves(w, items_bits(s.pc.cl, its), s, tree_fin(s, g, pad_lens(pc_run(s.pc, its).lens, alpha), (w.len() + items_bits(s.pc.cl, its).len()) as int)),
    decreases its.len(),
{
    let cl = s.pc.cl;
    let p2 = pc_tr(s.pc, its[0].0, its[0].1);
    let x = item_bits(cl, its[0]);
    let r = its.subrange(1, its.len() as int);
    assert(items_bits(cl, its) == x + items_bits(cl, r));
    if its.len() == 1 {
        assert(r =~= Seq::<(int, int)>::empty());
        assert(pc_run(p2, r) == p2);
        let t = tree_fin(s, g, pad_lens(p2.lens, alpha), (w.len() + x.len()) as int);
        assert(x + items_bits(cl, r) =~= x);
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + items_bits(cl, its)) implies step(b, s) == Step::Next(t) by {
            lemma_items_step(b, w, s, g, its, alpha);
        }
        lemma_moves_step(w, items_bits(cl, its), s, t);
    } else {
        let s1 = St { pos: (w.len() + x.len()) as int, pc: p2, ..s };
        assert forall|b: Seq<u8>| #[trigger] ext(b, w + x) implies step(b, s) == Step::Next(s1) by {
            // Only the first item's bits are read.
            let its1 = its.subrange(0, 1);
            assert(items_bits(cl, its1.subrange(1, 1)) =~= Seq::<nat>::empty()) by {
                assert(its1.subrange(1, 1).len() == 0);
            }
            assert(items_bits(cl, its1) =~= x) by {
                assert(its1[0] == its[0]);
                assert(its1.subrange(1, its1.len() as int) =~= Seq::<(int, int)>::empty());
            }
            assert(items_valid(s.pc, its1, alpha) == false || true);
            lemma_pc_sym(b, w, s.pc, its[0].0, its[0].1, alpha, Seq::empty());
            assert(x + Seq::<nat>::empty() =~= x);
            crate::decoder::lemma_step_trees(b, s, g);
        }
        lemma_moves_step(w, x, s, s1);
        assert forall|i: int| 0 <= i < r.len() implies {
            let c = #[trigger] r[i].0;
            &&& 0 <= c < cl.len()
            &&& 1 <= cl[c]
            &&& (used(cl) == 1 ==> first_used(cl, 0) == c)
        } by {
            assert(r[i] == its[i + 1]);
        }
        lemma_items(w + x, s1, g, r, alpha);
        assert(w + x + items_bits(cl, r) =~= w + items_bits(cl, its));
        lemma_moves_trans(w, x, items_bits(cl, r), s, s1, tree_fin(s1, g, pad_lens(pc_run(p2, r).lens, alpha), ((w + x).len() + items_bits(cl, r).len()) as int));
        assert(tree_fin(s1, g, pad_lens(pc_run(p2, r).lens, alpha), ((w + x).len() + items_bits(cl, r).len()) as int)
            == tree_fin(s, g, pad_lens(pc_run(s.pc, its).lens, alpha), (w.len() + items_bits(cl, its).len()) as int));
    }
}

// ---------------------------------------------------------------------------
// Complex prefix codes: the code length code
// ---------------------------------------------------------------------------

/// One code length code length (0 to 5), in the fields `read_clcl` reads.
pub open spec fn clcl_code(v: int) -> Seq<nat> {
    if v == 0 {
        fld(0, 2)
    } else if v == 4 {
        fld(1, 2)
    } else if v == 3 {
        fld(2, 2)
    } else if v == 2 {
        fld(3, 2) + fld(0, 1)
    } else if v == 1 {
        fld(3, 2) + (fld(1, 1) + fld(0, 1))
    } else {
        fld(3, 2) + (fld(1, 1) + fld(1, 1))
    }
}

/// `read_cl` with the lengths taken from `t` instead of the bits: the
/// lengths read, their number, the code space left, and where it stops.
pub open spec fn rcl(t: Seq<u8>, i: int, cl: Seq<u8>, num: int, space: int) -> (Seq<u8>, int, int, int)
    decreases 18 - i,
{
    if i >= 18 || i < 0 {
        (cl, num, space, i)
    } else {
        let v = t[CL_ORDER[i] as int];
        let cl2 = cl.update(CL_ORDER[i] as int, v);
        if v != 0 {
            let space2 = space - pow2((5 - v) as nat);
            if space2 <= 0 {
                (cl2, num + 1, space2, i + 1)
            } else {
                rcl(t, i + 1, cl2, num + 1, space2)
            }
        } else {
            rcl(t, i + 1, cl2, num, space)
        }
    }
}

/// The code length code lengths `t[CL_ORDER[i]]` to `t[CL_ORDER[j - 1]]`.
pub open spec fn clcl_bits(t: Seq<u8>, i: int, j: int) -> Seq<nat>
    decreases j - i,
{
    if i >= j || i < 0 || i >= 18 {
        Seq::empty()
    } else {
        clcl_code(t[CL_ORDER[i] as int] as int) + clcl_bits(t, i + 1, j)
    }
}

#[verifier::spinoff_prover]
proof fn lemma_read_clcl(b: Seq<u8>, w: Seq<nat>, v: int, rest: Seq<nat>)
    requires
        0 <= v <= 5,
        ext(b, w + (clcl_code(v) + rest)),
    ensures
        read_clcl(b, w.len() as int) == R::Ok(v, (w.len() + clcl_code(v).len()) as int),
{
    lemma_pow2_small();
    lemma_bits_of(0, 2);
    lemma_bits_of(1, 2);
    lemma_bits_of(2, 2);
    lemma_bits_of(3, 2);
    lemma_bits_of(0, 1);
    lemma_bits_of(1, 1);
    let p = w.len() as int;
    if v == 0 || v == 4 || v == 3 {
        let a: nat = if v == 0 { 0 } else if v == 4 { 1 } else { 2 };
        lemma_rd(b, w, a, 2, rest);
    } else {
        let tail = if v == 2 { fld(0, 1) } else if v == 1 { fld(1, 1) + fld(0, 1) } else { fld(1, 1) + fld(1, 1) };
        assert(clcl_code(v) == fld(3, 2) + tail);
        assert(w + (clcl_code(v) + rest) =~= w + (fld(3, 2) + (tail + rest)));
        lemma_rd(b, w, 3, 2, tail + rest);
        let w1 = w + fld(3, 2);
        assert(w + (fld(3, 2) + (tail + rest)) =~= w1 + (tail + rest));
        if v == 2 {
            lemma_rd(b, w1, 0, 1, rest);
        } else {
            let c: nat = 1;
            let d: nat = if v == 1 { 0 } else { 1 };
            assert(w1 + (tail + rest) =~= w1 + (fld(1, 1) + (fld(d, 1) + rest)));
            lemma_rd(b, w1, 1, 1, fld(d, 1) + rest);
            let w2 = w1 + fld(1, 1);
            assert(w1 + (fld(1, 1) + (fld(d, 1) + rest)) =~= w2 + (fld(d, 1) + rest));
            lemma_rd(b, w2, d, 1, rest);
        }
    }
}

/// `read_cl` reads back what `rcl` describes.
#[verifier::spinoff_prover]
proof fn lemma_read_cl(b: Seq<u8>, w: Seq<nat>, t: Seq<u8>, i: int, cl: Seq<u8>, num: int, space: int, rest: Seq<nat>)
    requires
        0 <= i <= 18,
        t.len() == 18,
        forall|k: int| 0 <= k < 18 ==> #[trigger] t[k] <= 5,
        ext(b, w + (clcl_bits(t, i, rcl(t, i, cl, num, space).3) + rest)),
    ensures
        ({
            let r = rcl(t, i, cl, num, space);
            read_cl(b, w.len() as int, i, cl, num, space) == R::Ok((r.0, r.1, r.2), (w.len() + clcl_bits(t, i, r.3).len()) as int)
        }),
        i <= rcl(t, i, cl, num, space).3 <= 18,
    decreases 18 - i,
{
    let r = rcl(t, i, cl, num, space);
    if i < 18 {
        let v = t[CL_ORDER[i] as int] as int;
        assert(CL_ORDER[i] < 18) by {
            assert(forall|k: int| 0 <= k < 18 ==> #[trigger] CL_ORDER[k] < 18) by (compute);
        }
        let x = clcl_code(v);
        let cl2 = cl.update(CL_ORDER[i] as int, v as u8);
        let j = r.3;
        let space2 = space - pow2((5 - v) as nat);
        let stop = v != 0 && space2 <= 0;
        if stop {
            assert(j == i + 1);
            assert(clcl_bits(t, i + 1, j) =~= Seq::<nat>::empty());
            assert(clcl_bits(t, i, j) == x + clcl_bits(t, i + 1, j));
            assert(x + Seq::<nat>::empty() =~= x);
            lemma_read_clcl(b, w, v, rest);
        } else {
            let num2 = if v != 0 { num + 1 } else { num };
            let sp = if v != 0 { space2 } else { space };
            assert(r == rcl(t, i + 1, cl2, num2, sp));
            lemma_rcl_end(t, i + 1, cl2, num2, sp);
            assert(clcl_bits(t, i, j) == x + clcl_bits(t, i + 1, j));
            let y = clcl_bits(t, i + 1, j);
            assert(w + (x + y + rest) =~= w + (x + (y + rest)));
            lemma_read_clcl(b, w, v, y + rest);
            assert(w + (x + (y + rest)) =~= (w + x) + (y + rest));
            lemma_read_cl(b, w + x, t, i + 1, cl2, num2, sp, rest);
        }
    } else {
        assert(clcl_bits(t, i, r.3) =~= Seq::<nat>::empty());
    }
}

proof fn lemma_rcl_end(t: Seq<u8>, i: int, cl: Seq<u8>, num: int, space: int)
    requires
        0 <= i <= 18,
    ensures
        i <= rcl(t, i, cl, num, space).3 <= 18,
    decreases 18 - i,
{
    if i < 18 {
        let v = t[CL_ORDER[i] as int];
        let cl2 = cl.update(CL_ORDER[i] as int, v);
        if v != 0 {
            let space2 = space - pow2((5 - v) as nat);
            if space2 > 0 {
                lemma_rcl_end(t, i + 1, cl2, num + 1, space2);
            }
        } else {
            lemma_rcl_end(t, i + 1, cl2, num, space);
        }
    }
}

/// The code length code of a complex code, read as `rcl` says.
pub open spec fn cx_head(t: Seq<u8>, hskip: int) -> (Seq<u8>, int, int, int) {
    rcl(t, hskip, Seq::new(18, |i: int| 0u8), 0, 32)
}

pub open spec fn cx_head_bits(t: Seq<u8>, hskip: int) -> Seq<nat> {
    fld(hskip as nat, 2) + clcl_bits(t, hskip, cx_head(t, hskip).3)
}

/// The state once a complex code's code length code is read.
pub open spec fn cx_started(cl: Seq<u8>) -> Pc {
    Pc { started: true, cl, lens: Seq::empty(), prev: 8, rep: 0, replen: 0, space: 32768 }
}

/// The start of a complex code in `Trees(g)`.
#[verifier::spinoff_prover]
pub proof fn lemma_cx_head(w: Seq<nat>, s: St, g: int, alpha: int, t: Seq<u8>, hskip: int)
    requires
        tree_phase(s, g, alpha),
        s.pos == w.len(),
        s.pc == pc_init(),
        hskip == 0 || hskip == 2 || hskip == 3,
        t.len() == 18,
        forall|k: int| 0 <= k < 18 ==> #[trigger] t[k] <= 5,
        cx_head(t, hskip).1 == 1 || cx_head(t, hskip).2 == 0,
    ensures
        moves(w, cx_head_bits(t, hskip), s, St { pos: (w.len() + cx_head_bits(t, hskip).len()) as int, pc: cx_started(cx_head(t, hskip).0), ..s }),
{
    let u = cx_head_bits(t, hskip);
    let h = fld(hskip as nat, 2);
    let y = clcl_bits(t, hskip, cx_head(t, hskip).3);
    let t1 = St { pos: (w.len() + u.len()) as int, pc: cx_started(cx_head(t, hskip).0), ..s };
    lemma_pow2_small();
    lemma_bits_of(hskip as nat, 2);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t1) by {
        lemma_rd(b, w, hskip as nat, 2, y);
        assert(w + u =~= (w + h) + (y + Seq::<nat>::empty()));
        lemma_read_cl(b, w + h, t, hskip, Seq::new(18, |i: int| 0u8), 0, 32, Seq::empty());
        crate::decoder::lemma_step_trees(b, s, g);
    }
    lemma_moves_step(w, u, s, t1);
}

// ---------------------------------------------------------------------------
// Simple prefix codes
// ---------------------------------------------------------------------------

pub open spec fn syms_bits(syms: Seq<int>, n: nat) -> Seq<nat>
    decreases syms.len(),
{
    if syms.len() == 0 {
        Seq::empty()
    } else {
        fld(syms[0] as nat, n) + syms_bits(syms.subrange(1, syms.len() as int), n)
    }
}

#[verifier::spinoff_prover]
proof fn lemma_simple_syms(b: Seq<u8>, w: Seq<nat>, syms: Seq<int>, n: nat, alpha: int, rest: Seq<nat>)
    requires
        forall|i: int| 0 <= i < syms.len() ==> 0 <= #[trigger] syms[i] < alpha,
        alpha <= pow2(n),
        ext(b, w + (syms_bits(syms, n) + rest)),
    ensures
        read_simple_syms(b, w.len() as int, syms.len() as int, n, alpha) == R::Ok(syms, (w.len() + syms_bits(syms, n).len()) as int),
        syms_bits(syms, n).len() == n * syms.len(),
    decreases syms.len(),
{
    if syms.len() == 0 {
        assert(syms =~= Seq::<int>::empty());
    } else {
        let r = syms.subrange(1, syms.len() as int);
        let x = fld(syms[0] as nat, n);
        lemma_bits_of(syms[0] as nat, n);
        assert(w + (syms_bits(syms, n) + rest) =~= w + (x + (syms_bits(r, n) + rest)));
        lemma_rd(b, w, syms[0] as nat, n, syms_bits(r, n) + rest);
        assert(w + (x + (syms_bits(r, n) + rest)) =~= (w + x) + (syms_bits(r, n) + rest));
        assert forall|i: int| 0 <= i < r.len() implies 0 <= #[trigger] r[i] < alpha by {
            assert(r[i] == syms[i + 1]);
        }
        lemma_simple_syms(b, w + x, r, n, alpha, rest);
        assert(seq![syms[0]] + r =~= syms);
        assert((syms.len() - 1) as int == r.len());
        assert(n * syms.len() == n + n * r.len()) by (nonlinear_arith)
            requires syms.len() == r.len() + 1;
    }
}

/// The lengths a simple code gives its symbols.
pub open spec fn simple_ls(nsym: int, tsel: int) -> Seq<u8> {
    if nsym == 1 {
        seq![1u8]
    } else if nsym == 2 {
        seq![1u8, 1u8]
    } else if nsym == 3 {
        seq![1u8, 2u8, 2u8]
    } else if tsel == 0 {
        seq![2u8, 2u8, 2u8, 2u8]
    } else {
        seq![1u8, 2u8, 3u8, 3u8]
    }
}

pub open spec fn simple_bits(alpha: int, syms: Seq<int>, tsel: int) -> Seq<nat> {
    fld(1, 2) + (fld((syms.len() - 1) as nat, 2) + (syms_bits(syms, bitlen((alpha - 1) as nat)) + if syms.len() == 4 {
        fld(tsel as nat, 1)
    } else {
        Seq::empty()
    }))
}

pub open spec fn simple_ok(alpha: int, syms: Seq<int>, tsel: int) -> bool {
    &&& 1 <= syms.len() <= 4
    &&& 2 <= alpha
    &&& alpha <= pow2(bitlen((alpha - 1) as nat))
    &&& forall|i: int| 0 <= i < syms.len() ==> 0 <= #[trigger] syms[i] < alpha
    &&& distinct(syms)
    &&& 0 <= tsel <= 1
}

/// A simple code in `Trees(g)`.
#[verifier::spinoff_prover]
pub proof fn lemma_simple(w: Seq<nat>, s: St, g: int, alpha: int, syms: Seq<int>, tsel: int)
    requires
        tree_phase(s, g, alpha),
        s.pos == w.len(),
        s.pc == pc_init(),
        simple_ok(alpha, syms, tsel),
    ensures
        moves(w, simple_bits(alpha, syms, tsel), s, tree_fin(s, g, simple_lens(alpha, syms, simple_ls(syms.len() as int, tsel)), (w.len() + simple_bits(alpha, syms, tsel).len()) as int)),
{
    let u = simple_bits(alpha, syms, tsel);
    let n = syms.len() as int;
    let wb = bitlen((alpha - 1) as nat);
    let a = fld(1, 2);
    let c = fld((n - 1) as nat, 2);
    let y = syms_bits(syms, wb);
    let z = if n == 4 { fld(tsel as nat, 1) } else { Seq::<nat>::empty() };
    let t = tree_fin(s, g, simple_lens(alpha, syms, simple_ls(n, tsel)), (w.len() + u.len()) as int);
    lemma_pow2_small();
    lemma_bits_of(1, 2);
    lemma_bits_of((n - 1) as nat, 2);
    lemma_bits_of(tsel as nat, 1);
    assert forall|b: Seq<u8>| #[trigger] ext(b, w + u) implies step(b, s) == Step::Next(t) by {
        lemma_rd(b, w, 1, 2, c + (y + z));
        let w1 = w + a;
        assert(w + u =~= w1 + (c + (y + z)));
        lemma_rd(b, w1, (n - 1) as nat, 2, y + z);
        let w2 = w1 + c;
        assert(w1 + (c + (y + z)) =~= w2 + (y + z));
        lemma_simple_syms(b, w2, syms, wb, alpha, z);
        if n == 4 {
            let w3 = w2 + y;
            assert(w2 + (y + z) =~= w3 + (z + Seq::<nat>::empty()));
            lemma_rd(b, w3, tsel as nat, 1, Seq::empty());
        }
        crate::decoder::lemma_step_trees(b, s, g);
    }
    lemma_moves_step(w, u, s, t);
}

// ---------------------------------------------------------------------------
// Planning a code's header: the exec side
// ---------------------------------------------------------------------------

/// `bitlen(x)`.
pub fn bitlen_exec(x: u32) -> (r: u32)
    ensures
        r as nat == bitlen(x as nat),
        r <= 32,
{
    let mut r: u32 = 0;
    let mut y = x;
    proof {
        lemma_bitlen_bound(x as nat);
    }
    while y > 0
        invariant
            bitlen(x as nat) == r + bitlen(y as nat),
            r + bitlen(y as nat) <= 32,
        decreases y,
    {
        proof {
            lemma_bitlen_bound(y as nat);
        }
        y = y / 2;
        r = r + 1;
    }
    r
}

pub proof fn lemma_bitlen_bound(x: nat)
    ensures
        x < pow2(bitlen(x)),
        x < 0x1_0000_0000 ==> bitlen(x) <= 32,
    decreases x,
{
    if x == 0 {
        lemma_pow2_small();
    } else {
        lemma_bitlen_bound(x / 2);
        lemma_pow2_unfold(bitlen(x));
        if x < 0x1_0000_0000 {
            assert(x / 2 < 0x8000_0000);
            if x / 2 >= 0x1_0000_0000 {
            }
            lemma_bitlen_le(x / 2);
        }
    }
}

proof fn lemma_bitlen_le(x: nat)
    requires
        x < 0x8000_0000,
    ensures
        bitlen(x) <= 31,
{
    lemma_bitlen_mono(x, 0x7fff_ffff);
    lemma_bitlen_31();
}

proof fn lemma_bitlen_31()
    ensures
        bitlen(0x7fff_ffff) == 31,
{
    reveal_with_fuel(bitlen, 33);
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

/// What a code's header is: a simple code (up to four symbols) or a
/// complex one (`hskip`, the code length code `cl`, the code length
/// symbols with their extra bits).
pub struct Plan {
    pub simple: bool,
    pub syms: [u16; 4],
    pub nsym: usize,
    pub tsel: u8,
    pub wb: u32,
    pub hskip: usize,
    pub cl: HCode,
    pub jend: usize,
    pub items: Vec<(u8, u8)>,
}

pub open spec fn items_seq(v: Seq<(u8, u8)>) -> Seq<(int, int)> {
    Seq::new(v.len(), |i: int| (v[i].0 as int, v[i].1 as int))
}

impl Plan {
    pub open spec fn syms_seq(&self) -> Seq<int> {
        Seq::new(self.nsym as nat, |i: int| self.syms@[i] as int)
    }

    /// The header the plan writes gives the spec the lengths `lens`.
    pub open spec fn ok(&self, lens: Seq<u8>, alpha: int) -> bool {
        if self.simple {
            &&& 1 <= self.nsym <= 4
            &&& simple_ok(alpha, self.syms_seq(), self.tsel as int)
            &&& self.wb == bitlen((alpha - 1) as nat)
            &&& lens == simple_lens(alpha, self.syms_seq(), simple_ls(self.nsym as int, self.tsel as int))
        } else {
            let t = self.cl.lens@;
            let h = cx_head(t, self.hskip as int);
            let its = items_seq(self.items@);
            &&& self.hskip == 0 || self.hskip == 2 || self.hskip == 3
            &&& self.cl.ok()
            &&& t.len() == 18
            &&& forall|k: int| 0 <= k < 18 ==> #[trigger] t[k] <= 5
            &&& h.0 == t
            &&& (h.1 == 1 || h.2 == 0)
            &&& self.jend == h.3
            &&& items_coded(t, its)
            &&& items_valid(cx_started(t), its, alpha)
            &&& pad_lens(pc_run(cx_started(t), its).lens, alpha) == lens
        }
    }
}

/// The exec mirror of `Pc` while checking a plan.
struct PcM {
    lens: Vec<u8>,
    prev: i64,
    rep: i64,
    replen: i64,
    space: i64,
}

impl PcM {
    spec fn view(&self, cl: Seq<u8>) -> Pc {
        Pc { started: true, cl, lens: self.lens@, prev: self.prev as int, rep: self.rep as int, replen: self.replen as int, space: self.space as int }
    }

    spec fn small(&self, alpha: int) -> bool {
        &&& 0 <= self.lens@.len() <= alpha
        &&& 0 <= self.rep <= self.lens@.len()
        &&& 0 <= self.prev <= 15
        &&& 0 <= self.replen <= 15
        &&& -0x1000_0000 <= self.space <= 32768
    }
}

pub proof fn lemma_pc_run_push(pc: Pc, its: Seq<(int, int)>, it: (int, int))
    ensures
        pc_run(pc, its.push(it)) == pc_tr(pc_run(pc, its), it.0, it.1),
    decreases its.len(),
{
    assert(its.push(it)[0] == if its.len() == 0 { it } else { its[0] });
    if its.len() == 0 {
        assert(its.push(it).subrange(1, 1) =~= Seq::<(int, int)>::empty());
        assert(pc_run(pc_tr(pc, it.0, it.1), Seq::<(int, int)>::empty()) == pc_tr(pc, it.0, it.1));
    } else {
        let r = its.subrange(1, its.len() as int);
        assert(its.push(it).subrange(1, (its.len() + 1) as int) =~= r.push(it));
        lemma_pc_run_push(pc_tr(pc, its[0].0, its[0].1), r, it);
    }
}

/// The forward reading of `items_valid`.
pub open spec fn valid_fwd(pc: Pc, its: Seq<(int, int)>, alpha: int) -> bool {
    &&& its.len() >= 1
    &&& forall|k: int| 0 <= k < its.len() ==> #[trigger] pc_ok1(pc_run(pc, its.subrange(0, k)), its[k].0, its[k].1, alpha)
    &&& forall|k: int| 1 <= k < its.len() ==> !pc_done(#[trigger] pc_run(pc, its.subrange(0, k)), alpha)
    &&& pc_done(pc_run(pc, its), alpha)
    &&& pc_run(pc, its).space == 0
}

pub proof fn lemma_valid_fwd(pc: Pc, its: Seq<(int, int)>, alpha: int)
    requires
        valid_fwd(pc, its, alpha),
    ensures
        items_valid(pc, its, alpha),
    decreases its.len(),
{
    let p2 = pc_tr(pc, its[0].0, its[0].1);
    let r = its.subrange(1, its.len() as int);
    assert(its.subrange(0, 0) =~= Seq::<(int, int)>::empty());
    assert(pc_run(pc, its.subrange(0, 0)) == pc);
    assert(pc_ok1(pc_run(pc, its.subrange(0, 0)), its[0].0, its[0].1, alpha));
    // pc_run(pc, its[0..k+1]) == pc_run(p2, r[0..k])
    assert forall|k: int| 0 <= k <= r.len() implies #[trigger] pc_run(p2, r.subrange(0, k)) == pc_run(pc, its.subrange(0, k + 1)) by {
        let a = its.subrange(0, k + 1);
        assert(a[0] == its[0]);
        assert(a.subrange(1, a.len() as int) =~= r.subrange(0, k));
    }
    assert(pc_run(p2, r) == pc_run(pc, its)) by {
        assert(r.subrange(0, r.len() as int) =~= r);
        assert(its.subrange(0, its.len() as int) =~= its);
    }
    if its.len() == 1 {
        assert(r.subrange(0, 0) =~= r);
        assert(pc_run(p2, r) == p2);
    } else {
        assert(pc_run(p2, r.subrange(0, 0)) == p2);
        assert(!pc_done(pc_run(pc, its.subrange(0, 1)), alpha));
        assert forall|k: int| 0 <= k < r.len() implies #[trigger] pc_ok1(pc_run(p2, r.subrange(0, k)), r[k].0, r[k].1, alpha) by {
            assert(r[k] == its[k + 1]);
            assert(pc_ok1(pc_run(pc, its.subrange(0, k + 1)), its[k + 1].0, its[k + 1].1, alpha));
        }
        assert forall|k: int| 1 <= k < r.len() implies !pc_done(#[trigger] pc_run(p2, r.subrange(0, k)), alpha) by {
            assert(!pc_done(pc_run(pc, its.subrange(0, k + 1)), alpha));
        }
        lemma_valid_fwd(p2, r, alpha);
    }
}

/// `pad_lens` of a prefix.
proof fn lemma_pad_lens_eq(lens: Seq<u8>, target: Seq<u8>, alpha: int)
    requires
        lens.len() <= alpha,
        target.len() == alpha,
        forall|i: int| 0 <= i < lens.len() ==> lens[i] == #[trigger] target[i],
        forall|i: int| lens.len() <= i < alpha ==> #[trigger] target[i] == 0,
    ensures
        pad_lens(lens, alpha) == target,
{
    assert(pad_lens(lens, alpha) =~= target);
}

/// `2^k`.
pub fn pow2_exec(k: u32) -> (r: i64)
    requires
        k <= 30,
    ensures
        r as int == pow2(k as nat),
        r >= 1,
{
    let mut r: i64 = 1;
    let mut i: u32 = 0;
    proof {
        lemma_pow2_small();
    }
    while i < k
        invariant
            i <= k <= 30,
            r as int == pow2(i as nat),
            1 <= r <= 0x4000_0000,
        decreases k - i,
    {
        proof {
            lemma_pow2_unfold((i + 1) as nat);
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(i as nat, 30);
            lemma2_to64();
        }
        r = 2 * r;
        i = i + 1;
    }
    r
}

/// Checks that reading `items` with code length code `t` gives `lens`.
#[verifier::rlimit(60)]
fn check_items(t: &[u8], items: &[(u8, u8)], lens: &[u8]) -> (r: bool)
    requires
        t@.len() == 18,
        lens@.len() <= 1024,
    ensures
        r ==> items_valid(cx_started(t@), items_seq(items@), lens@.len() as int),
        r ==> pad_lens(pc_run(cx_started(t@), items_seq(items@)).lens, lens@.len() as int) == lens@,
        r ==> forall|i: int| 0 <= i < items@.len() ==> (#[trigger] items@[i]).0 < 18 && 1 <= t@[items@[i].0 as int],
{
    let alpha = lens.len();
    let n = items.len();
    if n == 0 {
        return false;
    }
    let ghost its = items_seq(items@);
    let ghost pc0 = cx_started(t@);
    let mut m = PcM { lens: Vec::with_capacity(alpha), prev: 8, rep: 0, replen: 0, space: 32768 };
    let mut k: usize = 0;
    proof {
        assert(its.subrange(0, 0) =~= Seq::<(int, int)>::empty());
        assert(m.view(t@) == pc0) by {
            assert(m.lens@ =~= Seq::<u8>::empty());
        }
    }
    while k < n
        invariant
            k <= n,
            n == items@.len(),
            its == items_seq(items@),
            alpha == lens@.len(),
            alpha <= 1024,
            t@.len() == 18,
            pc0 == cx_started(t@),
            m.small(alpha as int),
            m.space >= 32768 - 16384 * m.lens@.len(),
            m.view(t@) == pc_run(pc0, its.subrange(0, k as int)),
            forall|j: int| 0 <= j < m.lens@.len() ==> m.lens@[j] == #[trigger] lens@[j],
            forall|j: int| 0 <= j < k ==> #[trigger] pc_ok1(pc_run(pc0, its.subrange(0, j)), its[j].0, its[j].1, alpha as int),
            forall|j: int| 1 <= j <= k && j < n ==> !pc_done(#[trigger] pc_run(pc0, its.subrange(0, j)), alpha as int),
            forall|i: int| 0 <= i < k ==> (#[trigger] items@[i]).0 < 18 && 1 <= t@[items@[i].0 as int],
        decreases n - k,
    {
        let (c, delta) = items[k];
        let ghost pk = m.view(t@);
        let ghost l0 = m.lens@;
        if c >= 18 || t[c as usize] == 0 {
            return false;
        }
        proof {
            lemma_pow2_small();
            assert(its[k as int] == (c as int, delta as int));
            lemma_pc_run_push(pc0, its.subrange(0, k as int), its[k as int]);
            assert(its.subrange(0, k as int).push(its[k as int]) =~= its.subrange(0, k + 1));
        }
        if c < 16 {
            if delta != 0 || m.lens.len() >= alpha {
                return false;
            }
            let want = lens[m.lens.len()];
            if want != c {
                return false;
            }
            m.lens.push(c);
            m.rep = 0;
            if c != 0 {
                let sh = pow2_exec((15 - c) as u32);
                proof {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases((15 - c) as nat, 15);
                    assert(sh <= 16384) by {
                        if c > 1 {
                            vstd::arithmetic::power2::lemma_pow2_strictly_increases((15 - c) as nat, 14);
                        }
                        lemma2_to64();
                    }
                }
                m.prev = c as i64;
                m.space = m.space - sh;
            }
            proof {
                assert(m.lens@ == l0.push(c));
                assert(m.view(t@) == pc_tr(pk, c as int, delta as int));
                assert(pc_ok1(pk, c as int, delta as int, alpha as int));
            }
        } else {
            let x: u32 = if c == 16 { 2 } else { 3 };
            let px = pow2_exec(x);
            proof {
                lemma_pow2_small();
                assert(px <= 8);
            }
            if delta as i64 >= px {
                return false;
            }
            let newlen: i64 = if c == 16 { m.prev } else { 0 };
            let rep0: i64 = if m.replen != newlen { 0 } else { m.rep };
            proof {
                assert(0 <= rep0 <= 1024);
                assert((rep0 - 2) * px <= 1024 * 8) by (nonlinear_arith)
                    requires rep0 <= 1024, 1 <= px <= 8;
                assert((rep0 - 2) * px >= -16) by (nonlinear_arith)
                    requires rep0 >= 0, 1 <= px <= 8;
            }
            let rep1: i64 = (if rep0 > 0 { (rep0 - 2) * px } else { 0 }) + delta as i64 + 3;
            let d = rep1 - rep0;
            if d < 0 || m.lens.len() as i64 + d > alpha as i64 {
                return false;
            }
            let mut q: i64 = 0;
            while q < d
                invariant
                    0 <= q <= d,
                    l0.len() + d <= alpha,
                    alpha == lens@.len(),
                    0 <= newlen <= 15,
                    m.lens@ == l0 + Seq::new(q as nat, |i: int| newlen as u8),
                    forall|j: int| 0 <= j < m.lens@.len() ==> m.lens@[j] == #[trigger] lens@[j],
                decreases d - q,
            {
                if lens[m.lens.len()] as i64 != newlen {
                    return false;
                }
                let ghost before = m.lens@;
                m.lens.push(newlen as u8);
                proof {
                    assert(m.lens@ =~= l0 + Seq::new((q + 1) as nat, |i: int| newlen as u8));
                    assert forall|j: int| 0 <= j < m.lens@.len() implies m.lens@[j] == #[trigger] lens@[j] by {
                        if j < before.len() {
                            assert(m.lens@[j] == before[j]);
                        }
                    }
                }
                q = q + 1;
            }
            m.rep = rep1;
            m.replen = newlen;
            if newlen != 0 {
                let sh = pow2_exec((15 - newlen) as u32);
                proof {
                    assert(sh <= 16384) by {
                        if newlen > 1 {
                            vstd::arithmetic::power2::lemma_pow2_strictly_increases((15 - newlen) as nat, 14);
                        }
                        lemma2_to64();
                    }
                    assert(d * sh <= d * 16384) by (nonlinear_arith)
                        requires d >= 0, sh <= 16384;
                }
                m.space = m.space - d * sh;
            }
            proof {
                assert(rep_d(pk, c as int, delta as int) == d);
                assert(m.view(t@) == pc_tr(pk, c as int, delta as int));
                assert(pc_ok1(pk, c as int, delta as int, alpha as int));
            }
        }
        let done = m.lens.len() >= alpha || m.space == 0;
        if k + 1 < n && done {
            return false;
        }
        k = k + 1;
    }
    if !(m.lens.len() >= alpha || m.space == 0) || m.space != 0 {
        return false;
    }
    let mut j = m.lens.len();
    while j < alpha
        invariant
            m.lens@.len() <= j <= alpha,
            alpha == lens@.len(),
            forall|i: int| m.lens@.len() <= i < j ==> #[trigger] lens@[i] == 0,
        decreases alpha - j,
    {
        if lens[j] != 0 {
            return false;
        }
        j = j + 1;
    }
    proof {
        assert(its.subrange(0, n as int) =~= its);
        lemma_pad_lens_eq(m.lens@, lens@, alpha as int);
        lemma_valid_fwd(pc0, its, alpha as int);
    }
    true
}

/// Checks the code length code header: `read_cl` from `hskip`, reading
/// `t`, gets back exactly `t`, and accepts it. Returns where it stops.
fn check_head(t: &[u8], hskip: usize) -> (r: Option<usize>)
    requires
        t@.len() == 18,
        hskip <= 18,
    ensures
        r matches Some(j) ==> cx_head(t@, hskip as int).0 == t@ && (cx_head(t@, hskip as int).1 == 1 || cx_head(t@, hskip as int).2 == 0)
            && cx_head(t@, hskip as int).3 == j && j <= 18 && forall|k: int| 0 <= k < 18 ==> #[trigger] t@[k] <= 5,
{
    let ghost h = cx_head(t@, hskip as int);
    let mut cl: Vec<u8> = vec![0u8; 18];
    let mut num: i64 = 0;
    let mut space: i64 = 32;
    let mut i = hskip;
    let mut stopped = false;
    proof {
        assert(cl@ =~= Seq::new(18, |i: int| 0u8));
        lemma_pow2_small();
    }
    while i < 18 && !stopped
        invariant
            hskip <= i <= 18,
            t@.len() == 18,
            cl@.len() == 18,
            0 <= num <= i,
            -32 <= space <= 32,
            forall|k: int| 0 <= k < 18 ==> #[trigger] cl@[k] <= 5,
            !stopped ==> space > 0,
            !stopped ==> rcl(t@, i as int, cl@, num as int, space as int) == h,
            stopped ==> h == (cl@, num as int, space as int, i as int),
        decreases 18 - i + if stopped { 0int } else { 1int },
    {
        proof {
            assert(forall|k: int| 0 <= k < 18 ==> #[trigger] CL_ORDER[k] < 18) by (compute);
        }
        let o = CL_ORDER[i] as usize;
        let v = t[o];
        if v > 5 {
            return None;
        }
        cl.set(o, v);
        if v != 0 {
            let sh = pow2_exec((5 - v) as u32);
            proof {
                if v > 1 {
                    vstd::arithmetic::power2::lemma_pow2_strictly_increases((5 - v) as nat, 4);
                }
                lemma_pow2_small();
                assert(sh <= 16);
            }
            num = num + 1;
            space = space - sh;
            if space <= 0 {
                stopped = true;
            }
        }
        i = i + 1;
    }
    if num != 1 && space != 0 {
        return None;
    }
    proof {
        if !stopped {
            assert(rcl(t@, i as int, cl@, num as int, space as int) == (cl@, num as int, space as int, i as int));
        }
    }
    // The lengths read must be `t`: none left unread.
    let mut k: usize = 0;
    while k < 18
        invariant
            k <= 18,
            cl@.len() == 18,
            t@.len() == 18,
            forall|j: int| 0 <= j < k ==> cl@[j] == #[trigger] t@[j],
            forall|k: int| 0 <= k < 18 ==> #[trigger] cl@[k] <= 5,
        decreases 18 - k,
    {
        if cl[k] != t[k] {
            return None;
        }
        k = k + 1;
    }
    proof {
        assert(cl@ =~= t@);
    }
    Some(i)
}

/// A code length code length as a number and a bit count.
fn clcl_put(v: u8) -> (r: (u32, u32))
    requires
        v <= 5,
    ensures
        r.1 <= 4,
        (r.0 as nat) < pow2(r.1 as nat),
        bits_of(r.0 as nat, r.1 as nat) == clcl_code(v as int),
{
    proof {
        lemma_pow2_small();
        reveal_with_fuel(bits_of, 5);
    }
    if v == 0 {
        (0, 2)
    } else if v == 4 {
        (1, 2)
    } else if v == 3 {
        (2, 2)
    } else if v == 2 {
        proof {
            assert(bits_of(3, 3) =~= fld(3, 2) + fld(0, 1));
        }
        (3, 3)
    } else if v == 1 {
        proof {
            assert(bits_of(7, 4) =~= fld(3, 2) + (fld(1, 1) + fld(0, 1)));
        }
        (7, 4)
    } else {
        proof {
            assert(bits_of(15, 4) =~= fld(3, 2) + (fld(1, 1) + fld(1, 1)));
        }
        (15, 4)
    }
}

proof fn lemma_clcl_bits_push(t: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j < 18,
    ensures
        clcl_bits(t, i, j + 1) == clcl_bits(t, i, j) + clcl_code(t[CL_ORDER[j] as int] as int),
    decreases j - i,
{
    if i == j {
        assert(clcl_bits(t, i + 1, j + 1) =~= Seq::<nat>::empty());
        assert(clcl_bits(t, i, j) =~= Seq::<nat>::empty());
        assert(clcl_code(t[CL_ORDER[j] as int] as int) + Seq::<nat>::empty() =~= clcl_code(t[CL_ORDER[j] as int] as int));
        assert(Seq::<nat>::empty() + clcl_code(t[CL_ORDER[j] as int] as int) =~= clcl_code(t[CL_ORDER[j] as int] as int));
    } else {
        lemma_clcl_bits_push(t, i + 1, j);
        assert(clcl_code(t[CL_ORDER[i] as int] as int) + (clcl_bits(t, i + 1, j) + clcl_code(t[CL_ORDER[j] as int] as int))
            =~= (clcl_code(t[CL_ORDER[i] as int] as int) + clcl_bits(t, i + 1, j)) + clcl_code(t[CL_ORDER[j] as int] as int));
    }
}

proof fn lemma_items_bits_push(cl: Seq<u8>, its: Seq<(int, int)>, it: (int, int))
    ensures
        items_bits(cl, its.push(it)) == items_bits(cl, its) + item_bits(cl, it),
    decreases its.len(),
{
    assert(its.push(it)[0] == if its.len() == 0 { it } else { its[0] });
    assert(items_bits(cl, its.push(it)) == item_bits(cl, its.push(it)[0]) + items_bits(cl, its.push(it).subrange(1, (its.len() + 1) as int)));
    if its.len() == 0 {
        assert(its.push(it).subrange(1, 1) =~= Seq::<(int, int)>::empty());
        assert(items_bits(cl, its) == Seq::<nat>::empty());
        assert(item_bits(cl, it) + Seq::<nat>::empty() =~= item_bits(cl, it));
        assert(Seq::<nat>::empty() + item_bits(cl, it) =~= item_bits(cl, it));
    } else {
        let r = its.subrange(1, its.len() as int);
        assert(its.push(it).subrange(1, (its.len() + 1) as int) =~= r.push(it));
        lemma_items_bits_push(cl, r, it);
        assert(item_bits(cl, its[0]) + (items_bits(cl, r) + item_bits(cl, it)) =~= (item_bits(cl, its[0]) + items_bits(cl, r)) + item_bits(cl, it));
    }
}

proof fn lemma_syms_bits_push(syms: Seq<int>, x: int, n: nat)
    ensures
        syms_bits(syms.push(x), n) == syms_bits(syms, n) + fld(x as nat, n),
    decreases syms.len(),
{
    assert(syms.push(x)[0] == if syms.len() == 0 { x } else { syms[0] });
    assert(syms_bits(syms.push(x), n) == fld(syms.push(x)[0] as nat, n) + syms_bits(syms.push(x).subrange(1, (syms.len() + 1) as int), n));
    if syms.len() == 0 {
        assert(syms.push(x).subrange(1, 1) =~= Seq::<int>::empty());
        assert(syms_bits(syms, n) == Seq::<nat>::empty());
        assert(fld(x as nat, n) + Seq::<nat>::empty() =~= fld(x as nat, n));
        assert(Seq::<nat>::empty() + fld(x as nat, n) =~= fld(x as nat, n));
    } else {
        let r = syms.subrange(1, syms.len() as int);
        assert(syms.push(x).subrange(1, (syms.len() + 1) as int) =~= r.push(x));
        lemma_syms_bits_push(r, x, n);
        assert(fld(syms[0] as nat, n) + (syms_bits(r, n) + fld(x as nat, n)) =~= (fld(syms[0] as nat, n) + syms_bits(r, n)) + fld(x as nat, n));
    }
}

// ---------------------------------------------------------------------------
// Building a plan
// ---------------------------------------------------------------------------

/// Code length symbols for `lens[..n]`, with runs as repeat codes (google/
/// brotli's `WriteHuffmanTree`). Only the size of the header depends on
/// this: `check_items` checks what it gives.
fn rle_items(lens: &[u8], n: usize, rle: bool) -> (r: Vec<(u8, u8)>)
    requires
        n <= lens@.len(),
{
    let mut out: Vec<(u8, u8)> = Vec::new();
    let mut prev: u8 = 8;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n <= lens@.len(),
        decreases n - i,
    {
        let v = lens[i];
        let mut k = i + 1;
        while k < n && lens[k] == v
            invariant
                i < k <= n,
                n <= lens@.len(),
            decreases n - k,
        {
            k = k + 1;
        }
        let mut reps = k - i;
        if !rle {
            let mut q = 0;
            while q < reps
                invariant q <= reps,
                decreases reps - q,
            {
                out.push((v, 0));
                q = q + 1;
            }
        } else if v == 0 {
            if reps == 11 {
                out.push((0, 0));
                reps = reps - 1;
            }
            if reps < 3 {
                let mut q = 0;
                while q < reps
                    invariant q <= reps,
                    decreases reps - q,
                {
                    out.push((0, 0));
                    q = q + 1;
                }
            } else {
                let start = out.len();
                let mut r = reps - 3;
                loop
                    invariant start <= out@.len(),
                    decreases r,
                {
                    out.push((17, (r % 8) as u8));
                    r = r / 8;
                    if r == 0 {
                        break;
                    }
                    r = r - 1;
                }
                reverse_from(&mut out, start);
            }
        } else {
            if prev != v {
                out.push((v, 0));
                reps = reps - 1;
            }
            if reps == 7 {
                out.push((v, 0));
                reps = reps - 1;
            }
            if reps < 3 {
                let mut q = 0;
                while q < reps
                    invariant q <= reps,
                    decreases reps - q,
                {
                    out.push((v, 0));
                    q = q + 1;
                }
            } else {
                let start = out.len();
                let mut r = reps - 3;
                loop
                    invariant start <= out@.len(),
                    decreases r,
                {
                    out.push((16, (r % 4) as u8));
                    r = r / 4;
                    if r == 0 {
                        break;
                    }
                    r = r - 1;
                }
                reverse_from(&mut out, start);
            }
            prev = v;
        }
        i = k;
    }
    out
}

fn reverse_from(v: &mut Vec<(u8, u8)>, start: usize)
    requires
        start <= old(v)@.len(),
    ensures
        final(v)@.len() == old(v)@.len(),
{
    let n = v.len();
    let mut a = start;
    let mut b = n;
    while b - a > 1
        invariant
            start <= a <= b <= n,
            v@.len() == n,
        decreases b - a,
    {
        let x = v[a];
        let y = v[b - 1];
        v.set(a, y);
        v.set(b - 1, x);
        a = a + 1;
        b = b - 1;
    }
}

/// `simple_lens`, built.
fn build_simple(alpha: usize, syms: &[u16; 4], ls: &[u8; 4], n: usize) -> (r: Vec<u8>)
    requires
        1 <= n <= 4,
        forall|i: int| 0 <= i < n ==> (#[trigger] syms@[i] as int) < alpha,
    ensures
        r@ == simple_lens(alpha as int, Seq::new(n as nat, |i: int| syms@[i] as int), ls@.subrange(0, n as int)),
{
    let mut v: Vec<u8> = vec![0u8; alpha];
    let ghost ss = Seq::new(n as nat, |i: int| syms@[i] as int);
    let mut i: usize = 0;
    proof {
        assert(v@ =~= simple_lens(alpha as int, ss.subrange(0, 0), ls@.subrange(0, 0)));
    }
    while i < n
        invariant
            i <= n <= 4,
            ss == Seq::new(n as nat, |i: int| syms@[i] as int),
            forall|i: int| 0 <= i < n ==> (#[trigger] syms@[i] as int) < alpha,
            v@ == simple_lens(alpha as int, ss.subrange(0, i as int), ls@.subrange(0, i as int)),
            v@.len() == alpha,
        decreases n - i,
    {
        v.set(syms[i] as usize, ls[i]);
        proof {
            let a = ss.subrange(0, i + 1);
            let l = ls@.subrange(0, i + 1);
            assert(a.drop_last() =~= ss.subrange(0, i as int));
            assert(l.drop_last() =~= ls@.subrange(0, i as int));
            assert(a.last() == syms@[i as int] as int);
            assert(l.last() == ls@[i as int]);
            assert(v@ =~= simple_lens(alpha as int, a, l));
        }
        i = i + 1;
    }
    proof {
        assert(ss.subrange(0, n as int) =~= ss);
    }
    v
}

proof fn lemma_simple_lens_len(alpha: int, syms: Seq<int>, ls: Seq<u8>)
    requires
        alpha >= 0,
    ensures
        simple_lens(alpha, syms, ls).len() == alpha,
    decreases syms.len(),
{
    if syms.len() > 0 {
        lemma_simple_lens_len(alpha, syms.drop_last(), ls.drop_last());
    }
}

fn eq_bytes(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len() == b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// A simple code for `lens`, if it has one: up to four symbols with the
/// lengths of one of the RFC's shapes.
fn plan_simple(lens: &[u8]) -> (r: Option<Plan>)
    requires
        2 <= lens@.len() <= 1024,
    ensures
        r matches Some(p) ==> p.ok(lens@, lens@.len() as int),
{
    let alpha = lens.len();
    let mut syms: [u16; 4] = [0; 4];
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < alpha
        invariant
            i <= alpha == lens@.len() <= 1024,
            n <= 4,
            forall|k: int| 0 <= k < n ==> (#[trigger] syms@[k] as int) < i,
            forall|k: int, j: int| 0 <= k < j < n ==> syms@[k] < syms@[j],
        decreases alpha - i,
    {
        if lens[i] != 0 {
            if n == 4 {
                return None;
            }
            syms[n] = i as u16;
            n = n + 1;
        }
        i = i + 1;
    }
    if n == 0 {
        return None;
    }
    // Order by length, then symbol.
    let mut a: usize = 0;
    while a < n
        invariant
            a <= n <= 4,
            alpha == lens@.len(),
            forall|k: int| 0 <= k < n ==> (#[trigger] syms@[k] as int) < alpha,
            forall|k: int, j: int| 0 <= k < j < n ==> syms@[k] != syms@[j],
        decreases n - a,
    {
        let mut b = a + 1;
        while b < n
            invariant
                a < b <= n <= 4,
                alpha == lens@.len(),
                forall|k: int| 0 <= k < n ==> (#[trigger] syms@[k] as int) < alpha,
                forall|k: int, j: int| 0 <= k < j < n ==> syms@[k] != syms@[j],
            decreases n - b,
        {
            if lens[syms[b] as usize] < lens[syms[a] as usize] {
                let t = syms[a];
                syms[a] = syms[b];
                syms[b] = t;
            }
            b = b + 1;
        }
        a = a + 1;
    }
    let tsel: u8 = if n == 4 && lens[syms[0] as usize] == 1 { 1 } else { 0 };
    let ls: [u8; 4] = if n == 1 {
        [1, 0, 0, 0]
    } else if n == 2 {
        [1, 1, 0, 0]
    } else if n == 3 {
        [1, 2, 2, 0]
    } else if tsel == 0 {
        [2, 2, 2, 2]
    } else {
        [1, 2, 3, 3]
    };
    let v = build_simple(alpha, &syms, &ls, n);
    if !eq_bytes(v.as_slice(), lens) {
        return None;
    }
    let wb = bitlen_exec((alpha - 1) as u32);
    let p = Plan { simple: true, syms, nsym: n, tsel, wb, hskip: 0, cl: HCode { lens: Vec::new(), codes: Vec::new(), nused: 0, one: 0 }, jend: 0, items: Vec::new() };
    proof {
        let ss = p.syms_seq();
        assert(ss =~= Seq::new(n as nat, |i: int| syms@[i] as int));
        assert(ls@.subrange(0, n as int) =~= simple_ls(n as int, tsel as int));
        lemma_bitlen_bound((alpha - 1) as nat);
        assert(distinct(ss));
    }
    Some(p)
}

/// A complex code for `lens`, with repeat codes or without.
fn plan_complex(lens: &[u8], n: usize, rle: bool) -> (r: Option<Plan>)
    requires
        lens@.len() <= 1024,
        n <= lens@.len(),
    ensures
        r matches Some(p) ==> p.ok(lens@, lens@.len() as int),
{
    let items = rle_items(lens, n, rle);
    let mut hist: Vec<u32> = vec![0u32; 18];
    let mut i: usize = 0;
    while i < items.len()
        invariant
            i <= items@.len(),
            hist@.len() == 18,
        decreases items@.len() - i,
    {
        let c = items[i].0 as usize;
        if c >= 18 || hist[c] == u32::MAX {
            return None;
        }
        hist.set(c, hist[c] + 1);
        i = i + 1;
    }
    let cll = crate::ehuff::huff_lens(hist.as_slice(), 5);
    let mut hskip: usize = 0;
    if cll[1] == 0 && cll[2] == 0 {
        hskip = if cll[3] == 0 { 3 } else { 2 };
    }
    let jend = match check_head(cll.as_slice(), hskip) {
        Some(j) => j,
        None => return None,
    };
    if !check_items(cll.as_slice(), items.as_slice(), lens) {
        return None;
    }
    let cl = match make_code(cll) {
        Some(c) => c,
        None => return None,
    };
    // With a single code length symbol, every item must be it.
    if cl.nused == 1 {
        let mut k: usize = 0;
        while k < items.len()
            invariant
                k <= items@.len(),
                forall|j: int| 0 <= j < k ==> (#[trigger] items@[j]).0 == cl.one,
            decreases items@.len() - k,
        {
            if items[k].0 as usize != cl.one {
                return None;
            }
            k = k + 1;
        }
    }
    let p = Plan { simple: false, syms: [0; 4], nsym: 0, tsel: 0, wb: 0, hskip, cl, jend, items };
    proof {
        let t = p.cl.lens@;
        let its = items_seq(p.items@);
        assert forall|k: int| 0 <= k < 18 implies #[trigger] t[k] <= 5 by {
        }
        assert forall|i: int| 0 <= i < its.len() implies {
            let c = #[trigger] its[i].0;
            &&& 0 <= c < t.len()
            &&& 1 <= t[c]
            &&& (used(t) == 1 ==> first_used(t, 0) == c)
        } by {
            assert(its[i].0 == p.items@[i].0 as int);
        }
    }
    Some(p)
}

/// The header for a code with lengths `lens` (a simple code when it can
/// be one, else a complex one).
pub fn make_plan(lens: &[u8]) -> (r: Option<Plan>)
    requires
        2 <= lens@.len() <= 1024,
    ensures
        r matches Some(p) ==> p.ok(lens@, lens@.len() as int),
{
    if let Some(p) = plan_simple(lens) {
        return Some(p);
    }
    // Up to the last symbol with a code.
    let mut n = lens.len();
    while n > 0 && lens[n - 1] == 0
        invariant
            n <= lens@.len(),
        decreases n,
    {
        n = n - 1;
    }
    if let Some(p) = plan_complex(lens, n, true) {
        return Some(p);
    }
    plan_complex(lens, n, false)
}

// ---------------------------------------------------------------------------
// Writing a code's header
// ---------------------------------------------------------------------------

/// Writes the header `p` plans, read in `Trees(g)` from state `s`.
pub fn put_tree(bw: &mut BitWriter, p: &Plan, alpha: usize, Ghost(s): Ghost<St>, Ghost(g): Ghost<int>, Ghost(lens): Ghost<Seq<u8>>)
    requires
        old(bw).wf(),
        p.ok(lens, alpha as int),
        tree_phase(s, g, alpha as int),
        s.pos == old(bw).bits().len(),
        s.pc == pc_init(),
        2 <= alpha <= 1024,
    ensures
        final(bw).wf(),
        final(bw).sent() == old(bw).sent(),
        final(bw).bits().len() >= old(bw).bits().len(),
        moves(old(bw).bits(), final(bw).bits().subrange(old(bw).bits().len() as int, final(bw).bits().len() as int), s,
            tree_fin(s, g, lens, final(bw).bits().len() as int)),
        final(bw).bits() == old(bw).bits() + final(bw).bits().subrange(old(bw).bits().len() as int, final(bw).bits().len() as int),
{
    let ghost w0 = bw.bits();
    proof {
        lemma_pow2_small();
    }
    if p.simple {
        let ghost ss = p.syms_seq();
        bw.put(1, 2);
        bw.put((p.nsym - 1) as u32, 2);
        let ghost w1 = bw.bits();
        let mut i: usize = 0;
        proof {
            assert(ss.subrange(0, 0) =~= Seq::<int>::empty());
            assert(w1 =~= w1 + syms_bits(ss.subrange(0, 0), p.wb as nat));
            lemma_bitlen_bound((alpha - 1) as nat);
        }
        while i < p.nsym
            invariant
                bw.wf(),
                bw.sent() == old(bw).sent(),
                i <= p.nsym <= 4,
                ss == p.syms_seq(),
                p.ok(lens, alpha as int),
                p.simple,
                bw.bits() == w1 + syms_bits(ss.subrange(0, i as int), p.wb as nat),
                (alpha - 1) < pow2(p.wb as nat),
                p.wb <= 32,
            decreases p.nsym - i,
        {
            proof {
                assert(0 <= ss[i as int] < alpha);
                assert(p.syms@[i as int] as int == ss[i as int]);
                lemma_bitlen_bound((alpha - 1) as nat);
            }
            bw.put(p.syms[i] as u32, p.wb);
            proof {
                lemma_syms_bits_push(ss.subrange(0, i as int), ss[i as int], p.wb as nat);
                assert(ss.subrange(0, i as int).push(ss[i as int]) =~= ss.subrange(0, i + 1));
            }
            i = i + 1;
        }
        if p.nsym == 4 {
            bw.put(p.tsel as u32, 1);
        }
        proof {
            assert(ss.subrange(0, p.nsym as int) =~= ss);
            let u = simple_bits(alpha as int, ss, p.tsel as int);
            assert(bw.bits() =~= w0 + u);
            lemma_simple(w0, s, g, alpha as int, ss, p.tsel as int);
            assert(bw.bits().subrange(w0.len() as int, bw.bits().len() as int) =~= u);
        }
    } else {
        let ghost t = p.cl.lens@;
        let ghost its = items_seq(p.items@);
        bw.put(p.hskip as u32, 2);
        let ghost w1 = bw.bits();
        let mut k = p.hskip;
        proof {
            assert(clcl_bits(t, p.hskip as int, p.hskip as int) =~= Seq::<nat>::empty());
            assert(w1 =~= w1 + clcl_bits(t, p.hskip as int, p.hskip as int));
            lemma_rcl_end(t, p.hskip as int, Seq::new(18, |i: int| 0u8), 0, 32);
        }
        while k < p.jend
            invariant
                bw.wf(),
                bw.sent() == old(bw).sent(),
                p.hskip <= k <= p.jend <= 18,
                t == p.cl.lens@,
                t.len() == 18,
                forall|q: int| 0 <= q < 18 ==> #[trigger] t[q] <= 5,
                bw.bits() == w1 + clcl_bits(t, p.hskip as int, k as int),
            decreases p.jend - k,
        {
            proof {
                assert(forall|q: int| 0 <= q < 18 ==> #[trigger] CL_ORDER[q] < 18) by (compute);
            }
            let o = CL_ORDER[k] as usize;
            let v = verilith_core::prims::get(p.cl.lens.as_slice(), o);
            let (c, n) = clcl_put(v);
            bw.put(c, n);
            proof {
                lemma_clcl_bits_push(t, p.hskip as int, k as int);
            }
            k = k + 1;
        }
        let ghost w2 = bw.bits();
        let ghost s2 = St { pos: w2.len() as int, pc: cx_started(cx_head(t, p.hskip as int).0), ..s };
        proof {
            assert(w2 =~= w0 + cx_head_bits(t, p.hskip as int));
            lemma_cx_head(w0, s, g, alpha as int, t, p.hskip as int);
            assert(s2.pc == cx_started(t));
            assert(items_bits(t, its.subrange(0, 0)) =~= Seq::<nat>::empty()) by {
                assert(its.subrange(0, 0).len() == 0);
            }
            assert(w2 =~= w2 + items_bits(t, its.subrange(0, 0)));
        }
        let mut i: usize = 0;
        while i < p.items.len()
            invariant
                bw.wf(),
                bw.sent() == old(bw).sent(),
                i <= p.items@.len(),
                its == items_seq(p.items@),
                t == p.cl.lens@,
                p.cl.ok(),
                p.ok(lens, alpha as int),
                !p.simple,
                bw.bits() == w2 + items_bits(t, its.subrange(0, i as int)),
            decreases p.items@.len() - i,
        {
            let (c, d) = p.items[i];
            proof {
                assert(its[i as int] == (c as int, d as int));
                assert(items_coded(t, its));
                let _ = its[i as int].0;
                assert(0 <= c < 18 && 1 <= t[c as int]);
                if p.cl.nused == 1 {
                    assert(first_used(t, 0) == c as int);
                    assert(first_used(t, 0) == p.cl.one as int);
                }
            }
            let (code, len) = p.cl.sym(c as usize);
            bw.put64(code, len);
            let x: u32 = if c == 16 { 2 } else if c == 17 { 3 } else { 0 };
            proof {
                assert(x as nat == xb(c as int));
                // pc_ok1 bounds the extra bits.
                lemma_items_valid_ok(cx_started(t), its, alpha as int, i as int);
            }
            bw.put(d as u32, x);
            proof {
                lemma_items_bits_push(t, its.subrange(0, i as int), its[i as int]);
                assert(its.subrange(0, i as int).push(its[i as int]) =~= its.subrange(0, i + 1));
            }
            i = i + 1;
        }
        proof {
            assert(its.subrange(0, p.items@.len() as int) =~= its);
            let s2p = St { pos: w2.len() as int, pc: cx_started(t), ..s };
            assert(s2 == s2p);
            lemma_items(w2, s2, g, its, alpha as int);
            let u1 = cx_head_bits(t, p.hskip as int);
            let u2 = items_bits(t, its);
            assert(w2 == w0 + u1);
            lemma_moves_trans(w0, u1, u2, s, s2, tree_fin(s2, g, pad_lens(pc_run(s2.pc, its).lens, alpha as int), (w2.len() + u2.len()) as int));
            assert(bw.bits() =~= w0 + (u1 + u2));
            assert(bw.bits().subrange(w0.len() as int, bw.bits().len() as int) =~= u1 + u2);
        }
    }
}

/// Each item of a valid list fits its extra bits.
proof fn lemma_items_valid_ok(pc: Pc, its: Seq<(int, int)>, alpha: int, i: int)
    requires
        items_valid(pc, its, alpha),
        0 <= i < its.len(),
    ensures
        0 <= its[i].1 < pow2(xb(its[i].0)),
    decreases its.len(),
{
    if i > 0 {
        let r = its.subrange(1, its.len() as int);
        assert(r[i - 1] == its[i]);
        lemma_items_valid_ok(pc_tr(pc, its[0].0, its[0].1), r, alpha, i - 1);
    }
}

} // verus!
