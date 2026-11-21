//! Reading prefix codes (§3.7.2.1), proven to compute `spec::read_code`.
use crate::bitreader::*;
use crate::huffman::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// The order in which the code length code's lengths are sent.
pub const CL_ORDER: [u8; 19] = [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

pub proof fn lemma_cl_order()
    ensures
        forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i],
        forall|i: int| 0 <= i < 19 ==> #[trigger] cl_order()[i] < 19,
{
    assert(forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i]) by (compute);
    assert(forall|i: int| 0 <= i < 19 ==> #[trigger] cl_order()[i] < 19) by (compute);
}

/// Work charged per alphabet symbol for reading a code (filling the
/// lengths), on top of building its tables.
pub open spec fn code_cost(size: nat) -> nat {
    build_cost(size, MAX_ROOT as nat) + build_cost(19, 7) + 38 * size + 400
}

/// Sets `lens[s]` to 1 if `s` is in the alphabet.
fn set_one_exec(lens: &mut Vec<u8>, s: u32)
    ensures
        final(lens)@ == set_one(old(lens)@, s as nat),
{
    if (s as usize) < lens.len() {
        lens.set(s as usize, 1);
    }
}

/// Simple code lengths (§3.7.2.1.1), after the first bit.
fn read_simple_lens(br: &mut BitReader, data: &[u8], size: usize) -> (r: Option<Vec<u8>>)
    requires
        old(br).ok(data@),
        1 <= size <= MAX_ALPHA,
    ensures
        final(br).ok(data@),
        match read_simple(data@, old(br).pos(), size as nat) {
            Some((lens, p)) => r matches Some(v) && v@ == lens && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + 4 * refill_cost() + size,
        final(br).pos() >= old(br).pos(),
        r matches Some(v) ==> v@.len() == size,
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let n1 = match br.take(data, 1) {
        Some(v) => v,
        None => return None,
    };
    let f8 = match br.take(data, 1) {
        Some(v) => v,
        None => return None,
    };
    proof {
        lemma2_to64();
        verilith_core::bits::lemma_bits_bound(b, p0, 1);
    }
    let w: u32 = if f8 == 0 { 1 } else { 8 };
    let ghost p2 = br.pos();
    let s0 = match br.take(data, w) {
        Some(v) => v,
        None => return None,
    };
    let ghost p3 = br.pos();
    assert(rd(b, p0, 1) == Some(n1 as nat));
    assert(rd(b, p0 + 1, 1) == Some(f8 as nat));
    assert(rd(b, p0 + 2, w as nat) == Some(s0 as nat));
    let mut lens: Vec<u8> = vec![0u8; size];
    br.work = Ghost(br.work@ + size as nat);
    proof {
        assert(lens@ == zeros(size as nat));
    }
    set_one_exec(&mut lens, s0);
    if n1 == 1 {
        let s1 = match br.take(data, 8) {
            Some(v) => v,
            None => return None,
        };
        set_one_exec(&mut lens, s1);
        assert(rd(b, p3, 8) == Some(s1 as nat));
        assert(read_simple(b, p0, size as nat) == Some((lens@, br.pos())));
    } else {
        assert(read_simple(b, p0, size as nat) == Some((lens@, br.pos())));
    }
    Some(lens)
}

/// The code length code's lengths: what `read_normal` reads before its
/// `valid_code` check.
pub open spec fn cl_part(b: Seq<u8>, pos: int) -> Option<(Seq<u8>, int)> {
    match rd(b, pos, 4) {
        None => None,
        Some(x) => {
            let n = x + 4;
            let p = pos + 4 + 3 * n;
            if p > nbits(b) {
                None
            } else {
                Some((cl_lens(b, pos + 4, n), p))
            }
        },
    }
}

fn read_cl(br: &mut BitReader, data: &[u8]) -> (r: Option<[u8; 19]>)
    requires
        old(br).ok(data@),
    ensures
        final(br).ok(data@),
        match cl_part(data@, old(br).pos()) {
            Some((cl, p)) => r matches Some(v) && v@ == cl && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + 20 * refill_cost(),
        final(br).pos() >= old(br).pos(),
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    let n = match br.take(data, 4) {
        Some(v) => {
            proof {
                lemma2_to64();
                verilith_core::bits::lemma_bits_bound(b, p0, 4);
            }
            v + 4
        },
        None => return None,
    };
    let ghost pc = br.pos();
    let mut cl = [0u8; 19];
    let mut i: u32 = 0;
    proof {
        lemma_cl_order();
        assert(cl@ == cl_lens(b, pc, 0));
    }
    while i < n
        invariant
            br.ok(b),
            b == data@,
            4 <= n <= 19,
            i <= n,
            pc == p0 + 4,
            p0 == old(br).pos(),
            w0 == old(br).work@,
            br.pos() == pc + 3 * i,
            rd(b, p0, 4) == Some((n - 4) as nat),
            cl@ == cl_lens(b, pc, i as nat),
            br.work@ <= w0 + refill_cost() + i * refill_cost(),
            forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i],
            forall|i: int| 0 <= i < 19 ==> #[trigger] cl_order()[i] < 19,
        decreases n - i,
    {
        proof {
            assert(i * refill_cost() <= 19 * refill_cost()) by (nonlinear_arith)
                requires i <= n, n <= 19;
        }
        let v = match br.take(data, 3) {
            Some(v) => v,
            None => {
                proof {
                    assert(pc + 3 * i + 3 > nbits(b));
                    assert(pc + 3 * n >= pc + 3 * i + 3) by (nonlinear_arith)
                        requires i < n;
                    assert(i * refill_cost() <= 19 * refill_cost()) by (nonlinear_arith)
                        requires i < n, n <= 19;
                }
                return None;
            },
        };
        proof {
            lemma2_to64();
            verilith_core::bits::lemma_bits_bound(b, pc + 3 * i, 3);
            assert(i * refill_cost() + refill_cost() == (i + 1) * refill_cost()) by (nonlinear_arith);
        }
        cl[CL_ORDER[i as usize] as usize] = v as u8;
        i = i + 1;
    }
    Some(cl)
}

/// Code lengths read with the code length code (§3.7.2.1.2).
#[verifier::rlimit(30)]
fn read_lens_exec(br: &mut BitReader, data: &[u8], clc: &HCode, Ghost(cl): Ghost<Seq<u8>>, size: usize, tokens0: usize) -> (r: Option<Vec<u8>>)
    requires
        old(br).ok(data@),
        hcode_ok(*clc, cl),
        cl.len() == 19,
        1 <= size <= MAX_ALPHA,
    ensures
        final(br).ok(data@),
        match read_lens(cl, data@, old(br).pos(), size as nat, tokens0 as nat, 0, 8, zeros(size as nat)) {
            Some((lens, p)) => r matches Some(v) && v@ == lens && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + 38 * size,
        final(br).pos() >= old(br).pos(),
        r matches Some(v) ==> v@.len() == size,
{
    let ghost b = data@;
    let ghost rl = read_lens(cl, b, br.pos(), size as nat, tokens0 as nat, 0, 8, zeros(size as nat));
    let ghost wl = br.work@;
    let mut lens: Vec<u8> = vec![0u8; size];
    br.work = Ghost(br.work@ + size as nat);
    proof {
        assert(lens@ == zeros(size as nat));
    }
    let mut tokens = tokens0;
    let mut sym: usize = 0;
    let mut prev: u8 = 8;
    while sym < size && tokens > 0
        invariant
            br.ok(b),
            br.pos() >= old(br).pos(),
            b == data@,
            hcode_ok(*clc, cl),
            cl.len() == 19,
            size <= MAX_ALPHA,
            sym <= size,
            lens@.len() == size,
            read_lens(cl, b, br.pos(), size as nat, tokens as nat, sym as nat, prev, lens@) == rl,
            rl == read_lens(cl, b, old(br).pos(), size as nat, tokens0 as nat, 0, 8, zeros(size as nat)),
            wl == old(br).work@,
            br.work@ <= wl + size + 37 * sym,
        decreases size - sym,
    {
        let ghost lp = lens@;
        proof {
            assert(37 * sym + 37 <= 37 * size) by (nonlinear_arith)
                requires sym < size;
        }
        let ghost pp = br.pos();
        let ghost pt = tokens as nat;
        let ghost pprev = prev;
        assert(read_lens(cl, b, pp, size as nat, pt, sym as nat, pprev, lp) == rl);
        let c = match br.read_symbol(data, clc, Ghost(cl)) {
            Some(c) => c,
            None => {
                assert(read_symbol(cl, b, pp) is None);
                assert(rl is None);
                return None;
            },
        };
        assert(read_symbol(cl, b, pp) == Some((c as nat, br.pos())));
        tokens = tokens - 1;
        if c < 16 {
            lens.set(sym, c as u8);
            sym = sym + 1;
            if c != 0 {
                prev = c as u8;
            }
        } else {
            let eb: u32 = if c == 16 {
                2
            } else if c == 17 {
                3
            } else {
                7
            };
            let off: usize = if c == 18 {
                11
            } else {
                3
            };
            let x = match br.take(data, eb) {
                Some(v) => v,
                None => return None,
            };
            proof {
                lemma2_to64();
                verilith_core::bits::lemma_bits_bound(b, br.pos() - eb, eb as nat);
                lemma_pow2_strictly_increases(eb as nat, 8);
            }
            let rep = x as usize + off;
            if rep > size - sym {
                return None;
            }
            let v = if c == 16 {
                prev
            } else {
                0u8
            };
            let mut k: usize = 0;
            let ghost wk = br.work@;
            while k < rep
                invariant
                    br.work@ == wk + k,
                    br.pos() >= old(br).pos(),
                    sym + rep <= size,
                    k <= rep,
                    lens@.len() == size,
                    lp.len() == size,
                    forall|j: int|
                        0 <= j < size ==> #[trigger] lens@[j] == if sym <= j < sym + k {
                            v
                        } else {
                            lp[j]
                        },
                decreases rep - k,
            {
                lens.set(sym + k, v);
                br.work = Ghost(br.work@ + 1);
                k = k + 1;
            }
            assert(lens@ == set_run(lp, sym as nat, rep as nat, v));
            proof {
                assert(37 * sym + 37 * rep == 37 * (sym + rep)) by (nonlinear_arith);
            }
            sym = sym + rep;
        }
    }
    Some(lens)
}

/// Normal code lengths (§3.7.2.1.2), after the first bit.
fn read_normal_lens(br: &mut BitReader, data: &[u8], size: usize) -> (r: Option<Vec<u8>>)
    requires
        old(br).ok(data@),
        1 <= size <= MAX_ALPHA,
    ensures
        final(br).ok(data@),
        match read_normal(data@, old(br).pos(), size as nat) {
            Some((lens, p)) => r matches Some(v) && v@ == lens && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + 25 * refill_cost() + build_cost(19, 7) + 38 * size,
        final(br).pos() >= old(br).pos(),
        r matches Some(v) ==> v@.len() == size,
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let cl = match read_cl(br, data) {
        Some(cl) => cl,
        None => return None,
    };
    let (clr, Ghost(cw)) = build(&cl, 7);
    br.work = Ghost(br.work@ + cw);
    let clc = match clr {
        Some(h) => h,
        None => return None,
    };
    let um = match br.take(data, 1) {
        Some(v) => v,
        None => return None,
    };
    let mut tokens: usize = size;
    if um == 1 {
        let y = match br.take(data, 3) {
            Some(v) => v,
            None => return None,
        };
        proof {
            lemma2_to64();
            verilith_core::bits::lemma_bits_bound(b, br.pos() - 3, 3);
        }
        let z = match br.take(data, 2 + 2 * y) {
            Some(v) => v,
            None => return None,
        };
        proof {
            verilith_core::bits::lemma_bits_bound(b, br.pos() - (2 + 2 * y), (2 + 2 * y) as nat);
            lemma_pow2_strictly_increases((2 + 2 * y) as nat, 17);
        }
        if z as usize + 2 > size {
            return None;
        }
        tokens = z as usize + 2;
    }
    read_lens_exec(br, data, &clc, Ghost(cl@), size, tokens)
}

/// Reads a prefix code for an alphabet of `size` symbols and builds its
/// tables. Returns the code and its lengths (ghost), or `None` exactly
/// when `spec::read_code` fails.
#[verifier::rlimit(30)]
pub fn read_prefix_code(br: &mut BitReader, data: &[u8], size: usize) -> (r: Option<(HCode, Ghost<Seq<u8>>)>)
    requires
        old(br).ok(data@),
        1 <= size <= MAX_ALPHA,
    ensures
        final(br).ok(data@),
        match read_code(data@, old(br).pos(), size as nat) {
            Some((lens, p)) => r matches Some((h, gl)) && gl@ == lens && hcode_ok(h, lens)
                && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + code_cost(size as nat),
        final(br).pos() >= old(br).pos(),
{
    let simple = match br.take(data, 1) {
        Some(v) => v,
        None => return None,
    };
    let lr = if simple == 1 {
        read_simple_lens(br, data, size)
    } else {
        read_normal_lens(br, data, size)
    };
    let lens = match lr {
        Some(l) => l,
        None => return None,
    };
    let (hr, Ghost(hw)) = build(&lens, MAX_ROOT);
    br.work = Ghost(br.work@ + hw);
    match hr {
        Some(h) => Some((h, Ghost(lens@))),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Groups (§3.7.2.2)
// ---------------------------------------------------------------------------

/// A group's five codes: green (with length prefixes and color cache),
/// red, blue, alpha, distance.
pub struct Group {
    pub codes: Vec<HCode>,
}

#[verifier::opaque]
pub open spec fn group_ok(g: Group, lens: Seq<Seq<u8>>) -> bool {
    &&& g.codes@.len() == 5
    &&& lens.len() == 5
    &&& forall|j: int| 0 <= j < 5 ==> #[trigger] hcode_ok(g.codes@[j], lens[j])
}

pub open spec fn groups_ok(gs: Seq<Group>, lens: Seq<Seq<Seq<u8>>>) -> bool {
    &&& gs.len() == lens.len()
    &&& forall|i: int| 0 <= i < gs.len() ==> #[trigger] group_ok(gs[i], lens[i])
}

/// Work charged for reading one group.
pub open spec fn group_cost(cb: nat) -> nat {
    5 * code_cost(MAX_ALPHA as nat)
}

pub proof fn lemma_code_cost_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        code_cost(a) <= code_cost(b),
{
}

/// Reads one group for `cb` color cache bits.
pub fn read_group(br: &mut BitReader, data: &[u8], cb: u32) -> (r: Option<(Group, Ghost<Seq<Seq<u8>>>)>)
    requires
        old(br).ok(data@),
        cb <= 11,
    ensures
        final(br).ok(data@),
        match read_group_codes(data@, old(br).pos(), cb as nat, 5) {
            Some((cs, p)) => r matches Some((g, gl)) && gl@ == cs && group_ok(g, cs) && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + group_cost(cb as nat),
        final(br).pos() >= old(br).pos(),
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    let mut codes: Vec<HCode> = Vec::new();
    let ghost mut gl: Seq<Seq<u8>> = seq![];
    let mut j: usize = 0;
    proof {
        lemma2_to64();
        lemma_pow2_strictly_increases(cb as nat, 12);
    }
    let cs: usize = if cb == 0 { 0 } else { 1usize << (cb as usize) };
    proof {
        if cb > 0 {
            vstd::bits::lemma_usize_shl_is_mul(1, cb as usize);
        }
        assert(cs == cache_size(cb as nat));
    }
    while j < 5
        invariant
            br.ok(b),
            br.pos() >= old(br).pos(),
            b == data@,
            j <= 5,
            cb <= 11,
            cs == cache_size(cb as nat),
            cs <= 2048,
            p0 == old(br).pos(),
            w0 == old(br).work@,
            read_group_codes(b, p0, cb as nat, j as nat) == Some((gl, br.pos())),
            codes@.len() == j,
            gl.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] hcode_ok(codes@[k], gl[k]),
            br.work@ <= w0 + j * code_cost(MAX_ALPHA as nat),
        decreases 5 - j,
    {
        let size: usize = if j == 0 {
            256 + 24 + cs
        } else if j == 4 {
            40
        } else {
            256
        };
        assert(size == alphabet(j as nat, cb as nat));
        let ghost wj = br.work@;
        let ghost before = codes@;
        match read_prefix_code(br, data, size) {
            Some((h, lens)) => {
                codes.push(h);
                proof {
                    gl = gl.push(lens@);
                    lemma_code_cost_mono(size as nat, MAX_ALPHA as nat);
                    assert(j * code_cost(MAX_ALPHA as nat) + code_cost(MAX_ALPHA as nat) == (j + 1) * code_cost(MAX_ALPHA as nat))
                        by (nonlinear_arith);
                    assert forall|k: int| 0 <= k < j + 1 implies #[trigger] hcode_ok(codes@[k], gl[k]) by {
                        if k < j {
                            assert(codes@[k] == before[k]);
                        }
                    }
                }
            },
            None => {
                proof {
                    if j < 4 {
                        crate::slemmas::lemma_group_codes_fail(b, p0, cb as nat, j as nat, 5);
                    }
                    lemma_code_cost_mono(size as nat, MAX_ALPHA as nat);
                    assert(j * code_cost(MAX_ALPHA as nat) + code_cost(MAX_ALPHA as nat) <= 5 * code_cost(MAX_ALPHA as nat))
                        by (nonlinear_arith) requires j < 5;
                }
                return None;
            },
        }
        j = j + 1;
    }
    let g = Group { codes };
    proof {
        reveal(group_ok);
    }
    Some((g, Ghost(gl)))
}

/// Reads `n` groups.
#[verifier::rlimit(100)]
pub fn read_groups_exec(br: &mut BitReader, data: &[u8], cb: u32, n: usize) -> (r: Option<(Vec<Group>, Ghost<Seq<Seq<Seq<u8>>>>)>)
    requires
        old(br).ok(data@),
        cb <= 11,
    ensures
        final(br).ok(data@),
        match read_groups(data@, old(br).pos(), cb as nat, n as nat) {
            Some((gs, p)) => r matches Some((g, gl)) && gl@ == gs && groups_ok(g@, gs) && final(br).pos() == p,
            None => r is None,
        },
        final(br).work@ <= old(br).work@ + n * group_cost(cb as nat),
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + group_cost(cb as nat) * (final(br).pos() - old(br).pos()) + group_cost(
            cb as nat,
        ),
{
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    let mut groups: Vec<Group> = Vec::new();
    let ghost mut gl: Seq<Seq<Seq<u8>>> = seq![];
    let mut i: usize = 0;
    while i < n
        invariant
            br.ok(b),
            br.pos() >= old(br).pos(),
            b == data@,
            i <= n,
            cb <= 11,
            p0 == old(br).pos(),
            w0 == old(br).work@,
            read_groups(b, p0, cb as nat, i as nat) == Some((gl, br.pos())),
            groups_ok(groups@, gl),
            gl.len() == i,
            br.work@ <= w0 + i * group_cost(cb as nat),
            br.work@ <= w0 + group_cost(cb as nat) * (br.pos() - p0),
        decreases n - i,
    {
        let ghost pi = br.pos();
        let ghost wi = br.work@;
        match read_group(br, data, cb) {
            Some((g, cs)) => {
                let ghost before = groups@;
                groups.push(g);
                proof {
                    crate::slemmas::lemma_groups_step(b, p0, cb as nat, i as nat, gl, pi, cs@, br.pos());
                    gl = gl.push(cs@);
                    assert forall|k: int| 0 <= k < groups@.len() implies #[trigger] group_ok(groups@[k], gl[k]) by {
                        if k < i {
                            assert(groups@[k] == before[k]);
                        }
                    }
                    crate::slemmas::lemma_mul_step(i as nat, group_cost(cb as nat));
                    crate::slemmas::lemma_group_codes_adv(b, pi, cb as nat, 5);
                    let gc = group_cost(cb as nat);
                    assert(br.work@ <= w0 + gc * (br.pos() - p0)) by (nonlinear_arith)
                        requires
                            br.work@ <= wi + gc,
                            wi <= w0 + gc * (pi - p0),
                            br.pos() >= pi + 5,
                    ;
                }
            },
            None => {
                proof {
                    if i + 1 < n {
                        crate::slemmas::lemma_groups_fail(b, p0, cb as nat, i as nat, n as nat);
                    }
                    crate::slemmas::lemma_mul_step(i as nat, group_cost(cb as nat));
                    crate::slemmas::lemma_mul_le((i + 1) as nat, n as nat, group_cost(cb as nat));
                    let gc = group_cost(cb as nat);
                    assert(br.work@ <= w0 + gc * (br.pos() - p0) + gc) by (nonlinear_arith)
                        requires
                            br.work@ <= wi + gc,
                            wi <= w0 + gc * (pi - p0),
                            br.pos() >= pi,
                    ;
                }
                return None;
            },
        }
        i = i + 1;
    }
    Some((groups, Ghost(gl)))
}

} // verus!
