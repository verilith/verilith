//! The meta-block planner: block types and counts, context modes and maps,
//! and code lengths, from the commands of a block. Not trusted: the writer
//! (`mbw`) checks everything it takes from here. Only memory safety and
//! termination are proven.
use crate::mblock::Cmd;
use crate::mbw::{CatPlan, MbPlan};
use vstd::prelude::*;

verus! {

/// One block type: the category is not split.
pub fn cat1() -> (r: CatPlan) {
    CatPlan { nbt: 1, types: Vec::new(), lens: Vec::new(), tl: Vec::new(), cl: Vec::new() }
}

/// Code lengths for counts `f` (some symbol always gets a code).
pub fn lens_of(f: &Vec<u32>) -> (r: Vec<u8>)
    requires
        1 <= f@.len() <= 1024,
{
    let mut g = f.clone();
    let mut any = false;
    let mut i: usize = 0;
    while i < g.len()
        invariant
            i <= g@.len(),
        decreases g@.len() - i,
    {
        if g[i] != 0 {
            any = true;
        }
        i = i + 1;
    }
    if !any && g.len() > 0 {
        g.set(0, 1);
    }
    crate::ehuff::huff_lens(&g, 15)
}

/// One block type and one tree per category: the literal, command and
/// distance counts `lf`, `cf`, `df`.
pub fn plan_single(lf: &Vec<u32>, cf: &Vec<u32>, df: &Vec<u32>) -> (r: MbPlan)
    requires
        lf@.len() == 256,
        cf@.len() == 704,
        df@.len() == 64,
{
    MbPlan {
        cats: vec![cat1(), cat1(), cat1()],
        modes: vec![0u8],
        lmap: vec![0u8; 64],
        ntl: 1,
        dmap: vec![0u8; 4],
        ntd: 1,
        lt: vec![lens_of(lf)],
        ct: vec![lens_of(cf)],
        dt: vec![lens_of(df)],
    }
}

// ---------------------------------------------------------------------------
// Costs in bits, from symbol counts
// ---------------------------------------------------------------------------

/// `log2(i)` in units of 2^-16, for `i < 256`.
pub const LOG2: [u32; 256] = [
    0, 0, 65536, 103872, 131072, 152170, 169408, 183983, 196608, 207744, 217706, 226717, 234944, 242512, 249519, 256042,
    262144, 267876, 273280, 278392, 283242, 287855, 292253, 296456, 300480, 304340, 308048, 311616, 315055, 318373, 321578, 324678,
    327680, 330589, 333412, 336153, 338816, 341407, 343928, 346384, 348778, 351113, 353391, 355616, 357789, 359914, 361992, 364026,
    366016, 367966, 369876, 371748, 373584, 375385, 377152, 378887, 380591, 382264, 383909, 385525, 387114, 388677, 390214, 391727,
    393216, 394682, 396125, 397547, 398948, 400328, 401689, 403030, 404352, 405656, 406943, 408212, 409464, 410700, 411920, 413125,
    414314, 415488, 416649, 417795, 418927, 420046, 421152, 422245, 423325, 424394, 425450, 426495, 427528, 428550, 429562, 430562,
    431552, 432532, 433502, 434462, 435412, 436353, 437284, 438206, 439120, 440025, 440921, 441809, 442688, 443560, 444423, 445279,
    446127, 446967, 447800, 448626, 449445, 450256, 451061, 451859, 452650, 453435, 454213, 454985, 455750, 456510, 457263, 458010,
    458752, 459488, 460218, 460942, 461661, 462375, 463083, 463786, 464484, 465177, 465864, 466547, 467225, 467898, 468566, 469229,
    469888, 470543, 471192, 471838, 472479, 473115, 473748, 474376, 475000, 475620, 476236, 476848, 477456, 478060, 478661, 479257,
    479850, 480439, 481024, 481606, 482185, 482759, 483331, 483898, 484463, 485024, 485582, 486136, 486688, 487236, 487781, 488323,
    488861, 489397, 489930, 490459, 490986, 491510, 492031, 492549, 493064, 493577, 494086, 494593, 495098, 495599, 496098, 496594,
    497088, 497579, 498068, 498554, 499038, 499519, 499998, 500474, 500948, 501419, 501889, 502355, 502820, 503282, 503742, 504200,
    504656, 505109, 505561, 506010, 506457, 506902, 507345, 507786, 508224, 508661, 509096, 509528, 509959, 510388, 510815, 511240,
    511663, 512084, 512503, 512921, 513336, 513750, 514162, 514572, 514981, 515387, 515792, 516195, 516597, 516997, 517395, 517791,
    518186, 518579, 518971, 519361, 519749, 520136, 520521, 520904, 521286, 521667, 522046, 522423, 522799, 523173, 523546, 523918,
];

/// `log2(x)` in units of 2^-16 (0 for 0), to about 1/256 of a bit.
#[inline(always)]
pub fn flog2(x: u32) -> (r: u64)
    ensures
        r <= 32 * 65536,
{
    proof {
        assert(forall|i: int| 0 <= i < 256 ==> #[trigger] LOG2[i] <= 8 * 65536) by (compute);
    }
    if x < 256 {
        LOG2[x as usize] as u64
    } else {
        let k = 31 - x.leading_zeros();
        let s = if k >= 7 && k <= 31 { k - 7 } else { 0 };
        let m = (x >> s) as usize;
        let m = if m < 256 { m } else { 255 };
        LOG2[m] as u64 + (s as u64) * 65536
    }
}

const SAT: u64 = 0x1000_0000_0000_0000;

/// The bits of a prefix code's header, roughly, for `nnz` symbols with a
/// code, in units of 2^-16 bits.
#[inline(always)]
pub fn hdr_cost(nnz: u64) -> (r: u64)
    ensures
        r < 0x100_0000_0000,
{
    let n = if nnz > 1024 { 1024 } else { nnz };
    let bits = if n <= 1 { 6 } else if n <= 4 { 4 + 9 * n } else { 50 + 3 * n };
    bits * 65536
}

/// `i * a`, for `i` and `a` up to 1024.
#[inline(always)]
fn mul_small(i: usize, a: usize) -> (r: usize)
    requires
        i <= 1024,
        a <= 1024,
    ensures
        r == i * a,
        r <= 0x10_0000,
{
    proof {
        assert(i * a <= 0x10_0000) by (nonlinear_arith)
            requires
                i <= 1024,
                a <= 1024,
        ;
    }
    i * a
}

/// The cost of coding the counts of rows `a` and (if `b` is not `a`) `b`
/// of `h` together, with `alpha` symbols per row, in units of 2^-16 bits,
/// header included. Rows outside `h` cost the most.
pub fn cost2(h: &Vec<u32>, alpha: usize, a: usize, b: usize) -> (r: u64) {
    if alpha > 1024 || a > 1024 || b > 1024 {
        return SAT;
    }
    let oa = mul_small(a, alpha);
    let ob = mul_small(b, alpha);
    if oa > h.len() || alpha > h.len() - oa || ob > h.len() || alpha > h.len() - ob {
        return SAT;
    }
    let mut tot: u64 = 0;
    let mut acc: u64 = 0;
    let mut nnz: u64 = 0;
    let mut s: usize = 0;
    while s < alpha
        invariant
            s <= alpha,
            alpha <= 1024,
            oa + alpha <= h.len(),
            ob + alpha <= h.len(),
            nnz <= s,
        decreases alpha - s,
    {
        let x = h[oa + s] as u64 + if a != b { h[ob + s] as u64 } else { 0 };
        if x > 0 {
            nnz = nnz + 1;
            let f = if x > 0xFFFF_FFFF { 0xFFFF_FFFF } else { x as u32 };
            let l = flog2(f);
            proof {
                assert(f as u64 * l <= 0xFFFF_FFFF * (32 * 65536)) by (nonlinear_arith)
                    requires
                        f <= 0xFFFF_FFFF,
                        l <= 32 * 65536,
                ;
            }
            if acc < SAT {
                acc = acc + f as u64 * l;
            }
            if tot < SAT {
                tot = tot + x;
            }
        }
        s = s + 1;
    }
    let t = if tot > 0xFFFF_FFFF { 0xFFFF_FFFF } else { tot as u32 };
    let lt = flog2(t);
    proof {
        assert(t as u64 * lt <= 0xFFFF_FFFF * (32 * 65536)) by (nonlinear_arith)
            requires
                t <= 0xFFFF_FFFF,
                lt <= 32 * 65536,
        ;
    }
    let whole = t as u64 * lt;
    let ent = if whole >= acc { whole - acc } else { 0 };
    ent + hdr_cost(nnz)
}

// ---------------------------------------------------------------------------
// Clustering
// ---------------------------------------------------------------------------

/// Groups the `n` rows of `h` (each `alpha` counts) into at most `maxc`
/// clusters, merging greedily the pair that costs least to merge while
/// merging saves bits (or there are too many). Rows end up added into the
/// first row of their cluster. Returns each row's cluster, numbered by
/// first use, and the number of clusters.
pub fn cluster(h: &mut Vec<u32>, n: usize, alpha: usize, maxc: usize) -> (r: (Vec<u8>, usize))
    requires
        1 <= n <= 1024,
        1 <= alpha <= 1024,
        1 <= maxc <= 256,
    ensures
        r.0@.len() == n,
        1 <= r.1 <= 256,
        forall|i: int| 0 <= i < n ==> (#[trigger] r.0@[i]) < r.1,
{
    let mut active: Vec<bool> = vec![false; n];
    let mut cost: Vec<u64> = vec![0u64; n];
    let mut parent: Vec<usize> = Vec::with_capacity(n);
    let mut nact: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 1024,
            1 <= alpha <= 1024,
            active@.len() == n,
            cost@.len() == n,
            parent@.len() == i,
            nact <= i,
            forall|k: int| 0 <= k < i ==> #[trigger] parent@[k] == k,
        decreases n - i,
    {
        parent.push(i);
        let off = mul_small(i, alpha);
        let mut any = false;
        if off <= h.len() && alpha <= h.len() - off {
            let mut s: usize = 0;
            while s < alpha
                invariant
                    s <= alpha,
                    off + alpha <= h.len(),
                decreases alpha - s,
            {
                if h[off + s] != 0 {
                    any = true;
                }
                s = s + 1;
            }
        }
        if any {
            active.set(i, true);
            cost.set(i, cost2(h, alpha, i, i));
            nact = nact + 1;
        }
        i = i + 1;
    }
    // The cost change of merging each pair: dm[i * n + j], for i < j.
    let nn = mul_small(n, n);
    let mut dm: Vec<i64> = vec![0i64; nn];
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 1024,
            active@.len() == n,
            cost@.len() == n,
            dm@.len() == nn,
        decreases n - i,
    {
        if active[i] {
            let mut j = i + 1;
            while j < n
                invariant
                    i < n,
                    i < j <= n,
                    n <= 1024,
                    active@.len() == n,
                    cost@.len() == n,
                    dm@.len() == nn,
                decreases n - j,
            {
                if active[j] {
                    let ij = mul_small(i, n) + j;
                    let c = cost2(h, alpha, i, j);
                    let d = delta(c, cost[i], cost[j]);
                    if ij < dm.len() {
                        dm.set(ij, d);
                    }
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    // Merge.
    let mut guard: usize = n;
    while nact > 1 && guard > 0
        invariant
            n <= 1024,
            1 <= alpha <= 1024,
            active@.len() == n,
            cost@.len() == n,
            parent@.len() == n,
            dm@.len() == nn,
            forall|k: int| 0 <= k < n ==> #[trigger] parent@[k] < n,
        decreases guard,
    {
        guard = guard - 1;
        let mut bi: usize = 0;
        let mut bj: usize = 0;
        let mut best: i64 = i64::MAX;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n <= 1024,
                active@.len() == n,
                dm@.len() == nn,
                bi < n || best == i64::MAX,
                bj < n || best == i64::MAX,
            decreases n - i,
        {
            if active[i] {
                let base = mul_small(i, n);
                let mut j = i + 1;
                while j < n
                    invariant
                        i < j <= n,
                        i < n,
                        n <= 1024,
                        base <= 0x10_0000,
                        active@.len() == n,
                        dm@.len() == nn,
                        bi < n || best == i64::MAX,
                        bj < n || best == i64::MAX,
                    decreases n - j,
                {
                    if active[j] && base + j < dm.len() {
                        let d = dm[base + j];
                        if d < best {
                            best = d;
                            bi = i;
                            bj = j;
                        }
                    }
                    j = j + 1;
                }
            }
            i = i + 1;
        }
        if best == i64::MAX || (nact <= maxc && best >= 0) {
            break;
        }
        // Row bj into row bi.
        let oi = mul_small(bi, alpha);
        let oj = mul_small(bj, alpha);
        if oi <= h.len() && alpha <= h.len() - oi && oj <= h.len() && alpha <= h.len() - oj {
            let mut s: usize = 0;
            while s < alpha
                invariant
                    s <= alpha,
                    oi + alpha <= h.len(),
                    oj + alpha <= h.len(),
                decreases alpha - s,
            {
                let x = h[oi + s] as u64 + h[oj + s] as u64;
                h.set(oi + s, if x > 0xFFFF_FFFF { 0xFFFF_FFFF } else { x as u32 });
                h.set(oj + s, 0);
                s = s + 1;
            }
        }
        active.set(bj, false);
        if nact > 0 {
            nact = nact - 1;
        }
        cost.set(bi, cost2(h, alpha, bi, bi));
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                parent@.len() == n,
                forall|q: int| 0 <= q < n ==> #[trigger] parent@[q] < n,
                bi < n,
                bj < n,
            decreases n - k,
        {
            if parent[k] == bj {
                parent.set(k, bi);
            }
            k = k + 1;
        }
        // The pairs with bi.
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n,
                n <= 1024,
                active@.len() == n,
                cost@.len() == n,
                dm@.len() == nn,
                bi < n,
            decreases n - k,
        {
            if k != bi && active[k] {
                let c = cost2(h, alpha, bi, k);
                let d = delta(c, cost[bi], cost[k]);
                let ij = if bi < k { mul_small(bi, n) + k } else { mul_small(k, n) + bi };
                if ij < dm.len() {
                    dm.set(ij, d);
                }
            }
            k = k + 1;
        }
    }
    // Number the clusters by first use; rows with no counts join cluster 0.
    let mut id: Vec<usize> = vec![usize::MAX; n];
    let mut map: Vec<u8> = vec![0u8; n];
    let mut nc: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 1024,
            parent@.len() == n,
            active@.len() == n,
            forall|k: int| 0 <= k < n ==> #[trigger] parent@[k] < n,
            id@.len() == n,
            map@.len() == n,
            nc <= 256,
            forall|k: int| 0 <= k < n ==> (#[trigger] map@[k]) < nc || map@[k] == 0,
        decreases n - i,
    {
        let root = parent[i];
        if active[root] {
            if id[root] == usize::MAX && nc < 256 {
                id.set(root, nc);
                nc = nc + 1;
            }
            let c = id[root];
            map.set(i, if c < nc && c < 256 { c as u8 } else { 0 });
        }
        i = i + 1;
    }
    if nc == 0 {
        nc = 1;
    }
    (map, nc)
}

/// `c - a - b`, clamped to `i64`.
#[inline(always)]
fn delta(c: u64, a: u64, b: u64) -> (r: i64) {
    let ab: u64 = if a < SAT && b < SAT { a + b } else { SAT };
    let c = if c < SAT { c } else { SAT };
    if c >= ab { (c - ab) as i64 } else { -((ab - c) as i64) }
}

// ---------------------------------------------------------------------------
// Counts
// ---------------------------------------------------------------------------

#[inline(always)]
fn bump(f: &mut Vec<u32>, i: usize)
    ensures
        final(f)@.len() == old(f)@.len(),
{
    if i < f.len() {
        let v = f[i];
        if v < 0xFFFF_FFFF {
            f.set(i, v + 1);
        }
    }
}

/// The distance context of insert-and-copy symbol `sym`.
#[inline(always)]
pub fn dctx_of(sym: u16) -> (r: usize)
    ensures
        r < 4,
{
    let (_ic, cc) = crate::cwrite::sym_codes_safe(sym);
    let cb = crate::spec::CPY_BASE[cc];
    if cb > 4 { 3 } else if cb >= 2 { (cb - 2) as usize } else { 0 }
}

/// Rows `0..nc` of clustered counts: row `map[i]` is the sum of the `n`
/// rows of `h` from `off`.
fn gather(h: &Vec<u32>, off: usize, n: usize, alpha: usize, map: &Vec<u8>, nc: usize) -> (r: Vec<u32>)
    requires
        1 <= nc <= 256,
        1 <= alpha <= 1024,
        n <= 1024,
    ensures
        r@.len() == nc * alpha,
{
    let len = mul_small(nc, alpha);
    let mut g: Vec<u32> = vec![0u32; len];
    let mut i: usize = 0;
    while i < n && i < map.len()
        invariant
            n <= 1024,
            1 <= alpha <= 1024,
            1 <= nc <= 256,
            g@.len() == len,
            len == nc * alpha,
        decreases n - i,
    {
        let c = map[i] as usize;
        let oi = mul_small(i, alpha);
        let b = mul_small(if c < 1024 { c } else { 1024 }, alpha);
        if oi <= h.len() - (if off <= h.len() { off } else { h.len() }) && off <= h.len() {
            let a = off + oi;
            if a <= h.len() && alpha <= h.len() - a && b <= g.len() && alpha <= g.len() - b {
                let mut s: usize = 0;
                while s < alpha
                    invariant
                        s <= alpha,
                        a + alpha <= h.len(),
                        b + alpha <= g.len(),
                        g@.len() == len,
                    decreases alpha - s,
                {
                    let x = g[b + s] as u64 + h[a + s] as u64;
                    g.set(b + s, if x > 0xFFFF_FFFF { 0xFFFF_FFFF } else { x as u32 });
                    s = s + 1;
                }
            }
        }
        i = i + 1;
    }
    g
}

/// The code lengths of each of the `nc` rows of `g`.
fn lens_rows(g: &Vec<u32>, nc: usize, alpha: usize) -> (r: Vec<Vec<u8>>)
    requires
        1 <= alpha <= 1024,
        nc <= 256,
{
    let mut v: Vec<Vec<u8>> = Vec::with_capacity(nc);
    let mut c: usize = 0;
    while c < nc
        invariant
            c <= nc,
            nc <= 256,
            1 <= alpha <= 1024,
        decreases nc - c,
    {
        let a = mul_small(c, alpha);
        let mut f: Vec<u32> = Vec::with_capacity(alpha);
        let mut s: usize = 0;
        while s < alpha
            invariant
                s <= alpha,
                alpha <= 1024,
                a <= 0x10_0000,
                f@.len() == s,
            decreases alpha - s,
        {
            f.push(if a + s < g.len() { g[a + s] } else { 0 });
            s = s + 1;
        }
        v.push(lens_of(&f));
        c = c + 1;
    }
    v
}

/// The total cost of the `nc` rows of `g`.
fn rows_cost(g: &Vec<u32>, nc: usize, alpha: usize) -> (r: u64)
    requires
        nc <= 256,
{
    let mut t: u64 = 0;
    let mut c: usize = 0;
    while c < nc
        invariant
            c <= nc,
            nc <= 256,
        decreases nc - c,
    {
        let x = cost2(g, alpha, c, c);
        if t < SAT && x < SAT {
            t = t + x;
        }
        c = c + 1;
    }
    t
}

/// Counts of the symbols `v` (below `alpha`).
fn hist_of(v: &Vec<u16>, alpha: usize) -> (r: Vec<u32>)
    ensures
        r@.len() == alpha,
{
    let mut f: Vec<u32> = vec![0u32; alpha];
    let mut i: usize = 0;
    while i < v.len()
        invariant
            f@.len() == alpha,
        decreases v@.len() - i,
    {
        bump(&mut f, v[i] as usize);
        i = i + 1;
    }
    f
}

// ---------------------------------------------------------------------------
// Block splitting
// ---------------------------------------------------------------------------

/// The settings of the planner.
#[derive(Clone)]
pub struct Knobs {
    /// Literal context modes to try (bit `m` for mode `m`).
    pub modes: u32,
    /// Trees per category at most.
    pub maxt: usize,
    /// Block types per category at most (1: no splitting).
    pub maxb: usize,
    /// Chunks per category at most, and the shortest chunk.
    pub maxch: usize,
    pub minch: usize,
}

/// Chunks of `chunk` symbols of `syms` (each below `alpha`), clustered
/// into at most `maxb` block types: the type of each chunk and the number
/// of types.
pub fn split(syms: &Vec<u16>, alpha: usize, chunk: usize, maxb: usize) -> (r: (Vec<u8>, usize))
    requires
        1 <= alpha <= 1024,
        chunk >= 1,
        1 <= maxb <= 256,
    ensures
        1 <= r.1 <= 256,
        forall|i: int| 0 <= i < r.0@.len() ==> (#[trigger] r.0@[i]) < r.1,
{
    let n = syms.len();
    if n == 0 {
        return (Vec::new(), 1);
    }
    let nch = (n - 1) / chunk + 1;
    if nch > 1024 || maxb == 1 {
        return (vec![0u8; if nch > 1024 { 0 } else { nch }], 1);
    }
    let mut h: Vec<u32> = vec![0u32; mul_small(nch, alpha)];
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == syms@.len(),
            nch <= 1024,
            chunk >= 1,
            1 <= alpha <= 1024,
        decreases n - i,
    {
        let c = i / chunk;
        let x = syms[i] as usize;
        if c < 1024 && x < alpha {
            bump(&mut h, mul_small(c, alpha) + x);
        }
        i = i + 1;
    }
    cluster(&mut h, nch, alpha, maxb)
}

/// The blocks that the chunk types `ct` (of `chunk` symbols each, `n` in
/// all) make, with `nbt` types: the category's plan.
pub fn blocks_of(ct: &Vec<u8>, chunk: usize, n: usize, nbt: usize) -> (r: CatPlan)
    requires
        1 <= nbt <= 256,
{
    if nbt < 2 || ct.len() == 0 || chunk == 0 {
        return cat1();
    }
    let mut types: Vec<u8> = Vec::new();
    let mut lens: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut done: usize = 0;
    while i < ct.len()
        invariant
            types@.len() == lens@.len(),
        decreases ct@.len() - i,
    {
        let t = ct[i];
        let mut j = i;
        while j < ct.len() && ct[j] == t
            invariant
                i <= j <= ct@.len(),
            decreases ct@.len() - j,
        {
            j = j + 1;
        }
        // Symbols in chunks i..j.
        let want: usize = if j - i <= 0x10_0000 / chunk { (j - i) * chunk } else { 0x10_0000 };
        let left = if n > done { n - done } else { 0 };
        let len = if want < left { want } else { left };
        if len > 0 {
            types.push(t);
            lens.push(if len > 0xFFFF_FFFF { 0xFFFF_FFFF } else { len as u32 });
            done = done + len;
        }
        i = if j > i { j } else { i + 1 };
    }
    if types.len() < 2 {
        return cat1();
    }
    // The block type and count codes, choosing symbols as the writer does.
    let mut tf: Vec<u32> = vec![0u32; nbt + 2];
    let mut lf: Vec<u32> = vec![0u32; 26];
    let mut bt: usize = 0;
    let mut bt2: usize = 1;
    let mut k: usize = 0;
    while k < types.len()
        invariant
            tf@.len() == nbt + 2,
            lf@.len() == 26,
            types@.len() == lens@.len(),
            nbt <= 256,
            bt < 256,
        decreases types@.len() - k,
    {
        let t = types[k] as usize;
        if k > 0 {
            let nxt = if bt + 1 >= nbt { bt + 1 - nbt } else { bt + 1 };
            let sym = if t == bt2 { 0 } else if t == nxt { 1 } else { t + 2 };
            bump(&mut tf, sym);
            bt2 = bt;
            bt = t;
        }
        if let Some(ls) = crate::mbw::blen_sym(lens[k]) {
            bump(&mut lf, ls);
        }
        k = k + 1;
    }
    CatPlan { nbt, types, lens, tl: lens_of(&tf), cl: lens_of(&lf) }
}

/// The chunk length for `n` symbols in at most `maxch` chunks, at least
/// `minch` long.
fn chunk_len(n: usize, maxch: usize, minch: usize) -> (r: usize)
    ensures
        r >= 1,
{
    let m = if maxch == 0 { 1 } else { maxch };
    let c = n / m + 1;
    let c = if c < minch { minch } else { c };
    if c == 0 { 1 } else { c }
}

/// The type of symbol `i` with chunk types `ct` of `chunk` symbols.
#[inline(always)]
fn type_at(ct: &Vec<u8>, chunk: usize, i: usize) -> (r: usize)
    requires
        chunk >= 1,
    ensures
        r < 256,
{
    let c = i / chunk;
    if c < ct.len() { ct[c] as usize } else { 0 }
}

/// The rows `t * 64 .. t * 64 + 64` of `h` (256 counts each).
fn rows64(h: &Vec<u32>, t: usize) -> (r: Vec<u32>)
    ensures
        r@.len() == 16384,
{
    let mut rows: Vec<u32> = Vec::with_capacity(16384);
    let o = if t < 1024 { t * 16384 } else { 0 };
    let mut j: usize = 0;
    while j < 16384
        invariant
            j <= 16384,
            rows@.len() == j,
            o <= 1024 * 16384,
        decreases 16384 - j,
    {
        rows.push(if o + j < h.len() { h[o + j] } else { 0 });
        j = j + 1;
    }
    rows
}

/// The whole plan of a meta-block: block types per category, a context mode
/// and context maps, and the trees.
pub fn plan_full(data: &[u8], start: usize, end: usize, cmds: &Vec<Cmd>, k: &Knobs) -> (r: MbPlan)
    requires
        start <= end <= data@.len(),
{
    let maxt = if k.maxt < 1 { 1 } else if k.maxt > 256 { 256 } else { k.maxt };
    let maxb = if k.maxb < 1 { 1 } else if k.maxb > 16 { 16 } else { k.maxb };
    // The three symbol streams, and where each literal is.
    let mut lpos: Vec<usize> = Vec::new();
    let mut lsym: Vec<u16> = Vec::new();
    let mut csym: Vec<u16> = Vec::new();
    let mut dsym: Vec<u16> = Vec::new();
    let mut dcx: Vec<u8> = Vec::new();
    let mut q = start;
    let mut i: usize = 0;
    while i < cmds.len()
        invariant
            start <= q <= end <= data@.len(),
        decreases cmds.len() - i,
    {
        let x = &cmds[i];
        let ins = x.ins as usize;
        if ins > end - q {
            break;
        }
        csym.push(x.sym);
        let mut kk = q;
        while kk < q + ins
            invariant
                q <= kk <= q + ins,
                q + ins <= end <= data@.len(),
            decreases q + ins - kk,
        {
            lpos.push(kk);
            lsym.push(data[kk] as u16);
            kk = kk + 1;
        }
        q = q + ins;
        if q >= end {
            break;
        }
        if x.sym >= 128 {
            dsym.push(x.dcode as u16);
            dcx.push(dctx_of(x.sym) as u8);
        }
        let cl = x.clen as usize;
        if cl > end - q {
            break;
        }
        q = q + cl;
        i = i + 1;
    }
    let single = plan_single(&hist_of(&lsym, 256), &hist_of(&csym, 704), &hist_of(&dsym, 64));
    // Block types.
    let lch = chunk_len(lsym.len(), k.maxch, if k.minch < 0x1000_0000 { k.minch * 4 } else { k.minch });
    let cch = chunk_len(csym.len(), k.maxch, k.minch);
    let dch = chunk_len(dsym.len(), k.maxch, k.minch);
    let (lct, nbl) = split(&lsym, 256, lch, maxb);
    let (cct, nbc) = split(&csym, 704, cch, maxb);
    let (dct, nbd) = split(&dsym, 64, dch, maxb);
    let lcat = blocks_of(&lct, lch, lsym.len(), nbl);
    let ccat = blocks_of(&cct, cch, csym.len(), nbc);
    let dcat = blocks_of(&dct, dch, dsym.len(), nbd);
    let nbl = if lcat.nbt >= 2 && lcat.nbt <= 16 { lcat.nbt } else { 1 };
    let nbc = if ccat.nbt >= 2 && ccat.nbt <= 16 { ccat.nbt } else { 1 };
    let nbd = if dcat.nbt >= 2 && dcat.nbt <= 16 { dcat.nbt } else { 1 };
    // The context mode, from all literals as one block.
    let mut lh: Vec<u32> = vec![0u32; 4 * 16384];
    let mut j: usize = 0;
    while j < lpos.len()
        invariant
            lh@.len() == 4 * 16384,
        decreases lpos@.len() - j,
    {
        let kk = lpos[j];
        if kk < data.len() {
            let b = data[kk] as usize;
            let p1: u8 = if kk >= 1 { data[kk - 1] } else { 0 };
            let p2: u8 = if kk >= 2 { data[kk - 2] } else { 0 };
            let mut m: usize = 0;
            while m < 4
                invariant
                    m <= 4,
                    b < 256,
                    lh@.len() == 4 * 16384,
                decreases 4 - m,
            {
                if (k.modes >> (m as u32)) & 1 == 1 {
                    let c = crate::decoder::lit_ctx(m, p1, p2);
                    bump(&mut lh, m * 16384 + c * 256 + b);
                }
                m = m + 1;
            }
        }
        j = j + 1;
    }
    let mut mode: usize = 0;
    let mut best: u64 = u64::MAX;
    let mut m: usize = 0;
    while m < 4
        invariant
            m <= 4,
            mode < 4,
            1 <= maxt <= 256,
        decreases 4 - m,
    {
        if (k.modes >> (m as u32)) & 1 == 1 {
            let mut rows = rows64(&lh, m);
            let orig = rows.clone();
            let (map, nc) = cluster(&mut rows, 64, 256, maxt);
            let g = gather(&orig, 0, 64, 256, &map, nc);
            let c = rows_cost(&g, nc, 256);
            if c < best {
                best = c;
                mode = m;
            }
        }
        m = m + 1;
    }
    // Literal counts per block type and context, clustered per block type,
    // then across.
    let mut th: Vec<u32> = vec![0u32; mul_small(nbl, 16) * 1024];
    let mut j: usize = 0;
    while j < lpos.len()
        invariant
            1 <= nbl <= 16,
            lch >= 1,
            mode < 4,
        decreases lpos@.len() - j,
    {
        let kk = lpos[j];
        if kk < data.len() {
            let b = data[kk] as usize;
            let p1: u8 = if kk >= 1 { data[kk - 1] } else { 0 };
            let p2: u8 = if kk >= 2 { data[kk - 2] } else { 0 };
            let t = type_at(&lct, lch, j);
            let t = if t < nbl { t } else { 0 };
            let c = crate::decoder::lit_ctx(mode, p1, p2);
            bump(&mut th, t * 16384 + c * 256 + b);
        }
        j = j + 1;
    }
    let nrows = nbl * 64;
    let mut map1: Vec<u8> = vec![0u8; nrows];
    let mut g1: Vec<u32> = Vec::new();
    let mut n1: usize = 0;
    let mut t: usize = 0;
    while t < nbl
        invariant
            1 <= nbl <= 16,
            nrows == nbl * 64,
            map1@.len() == nrows,
            n1 <= t * 256,
            t <= nbl,
        decreases nbl - t,
    {
        let mut rows = rows64(&th, t);
        let ro = rows.clone();
        let cap: usize = if nbl == 1 { 256 } else { 16 };
        let (mp, nc) = cluster(&mut rows, 64, 256, if nbl == 1 { maxt } else { 16 });
        let nc = if nc > cap { cap } else { nc };
        let g = gather(&ro, 0, 64, 256, &mp, nc);
        let mut c: usize = 0;
        while c < 64
            invariant
                c <= 64,
                map1@.len() == nrows,
                nrows == nbl * 64,
                t < nbl,
                n1 <= t * 256,
            decreases 64 - c,
        {
            let v = n1 + if c < mp.len() { mp[c] as usize } else { 0 };
            let at = t * 64 + c;
            if at < map1.len() {
                map1.set(at, if v < 256 { v as u8 } else { 0 });
            }
            c = c + 1;
        }
        let mut j: usize = 0;
        while j < g.len()
            decreases g@.len() - j,
        {
            g1.push(g[j]);
            j = j + 1;
        }
        n1 = n1 + nc;
        t = t + 1;
    }
    if n1 == 0 || n1 > 256 || g1.len() != n1 * 256 {
        return single;
    }
    let (map1, n1) = if nbl == 1 {
        (map1, n1)
    } else {
        // Then across block types.
        let (mp2, n2) = cluster(&mut g1, n1, 256, maxt);
        let mut map2 = map1.clone();
        let mut c: usize = 0;
        while c < map2.len()
            decreases map2@.len() - c,
        {
            let a = map2[c] as usize;
            map2.set(c, if a < mp2.len() { mp2[a] } else { 0 });
            c = c + 1;
        }
        (map2, n2)
    };
    let mut ok = map1.len() == nrows && n1 >= 1 && n1 <= 256;
    let mut c: usize = 0;
    while c < map1.len()
        decreases map1@.len() - c,
    {
        if map1[c] as usize >= n1 {
            ok = false;
        }
        c = c + 1;
    }
    if !ok || n1 < 1 || n1 > 256 {
        return single;
    }
    let lg = gather(&th, 0, nrows, 256, &map1, n1);
    let lt = lens_rows(&lg, n1, 256);
    // Command trees, one per block type.
    let mut ch: Vec<u32> = vec![0u32; mul_small(nbc, 704)];
    let mut j: usize = 0;
    while j < csym.len()
        invariant
            1 <= nbc <= 16,
            cch >= 1,
        decreases csym@.len() - j,
    {
        let t = type_at(&cct, cch, j);
        let t = if t < nbc { t } else { 0 };
        let x = csym[j] as usize;
        if x < 704 {
            bump(&mut ch, mul_small(t, 704) + x);
        }
        j = j + 1;
    }
    let ct = lens_rows(&ch, nbc, 704);
    // Distance counts per block type and context, clustered.
    let dn = nbd * 4;
    let mut dh: Vec<u32> = vec![0u32; mul_small(dn, 64)];
    let mut j: usize = 0;
    while j < dsym.len() && j < dcx.len()
        invariant
            1 <= nbd <= 16,
            dch >= 1,
        decreases dsym@.len() - j,
    {
        let t = type_at(&dct, dch, j);
        let t = if t < nbd { t } else { 0 };
        let x = dsym[j] as usize;
        let c = dcx[j] as usize;
        if x < 64 && c < 4 {
            bump(&mut dh, t * 256 + c * 64 + x);
        }
        j = j + 1;
    }
    let dorig = dh.clone();
    let (dmap, nd) = cluster(&mut dh, dn, 64, maxt);
    let dg = gather(&dorig, 0, dn, 64, &dmap, nd);
    let dt = lens_rows(&dg, nd, 64);
    let mut modes: Vec<u8> = Vec::new();
    let mut t: usize = 0;
    while t < nbl
        decreases nbl - t,
    {
        modes.push(mode as u8);
        t = t + 1;
    }
    MbPlan {
        cats: vec![if nbl >= 2 { lcat } else { cat1() }, if nbc >= 2 { ccat } else { cat1() }, if nbd >= 2 { dcat } else { cat1() }],
        modes,
        lmap: map1,
        ntl: n1,
        dmap,
        ntd: nd,
        lt,
        ct,
        dt,
    }
}

} // verus!
