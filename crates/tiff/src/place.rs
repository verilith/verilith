//! Where each strip or tile goes in the output: the arithmetic behind
//! `spec::owner`. For strip `k` the bytes it fills are one run, from
//! `strip_start`; for tile `k` they are one run per tile row, from
//! `tile_dst`. Each "a" lemma says that the bytes a copy writes are owned by
//! the strip or tile being copied, at the offsets copied from; each "b"
//! lemma that every byte of the output is written by the copy of its
//! owner.
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

impl Params {
    /// What `spec::params` guarantees about the numbers.
    pub open spec fn wf(self) -> bool {
        &&& self.width >= 1
        &&& self.height >= 1
        &&& self.spp >= 1
        &&& 1 <= self.bps <= 32
        &&& self.rps >= 1
        &&& (self.planar == 1 || self.planar == 2)
        &&& compression_ok(self.compression)
        &&& (self.predictor == 1 || (self.predictor == 2 && (self.bps == 8 || self.bps == 16 || self.bps == 32)))
        &&& self.tiled ==> self.tw >= 1 && self.th >= 1 && (self.tw * self.sc() * self.bps) % 8 == 0
    }

    pub open spec fn plane_size(self) -> nat {
        self.height * self.row_bytes()
    }

    /// Where strip `k` starts in the output.
    pub open spec fn strip_start(self, k: nat) -> nat {
        (k / self.strips()) * self.plane_size() + (k % self.strips()) * (self.rps * self.row_bytes())
    }

    /// The bytes of each row of tile `k` that are inside the image.
    pub open spec fn tile_len(self, k: nat) -> nat {
        let tx = (k % (self.tiles_across() * self.tiles_down())) % self.tiles_across();
        let left = self.row_bytes() - tx * self.tile_row_bytes();
        if self.tile_row_bytes() <= left { self.tile_row_bytes() } else { left as nat }
    }

    /// Where row `yy` of tile `k` goes in the output.
    pub open spec fn tile_dst(self, k: nat, yy: nat) -> nat {
        let t = self.tiles_across() * self.tiles_down();
        let pl = k / t;
        let ty = (k % t) / self.tiles_across();
        let tx = (k % t) % self.tiles_across();
        pl * self.plane_size() + (ty * self.th + yy) * self.row_bytes() + tx * self.tile_row_bytes()
    }

    /// The tile row `ty` of tile `k`.
    pub open spec fn tile_y(self, k: nat) -> nat {
        ((k % (self.tiles_across() * self.tiles_down())) / self.tiles_across()) * self.th
    }
}

/// `x == q * d + r` with `0 <= r < d` pins down `x / d` and `x % d`.
proof fn lemma_qr(x: int, d: int, q: int, r: int)
    requires
        0 < d,
        0 <= r < d,
        x == q * d + r,
    ensures
        x / d == q,
        x % d == r,
{
    lemma_fundamental_div_mod_converse(x, d, q, r);
}

/// `x == (x / d) * d + x % d`, with the bounds.
proof fn lemma_dm(x: int, d: int)
    requires
        0 < d,
        0 <= x,
    ensures
        x == (x / d) * d + x % d,
        0 <= x % d < d,
        0 <= x / d,
{
    lemma_fundamental_div_mod(x, d);
    lemma_mul_is_commutative(d, x / d);
    lemma_mod_bound(x, d);
    lemma_div_pos_is_pos(x, d);
}

/// `j * a < b * a` from `j < b`, and the like.
proof fn lemma_lt_mul(j: int, b: int, a: int)
    requires
        0 <= j < b,
        0 < a,
    ensures
        j * a < b * a,
        (j + 1) * a <= b * a,
        j * a + a == (j + 1) * a,
{
    lemma_mul_strict_inequality(j, b, a);
    lemma_mul_inequality(j + 1, b, a);
    lemma_mul_is_distributive_add_other_way(a, j, 1);
}

/// `ceil(a / d) * d >= a`, and `j < ceil(a / d)` exactly when `j * d < a`.
pub proof fn lemma_div_up(a: int, d: int, j: int)
    requires
        0 < d,
        0 < a,
        0 <= j,
    ensures
        (j < div_up(a as nat, d as nat)) == (j * d < a),
{
    let s = div_up(a as nat, d as nat) as int;
    lemma_dm(a + d - 1, d);
    assert(s == (a + d - 1) / d);
    if j < s {
        // j * d <= (s - 1) * d <= a - 1.
        lemma_mul_inequality(j, s - 1, d);
        lemma_mul_is_distributive_sub_other_way(d, s, 1);
        assert((s - 1) * d == s * d - d) by {
            lemma_mul_is_distributive_sub(d, s, 1);
            lemma_mul_is_commutative(d, s);
            lemma_mul_is_commutative(d, s - 1);
        }
    } else {
        lemma_mul_inequality(s, j, d);
    }
}

pub proof fn lemma_row_bytes_pos(p: Params)
    requires
        p.wf(),
    ensures
        p.row_bytes() >= 1,
        p.plane_size() >= 1,
        p.sc() >= 1,
{
    lemma_mul_inequality(1, p.width as int, p.sc() as int);
    lemma_mul_inequality(1, (p.width * p.sc()) as int, p.bps as int);
    lemma_mul_inequality(1, p.height as int, p.row_bytes() as int);
}

/// Strip `k`'s bytes are its own, from `strip_start(k)`.
pub proof fn lemma_strip_a(p: Params, k: nat, t: nat)
    requires
        p.wf(),
        !p.tiled,
        k < p.chunks(),
        t < p.chunk_size(k),
    ensures
        p.strip_start(k) + t < p.image_size(),
        owner(p, (p.strip_start(k) + t) as int) == (k as int, t as int),
{
    reveal(owner);
    lemma_row_bytes_pos(p);
    let rb = p.row_bytes() as int;
    let ps = p.plane_size() as int;
    let s = p.strips() as int;
    let big_r = (p.rps * p.row_bytes()) as int;
    let h = p.height as int;
    let rps = p.rps as int;
    assert(s >= 1) by {
        lemma_div_up(h, rps, 0);
    }
    lemma_dm(k as int, s);
    let pl = k as int / s;
    let j = k as int % s;
    lemma_div_up(h, rps, j);
    assert(j * rps < h);
    lemma_mul_inequality(1, rps, rb);
    // The strip's size is at most R, and fits in the plane after j R.
    let size = p.chunk_size(k) as int;
    assert(size <= big_r && j * big_r + size <= ps) by {
        lemma_mul_is_associative(j, rps, rb);
        if (j + 1) * rps <= h {
            assert(size == big_r);
            lemma_mul_inequality((j + 1) * rps, h, rb);
            lemma_mul_is_distributive_add_other_way(rps, j, 1);
            lemma_mul_is_distributive_add_other_way(rb, j * rps, rps);
        } else {
            assert(size == (h - j * rps) * rb);
            lemma_mul_is_distributive_sub_other_way(rb, h, j * rps);
            lemma_mul_is_distributive_add(rps, j, 1);
            lemma_mul_is_commutative(rps, j + 1);
            lemma_mul_is_commutative(rps, j);
            lemma_mul_inequality(h - j * rps, rps, rb);
        }
    }
    let r = j * big_r + t;
    assert(0 <= r < ps) by {
        lemma_mul_nonnegative(j, big_r);
    }
    // The plane count bounds pl.
    assert(pl < p.planes()) by {
        lemma_mul_is_commutative(p.planes() as int, s);
        lemma_multiply_divide_lt(k as int, s, p.planes() as int);
        lemma_mul_is_commutative(s, p.planes() as int);
    }
    let i = pl * ps + r;
    assert(i == p.strip_start(k) + t);
    lemma_qr(i, ps, pl, r);
    lemma_qr(r, big_r, j, t as int);
    assert(i < p.image_size()) by {
        lemma_lt_mul(pl, p.planes() as int, ps);
        lemma_mul_is_commutative(p.planes() as int, ps);
    }
    assert(owner(p, i) == (pl * s + j, t as int));
}

/// Every byte of the output is in its strip's run.
pub proof fn lemma_strip_b(p: Params, i: int)
    requires
        p.wf(),
        !p.tiled,
        0 <= i < p.image_size(),
    ensures
        0 <= owner(p, i).0 < p.chunks(),
        0 <= owner(p, i).1 < p.chunk_size(owner(p, i).0 as nat),
        i == p.strip_start(owner(p, i).0 as nat) + owner(p, i).1,
{
    reveal(owner);
    lemma_row_bytes_pos(p);
    let rb = p.row_bytes() as int;
    let ps = p.plane_size() as int;
    let s = p.strips() as int;
    let big_r = (p.rps * p.row_bytes()) as int;
    let h = p.height as int;
    let rps = p.rps as int;
    lemma_mul_inequality(1, rps, rb);
    lemma_dm(i, ps);
    let pl = i / ps;
    let r = i % ps;
    lemma_dm(r, big_r);
    let j = r / big_r;
    let t = r % big_r;
    assert(pl < p.planes()) by {
        lemma_mul_is_commutative(p.planes() as int, ps);
        lemma_multiply_divide_lt(i, ps, p.planes() as int);
    }
    // j R <= r < h rb, so j rps < h.
    assert(j * rps < h) by {
        lemma_mul_is_associative(j, rps, rb);
        if j * rps >= h {
            lemma_mul_inequality(h, j * rps, rb);
        }
    }
    lemma_div_up(h, rps, j);
    let k = pl * s + j;
    assert(k < p.chunks()) by {
        lemma_lt_mul(pl, p.planes() as int, s);
        lemma_mul_is_commutative(p.planes() as int, s);
    }
    assert(0 <= k) by {
        lemma_mul_nonnegative(pl, s);
    }
    lemma_qr(k, s, pl, j);
    assert(owner(p, i) == (k, t));
    // t is inside the strip.
    let size = p.chunk_size(k as nat) as int;
    if (j + 1) * rps > h {
        assert(size == (h - j * rps) * rb);
        lemma_mul_is_distributive_sub_other_way(rb, h, j * rps);
        lemma_mul_is_associative(j, rps, rb);
    }
}

/// Row `yy` of tile `k`, inside the image, holds bytes of tile `k`.
pub proof fn lemma_tile_a(p: Params, k: nat, yy: nat, xx: nat)
    requires
        p.wf(),
        p.tiled,
        k < p.chunks(),
        yy < p.th,
        p.tile_y(k) + yy < p.height,
        xx < p.tile_len(k),
    ensures
        p.tile_dst(k, yy) + xx < p.image_size(),
        owner(p, (p.tile_dst(k, yy) + xx) as int) == (k as int, (yy * p.tile_row_bytes() + xx) as int),
        yy * p.tile_row_bytes() + xx < p.chunk_size(k),
{
    reveal(owner);
    lemma_row_bytes_pos(p);
    let rb = p.row_bytes() as int;
    let trb = p.tile_row_bytes() as int;
    let ps = p.plane_size() as int;
    let ta = p.tiles_across() as int;
    let td = p.tiles_down() as int;
    let th = p.th as int;
    let tt = ta * td;
    assert(ta >= 1 && td >= 1) by {
        lemma_div_up(p.width as int, p.tw as int, 0);
        lemma_div_up(p.height as int, th, 0);
    }
    lemma_mul_inequality(1, ta, td);
    lemma_dm(k as int, tt);
    let pl = k as int / tt;
    let m = k as int % tt;
    lemma_dm(m, ta);
    let ty = m / ta;
    let tx = m % ta;
    assert(trb >= 1) by {
        lemma_mul_inequality(1, p.tw as int, p.sc() as int);
        lemma_mul_inequality(1, (p.tw * p.sc()) as int, p.bps as int);
        lemma_dm((p.tw * p.sc() * p.bps) as int, 8);
    }
    // tx trb < rb: the tile starts inside the row.
    assert(tx * trb < rb) by {
        lemma_tile_starts(p, tx);
    }
    let y = ty * th + yy as int;
    let x = tx * trb + xx as int;
    assert(0 <= x < rb) by {
        lemma_mul_nonnegative(tx, trb);
    }
    let r = y * rb + x;
    assert(0 <= y < p.height);
    assert(0 <= r < ps) by {
        lemma_mul_nonnegative(y, rb);
        lemma_lt_mul(y, p.height as int, rb);
    }
    assert(pl < p.planes()) by {
        lemma_mul_is_commutative(p.planes() as int, tt);
        lemma_multiply_divide_lt(k as int, tt, p.planes() as int);
    }
    let i = pl * ps + r;
    assert(i == p.tile_dst(k, yy) + xx) by {
        lemma_mul_is_distributive_add_other_way(rb, ty * th, yy as int);
    }
    assert(i < p.image_size()) by {
        lemma_lt_mul(pl, p.planes() as int, ps);
        lemma_mul_is_commutative(p.planes() as int, ps);
    }
    lemma_qr(i, ps, pl, r);
    lemma_qr(r, rb, y, x);
    lemma_qr(y, th, ty, yy as int);
    lemma_qr(x, trb, tx, xx as int);
    assert(owner(p, i) == (pl * tt + ty * ta + tx, yy * trb + xx as int));
    assert(pl * tt + ty * ta + tx == k);
    assert(yy * trb + xx < p.chunk_size(k)) by {
        lemma_lt_mul(yy as int, th, trb);
        lemma_mul_is_commutative(th, trb);
    }
}

/// Tile column `tx` starts inside the image's row.
pub proof fn lemma_tile_starts_pub(p: Params, tx: int)
    requires
        p.wf(),
        p.tiled,
        0 <= tx < p.tiles_across(),
    ensures
        tx * p.tile_row_bytes() < p.row_bytes(),
{
    lemma_tile_starts(p, tx);
}

proof fn lemma_tile_starts(p: Params, tx: int)
    requires
        p.wf(),
        p.tiled,
        0 <= tx < p.tiles_across(),
    ensures
        tx * p.tile_row_bytes() < p.row_bytes(),
{
    let e = (p.sc() * p.bps) as int;
    let tw = p.tw as int;
    let w = p.width as int;
    lemma_div_up(w, tw, tx);
    // tx tw < w, so tx tw e <= (w - 1) e, and (tx tw e) / 8 <= ((w - 1) e) / 8 < ceil(w e / 8).
    lemma_mul_inequality(1, p.sc() as int, p.bps as int);
    lemma_mul_inequality(tx * tw, w - 1, e);
    lemma_mul_is_associative(tw, p.sc() as int, p.bps as int);
    lemma_mul_is_associative(w, p.sc() as int, p.bps as int);
    lemma_dm(tw * e, 8);
    assert((tw * e) % 8 == 0);
    let trb = (tw * e) / 8;
    assert(tx * trb * 8 == tx * tw * e) by {
        lemma_mul_is_associative(tx, trb, 8);
        lemma_mul_is_associative(tx, tw, e);
        lemma_mul_is_commutative(trb, 8);
    }
    assert(tx * trb * 8 <= (w - 1) * e);
    lemma_mul_is_distributive_sub_other_way(e, w, 1);
    // (w e + 7) / 8 * 8 > w e - 1 >= tx trb 8 + ... : from tx trb 8 <= w e - e <= w e - 1.
    lemma_dm(w * e + 7, 8);
    assert(tx * trb * 8 < ((w * e + 7) / 8) * 8);
    lemma_mul_strict_inequality_converse(tx * trb, (w * e + 7) / 8, 8);
}

/// Every byte of the output is in a row of its tile.
pub proof fn lemma_tile_b(p: Params, i: int)
    requires
        p.wf(),
        p.tiled,
        0 <= i < p.image_size(),
    ensures
        ({
            let (k, t) = owner(p, i);
            let trb = p.tile_row_bytes() as int;
            &&& 0 <= k < p.chunks()
            &&& 0 <= t
            &&& t / trb < p.th
            &&& p.tile_y(k as nat) + t / trb < p.height
            &&& t % trb < p.tile_len(k as nat)
            &&& i == p.tile_dst(k as nat, (t / trb) as nat) + t % trb
        }),
{
    reveal(owner);
    lemma_row_bytes_pos(p);
    let rb = p.row_bytes() as int;
    let trb = p.tile_row_bytes() as int;
    let ps = p.plane_size() as int;
    let ta = p.tiles_across() as int;
    let td = p.tiles_down() as int;
    let th = p.th as int;
    let tt = ta * td;
    assert(trb >= 1) by {
        lemma_mul_inequality(1, p.tw as int, p.sc() as int);
        lemma_mul_inequality(1, (p.tw * p.sc()) as int, p.bps as int);
        lemma_dm((p.tw * p.sc() * p.bps) as int, 8);
    }
    lemma_dm(i, ps);
    let pl = i / ps;
    let r = i % ps;
    lemma_dm(r, rb);
    let y = r / rb;
    let x = r % rb;
    lemma_dm(y, th);
    let ty = y / th;
    let yy = y % th;
    lemma_dm(x, trb);
    let tx = x / trb;
    let xx = x % trb;
    assert(pl < p.planes()) by {
        lemma_mul_is_commutative(p.planes() as int, ps);
        lemma_multiply_divide_lt(i, ps, p.planes() as int);
    }
    assert(y < p.height) by {
        lemma_mul_is_commutative(rb, p.height as int);
        lemma_multiply_divide_lt(r, rb, p.height as int);
    }
    assert(ty < td) by {
        lemma_div_up(p.height as int, th, ty);
        lemma_mul_inequality(ty, ty, th);
    }
    assert(tx < ta) by {
        lemma_tile_ends(p, x, tx);
    }
    let m = ty * ta + tx;
    assert(0 <= m < tt) by {
        lemma_mul_nonnegative(ty, ta);
        lemma_lt_mul(ty, td, ta);
        lemma_mul_is_commutative(td, ta);
    }
    let k = pl * tt + m;
    assert(0 <= k < p.chunks()) by {
        lemma_mul_nonnegative(pl, tt);
        lemma_lt_mul(pl, p.planes() as int, tt);
        lemma_mul_is_commutative(p.planes() as int, tt);
    }
    lemma_qr(k, tt, pl, m);
    lemma_qr(m, ta, ty, tx);
    let t = yy * trb + xx;
    assert(owner(p, i) == (k, t));
    lemma_mul_nonnegative(yy, trb);
    lemma_qr(t, trb, yy, xx);
    assert(p.tile_y(k as nat) == ty * th);
    // xx < tile_len: xx < trb, and tx trb + xx = x < rb.
    assert(i == p.tile_dst(k as nat, yy as nat) + xx) by {
        lemma_mul_is_distributive_add_other_way(rb, ty * th, yy);
    }
}

/// A byte of a row is in a tile column that exists.
proof fn lemma_tile_ends(p: Params, x: int, tx: int)
    requires
        p.wf(),
        p.tiled,
        0 <= x < p.row_bytes(),
        p.tile_row_bytes() >= 1,
        tx == x / p.tile_row_bytes() as int,
    ensures
        tx < p.tiles_across(),
{
    let e = (p.sc() * p.bps) as int;
    let tw = p.tw as int;
    let w = p.width as int;
    let trb = p.tile_row_bytes() as int;
    lemma_dm(x, trb);
    lemma_div_pos_is_pos(x, trb);
    lemma_mul_is_associative(tw, p.sc() as int, p.bps as int);
    lemma_mul_is_associative(w, p.sc() as int, p.bps as int);
    lemma_dm(tw * e, 8);
    // tx trb 8 <= x 8 < ceil(w e / 8) 8 <= w e + 7, and tx trb 8 = tx tw e.
    assert(tx * trb <= x);
    lemma_dm(w * e + 7, 8);
    lemma_mul_inequality(x + 1, (w * e + 7) / 8, 8);
    lemma_mul_inequality(tx * trb, x, 8);
    assert(tx * trb * 8 == tx * tw * e) by {
        lemma_mul_is_associative(tx, trb, 8);
        lemma_mul_is_associative(tx, tw, e);
        lemma_mul_is_commutative(trb, 8);
    }
    // tx tw e <= x 8 <= w e + 7 - 8 < w e, so tx tw < w.
    lemma_mul_is_distributive_add_other_way(8, x, 1);
    lemma_mul_is_commutative(x + 1, 8);
    lemma_mul_is_commutative((w * e + 7) / 8, 8);
    assert(tx * tw * e < w * e);
    lemma_mul_inequality(1, p.sc() as int, p.bps as int);
    lemma_mul_strict_inequality_converse(tx * tw, w, e);
    lemma_div_up(w, tw, tx);
}

} // verus!
