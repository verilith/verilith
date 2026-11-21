//! Facts about the spec that the decoder's proofs build on.
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
// Code lengths
// ---------------------------------------------------------------------------

pub proof fn lemma_read_lens_len(
    cl: Seq<u8>,
    b: Seq<u8>,
    pos: int,
    size: nat,
    tokens: nat,
    sym: nat,
    prev: u8,
    lens: Seq<u8>,
)
    requires
        lens.len() == size,
    ensures
        read_lens(cl, b, pos, size, tokens, sym, prev, lens) matches Some((l, p)) ==> l.len() == size,
    decreases size - sym,
{
    if sym >= size || tokens == 0 {
    } else {
        match read_symbol(cl, b, pos) {
            None => {},
            Some((c, p)) => if c < 16 {
                lemma_read_lens_len(
                    cl,
                    b,
                    p,
                    size,
                    (tokens - 1) as nat,
                    sym + 1,
                    if c != 0 {
                        c as u8
                    } else {
                        prev
                    },
                    lens.update(sym as int, c as u8),
                );
            } else {
                let eb: nat = if c == 16 {
                    2
                } else if c == 17 {
                    3
                } else {
                    7
                };
                let off: nat = if c == 18 {
                    11
                } else {
                    3
                };
                match rd(b, p, eb) {
                    None => {},
                    Some(x) => {
                        let rep = x + off;
                        if sym + rep <= size {
                            lemma_read_lens_len(
                                cl,
                                b,
                                p + eb,
                                size,
                                (tokens - 1) as nat,
                                sym + rep,
                                prev,
                                set_run(
                                    lens,
                                    sym,
                                    rep,
                                    if c == 16 {
                                        prev
                                    } else {
                                        0u8
                                    },
                                ),
                            );
                        }
                    },
                }
            },
        }
    }
}

/// A code read for an alphabet has a length for each symbol.
pub proof fn lemma_read_code_len(b: Seq<u8>, pos: int, size: nat)
    ensures
        read_code(b, pos, size) matches Some((l, p)) ==> l.len() == size && valid_code(l),
{
    reveal_with_fuel(read_lens, 1);
    match rd(b, pos + 1, 4) {
        Some(x) => {
            let n = x + 4;
            let p = pos + 1 + 4 + 3 * n;
            match rd(b, p, 1) {
                Some(um) => if um == 1 {
                    match (rd(b, p + 1, 3)) {
                        Some(y) => {
                            let nb = 2 + 2 * y;
                            match rd(b, p + 4, nb) {
                                Some(z) => lemma_read_lens_len(
                                    cl_lens(b, pos + 5, n),
                                    b,
                                    p + 4 + nb,
                                    size,
                                    2 + z,
                                    0,
                                    8,
                                    zeros(size),
                                ),
                                None => {},
                            }
                        },
                        None => {},
                    }
                } else {
                    lemma_read_lens_len(cl_lens(b, pos + 5, n), b, p + 1, size, size, 0, 8, zeros(size));
                },
                None => {},
            }
        },
        None => {},
    }
}

/// The codes of a group have the group's alphabet sizes.
pub proof fn lemma_group_codes(b: Seq<u8>, pos: int, cb: nat, j: nat)
    ensures
        read_group_codes(b, pos, cb, j) matches Some((cs, p)) ==> cs.len() == j && forall|k: int|
            0 <= k < j ==> (#[trigger] cs[k]).len() == alphabet(k as nat, cb) && valid_code(cs[k]),
    decreases j,
{
    if j > 0 {
        lemma_group_codes(b, pos, cb, (j - 1) as nat);
        match read_group_codes(b, pos, cb, (j - 1) as nat) {
            None => {},
            Some((cs, p)) => {
                lemma_read_code_len(b, p, alphabet((j - 1) as nat, cb));
            },
        }
    }
}

/// The groups read have five codes each, of the right sizes.
pub open spec fn groups_shape(gs: Seq<Seq<Seq<u8>>>, cb: nat) -> bool {
    forall|i: int|
        0 <= i < gs.len() ==> (#[trigger] gs[i]).len() == 5 && forall|k: int|
            0 <= k < 5 ==> (#[trigger] gs[i][k]).len() == alphabet(k as nat, cb) && valid_code(
                gs[i][k],
            )
}

pub proof fn lemma_groups_shape(b: Seq<u8>, pos: int, cb: nat, n: nat)
    ensures
        read_groups(b, pos, cb, n) matches Some((gs, p)) ==> gs.len() == n && groups_shape(gs, cb),
    decreases n,
{
    if n > 0 {
        lemma_groups_shape(b, pos, cb, (n - 1) as nat);
        match read_groups(b, pos, cb, (n - 1) as nat) {
            None => {},
            Some((gs, p)) => {
                lemma_group_codes(b, p, cb, 5);
                match read_group_codes(b, p, cb, 5) {
                    None => {},
                    Some((g, q)) => {
                        let ng = gs.push(g);
                        assert forall|i: int| 0 <= i < ng.len() implies (#[trigger] ng[i]).len() == 5
                            && forall|k: int|
                            0 <= k < 5 ==> (#[trigger] ng[i][k]).len() == alphabet(k as nat, cb)
                                && valid_code(ng[i][k]) by {
                            if i < gs.len() {
                                assert(ng[i] == gs[i]);
                            }
                        }
                    },
                }
            },
        }
    }
}

/// Once a code of a group fails to read, the group does.
pub proof fn lemma_group_codes_fail(b: Seq<u8>, pos: int, cb: nat, j: nat, k: nat)
    requires
        j < k,
        read_group_codes(b, pos, cb, j) matches Some((cs, p)) && read_code(b, p, alphabet(j, cb)) is None,
    ensures
        read_group_codes(b, pos, cb, k) is None,
    decreases k,
{
    if k > j + 1 {
        lemma_group_codes_fail(b, pos, cb, j, (k - 1) as nat);
    }
}

/// Once a group fails to read, reading more groups does.
pub proof fn lemma_groups_fail(b: Seq<u8>, pos: int, cb: nat, j: nat, k: nat)
    requires
        j < k,
        read_groups(b, pos, cb, j) matches Some((gs, p)) && read_group_codes(b, p, cb, 5) is None,
    ensures
        read_groups(b, pos, cb, k) is None,
    decreases k,
{
    if k > j + 1 {
        lemma_groups_fail(b, pos, cb, j, (k - 1) as nat);
    }
}

pub proof fn lemma_groups_step(b: Seq<u8>, pos: int, cb: nat, i: nat, gl: Seq<Seq<Seq<u8>>>, p: int, cs: Seq<Seq<u8>>, q: int)
    requires
        read_groups(b, pos, cb, i) == Some((gl, p)),
        read_group_codes(b, p, cb, 5) == Some((cs, q)),
    ensures
        read_groups(b, pos, cb, i + 1) == Some((gl.push(cs), q)),
{
}

pub proof fn lemma_mul_step(i: nat, c: nat)
    ensures
        i * c + c == (i + 1) * c,
{
    lemma_mul_is_distributive_add_other_way(c as int, i as int, 1);
}

pub proof fn lemma_mul_le(i: nat, n: nat, c: nat)
    requires
        i <= n,
    ensures
        i * c <= n * c,
{
    lemma_mul_inequality(i as int, n as int, c as int);
}

// ---------------------------------------------------------------------------
// Positions only move forward
// ---------------------------------------------------------------------------

pub proof fn lemma_decode_from_len(lens: Seq<u8>, b: Seq<u8>, pos: int, l: nat)
    ensures
        decode_from(lens, b, pos, l) matches Some((s, k)) ==> k >= l,
    decreases MAX_BITS + 1 - l,
{
    if l > MAX_BITS || pos + l > nbits(b) {
    } else {
        lemma_decode_from_len(lens, b, pos, l + 1);
    }
}

pub proof fn lemma_read_symbol_adv(lens: Seq<u8>, b: Seq<u8>, pos: int)
    ensures
        read_symbol(lens, b, pos) matches Some((s, p)) ==> p >= pos,
{
    lemma_decode_from_len(lens, b, pos, 1);
}

pub proof fn lemma_read_lens_adv(
    cl: Seq<u8>,
    b: Seq<u8>,
    pos: int,
    size: nat,
    tokens: nat,
    sym: nat,
    prev: u8,
    lens: Seq<u8>,
)
    ensures
        read_lens(cl, b, pos, size, tokens, sym, prev, lens) matches Some((l, p)) ==> p >= pos,
    decreases size - sym,
{
    if sym >= size || tokens == 0 {
    } else {
        lemma_read_symbol_adv(cl, b, pos);
        match read_symbol(cl, b, pos) {
            None => {},
            Some((c, p)) => if c < 16 {
                lemma_read_lens_adv(
                    cl,
                    b,
                    p,
                    size,
                    (tokens - 1) as nat,
                    sym + 1,
                    if c != 0 {
                        c as u8
                    } else {
                        prev
                    },
                    lens.update(sym as int, c as u8),
                );
            } else {
                let eb: nat = if c == 16 {
                    2
                } else if c == 17 {
                    3
                } else {
                    7
                };
                let off: nat = if c == 18 {
                    11
                } else {
                    3
                };
                match rd(b, p, eb) {
                    None => {},
                    Some(x) => {
                        let rep = x + off;
                        if sym + rep <= size {
                            lemma_read_lens_adv(
                                cl,
                                b,
                                p + eb,
                                size,
                                (tokens - 1) as nat,
                                sym + rep,
                                prev,
                                set_run(
                                    lens,
                                    sym,
                                    rep,
                                    if c == 16 {
                                        prev
                                    } else {
                                        0u8
                                    },
                                ),
                            );
                        }
                    },
                }
            },
        }
    }
}

/// Reading a code takes at least one bit.
pub proof fn lemma_read_code_adv(b: Seq<u8>, pos: int, size: nat)
    ensures
        read_code(b, pos, size) matches Some((l, p)) ==> p >= pos + 1,
{
    match rd(b, pos + 1 + 4, 0) {
        _ => {},
    }
    match rd(b, pos + 1, 4) {
        Some(x) => {
            let n = x + 4;
            let p = pos + 1 + 4 + 3 * n;
            match rd(b, p, 1) {
                Some(um) => if um == 1 {
                    match (rd(b, p + 1, 3)) {
                        Some(y) => {
                            let nb = 2 + 2 * y;
                            match rd(b, p + 4, nb) {
                                Some(z) => lemma_read_lens_adv(
                                    cl_lens(b, pos + 5, n),
                                    b,
                                    p + 4 + nb,
                                    size,
                                    2 + z,
                                    0,
                                    8,
                                    zeros(size),
                                ),
                                None => {},
                            }
                        },
                        None => {},
                    }
                } else {
                    lemma_read_lens_adv(cl_lens(b, pos + 5, n), b, p + 1, size, size, 0, 8, zeros(size));
                },
                None => {},
            }
        },
        None => {},
    }
}

pub proof fn lemma_group_codes_adv(b: Seq<u8>, pos: int, cb: nat, j: nat)
    ensures
        read_group_codes(b, pos, cb, j) matches Some((cs, p)) ==> p >= pos + j,
    decreases j,
{
    if j > 0 {
        lemma_group_codes_adv(b, pos, cb, (j - 1) as nat);
        match read_group_codes(b, pos, cb, (j - 1) as nat) {
            None => {},
            Some((cs, p)) => {
                lemma_read_code_adv(b, p, alphabet((j - 1) as nat, cb));
            },
        }
    }
}

/// Each group takes at least five bits.
pub proof fn lemma_groups_adv(b: Seq<u8>, pos: int, cb: nat, n: nat)
    ensures
        read_groups(b, pos, cb, n) matches Some((gs, p)) ==> p >= pos + 5 * n,
    decreases n,
{
    if n > 0 {
        lemma_groups_adv(b, pos, cb, (n - 1) as nat);
        match read_groups(b, pos, cb, (n - 1) as nat) {
            None => {},
            Some((gs, p)) => {
                lemma_group_codes_adv(b, p, cb, 5);
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Pixels
// ---------------------------------------------------------------------------

/// Decoding gives exactly the image's pixels, and moves forward.
pub proof fn lemma_dp_len(b: Seq<u8>, pos: int, img: Img, out: Seq<u32>, cache: Seq<u32>)
    requires
        out.len() <= img.npix,
    ensures
        decode_pixels(b, pos, img, out, cache) matches Some((px, p)) ==> px.len() == img.npix && p >= pos,
    decreases img.npix - out.len(),
{
    if out.len() < img.npix {
        let g = group_at(img, out.len());
        lemma_read_symbol_adv(g[0], b, pos);
        match read_symbol(g[0], b, pos) {
            None => {},
            Some((s, p1)) => if s < 256 {
                lemma_read_symbol_adv(g[1], b, p1);
                match read_symbol(g[1], b, p1) {
                    None => {},
                    Some((r, p2)) => {
                        lemma_read_symbol_adv(g[2], b, p2);
                        match read_symbol(g[2], b, p2) {
                            None => {},
                            Some((bl, p3)) => {
                                lemma_read_symbol_adv(g[3], b, p3);
                                match read_symbol(g[3], b, p3) {
                                    None => {},
                                    Some((a, p4)) => {
                                        let c = argb(a, r, s, bl);
                                        lemma_dp_len(b, p4, img, out.push(c), cache_insert(cache, img.cb, c));
                                    },
                                }
                            },
                        }
                    },
                }
            } else if s < 280 {
                let ls = (s - 256) as nat;
                match rd(b, p1, pfx_extra(ls)) {
                    None => {},
                    Some(x) => {
                        let len = pfx_base(ls) + x + 1;
                        lemma_read_symbol_adv(g[4], b, p1 + pfx_extra(ls));
                        match read_symbol(g[4], b, p1 + pfx_extra(ls)) {
                            None => {},
                            Some((ds, p3)) => match rd(b, p3, pfx_extra(ds)) {
                                None => {},
                                Some(y) => {
                                    let d = plane_to_dist(img.w, pfx_base(ds) + y + 1);
                                    if d > out.len() || len > img.npix - out.len() {
                                    } else {
                                        let seg = copy_seg(out, d, len);
                                        lemma_dp_len(
                                            b,
                                            p3 + pfx_extra(ds),
                                            img,
                                            out + seg,
                                            cache_insert_all(cache, img.cb, seg),
                                        );
                                    }
                                },
                            },
                        }
                    },
                }
            } else {
                let c = cache[s - 280];
                lemma_dp_len(b, p1, img, out.push(c), cache_insert(cache, img.cb, c));
            },
        }
    }
}

/// The largest group referenced is at least each.
pub proof fn lemma_max_meta(meta: Seq<u32>, n: nat)
    ensures
        forall|t: int| 0 <= t < n ==> #[trigger] meta_code(meta[t]) <= max_meta(meta, n),
        max_meta(meta, n) < 0x1_0000,
    decreases n,
{
    if n > 0 {
        lemma_max_meta(meta, (n - 1) as nat);
    }
}

} // verus!
