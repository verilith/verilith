//! Conversions of the decoders' pixel formats to 8-bit RGBA, each proven
//! to compute its `*_spec` function byte for byte.
use vstd::prelude::*;

verus! {

/// Grey (`nc == 1`) or RGB (`nc == 3`) pixels as RGBA: grey copied to red,
/// green and blue, alpha 255.
pub open spec fn expand_spec(px: Seq<u8>, nc: int) -> Seq<u8> {
    Seq::new(
        (px.len() as int / nc * 4) as nat,
        |k: int|
            if k % 4 == 3 {
                255u8
            } else if nc == 1 {
                px[k / 4]
            } else {
                px[(k / 4) * 3 + k % 4]
            },
    )
}

/// One-byte or three-byte pixels as RGBA (`expand_spec`).
pub fn expand(px: &[u8], nc: usize) -> (r: Vec<u8>)
    requires
        nc == 1 || nc == 3,
        px@.len() as int % nc as int == 0,
        px@.len() as int / nc as int * 4 <= usize::MAX,
    ensures
        r@ == expand_spec(px@, nc as int),
{
    let n = px.len() / nc;
    let mut out: Vec<u8> = Vec::with_capacity(n * 4);
    let mut i: usize = 0;
    while i < n
        invariant
            nc == 1 || nc == 3,
            n == px@.len() as int / nc as int,
            px@.len() as int % nc as int == 0,
            n * 4 <= usize::MAX,
            i <= n,
            out@.len() == i * 4,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == expand_spec(px@, nc as int)[k],
        decreases n - i,
    {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(px@.len() as int, nc as int);
            assert(i * nc + nc <= px@.len()) by (nonlinear_arith)
                requires
                    i < n,
                    px@.len() == nc * n,
            ;
        }
        let ghost before = out@;
        if nc == 1 {
            let g = px[i];
            out.push(g);
            out.push(g);
            out.push(g);
        } else {
            out.push(px[i * 3]);
            out.push(px[i * 3 + 1]);
            out.push(px[i * 3 + 2]);
        }
        out.push(255);
        proof {
            assert forall|k: int| 0 <= k < out@.len() implies #[trigger] out@[k] == expand_spec(px@, nc as int)[k] by {
                if k >= before.len() {
                    let c = k - i * 4;
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k, 4, i as int, c);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(out@ =~= expand_spec(px@, nc as int));
    }
    out
}

/// Byte `c` of a WebP ARGB pixel (`0xAARRGGBB`) as RGBA.
pub open spec fn argb_byte(p: u32, c: int) -> u8 {
    if c == 0 {
        ((p >> 16) & 0xff) as u8
    } else if c == 1 {
        ((p >> 8) & 0xff) as u8
    } else if c == 2 {
        (p & 0xff) as u8
    } else {
        (p >> 24) as u8
    }
}

pub open spec fn argb_spec(px: Seq<u32>) -> Seq<u8> {
    Seq::new((px.len() * 4) as nat, |k: int| argb_byte(px[k / 4], k % 4))
}

/// ARGB words as RGBA bytes (`argb_spec`).
pub fn from_argb(px: &[u32]) -> (r: Vec<u8>)
    requires
        px@.len() * 4 <= usize::MAX,
    ensures
        r@ == argb_spec(px@),
{
    let n = px.len();
    let mut out: Vec<u8> = Vec::with_capacity(n * 4);
    let mut i: usize = 0;
    while i < n
        invariant
            n == px@.len(),
            n * 4 <= usize::MAX,
            i <= n,
            out@.len() == i * 4,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == argb_spec(px@)[k],
        decreases n - i,
    {
        let p = px[i];
        let ghost before = out@;
        out.push(((p >> 16) & 0xff) as u8);
        out.push(((p >> 8) & 0xff) as u8);
        out.push((p & 0xff) as u8);
        out.push((p >> 24) as u8);
        proof {
            assert forall|k: int| 0 <= k < out@.len() implies #[trigger] out@[k] == argb_spec(px@)[k] by {
                if k >= before.len() {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k, 4, i as int, k - i * 4);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(out@ =~= argb_spec(px@));
    }
    out
}

/// Byte `c` of a GIF pixel with colour index `i`, through colour table
/// `t` (3 bytes per entry). An index past the table is black (as giflib's
/// zero-filled colour map); the transparent index has alpha 0.
pub open spec fn indexed_byte(t: Seq<u8>, tr: Option<u8>, i: u8, c: int) -> u8 {
    if c == 3 {
        if tr == Some(i) { 0u8 } else { 255u8 }
    } else if 3 * (i as int) + 3 <= t.len() {
        t[3 * i + c]
    } else {
        0u8
    }
}

pub open spec fn indexed_spec(px: Seq<u8>, t: Seq<u8>, tr: Option<u8>) -> Seq<u8> {
    Seq::new((px.len() * 4) as nat, |k: int| indexed_byte(t, tr, px[k / 4], k % 4))
}

/// Colour indices as RGBA bytes (`indexed_spec`).
pub fn from_indexed(px: &[u8], t: &[u8], tr: Option<u8>) -> (r: Vec<u8>)
    requires
        px@.len() * 4 <= usize::MAX,
    ensures
        r@ == indexed_spec(px@, t@, tr),
{
    let n = px.len();
    let mut out: Vec<u8> = Vec::with_capacity(n * 4);
    let mut i: usize = 0;
    while i < n
        invariant
            n == px@.len(),
            n * 4 <= usize::MAX,
            i <= n,
            out@.len() == i * 4,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == indexed_spec(px@, t@, tr)[k],
        decreases n - i,
    {
        let x = px[i];
        let j = 3 * x as usize;
        let ghost before = out@;
        if j + 3 <= t.len() {
            out.push(t[j]);
            out.push(t[j + 1]);
            out.push(t[j + 2]);
        } else {
            out.push(0);
            out.push(0);
            out.push(0);
        }
        out.push(if tr == Some(x) { 0 } else { 255 });
        proof {
            assert forall|k: int| 0 <= k < out@.len() implies #[trigger] out@[k] == indexed_spec(px@, t@, tr)[k] by {
                if k >= before.len() {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k, 4, i as int, k - i * 4);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(out@ =~= indexed_spec(px@, t@, tr));
    }
    out
}

/// Byte `c` of an RGBA pixel with alpha flattened onto background
/// `(br, bg, bb)`: `(v * a + b * (255 - a) + 127) / 255`, alpha 255.
pub open spec fn flat_byte(p: Seq<u8>, k: int, bg: Seq<u8>) -> u8 {
    let c = k % 4;
    if c == 3 {
        255u8
    } else {
        let a = p[k - c + 3] as int;
        ((p[k] as int * a + bg[c] as int * (255 - a) + 127) / 255) as u8
    }
}

pub open spec fn flatten_spec(px: Seq<u8>, bg: Seq<u8>) -> Seq<u8> {
    Seq::new(px.len(), |k: int| flat_byte(px, k, bg))
}

/// Flattens alpha onto a background colour (`flatten_spec`), for output
/// formats without alpha and for `background` requests.
pub fn flatten(px: &[u8], bg: [u8; 3]) -> (r: Vec<u8>)
    requires
        px@.len() % 4 == 0,
    ensures
        r@ == flatten_spec(px@, bg@),
{
    let n = px.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == px@.len(),
            n % 4 == 0,
            i <= n,
            i % 4 == 0,
            out@.len() == i,
            forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == flatten_spec(px@, bg@)[k],
        decreases n - i,
    {
        let a = px[i + 3] as u32;
        let ghost before = out@;
        let mut c: usize = 0;
        while c < 3
            invariant
                n == px@.len(),
                i + 4 <= n,
                i % 4 == 0,
                a == px@[i + 3],
                c <= 3,
                out@.len() == i + c,
                forall|k: int| 0 <= k < out@.len() ==> #[trigger] out@[k] == flatten_spec(px@, bg@)[k],
            decreases 3 - c,
        {
            let v = px[i + c] as u32;
            let b = bg[c] as u32;
            proof {
                assert(v * a + b * (255 - a) + 127 <= 255 * 255 + 127) by (nonlinear_arith)
                    requires
                        v <= 255,
                        b <= 255,
                        a <= 255,
                ;
                assert(v * a + b * (255 - a) <= 255 * a + 255 * (255 - a)) by (nonlinear_arith)
                    requires
                        v <= 255,
                        b <= 255,
                        a <= 255,
                ;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, 4);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((i + c) as int, 4, (i / 4) as int, c as int);
            }
            out.push(((v * a + b * (255 - a) + 127) / 255) as u8);
            c = c + 1;
        }
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i as int, 4);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((i + 3) as int, 4, (i / 4) as int, 3);
        }
        out.push(255);
        i = i + 4;
    }
    proof {
        assert(out@ =~= flatten_spec(px@, bg@));
    }
    out
}

} // verus!
