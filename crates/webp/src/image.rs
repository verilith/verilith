//! Entropy-coded images (§5): the color cache, the meta prefix codes and the
//! prefix code groups, then the pixels. Proven to compute
//! `spec::decode_sub` and `spec::decode_main`.
use crate::bitreader::*;
use crate::codes::*;
use crate::pixels::*;
#[cfg(verus_only)]
use crate::slemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// Work charged per bit read: enough for a whole group, as each group takes
/// at least five bits.
pub open spec fn bit_cost() -> nat {
    group_cost(0)
}

pub proof fn lemma_bit_cost(cb: nat)
    ensures
        group_cost(cb) == bit_cost(),
        bit_cost() >= 1000,
        refill_cost() == 9,
{
    assert(crate::huffman::build_cost(crate::huffman::MAX_ALPHA as nat, 10) >= 0);
}

/// The color cache bits (`spec::read_cache_bits`).
fn read_cache_bits_exec(br: &mut BitReader, data: &[u8]) -> (r: Option<u32>)
    requires
        old(br).ok(data@),
    ensures
        final(br).ok(data@),
        match read_cache_bits(data@, old(br).pos()) {
            Some((cb, p)) => r == Some(cb as u32) && final(br).pos() == p,
            None => r is None,
        },
        r matches Some(cb) ==> cb <= 11 && final(br).pos() >= old(br).pos() + 1,
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + 2 * refill_cost(),
{
    let f = match br.take(data, 1) {
        Some(v) => v,
        None => return None,
    };
    if f == 0 {
        return Some(0);
    }
    let cb = match br.take(data, 4) {
        Some(v) => v,
        None => return None,
    };
    if 1 <= cb && cb <= 11 {
        Some(cb)
    } else {
        None
    }
}

/// Reading one bit charged at `bit_cost`, a successful step that moved on
/// pays for itself.
proof fn lemma_paid(w1: int, w0: int, p1: int, p0: int, c: int)
    requires
        w1 <= w0 + c,
        p1 >= p0 + 1,
        c <= bit_cost(),
    ensures
        w1 <= w0 + bit_cost() * (p1 - p0),
{
    assert(bit_cost() * (p1 - p0) >= bit_cost()) by (nonlinear_arith)
        requires
            p1 - p0 >= 1,
    ;
}

/// An entropy-coded image without meta prefix codes (`spec::decode_sub`).
pub fn decode_sub_exec(br: &mut BitReader, data: &[u8], w: usize, h: usize) -> (r: Result<Vec<u32>, Error>)
    requires
        old(br).ok(data@),
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        final(br).ok(data@),
        match decode_sub(data@, old(br).pos(), w as nat, h as nat) {
            Some((px, p)) => (r matches Ok(v) && v@ == px && final(br).pos() == p) || r == Err::<Vec<u32>, Error>(Error::OutOfMemory),
            None => r is Err,
        },
        r != Err::<Vec<u32>, Error>(Error::Unsupported),
        r matches Ok(v) ==> v@.len() == w * h,
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + pix_cost() * (w * h) as nat
            + bit_cost(),
{
    hide(decode_pixels);
    hide(group_cost);
    hide(read_groups);
    hide(decode_with);
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    proof {
        lemma_bit_cost(0);
    }
    let cb = match read_cache_bits_exec(br, data) {
        Some(c) => c,
        None => return Err(Error::Bitstream),
    };
    let ghost p1 = br.pos();
    let ghost w1 = br.work@;
    proof {
        lemma_paid(w1 as int, w0 as int, p1, p0, (2 * refill_cost()) as int);
        lemma_bit_cost(cb as nat);
    }
    let (groups, Ghost(gl)) = match read_groups_exec(br, data, cb, 1) {
        Some(x) => x,
        None => {
            proof {
                assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + bit_cost()) by (nonlinear_arith)
                    requires
                        br.work@ <= w1 + bit_cost() * (br.pos() - p1) + bit_cost(),
                        w1 <= w0 + bit_cost() * (p1 - p0),
                ;
                assert(pix_cost() * (w * h) as nat >= 0);
            }
            return Err(Error::Bitstream);
        },
    };
    let ghost p2 = br.pos();
    let ghost w2 = br.work@;
    proof {
        lemma_groups_shape(b, p1, cb as nat, 1);
        assert(w2 <= w0 + bit_cost() * (p2 - p0) + bit_cost()) by (nonlinear_arith)
            requires
                w2 <= w1 + bit_cost() * (p2 - p1) + bit_cost(),
                w1 <= w0 + bit_cost() * (p1 - p0),
        ;
    }
    let empty: Vec<u32> = Vec::new();
    let r = decode_image_data(br, data, w, h, cb, &groups, Ghost(gl), 0, &empty);
    proof {
        assert(empty@ =~= seq![]);
        lemma_decode_with_len(b, p2, w as nat, h as nat, cb as nat, gl, 0, seq![]);
        assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * (w * h) as nat + bit_cost())
            by (nonlinear_arith)
            requires
                br.work@ <= w2 + pix_cost() * (w * h) as nat,
                w2 <= w0 + bit_cost() * (p2 - p0) + bit_cost(),
                br.pos() >= p2,
                bit_cost() >= 0,
        ;
    }
    r
}

/// The largest group a meta prefix code names (`spec::max_meta`).
fn max_meta_exec(meta: &Vec<u32>) -> (r: usize)
    ensures
        r == max_meta(meta@, meta@.len()),
        r < 0x1_0000,
{
    let mut m: usize = 0;
    let mut i: usize = 0;
    proof {
        lemma_max_meta(meta@, 0);
    }
    while i < meta.len()
        invariant
            i <= meta@.len(),
            m == max_meta(meta@, i as nat),
            m < 0x1_0000,
        decreases meta@.len() - i,
    {
        let p = meta[i];
        let c = ((p >> 8) & 0xffff) as usize;
        proof {
            assert(((p >> 8u32) & 0xffffu32) == (p / 0x100) % 0x1_0000) by (bit_vector);
            assert(c == meta_code(meta@[i as int]));
        }
        if c > m {
            m = c;
        }
        i = i + 1;
    }
    m
}

/// Pixels decoded for the main image, counting its entropy image (no
/// larger than the image) twice: decoded, then scanned for the largest
/// group.
pub open spec fn main_pix(w: nat, h: nat) -> nat {
    3 * (w * h)
}

/// The ARGB image (`spec::decode_main`).
#[verifier::rlimit(50)]
pub fn decode_main_exec(br: &mut BitReader, data: &[u8], w: usize, h: usize) -> (r: Result<Vec<u32>, Error>)
    requires
        old(br).ok(data@),
        1 <= w <= 16384,
        1 <= h <= 16384,
    ensures
        final(br).ok(data@),
        match decode_main(data@, old(br).pos(), w as nat, h as nat) {
            Some((px, p)) => (r matches Ok(v) && v@ == px && final(br).pos() == p) || r == Err::<Vec<u32>, Error>(Error::OutOfMemory),
            None => r is Err,
        },
        r != Err::<Vec<u32>, Error>(Error::Unsupported),
        r matches Ok(v) ==> v@.len() == w * h,
        final(br).pos() >= old(br).pos(),
        final(br).work@ <= old(br).work@ + bit_cost() * (final(br).pos() - old(br).pos()) + pix_cost() * main_pix(
            w as nat,
            h as nat,
        ) + 2 * bit_cost(),
{
    hide(decode_pixels);
    hide(group_cost);
    hide(read_groups);
    hide(decode_with);
    let ghost b = data@;
    let ghost p0 = br.pos();
    let ghost w0 = br.work@;
    proof {
        lemma_bit_cost(0);
        assert(pix_cost() * main_pix(w as nat, h as nat) == 3 * (pix_cost() * (w * h) as nat)) by (nonlinear_arith);
        assert(pix_cost() * (w * h) as nat >= 0);
    }
    let cb = match read_cache_bits_exec(br, data) {
        Some(c) => c,
        None => return Err(Error::Bitstream),
    };
    let ghost p1 = br.pos();
    let ghost w1 = br.work@;
    proof {
        lemma_paid(w1 as int, w0 as int, p1, p0, (2 * refill_cost()) as int);
        lemma_bit_cost(cb as nat);
    }
    let m = match br.take(data, 1) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    let ghost p1m = br.pos();
    let ghost w1m = br.work@;
    proof {
        lemma_paid(br.work@ as int, w1 as int, p1m, p1, refill_cost() as int);
        assert(br.work@ <= w0 + bit_cost() * (p1m - p0)) by (nonlinear_arith)
            requires
                br.work@ <= w1 + bit_cost() * (p1m - p1),
                w1 <= w0 + bit_cost() * (p1 - p0),
        ;
    }
    if m == 0 {
        let (groups, Ghost(gl)) = match read_groups_exec(br, data, cb, 1) {
            Some(x) => x,
            None => {
                proof {
                    assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * main_pix(w as nat, h as nat)
                        + 2 * bit_cost()) by (nonlinear_arith)
                        requires
                            br.work@ <= w1m + bit_cost() * (br.pos() - p1m) + bit_cost(),
                            w1m <= w0 + bit_cost() * (p1m - p0),
                            pix_cost() * main_pix(w as nat, h as nat) >= 0,
                            bit_cost() >= 0,
                    ;
                }
                return Err(Error::Bitstream);
            },
        };
        let ghost p2 = br.pos();
        let ghost w2 = br.work@;
        proof {
            lemma_groups_shape(b, p1 + 1, cb as nat, 1);
            assert(w2 <= w0 + bit_cost() * (p2 - p0) + bit_cost()) by (nonlinear_arith)
                requires
                    w2 <= w1m + bit_cost() * (p2 - p1m) + bit_cost(),
                    w1m <= w0 + bit_cost() * (p1m - p0),
            ;
        }
        let empty: Vec<u32> = Vec::new();
        let r = decode_image_data(br, data, w, h, cb, &groups, Ghost(gl), 0, &empty);
        proof {
            assert(empty@ =~= seq![]);
            lemma_decode_with_len(b, p2, w as nat, h as nat, cb as nat, gl, 0, seq![]);
            assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * main_pix(w as nat, h as nat) + 2
                * bit_cost()) by (nonlinear_arith)
                requires
                    br.work@ <= w2 + pix_cost() * (w * h) as nat,
                    w2 <= w0 + bit_cost() * (p2 - p0) + bit_cost(),
                    br.pos() >= p2,
                    bit_cost() >= 0,
                    pix_cost() * main_pix(w as nat, h as nat) == 3 * (pix_cost() * (w * h) as nat),
                    pix_cost() * (w * h) as nat >= 0,
            ;
        }
        return r;
    }
    let x = match br.take(data, 3) {
        Some(v) => v,
        None => return Err(Error::Bitstream),
    };
    proof {
        verilith_core::bits::lemma_bits_bound(b, p1m, 3);
        vstd::arithmetic::power2::lemma2_to64();
    }
    let hb = x + 2;
    let ghost p1x = br.pos();
    let ghost w1x = br.work@;
    proof {
        lemma_paid(w1x as int, br.work@ as int, p1x, p1m, 0);
        assert(w1x <= w0 + bit_cost() * (p1x - p0)) by (nonlinear_arith)
            requires
                w1x <= w0 + bit_cost() * (p1m - p0) + refill_cost(),
                p1x == p1m + 3,
                refill_cost() <= bit_cost(),
        ;
        assert(hb <= 9) by {
            verilith_core::bits::lemma_bits_bound(b, p1m, 3);
            vstd::arithmetic::power2::lemma2_to64();
        }
    }
    let sw = subsample_exec(w, hb);
    let sh = subsample_exec(h, hb);
    let meta = match decode_sub_exec(br, data, sw, sh) {
        Ok(v) => v,
        Err(e) => {
            proof {
                assert(sw * sh <= w * h) by (nonlinear_arith)
                    requires
                        sw <= w,
                        sh <= h,
                ;
                assert(pix_cost() * (sw * sh) as nat <= pix_cost() * (w * h) as nat) by (nonlinear_arith)
                    requires
                        sw * sh <= w * h,
                ;
                assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * main_pix(w as nat, h as nat) + 2
                    * bit_cost()) by (nonlinear_arith)
                    requires
                        br.work@ <= w1x + bit_cost() * (br.pos() - p1x) + pix_cost() * (sw * sh) as nat
                            + bit_cost(),
                        w1x <= w0 + bit_cost() * (p1x - p0),
                        pix_cost() * (sw * sh) as nat <= pix_cost() * (w * h) as nat,
                        pix_cost() * main_pix(w as nat, h as nat) == 3 * (pix_cost() * (w * h) as nat),
                        pix_cost() * (w * h) as nat >= 0,
                        bit_cost() >= 0,
                ;
            }
            return Err(e);
        },
    };
    let ghost p2 = br.pos();
    let mx = max_meta_exec(&meta);
    br.work = Ghost(br.work@ + meta@.len());
    let ghost w2 = br.work@;
    proof {
        lemma_max_meta(meta@, meta@.len());
        assert(sw * sh <= w * h) by (nonlinear_arith)
            requires
                sw <= w,
                sh <= h,
        ;
        assert(pix_cost() * (sw * sh) as nat + meta@.len() <= 2 * (pix_cost() * (w * h) as nat)) by (nonlinear_arith)
            requires
                sw * sh <= w * h,
                meta@.len() == sw * sh,
                pix_cost() == 110,
        ;
        assert(w2 <= w0 + bit_cost() * (p2 - p0) + 2 * (pix_cost() * (w * h) as nat) + bit_cost()) by (nonlinear_arith)
            requires
                w2 <= w1x + bit_cost() * (p2 - p1x) + pix_cost() * (sw * sh) as nat + bit_cost() + meta@.len(),
                w1x <= w0 + bit_cost() * (p1x - p0),
                pix_cost() * (sw * sh) as nat + meta@.len() <= 2 * (pix_cost() * (w * h) as nat),
        ;
    }
    let n = mx + 1;
    let (groups, Ghost(gl)) = match read_groups_exec(br, data, cb, n) {
        Some(x) => x,
        None => {
            proof {
                assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * main_pix(w as nat, h as nat) + 2
                    * bit_cost()) by (nonlinear_arith)
                    requires
                        br.work@ <= w2 + bit_cost() * (br.pos() - p2) + bit_cost(),
                        w2 <= w0 + bit_cost() * (p2 - p0) + 2 * (pix_cost() * (w * h) as nat) + bit_cost(),
                        pix_cost() * main_pix(w as nat, h as nat) == 3 * (pix_cost() * (w * h) as nat),
                        pix_cost() * (w * h) as nat >= 0,
                ;
            }
            return Err(Error::Bitstream);
        },
    };
    let ghost p3 = br.pos();
    let ghost w3 = br.work@;
    proof {
        lemma_groups_shape(b, p2, cb as nat, n as nat);
        assert(meta_ok(w as nat, h as nat, hb as nat, meta@, gl.len()));
    }
    let r = decode_image_data(br, data, w, h, cb, &groups, Ghost(gl), hb, &meta);
    proof {
        lemma_decode_with_len(b, p3, w as nat, h as nat, cb as nat, gl, hb as nat, meta@);
        assert(br.work@ <= w0 + bit_cost() * (br.pos() - p0) + pix_cost() * main_pix(w as nat, h as nat) + 2
            * bit_cost()) by (nonlinear_arith)
            requires
                br.work@ <= w3 + pix_cost() * (w * h) as nat,
                w3 <= w2 + bit_cost() * (p3 - p2) + bit_cost(),
                w2 <= w0 + bit_cost() * (p2 - p0) + 2 * (pix_cost() * (w * h) as nat) + bit_cost(),
                br.pos() >= p3,
                bit_cost() >= 0,
                pix_cost() * main_pix(w as nat, h as nat) == 3 * (pix_cost() * (w * h) as nat),
        ;
    }
    r
}

} // verus!
