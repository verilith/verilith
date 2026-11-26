//! Reconstructs every pass's reduced image into one buffer, proven to
//! compute `spec::pass_images`.
use crate::chunks::Header;
use crate::geom::*;
use crate::spec::*;
use crate::unfilter::*;
use crate::work::Meter;
use vstd::prelude::*;

verus! {

/// Bytes of pass `p`'s reconstructed image.
pub open spec fn img_size(h: Ihdr, p: nat) -> nat {
    if pass_size(h, p) == 0 {
        0
    } else {
        pass_h(h, p) * row_bytes(h, pass_w(h, p))
    }
}

/// Where pass `p`'s image starts in the buffer.
pub open spec fn img_off(h: Ihdr, p: nat) -> nat
    decreases p,
{
    if p == 0 {
        0
    } else {
        img_off(h, (p - 1) as nat) + img_size(h, (p - 1) as nat)
    }
}

pub proof fn lemma_img_le_pass(h: Ihdr, p: nat)
    ensures
        img_size(h, p) <= pass_size(h, p),
        img_off(h, p) <= pass_off(h, p),
    decreases p,
{
    if pass_size(h, p) != 0 {
        let a = pass_h(h, p);
        let b = row_bytes(h, pass_w(h, p));
        assert(a * b <= a * (1 + b)) by (nonlinear_arith);
    }
    if p > 0 {
        lemma_img_le_pass(h, (p - 1) as nat);
    }
}

pub proof fn lemma_off_mono(h: Ihdr, p: nat, q: nat)
    requires
        p <= q,
    ensures
        pass_off(h, p) <= pass_off(h, q),
        img_off(h, p) <= img_off(h, q),
        p < q ==> pass_off(h, p) + pass_size(h, p) <= pass_off(h, q),
        p < q ==> img_off(h, p) + img_size(h, p) <= img_off(h, q),
    decreases q - p,
{
    if p < q {
        lemma_off_mono(h, p, (q - 1) as nat);
    }
}

/// The reduced images, as `(buffer, offsets)`: pass `p` is
/// `buf[off[p]..off[p + 1]]`.
pub open spec fn imgs_view(buf: Seq<u8>, off: Seq<usize>, n: nat) -> Seq<Seq<u8>> {
    Seq::new(n, |p: int| buf.subrange(off[p] as int, off[p + 1int] as int))
}

pub open spec fn offs_ok(h: Ihdr, off: Seq<usize>) -> bool {
    &&& off.len() == 8
    &&& forall|p: int| 0 <= p <= npasses(h) ==> #[trigger] off[p] == img_off(h, p as nat)
}

/// Reconstructs every pass of the raw image data in place: `buf` holds
/// exactly `raw_size` bytes of filtered data, and afterwards pass `p`'s
/// image is `buf[off[p]..off[p + 1]]` (each image starts at or before its
/// filtered data). Returns `Err(())` at an invalid filter type.
pub fn reconstruct(h: &Header, buf: &mut [u8]) -> (r: Result<[usize; 8], ()>)
    requires
        hdr_ok(h.view()),
        old(buf)@.len() == raw_size(h.view()),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        match r {
            Ok(off) => offs_ok(h.view(), off@) && off@[npasses(h.view()) as int] <= final(buf)@.len()
                && pass_images(h.view(), old(buf)@, npasses(h.view())) == Some(
                imgs_view(final(buf)@, off@, npasses(h.view())),
            ),
            Err(()) => pass_images(h.view(), old(buf)@, npasses(h.view())) is None,
        },
{
    let tracked mut m = Meter { n: 0 };
    reconstruct_counted(h, buf, Tracked(&mut m))
}

/// `reconstruct`, counting its steps: at most three for each byte of the
/// image data, and 8.
pub fn reconstruct_counted(h: &Header, buf: &mut [u8], Tracked(m): Tracked<&mut Meter>) -> (r: Result<[usize; 8], ()>)
    requires
        hdr_ok(h.view()),
        old(buf)@.len() == raw_size(h.view()),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        match r {
            Ok(off) => offs_ok(h.view(), off@) && off@[npasses(h.view()) as int] <= final(buf)@.len()
                && pass_images(h.view(), old(buf)@, npasses(h.view())) == Some(
                imgs_view(final(buf)@, off@, npasses(h.view())),
            ),
            Err(()) => pass_images(h.view(), old(buf)@, npasses(h.view())) is None,
        },
        final(m).n <= old(m).n + 3 * old(buf)@.len() + 8,
{
    let ghost m0 = m.n;
    let ghost hv = h.view();
    let ghost raw = buf@;
    let np = npasses_exec(h);
    let roffs = pass_offsets(h);
    let bpp = filter_bpp_exec(h) as usize;
    // The image offsets, each at most the raw offset.
    let mut off: [usize; 8] = [0; 8];
    let mut p: u64 = 0;
    let _ = buf.len();
    while p < np
        invariant
            hdr_ok(hv),
            hv == h.view(),
            np == npasses(hv),
            np <= 7,
            p <= np,
            off@.len() == 8,
            buf@.len() == raw_size(hv),
            buf@.len() <= usize::MAX,
            forall|q: int| 0 <= q <= npasses(hv) ==> #[trigger] roffs@[q] == pass_off(hv, q as nat),
            forall|q: int| 0 <= q <= p ==> #[trigger] off@[q] == img_off(hv, q as nat),
            m.n <= m0 + p,
            m0 == old(m).n,
        decreases np - p,
    {
        proof {
            m.n = m.n + 1;
        }
        let (pw, ph) = pass_dims(h, p);
        let sz: usize = if pw == 0 || ph == 0 {
            0
        } else {
            let rb = row_bytes_exec(h, pw);
            proof {
                lemma_img_le_pass(hv, (p + 1) as nat);
                lemma_off_mono(hv, (p + 1) as nat, np as nat);
                assert(ph * rb <= ph * (1 + rb)) by (nonlinear_arith);
                assert(img_off(hv, p as nat) + ph * rb <= buf@.len());
            }
            (ph * rb) as usize
        };
        proof {
            lemma_img_le_pass(hv, (p + 1) as nat);
            lemma_off_mono(hv, (p + 1) as nat, np as nat);
        }
        off[p as usize + 1] = off[p as usize] + sz;
        p = p + 1;
    }
    let mut p: u64 = 0;
    proof {
        assert(imgs_view(buf@, off@, 0) =~= Seq::<Seq<u8>>::empty());
        lemma_img_le_pass(hv, np as nat);
    }
    while p < np
        invariant
            hdr_ok(hv),
            hv == h.view(),
            np == npasses(hv),
            np <= 7,
            p <= np,
            1 <= bpp <= 8,
            bpp == filter_bpp(hv),
            off@.len() == 8,
            raw.len() == raw_size(hv),
            raw == old(buf)@,
            buf@.len() == raw.len(),
            buf@.len() <= usize::MAX,
            forall|q: int| 0 <= q <= npasses(hv) ==> #[trigger] roffs@[q] == pass_off(hv, q as nat),
            offs_ok(hv, off@),
            off@[np as int] <= buf@.len(),
            pass_images(hv, raw, p as nat) == Some(imgs_view(buf@, off@, p as nat)),
            forall|k: int| 0 <= k < buf@.len() && k >= roffs@[p as int] ==> #[trigger] buf@[k] == raw[k],
            m.n <= m0 + 7 + 3 * pass_off(hv, p as nat),
            m0 == old(m).n,
        decreases np - p,
    {
        proof {
            lemma_off_le_raw(hv, (p + 1) as nat);
        }
        if !one_pass(h, &roffs, buf, &off, p, bpp, Ghost(raw), Tracked(m)) {
            proof {
                lemma_images_none(hv, raw, (p + 1) as nat, np as nat);
            }
            return Err(());
        }
        p = p + 1;
    }
    Ok(off)
}

/// Reconstructs pass `p` into `buf[off[p]..off[p + 1]]`; `false` at an
/// invalid filter type.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn one_pass(h: &Header, roffs: &[u128; 8], buf: &mut [u8], off: &[usize; 8], p: u64, bpp: usize, Ghost(raw): Ghost<Seq<u8>>, Tracked(m): Tracked<&mut Meter>) -> (ok: bool)
    requires
        hdr_ok(h.view()),
        p < npasses(h.view()),
        bpp == filter_bpp(h.view()),
        raw.len() == raw_size(h.view()),
        old(buf)@.len() == raw.len(),
        forall|q: int| 0 <= q <= npasses(h.view()) ==> #[trigger] roffs@[q] == pass_off(h.view(), q as nat),
        offs_ok(h.view(), off@),
        pass_images(h.view(), raw, p as nat) == Some(imgs_view(old(buf)@, off@, p as nat)),
        forall|k: int| 0 <= k < old(buf)@.len() && k >= roffs@[p as int] ==> #[trigger] old(buf)@[k] == raw[k],
    ensures
        final(m).n <= old(m).n + 3 * pass_size(h.view(), p as nat),
        final(buf)@.len() == old(buf)@.len(),
        ok ==> pass_images(h.view(), raw, (p + 1) as nat) == Some(imgs_view(final(buf)@, off@, (p + 1) as nat)),
        ok ==> forall|k: int| 0 <= k < final(buf)@.len() && k >= roffs@[p + 1] ==> #[trigger] final(buf)@[k] == raw[k],
        !ok ==> pass_images(h.view(), raw, (p + 1) as nat) is None,
{
    let ghost hv = h.view();
    let ghost np = npasses(hv);
    let (pw, ph) = pass_dims(h, p);
    let ghost b0 = buf@;
    let _ = buf.len();
    proof {
        lemma_off_mono(hv, p as nat, np);
        lemma_off_mono(hv, (p + 1) as nat, np);
        lemma_img_le_pass(hv, p as nat);
    }
    if pw != 0 && ph != 0 {
        let rb = row_bytes_exec(h, pw);
        proof {
            assert(pass_size(hv, p as nat) == ph * (1 + rb));
            assert(ph * (1 + rb) > 0) by (nonlinear_arith) requires ph > 0;
            assert(img_size(hv, p as nat) == ph * rb);
            assert(ph * (rb + 1) == ph * (1 + rb)) by (nonlinear_arith);
            assert(roffs@[p as int] + ph * (rb + 1) <= buf@.len());
            assert(off@[p as int] <= roffs@[p as int]);
            lemma_rows_frame(b0, raw, roffs@[p as int] as int, rb as nat, bpp as nat, ph as nat);
            // All within the buffer, so the casts below keep every value on
            // 32-bit targets too.
            assert(rb <= ph * (rb + 1) && ph <= ph * (rb + 1)) by (nonlinear_arith)
                requires
                    ph >= 1,
            ;
        }
        let ok = unfilter_rows(buf, roffs[p as usize] as usize, rb as usize, bpp, ph as usize, off[p as usize], Tracked(m));
        if !ok {
            return false;
        }
        proof {
            assert(roffs@[p + 1] == roffs@[p as int] + ph * (rb + 1));
        }
    } else {
        proof {
            assert(buf@.subrange(off@[p as int] as int, off@[p + 1] as int) =~= Seq::<u8>::empty());
        }
    }
    proof {
        assert(pass_image(hv, raw, p as nat) == Some(buf@.subrange(off@[p as int] as int, off@[p + 1int] as int)));
        lemma_img_le_pass(hv, np);
        lemma_imgs_step(hv, raw, b0, buf@, off@, p as nat);
    }
    true
}

/// The passes up to `p` fit in the image data.
pub proof fn lemma_off_le_raw(h: Ihdr, p: nat)
    requires
        p <= npasses(h),
    ensures
        pass_off(h, p) <= raw_size(h),
    decreases npasses(h) - p,
{
    if p < npasses(h) {
        lemma_off_le_raw(h, p + 1);
    }
}

/// `recon_rows` reads only the rows it reconstructs.
pub proof fn lemma_rows_frame(r1: Seq<u8>, r2: Seq<u8>, off: int, rb: nat, bpp: nat, n: nat)
    requires
        0 <= off,
        off + n * (rb + 1) <= r1.len(),
        off + n * (rb + 1) <= r2.len(),
        forall|k: int| off <= k < off + n * (rb + 1) ==> #[trigger] r1[k] == r2[k],
    ensures
        recon_rows(r1, off, rb, bpp, n) == recon_rows(r2, off, rb, bpp, n),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        assert(m * (rb + 1) + (rb + 1) == n * (rb + 1)) by (nonlinear_arith) requires m + 1 == n;
        lemma_rows_frame(r1, r2, off, rb, bpp, m);
        let i = off + m * (rb + 1);
        assert(r1.subrange(i + 1, i + 1 + rb) =~= r2.subrange(i + 1, i + 1 + rb));
    }
}

pub proof fn lemma_imgs_step(h: Ihdr, raw: Seq<u8>, b0: Seq<u8>, buf: Seq<u8>, off: Seq<usize>, p: nat)
    requires
        p < npasses(h),
        offs_ok(h, off),
        buf.len() == b0.len(),
        b0.len() >= img_off(h, npasses(h)),
        forall|k: int| 0 <= k < off[p as int] ==> #[trigger] buf[k] == b0[k],
        pass_images(h, raw, p) == Some(imgs_view(b0, off, p)),
        pass_image(h, raw, p) == Some(buf.subrange(off[p as int] as int, off[p + 1int] as int)),
    ensures
        pass_images(h, raw, p + 1) == Some(imgs_view(buf, off, p + 1)),
{
    assert forall|q: int| 0 <= q < p implies #[trigger] imgs_view(buf, off, p)[q] == imgs_view(b0, off, p)[q] by {
        lemma_off_mono(h, (q + 1) as nat, p);
        lemma_off_mono(h, p, npasses(h));
        assert(buf.subrange(off[q] as int, off[q + 1] as int) =~= b0.subrange(off[q] as int, off[q + 1] as int));
    }
    assert(imgs_view(buf, off, p) =~= imgs_view(b0, off, p));
    assert(imgs_view(buf, off, p + 1) =~= imgs_view(buf, off, p).push(buf.subrange(off[p as int] as int, off[p + 1int] as int)));
}

pub proof fn lemma_images_none(h: Ihdr, raw: Seq<u8>, p: nat, n: nat)
    requires
        p <= n,
        pass_images(h, raw, p) is None,
    ensures
        pass_images(h, raw, n) is None,
    decreases n - p,
{
    if p < n {
        lemma_images_none(h, raw, p + 1, n);
    }
}

} // verus!
