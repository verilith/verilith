//! The public API: [`AesGcm`] (AES-128-GCM and AES-256-GCM) and [`Aes`]
//! (the block cipher alone, as QUIC header protection uses it), proven
//! against [`crate::spec`], over the kernel this CPU has.
//!
//! Trusted here: run-time CPU detection ([`crate::x86::has_ni`]), and the
//! trampolines in `tf` that compile each verified function with the
//! target features its instructions need (Verus does not accept
//! `#[target_feature]` on verified code); each is one call of that
//! function, with its contract.
#![allow(unused_imports)]
use crate::gcm::Gcm;
use crate::lemmas::*;
use crate::spec::*;
use crate::x86::*;
use vstd::prelude::*;

verus! {

/// An AES-GCM key, expanded.
pub struct AesGcm {
    g: Gcm,
    wide: bool,
}

impl AesGcm {
    /// The key it was made from.
    pub closed spec fn key(&self) -> Seq<u8> {
        self.g.key@
    }

    pub closed spec fn wf(&self) -> bool {
        self.g.wf() && ni() && (self.wide ==> vaes())
    }

    /// The key, expanded; `None` unless it is 16 or 32 bytes and the CPU
    /// has the instructions the kernels use.
    pub fn new(key: &[u8]) -> (r: Option<Self>)
        ensures
            r matches Some(k) ==> k.wf() && k.key() == key@,
            r is Some ==> key_ok(key@),
    {
        if key.len() != 16 && key.len() != 32 {
            return None;
        }
        if !has_ni() {
            return None;
        }
        let wide = has_vaes();
        Some(AesGcm { g: new_tf(key), wide })
    }

    /// GCM-AE_K(IV, P, A): encrypts `buf` in place and writes the tag to
    /// `tag`. `false`, with `buf` unchanged, if the lengths are beyond
    /// SP 800-38D's limits.
    pub fn seal(&self, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16]) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == gcm_ok(self.key(), iv@, aad@, old(buf)@.len()),
            r ==> final(buf)@ + final(tag)@ == gcm_seal(self.key(), iv@, aad@, old(buf)@),
            !r ==> final(buf)@ == old(buf)@,
    {
        if buf.len() as u64 > 0xf_ffff_ffe0u64 || aad.len() as u64 >= 0x2000_0000_0000_0000u64 {
            return false;
        }
        if self.wide {
            seal_vaes(&self.g, iv, aad, buf, tag);
        } else {
            seal_tf(&self.g, iv, aad, buf, tag);
        }
        true
    }

    /// GCM-AD_K(IV, C, T, A): decrypts `buf` in place if `tag` is its tag.
    /// If it is not (or the lengths are beyond SP 800-38D's limits),
    /// returns `false` and zeroes `buf`.
    pub fn open(&self, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> (r: bool)
        requires
            self.wf(),
        ensures
            r ==> gcm_ok(self.key(), iv@, aad@, old(buf)@.len()),
            r ==> gcm_open(self.key(), iv@, aad@, old(buf)@ + tag@) == Some(final(buf)@),
            gcm_ok(self.key(), iv@, aad@, old(buf)@.len()) && !r ==> gcm_open(
                self.key(),
                iv@,
                aad@,
                old(buf)@ + tag@,
            ) is None,
            !r ==> final(buf)@ == zeros(old(buf)@.len()),
    {
        if buf.len() as u64 > 0xf_ffff_ffe0u64 || aad.len() as u64 >= 0x2000_0000_0000_0000u64 {
            let n = buf.len();
            let mut k: usize = 0;
            while k < n
                invariant
                    n == buf@.len(),
                    k <= n,
                    forall|j: int| 0 <= j < k ==> #[trigger] buf@[j] == 0,
                decreases n - k,
            {
                buf[k] = 0;
                k = k + 1;
            }
            assert(buf@ =~= zeros(n as nat));
            return false;
        }
        if self.wide {
            open_vaes(&self.g, iv, aad, buf, tag)
        } else {
            open_tf(&self.g, iv, aad, buf, tag)
        }
    }
}

/// [`Gcm::new`] compiled with AES-NI, PCLMULQDQ, SSSE3 and SSE4.1
/// (trusted only to be that function).
#[verifier::external_body]
fn new_tf(key: &[u8]) -> (r: Gcm)
    requires
        ni(),
        key@.len() == 16 || key@.len() == 32,
    ensures
        r.wf(),
        r.key@ == key@,
{
    // SAFETY: the CPU has the features (the precondition).
    unsafe { tf::new(key) }
}

/// [`Gcm::seal`], compiled as [`new_tf`] is.
#[verifier::external_body]
fn seal_tf(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16])
    requires
        ni(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        final(buf)@ + final(tag)@ == gcm_seal(g.key@, iv@, aad@, old(buf)@),
        final(buf)@ == gctr(g.key@, iv@, old(buf)@),
{
    // SAFETY: as in `new_tf`.
    unsafe { tf::seal(g, iv, aad, buf, tag) }
}

/// [`Gcm::open`], compiled as [`new_tf`] is.
#[verifier::external_body]
fn open_tf(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> (r: bool)
    requires
        ni(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        r == (gcm_tag(g.key@, iv@, aad@, old(buf)@) == tag@),
        r ==> final(buf)@ == gctr(g.key@, iv@, old(buf)@),
        r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) == Some(final(buf)@),
        !r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) is None,
        !r ==> final(buf)@ == zeros(old(buf)@.len()),
{
    // SAFETY: as in `new_tf`.
    unsafe { tf::open(g, iv, aad, buf, tag) }
}

/// [`Gcm::seal`], compiled with AVX-512, VAES and VPCLMULQDQ as well.
#[verifier::external_body]
fn seal_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16])
    requires
        ni(),
        vaes(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        final(buf)@ + final(tag)@ == gcm_seal(g.key@, iv@, aad@, old(buf)@),
        final(buf)@ == gctr(g.key@, iv@, old(buf)@),
{
    // SAFETY: as in `new_tf`.
    unsafe { tf::seal_vaes(g, iv, aad, buf, tag) }
}

/// [`Gcm::open`], compiled with AVX-512, VAES and VPCLMULQDQ as well.
#[verifier::external_body]
fn open_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> (r: bool)
    requires
        ni(),
        vaes(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        r == (gcm_tag(g.key@, iv@, aad@, old(buf)@) == tag@),
        r ==> final(buf)@ == gctr(g.key@, iv@, old(buf)@),
        r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) == Some(final(buf)@),
        !r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) is None,
        !r ==> final(buf)@ == zeros(old(buf)@.len()),
{
    // SAFETY: as in `new_tf`.
    unsafe { tf::open_vaes(g, iv, aad, buf, tag) }
}

} // verus!

mod tf {
    use crate::gcm::Gcm;

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn new(key: &[u8]) -> Gcm {
        Gcm::new(key)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn seal(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16]) {
        g.seal(iv, aad, buf, tag, false)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn open(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> bool {
        g.open(iv, aad, buf, tag, false)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1,avx2,avx512f,avx512bw,avx512vl,vaes,vpclmulqdq")]
    #[inline(never)]
    pub(super) unsafe fn seal_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16]) {
        g.seal(iv, aad, buf, tag, true)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1,avx2,avx512f,avx512bw,avx512vl,vaes,vpclmulqdq")]
    #[inline(never)]
    pub(super) unsafe fn open_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> bool {
        g.open(iv, aad, buf, tag, true)
    }
}
