//! The public API: [`AesGcm`] (AES-128-GCM and AES-256-GCM) and [`Aes`]
//! (the block cipher alone, as QUIC header protection uses it), proven
//! against [`crate::spec`], over the kernels this CPU has: AES-NI and
//! PCLMULQDQ (with VAES and VPCLMULQDQ where there are) on x86-64, FEAT_AES
//! and FEAT_PMULL on AArch64.
//!
//! Trusted here: run-time CPU detection ([`crate::x86::has_ni`],
//! [`crate::x86::has_vaes`], [`crate::neon::has_arm_aes`]), and the
//! trampolines in `tf` that compile each verified function with the
//! target features its instructions need (Verus does not accept
//! `#[target_feature]` on verified code); each is one call of that
//! function, with its contract.
#![allow(unused_imports)]
use crate::gcm::Gcm;
use crate::lemmas::*;
use crate::spec::*;
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
use crate::x86::*;
#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
use crate::neon::*;
use vstd::prelude::*;

verus! {

/// The CPU has the instructions of the 128-bit kernels.
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
pub open spec fn cpu_ok() -> bool {
    ni()
}

/// The CPU also has those of the 16-block path.
#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
pub open spec fn cpu_wide() -> bool {
    vaes()
}

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
fn detect() -> (r: (bool, bool))
    ensures
        r.0 ==> cpu_ok(),
        r.1 ==> r.0 && cpu_wide(),
{
    if !has_ni() {
        return (false, false);
    }
    (true, has_vaes())
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
pub open spec fn cpu_ok() -> bool {
    arm_aes()
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
pub open spec fn cpu_wide() -> bool {
    false
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
fn detect() -> (r: (bool, bool))
    ensures
        r.0 ==> cpu_ok(),
        r.1 ==> r.0 && cpu_wide(),
{
    (has_arm_aes(), false)
}

/// Elsewhere there are no kernels: [`AesGcm::new`] and [`Aes::new`] return
/// `None`.
#[cfg(not(any(all(target_arch = "x86_64", target_feature = "sse2"), all(target_arch = "aarch64", target_endian = "little"))))]
pub open spec fn cpu_ok() -> bool {
    false
}

#[cfg(not(any(all(target_arch = "x86_64", target_feature = "sse2"), all(target_arch = "aarch64", target_endian = "little"))))]
pub open spec fn cpu_wide() -> bool {
    false
}

#[cfg(not(any(all(target_arch = "x86_64", target_feature = "sse2"), all(target_arch = "aarch64", target_endian = "little"))))]
fn detect() -> (r: (bool, bool))
    ensures
        r.0 ==> cpu_ok(),
        r.1 ==> r.0 && cpu_wide(),
{
    (false, false)
}

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
        self.g.wf() && cpu_ok() && (self.wide ==> cpu_wide())
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
        let (ok, wide) = detect();
        if !ok {
            return None;
        }
        Some(AesGcm { g: new_tf(key), wide })
    }

    /// As [`AesGcm::new`], but never taking the 16-block path (for tests
    /// of the 128-bit kernels on a CPU that has it).
    #[doc(hidden)]
    pub fn new_narrow(key: &[u8]) -> (r: Option<Self>)
        ensures
            r matches Some(k) ==> k.wf() && k.key() == key@,
            r is Some ==> key_ok(key@),
    {
        if key.len() != 16 && key.len() != 32 {
            return None;
        }
        let (ok, _) = detect();
        if !ok {
            return None;
        }
        Some(AesGcm { g: new_tf(key), wide: false })
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
        seal_tf(&self.g, iv, aad, buf, tag, self.wide);
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
        open_tf(&self.g, iv, aad, buf, tag, self.wide)
    }
}

/// An AES key, expanded, for the block cipher alone.
#[allow(dead_code)]
pub struct Aes {
    rk: [u128; 15],
    nr: usize,
    key: Ghost<Seq<u8>>,
}

impl Aes {
    /// The key it was made from.
    pub closed spec fn key(&self) -> Seq<u8> {
        self.key@
    }

    pub closed spec fn wf(&self) -> bool {
        rk_ok(self.key@, self.rk@) && self.nr == nr(self.key@) && cpu_ok()
    }

    /// The key, expanded; `None` unless it is 16 or 32 bytes and the CPU
    /// has the instructions.
    pub fn new(key: &[u8]) -> (r: Option<Self>)
        ensures
            r matches Some(k) ==> k.wf() && k.key() == key@,
            r is Some ==> key_ok(key@),
    {
        if key.len() != 16 && key.len() != 32 {
            return None;
        }
        let (ok, _) = detect();
        if !ok {
            return None;
        }
        let (rk, nr) = expand_tf(key);
        Some(Aes { rk, nr, key: Ghost(key@) })
    }

    /// CIPHER(block), in place.
    pub fn encrypt_block(&self, block: &mut [u8; 16])
        requires
            self.wf(),
        ensures
            final(block)@ == cipher(self.key(), old(block)@),
    {
        enc_tf(&self.rk, self.nr, block, Ghost(self.key@))
    }
}

/// [`crate::gcm::expand`] compiled with the target features (trusted
/// only to be that function).
#[verifier::external_body]
fn expand_tf(key: &[u8]) -> (r: ([u128; 15], usize))
    requires
        cpu_ok(),
        key@.len() == 16 || key@.len() == 32,
    ensures
        rk_ok(key@, r.0@),
        r.1 == nr(key@),
{
    // SAFETY: the CPU has the features (the precondition).
    unsafe { tf::expand(key) }
}

/// [`crate::gcm::encrypt_block`], compiled as [`expand_tf`] is.
#[verifier::external_body]
fn enc_tf(rk: &[u128; 15], nr: usize, b: &mut [u8; 16], key: Ghost<Seq<u8>>)
    requires
        cpu_ok(),
        rk_ok(key@, rk@),
        nr == crate::spec::nr(key@),
    ensures
        final(b)@ == cipher(key@, old(b)@),
{
    // SAFETY: as in `expand_tf`.
    unsafe { tf::enc(rk, nr, b, key) }
}

/// [`Gcm::new`], compiled as [`expand_tf`] is.
#[verifier::external_body]
fn new_tf(key: &[u8]) -> (r: Gcm)
    requires
        cpu_ok(),
        key@.len() == 16 || key@.len() == 32,
    ensures
        r.wf(),
        r.key@ == key@,
{
    // SAFETY: as in `expand_tf`.
    unsafe { tf::new(key) }
}

/// [`Gcm::seal`], compiled as [`expand_tf`] is, or with the 16-block
/// path's features as well if `wide`.
#[verifier::external_body]
fn seal_tf(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16], wide: bool)
    requires
        cpu_ok(),
        wide ==> cpu_wide(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        final(buf)@ + final(tag)@ == gcm_seal(g.key@, iv@, aad@, old(buf)@),
        final(buf)@ == gctr(g.key@, iv@, old(buf)@),
{
    // SAFETY: as in `expand_tf`, and `wide` only if the CPU has the
    // 16-block path's features.
    unsafe { tf::seal(g, iv, aad, buf, tag, wide) }
}

/// [`Gcm::open`], compiled as [`seal_tf`] is.
#[verifier::external_body]
fn open_tf(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16], wide: bool) -> (r: bool)
    requires
        cpu_ok(),
        wide ==> cpu_wide(),
        g.wf(),
        gcm_ok(g.key@, iv@, aad@, old(buf)@.len()),
    ensures
        r == (gcm_tag(g.key@, iv@, aad@, old(buf)@) == tag@),
        r ==> final(buf)@ == gctr(g.key@, iv@, old(buf)@),
        r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) == Some(final(buf)@),
        !r ==> gcm_open(g.key@, iv@, aad@, old(buf)@ + tag@) is None,
        !r ==> final(buf)@ == zeros(old(buf)@.len()),
{
    // SAFETY: as in `seal_tf`.
    unsafe { tf::open(g, iv, aad, buf, tag, wide) }
}

} // verus!

#[cfg(all(target_arch = "x86_64", target_feature = "sse2"))]
mod tf {
    use crate::gcm::{self, Gcm};
    use crate::ni::Ni;
    use vstd::prelude::{Ghost, Seq};

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn expand(key: &[u8]) -> ([u128; 15], usize) {
        gcm::expand::<Ni>(key)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn enc(rk: &[u128; 15], nr: usize, b: &mut [u8; 16], key: Ghost<Seq<u8>>) {
        gcm::encrypt_block::<Ni>(rk, nr, b, key)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    pub(super) unsafe fn new(key: &[u8]) -> Gcm {
        Gcm::new::<Ni>(key)
    }

    #[inline(always)]
    pub(super) unsafe fn seal(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16], wide: bool) {
        unsafe { if wide { seal_vaes(g, iv, aad, buf, tag) } else { seal_ni(g, iv, aad, buf, tag) } }
    }

    #[inline(always)]
    pub(super) unsafe fn open(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16], wide: bool) -> bool {
        unsafe { if wide { open_vaes(g, iv, aad, buf, tag) } else { open_ni(g, iv, aad, buf, tag) } }
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    unsafe fn seal_ni(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16]) {
        g.seal::<Ni>(iv, aad, buf, tag, false)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1")]
    #[inline(never)]
    unsafe fn open_ni(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> bool {
        g.open::<Ni>(iv, aad, buf, tag, false)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1,avx2,avx512f,avx512bw,avx512vl,vaes,vpclmulqdq")]
    #[inline(never)]
    unsafe fn seal_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16]) {
        g.seal::<Ni>(iv, aad, buf, tag, true)
    }

    #[target_feature(enable = "aes,pclmulqdq,ssse3,sse4.1,avx2,avx512f,avx512bw,avx512vl,vaes,vpclmulqdq")]
    #[inline(never)]
    unsafe fn open_vaes(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16]) -> bool {
        g.open::<Ni>(iv, aad, buf, tag, true)
    }
}

#[cfg(all(target_arch = "aarch64", target_endian = "little"))]
mod tf {
    use crate::arm::Arm;
    use crate::gcm::{self, Gcm};
    use vstd::prelude::{Ghost, Seq};

    #[target_feature(enable = "neon,aes")]
    #[inline(never)]
    pub(super) unsafe fn expand(key: &[u8]) -> ([u128; 15], usize) {
        let _dit = crate::dit::Dit::on();
        gcm::expand::<Arm>(key)
    }

    #[target_feature(enable = "neon,aes")]
    #[inline(never)]
    pub(super) unsafe fn enc(rk: &[u128; 15], nr: usize, b: &mut [u8; 16], key: Ghost<Seq<u8>>) {
        let _dit = crate::dit::Dit::on();
        gcm::encrypt_block::<Arm>(rk, nr, b, key)
    }

    #[target_feature(enable = "neon,aes")]
    #[inline(never)]
    pub(super) unsafe fn new(key: &[u8]) -> Gcm {
        let _dit = crate::dit::Dit::on();
        Gcm::new::<Arm>(key)
    }

    #[target_feature(enable = "neon,aes")]
    #[inline(never)]
    pub(super) unsafe fn seal(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &mut [u8; 16], _wide: bool) {
        let _dit = crate::dit::Dit::on();
        g.seal::<Arm>(iv, aad, buf, tag, false)
    }

    #[target_feature(enable = "neon,aes")]
    #[inline(never)]
    pub(super) unsafe fn open(g: &Gcm, iv: &[u8; 12], aad: &[u8], buf: &mut [u8], tag: &[u8; 16], _wide: bool) -> bool {
        let _dit = crate::dit::Dit::on();
        g.open::<Arm>(iv, aad, buf, tag, false)
    }
}

#[cfg(not(any(all(target_arch = "x86_64", target_feature = "sse2"), all(target_arch = "aarch64", target_endian = "little"))))]
mod tf {
    use crate::gcm::Gcm;
    use vstd::prelude::{Ghost, Seq};

    // Never called: each needs `cpu_ok()`, which is false here.
    pub(super) unsafe fn expand(_: &[u8]) -> ([u128; 15], usize) {
        unreachable!()
    }
    pub(super) unsafe fn enc(_: &[u128; 15], _: usize, _: &mut [u8; 16], _: Ghost<Seq<u8>>) {
        unreachable!()
    }
    pub(super) unsafe fn new(_: &[u8]) -> Gcm {
        unreachable!()
    }
    pub(super) unsafe fn seal(_: &Gcm, _: &[u8; 12], _: &[u8], _: &mut [u8], _: &mut [u8; 16], _: bool) {
        unreachable!()
    }
    pub(super) unsafe fn open(_: &Gcm, _: &[u8; 12], _: &[u8], _: &mut [u8], _: &[u8; 16], _: bool) -> bool {
        unreachable!()
    }
}
