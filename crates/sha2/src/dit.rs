//! Arm's Data Independent Timing (FEAT_DIT): while PSTATE.DIT is set, the
//! instructions on Arm's list (the integer, logical, vector and AES, SHA
//! and PMULL instructions the kernels use) take time independent of their
//! data. Without it Arm promises nothing, and some cores (Apple's M-series,
//! for one) vary in time: for instance their data-memory-dependent
//! prefetcher (GoFetch) acts on loaded values that look like pointers
//! unless DIT is set.
//!
//! [`Dit::on`] sets DIT for as long as the guard lives, if the CPU has it
//! and it was not set already, and the guard's drop puts it back. The
//! ARMv8 kernels (`armv8::tf`) hold one across the work on
//! secrets. Not verified: a read and a write of one system register.
#[cfg(target_arch = "aarch64")]
pub(crate) struct Dit {
    restore: bool,
}

#[cfg(all(target_arch = "aarch64", feature = "std"))]
#[inline(always)]
fn has_dit() -> bool {
    std::arch::is_aarch64_feature_detected!("dit")
}

#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
#[inline(always)]
fn has_dit() -> bool {
    cfg!(target_feature = "dit")
}

#[cfg(target_arch = "aarch64")]
impl Dit {
    /// DIT is PSTATE bit 24, read and written as the system register
    /// `S3_3_C4_C2_5` (named DIT by assemblers that know FEAT_DIT).
    const BIT: u64 = 1 << 24;

    #[inline(always)]
    pub(crate) fn on() -> Dit {
        if !has_dit() {
            return Dit { restore: false };
        }
        let v: u64;
        // SAFETY: the CPU has FEAT_DIT, so the register exists and EL0 may
        // read and write it. Not `nomem`: memory accesses must not move
        // across it.
        unsafe { core::arch::asm!("mrs {}, s3_3_c4_c2_5", out(reg) v, options(nostack, preserves_flags)) };
        if v & Self::BIT != 0 {
            return Dit { restore: false };
        }
        // SAFETY: as above.
        unsafe { core::arch::asm!("msr s3_3_c4_c2_5, {}", in(reg) Self::BIT, options(nostack, preserves_flags)) };
        Dit { restore: true }
    }
}

#[cfg(target_arch = "aarch64")]
impl Drop for Dit {
    #[inline(always)]
    fn drop(&mut self) {
        if self.restore {
            // SAFETY: only when `on` found the CPU has FEAT_DIT.
            unsafe { core::arch::asm!("msr s3_3_c4_c2_5, xzr", options(nostack, preserves_flags)) };
        }
    }
}
