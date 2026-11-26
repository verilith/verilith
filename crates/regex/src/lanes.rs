//! The six SSE2 operations the first-byte scans use on x86-64 (`load16`,
//! `splat16`, `eq16`, `subs16`, `or16`, `movemask16`), with the bytes
//! `b16` of a register and the bits `bit` of a mask. They are
//! verilith-simd's `sse2` wrappers, whose contracts are proven there from
//! its specifications of the instructions, so nothing here is trusted.
//! On AArch64 the scan uses NEON through vsimd instead (`crate::find`),
//! but this code still builds there (vsimd emulates it), so one generic
//! scanner, verified for both, serves both.
#[cfg(verus_only)]
pub use verilith_simd::sse2::bit;

#[cfg(all(verus_only, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
pub use verilith_simd::sse2::b16;
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
pub use verilith_simd::sse2::{eq16, load16, movemask16, or16, splat16, subs16};
