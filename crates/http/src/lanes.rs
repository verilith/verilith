//! The SSE2 operations the scanners use (`load16`, `splat16`, `eq16`,
//! `or16`, `min16`, `movemask16`), with the bytes `b16` of a register
//! and the bits `bit` of a mask. They are verilith-simd's `sse2`
//! wrappers, whose contracts are proven there from its specifications of
//! the instructions, so nothing here is trusted. `tests/lanes.rs` still
//! checks every function against its contract on exhaustive inputs. SSE2
//! is part of the x86_64 baseline, so no runtime feature detection is
//! needed.
//!
//! On AArch64 the scanners use NEON instead (`crate::scan_neon`), but the
//! SSE2 code still builds there on verilith-simd's emulation, so one
//! generic scanner, verified for both, serves both.
#[cfg(verus_only)]
pub use verilith_simd::sse2::bit;

#[cfg(all(verus_only, any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128"))))]
pub use verilith_simd::sse2::b16;
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", all(target_arch = "wasm32", target_feature = "simd128")))]
pub use verilith_simd::sse2::{eq16, load16, min16, movemask16, or16, splat16};
