//! The SSE2 instructions the scanners use: verilith-simd's `sse2` wrappers,
//! proven there from verilith-simd's specification of each instruction and
//! shared with verilith-json, verilith-xml and verilith-regex. Nothing in
//! this file is trusted. SSE2 is part of the x86_64 baseline, so no runtime
//! feature detection is needed.
//!
//! On AArch64 the scanners use NEON instead (`crate::scan_neon`), but the
//! SSE2 code still builds there over verilith-simd's emulation, so one
//! generic scanner, verified for both, serves both.
pub use verilith_simd::sse2::*;
