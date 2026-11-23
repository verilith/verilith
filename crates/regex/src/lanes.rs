//! The SSE2 operations the first-byte scans use on x86-64: verilith-simd's
//! `sse2` wrappers, proven there from verilith-simd's specification of each
//! instruction. Nothing in this file is trusted. On AArch64 the scan uses
//! NEON through verilith-simd instead (`crate::find`), but this code still
//! builds there over verilith-simd's emulation, so one generic scanner,
//! verified for both, serves both.
pub use verilith_simd::sse2::*;
