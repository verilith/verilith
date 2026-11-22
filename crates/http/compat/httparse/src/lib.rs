//! httparse's API, implemented by `verilith_http::httparse` on vhttp's verified
//! parser. Use it in place of httparse with
//!
//! ```toml
//! [patch.crates-io]
//! httparse = { git = "https://github.com/verilith/vhttp" }
//! ```
//!
//! See `verilith_http::httparse` for how its parsing differs.
pub use verilith_http::httparse::*;
