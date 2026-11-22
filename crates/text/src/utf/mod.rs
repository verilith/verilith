//! Transcoding between UTF-8, UTF-16 and Latin-1, and the forgiving
//! base64 of the WHATWG Infra Standard: the operations simdutf provides to
//! Node.js, each proven to compute its spec.
pub mod spec;
pub mod avx2;
pub mod neon;
pub mod conv;
pub mod valid8;
