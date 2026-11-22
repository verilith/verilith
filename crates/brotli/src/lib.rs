//! A formally verified Brotli (RFC 7932) decompressor.
#![cfg_attr(not(verus_only), allow(unused_variables, unused_imports))]
pub mod bitread;
pub mod huffman;
pub mod items;
pub mod spec;
pub mod tables;
pub mod decoder;
pub mod dict;
pub mod prefix;
pub mod capi;
pub mod stream;
pub mod rank;
pub mod codes;
pub mod words;
