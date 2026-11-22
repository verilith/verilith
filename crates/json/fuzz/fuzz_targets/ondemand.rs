//! The on-demand reader against the tape parser (the checks of
//! `tests/ondemand.rs`): a full on-demand read accepts the same texts and
//! reads the same values, partial reads of an accepted text end at its
//! end, and no sequence of calls panics on any input.
#![no_main]
use libfuzzer_sys::fuzz_target;

include!("../../tests/ondemand.rs");

fuzz_target!(|data: &[u8]| check(data));
