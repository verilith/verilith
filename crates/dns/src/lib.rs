#![doc = include_str!("../README.md")]
// A formally verified DNS (RFC 1035) message parser and serializer.
#![cfg_attr(not(verus_only), allow(unused_variables, non_shorthand_field_patterns))]
#![cfg_attr(not(feature = "std"), no_std)]
//
// - [`spec`]: the wire format as pure functions (the trusted specification).
// - [`lemmas`]: proofs about the spec, including the round-trip theorem.
// - [`message`]: the [`Message`] type, its verified accessors, builder and
//   serializer.
// - [`parse`]: the verified parser.
// - [`spec_rdata`], [`rdata`]: typed RDATA, specified and verified.
// - [`encode`]: the verified typed RDATA encoder, proven to be undone by
//   [`rdata::read_rdata`]; the c-ares writer uses it.
// - [`name`]: unverified conveniences (name views, presentation format,
//   iterators).
// - [`error`]: [`try_parse`], which says why a message was rejected.
// - [`capi`], `cares` (feature `cares`): unverified C ABI adapters for
//   c-ares's `ares_expand_name` and `ares_dns_parse`.
// - `native` (feature `capi`): the unverified native C API,
//   `include/vdns.h`.
extern crate alloc;

#[doc(hidden)]
pub mod capi;
#[doc(hidden)]
pub mod compress;
#[doc(hidden)]
pub mod encode;
#[cfg(feature = "cares")]
#[doc(hidden)]
pub mod cares;
#[doc(hidden)]
pub mod error;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod lemmas_rdata;
#[doc(hidden)]
pub mod message;
pub mod name;
// Unverified glue over `message`; not compiled when verifying.
#[cfg(all(feature = "capi", not(verus_only)))]
#[doc(hidden)]
pub mod native;
#[doc(hidden)]
pub mod parse;
pub mod rdata;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod spec_rdata;
#[doc(hidden)]
pub mod spec_text;
#[doc(hidden)]
pub mod text;

pub use message::{BuildError, Message, QuestionRef, RecordRef, Section};
pub use name::{encode_name, Name};
pub use error::{try_parse, Error, ErrorKind, Part};
pub use parse::parse;

// The static library needs a panic handler and an allocator when built
// without std, as inside an embedded c-ares (`--no-default-features
// --features cares,ares-abi`). Panics call the C library's abort(); the
// verified parser and serializer cannot panic, so this covers the
// unverified adapters. Memory comes from c-ares's own allocator, so
// `ares_library_init_mem` hooks apply to vdns too.
#[cfg(all(feature = "cares", not(feature = "std"), not(test)))]
mod c_runtime {
    use core::alloc::{GlobalAlloc, Layout};
    use core::ffi::c_void;

    unsafe extern "C" {
        fn abort() -> !;
        fn ares_malloc(size: usize) -> *mut c_void;
        fn ares_realloc(p: *mut c_void, size: usize) -> *mut c_void;
        fn ares_free(p: *mut c_void);
    }

    #[panic_handler]
    fn panic(_: &core::panic::PanicInfo) -> ! {
        unsafe { abort() }
    }

    // malloc's alignment is at least that of every scalar type; vdns never
    // asks for more than a u64's. Larger requests fail (null), which Rust
    // reports as an allocation error rather than misaligning.
    const MAX_ALIGN: usize = core::mem::align_of::<u64>();

    struct CAlloc;

    unsafe impl GlobalAlloc for CAlloc {
        unsafe fn alloc(&self, l: Layout) -> *mut u8 {
            if l.align() > MAX_ALIGN {
                return core::ptr::null_mut();
            }
            unsafe { ares_malloc(l.size()) as *mut u8 }
        }
        unsafe fn dealloc(&self, p: *mut u8, _: Layout) {
            unsafe { ares_free(p as *mut c_void) }
        }
        unsafe fn realloc(&self, p: *mut u8, l: Layout, new_size: usize) -> *mut u8 {
            if l.align() > MAX_ALIGN {
                return core::ptr::null_mut();
            }
            unsafe { ares_realloc(p as *mut c_void, new_size) as *mut u8 }
        }
    }

    #[global_allocator]
    static ALLOC: CAlloc = CAlloc;
}
