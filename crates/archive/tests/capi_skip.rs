//! `archive_read_data_skip` followed by `archive_read_data`: as in
//! libarchive, the skipped member has no data left.
use std::ffi::c_void;
use verilith_archive::capi::*;

#[test]
fn read_after_skip_is_end_of_data() {
    let tar = std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/gnutar-gnu.tar")).unwrap();
    unsafe {
        let a = read_new();
        assert_eq!(read_open_memory(a, tar.as_ptr() as *const c_void, tar.len()), 0);
        let mut e = core::ptr::null_mut();
        let mut found = false;
        while read_next_header(a, &mut e) == 0 {
            if entry_size(e) == 0 {
                continue;
            }
            found = true;
            assert_eq!(read_data_skip(a), 0);
            let mut buf = [0u8; 64];
            assert_eq!(read_data(a, buf.as_mut_ptr() as *mut c_void, buf.len()), 0);
            let (mut p, mut n, mut off) = (core::ptr::null(), 1usize, 0i64);
            assert_eq!(read_data_block(a, &mut p, &mut n, &mut off), 1, "ARCHIVE_EOF");
            assert_eq!(n, 0);
        }
        assert!(found, "the test archive has a member with data");
        read_free(a);
    }
}
