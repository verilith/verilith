//! Archives, verilith-archive's Rust API against libarchive's read API
//! (suites/archive/archive.c), the same cases and check value:
//!   read/ARCHIVE  `Archive::open`, then every member's data (`read_ref`:
//!                 a stored member is borrowed from the archive, checked)
//!   list/ARCHIVE  `Archive::open` and every member's name and size
use verilith_archive::{Archive, Kind};

fn walk(bytes: &[u8], read: bool) -> u64 {
    let a = Archive::open(bytes).expect("open");
    let (mut h, mut members) = (0u64, 0u64);
    for (i, e) in a.entries().iter().enumerate() {
        let link = matches!(e.kind, Kind::Symlink | Kind::Hardlink);
        // As libarchive's pathname and size: up to a NUL; links have size 0.
        let name = &e.name[..e.name.iter().position(|&c| c == 0).unwrap_or(e.name.len())];
        let size = if link { 0 } else { e.size };
        h = vbrun::mix(h.wrapping_add(size), name);
        members += 1;
        if read {
            let (mut total, mut d) = (0u64, 0u64);
            if !link {
                let data = a.read_ref(i).expect("read");
                let mut j = 0;
                while j < data.len() {
                    d = (d ^ data[j] as u64).wrapping_mul(0x100000001b3);
                    j += 4093;
                }
                total = data.len() as u64;
            }
            h = (h ^ total ^ d).wrapping_mul(0x100000001b3);
        }
    }
    h ^ (members << 48)
}

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let bytes = std::fs::read(format!("{dir}/{name}")).unwrap();
        for read in [true, false] {
            let b = bytes.clone();
            let len = b.len() as u64;
            r.case(format!("{}/{name}", if read { "read" } else { "list" }), len, move || walk(std::hint::black_box(&b), read));
        }
    }
    r.main();
}
