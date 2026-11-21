//! The bug classes the proofs rule out, each as a concrete archive.
mod common;
use common::*;
use verilith_archive::{Archive, Error, Kind, OpenError, Why};

/// A pax extended header record.
fn pax(key: &str, value: &str) -> Vec<u8> {
    let body = format!(" {}={}\n", key, value);
    let mut len = body.len() + 1;
    while format!("{}{}", len, body).len() != len {
        len += 1;
    }
    format!("{}{}", len, body).into_bytes()
}

fn why(bytes: &[u8]) -> Why {
    Archive::open(bytes).expect("parses").plan().expect_err("planner must refuse").why
}

fn ok(bytes: &[u8]) -> usize {
    Archive::open(bytes).expect("parses").plan().expect("planner must accept").len()
}

#[test]
fn zip_slip() {
    assert_eq!(why(&zip(&[stored("../evil", b"x")])), Why::Path);
    assert_eq!(why(&zip(&[stored("a/../../evil", b"x")])), Why::Path);
    assert_eq!(why(&zip(&[stored("a/b/..", b"x")])), Why::Path);
    assert_eq!(why(&tar(&[("../evil", b'0', b"x", "")])), Why::Path);
    // `..` inside a name is refused even where it would stay inside.
    assert_eq!(why(&tar(&[("a/../b", b'0', b"x", "")])), Why::Path);
}

#[test]
fn absolute_and_odd_names() {
    assert_eq!(why(&zip(&[stored("/etc/passwd", b"x")])), Why::Path);
    assert_eq!(why(&tar(&[("/etc/passwd", b'0', b"x", "")])), Why::Path);
    assert_eq!(why(&zip(&[stored("a\\..\\b", b"x")])), Why::Path);
    assert_eq!(why(&zip(&[stored("", b"x")])), Why::Path);
    assert_eq!(why(&zip(&[stored(".", b"x")])), Why::Path);
    assert_eq!(why(&zip(&[stored("a\0b", b"x")])), Why::Path);
    // Harmless oddities are normalised, not refused.
    assert_eq!(ok(&tar(&[("./a//b/./c", b'0', b"x", "")])), 1);
}

#[test]
fn symlink_escapes() {
    // The classic: a link out of the root, then a file through it.
    // (Refused twice over: for the member written through the link, and,
    // without that member, for the link's target.)
    assert_eq!(why(&tar(&[("link", b'2', b"", "/tmp"), ("link/x", b'0', b"x", "")])), Why::SymlinkTarget);
    assert_eq!(why(&tar(&[("link", b'2', b"", ".."), ("link/x", b'0', b"x", "")])), Why::ThroughSymlink);
    assert_eq!(why(&tar(&[("link", b'2', b"", "/tmp")])), Why::SymlinkTarget);
    assert_eq!(why(&tar(&[("link", b'2', b"", "..")])), Why::SymlinkTarget);
    // A link that stays inside, but a member written through it.
    assert_eq!(why(&tar(&[("d/x", b'0', b"x", ""), ("link", b'2', b"", "d"), ("link/y", b'0', b"y", "")])), Why::ThroughSymlink);
    // The same with the members in the other order.
    assert_eq!(why(&tar(&[("link/y", b'0', b"y", ""), ("link", b'2', b"", "d")])), Why::ThroughSymlink);
    // A target that climbs out of the root.
    assert_eq!(why(&tar(&[("d/link", b'2', b"", "../..")])), Why::SymlinkTarget);
    assert_eq!(why(&tar(&[("link", b'2', b"", "a/../../b")])), Why::SymlinkTarget);
    // A target that goes through another link: `b` is the root, so
    // `b/..` is really the root's parent.
    assert_eq!(why(&tar(&[("b", b'2', b"", "."), ("a", b'2', b"", "b/..")])), Why::SymlinkTarget);
    // Relative links that stay inside are fine, `..` included.
    assert_eq!(ok(&tar(&[("lib/x", b'0', b"x", ""), ("bin/x", b'2', b"", "../lib/x"), ("y", b'2', b"", "bin/x")])), 3);
    // The same checks for zip, where the target is the member's data.
    assert_eq!(why(&zip(&[zip_symlink("link", "../..")])), Why::SymlinkTarget);
    assert_eq!(why(&zip(&[zip_symlink("link", "d"), stored("link/x", b"x")])), Why::ThroughSymlink);
    assert_eq!(ok(&zip(&[stored("d/x", b"x"), zip_symlink("link", "d/x")])), 2);
}

#[test]
fn hardlink_escapes() {
    assert_eq!(why(&tar(&[("h", b'1', b"", "../../etc/passwd")])), Why::HardlinkTarget);
    assert_eq!(why(&tar(&[("h", b'1', b"", "/etc/passwd")])), Why::HardlinkTarget);
    assert_eq!(why(&tar(&[("h", b'1', b"", "missing")])), Why::HardlinkTarget);
    // To a later member, or to a symlink: refused.
    assert_eq!(why(&tar(&[("h", b'1', b"", "f"), ("f", b'0', b"x", "")])), Why::HardlinkTarget);
    assert_eq!(why(&tar(&[("f", b'0', b"x", ""), ("s", b'2', b"", "f"), ("h", b'1', b"", "s")])), Why::HardlinkTarget);
    assert_eq!(ok(&tar(&[("f", b'0', b"x", ""), ("h", b'1', b"", "f")])), 2);
}

#[test]
fn duplicates() {
    assert_eq!(why(&zip(&[stored("a", b"1"), stored("a", b"2")])), Why::Duplicate);
    assert_eq!(why(&tar(&[("a", b'0', b"1", ""), ("./a", b'0', b"2", "")])), Why::Duplicate);
    assert_eq!(why(&tar(&[("a", b'0', b"1", ""), ("a", b'2', b"", "b")])), Why::Duplicate);
}

#[test]
fn overlapping_members() {
    // Two directory entries for one local header: the "zip bomb" shape.
    let m = deflated("a", &vec![0u8; 100_000]);
    let body = zip(&[m.clone()]);
    let body_len = body.len();
    let local_only = body[..30 + 1 + m.stored.len()].to_vec();
    let bomb = zip_with_directory(local_only.clone(), &[m.clone(), m.clone()], &[0, 0]);
    assert_eq!(Archive::open(&bomb).err(), Some(OpenError::NotAnArchive));
    // The honest one opens.
    assert!(body_len > 0 && Archive::open(&body).is_ok());
    // Partial overlap: a second member whose header sits inside the first's data.
    let inner = stored("b", b"");
    let mut big = stored("a", &[0u8; 64]);
    let inner_local: Vec<u8> = zip(&[inner.clone()])[..31].to_vec();
    big.stored[10..41].copy_from_slice(&inner_local);
    big.crc = crc32(&big.stored);
    let honest = zip(&[big.clone()]);
    let body = honest[..30 + 1 + 64].to_vec();
    let nested = zip_with_directory(body, &[big, inner], &[0, 31 + 10]);
    assert_eq!(Archive::open(&nested).err(), Some(OpenError::NotAnArchive));
}

#[test]
fn lying_sizes() {
    let data = vec![7u8; 5000];
    // Declares less than the data decompresses to.
    let mut m = deflated("a", &data);
    m.size = 100;
    assert_eq!(Archive::open(&zip(&[m])).unwrap().read(0), Err(Error::BadData));
    // Declares more.
    let mut m = deflated("a", &data);
    m.size = 1 << 20;
    assert_eq!(Archive::open(&zip(&[m])).unwrap().read(0), Err(Error::BadData));
    // Declares far more than the limit: refused before anything is allocated.
    let mut m = deflated("a", &data);
    m.size = u32::MAX - 1;
    let z = zip(&[m]);
    assert_eq!(Archive::open_with_limit(&z, 1 << 20).unwrap().read(0), Err(Error::TooLarge));
    // Stored, with a size that is not the stored length.
    let mut m = stored("a", &data);
    m.size = 4999;
    assert_eq!(Archive::open(&zip(&[m])).unwrap().read(0), Err(Error::BadData));
    // A wrong CRC.
    let mut m = deflated("a", &data);
    m.crc ^= 1;
    assert_eq!(Archive::open(&zip(&[m])).unwrap().read(0), Err(Error::BadData));
    // The honest one reads back.
    assert_eq!(Archive::open(&zip(&[deflated("a", &data)])).unwrap().read(0), Ok(data));
}

#[test]
fn lying_offsets() {
    let m = stored("a", b"hello");
    let good = zip(&[m.clone()]);
    // A local header offset past the directory, and one that wraps.
    for off in [good.len() as u32, 0xffff_fff0, 36] {
        let body = good[..36].to_vec();
        assert_eq!(Archive::open(&zip_with_directory(body, &[m.clone()], &[off])).err(), Some(OpenError::NotAnArchive));
    }
    // A compressed size that runs into the central directory.
    let mut z = good.clone();
    let cd = 36;
    z[cd + 20..cd + 24].copy_from_slice(&1000u32.to_le_bytes());
    assert_eq!(Archive::open(&z).err(), Some(OpenError::NotAnArchive));
    // A central directory that claims to extend past the end record.
    let mut z = good.clone();
    let e = z.len() - 22;
    z[e + 12..e + 16].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
    assert_eq!(Archive::open(&z).err(), Some(OpenError::NotAnArchive));
    // More members declared than the directory holds.
    let mut z = good.clone();
    z[e + 8..e + 10].copy_from_slice(&9u16.to_le_bytes());
    z[e + 10..e + 12].copy_from_slice(&9u16.to_le_bytes());
    assert_eq!(Archive::open(&z).err(), Some(OpenError::NotAnArchive));
}

#[test]
fn local_and_central_disagree() {
    // The directory says `safe.txt`; the local header says `../evil`.
    let mut m = stored("safe.txt", b"x");
    m.local_name = b"../evil.".to_vec();
    assert_eq!(Archive::open(&zip(&[m])).err(), Some(OpenError::NotAnArchive));
}

#[test]
fn tar_sizes() {
    // A size far past the end of the archive, in octal and in base-256.
    let mut t = tar(&[("a", b'0', b"hello", "")]);
    t[124..136].copy_from_slice(b"77777777777\0");
    let mut h: [u8; 512] = t[..512].try_into().unwrap();
    fix_checksum(&mut h);
    t[..512].copy_from_slice(&h);
    assert_eq!(Archive::open(&t).err(), Some(OpenError::NotAnArchive));
    for first in [0x80u8, 0xff] {
        let mut h: [u8; 512] = tar(&[("a", b'0', b"hello", "")])[..512].try_into().unwrap();
        h[124] = first;
        h[125..136].copy_from_slice(&[0x7f; 11]);
        fix_checksum(&mut h);
        t[..512].copy_from_slice(&h);
        assert_eq!(Archive::open(&t).err(), Some(OpenError::NotAnArchive));
    }
    // A pax size that overrides the header's and runs past the end.
    let t = tar(&[("pax", b'x', &pax("size", "99999999999"), ""), ("a", b'0', b"hello", "")]);
    assert_eq!(Archive::open(&t).err(), Some(OpenError::NotAnArchive));
    // A pax record whose length runs past the header's data.
    let t = tar(&[("pax", b'x', b"99 path=a\n", ""), ("a", b'0', b"hello", "")]);
    assert_eq!(Archive::open(&t).err(), Some(OpenError::NotAnArchive));
    // A bad checksum.
    let mut t = tar(&[("a", b'0', b"hello", "")]);
    t[0] = b'b';
    assert_eq!(Archive::open(&t).err(), Some(OpenError::NotAnArchive));
}

#[test]
fn pax_and_gnu_names_are_checked_too() {
    // The name that counts is the pax or GNU one, not the header's.
    let t = tar(&[("pax", b'x', &pax("path", "../evil"), ""), ("innocent", b'0', b"x", "")]);
    let a = Archive::open(&t).unwrap();
    assert_eq!(a.entries()[0].name, b"../evil");
    assert_eq!(a.plan().unwrap_err().why, Why::Path);
    let t = tar(&[("././@LongLink", b'L', b"../evil\0", ""), ("innocent", b'0', b"x", "")]);
    assert_eq!(why(&t), Why::Path);
    let t = tar(&[("././@LongLink", b'K', b"../..\0", ""), ("d/l", b'2', b"", "ok")]);
    assert_eq!(why(&t), Why::SymlinkTarget);
    let t = tar(&[("pax", b'x', &pax("linkpath", "/etc"), ""), ("l", b'2', b"", "ok")]);
    let a = Archive::open(&t).unwrap();
    assert_eq!(a.entries()[0].kind, Kind::Symlink);
    assert_eq!(a.plan().unwrap_err().why, Why::SymlinkTarget);
}

#[cfg(unix)]
#[test]
fn nothing_is_written_when_refused() {
    let dir = std::env::temp_dir().join(format!("varchive-refuse-{}", std::process::id()));
    let root = dir.join("root");
    std::fs::create_dir_all(&root).unwrap();
    let t = tar(&[("fine.txt", b'0', b"x", ""), ("link", b'2', b"", ".."), ("link/escaped.txt", b'0', b"x", "")]);
    let a = Archive::open(&t).unwrap();
    assert!(matches!(verilith_archive::extract::extract(&a, &root), Err(verilith_archive::extract::ExtractError::Rejected(_))));
    assert_eq!(std::fs::read_dir(&root).unwrap().count(), 0);
    assert!(!dir.join("escaped.txt").exists());
    std::fs::remove_dir_all(&dir).unwrap();
}
