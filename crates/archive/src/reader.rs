//! Recognising an archive: tar if the bytes are a tar archive with at
//! least one member, else zip, else an empty tar archive.
use crate::spec::*;
use crate::tar::parse_tar;
use crate::zip::{parse_zip, Entry};
#[cfg(verus_only)]
use crate::zip::views;
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Format {
    Zip,
    Tar,
}

/// The members of `b` and the format they were read as; `None` exactly
/// when `b` is neither a zip nor a tar archive.
pub fn parse(b: &[u8]) -> (r: Option<(Format, Vec<Entry>)>)
    ensures
        match r {
            Some((f, es)) => (match f {
                Format::Tar => tar(b@) == Some(views(es@)),
                Format::Zip => zip(b@) == Some(views(es@)),
            }) && disjoint(views(es@)) && in_bounds(views(es@), b@.len() as int),
            None => zip(b@) is None && tar(b@) is None,
        },
{
    let t = parse_tar(b);
    match t {
        Some(es) => {
            if es.len() > 0 {
                return Some((Format::Tar, es));
            }
            match parse_zip(b) {
                Some(zs) => Some((Format::Zip, zs)),
                None => Some((Format::Tar, es)),
            }
        },
        None => match parse_zip(b) {
            Some(zs) => Some((Format::Zip, zs)),
            None => None,
        },
    }
}

} // verus!
