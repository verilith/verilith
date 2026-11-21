//! Carrying out an extraction plan on a real file system (Unix).
//!
//! This file is plain Rust and is trusted: it must do what the plan says
//! and nothing else. What the proofs say about the plan is in `plan.rs`;
//! what is assumed about this file and about the file system is in
//! TRUST.md. In short: the directory `root` must hold no symbolic links of
//! its own on the paths the archive uses, and nothing else may change it
//! while the extraction runs.
use crate::api::Archive;
use crate::plan::{Item, Rejected};
use crate::read::Error;
use crate::spec::Kind;
use std::ffi::OsStr;
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub enum ExtractError {
    /// The planner refused the archive. Nothing was written.
    Rejected(Rejected),
    /// A member's data could not be read.
    Read(usize, Error),
    /// The file system refused a step.
    Io(usize, std::io::Error),
}

/// The components joined with `/`.
pub fn join(p: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for (i, c) in p.iter().enumerate() {
        if i > 0 {
            out.push(b'/');
        }
        out.extend_from_slice(c);
    }
    out
}

fn under(root: &Path, p: &[Vec<u8>]) -> PathBuf {
    root.join(OsStr::from_bytes(&join(p)))
}

/// Carries out one step of a plan under `root`.
pub fn extract_item(a: &Archive, it: &Item, root: &Path) -> Result<(), ExtractError> {
    let io = |e| ExtractError::Io(it.entry, e);
    let dst = under(root, &it.path);
    if let Some(parent) = dst.parent() {
        std::fs::create_dir_all(parent).map_err(io)?;
    }
    match it.kind {
        Kind::Dir => std::fs::create_dir_all(&dst).map_err(io),
        Kind::File => {
            let data = a.read(it.entry).map_err(|e| ExtractError::Read(it.entry, e))?;
            let mode = a.entries()[it.entry].mode & 0o777;
            // `create_new` is O_CREAT|O_EXCL: it never opens an existing
            // file and never follows a link in the last component.
            let mut f = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(if mode == 0 { 0o644 } else { mode })
                .open(&dst)
                .map_err(io)?;
            f.write_all(&data).map_err(io)
        }
        Kind::Symlink => std::os::unix::fs::symlink(OsStr::from_bytes(&join(&it.target)), &dst).map_err(io),
        Kind::Hardlink => std::fs::hard_link(under(root, &it.target), &dst).map_err(io),
        Kind::Other => Ok(()),
    }
}

/// Extracts the whole archive under `root`, which must exist. The archive
/// is planned first; if the planner refuses it, nothing is written.
/// Returns the number of steps carried out.
pub fn extract(a: &Archive, root: &Path) -> Result<usize, ExtractError> {
    let items = a.plan().map_err(ExtractError::Rejected)?;
    for it in &items {
        extract_item(a, it, root)?;
    }
    Ok(items.len())
}
