// One-shot decompression: plain Rust over the verified `Stream`, which
// decides every byte of the output.
use crate::stream::{Result as StreamResult, Stream};

/// Why [`decompress`] failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The input is not a valid Brotli stream.
    Corrupt,
    /// The input ends before the stream does.
    Truncated,
    /// The output would be longer than the limit.
    TooLarge,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Corrupt => "corrupt Brotli data",
            Error::Truncated => "the input ends before the Brotli stream does",
            Error::TooLarge => "the output would be larger than the limit",
        })
    }
}

impl std::error::Error for Error {}

/// Decompresses the Brotli stream `input`, if its output is at most
/// `limit` bytes. Bytes after the end of the stream are ignored.
pub fn decompress(input: &[u8], limit: usize) -> Result<Vec<u8>, Error> {
    let mut s = Stream::open();
    let mut out = Vec::new();
    let mut buf = vec![0u8; 64 * 1024];
    let mut ip = 0;
    loop {
        let (r, used, made) = s.decompress(&input[ip..], &mut buf);
        ip += used;
        if made > limit - out.len() {
            return Err(Error::TooLarge);
        }
        out.extend_from_slice(&buf[..made]);
        match r {
            StreamResult::Success => return Ok(out),
            StreamResult::Error => return Err(Error::Corrupt),
            StreamResult::NeedsMoreInput => return Err(Error::Truncated),
            StreamResult::NeedsMoreOutput => {}
        }
    }
}
