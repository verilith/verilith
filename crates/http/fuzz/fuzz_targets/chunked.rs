//! The chunked decoder: decoding in one call or split at any point gives
//! the same body and the same outcome (the split-invariance theorem,
//! checked on the compiled code).
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_http::{Chunked, ChunkedDecoder};

fn run(input: &[u8], cuts: &[usize], keep: bool) -> Option<(Vec<u8>, Option<usize>)> {
    let mut d = if keep { ChunkedDecoder::keeping_trailers() } else { ChunkedDecoder::new() };
    let mut out = Vec::new();
    let mut start = 0;
    for &end in cuts.iter().chain(std::iter::once(&input.len())) {
        let mut piece = input[start..end].to_vec();
        match d.decode(&mut piece).ok()? {
            Chunked::More { out: n } => out.extend_from_slice(&piece[..n]),
            Chunked::Done { out: n, rest } => {
                out.extend_from_slice(&piece[..n]);
                return Some((out, Some(end - rest)));
            }
        }
        start = end;
    }
    Some((out, None))
}

fuzz_target!(|data: &[u8]| {
    if data.len() < 3 {
        return;
    }
    let (a, b, keep, input) = (data[0] as usize, data[1] as usize, data[2] & 1 != 0, &data[3..]);
    let n = input.len();
    let mut cuts = vec![a * n / 255, b * n / 255];
    cuts.sort();
    let whole = run(input, &[], keep);
    let split = run(input, &cuts, keep);
    // A split can only end an invalid input earlier or later; on valid
    // input the results agree exactly.
    if let (Some(w), Some(s)) = (&whole, &split) {
        assert_eq!(w, s);
    } else {
        assert_eq!(whole.is_none(), split.is_none());
    }
});
