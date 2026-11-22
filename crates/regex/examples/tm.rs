// Times finding every match of each pattern in a file: tm FILE PATTERN...
use std::time::Instant;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let text = std::fs::read(&a[1]).unwrap();
    for pat in &a[2..] {
        let re = verilith_regex::Regex::new(pat.as_bytes()).ok().unwrap();
        let mut sc = re.scratch();
        let mut out = re.slots();
        let mut best = u128::MAX;
        let mut cnt = 0;
        let passes: usize = std::env::var("TM_PASSES").ok().and_then(|v| v.parse().ok()).unwrap_or(5);
        for _ in 0..passes {
            let t = Instant::now();
            cnt = 0;
            let mut p = 0;
            while p <= text.len() {
                let (m, _) = re.search_with(&text, p, &mut sc, &mut out);
                if !m {
                    break;
                }
                cnt += 1;
                p = if out[1] > out[0] { out[1] } else { out[1] + 1 };
            }
            best = best.min(t.elapsed().as_nanos());
        }
        println!("{:40} {:6} matches {:8.3} ns/byte", pat, cnt, best as f64 / text.len() as f64);
    }
}
