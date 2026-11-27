//! Regex, verilith-regex's Rust API (`Regex::search_with` with reused
//! scratch and slots) against RE2 through cre2 (suites/regex/regex.c): the
//! same patterns, cases and check value (matches * 2^32 + total length of
//! the match and its first three groups).
use verilith_regex::Regex;

const PATTERNS: &[(&str, &str)] = &[
    ("literal", "Copperfield"),
    ("literal-nocase", "(?i)copperfield"),
    ("alternation", "Agnes|Dora|Steerforth|Peggotty|Micawber"),
    ("class-run", "[A-Z][a-z]+ [A-Z][a-z]+"),
    ("word-suffix", "\\b\\w+ing\\b"),
    ("unicode-words", "\\p{Lu}\\p{Ll}+"),
    ("digits", "[0-9]{2,4}"),
    ("url-host", "https?://([^/?#\\s]+)"),
    ("tld", "\\.(?:com|org|net)\\b"),
    ("email", "[\\w.+-]+@[\\w-]+\\.[\\w.-]+"),
    ("captures", "(\\w+)=(\\w*)(&|$)"),
    ("no-match", "\\x{2603}zzz"),
];
const MAXG: usize = 4;
const NONE: usize = usize::MAX;

fn main() {
    let dir = vbrun::data_dir();
    let mut r = vbrun::Runner::new();
    for name in vbrun::list_dir(&dir) {
        let text = std::fs::read(format!("{dir}/{name}")).unwrap();
        for &(pname, pat) in PATTERNS {
            let re = Regex::new(pat.as_bytes()).unwrap_or_else(|_| panic!("pattern {pname} does not compile"));
            let ng = re.groups().min(MAXG);
            let mut sc = re.scratch();
            let mut out = re.slots();
            let t = text.clone();
            r.case(format!("{pname}/{name}"), t.len() as u64, move || {
                let t = std::hint::black_box(&t);
                let (mut n, mut total, mut pos) = (0u64, 0u64, 0usize);
                while pos <= t.len() && re.search_with(t, pos, &mut sc, &mut out).0 {
                    n += 1;
                    for g in 0..ng {
                        if out[2 * g] != NONE {
                            total += (out[2 * g + 1] - out[2 * g]) as u64;
                        }
                    }
                    let (s, e) = (out[0], out[1]);
                    pos = if e > s { e } else { e + 1 };
                }
                (n << 32) + total
            });
        }
    }
    r.main();
}
