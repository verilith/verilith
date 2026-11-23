use verilith_regex::{Error, Regex};

const N: usize = usize::MAX;

fn caps(pat: &str, text: &str) -> Option<Vec<usize>> {
    Regex::new(pat.as_bytes()).unwrap().captures_at(text.as_bytes(), 0)
}

#[test]
fn basics() {
    assert_eq!(caps("a(b*)c", "xabbbcx"), Some(vec![1, 6, 2, 5]));
    assert_eq!(caps("(a)|b", "b"), Some(vec![0, 1, N, N]));
    assert_eq!(caps("a+?", "aaa"), Some(vec![0, 1]));
    assert_eq!(caps("(a|ab)(c|bcd)(d*)", "abcd"), Some(vec![0, 4, 0, 1, 1, 4, 4, 4]));
    assert_eq!(caps("x", "abc"), None);
    assert_eq!(caps("", "abc"), Some(vec![0, 0]));
    assert_eq!(caps("$", "abc"), Some(vec![3, 3]));
}

#[test]
fn unicode_and_flags() {
    assert_eq!(caps(r"\p{Greek}+", "abc αβγ d"), Some(vec![4, 10]));
    assert_eq!(caps(r"(?i)straße", "STRASSE Straße"), Some(vec![8, 15]));
    assert_eq!(caps(r"(?i)k", "\u{212A}"), Some(vec![0, 3]));
    assert_eq!(caps(r"(?m)^b$", "a\nb\nc"), Some(vec![2, 3]));
    assert_eq!(caps(r"(?s)a.b", "a\nb"), Some(vec![0, 3]));
    assert_eq!(caps(r"a.b", "a\nb"), None);
    assert_eq!(caps(r"\bfoo\b", "a foo."), Some(vec![2, 5]));
    assert_eq!(caps(r"[[:^alpha:][:digit:]]+", "ab12-c"), Some(vec![2, 5]));
    // A byte that starts no UTF-8 sequence matches no class.
    assert_eq!(Regex::new(b".").unwrap().captures_at(b"\xff", 0), None);
}

#[test]
fn errors() {
    assert!(matches!(Regex::new(b"a("), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"a**"), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"\\1"), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"(?=a)"), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"a{1001}"), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"(?P<n>a)(?P<n>b)"), Err(Error::Syntax(_))));
    assert!(matches!(Regex::new(b"\xff"), Err(Error::BadUtf8)));
    assert!(matches!(Regex::new("(".repeat(300).as_bytes()), Err(Error::TooBig)));
}

#[test]
fn names() {
    let re = Regex::new(br"(?P<y>\d+)-(?<m>\d+)").unwrap();
    assert_eq!(re.groups(), 3);
    assert_eq!(re.names, vec![(b"y".to_vec(), 1), (b"m".to_vec(), 2)]);
}

/// Patterns that take exponential time in a backtracking matcher.
#[test]
fn linear_time() {
    let text = "a".repeat(20_000);
    for pat in ["(a*)*b", "(a|aa)+b", "(a+)+b", "(?:a?){200}a{200}b", r"(\w+\s?)*!"] {
        let re = Regex::new(pat.as_bytes()).unwrap();
        let t = std::time::Instant::now();
        assert_eq!(re.captures_at(text.as_bytes(), 0), None, "{pat}");
        assert!(t.elapsed().as_secs() < 60, "{pat} took {:?}", t.elapsed());
    }
}

#[test]
fn first_byte_scan_at_every_offset() {
    // One byte starts every match, so the search runs 16 bytes at a time.
    let re = Regex::new(b"Zq").unwrap();
    for len in 0..70usize {
        for at in 0..len {
            for from in 0..=len {
                let mut t = vec![b'a'; len];
                if at + 1 < len {
                    t[at] = b'Z';
                    t[at + 1] = b'q';
                }
                // A lone first byte earlier on must not stop the search.
                if at >= 3 {
                    t[at - 3] = b'Z';
                }
                let want = if at + 1 < len && from <= at { Some(vec![at, at + 2]) } else { None };
                assert_eq!(re.captures_at(&t, from), want, "len {len} at {at} from {from}");
            }
        }
    }
}

#[test]
fn stored_steps_agree_with_fresh_memory() {
    // A search that reuses working memory replays steps it stored in
    // earlier searches; one with fresh memory computes them anew. Both
    // must report the same matches and groups from every start.
    let pats: [&str; 8] = [
        r"https?://([^/?#\s]+)",
        r"(\w+)=(\w*)(&|$)",
        r"\b(\w+)ing\b",
        r"(a|ab)(c|bcd)(d*)",
        r"(?m)^(\w+):\s*(.*?)$",
        r"(\d+)-(\d+)?",
        r"((a+)(b*))+c",
        r"(é|e)+(x)?",
    ];
    let texts: [&str; 6] = [
        "see http://a.example/x?k=v&key2=&z=9 and https://b.org#f\nname: value \nrunning=1&sing",
        "abcd abbcdd aabbc ac 12-34 5- 6-7-8",
        "k=v",
        "",
        "héllo=wörld&ée=x éex running\nkey: v\n",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaac",
    ];
    for pat in pats {
        let re = Regex::new(pat.as_bytes()).unwrap();
        let mut sc = re.scratch();
        let mut out = re.slots();
        for round in 0..2 {
            for text in texts {
                let t = text.as_bytes();
                for from in 0..=t.len() {
                    let (found, _) = re.search_with(t, from, &mut sc, &mut out);
                    let got = if found { Some(out.clone()) } else { None };
                    assert_eq!(got, re.captures_at(t, from), "{pat} on {text:?} from {from} round {round}");
                }
            }
        }
    }
}

#[test]
fn required_byte_skip_agrees_with_plain_search() {
    // A pattern that cannot match without one particular byte lets the
    // search jump ahead to it. Writing that byte as a class of two
    // characters, the second absent from the text, turns the jump off
    // and must give the same matches and groups from every start.
    let pats: [(&str, &str); 6] = [
        (r"(\w+)=(\w*)(&|$)", r"(\w+)[=☃](\w*)(&|$)"),
        (r"[\w.+-]+@[\w-]+\.[\w.-]+", r"[\w.+-]+[@☃][\w-]+\.[\w.-]+"),
        (r"\b\w+ing\b", r"\b\w+in[g☃]\b"),
        (r"(a|b)*#(é|e)+", r"(a|b)*[#☃](é|e)+"),
        (r"(?s).*Q.*", r"(?s).*[Q☃].*"),
        (r"x?=|y=", r"x?[=☃]|y[=☃]"),
    ];
    // Texts over a small alphabet, so that the byte turns up at every
    // distance from the start, the end, and bytes outside the pattern.
    let alpha: [&str; 12] = ["a", "b", "g", "in", "=", "@", ".", " ", "é", "#", "Q", "&"];
    let mut texts: Vec<String> = vec![String::new(), "=".into(), "a=".into(), "=a".into()];
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    for len in 1..60 {
        for _ in 0..4 {
            let mut t = String::new();
            for _ in 0..len {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                t.push_str(alpha[((seed >> 33) % 12) as usize]);
            }
            texts.push(t);
        }
    }
    for (pat, plain) in pats {
        let re = Regex::new(pat.as_bytes()).unwrap();
        let re2 = Regex::new(plain.as_bytes()).unwrap();
        let mut sc = re.scratch();
        let mut out = re.slots();
        for text in &texts {
            let t = text.as_bytes();
            for from in 0..=t.len() {
                let (found, _) = re.search_with(t, from, &mut sc, &mut out);
                let got = if found { Some(out.clone()) } else { None };
                assert_eq!(got, re2.captures_at(t, from), "{pat} on {text:?} from {from}");
            }
        }
    }
}

#[test]
fn range_scan_agrees_with_plain_search() {
    // When the bytes a match can start with are few and lie in up to
    // three ranges, the search looks for them 16 at a time. An extra
    // branch that starts with a lower-case letter and cannot match
    // these texts turns that off and must change nothing.
    let pats: [&str; 6] = [
        r"[0-9]{2,4}",
        r"[A-Z][a-z]+ [A-Z][a-z]+",
        r"Agnes|Dora|Steerforth|Peggotty|Micawber",
        r"\p{Lu}\p{Ll}+",
        r"([0-9]+)-([A-F]+)",
        r"[#-%]x|[É-Ö]+y?",
    ];
    let alpha: [&str; 16] =
        ["a", "b", "x", " ", "7", "42", "A", "Do", "Dora", "Agnes", "É", "Ö", "#", "-", "F", "é"];
    let mut texts: Vec<String> = vec![String::new(), "7".into(), "A".into()];
    let mut seed: u64 = 0x2545_F491_4F6C_DD1D;
    for len in 1..70 {
        for _ in 0..4 {
            let mut t = String::new();
            for _ in 0..len {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                t.push_str(alpha[((seed >> 33) % 16) as usize]);
            }
            texts.push(t);
        }
    }
    for pat in pats {
        let plain = format!("(?:{pat})|zqzq");
        let re = Regex::new(pat.as_bytes()).unwrap();
        let re2 = Regex::new(plain.as_bytes()).unwrap();
        let mut sc = re.scratch();
        let mut out = re.slots();
        for text in &texts {
            let t = text.as_bytes();
            for from in 0..=t.len() {
                let (found, _) = re.search_with(t, from, &mut sc, &mut out);
                let got = if found { Some(out.clone()) } else { None };
                let want = re2.captures_at(t, from).map(|v| v[..out.len()].to_vec());
                assert_eq!(got, want, "{pat} on {text:?} from {from}");
            }
        }
    }
}

#[test]
fn limits() {
    // Patterns may be longer than 64 KiB.
    let long = "a".repeat(70_000);
    assert!(Regex::new(long.as_bytes()).is_ok());
    // The instruction limit is the caller's.
    let big = "a{1000}".repeat(300);
    assert!(matches!(Regex::new(big.as_bytes()), Err(Error::TooBig)));
    assert!(matches!(Regex::with_limit(b"a{1000}", 900), Err(Error::TooBig)));
    assert!(Regex::with_limit(b"a{1000}", 2000).is_ok());
    assert!(matches!(Regex::with_limit(b"abc", 3), Err(Error::TooBig)));
    // Repetitions stop expanding at the limit, so this is refused at once
    // rather than after building millions of nodes.
    let wide = format!("(?:{}){{1000}}", "a".repeat(16_000));
    let t = std::time::Instant::now();
    assert!(matches!(Regex::new(wide.as_bytes()), Err(Error::TooBig)));
    assert!(t.elapsed().as_secs() < 5);
    let many = "(?:a{1000})".repeat(2_000);
    assert!(matches!(Regex::new(many.as_bytes()), Err(Error::TooBig)));
}
