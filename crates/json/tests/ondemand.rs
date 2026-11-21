// The on-demand reader against the tape parser: reading everything must
// accept the same texts and give the same values; skipping, leaving and
// searching must end where the tape says the value ends; and no sequence
// of calls may panic on any input.
use verilith_json::ondemand::{Mismatch, Reader};
use verilith_json::{Type, Value};

const DEPTH: usize = 1000;

fn dump_tape(v: Value, out: &mut Vec<u8>) {
    match v.kind() {
        Type::Null => out.push(b'n'),
        Type::Bool => out.push(if v.as_bool().unwrap() { b't' } else { b'f' }),
        Type::Number => {
            out.push(b'#');
            out.extend_from_slice(v.as_number_str().unwrap().as_bytes());
            out.extend_from_slice(format!("={:016x}", v.as_f64().unwrap().to_bits()).as_bytes());
        }
        Type::String => {
            let b = v.as_bytes().unwrap();
            out.extend_from_slice(format!("\"{}:", b.len()).as_bytes());
            out.extend_from_slice(&b);
        }
        Type::Array => {
            out.push(b'[');
            for e in v.elements().unwrap() {
                dump_tape(e, out);
            }
            out.push(b']');
        }
        Type::Object => {
            out.push(b'{');
            for (k, e) in v.members().unwrap() {
                let b = k.as_bytes();
                out.extend_from_slice(format!("\"{}:", b.len()).as_bytes());
                out.extend_from_slice(&b);
                dump_tape(e, out);
            }
            out.push(b'}');
        }
    }
}

fn dump_od(r: &mut Reader, buf: &mut Vec<u8>, out: &mut Vec<u8>, depth: usize) -> Result<(), Mismatch> {
    match r.peek() {
        b'n' => {
            if !r.null() {
                return Err(Mismatch);
            }
            out.push(b'n');
        }
        b't' | b'f' => out.push(if r.bool()? { b't' } else { b'f' }),
        b'"' => {
            let s = r.str(buf)?;
            out.extend_from_slice(format!("\"{}:", s.len()).as_bytes());
            out.extend_from_slice(s);
        }
        b'[' => {
            if depth == 0 {
                return Err(Mismatch);
            }
            r.arr_begin()?;
            out.push(b'[');
            while r.arr_next()? {
                dump_od(r, buf, out, depth - 1)?;
            }
            out.push(b']');
        }
        b'{' => {
            if depth == 0 {
                return Err(Mismatch);
            }
            r.obj_begin()?;
            out.push(b'{');
            while r.obj_next()? {
                let k = r.key()?;
                out.extend_from_slice(format!("\"{}:", k.len()).as_bytes());
                out.extend_from_slice(k);
                dump_od(r, buf, out, depth - 1)?;
            }
            out.push(b'}');
        }
        _ => {
            let s = r.source();
            let a = r.offset();
            let x = r.f64()?;
            let b = a + s[a..].iter().take_while(|c| !b" \t\n\r,]}".contains(c)).count();
            out.push(b'#');
            out.extend_from_slice(&s[a..b]);
            out.extend_from_slice(format!("={:016x}", x.to_bits()).as_bytes());
        }
    }
    Ok(())
}

fn rng(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

/// Reads some values, skips others, leaves containers early.
fn mixed(r: &mut Reader, buf: &mut Vec<u8>, seed: &mut u64, depth: usize) -> Result<(), Mismatch> {
    if depth == 0 || rng(seed) % 4 == 0 {
        return r.skip();
    }
    match r.peek() {
        b'n' => {
            if !r.null() {
                return Err(Mismatch);
            }
        }
        b't' | b'f' => {
            r.bool()?;
        }
        b'"' => {
            r.str(buf)?;
        }
        b'[' => {
            r.arr_begin()?;
            while r.arr_next()? {
                match rng(seed) % 8 {
                    0 => return r.leave(),
                    1 | 2 => {}
                    _ => mixed(r, buf, seed, depth - 1)?,
                }
            }
        }
        b'{' => {
            r.obj_begin()?;
            if rng(seed) % 4 == 0 {
                if r.find(b"id")? {
                    mixed(r, buf, seed, depth - 1)?;
                    return r.leave();
                }
                return Ok(());
            }
            while r.obj_next()? {
                match rng(seed) % 3 {
                    0 => r.key_skip()?,
                    1 => {
                        r.key()?;
                    }
                    _ => {
                        r.key_is(b"a")?;
                    }
                }
                match rng(seed) % 8 {
                    0 => return r.leave(),
                    1 | 2 => {}
                    _ => mixed(r, buf, seed, depth - 1)?,
                }
            }
        }
        _ => {
            if rng(seed) % 2 == 0 {
                r.f64()?;
            } else {
                r.num_raw()?;
            }
        }
    }
    Ok(())
}

/// Calls in no sensible order: nothing may panic.
fn chaos(r: &mut Reader, buf: &mut Vec<u8>, seed: &mut u64) {
    for _ in 0..200 {
        match rng(seed) % 16 {
            0 => drop(r.skip()),
            1 => drop(r.arr_begin()),
            2 => drop(r.arr_next()),
            3 => drop(r.obj_begin()),
            4 => drop(r.obj_next()),
            5 => drop(r.leave()),
            6 => drop(r.key().map(|_| ())),
            7 => drop(r.key_is(b"a")),
            8 => drop(r.find(b"a")),
            9 => drop(r.str(buf).map(|_| ())),
            10 => drop(r.f64()),
            11 => drop(r.i64()),
            12 => drop(r.null()),
            13 => drop(r.bool()),
            14 => drop(r.key_skip()),
            _ => {
                r.peek();
                r.offset();
                r.at_end();
            }
        }
    }
}

pub fn check(data: &[u8]) {
    let tape = verilith_json::parse(data);
    let mut idx = Vec::new();
    let mut buf = Vec::new();
    let mut got = Vec::new();
    let full = match Reader::new(data, &mut idx) {
        Some(mut r) => dump_od(&mut r, &mut buf, &mut got, DEPTH).is_ok() && r.at_end(),
        None => false,
    };
    match &tape {
        Ok(doc) => {
            assert!(full, "tape accepts, a full on-demand read does not");
            let mut want = Vec::new();
            dump_tape(doc.root(), &mut want);
            assert!(want == got, "values differ");
            let mut idx = Vec::new();
            let mut r = Reader::new(data, &mut idx).unwrap();
            assert!(r.skip().is_ok() && r.at_end(), "skip of the document");
            for s in 1..6u64 {
                let mut idx = Vec::new();
                let mut r = Reader::new(data, &mut idx).unwrap();
                let mut seed = s.wrapping_mul(0x9E3779B97F4A7C15) ^ data.len() as u64 | 1;
                assert!(mixed(&mut r, &mut buf, &mut seed, DEPTH).is_ok(), "mixed read");
                assert!(r.at_end(), "mixed read ends at the end");
            }
        }
        Err(_) => assert!(!full, "a full on-demand read accepts, the tape does not"),
    }
    for s in 1..4u64 {
        let mut idx = Vec::new();
        if let Some(mut r) = Reader::new(data, &mut idx) {
            let mut seed = s.wrapping_mul(0xD1B54A32D192ED03) ^ data.len() as u64 | 1;
            let _ = mixed(&mut r, &mut buf, &mut seed, DEPTH);
            chaos(&mut r, &mut buf, &mut seed);
        }
    }
}

const CASES: &[&[u8]] = &[
        b"null", b" true ", b"false", b"0", b"-1.5e3", b"\"\"", b"\"a\\n\\u00e9\\ud83d\\ude00\"", b"[]", b"{}",
        b"[1,2,3]", b"{\"a\":1,\"b\":[true,null,{\"c\":\"d\"}],\"a\":2}", b"[[[[]]],{\"\":{}}]",
        b"\xEF\xBB\xBF[1]", b"{\"k\\u0061\":1,\"a\":2}", b"[\"x\\\\\",\"\\\"\",\"]\",\"{\"]",
        // Rejected.
        b"", b" ", b"[", b"]", b"{", b"}", b"[1,]", b"[,1]", b"{\"a\"}", b"{\"a\":}", b"{\"a\":1,}", b"[1 2]",
        b"nul", b"truex", b"01", b"1.", b"-", b"\"", b"\"\\x\"", b"\"\x01\"", b"[1]]", b"{}{}", b"1 2", b"[\"a\":1]",
        b"{1:2}", b"\xff", b"[\"\xff\"]", b"{\"a\":1 \"b\":2}", b"[1}", b"{\"a\":1]", b"\\", b"[\\]", b"tru\\e",
        b"1\\", b"[1\\,2]", b"{\"a\\\":1}", b"\"a\" \0}", b"\0", b"[\0]",
];

#[test]
fn small_cases() {
    for c in CASES {
        check(c);
    }
}

/// Random edits of the small cases (and of JSON_TEST_SUITE's files if set):
/// most are no longer JSON, many still pass stage 1.
#[test]
fn mutations() {
    let mut seeds: Vec<Vec<u8>> = CASES.iter().map(|c| c.to_vec()).collect();
    if let Ok(dir) = std::env::var("JSON_TEST_SUITE") {
        for entry in std::fs::read_dir(dir).unwrap() {
            let data = std::fs::read(entry.unwrap().path()).unwrap();
            if data.len() < 4096 {
                seeds.push(data);
            }
        }
    }
    let rounds: usize = std::env::var("ONDEMAND_ROUNDS").ok().and_then(|s| s.parse().ok()).unwrap_or(20_000);
    let pool = b"[]{},:\"\\ \n0123456789-+.eEtruefalsn\x00\x7f\xc3\xa9u";
    let mut seed = 0x243F6A8885A308D3u64;
    for _ in 0..rounds {
        let mut v = seeds[rng(&mut seed) as usize % seeds.len()].clone();
        for _ in 0..1 + rng(&mut seed) % 4 {
            let at = rng(&mut seed) as usize % (v.len() + 1);
            let c = pool[rng(&mut seed) as usize % pool.len()];
            match rng(&mut seed) % 4 {
                0 => v.insert(at, c),
                1 if at < v.len() => v[at] = c,
                2 if at < v.len() => drop(v.remove(at)),
                _ => {
                    let other = &seeds[rng(&mut seed) as usize % seeds.len()];
                    let cut = rng(&mut seed) as usize % (other.len() + 1);
                    v.truncate(at);
                    v.extend_from_slice(&other[cut..]);
                }
            }
        }
        if std::panic::catch_unwind(|| check(&v)).is_err() {
            panic!("failing input: {:?}", String::from_utf8_lossy(&v));
        }
    }
}

#[test]
fn partial_reads() {
    let src = br#"{"skip": {"deep": [1, {"x": "]}"}, [[]]]}, "id": 7, "k\u0065y": "v\n", "tail": [1.5, "s", null]}"#;
    let mut idx = Vec::new();
    let mut buf = Vec::new();
    let mut r = Reader::new(src, &mut idx).unwrap();
    r.obj_begin().unwrap();
    assert_eq!(r.find(b"id"), Ok(true));
    assert_eq!(r.i64(), Ok(7));
    assert_eq!(r.find(b"key"), Ok(true));
    assert_eq!(r.str(&mut buf).unwrap(), b"v\n");
    assert_eq!(r.find(b"tail"), Ok(true));
    r.arr_begin().unwrap();
    assert_eq!(r.arr_next(), Ok(true));
    assert_eq!(r.f64(), Ok(1.5));
    assert_eq!(r.arr_next(), Ok(true));
    // Leave without reading "s" or what follows.
    r.leave().unwrap();
    assert_eq!(r.find(b"none"), Ok(false));
    assert!(r.at_end());

    // The wrong reader for the token is a mismatch and does not move.
    let mut idx = Vec::new();
    let mut r = Reader::new(b"[1]", &mut idx).unwrap();
    assert_eq!(r.obj_begin(), Err(Mismatch));
    assert_eq!(r.f64(), Err(Mismatch));
    assert_eq!(r.offset(), 0);
    r.arr_begin().unwrap();
    assert_eq!(r.arr_next(), Ok(true));
    assert_eq!(r.str(&mut buf).map(|_| ()), Err(Mismatch));
    assert_eq!(r.i64(), Ok(1));
    assert_eq!(r.arr_next(), Ok(false));
    assert!(r.at_end());
}

/// Runs JSONTestSuite's test_parsing directory if JSON_TEST_SUITE points at
/// it, and every file of JSON_DATA if that is set.
#[test]
fn corpora() {
    for var in ["JSON_TEST_SUITE", "JSON_DATA"] {
        let Ok(dir) = std::env::var(var) else {
            eprintln!("{var} not set; skipping");
            continue;
        };
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_file() {
                eprintln!("{}", path.display());
                check(&std::fs::read(&path).unwrap());
            }
        }
    }
}
