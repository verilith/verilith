//! Runs a random sequence of cJSON building, editing, parsing and printing
//! calls against vjson's C ABI and against upstream cJSON side by side, and
//! checks that every call gives the same result. Build with ASan (the
//! cargo-fuzz default) to also catch memory errors in either.
#![no_main]
#![allow(unsafe_op_in_unsafe_fn)]
use libfuzzer_sys::fuzz_target;
use std::ffi::{CStr, CString};
use std::os::raw::{c_char, c_int};


#[path = "api.rs"]
mod api;
use api::{cJSON, Lib, UPSTREAM, VJSON};

struct Input<'a>(&'a [u8]);

impl Input<'_> {
    fn byte(&mut self) -> Option<u8> {
        let (&b, rest) = self.0.split_first()?;
        self.0 = rest;
        Some(b)
    }
    fn bytes(&mut self, max: usize) -> Vec<u8> {
        let n = (self.byte().unwrap_or(0) as usize % (max + 1)).min(self.0.len());
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        a.to_vec()
    }
    /// A C string from the input (cut at the first NUL).
    fn cstring(&mut self, max: usize) -> CString {
        let mut v = self.bytes(max);
        if let Some(i) = v.iter().position(|&b| b == 0) {
            v.truncate(i);
        }
        CString::new(v).unwrap()
    }
    fn number(&mut self) -> f64 {
        const NICE: [f64; 12] = [0.0, -0.0, 1.0, -1.0, 0.5, 1e21, 1e-7, 123456789.0, 3.14159, f64::NAN, f64::INFINITY, 2147483648.0];
        match self.byte().unwrap_or(0) {
            b @ 0..=127 => NICE[b as usize % NICE.len()],
            b @ 128..=191 => (b as f64 - 160.0) * 7.0,
            _ => {
                let mut x = [0u8; 8];
                for v in &mut x {
                    *v = self.byte().unwrap_or(0);
                }
                f64::from_le_bytes(x)
            }
        }
    }
}

/// Keys from a small set, so that lookups hit (and case matters).
static KEYS: [&CStr; 6] = [c"a", c"A", c"b", c"key", c"Key", c""];

/// The same tree in both libraries.
#[derive(Clone, Copy)]
struct Pair {
    v: *mut cJSON,
    u: *mut cJSON,
}

unsafe fn printed(lib: &Lib, item: *const cJSON, fmt: bool) -> Option<Vec<u8>> {
    let p = if fmt { (lib.print)(item) } else { (lib.print_unformatted)(item) };
    if p.is_null() {
        return None;
    }
    let s = CStr::from_ptr(p).to_bytes().to_vec();
    (lib.free)(p as *mut _);
    Some(s)
}

unsafe fn same(p: Pair, what: &str) {
    for fmt in [false, true] {
        let a = printed(&VJSON, p.v, fmt);
        let b = printed(&UPSTREAM, p.u, fmt);
        assert_eq!(
            a.as_deref().map(String::from_utf8_lossy),
            b.as_deref().map(String::from_utf8_lossy),
            "print differs after {what}"
        );
    }
}

/// Both pointers null or both not.
fn both(a: *mut cJSON, b: *mut cJSON, what: &str) -> Option<Pair> {
    assert_eq!(a.is_null(), b.is_null(), "{what}: one returned null");
    if a.is_null() {
        None
    } else {
        Some(Pair { v: a, u: b })
    }
}

macro_rules! call {
    ($f:ident ( $($a:expr),* )) => {
        ((VJSON.$f)($($a.0),*), (UPSTREAM.$f)($($a.1),*))
    };
}

/// An argument that is the same for both libraries.
fn s<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

fuzz_target!(|data: &[u8]| unsafe {
    let mut inp = Input(data);
    let mut pool: Vec<Pair> = Vec::new();
    let mut steps = 0;
    while let Some(op) = inp.byte() {
        steps += 1;
        if steps > 200 {
            break;
        }
        let pick = |inp: &mut Input, pool: &Vec<Pair>| -> Option<usize> {
            if pool.is_empty() {
                None
            } else {
                Some(inp.byte().unwrap_or(0) as usize % pool.len())
            }
        };
        let key = KEYS[inp.byte().unwrap_or(0) as usize % KEYS.len()].as_ptr();
        let index = inp.byte().unwrap_or(0) as c_int % 6 - 1;
        if std::env::var_os("TRACE").is_some() {
            eprintln!("op {} key {:?} index {index} pool {}", op % 32, CStr::from_ptr(key), pool.len());
        }
        let made = match op % 32 {
            0 => both((VJSON.create_null)(), (UPSTREAM.create_null)(), "CreateNull"),
            1 => both((VJSON.create_true)(), (UPSTREAM.create_true)(), "CreateTrue"),
            2 => {
                let b = inp.byte().unwrap_or(0) as c_int;
                let (a, u) = call!(create_bool(s(b)));
                both(a, u, "CreateBool")
            }
            3 => {
                let x = inp.number();
                let (a, u) = call!(create_number(s(x)));
                both(a, u, "CreateNumber")
            }
            4 => {
                let t = inp.cstring(12);
                let (a, u) = call!(create_string(s(t.as_ptr())));
                both(a, u, "CreateString")
            }
            5 => both((VJSON.create_array)(), (UPSTREAM.create_array)(), "CreateArray"),
            6 => both((VJSON.create_object)(), (UPSTREAM.create_object)(), "CreateObject"),
            7 => {
                // Parse text from the input.
                let t = inp.bytes(64);
                let (a, u) = call!(parse_with_length(s(t.as_ptr() as *const c_char), s(t.len())));
                // vjson rejects more than cJSON (RFC 8259), never less,
                // except that cJSON skips a BOM only when more than 4 bytes
                // follow from the start.
                if a.is_null() || u.is_null() {
                    assert!(a.is_null() || (t.starts_with(b"\xEF\xBB\xBF") && t.len() <= 4), "vjson accepted what cJSON rejects");
                    (VJSON.delete)(a);
                    (UPSTREAM.delete)(u);
                    None
                } else {
                    both(a, u, "ParseWithLength")
                }
            }
            8 => {
                let n = inp.byte().unwrap_or(0) as usize % 5;
                let xs: Vec<f64> = (0..n).map(|_| inp.number()).collect();
                let (a, u) = call!(create_double_array(s(xs.as_ptr()), s(n as c_int)));
                both(a, u, "CreateDoubleArray")
            }
            9 => {
                let n = inp.byte().unwrap_or(0) as usize % 5;
                let xs: Vec<c_int> = (0..n).map(|_| inp.byte().unwrap_or(0) as c_int * 1000003 - 99999).collect();
                let (a, u) = call!(create_int_array(s(xs.as_ptr()), s(n as c_int)));
                both(a, u, "CreateIntArray")
            }
            10 => {
                let n = inp.byte().unwrap_or(0) as usize % 4;
                let ts: Vec<CString> = (0..n).map(|_| inp.cstring(6)).collect();
                let ps: Vec<*const c_char> = ts.iter().map(|t| t.as_ptr()).collect();
                let (a, u) = call!(create_string_array(s(ps.as_ptr()), s(n as c_int)));
                both(a, u, "CreateStringArray")
            }
            11 => {
                let n = inp.byte().unwrap_or(0) as usize % 4;
                let xs: Vec<f32> = (0..n).map(|_| inp.number() as f32).collect();
                let (a, u) = call!(create_float_array(s(xs.as_ptr()), s(n as c_int)));
                both(a, u, "CreateFloatArray")
            }
            12 => {
                let t = inp.cstring(12);
                let (a, u) = call!(create_raw(s(t.as_ptr())));
                both(a, u, "CreateRaw")
            }
            // Moving one root into another.
            13..=17 => {
                let (Some(i), Some(j)) = (pick(&mut inp, &pool), pick(&mut inp, &pool)) else { continue };
                if i == j {
                    continue;
                }
                let (a, b) = (pool[i], pool[j]);
                let (r1, r2) = match op % 32 {
                    13 => call!(add_item_to_array((a.v, a.u), (b.v, b.u))),
                    14 => call!(add_item_to_object((a.v, a.u), s(key), (b.v, b.u))),
                    15 => call!(add_item_to_object_c_s((a.v, a.u), s(key), (b.v, b.u))),
                    16 => call!(insert_item_in_array((a.v, a.u), s(index), (b.v, b.u))),
                    _ => {
                        if inp.byte().unwrap_or(0) & 1 == 0 {
                            call!(replace_item_in_array((a.v, a.u), s(index), (b.v, b.u)))
                        } else {
                            call!(replace_item_in_object((a.v, a.u), s(key), (b.v, b.u)))
                        }
                    }
                };
                assert_eq!(r1, r2, "add/insert/replace result differs (op {op})");
                if r1 != 0 {
                    pool.remove(j);
                }
                let i = if j < i { i - 1 } else { i };
                same(pool[i], "add/insert/replace");
                None
            }
            18 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let (r1, r2) = if inp.byte().unwrap_or(0) & 1 == 0 {
                    call!(detach_item_from_array((a.v, a.u), s(index)))
                } else if inp.byte().unwrap_or(0) & 1 == 0 {
                    call!(detach_item_from_object((a.v, a.u), s(key)))
                } else {
                    call!(detach_item_from_object_case_sensitive((a.v, a.u), s(key)))
                };
                same(a, "detach");
                both(r1, r2, "Detach")
            }
            19 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                match inp.byte().unwrap_or(0) % 3 {
                    0 => call!(delete_item_from_array((a.v, a.u), s(index))),
                    1 => call!(delete_item_from_object((a.v, a.u), s(key))),
                    _ => call!(delete_item_from_object_case_sensitive((a.v, a.u), s(key))),
                };
                same(a, "delete from");
                None
            }
            20 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let rec = (inp.byte().unwrap_or(0) & 1) as c_int;
                let (r1, r2) = call!(duplicate((a.v, a.u), s(rec)));
                let d = both(r1, r2, "Duplicate");
                if let Some(d) = d {
                    let (c1, c2) = call!(compare((d.v, d.u), (a.v, a.u), s(1)));
                    assert_eq!(c1, c2, "Compare(duplicate) differs");
                }
                d
            }
            21 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool.remove(i);
                (VJSON.delete)(a.v);
                (UPSTREAM.delete)(a.u);
                None
            }
            22 => {
                let (Some(i), Some(j)) = (pick(&mut inp, &pool), pick(&mut inp, &pool)) else { continue };
                let (a, b) = (pool[i], pool[j]);
                let cs = (inp.byte().unwrap_or(0) & 1) as c_int;
                let (c1, c2) = call!(compare((a.v, a.u), (b.v, b.u), s(cs)));
                assert_eq!(c1, c2, "Compare differs");
                None
            }
            23 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let x = inp.number();
                let (r1, r2) = call!(set_number_helper((a.v, a.u), s(x)));
                assert_eq!(r1.to_bits(), r2.to_bits(), "SetNumberHelper differs");
                same(a, "SetNumberHelper");
                None
            }
            24 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let t = inp.cstring(16);
                let (r1, r2) = call!(set_valuestring((a.v, a.u), s(t.as_ptr())));
                assert_eq!(r1.is_null(), r2.is_null(), "SetValuestring differs");
                same(a, "SetValuestring");
                None
            }
            25 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let (r1, r2) = match inp.byte().unwrap_or(0) % 6 {
                    0 => call!(add_null_to_object((a.v, a.u), s(key))),
                    1 => {
                        let b = inp.byte().unwrap_or(0) as c_int;
                        call!(add_bool_to_object((a.v, a.u), s(key), s(b)))
                    }
                    2 => {
                        let x = inp.number();
                        call!(add_number_to_object((a.v, a.u), s(key), s(x)))
                    }
                    3 => {
                        let t = inp.cstring(8);
                        call!(add_string_to_object((a.v, a.u), s(key), s(t.as_ptr())))
                    }
                    4 => call!(add_array_to_object((a.v, a.u), s(key))),
                    _ => call!(add_object_to_object((a.v, a.u), s(key))),
                };
                assert_eq!(r1.is_null(), r2.is_null(), "Add*ToObject differs");
                same(a, "Add*ToObject");
                None
            }
            26 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let (n1, n2) = call!(get_array_size((a.v, a.u)));
                assert_eq!(n1, n2, "GetArraySize differs");
                let (g1, g2) = call!(get_array_item((a.v, a.u), s(index)));
                assert_eq!(g1.is_null(), g2.is_null(), "GetArrayItem differs");
                let (h1, h2) = call!(has_object_item((a.v, a.u), s(key)));
                assert_eq!(h1, h2, "HasObjectItem differs");
                let (o1, o2) = call!(get_object_item((a.v, a.u), s(key)));
                assert_eq!(o1.is_null(), o2.is_null(), "GetObjectItem differs");
                let (x1, x2) = call!(get_number_value((a.v, a.u)));
                assert_eq!(x1.to_bits(), x2.to_bits(), "GetNumberValue differs");
                None
            }
            27 => {
                // Minify printed text, then compare.
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                if let Some(t) = printed(&VJSON, a.v, true) {
                    let (mut x, mut y) = (t.clone(), t);
                    x.push(0);
                    y.push(0);
                    (VJSON.minify)(x.as_mut_ptr() as *mut c_char);
                    (UPSTREAM.minify)(y.as_mut_ptr() as *mut c_char);
                    assert_eq!(CStr::from_bytes_until_nul(&x).unwrap(), CStr::from_bytes_until_nul(&y).unwrap(), "Minify differs");
                }
                None
            }
            28 => {
                // Minify text from the input.
                let mut t = inp.cstring(48).into_bytes_with_nul();
                let mut t2 = t.clone();
                (VJSON.minify)(t.as_mut_ptr() as *mut c_char);
                (UPSTREAM.minify)(t2.as_mut_ptr() as *mut c_char);
                assert_eq!(t, t2, "Minify differs");
                None
            }
            29 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let n = inp.byte().unwrap_or(0) as usize;
                let fmt = (inp.byte().unwrap_or(0) & 1) as c_int;
                let mut b1 = vec![0x55u8; n + 1];
                let mut b2 = vec![0x55u8; n + 1];
                let r1 = (VJSON.print_preallocated)(a.v, b1.as_mut_ptr() as *mut c_char, n as c_int, fmt);
                let r2 = (UPSTREAM.print_preallocated)(a.u, b2.as_mut_ptr() as *mut c_char, n as c_int, fmt);
                // cJSON wants spare room in the buffer (its docs say 5 bytes
                // more than the text); vjson needs only the text and its NUL.
                // So vjson may succeed where cJSON does not.
                assert!(r1 != 0 || r2 == 0, "PrintPreallocated: cJSON fit, vjson did not");
                assert_eq!(b1[n], 0x55, "PrintPreallocated wrote past the buffer");
                if r2 != 0 {
                    assert_eq!(CStr::from_bytes_until_nul(&b1).unwrap(), CStr::from_bytes_until_nul(&b2).unwrap());
                }
                if r1 != 0 {
                    let t = printed(&VJSON, a.v, fmt != 0).unwrap();
                    assert_eq!(CStr::from_bytes_until_nul(&b1).unwrap().to_bytes(), &t[..]);
                }
                None
            }
            30 => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                let a = pool[i];
                let pre = inp.byte().unwrap_or(0) as c_int - 16;
                let fmt = (inp.byte().unwrap_or(0) & 1) as c_int;
                let p1 = (VJSON.print_buffered)(a.v, pre, fmt);
                let p2 = (UPSTREAM.print_buffered)(a.u, pre, fmt);
                assert_eq!(p1.is_null(), p2.is_null(), "PrintBuffered differs");
                if !p1.is_null() {
                    assert_eq!(CStr::from_ptr(p1), CStr::from_ptr(p2), "PrintBuffered text differs");
                    (VJSON.free)(p1 as *mut _);
                    (UPSTREAM.free)(p2 as *mut _);
                }
                None
            }
            _ => {
                let Some(i) = pick(&mut inp, &pool) else { continue };
                same(pool[i], "nothing");
                None
            }
        };
        if let Some(p) = made {
            same(p, "create");
            pool.push(p);
        }
        if pool.len() > 12 {
            let a = pool.remove(0);
            (VJSON.delete)(a.v);
            (UPSTREAM.delete)(a.u);
        }
    }
    for a in pool {
        same(a, "end");
        (VJSON.delete)(a.v);
        (UPSTREAM.delete)(a.u);
    }
});
