//! Drives the C ABI (the ada_c.h functions) with an arbitrary sequence of
//! calls on a few URL and URLSearchParams handles, reading every string it
//! hands out, so ASan sees any bad pointer, length or double free.
#![no_main]
#![allow(unsafe_op_in_unsafe_fn)]
use libfuzzer_sys::fuzz_target;
use verilith_url::capi::*;

unsafe fn touch(s: AdaString) {
    if s.length > 0 {
        let b = std::slice::from_raw_parts(s.data as *const u8, s.length);
        std::hint::black_box(b.iter().fold(0u8, |a, &c| a ^ c));
    }
}

unsafe fn touch_owned(s: AdaOwnedString) {
    touch(AdaString { data: s.data, length: s.length });
    free_owned_string(s);
}

fuzz_target!(|data: &[u8]| unsafe {
    let mut urls: Vec<*mut Handle> = Vec::new();
    let mut params: Vec<*mut verilith_url::searchparams::UrlSearchParams> = Vec::new();
    for chunk in data.split(|&c| c == 0) {
        let Some((&op, arg)) = chunk.split_first() else { continue };
        let p = arg.as_ptr() as *const core::ffi::c_char;
        let n = arg.len();
        let k = arg.len() / 2;
        let u = if urls.is_empty() { core::ptr::null_mut() } else { urls[op as usize % urls.len()] };
        let sp = if params.is_empty() { core::ptr::null_mut() } else { params[op as usize % params.len()] };
        match op % 24 {
            0 => {
                // The C API keeps the host parser's scratch buffers between
                // calls; the result must match a parse with fresh ones.
                let h = parse(p, n);
                let want = verilith_url::Url::parse_bytes(arg, None).filter(|u| u.href().len() <= u32::MAX as usize);
                assert_eq!(is_valid(h), want.is_some());
                if let Some(w) = want {
                    let g = get_href(h);
                    assert_eq!(std::slice::from_raw_parts(g.data as *const u8, g.length), w.href().as_bytes());
                }
                urls.push(h);
            },
            1 => urls.push(parse_with_base(p, k, p.add(k), n - k)),
            2 => drop(can_parse(p, n) | can_parse_with_base(p, k, p.add(k), n - k)),
            3 if !u.is_null() => urls.push(copy(u)),
            4 if !u.is_null() => {
                for g in [get_href, get_username, get_password, get_hash, get_host, get_hostname, get_pathname, get_search, get_protocol, get_port] {
                    touch(g(u));
                }
                touch_owned(get_origin(u));
                // Null for a URL that failed to parse, as in ada.
                let c = get_components(u);
                if !c.is_null() {
                    std::hint::black_box(((*c).protocol_end, (*c).host_end));
                }
                std::hint::black_box((get_host_type(u), get_scheme_type(u), is_valid(u)));
            }
            5 if !u.is_null() => {
                for s in [set_href, set_host, set_hostname, set_protocol, set_username, set_password, set_port, set_pathname] {
                    if (op / 24) % 8 == 0 {
                        drop(s(u, p, n));
                    }
                }
                drop(set_href(u, p, n));
            }
            6 if !u.is_null() && op >= 128 => {
                // The shortcut host (kept in a per-thread buffer, with the
                // per-thread scratch) must be what set_hostname gives.
                let mut hs = AdaString { data: core::ptr::null(), length: 0 };
                let mut ht = 0u8;
                let k = hostname_after_set(u, p, n, &mut hs, &mut ht);
                let c = copy(u);
                let ok = set_hostname(c, p, n);
                if k == 1 {
                    let g = get_hostname(c);
                    assert!(ok);
                    assert_eq!(std::slice::from_raw_parts(hs.data as *const u8, hs.length), std::slice::from_raw_parts(g.data as *const u8, g.length));
                    assert_eq!(ht, get_host_type(c));
                } else if k == 0 {
                    assert!(!ok);
                }
                free(c);
            }
            6 if !u.is_null() => set_search(u, p, n),
            7 if !u.is_null() => set_hash(u, p, n),
            8 if !u.is_null() => {
                clear_port(u);
                clear_hash(u);
                clear_search(u);
            }
            9 if !u.is_null() => {
                let i = urls.iter().position(|&x| x == u).unwrap();
                free(urls.swap_remove(i));
            }
            10 => touch_owned(idna_to_unicode(p, n)),
            11 => touch_owned(idna_to_ascii(p, n)),
            12 => params.push(parse_search_params(p, n)),
            13 if !sp.is_null() => search_params_append(sp, p, k, p.add(k), n - k),
            14 if !sp.is_null() => search_params_set(sp, p, k, p.add(k), n - k),
            15 if !sp.is_null() => search_params_remove(sp, p, n),
            16 if !sp.is_null() => search_params_remove_value(sp, p, k, p.add(k), n - k),
            17 if !sp.is_null() => {
                search_params_sort(sp);
                touch_owned(search_params_to_string(sp));
                touch(search_params_get(sp, p, n));
                std::hint::black_box((search_params_size(sp), search_params_has(sp, p, n), search_params_has_value(sp, p, k, p.add(k), n - k)));
            }
            18 if !sp.is_null() => {
                let all = search_params_get_all(sp, p, n);
                for i in 0..strings_size(all) + 1 {
                    touch(strings_get(all, i));
                }
                free_strings(all);
            }
            19 if !sp.is_null() => {
                let it = search_params_get_keys(sp);
                while search_params_keys_iter_has_next(it) {
                    touch(search_params_keys_iter_next(it));
                }
                touch(search_params_keys_iter_next(it));
                free_search_params_keys_iter(it);
                let it = search_params_get_values(sp);
                while search_params_values_iter_has_next(it) {
                    touch(search_params_values_iter_next(it));
                }
                free_search_params_values_iter(it);
                let it = search_params_get_entries(sp);
                while search_params_entries_iter_has_next(it) {
                    let e = search_params_entries_iter_next(it);
                    touch(e.key);
                    touch(e.value);
                }
                free_search_params_entries_iter(it);
            }
            20 if !sp.is_null() => search_params_reset(sp, p, n),
            21 if !sp.is_null() => {
                let i = params.iter().position(|&x| x == sp).unwrap();
                free_search_params(params.swap_remove(i));
            }
            22 => {
                // Null handles must be safe everywhere.
                touch(get_href(core::ptr::null_mut()));
                drop(set_href(core::ptr::null_mut(), p, n));
                std::hint::black_box(search_params_size(core::ptr::null_mut()));
            }
            _ => {}
        }
    }
    for u in urls {
        free(u);
    }
    for sp in params {
        free_search_params(sp);
    }
});
