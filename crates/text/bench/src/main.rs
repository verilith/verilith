//! Throughput of vtext against the reference crates. Best of 15 runs of
//! enough iterations to take ~20 ms each; reports GB/s of input.
mod proto;
use base64::Engine as _;
use std::hint::black_box;
use std::time::Instant;

fn bench<F: FnMut() -> usize>(name: &str, bytes: usize, mut f: F) -> f64 {
    let mut iters = 1;
    loop {
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        if t.elapsed().as_millis() >= 20 {
            break;
        }
        iters *= 2;
    }
    let mut best = f64::MAX;
    for _ in 0..15 {
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    let gbs = bytes as f64 / best / 1e9;
    println!("{:<34} {:>8.2} GB/s", name, gbs);
    gbs
}

fn per_call<F: FnMut() -> usize>(name: &str, mut f: F) {
    let mut iters = 1;
    loop {
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        if t.elapsed().as_millis() >= 20 {
            break;
        }
        iters *= 2;
    }
    let mut best = f64::MAX;
    for _ in 0..15 {
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    println!("{:<44} {:>9.1} ns", name, best * 1e9);
}

fn idna_bench() {
    let domains = [
        ("lowercase ascii", "www.example.com"),
        ("long ascii", "static-assets.cdn.subdomain.example-company.co.uk"),
        ("mixed-case ascii", "WWW.Example.COM"),
        ("punycode", "xn--mnchen-3ya.de"),
        ("german", "münchen.de"),
        ("chinese", "例子.测试"),
        ("arabic (bidi)", "مثال.إختبار"),
        ("fullwidth", "ｅｘａｍｐｌｅ．ｃｏｍ"),
    ];
    for (name, d) in domains {
        println!("--- {name}: {d}");
        per_call("vtext domain_to_ascii_cow", || verilith_text::idna::domain_to_ascii_cow(black_box(d)).map(|s| s.len()).unwrap_or(0));
        per_call("idna domain_to_ascii_cow", || {
            idna::domain_to_ascii_cow(black_box(d).as_bytes(), idna::AsciiDenyList::EMPTY).map(|s| s.len()).unwrap_or(0)
        });
        per_call("vtext domain_to_unicode", || verilith_text::idna::domain_to_unicode(black_box(d)).0.len());
        per_call("idna domain_to_unicode", || idna::domain_to_unicode(black_box(d)).0.len());
    }
}

fn norm_bench() {
    use icu_normalizer::{ComposingNormalizerBorrowed, DecomposingNormalizerBorrowed};
    use unicode_normalization::UnicodeNormalization;
    use verilith_text::unicode::Form;
    let samples = [
        ("ascii", "The quick brown fox jumps over the lazy dog. 0123456789 "),
        ("french", "Le cœur déçu mais l'âme plutôt naïve, Louÿs rêva de crapaüter en canoë au delà des îles. "),
        ("vietnamese", "Tiếng Việt là ngôn ngữ chính thức của Việt Nam, có nguồn gốc từ khu vực Bắc Bộ. "),
        ("greek", "Ἐν ἀρχῇ ἦν ὁ λόγος, καὶ ὁ λόγος ἦν πρὸς τὸν θεόν, καὶ θεὸς ἦν ὁ λόγος. "),
        ("korean", "모든 인간은 태어날 때부터 자유로우며 그 존엄과 권리에 있어 동등하다. "),
        ("hindi", "सभी मनुष्यों को गौरव और अधिकारों के मामले में जन्मजात स्वतन्त्रता प्राप्त है। "),
        ("japanese", "すべての人間は、生まれながらにして自由であり、かつ、尊厳と権利とについて平等である。ｶﾀｶﾅ "),
    ];
    let c = ComposingNormalizerBorrowed::new_nfc();
    let d = DecomposingNormalizerBorrowed::new_nfd();
    let kc = ComposingNormalizerBorrowed::new_nfkc();
    let only = std::env::args().nth(2);
    for (name, unit) in samples {
        if only.as_deref().is_some_and(|o| o != name) {
            continue;
        }
        for (label, text) in [("", unit.repeat(64 * 1024 / unit.len() + 1)), (" (nfd input)", verilith_text::unicode::nfd(&unit.repeat(64 * 1024 / unit.len() + 1)).into_owned())] {
            let n = text.len();
            println!("--- {name}{label}, {n} bytes");
            let t = &text;
            bench("vtext nfc", n, || verilith_text::unicode::normalize(black_box(t), Form::Nfc).len());
            bench("unicode-normalization nfc", n, || black_box(t).nfc().collect::<String>().len());
            bench("icu_normalizer nfc", n, || c.normalize(black_box(t)).len());
            bench("vtext nfd", n, || verilith_text::unicode::normalize(black_box(t), Form::Nfd).len());
            bench("unicode-normalization nfd", n, || black_box(t).nfd().collect::<String>().len());
            bench("icu_normalizer nfd", n, || d.normalize(black_box(t)).len());
            bench("vtext nfkc", n, || verilith_text::unicode::normalize(black_box(t), Form::Nfkc).len());
            bench("unicode-normalization nfkc", n, || black_box(t).nfkc().collect::<String>().len());
            bench("icu_normalizer nfkc", n, || kc.normalize(black_box(t)).len());
        }
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("profidna") {
        let d = std::env::args().nth(2).unwrap();
        let mut n = 0;
        for _ in 0..20000 {
            n += verilith_text::idna::domain_to_ascii_cow(black_box(&d)).map(|s| s.len()).unwrap_or(0);
        }
        println!("{n}");
        return;
    }
    if std::env::args().nth(1).as_deref() == Some("prof") {
        let unit = std::env::args().nth(2).unwrap();
        let form = match std::env::args().nth(3).as_deref() {
            Some("nfc") => verilith_text::unicode::Form::Nfc,
            _ => verilith_text::unicode::Form::Nfd,
        };
        let t = unit.repeat(64 * 1024 / unit.len() + 1);
        let mut n = 0;
        for _ in 0..200 {
            n += verilith_text::unicode::normalize(black_box(&t), form).len();
        }
        println!("{n}");
        return;
    }
    if std::env::args().nth(1).as_deref() == Some("norm") {
        return norm_bench();
    }
    if std::env::args().nth(1).as_deref() == Some("idna") {
        return idna_bench();
    }
    let sizes = [64usize, 1024, 64 * 1024];
    for &n in &sizes {
        let x: Vec<u8> = (0..n).map(|i| (i * 7919 % 251) as u8).collect();
        let e = base64::engine::general_purpose::STANDARD.encode(&x);
        println!("--- base64, {} bytes", n);
        bench("vtext encode", n, || verilith_text::base64::STANDARD.encode(black_box(&x)).len());
        bench("base64 encode", n, || base64::engine::general_purpose::STANDARD.encode(black_box(&x)).len());
        bench("base64-simd encode", n, || base64_simd::STANDARD.encode_to_string(black_box(&x)).len());
        {
            let mut buf = vec![0u8; e.len()];
            bench("vtext encode_slice", n, || verilith_text::base64::STANDARD.encode_slice(black_box(&x), &mut buf).unwrap());
            bench("base64 encode_slice", n, || base64::engine::general_purpose::STANDARD.encode_slice(black_box(&x), &mut buf).unwrap());
            bench("base64-simd encode (slice)", n, || base64_simd::STANDARD.encode(black_box(&x), base64_simd::Out::from_slice(&mut buf)).len());
            let mut dbuf = vec![0u8; n + 64];
            bench("vtext decode_slice", e.len(), || verilith_text::base64::STANDARD.decode_slice(black_box(&e), &mut dbuf).unwrap());
            bench("base64 decode_slice", e.len(), || base64::engine::general_purpose::STANDARD.decode_slice(black_box(&e), &mut dbuf).unwrap());
            bench("base64-simd decode (slice)", e.len(), || base64_simd::STANDARD.decode(black_box(e.as_bytes()), base64_simd::Out::from_slice(&mut dbuf)).unwrap().len());
        }
        bench("proto encode", n, || {
            let mut o = vec![0u8; (n + 2) / 3 * 4];
            let i = unsafe { proto::enc(black_box(&x), &mut o) };
            o.len() + i
        });
        {
            let mut o = vec![0u8; (n + 2) / 3 * 4];
            let i = unsafe { proto::enc(&x, &mut o) };
            assert_eq!(&o[..i / 3 * 4], &e.as_bytes()[..i / 3 * 4]);
            let mut d = vec![0u8; e.len()];
            let j = unsafe { proto::dec(e.as_bytes(), &mut d) }.unwrap();
            assert_eq!(&d[..j / 4 * 3], &x[..j / 4 * 3]);
        }
        bench("proto decode", e.len(), || {
            let mut o = vec![0u8; e.len() / 4 * 3];
            let j = unsafe { proto::dec(black_box(e.as_bytes()), &mut o) }.unwrap();
            o.len() + j
        });
        bench("vtext decode", e.len(), || verilith_text::base64::STANDARD.decode(black_box(&e)).unwrap().len());
        bench("base64 decode", e.len(), || base64::engine::general_purpose::STANDARD.decode(black_box(&e)).unwrap().len());
        bench("base64-simd decode", e.len(), || base64_simd::STANDARD.decode_to_vec(black_box(&e)).unwrap().len());
        println!("--- hex, {} bytes", n);
        let h = hex::encode(&x);
        bench("vtext hex encode", n, || verilith_text::hex::encode(black_box(&x)).len());
        bench("hex encode", n, || hex::encode(black_box(&x)).len());
        bench("faster-hex encode", n, || faster_hex::hex_string(black_box(&x)).len());
        bench("vtext hex decode", h.len(), || verilith_text::hex::decode(black_box(&h)).unwrap().len());
        bench("hex decode", h.len(), || hex::decode(black_box(&h)).unwrap().len());
        bench("faster-hex decode", h.len(), || {
            let mut o = vec![0u8; h.len() / 2];
            faster_hex::hex_decode(black_box(h.as_bytes()), &mut o).unwrap();
            o.len()
        });
        println!("--- percent, {} bytes", n);
        let text: String = (0..n).map(|i| if i % 13 == 0 { ' ' } else { (b'a' + (i % 26) as u8) as char }).collect();
        const SV: &verilith_text::percent::AsciiSet = &verilith_text::percent::CONTROLS.add(b' ').add(b'"').add(b'#').add(b'<').add(b'>');
        const SR: &percent_encoding::AsciiSet = &percent_encoding::CONTROLS.add(b' ').add(b'"').add(b'#').add(b'<').add(b'>');
        bench("vtext percent encode", n, || verilith_text::percent::utf8_percent_encode(black_box(&text), SV).to_string().len());
        bench("percent-encoding encode", n, || percent_encoding::utf8_percent_encode(black_box(&text), SR).to_string().len());
        let pe = percent_encoding::utf8_percent_encode(&text, SR).to_string();
        bench("vtext percent decode", pe.len(), || verilith_text::percent::percent_decode_str(black_box(&pe)).decode_utf8().unwrap().len());
        bench("percent-encoding decode", pe.len(), || percent_encoding::percent_decode_str(black_box(&pe)).decode_utf8().unwrap().len());
    }
}
