//! mbedTLS-compatible error codes for certificates vx509 rejects.
//!
//! The verdict is always vx509's. When it rejects, this walker retraces the
//! certificate the way mbedTLS 3.6's `x509_crt_parse_der_core` does, so the
//! drop-in returns the error code mbedTLS would have returned. It is
//! unverified safe Rust that only computes a number: every index is
//! checked, and its result never turns a rejection into an acceptance.

pub const ASN1_OUT_OF_DATA: i32 = -0x0060;
pub const ASN1_UNEXPECTED_TAG: i32 = -0x0062;
pub const ASN1_INVALID_LENGTH: i32 = -0x0064;
pub const ASN1_LENGTH_MISMATCH: i32 = -0x0066;
pub const ASN1_INVALID_DATA: i32 = -0x0068;

pub const X509_FEATURE_UNAVAILABLE: i32 = -0x2080;
pub const X509_INVALID_FORMAT: i32 = -0x2180;
pub const X509_INVALID_VERSION: i32 = -0x2200;
pub const X509_INVALID_SERIAL: i32 = -0x2280;
pub const X509_INVALID_ALG: i32 = -0x2300;
pub const X509_INVALID_NAME: i32 = -0x2380;
pub const X509_INVALID_DATE: i32 = -0x2400;
pub const X509_INVALID_SIGNATURE: i32 = -0x2480;
pub const X509_INVALID_EXTENSIONS: i32 = -0x2500;
pub const X509_UNKNOWN_VERSION: i32 = -0x2580;
pub const X509_SIG_MISMATCH: i32 = -0x2680;
pub const X509_BAD_INPUT_DATA: i32 = -0x2800;

pub const PK_KEY_INVALID_FORMAT: i32 = -0x3D00;

/// How far mbedTLS gets before the error, so the C side can run the steps
/// it still owns, in mbedTLS's order, before reporting `code`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    /// Failed before the signature algorithm is mapped.
    Early,
    /// Failed after the signature algorithm is mapped, before the key.
    AfterSigAlg,
    /// Failed after the SubjectPublicKeyInfo, which mbedTLS parses itself.
    AfterKey,
}

#[derive(Clone, Copy, Debug)]
pub struct Diag {
    pub code: i32,
    pub stage: Stage,
    /// Offsets into the input of the signature OID contents, its params
    /// (tag, contents) and the SubjectPublicKeyInfo TLV, when reached.
    pub sig_oid: (usize, usize),
    pub sig_params: (u8, usize, usize),
    pub spki: (usize, usize),
}

type R<T> = Result<T, i32>;

/// A position `p` in `b`, reading up to `end`.
struct Cur<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Cur<'a> {
    fn get_len(&mut self, end: usize) -> R<usize> {
        if end <= self.p {
            return Err(ASN1_OUT_OF_DATA);
        }
        let c = self.b[self.p];
        let len;
        if c & 0x80 == 0 {
            len = c as usize;
            self.p += 1;
        } else {
            let n = (c & 0x7F) as usize;
            if n == 0 || n > 4 {
                return Err(ASN1_INVALID_LENGTH);
            }
            if end - self.p <= n {
                return Err(ASN1_OUT_OF_DATA);
            }
            self.p += 1;
            let mut l: usize = 0;
            for _ in 0..n {
                l = (l << 8) | self.b[self.p] as usize;
                self.p += 1;
            }
            len = l;
        }
        if len > end - self.p {
            return Err(ASN1_OUT_OF_DATA);
        }
        Ok(len)
    }

    fn get_tag(&mut self, end: usize, tag: u8) -> R<usize> {
        if end <= self.p {
            return Err(ASN1_OUT_OF_DATA);
        }
        if self.b[self.p] != tag {
            return Err(ASN1_UNEXPECTED_TAG);
        }
        self.p += 1;
        self.get_len(end)
    }

    fn peek(&self, end: usize) -> Option<u8> {
        if self.p < end { Some(self.b[self.p]) } else { None }
    }

    /// `mbedtls_asn1_get_int`: a non-negative INTEGER that fits an `int`.
    fn get_int(&mut self, end: usize) -> R<i64> {
        let mut len = self.get_tag(end, 0x02)?;
        if len == 0 {
            return Err(ASN1_INVALID_LENGTH);
        }
        if self.b[self.p] & 0x80 != 0 {
            return Err(ASN1_INVALID_LENGTH);
        }
        while len > 0 && self.b[self.p] == 0 {
            self.p += 1;
            len -= 1;
        }
        if len > 4 || (len == 4 && self.b[self.p] & 0x80 != 0) {
            return Err(ASN1_INVALID_LENGTH);
        }
        let mut v: i64 = 0;
        for _ in 0..len {
            v = (v << 8) | self.b[self.p] as i64;
            self.p += 1;
        }
        Ok(v)
    }

    fn get_bool(&mut self, end: usize) -> R<bool> {
        let len = self.get_tag(end, 0x01)?;
        if len != 1 {
            return Err(ASN1_INVALID_LENGTH);
        }
        let v = self.b[self.p] != 0;
        self.p += 1;
        Ok(v)
    }

    /// `mbedtls_asn1_get_bitstring`, which must fill `end`: (unused, start, len).
    fn get_bitstring(&mut self, end: usize) -> R<(u8, usize, usize)> {
        let len = self.get_tag(end, 0x03)?;
        if len < 1 {
            return Err(ASN1_OUT_OF_DATA);
        }
        let unused = self.b[self.p];
        self.p += 1;
        if unused > 7 {
            return Err(ASN1_INVALID_LENGTH);
        }
        let start = self.p;
        self.p += len - 1;
        if self.p != end {
            return Err(ASN1_LENGTH_MISMATCH);
        }
        Ok((unused, start, len - 1))
    }

    /// `mbedtls_asn1_get_bitstring_null`: a BIT STRING with no unused bits.
    fn get_bitstring_null(&mut self, end: usize) -> R<usize> {
        let len = self.get_tag(end, 0x03)?;
        if len < 2 || self.b[self.p] != 0 {
            return Err(ASN1_INVALID_DATA);
        }
        self.p += 1;
        Ok(len - 1)
    }

    /// `mbedtls_asn1_get_alg`: (oid start, oid len, params tag, start, len).
    fn get_alg(&mut self, end: usize) -> R<((usize, usize), (u8, usize, usize))> {
        let len = self.get_tag(end, 0x30)?;
        if end <= self.p {
            return Err(ASN1_OUT_OF_DATA);
        }
        let end = self.p + len;
        let olen = self.get_tag(end, 0x06)?;
        let oid = (self.p, olen);
        self.p += olen;
        if self.p == end {
            return Ok((oid, (0, 0, 0)));
        }
        let tag = self.b[self.p];
        self.p += 1;
        let plen = self.get_len(end)?;
        let params = (tag, self.p, plen);
        self.p += plen;
        if self.p != end {
            return Err(ASN1_LENGTH_MISMATCH);
        }
        Ok((oid, params))
    }
}

fn add(high: i32, low: i32) -> i32 {
    high + low
}

fn get_name(c: &mut Cur, end: usize) -> R<()> {
    loop {
        let set_len = c.get_tag(end, 0x31).map_err(|e| add(X509_INVALID_NAME, e))?;
        let end_set = c.p + set_len;
        loop {
            let len = c.get_tag(end_set, 0x30).map_err(|e| add(X509_INVALID_NAME, e))?;
            let end_atv = c.p + len;
            if end_atv <= c.p {
                return Err(add(X509_INVALID_NAME, ASN1_OUT_OF_DATA));
            }
            let olen = c.get_tag(end_atv, 0x06).map_err(|e| add(X509_INVALID_NAME, e))?;
            c.p += olen;
            let Some(t) = c.peek(end_atv) else { return Err(add(X509_INVALID_NAME, ASN1_OUT_OF_DATA)) };
            if ![0x1E, 0x0C, 0x14, 0x13, 0x16, 0x1C, 0x03].contains(&t) {
                return Err(add(X509_INVALID_NAME, ASN1_UNEXPECTED_TAG));
            }
            c.p += 1;
            let vlen = c.get_len(end_atv).map_err(|e| add(X509_INVALID_NAME, e))?;
            c.p += vlen;
            if c.p != end_atv {
                return Err(add(X509_INVALID_NAME, ASN1_LENGTH_MISMATCH));
            }
            if c.p == end_set {
                break;
            }
        }
        if c.p == end {
            return Ok(());
        }
    }
}

fn get_time(c: &mut Cur, end: usize) -> R<()> {
    let Some(tag) = c.peek(end) else { return Err(add(X509_INVALID_DATE, ASN1_OUT_OF_DATA)) };
    let year_len = match tag {
        0x17 => 2,
        0x18 => 4,
        _ => return Err(add(X509_INVALID_DATE, ASN1_UNEXPECTED_TAG)),
    };
    c.p += 1;
    let len = c.get_len(end).map_err(|e| add(X509_INVALID_DATE, e))?;
    let s = &c.b[c.p..c.p + len];
    if len != year_len + 10 && !(len == year_len + 11 && s[len - 1] == b'Z') {
        return Err(X509_INVALID_DATE);
    }
    c.p += len;
    let d2 = |i: usize| {
        let (a, b) = (s[i].wrapping_sub(b'0'), s[i + 1].wrapping_sub(b'0'));
        if a < 10 && b < 10 { Some(a as u32 * 10 + b as u32) } else { None }
    };
    let mut year = d2(0).ok_or(X509_INVALID_DATE)?;
    let mut q = 2;
    if year_len == 4 {
        year = year * 100 + d2(2).ok_or(X509_INVALID_DATE)?;
        q = 4;
    } else {
        year += if year < 50 { 2000 } else { 1900 };
    }
    let f = [d2(q), d2(q + 2), d2(q + 4), d2(q + 6), d2(q + 8)];
    let (Some(mon), Some(day), Some(hour), Some(min), Some(sec)) = (f[0], f[1], f[2], f[3], f[4]) else {
        return Err(X509_INVALID_DATE);
    };
    let mdays = match mon {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => if (year & 3) != 0 || (year % 100 == 0 && year % 400 != 0) { 28 } else { 29 },
        _ => return Err(X509_INVALID_DATE),
    };
    if day == 0 || day > mdays || hour > 23 || min > 59 || sec > 59 {
        return Err(X509_INVALID_DATE);
    }
    Ok(())
}

/// The OIDs mbedTLS knows as extension types (`mbedtls_oid_get_x509_ext_type`).
fn known_ext(oid: &[u8]) -> Option<u8> {
    match oid {
        [0x55, 0x1D, x @ (14 | 15 | 17 | 19 | 32 | 35 | 37)] => Some(*x),
        [0x60, 0x86, 0x48, 0x01, 0x86, 0xF8, 0x42, 0x01, 0x01] => Some(0xFF),
        _ => None,
    }
}

fn general_names(c: &mut Cur, end: usize) -> R<()> {
    while c.p < end {
        let tag = c.b[c.p];
        c.p += 1;
        let len = c.get_len(end).map_err(|e| add(X509_INVALID_EXTENSIONS, e))?;
        if tag & 0xC0 != 0x80 {
            return Err(add(X509_INVALID_EXTENSIONS, ASN1_UNEXPECTED_TAG));
        }
        let start = c.p;
        match tag & 0x9F {
            0x80 => {
                // otherName: only HwModuleName is checked further.
                let mut o = Cur { b: c.b, p: start };
                let e = start + len;
                let olen = o.get_tag(e, 0x06).map_err(|x| add(X509_INVALID_EXTENSIONS, x))?;
                if &c.b[o.p..o.p + olen] == [0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x08, 0x04] {
                    o.p += olen;
                    let l = o.get_tag(e, 0xA0).map_err(|x| add(X509_INVALID_EXTENSIONS, x))?;
                    if e != o.p + l {
                        return Err(add(X509_INVALID_EXTENSIONS, ASN1_LENGTH_MISMATCH));
                    }
                    let l = o.get_tag(e, 0x30).map_err(|x| add(X509_INVALID_EXTENSIONS, x))?;
                    if e != o.p + l {
                        return Err(add(X509_INVALID_EXTENSIONS, ASN1_LENGTH_MISMATCH));
                    }
                    let l = o.get_tag(e, 0x06).map_err(|x| add(X509_INVALID_EXTENSIONS, x))?;
                    o.p += l;
                    let l = o.get_tag(e, 0x04).map_err(|x| add(X509_INVALID_EXTENSIONS, x))?;
                    o.p += l;
                    if o.p != e {
                        return Err(add(X509_INVALID_EXTENSIONS, ASN1_LENGTH_MISMATCH));
                    }
                }
            }
            0x87 => {
                if len != 4 && len != 16 {
                    return Err(X509_BAD_INPUT_DATA);
                }
            }
            0x84 => {
                let mut o = Cur { b: c.b, p: start };
                let nl = o.get_tag(start + len, 0x30)?;
                let ne = o.p + nl;
                get_name(&mut o, ne)?;
            }
            _ => {}
        }
        c.p = start + len;
    }
    if c.p != end {
        return Err(add(X509_INVALID_EXTENSIONS, ASN1_LENGTH_MISMATCH));
    }
    Ok(())
}

fn extension_value(c: &mut Cur, end: usize, ty: u8) -> R<()> {
    let ext = |e| add(X509_INVALID_EXTENSIONS, e);
    match ty {
        19 => {
            let len = c.get_tag(end, 0x30).map_err(ext)?;
            if c.p == end {
                return Ok(());
            }
            // mbedTLS 3.6.7: the SEQUENCE must fill the extension value.
            if end - c.p != len {
                return Err(X509_INVALID_EXTENSIONS);
            }
            // A missing cA leaves the first element to the INTEGER parser
            // below (before 3.6.7 an INTEGER here was read as cA).
            match c.get_bool(end) {
                Ok(_) | Err(ASN1_UNEXPECTED_TAG) => {}
                Err(e) => return Err(ext(e)),
            }
            if c.p == end {
                return Ok(());
            }
            let v = c.get_int(end).map_err(ext)?;
            if c.p != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
            if v == i32::MAX as i64 {
                return Err(ext(ASN1_INVALID_LENGTH));
            }
        }
        15 => {
            c.get_bitstring(end).map_err(ext)?;
        }
        0xFF => {
            let (_, _, len) = c.get_bitstring(end).map_err(ext)?;
            if len > 1 {
                return Err(ext(ASN1_INVALID_LENGTH));
            }
        }
        37 => {
            let len = c.get_tag(end, 0x30).map_err(ext)?;
            if c.p + len != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
            let mut n = 0;
            while c.p < end {
                let l = c.get_tag(end, 0x06).map_err(ext)?;
                c.p += l;
                n += 1;
            }
            if n == 0 {
                return Err(ext(ASN1_INVALID_LENGTH));
            }
        }
        14 => {
            let l = c.get_tag(end, 0x04).map_err(ext)?;
            c.p += l;
            if c.p != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
        }
        35 => {
            let len = c.get_tag(end, 0x30).map_err(ext)?;
            if c.p + len != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
            match c.get_tag(end, 0x80) {
                Ok(l) => c.p += l,
                Err(ASN1_UNEXPECTED_TAG) => {}
                Err(e) => return Err(ext(e)),
            }
            if c.p < end {
                let l = c.get_tag(end, 0xA1).map_err(ext)?;
                let e2 = c.p + l;
                general_names(c, e2)?;
                let l = c.get_tag(end, 0x82).map_err(ext)?;
                c.p += l;
            }
            if c.p != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
        }
        17 => {
            let len = c.get_tag(end, 0x30).map_err(ext)?;
            if c.p + len != end {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
            general_names(c, end)?;
        }
        32 => {
            let len = c.get_tag(end, 0x30).map_err(ext)?;
            if c.p + len != end || len == 0 {
                return Err(ext(ASN1_LENGTH_MISMATCH));
            }
            while c.p < end {
                let l = c.get_tag(end, 0x30).map_err(ext)?;
                let pe = c.p + l;
                let ol = c.get_tag(pe, 0x06).map_err(ext)?;
                c.p += ol;
                if c.p < pe {
                    let ql = c.get_tag(pe, 0x30).map_err(ext)?;
                    c.p += ql;
                }
                if c.p != pe {
                    return Err(ext(ASN1_LENGTH_MISMATCH));
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn extensions(c: &mut Cur, end: usize) -> R<()> {
    let ext = |e| add(X509_INVALID_EXTENSIONS, e);
    if c.p == end {
        return Ok(());
    }
    let len = c.get_tag(end, 0xA3).map_err(ext)?;
    let end = c.p + len;
    let l = c.get_tag(end, 0x30).map_err(ext)?;
    if end != c.p + l {
        return Err(ext(ASN1_LENGTH_MISMATCH));
    }
    let mut seen = [false; 256];
    while c.p < end {
        let len = c.get_tag(end, 0x30).map_err(ext)?;
        let end_data = c.p + len;
        let olen = c.get_tag(end_data, 0x06).map_err(ext)?;
        let oid = &c.b[c.p..c.p + olen];
        c.p += olen;
        let critical = match c.get_bool(end_data) {
            Ok(v) => v,
            Err(ASN1_UNEXPECTED_TAG) => false,
            Err(e) => return Err(ext(e)),
        };
        let vlen = c.get_tag(end_data, 0x04).map_err(ext)?;
        let end_oct = c.p + vlen;
        if end_oct != end_data {
            return Err(ext(ASN1_LENGTH_MISMATCH));
        }
        match known_ext(oid) {
            None => {
                c.p = end_oct;
                if critical {
                    return Err(ext(ASN1_UNEXPECTED_TAG));
                }
            }
            Some(t) => {
                if seen[t as usize] {
                    return Err(X509_INVALID_EXTENSIONS);
                }
                seen[t as usize] = true;
                if [19, 15, 37, 14, 35, 17, 32, 0xFF].contains(&t) {
                    let mut v = Cur { b: c.b, p: c.p };
                    match extension_value(&mut v, end_oct, t) {
                        Ok(()) => {}
                        Err(X509_FEATURE_UNAVAILABLE) if !critical => {}
                        Err(e) => return Err(e),
                    }
                    if t == 32 {
                        // Only anyPolicy is supported; others fail if critical.
                        let mut v = Cur { b: c.b, p: c.p };
                        let _ = v.get_tag(end_oct, 0x30);
                        let mut other = false;
                        while v.p < end_oct {
                            let Ok(l) = v.get_tag(end_oct, 0x30) else { break };
                            let pe = v.p + l;
                            if let Ok(ol) = v.get_tag(pe, 0x06) {
                                other |= &c.b[v.p..v.p + ol] != [0x55, 0x1D, 0x20, 0x00];
                            }
                            v.p = pe;
                        }
                        if other && critical {
                            return Err(X509_FEATURE_UNAVAILABLE);
                        }
                    }
                } else if critical {
                    return Err(X509_FEATURE_UNAVAILABLE);
                }
                c.p = end_oct;
            }
        }
    }
    if c.p != end {
        return Err(ext(ASN1_LENGTH_MISMATCH));
    }
    Ok(())
}

/// The error mbedTLS 3.6 returns for `buf`, which vx509 rejected.
pub fn diagnose(buf: &[u8]) -> Diag {
    let mut d = Diag { code: X509_INVALID_FORMAT, stage: Stage::Early, sig_oid: (0, 0), sig_params: (0, 0, 0), spki: (0, 0) };
    if let Err(code) = walk(buf, &mut d) {
        d.code = code;
    }
    d
}

fn walk(buf: &[u8], d: &mut Diag) -> R<()> {
    let fmt = |e| add(X509_INVALID_FORMAT, e);
    let mut c = Cur { b: buf, p: 0 };
    let len = c.get_tag(buf.len(), 0x30).map_err(|_| X509_INVALID_FORMAT)?;
    let crt_end = c.p + len;
    let len = c.get_tag(crt_end, 0x30).map_err(fmt)?;
    let end = c.p + len;

    // version
    let version = match c.get_tag(end, 0xA0) {
        Ok(l) => {
            let ve = c.p + l;
            let v = c.get_int(ve).map_err(|e| add(X509_INVALID_VERSION, e))?;
            if c.p != ve {
                return Err(add(X509_INVALID_VERSION, ASN1_LENGTH_MISMATCH));
            }
            v
        }
        Err(ASN1_UNEXPECTED_TAG) => 0,
        Err(e) => return Err(fmt(e)),
    };
    // serial
    if end <= c.p {
        return Err(add(X509_INVALID_SERIAL, ASN1_OUT_OF_DATA));
    }
    if c.b[c.p] != 0x82 && c.b[c.p] != 0x02 {
        return Err(add(X509_INVALID_SERIAL, ASN1_UNEXPECTED_TAG));
    }
    c.p += 1;
    let sl = c.get_len(end).map_err(|e| add(X509_INVALID_SERIAL, e))?;
    c.p += sl;
    // signature
    let (oid, params) = c.get_alg(end).map_err(|e| add(X509_INVALID_ALG, e))?;
    if !(0..=2).contains(&version) {
        return Err(X509_UNKNOWN_VERSION);
    }
    d.sig_oid = oid;
    d.sig_params = params;
    d.stage = Stage::AfterSigAlg;
    // issuer
    let l = c.get_tag(end, 0x30).map_err(fmt)?;
    let ie = c.p + l;
    get_name(&mut c, ie)?;
    // validity
    let l = c.get_tag(end, 0x30).map_err(|e| add(X509_INVALID_DATE, e))?;
    let ve = c.p + l;
    get_time(&mut c, ve)?;
    get_time(&mut c, ve)?;
    if c.p != ve {
        return Err(add(X509_INVALID_DATE, ASN1_LENGTH_MISMATCH));
    }
    // subject
    let l = c.get_tag(end, 0x30).map_err(fmt)?;
    if l > 0 {
        let se = c.p + l;
        get_name(&mut c, se)?;
    }
    // key: the outer TLV here, the rest by mbedTLS itself
    let ks = c.p;
    let l = c.get_tag(end, 0x30).map_err(|e| add(PK_KEY_INVALID_FORMAT, e))?;
    c.p += l;
    d.spki = (ks, c.p - ks);
    d.stage = Stage::AfterKey;
    // unique ids (mbedTLS expects constructed tags here)
    if version >= 1 {
        for n in [0xA1u8, 0xA2] {
            if c.p == end {
                break;
            }
            match c.get_tag(end, n) {
                Ok(l) => c.p += l,
                Err(ASN1_UNEXPECTED_TAG) => {}
                Err(e) => return Err(fmt(e)),
            }
        }
    }
    if version == 2 {
        extensions(&mut c, end)?;
    }
    if c.p != end {
        return Err(fmt(ASN1_LENGTH_MISMATCH));
    }
    // signatureAlgorithm, signatureValue
    let (oid2, params2) = c.get_alg(crt_end).map_err(|e| add(X509_INVALID_ALG, e))?;
    let same = |a: (usize, usize), b: (usize, usize)| buf[a.0..a.0 + a.1] == buf[b.0..b.0 + b.1];
    if !same(oid, oid2) || params.0 != params2.0 || !same((params.1, params.2), (params2.1, params2.2)) {
        return Err(X509_SIG_MISMATCH);
    }
    if crt_end <= c.p {
        return Err(add(X509_INVALID_SIGNATURE, ASN1_OUT_OF_DATA));
    }
    let l = c.get_bitstring_null(crt_end).map_err(|e| add(X509_INVALID_SIGNATURE, e))?;
    c.p += l;
    if c.p != crt_end {
        return Err(fmt(ASN1_LENGTH_MISMATCH));
    }
    // mbedTLS would accept this certificate; vx509 does not.
    Err(X509_INVALID_FORMAT)
}
