//! The client's handshake messages, proven against `spec_client_hs.rs`:
//! the ClientHello it builds, and how it reads ServerHello,
//! HelloRetryRequest, EncryptedExtensions, CertificateRequest and
//! CertificateVerify.
#[cfg(verus_only)]
use crate::client::{lemma_scheme_list_len, lemma_scheme_list_push};
use crate::messages::*;
use crate::spec::*;
use crate::spec_client::*;
use crate::spec_client_hs::*;
use crate::spec_server::*;
use alloc::vec::Vec;
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

/// The longest key share the client sends (X25519MLKEM768's is 1216
/// bytes).
pub const MAX_SHARE: usize = 1300;

/// The most ALPN protocols the client offers.
pub const MAX_ALPN: usize = 8;

/// A client's configuration (`SpecCliCfg`).
pub struct ClientConfig {
    pub suites: Vec<u16>,
    pub groups: Vec<u16>,
    pub shares: usize,
    pub sigs: Vec<u16>,
    pub alpn: Vec<Vec<u8>>,
    pub roots: Vec<Vec<u8>>,
}

impl View for ClientConfig {
    type V = SpecCliCfg;

    open spec fn view(&self) -> SpecCliCfg {
        SpecCliCfg {
            suites: self.suites@,
            groups: self.groups@,
            shares: self.shares as nat,
            sigs: self.sigs@,
            alpn: chain_view(self.alpn@),
            roots: chain_view(self.roots@),
        }
    }
}

impl ClientConfig {
    pub open spec fn wf(&self) -> bool {
        &&& 1 <= self.suites@.len() <= 16
        &&& forall|i: int| 0 <= i < self.suites@.len() ==> known_suite(#[trigger] self.suites@[i])
        &&& 1 <= self.groups@.len() <= 16
        &&& 1 <= self.shares <= 2
        &&& self.shares <= self.groups@.len()
        &&& 1 <= self.sigs@.len() <= 32
        &&& self.alpn@.len() <= MAX_ALPN
        &&& forall|i: int| 0 <= i < self.alpn@.len() ==> 1 <= (#[trigger] self.alpn@[i])@.len() <= 255
    }

    /// Whether the configuration is one `ClientConn::new` takes.
    pub fn check(&self) -> (r: bool)
        ensures
            r == self.wf(),
    {
        let ns = self.suites.len();
        if ns < 1 || ns > 16 || self.groups.len() < 1 || self.groups.len() > 16 || self.shares < 1 || self.shares > 2
            || self.shares > self.groups.len() || self.sigs.len() < 1 || self.sigs.len() > 32 || self.alpn.len() > MAX_ALPN {
            return false;
        }
        let mut i = 0;
        while i < ns
            invariant
                ns == self.suites@.len(),
                i <= ns,
                forall|j: int| 0 <= j < i ==> known_suite(#[trigger] self.suites@[j]),
            decreases ns - i,
        {
            let s = self.suites[i];
            if !(s == 0x1301 || s == 0x1302 || s == 0x1303) {
                return false;
            }
            i += 1;
        }
        let na = self.alpn.len();
        let mut i = 0;
        while i < na
            invariant
                na == self.alpn@.len(),
                i <= na,
                forall|j: int| 0 <= j < i ==> 1 <= (#[trigger] self.alpn@[j])@.len() <= 255,
            decreases na - i,
        {
            let l = self.alpn[i].len();
            if l < 1 || l > 255 {
                return false;
            }
            i += 1;
        }
        true
    }
}

/// The bytes of a list of key shares.
pub open spec fn shares_view(v: Seq<(u16, Vec<u8>)>) -> Seq<(u16, Seq<u8>)> {
    v.map_values(|p: (u16, Vec<u8>)| (p.0, p.1@))
}

/// Shares of at most `MAX_SHARE` bytes, none empty, at most two.
pub open spec fn shares_wf(v: Seq<(u16, Vec<u8>)>) -> bool {
    &&& 1 <= v.len() <= 2
    &&& forall|i: int| 0 <= i < v.len() ==> 1 <= (#[trigger] v[i]).1@.len() <= MAX_SHARE
}

fn put_list16(out: &mut Vec<u8>, s: &[u16])
    requires
        s@.len() <= 1000,
    ensures
        final(out)@ == old(out)@ + list16(s@),
        list16(s@).len() == 2 + 2 * s@.len(),
{
    let n = s.len();
    put2(out, 2 * n);
    let ghost o1 = out@;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            n <= 1000,
            out@ == o1 + scheme_list(s@.take(i as int)),
        decreases n - i,
    {
        proof {
            lemma_scheme_list_push(s@.take(i as int), s@[i as int]);
            assert(s@.take(i as int).push(s@[i as int]) =~= s@.take(i as int + 1));
        }
        put2(out, s[i] as usize);
        i = i + 1;
    }
    proof {
        assert(s@.take(n as int) =~= s@);
        lemma_scheme_list_len(s@);
        assert(out@ =~= old(out)@ + list16(s@));
    }
}

proof fn lemma_ks_len(sh: Seq<(u16, Seq<u8>)>)
    requires
        forall|i: int| 0 <= i < sh.len() ==> (#[trigger] sh[i]).1.len() <= MAX_SHARE,
    ensures
        ks_entries(sh).len() <= sh.len() * (4 + MAX_SHARE),
    decreases sh.len(),
{
    if sh.len() > 0 {
        let d = sh.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).1.len() <= MAX_SHARE by {
            assert(d[i] == sh[i]);
        }
        lemma_ks_len(d);
        assert(sh.last() == sh[sh.len() - 1]);
        assert(d.len() * (4 + MAX_SHARE) + 4 + MAX_SHARE == sh.len() * (4 + MAX_SHARE)) by (nonlinear_arith)
            requires d.len() + 1 == sh.len();
    }
}

fn put_ks_entries(out: &mut Vec<u8>, sh: &Vec<(u16, Vec<u8>)>)
    requires
        shares_wf(sh@),
    ensures
        final(out)@ == old(out)@ + ks_entries(shares_view(sh@)),
        ks_entries(shares_view(sh@)).len() <= 2 * (4 + MAX_SHARE),
{
    let n = sh.len();
    let ghost o = out@;
    let ghost sv = shares_view(sh@);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == sh@.len(),
            shares_wf(sh@),
            sv == shares_view(sh@),
            out@ == o + ks_entries(sv.take(i as int)),
        decreases n - i,
    {
        let g = sh[i].0;
        let s = &sh[i].1;
        proof {
            let t = sv.take(i as int + 1);
            assert(t.drop_last() =~= sv.take(i as int));
            assert(t.last() == sv[i as int]);
            assert(sv[i as int] == (g, s@));
            assert(1 <= sh@[i as int].1@.len() <= MAX_SHARE);
        }
        put2(out, g as usize);
        put2(out, s.len());
        put(out, s.as_slice());
        proof {
            let t = sv.take(i as int + 1);
            assert(ks_entries(t) == ks_entries(sv.take(i as int)) + be2(g as nat) + be2(s@.len()) + s@);
            assert(out@ =~= o + ks_entries(t));
        }
        i = i + 1;
    }
    proof {
        assert(sv.take(n as int) =~= sv);
        assert forall|i: int| 0 <= i < sv.len() implies (#[trigger] sv[i]).1.len() <= MAX_SHARE by {
            assert(sv[i].1 == sh@[i].1@);
        }
        lemma_ks_len(sv);
        assert(sv.len() <= 2);
        assert(sv.len() * (4 + MAX_SHARE) <= 2 * (4 + MAX_SHARE)) by (nonlinear_arith)
            requires sv.len() <= 2;
    }
}

proof fn lemma_alpn_len(a: Seq<Seq<u8>>)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() <= 255,
    ensures
        alpn_names(a).len() <= a.len() * 256,
    decreases a.len(),
{
    if a.len() > 0 {
        let d = a.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]).len() <= 255 by {
            assert(d[i] == a[i]);
        }
        lemma_alpn_len(d);
        assert(a.last() == a[a.len() - 1]);
        assert(d.len() * 256 + 256 == a.len() * 256) by (nonlinear_arith)
            requires d.len() + 1 == a.len();
    }
}

fn put_alpn_names(out: &mut Vec<u8>, a: &Vec<Vec<u8>>)
    requires
        a@.len() <= MAX_ALPN,
        forall|i: int| 0 <= i < a@.len() ==> 1 <= (#[trigger] a@[i])@.len() <= 255,
    ensures
        final(out)@ == old(out)@ + alpn_names(chain_view(a@)),
        alpn_names(chain_view(a@)).len() <= MAX_ALPN * 256,
{
    let n = a.len();
    let ghost o = out@;
    let ghost av = chain_view(a@);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n <= MAX_ALPN,
            forall|i: int| 0 <= i < a@.len() ==> 1 <= (#[trigger] a@[i])@.len() <= 255,
            av == chain_view(a@),
            out@ == o + alpn_names(av.take(i as int)),
        decreases n - i,
    {
        let p = &a[i];
        proof {
            let t = av.take(i as int + 1);
            assert(t.drop_last() =~= av.take(i as int));
            assert(t.last() == av[i as int]);
            assert(av[i as int] == p@);
            assert(1 <= a@[i as int]@.len() <= 255);
        }
        put1(out, p.len() as u8);
        put(out, p.as_slice());
        proof {
            let t = av.take(i as int + 1);
            assert(out@ =~= o + alpn_names(t));
        }
        i = i + 1;
    }
    proof {
        assert(av.take(n as int) =~= av);
        assert forall|i: int| 0 <= i < av.len() implies (#[trigger] av[i]).len() <= 255 by {
            assert(av[i] == a@[i]@);
        }
        lemma_alpn_len(av);
        assert(av.len() * 256 <= MAX_ALPN * 256) by (nonlinear_arith)
            requires av.len() <= MAX_ALPN;
    }
}

/// Appends extension `t` with data `d`.
fn put_ext(out: &mut Vec<u8>, t: u16, d: &[u8])
    requires
        d@.len() < 65536,
    ensures
        final(out)@ == old(out)@ + ext(t, d@),
{
    put2(out, t as usize);
    put2(out, d.len());
    put(out, d);
    assert(final(out)@ =~= old(out)@ + ext(t, d@));
}

/// The ClientHello's extensions.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn ch_exts_x(cfg: &ClientConfig, host: &[u8], shares: &Vec<(u16, Vec<u8>)>, cookie: Option<&[u8]>) -> (r: Vec<u8>)
    requires
        cfg.wf(),
        host@.len() <= 253,
        shares_wf(shares@),
        cookie matches Some(k) ==> k@.len() <= MAX_COOKIE,
    ensures
        r@ == ch_exts(cfg@, host@, shares_view(shares@), opt_view(cookie)),
        r@.len() <= 9200,
{
    let mut e: Vec<u8> = Vec::new();
    // server_name
    let mut d: Vec<u8> = Vec::new();
    put2(&mut d, host.len() + 3);
    put1(&mut d, 0);
    put2(&mut d, host.len());
    put(&mut d, host);
    put_ext(&mut e, 0, d.as_slice());
    let ghost e1 = e@;
    assert(e1 == sni_ext(host@));
    // supported_versions
    let v: [u8; 3] = [2, 3, 4];
    put_ext(&mut e, 43, &v);
    assert(v@ =~= seq![2u8, 3u8, 4u8]);
    // supported_groups
    let mut d: Vec<u8> = Vec::new();
    put_list16(&mut d, cfg.groups.as_slice());
    put_ext(&mut e, 10, d.as_slice());
    // signature_algorithms
    let mut d: Vec<u8> = Vec::new();
    put_list16(&mut d, cfg.sigs.as_slice());
    put_ext(&mut e, 13, d.as_slice());
    // key_share
    let mut ks: Vec<u8> = Vec::new();
    put_ks_entries(&mut ks, shares);
    let mut d: Vec<u8> = Vec::new();
    put2(&mut d, ks.len());
    put(&mut d, ks.as_slice());
    put_ext(&mut e, 51, d.as_slice());
    let ghost e5 = e@;
    assert(e5 =~= sni_ext(host@) + ext(43, seq![2u8, 3u8, 4u8]) + ext(10, list16(cfg@.groups)) + ext(13, list16(cfg@.sigs)) + ext(
        51,
        be2(ks_entries(shares_view(shares@)).len()) + ks_entries(shares_view(shares@)),
    ));
    // ALPN
    if cfg.alpn.len() > 0 {
        let mut names: Vec<u8> = Vec::new();
        put_alpn_names(&mut names, &cfg.alpn);
        let mut d: Vec<u8> = Vec::new();
        put2(&mut d, names.len());
        put(&mut d, names.as_slice());
        put_ext(&mut e, 16, d.as_slice());
    }
    let ghost e6 = e@;
    assert(e6 =~= e5 + ch_alpn_ext(cfg@.alpn));
    assert(ch_alpn_ext(cfg@.alpn).len() <= 6 + MAX_ALPN * 256) by {
        if cfg@.alpn.len() > 0 {
        }
    }
    // cookie
    match cookie {
        Some(k) => {
            let mut d: Vec<u8> = Vec::new();
            put2(&mut d, k.len());
            put(&mut d, k);
            put_ext(&mut e, 44, d.as_slice());
        },
        None => {},
    }
    assert(e@ =~= e6 + cookie_ext(opt_view(cookie)));
    e
}

/// `client_hello`, built.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn client_hello_x(
    cfg: &ClientConfig,
    host: &[u8],
    random: &[u8; 32],
    sid: &[u8; 32],
    shares: &Vec<(u16, Vec<u8>)>,
    cookie: Option<&[u8]>,
) -> (r: Vec<u8>)
    requires
        cfg.wf(),
        host@.len() <= 253,
        shares_wf(shares@),
        cookie matches Some(k) ==> k@.len() <= MAX_COOKIE,
    ensures
        r@ == client_hello(cfg@, host@, random@, sid@, shares_view(shares@), opt_view(cookie)),
        r@.len() <= 9400,
{
    let e = ch_exts_x(cfg, host, shares, cookie);
    let ghost ev = ch_exts(cfg@, host@, shares_view(shares@), opt_view(cookie));
    let mut b: Vec<u8> = Vec::new();
    put1(&mut b, 3);
    put1(&mut b, 3);
    put(&mut b, random);
    put1(&mut b, 32);
    put(&mut b, sid);
    put_list16(&mut b, cfg.suites.as_slice());
    put1(&mut b, 1);
    put1(&mut b, 0);
    put2(&mut b, e.len());
    put(&mut b, e.as_slice());
    let ghost body = seq![3u8, 3u8] + random@ + seq![32u8] + sid@ + list16(cfg@.suites) + seq![1u8, 0u8] + be2(ev.len()) + ev;
    assert(b@ =~= body);
    let mut m: Vec<u8> = Vec::new();
    put1(&mut m, 1);
    put3(&mut m, b.len());
    put(&mut m, b.as_slice());
    assert(m@ =~= hs_msg(1, body));
    proof {
        reveal(client_hello);
        assert(sid@.len() == 32);
    }
    m
}

// ---------------------------------------------------------------------------
// ServerHello
// ---------------------------------------------------------------------------

/// `ShExts`, as slices.
pub struct ShExtsX<'a> {
    pub version: Option<&'a [u8]>,
    pub key_share: Option<&'a [u8]>,
    pub cookie: Option<&'a [u8]>,
}

impl<'a> View for ShExtsX<'a> {
    type V = ShExts;

    open spec fn view(&self) -> ShExts {
        ShExts { version: opt_view(self.version), key_share: opt_view(self.key_share), cookie: opt_view(self.cookie) }
    }
}

/// `sh_ext_scan(b, no_sh_exts(), hrr)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn sh_ext_scan_x<'a>(b: &'a [u8], hrr: bool) -> (r: Result<ShExtsX<'a>, u8>)
    ensures
        match r {
            Ok(x) => sh_ext_scan(b@, no_sh_exts(), hrr) == Ok::<ShExts, u8>(x@),
            Err(a) => sh_ext_scan(b@, no_sh_exts(), hrr) == Err::<ShExts, u8>(a),
        },
{
    let mut acc = ShExtsX { version: None, key_share: None, cookie: None };
    let mut cur: &'a [u8] = b;
    loop
        invariant
            sh_ext_scan(b@, no_sh_exts(), hrr) == sh_ext_scan(cur@, acc@, hrr),
        decreases cur@.len(),
    {
        let n = cur.len();
        if n == 0 {
            return Ok(acc);
        }
        if n < 4 {
            return Err(DECODE_ERROR_ALERT);
        }
        let t = (cur[0] as usize) * 256 + cur[1] as usize;
        let l = (cur[2] as usize) * 256 + cur[3] as usize;
        proof {
            assert(t == be16(cur@, 0));
            assert(l == be16(cur@, 2));
        }
        if n - 4 < l {
            return Err(DECODE_ERROR_ALERT);
        }
        let d = vstd::slice::slice_subrange(cur, 4, 4 + l);
        let rest = vstd::slice::slice_subrange(cur, 4 + l, n);
        proof {
            assert(d@ =~= cur@.subrange(4, 4 + l as int));
            assert(rest@ =~= cur@.skip(4 + l as int));
        }
        if t == 43 {
            if acc.version.is_some() {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            acc = ShExtsX { version: Some(d), ..acc };
        } else if t == 51 {
            if acc.key_share.is_some() {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            acc = ShExtsX { key_share: Some(d), ..acc };
        } else if t == 44 && hrr {
            if acc.cookie.is_some() {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            acc = ShExtsX { cookie: Some(d), ..acc };
        } else {
            return Err(UNSUPPORTED_EXTENSION);
        }
        cur = rest;
    }
}

/// `SpecShOut`, with the share and cookie as slices of the message.
pub enum ShOut<'a> {
    Hello { suite: u16, group: u16, share: &'a [u8] },
    Retry { suite: u16, group: Option<u16>, cookie: Option<&'a [u8]> },
}

impl<'a> View for ShOut<'a> {
    type V = SpecShOut;

    open spec fn view(&self) -> SpecShOut {
        match *self {
            ShOut::Hello { suite, group, share } => SpecShOut::Hello { suite, group, share: share@ },
            ShOut::Retry { suite, group, cookie } => SpecShOut::Retry { suite, group, cookie: opt_view(cookie) },
        }
    }
}

pub fn has_u16_x(s: &[u16], x: u16) -> (r: bool)
    ensures
        r == s@.contains(x),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != x,
        decreases s@.len() - i,
    {
        if s[i] == x {
            assert(s@[i as int] == x);
            return true;
        }
        i = i + 1;
    }
    false
}

/// Whether the 32 bytes at `b[2..34]` are HelloRetryRequest's random.
fn is_hrr_random(b: &[u8]) -> (r: bool)
    requires
        b@.len() >= 34,
    ensures
        r == (b@.subrange(2, 34) == hrr_random()),
{
    let h: [u8; 32] = [
        0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8,
        0x91, 0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8,
        0x33, 0x9c,
    ];
    assert(h@ =~= hrr_random());
    let mut i: usize = 0;
    while i < 32
        invariant
            i <= 32,
            b@.len() >= 34,
            h@ == hrr_random(),
            forall|j: int| 0 <= j < i ==> b@[2 + j] == h@[j],
        decreases 32 - i,
    {
        if b[2 + i] != h[i] {
            assert(b@.subrange(2, 34)[i as int] != hrr_random()[i as int]);
            return false;
        }
        i = i + 1;
    }
    assert(b@.subrange(2, 34) =~= hrr_random());
    true
}

/// `read_sh(cfg, sid, offered, m)`.
#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
pub fn read_sh_x<'a>(cfg: &ClientConfig, sid: &[u8], offered: &[u16], m: &'a [u8]) -> (r: Result<ShOut<'a>, u8>)
    requires
        m@.len() >= 4,
    ensures
        match r {
            Ok(o) => read_sh(cfg@, sid@, offered@, m@) == Ok::<SpecShOut, u8>(o@),
            Err(a) => read_sh(cfg@, sid@, offered@, m@) == Err::<SpecShOut, u8>(a),
        },
{
    reveal(read_sh);
    let b = vstd::slice::slice_subrange(m, 4, m.len());
    assert(b@ =~= m@.skip(4));
    let n = b.len();
    if n < 35 || b[34] > 32 {
        return Err(DECODE_ERROR_ALERT);
    }
    let l = b[34] as usize;
    if n < 40 + l {
        return Err(DECODE_ERROR_ALERT);
    }
    let el = (b[38 + l] as usize) * 256 + b[39 + l] as usize;
    assert(el == be16(b@, 38 + l as int));
    if n != 40 + l + el {
        return Err(DECODE_ERROR_ALERT);
    }
    let ghost s = parse_sh(b@).unwrap();
    let lv = (b[0] as usize) * 256 + b[1] as usize;
    let suite = ((b[35 + l] as usize) * 256 + b[36 + l] as usize) as u16;
    let comp = b[37 + l];
    let exts = vstd::slice::slice_subrange(b, 40 + l, n);
    let ssid = vstd::slice::slice_subrange(b, 35, 35 + l);
    proof {
        assert(lv == s.legacy_version);
        assert(suite == s.suite);
        assert(comp == s.compression);
        assert(exts@ =~= s.exts);
        assert(ssid@ =~= s.sid);
    }
    let hrr = is_hrr_random(b);
    assert(hrr == (s.random == hrr_random()));
    let x = match sh_ext_scan_x(exts, hrr) {
        Err(a) => return Err(a),
        Ok(x) => x,
    };
    let v = match x.version {
        None => return Err(PROTOCOL_VERSION_A),
        Some(v) => v,
    };
    let vok = v.len() == 2 && v[0] == 3 && v[1] == 4;
    proof {
        if vok {
            assert(v@ =~= seq![3u8, 4u8]);
        } else if v@.len() == 2 {
            assert(v@ != seq![3u8, 4u8]) by {
                if v@ == seq![3u8, 4u8] {
                    assert(v@[0] == 3 && v@[1] == 4);
                }
            }
        }
    }
    if !vok || lv != 0x0303 || !crate::client::eq_bytes(ssid, sid) || comp != 0 || !has_u16_x(cfg.suites.as_slice(), suite) {
        return Err(ILLEGAL_PARAMETER_ALERT);
    }
    if hrr {
        let g: Option<u16> = match x.key_share {
            None => None,
            Some(d) => {
                if d.len() != 2 {
                    return Err(DECODE_ERROR_ALERT);
                }
                let gv = ((d[0] as usize) * 256 + d[1] as usize) as u16;
                assert(gv == be16(d@, 0) as u16);
                if !has_u16_x(cfg.groups.as_slice(), gv) || has_u16_x(offered, gv) {
                    return Err(ILLEGAL_PARAMETER_ALERT);
                }
                Some(gv)
            },
        };
        let k: Option<&'a [u8]> = match x.cookie {
            None => None,
            Some(d) => {
                if d.len() < 3 {
                    return Err(DECODE_ERROR_ALERT);
                }
                let kl = (d[0] as usize) * 256 + d[1] as usize;
                assert(kl == be16(d@, 0));
                if kl != d.len() - 2 {
                    return Err(DECODE_ERROR_ALERT);
                }
                if d.len() - 2 > MAX_COOKIE {
                    return Err(ILLEGAL_PARAMETER_ALERT);
                }
                let kk = vstd::slice::slice_subrange(d, 2, d.len());
                assert(kk@ =~= d@.skip(2));
                Some(kk)
            },
        };
        if g.is_none() && k.is_none() {
            return Err(ILLEGAL_PARAMETER_ALERT);
        }
        return Ok(ShOut::Retry { suite, group: g, cookie: k });
    }
    match x.key_share {
        None => Err(MISSING_EXTENSION_A),
        Some(d) => {
            if d.len() <= 4 {
                return Err(DECODE_ERROR_ALERT);
            }
            let sl = (d[2] as usize) * 256 + d[3] as usize;
            assert(sl == be16(d@, 2));
            if sl != d.len() - 4 {
                return Err(DECODE_ERROR_ALERT);
            }
            let gv = ((d[0] as usize) * 256 + d[1] as usize) as u16;
            assert(gv == be16(d@, 0) as u16);
            if !has_u16_x(offered, gv) {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            let share = vstd::slice::slice_subrange(d, 4, d.len());
            assert(share@ =~= d@.skip(4));
            Ok(ShOut::Hello { suite, group: gv, share })
        },
    }
}

// ---------------------------------------------------------------------------
// EncryptedExtensions, CertificateRequest
// ---------------------------------------------------------------------------

fn has_name(a: &Vec<Vec<u8>>, x: &[u8]) -> (r: bool)
    ensures
        r == chain_view(a@).contains(x@),
{
    let ghost av = chain_view(a@);
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            av == chain_view(a@),
            forall|j: int| 0 <= j < i ==> av[j] != x@,
        decreases a@.len() - i,
    {
        if crate::client::eq_bytes(a[i].as_slice(), x) {
            assert(av[i as int] == x@);
            return true;
        }
        assert(av[i as int] == a@[i as int]@);
        i = i + 1;
    }
    false
}

/// `read_ee(cfg, m)`: the ALPN protocol chosen, a slice of `m`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn read_ee_x<'a>(cfg: &ClientConfig, m: &'a [u8]) -> (r: Result<Option<&'a [u8]>, u8>)
    requires
        m@.len() >= 4,
    ensures
        match r {
            Ok(a) => read_ee(cfg@, m@) == Ok::<Option<Seq<u8>>, u8>(opt_view(a)),
            Err(e) => read_ee(cfg@, m@) == Err::<Option<Seq<u8>>, u8>(e),
        },
{
    reveal(read_ee);
    let b = vstd::slice::slice_subrange(m, 4, m.len());
    assert(b@ =~= m@.skip(4));
    if b.len() < 2 || (b[0] as usize) * 256 + b[1] as usize != b.len() - 2 {
        return Err(DECODE_ERROR_ALERT);
    }
    let all = vstd::slice::slice_subrange(b, 2, b.len());
    assert(all@ =~= b@.skip(2));
    let mut sni = false;
    let mut groups = false;
    let mut alpn: Option<&'a [u8]> = None;
    let mut cur: &'a [u8] = all;
    let ghost init = EeExts { sni: false, groups: false, alpn: None };
    assert(read_ee(cfg@, m@) == match ee_scan(cfg@, all@, init) {
        Ok(x) => Ok::<Option<Seq<u8>>, u8>(x.alpn),
        Err(a) => Err::<Option<Seq<u8>>, u8>(a),
    });
    loop
        invariant
            read_ee(cfg@, m@) == match ee_scan(cfg@, all@, init) {
                Ok(x) => Ok::<Option<Seq<u8>>, u8>(x.alpn),
                Err(a) => Err::<Option<Seq<u8>>, u8>(a),
            },
            init == (EeExts { sni: false, groups: false, alpn: None }),
            ee_scan(cfg@, all@, EeExts { sni: false, groups: false, alpn: None }) == ee_scan(
                cfg@,
                cur@,
                EeExts { sni, groups, alpn: opt_view(alpn) },
            ),
        decreases cur@.len(),
    {
        let n = cur.len();
        if n == 0 {
            return Ok(alpn);
        }
        if n < 4 {
            return Err(DECODE_ERROR_ALERT);
        }
        let t = (cur[0] as usize) * 256 + cur[1] as usize;
        let l = (cur[2] as usize) * 256 + cur[3] as usize;
        proof {
            assert(t == be16(cur@, 0));
            assert(l == be16(cur@, 2));
        }
        if n - 4 < l {
            return Err(DECODE_ERROR_ALERT);
        }
        let d = vstd::slice::slice_subrange(cur, 4, 4 + l);
        let rest = vstd::slice::slice_subrange(cur, 4 + l, n);
        proof {
            assert(d@ =~= cur@.subrange(4, 4 + l as int));
            assert(rest@ =~= cur@.skip(4 + l as int));
        }
        if t == 0 {
            if sni {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            if l != 0 {
                return Err(DECODE_ERROR_ALERT);
            }
            sni = true;
        } else if t == 10 {
            if groups {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            groups = true;
        } else if t == 16 && cfg.alpn.len() > 0 {
            if alpn.is_some() {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            if l < 4 || (d[0] as usize) * 256 + d[1] as usize != l - 2 || d[2] as usize != l - 3 {
                proof {
                    if l >= 4 {
                        assert(be16(d@, 0) == (d[0] as usize) * 256 + d[1] as usize);
                    }
                }
                return Err(DECODE_ERROR_ALERT);
            }
            proof {
                assert(be16(d@, 0) == (d[0] as usize) * 256 + d[1] as usize);
            }
            let name = vstd::slice::slice_subrange(d, 3, l);
            assert(name@ =~= d@.skip(3));
            if !has_name(&cfg.alpn, name) {
                return Err(ILLEGAL_PARAMETER_ALERT);
            }
            alpn = Some(name);
        } else {
            return Err(UNSUPPORTED_EXTENSION);
        }
        cur = rest;
    }
}

/// `read_cr(m)`.
pub fn read_cr_x(m: &[u8]) -> (r: Result<(), u8>)
    requires
        m@.len() >= 4,
    ensures
        r == read_cr(m@),
{
    reveal(read_cr);
    let b = vstd::slice::slice_subrange(m, 4, m.len());
    assert(b@ =~= m@.skip(4));
    let n = b.len();
    if n < 3 {
        return Err(DECODE_ERROR_ALERT);
    }
    let c = b[0] as usize;
    if n < 3 + c {
        return Err(DECODE_ERROR_ALERT);
    }
    let el = (b[1 + c] as usize) * 256 + b[2 + c] as usize;
    assert(el == be16(b@, 1 + c as int));
    if n != 3 + c + el {
        return Err(DECODE_ERROR_ALERT);
    }
    if c != 0 {
        return Err(ILLEGAL_PARAMETER_ALERT);
    }
    Ok(())
}

} // verus!
