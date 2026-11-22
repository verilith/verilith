#![allow(unsafe_op_in_unsafe_fn)]
mod proto;
use domain::base::ToName;
use hickory_proto::op::{Message, MessageType, OpCode, Query};
use hickory_proto::rr::{rdata, Name, RData, Record, RecordType};
use std::hint::black_box;
use std::os::raw::{c_char, c_int, c_long, c_uchar, c_void};
use std::str::FromStr;
use std::time::Instant;

unsafe extern "C" {
    fn ares_dns_parse(buf: *const c_uchar, len: usize, flags: u32, rec: *mut *mut c_void) -> c_int;
    fn ares_dns_record_destroy(rec: *mut c_void);
    fn ares_expand_name(enc: *const c_uchar, abuf: *const c_uchar, alen: c_int, s: *mut *mut c_char, enclen: *mut c_long) -> c_int;
    fn ares_free_string(s: *mut c_void);
    fn ares_dns_write(rec: *const c_void, buf: *mut *mut c_uchar, len: *mut usize) -> c_int;
}

// `dnsbench ROW` runs only the rows whose name is exactly ROW, so that each
// implementation can be timed in its own process.
fn bench<F: FnMut() -> usize>(name: &str, msg: &str, mut f: F) {
    if let Some(only) = std::env::args().nth(1) {
        if only != name { return; }
    }
    for _ in 0..1000 { black_box(f()); }
    let mut best = f64::MAX;
    for _ in 0..30 {
        let iters = 20000;
        let t = Instant::now();
        for _ in 0..iters { black_box(f()); }
        best = best.min(t.elapsed().as_secs_f64() / iters as f64);
    }
    println!("{msg}\t{name}\t{:.0}", best * 1e9);
}

fn n(s: &str) -> Name { Name::from_str(s).unwrap() }
fn a(name: &str, ip: [u8; 4]) -> Record { Record::from_rdata(n(name), 300, RData::A(rdata::A::new(ip[0], ip[1], ip[2], ip[3]))) }
fn ns(name: &str, t: &str) -> Record { Record::from_rdata(n(name), 86400, RData::NS(rdata::NS(n(t)))) }

fn build(kind: &str) -> Vec<u8> {
    let mut m = Message::new(0x1234, MessageType::Response, OpCode::Query);
    m.metadata.recursion_desired = true;
    m.metadata.recursion_available = true;
    match kind {
        "small" => {
            m.add_query(Query::query(n("example.com."), RecordType::A));
            m.add_answer(a("example.com.", [93, 184, 215, 14]));
        }
        "typical" => {
            m.add_query(Query::query(n("www.example.com."), RecordType::A));
            m.add_answer(Record::from_rdata(n("www.example.com."), 300, RData::CNAME(rdata::CNAME(n("www.example.com.cdn.example.net.")))));
            for i in 0..4 { m.add_answer(a("www.example.com.cdn.example.net.", [192, 0, 2, i])); }
            for i in 0..4 { m.add_authority(ns("example.net.", &format!("ns{i}.example.net."))); }
            for i in 0..4 { m.add_additional(a(&format!("ns{i}.example.net."), [198, 51, 100, i])); }
        }
        _ => {
            m.add_query(Query::query(n("big.example.org."), RecordType::A));
            for i in 0..30 { m.add_answer(a("big.example.org.", [203, 0, 113, i])); }
            for i in 0..13 { m.add_authority(ns("example.org.", &format!("{}.ns.example-servers.org.", (b'a' + i) as char))); }
            for i in 0..13 { m.add_additional(a(&format!("{}.ns.example-servers.org.", (b'a' + i) as char), [198, 51, 100, i])); }
        }
    }
    m.to_vec().unwrap()
}

fn main() {
    println!("message\tparser\tns/msg");
    for kind in ["small", "typical", "large"] {
        let b = build(kind);
        std::fs::write(format!("./{kind}.dns"), &b).unwrap();
        // sanity: everyone accepts it
        let v = verilith_dns::parse(&b).expect("vdns");
        let total = v.questions().len() + v.answers().len() + v.authorities().len() + v.additionals().len();
        eprintln!("{kind}: {} bytes, {} q+rr", b.len(), total);
        let label = format!("{kind} ({}B, {} rr)", b.len(), total);

        bench("vdns parse", &label, || verilith_dns::parse(&b).unwrap().answer_count());
        let mut reuse = verilith_dns::Message::new(0, 0);
        bench("vdns Message::parse_into (reused buffers)", &label, || {
            assert!(reuse.parse_into(&b));
            reuse.answer_count()
        });
        bench("vdns parse + decode every record's RDATA", &label, || {
            let m = verilith_dns::parse(&b).unwrap();
            let mut c = 0;
            for s in [verilith_dns::Section::Answer, verilith_dns::Section::Authority, verilith_dns::Section::Additional] {
                for rr in m.records(s) {
                    c += rr.data().is_some() as usize;
                }
            }
            c
        });
        bench("vdns-backed ares_dns_parse (same c-ares record)", &label, || unsafe {
            let mut rec = std::ptr::null_mut();
            assert_eq!(verilith_dns::cares::vdns_ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec), 0);
            ares_dns_record_destroy(rec);
            1
        });
        bench("prototype: arena names, no per-label alloc (unverified)", &label, || proto::parse(&b).unwrap().rrs.len());
        bench("hickory-proto Message::from_vec (decodes RDATA)", &label, || {
            let m = Message::from_vec(&b).unwrap();
            m.answers.len()
        });
        bench("domain: walk all RRs, materialize owner names", &label, || {
            use domain::base::Message as DM;
            let m = DM::from_octets(&b[..]).unwrap();
            let mut c = 0;
            for q in m.question() { let q = q.unwrap(); c += q.qname().to_name::<Vec<u8>>().len(); }
            let mut sec = m.answer().unwrap();
            loop {
                for rr in &mut sec { let rr = rr.unwrap(); c += rr.owner().to_name::<Vec<u8>>().len() + rr.rdlen() as usize; }
                match sec.next_section().unwrap() { Some(s) => sec = s, None => break }
            }
            c
        });
        bench("simple-dns Packet::parse (names as borrowed labels, typed RDATA)", &label, || {
            let p = simple_dns::Packet::parse(&b).unwrap();
            p.answers.len() + p.name_servers.len() + p.additional_records.len()
        });
        bench("dns-parser Packet::parse (lazy names, typed RDATA)", &label, || {
            let p = dns_parser::Packet::parse(&b).unwrap();
            p.answers.len() + p.nameservers.len() + p.additional.len()
        });
        bench("glibc ns_initparse + ns_parserr x all RRs (lazy names)", &label, || unsafe { glibc_walk(&b, false) });
        bench("glibc ns_parserr + dn_expand x all owners", &label, || unsafe { glibc_walk(&b, true) });
        bench("c-ares ares_dns_parse (decodes RDATA)", &label, || unsafe {
            let mut rec = std::ptr::null_mut();
            assert_eq!(ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec), 0);
            ares_dns_record_destroy(rec);
            1
        });

        // Writing: the parsed message back to wire form, with compression.
        let vm = verilith_dns::parse(&b).unwrap();
        bench("write: vdns to_bytes_compressed", &label, || vm.to_bytes_compressed().len());
        bench("write: vdns to_bytes (uncompressed)", &label, || vm.to_bytes().len());
        let hm = Message::from_vec(&b).unwrap();
        bench("write: hickory-proto Message::to_vec", &label, || hm.to_vec().unwrap().len());
        let sp = simple_dns::Packet::parse(&b).unwrap();
        bench("write: simple-dns build_bytes_vec_compressed", &label, || sp.build_bytes_vec_compressed().unwrap().len());
        let mut rec = std::ptr::null_mut();
        assert_eq!(unsafe { ares_dns_parse(b.as_ptr(), b.len(), 0, &mut rec) }, 0);
        bench("write: vdns-backed ares_dns_write", &label, || unsafe { verilith_dns::cares::dns_write(rec, 0).unwrap().len() });
        bench("write: c-ares ares_dns_write", &label, || unsafe {
            let (mut p, mut l) = (std::ptr::null_mut(), 0);
            assert_eq!(ares_dns_write(rec, &mut p, &mut l), 0);
            ares_free_string(p as *mut c_void);
            l
        });
        eprintln!(
            "{kind}: written sizes simple-dns {} vdns {} hickory {} vdns-backed ares_dns_write {} c-ares {} (input {})",
            sp.build_bytes_vec_compressed().unwrap().len(),
            vm.to_bytes_compressed().len(),
            hm.to_vec().unwrap().len(),
            unsafe { verilith_dns::cares::dns_write(rec, 0).unwrap().len() },
            unsafe {
                let (mut p, mut l) = (std::ptr::null_mut(), 0);
                ares_dns_write(rec, &mut p, &mut l);
                ares_free_string(p as *mut c_void);
                l
            },
            b.len()
        );
        unsafe { ares_dns_record_destroy(rec) };

        // Name decoding only: every owner name offset, as ares_expand_name callers do.
        let mut offs = Vec::new();
        {
            let mut p = 12;
            let (e, _) = verilith_dns::parse::read_name_into(&b, p, &mut Vec::new()).unwrap(); offs.push(p); p = e + 4;
            for _ in 0..(total - 1) { let (e, _) = verilith_dns::parse::read_name_into(&b, p, &mut Vec::new()).unwrap(); offs.push(p); p = e + 8; let rl = u16::from_be_bytes([b[p], b[p + 1]]) as usize; p += 2 + rl; }
        }
        bench("expand_name x all owners: vdns", &label, || unsafe {
            let mut c = 0;
            for &o in &offs { let mut s = std::ptr::null_mut(); let mut l = 0; assert_eq!(verilith_dns::capi::vdns_expand_name(b.as_ptr().add(o), b.as_ptr(), b.len() as c_int, &mut s, &mut l), 0); c += l as usize; libc_free(s as *mut c_void); }
            c
        });
        bench("expand_name x all owners: c-ares", &label, || unsafe {
            let mut c = 0;
            for &o in &offs { let mut s = std::ptr::null_mut(); let mut l = 0; assert_eq!(ares_expand_name(b.as_ptr().add(o), b.as_ptr(), b.len() as c_int, &mut s, &mut l), 0); c += l as usize; ares_free_string(s as *mut c_void); }
            c
        });
        bench("read_name_into x all owners: vdns (wire form)", &label, || {
            let mut c = 0;
            let mut w = Vec::with_capacity(256);
            for &o in &offs { w.clear(); c += verilith_dns::parse::read_name_into(&b, o, &mut w).unwrap().0; }
            c
        });
    }
}
unsafe extern "C" { #[link_name = "free"] fn libc_free(p: *mut c_void); }

// glibc's libresolv (ns_initparse / ns_parserr / dn_expand).
#[repr(C)]
struct NsMsg { msg: *const u8, eom: *const u8, id: u16, flags: u16, counts: [u16; 4], sections: [*const u8; 4], sect: c_int, rrnum: c_int, msg_ptr: *const u8 }
#[repr(C)]
struct NsRr { name: [c_char; 1025], typ: u16, class: u16, ttl: u32, rdlength: u16, rdata: *const u8 }
#[link(name = "resolv")]
unsafe extern "C" {
    fn ns_initparse(msg: *const u8, len: c_int, handle: *mut NsMsg) -> c_int;
    fn ns_parserr(handle: *mut NsMsg, sect: c_int, rrnum: c_int, rr: *mut NsRr) -> c_int;
    fn dn_expand(msg: *const u8, eom: *const u8, src: *const u8, dst: *mut c_char, len: c_int) -> c_int;
}
unsafe fn glibc_walk(b: &[u8], expand: bool) -> usize {
    let mut h: NsMsg = std::mem::zeroed();
    assert_eq!(ns_initparse(b.as_ptr(), b.len() as c_int, &mut h), 0);
    let mut rr: NsRr = std::mem::zeroed();
    let mut c = 0;
    for s in 0..4 {
        for i in 0..h.counts[s] as c_int {
            assert_eq!(ns_parserr(&mut h, s as c_int, i, &mut rr), 0);
            c += rr.rdlength as usize + rr.name[0] as usize;
            if expand && (rr.typ == 2 || rr.typ == 5) {
                let mut out = [0 as c_char; 1025];
                c += dn_expand(b.as_ptr(), b.as_ptr().add(b.len()), rr.rdata, out.as_mut_ptr(), 1025) as usize;
            }
        }
    }
    c
}
