//! The verified parser, every accessor and typed RDATA decoder, the
//! presentation printer, and the serializer's round trip.
#![no_main]
use libfuzzer_sys::fuzz_target;
use verilith_dns::{parse, Message, Section};

fuzz_target!(|b: &[u8]| {
    let Some(m) = parse(b) else { return };
    let mut s = Vec::new();
    for q in m.questions() {
        q.name().write_presentation(&mut s);
    }
    for sec in [Section::Answer, Section::Authority, Section::Additional] {
        for rr in m.records(sec) {
            rr.name().write_presentation(&mut s);
            let _ = rr.data();
        }
    }
    let out = m.to_bytes();
    let again = parse(&out).expect("serialized output parses");
    assert_eq!(again.to_bytes(), out);
    let mut reused = Message::new(0, 0);
    assert!(reused.parse_into(b));
    assert_eq!(reused.to_bytes(), out);
});
