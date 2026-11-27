//! `route`: connection IDs name their slot, and Version Negotiation.
use verilith_quic::packet::{parse_header, Header};
use verilith_quic::route::{cid_slot, make_cid, version_negotiation};

#[test]
fn cids_name_their_slot() {
    for slot in [0u32, 1, 77, 0xdead_beef, u32::MAX] {
        let c = make_cid(slot, &[9, 8, 7, 6]);
        assert_eq!(cid_slot(&c), Some(slot));
    }
    assert_eq!(cid_slot(&[0; 7]), None);
}

#[test]
fn version_negotiation_echoes_the_ids_swapped() {
    let mut out = vec![1, 2, 3];
    assert!(version_negotiation(b"client-dcid", b"cscid", 0xff, &mut out));
    match parse_header(&out, 0, 0) {
        Some((Header::VersionNegotiation { first, dcid, scid, versions }, e)) => {
            assert_eq!(e, out.len());
            assert!(first & 0x80 != 0);
            assert_eq!(dcid, b"cscid");
            assert_eq!(scid, b"client-dcid");
            assert_eq!(versions, &[0, 0, 0, 1]);
        }
        _ => panic!("not a Version Negotiation packet"),
    }
}
