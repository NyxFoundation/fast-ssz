use libssz::SszDecode;
use nyx_ssz::codec::Ssz;
use nyx_ssz_bench_compare::{nyx, reference};

#[test]
fn should_decode_expected_fields_when_the_canonical_shared_inputs_are_used() {
    let fixtures = nyx_ssz_bench_compare::fixtures();
    let header = hex::decode(fixtures[0]["wire"].as_str().unwrap()).unwrap();
    let n = nyx::Header::decode(&header).unwrap();
    let l = reference::Header::from_ssz_bytes(&header).unwrap();
    assert_eq!(n.slot, 0x0102030405060708);
    assert_eq!(n.proposer_index, 0x1122334455667788);
    assert_eq!((n.slot, n.proposer_index), (l.slot, l.proposer_index));
    assert_eq!(n.parent_root.as_bytes(), l.parent_root);
    assert_eq!(n.state_root.as_bytes(), l.state_root);
    assert_eq!(n.body_root.as_bytes(), l.body_root);
    let mixed = hex::decode(fixtures[1]["wire"].as_str().unwrap()).unwrap();
    let n = nyx::Mixed::decode(&mixed).unwrap();
    let l = reference::Mixed::from_ssz_bytes(&mixed).unwrap();
    assert_eq!(n.slot, 42);
    assert_eq!(l.slot, 42);
    assert_eq!(n.payload.as_bytes(), &[7; 4096]);
    assert_eq!(&l.payload[..], &[7; 4096]);
    assert_eq!(n.votes.as_slice(), &[1; 1024]);
    assert_eq!(&l.votes[..], &[1; 1024]);
}
