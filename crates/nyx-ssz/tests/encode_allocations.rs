use nyx_ssz::{
    bytecollections::ByteList,
    codec::Ssz,
    collections::{list, List},
};
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};
use std::alloc::System;

#[global_allocator]
static ALLOCATOR: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

#[derive(nyx_ssz::Ssz)]
struct Mixed {
    slot: u64,
    payload: ByteList<4096>,
    votes: List<u64, 1024>,
}

#[test]
fn should_allocate_only_the_output_when_encoding_the_shared_mixed_fixture() {
    let value = Mixed {
        slot: 42,
        payload: ByteList::from_bytes(vec![7; 4096]).unwrap(),
        votes: list(vec![1; 1024]).unwrap(),
    };
    let region = Region::new(ALLOCATOR);
    let encoded = value.encode().unwrap();
    let stats = region.change();
    assert_eq!(encoded.len(), 12_304);
    assert_eq!(stats.allocations, 1, "{stats:?}");
    assert_eq!(stats.reallocations, 0, "{stats:?}");
    let mut output = vec![0; value.encoded_len().unwrap()];
    let region = Region::new(ALLOCATOR);
    value.encode_into(&mut output).unwrap();
    let stats = region.change();
    assert_eq!(stats.allocations, 0, "{stats:?}");
    assert_eq!(stats.reallocations, 0, "{stats:?}");
    assert_eq!(output, encoded);
}
