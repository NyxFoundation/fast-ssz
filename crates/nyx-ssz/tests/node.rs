use nyx_ssz::{
    bitcollections::{BitList, BitVector, ProgressiveBitList},
    bytecollections::{ByteList, ByteVector},
    codec::Ssz,
    collections::{list, progressive_list, vector},
    merkle, multiproof, node,
    path::{self, AccessError, Step},
    proof,
};

#[derive(nyx_ssz::Ssz)]
struct Record {
    a: u16,
    items: nyx_ssz::collections::List<u64, 8>,
    bits: BitList<300>,
}
#[derive(nyx_ssz::Ssz)]
#[ssz(progressive)]
struct Sparse {
    #[ssz(position = 255)]
    last: u16,
    #[ssz(position = 0)]
    first: bool,
}
#[derive(nyx_ssz::Ssz)]
enum Choice {
    #[ssz(selector = 1)]
    A(u16),
    #[ssz(selector = 127)]
    B(u16),
}

fn verify_nodes<T: Ssz>(value: &T) {
    let root = value.hash_tree_root().unwrap();
    assert_eq!(node::get(value, 1).unwrap(), root);
    let mut leaves = Vec::new();
    for index in 2..64 {
        let Ok(leaf) = node::get(value, index) else {
            continue;
        };
        let branch = proof::create(value, index).unwrap();
        assert_eq!(branch.leaf, leaf);
        assert!(merkle::verify_merkle_proof(&leaf, &branch.siblings, index, &root).unwrap());
        if index >= 32 {
            leaves.push(index);
        }
    }
    if !leaves.is_empty() {
        leaves.reverse();
        let proof = proof::create_multi(value, &leaves).unwrap();
        assert!(multiproof::verify_merkle_proof(
            &proof.leaves,
            &proof.helpers,
            &proof.indices,
            &root
        )
        .unwrap());
    }
}

#[test]
fn should_match_roots_and_construct_valid_branches_when_accessing_every_type_family() {
    verify_nodes(&true);
    verify_nodes(&0x1234u16);
    verify_nodes(&ByteVector::<65>::from_bytes(vec![42; 65]).unwrap());
    verify_nodes(&ByteList::<100>::from_bytes(vec![42; 35]).unwrap());
    verify_nodes(&BitVector::<257>::decode(&[vec![0xff; 32], vec![1]].concat()).unwrap());
    verify_nodes(&BitList::<300>::decode(&[vec![0xff; 32], vec![3]].concat()).unwrap());
    verify_nodes(&ProgressiveBitList::decode(&[vec![0xff; 32], vec![3]].concat()).unwrap());
    verify_nodes(&vector::<_, 4>(vec![1u64, 2, 3, 4]).unwrap());
    verify_nodes(&list::<_, 32>(vec![1u64, 2, 3, 4, 5]).unwrap());
    verify_nodes(&progressive_list(vec![1u64; 20]));
    verify_nodes(&progressive_list(vec![
        list::<_, 8>(vec![1u16, 2]).unwrap(),
        list::<_, 8>(vec![]).unwrap(),
    ]));
    verify_nodes(&Record {
        a: 9,
        items: list(vec![1, 2, 3]).unwrap(),
        bits: BitList::decode(&[3]).unwrap(),
    });
    verify_nodes(&Sparse {
        last: 8,
        first: true,
    });
    verify_nodes(&Choice::B(7));
}

#[test]
fn should_resolve_names_packed_ranges_and_reserved_words_when_paths_are_typed() {
    let location = path::resolve::<Record>(&[Step::Field("items"), Step::Position(3)]).unwrap();
    assert_eq!(
        (location.generalized_index, location.start, location.stop),
        (20, 24, 32)
    );
    assert_eq!(
        path::resolve::<Record>(&[Step::Position(1), Step::Length])
            .unwrap()
            .generalized_index,
        11
    );
    let bit = path::resolve::<BitList<300>>(&[Step::Position(257)]).unwrap();
    assert_eq!(
        (bit.generalized_index, bit.start, bit.stop, bit.bit_offset),
        (5, 0, 0, Some(1))
    );
    assert_eq!(
        path::resolve::<Sparse>(&[Step::Field("first")])
            .unwrap()
            .generalized_index,
        4
    );
    assert_eq!(
        path::resolve::<Sparse>(&[Step::ActiveFields])
            .unwrap()
            .generalized_index,
        3
    );
    assert_eq!(
        path::resolve::<Choice>(&[Step::Position(127)])
            .unwrap()
            .generalized_index,
        2
    );
    assert_eq!(
        path::resolve::<Choice>(&[Step::Selector])
            .unwrap()
            .generalized_index,
        3
    );
    assert_eq!(path::resolve::<u8>(&[]).unwrap().generalized_index, 1);
}

#[test]
fn should_read_typed_paths_and_generate_shared_helpers_when_fields_are_nested() {
    let value = Record {
        a: 9,
        items: list(vec![1, 2, 3]).unwrap(),
        bits: BitList::decode(&[3]).unwrap(),
    };
    let steps = [Step::Field("items"), Step::Length];
    assert_eq!(node::at_path(&value, &steps).unwrap()[0], 3);
    let branch = proof::at_path(&value, &steps).unwrap();
    assert_eq!(branch.root, value.hash_tree_root().unwrap());
    let proof = proof::create_multi(&value, &[11, 4, 6]).unwrap();
    assert!(multiproof::verify_merkle_proof(
        &proof.leaves,
        &proof.helpers,
        &proof.indices,
        &proof.root
    )
    .unwrap());
}

#[test]
fn should_address_padding_without_allocating_it_when_capacity_is_machine_maximum() {
    let value = ByteList::<{ usize::MAX }>::from_bytes(vec![1]).unwrap();
    let location =
        path::resolve::<ByteList<{ usize::MAX }>>(&[Step::Position(usize::MAX - 1)]).unwrap();
    let branch = proof::create(&value, location.generalized_index).unwrap();
    assert_eq!(branch.leaf, [0; 32]);
    assert!(merkle::verify_merkle_proof(
        &branch.leaf,
        &branch.siblings,
        branch.index,
        &value.hash_tree_root().unwrap()
    )
    .unwrap());
}

#[test]
fn should_reject_invalid_paths_and_requests_without_returning_truncated_indices() {
    assert_eq!(
        path::resolve::<u8>(&[Step::Position(0)]),
        Err(AccessError::InvalidPath)
    );
    assert_eq!(
        path::resolve::<Record>(&[Step::Field("missing")]),
        Err(AccessError::NoSuchPosition)
    );
    assert_eq!(
        path::resolve::<Record>(&[Step::Length]),
        Err(AccessError::InvalidPath)
    );
    assert_eq!(
        path::resolve::<ByteList<1>>(&[Step::Position(1)]),
        Err(AccessError::NoSuchPosition)
    );
    assert_eq!(
        path::resolve::<ByteList<1>>(&[Step::Length, Step::Position(0)]),
        Err(AccessError::InvalidPath)
    );
    assert!(path::resolve::<Choice>(&[Step::Position(0)]).is_err());
    type Base = nyx_ssz::collections::List<nyx_ssz::U256, { usize::MAX }>;
    type Nested = nyx_ssz::collections::List<Base, { usize::MAX }>;
    type Deeper = nyx_ssz::collections::List<Nested, { usize::MAX }>;
    type Deep = nyx_ssz::collections::List<
        nyx_ssz::collections::List<Deeper, { usize::MAX }>,
        { usize::MAX },
    >;
    assert_eq!(
        path::resolve::<Deep>(&[Step::Position(0); 5]),
        Err(AccessError::Proof(merkle::ProofError::IndexOverflow))
    );
    assert!(node::get(&true, 0).is_err());
    assert!(node::get(&true, 2).is_err());
    assert!(proof::create(&true, 1).is_err());
    assert!(proof::create_multi(&true, &[]).is_err());
    assert!(proof::create_multi(&true, &[2, 2]).is_err());
    assert!(proof::create_multi(&true, &[2, 4]).is_err());
}
