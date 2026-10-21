use nyx_ssz::{
    bitfield::{decode_progressive_bit_list, encode_progressive_bit_list},
    error::CodecError,
    tree_hash::{
        hash_tree_root_bit_list, hash_tree_root_bit_vector, hash_tree_root_byte_list,
        hash_tree_root_byte_vector, hash_tree_root_progressive_bit_list,
        hash_tree_root_progressive_bit_list_view, hash_tree_root_progressive_byte_list,
    },
};
use sha2::{Digest, Sha256};

type Node = [u8; 32];

fn hash(left: &Node, right: &Node) -> Node {
    let mut state = Sha256::new();
    state.update(left);
    state.update(right);
    state.finalize().into()
}

fn pack(data: &[u8]) -> Vec<Node> {
    data.chunks(32)
        .map(|bytes| {
            let mut node = [0; 32];
            node[..bytes.len()].copy_from_slice(bytes);
            node
        })
        .collect()
}

fn pack_bits(bits: &[bool]) -> Vec<u8> {
    let mut bytes = vec![0; bits.len().div_ceil(8)];
    for (index, bit) in bits.iter().enumerate() {
        bytes[index / 8] |= u8::from(*bit) << (index % 8);
    }
    bytes
}

fn bounded(nodes: &[Node], capacity: usize) -> Node {
    let mut level = nodes.to_vec();
    level.resize(capacity.max(1).next_power_of_two(), [0; 32]);
    while level.len() > 1 {
        level = level
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| hash(&pair[0], &pair[1]))
            .collect();
    }
    level[0]
}

fn progressive(nodes: &[Node], width: usize) -> Node {
    if nodes.is_empty() {
        return [0; 32];
    }
    let count = nodes.len().min(width);
    hash(
        &bounded(&nodes[..count], width),
        &progressive(&nodes[count..], width * 4),
    )
}

fn mix(root: Node, count: usize) -> Node {
    let mut word = [0; 32];
    word[..16].copy_from_slice(&(count as u128).to_le_bytes());
    hash(&root, &word)
}

#[test]
fn should_match_independent_byte_vector_roots_across_chunk_boundaries() {
    for count in [1_usize, 31, 32, 33, 63, 64, 65] {
        let bytes = (0..count)
            .map(|index| (index * 17) as u8)
            .collect::<Vec<_>>();
        assert_eq!(
            hash_tree_root_byte_vector(&bytes, count),
            Ok(bounded(&pack(&bytes), count.div_ceil(32)))
        );
    }
}

#[test]
fn should_use_capacity_for_byte_list_trees_but_mix_the_actual_byte_count() {
    for count in [0_usize, 1, 31, 32, 33, 127] {
        let bytes = vec![37; count];
        for capacity in [count, 129] {
            assert_eq!(
                hash_tree_root_byte_list(&bytes, capacity),
                Ok(mix(bounded(&pack(&bytes), capacity.div_ceil(32)), count))
            );
        }
    }
}

#[test]
fn should_pack_bits_without_boolean_byte_expansion_or_list_delimiters() {
    for count in [1_usize, 7, 8, 255, 256, 257, 512, 1025] {
        let bits = (0..count).map(|index| index % 3 != 0).collect::<Vec<_>>();
        let packed = pack_bits(&bits);
        assert_eq!(
            hash_tree_root_bit_vector(&bits, count),
            Ok(bounded(&pack(&packed), count.div_ceil(256)))
        );
        let capacity = count + 259;
        assert_eq!(
            hash_tree_root_bit_list(&bits, capacity),
            Ok(mix(bounded(&pack(&packed), capacity.div_ceil(256)), count))
        );
    }
}

#[test]
fn should_use_progressive_spine_widths_when_byte_lists_cross_each_level() {
    for count in [0_usize, 1, 32, 33, 160, 161, 672, 673, 2720] {
        let bytes = (0..count)
            .map(|index| (index * 13 + 1) as u8)
            .collect::<Vec<_>>();
        let expected = mix(progressive(&pack(&bytes), 1), count);
        assert_eq!(
            hash_tree_root_progressive_byte_list(&bytes, None),
            Ok(expected)
        );
        assert_eq!(
            hash_tree_root_progressive_byte_list(&bytes, Some(count)),
            Ok(expected)
        );
    }
}

#[test]
fn should_root_canonical_progressive_views_without_mutation_or_boolean_expansion() {
    for count in [0_usize, 1, 7, 8, 255, 256, 257, 1279, 1280, 1281, 5377] {
        let bits = (0..count).map(|index| index % 5 != 1).collect::<Vec<_>>();
        let encoded = encode_progressive_bit_list(&bits, None).unwrap();
        let original = encoded.clone();
        let view = decode_progressive_bit_list(&encoded, None).unwrap();
        let pointer = view.as_ssz_bytes().as_ptr();
        let expected = mix(progressive(&pack(&pack_bits(&bits)), 1), count);
        for capacity in [None, Some(count), Some(count + 17)] {
            assert_eq!(
                hash_tree_root_progressive_bit_list(&bits, capacity),
                Ok(expected)
            );
            assert_eq!(
                hash_tree_root_progressive_bit_list_view(&view, capacity),
                Ok(expected)
            );
        }
        assert_eq!(view.as_ssz_bytes().as_ptr(), pointer);
        assert_eq!(view.as_ssz_bytes(), original);
    }
}

#[test]
fn should_reject_illegal_declarations_and_counts_before_merkleization() {
    assert_eq!(
        hash_tree_root_byte_vector(&[1], 0),
        Err(CodecError::EmptyVector)
    );
    assert_eq!(
        hash_tree_root_bit_vector(&[true], 0),
        Err(CodecError::EmptyVector)
    );
    assert_eq!(
        hash_tree_root_byte_vector(&[], 1),
        Err(CodecError::InvalidLength)
    );
    assert_eq!(
        hash_tree_root_bit_vector(&[], 1),
        Err(CodecError::InvalidLength)
    );
    assert_eq!(
        hash_tree_root_byte_list(&[1], 0),
        Err(CodecError::OverLimit)
    );
    assert_eq!(
        hash_tree_root_bit_list(&[true], 0),
        Err(CodecError::OverLimit)
    );
    assert_eq!(
        hash_tree_root_progressive_byte_list(&[1], Some(0)),
        Err(CodecError::OverLimit)
    );
    assert_eq!(
        hash_tree_root_progressive_bit_list(&[true], Some(0)),
        Err(CodecError::OverLimit)
    );
    let encoded = encode_progressive_bit_list(&[true], None).unwrap();
    let view = decode_progressive_bit_list(&encoded, None).unwrap();
    assert_eq!(
        hash_tree_root_progressive_bit_list_view(&view, Some(0)),
        Err(CodecError::OverLimit)
    );
}

#[test]
fn should_handle_empty_values_and_maximum_capacities_without_padding_allocations() {
    let byte_depth = (usize::MAX.div_ceil(32) - 1).ilog2() as usize + 1;
    let byte_zero = (0..byte_depth).fold([0; 32], |root, _| hash(&root, &root));
    assert_eq!(
        hash_tree_root_byte_list(&[], usize::MAX),
        Ok(mix(byte_zero, 0))
    );
    let bit_depth = (usize::MAX.div_ceil(256) - 1).ilog2() as usize + 1;
    let bit_zero = (0..bit_depth).fold([0; 32], |root, _| hash(&root, &root));
    assert_eq!(
        hash_tree_root_bit_list(&[], usize::MAX),
        Ok(mix(bit_zero, 0))
    );
    assert_eq!(hash_tree_root_byte_list(&[], 0), Ok(mix([0; 32], 0)));
    assert_eq!(hash_tree_root_bit_list(&[], 0), Ok(mix([0; 32], 0)));
    assert_eq!(
        hash_tree_root_progressive_byte_list(&[], None),
        Ok(mix([0; 32], 0))
    );
    assert_eq!(
        hash_tree_root_progressive_bit_list(&[], None),
        Ok(mix([0; 32], 0))
    );
}
