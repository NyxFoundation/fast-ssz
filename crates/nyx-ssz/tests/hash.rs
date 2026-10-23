use nyx_ssz::sha256::hash_pair;
use sha2::{Digest, Sha256};

#[test]
fn should_hash_two_zero_nodes_to_the_known_sha256_root() {
    assert_eq!(
        hash_pair(&[0; 32], &[0; 32]),
        [
            0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30, 0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09,
            0x97, 0x9b, 0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8, 0xea, 0x98, 0x31, 0xa9,
            0x27, 0x59, 0xfb, 0x4b,
        ]
    );
}

#[test]
fn should_hash_exact_concatenation_when_node_pairs_have_diverse_bytes() {
    let mut seed = 0x243f_6a88_85a3_08d3_u64;
    for case in 0..512 {
        let mut message = [0; 64];
        for byte in &mut message {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            *byte = match case {
                0 => 0,
                1 => 255,
                _ => seed as u8,
            };
        }
        let left: [u8; 32] = message[..32].try_into().unwrap();
        let right: [u8; 32] = message[32..].try_into().unwrap();
        let expected: [u8; 32] = Sha256::digest(message).into();
        assert_eq!(hash_pair(&left, &right), expected, "case {case}");
    }
}

#[test]
fn should_match_known_answers_when_input_bytes_are_nonzero() {
    // Independent known-answer digests, not a comparison with the same backend.
    let inputs = [
        std::array::from_fn::<_, 64, _>(|index| index as u8),
        [255; 64],
    ];
    let expected = [
        [
            253, 234, 185, 172, 243, 113, 3, 98, 189, 38, 88, 205, 201, 162, 158, 143, 156, 117,
            127, 207, 152, 17, 96, 58, 140, 68, 124, 209, 217, 21, 17, 8,
        ],
        [
            134, 103, 231, 24, 41, 78, 158, 13, 241, 211, 6, 0, 186, 62, 235, 32, 31, 118, 74, 173,
            45, 173, 114, 116, 134, 67, 228, 162, 133, 225, 209, 247,
        ],
    ];
    for (input, digest) in inputs.iter().zip(expected) {
        let left = input[..32].try_into().unwrap();
        let right = input[32..].try_into().unwrap();
        assert_eq!(hash_pair(&left, &right), digest);
    }
}

#[test]
fn should_preserve_left_right_order_in_merkle_combination() {
    let left = [0x11; 32];
    let right = [0x22; 32];
    assert_ne!(hash_pair(&left, &right), hash_pair(&right, &left));
    let mut expected = Sha256::new();
    expected.update(left);
    expected.update(right);
    assert_eq!(
        hash_pair(&left, &right).as_slice(),
        expected.finalize().as_slice()
    );
}
