use nyx_ssz::{codec::Ssz, U256};
use yaml_serde::Value;

use crate::{
    fixture::{decode_snappy, Case, Outcome},
    types::{validate_families, FromFixture, Schema},
};

#[test]
fn should_accept_the_exact_supported_vector_lengths_when_the_name_is_canonical() {
    for count in [0, 1, 2, 3, 4, 5, 8, 16, 31, 512, 513] {
        assert!(Schema::parse("basic_vector", &format!("vec_uint64_{count}_zero")).is_ok());
    }
}

#[test]
fn should_reject_unknown_schemas_instead_of_skipping_them() {
    assert!(Schema::parse("containers", "UnknownStruct_zero").is_err());
    assert!(Schema::parse("containers", "SmallTestStruct_zero").is_ok());
    assert!(Schema::parse("uints", "uint_512_max").is_err());
    assert!(Schema::parse("basic_vector", "vec_bool_511_zero").is_err());
    assert!(Schema::parse("basic_vector", "vec_uint9_1_zero").is_err());
}

#[test]
fn should_check_typed_progressive_values_roots_and_invalid_inputs() {
    use nyx_ssz::collections::progressive_list;
    let value = progressive_list(vec![0x0102_u16, 0x0304]);
    let case = Case {
        outcome: Outcome::Valid,
        bytes: vec![2, 1, 4, 3],
        value: Some(Value::Sequence(vec![Value::from(258), Value::from(772)])),
        root: Some(value.hash_tree_root().unwrap()),
    };
    let schema = Schema::parse("basic_progressive_list", "proglist_uint16_random_2").unwrap();
    assert!(schema.verify(&case).is_ok());
    let wrong = Case {
        root: Some([0; 32]),
        ..case
    };
    assert!(schema.verify(&wrong).is_err());
    let invalid = Case {
        outcome: Outcome::Invalid,
        bytes: vec![1],
        value: None,
        root: None,
    };
    assert!(schema.verify(&invalid).is_ok());
    assert!(Schema::parse("basic_progressive_list", "proglist_uint17_zero_0").is_err());
    assert!(validate_families(&["basic_progressive_list".into()]).is_ok());
}

#[test]
fn should_validate_family_arguments_before_accessing_the_filesystem() {
    assert!(validate_families(&[]).is_err());
    assert!(validate_families(&["../outside".into()]).is_err());
    assert!(validate_families(&["boolean".into(), "boolean".into()]).is_err());
    assert!(validate_families(&["boolean".into(), "uints".into()]).is_ok());
}

#[test]
fn should_parse_full_width_unsigned_values_without_truncation() {
    let value = Value::String(u128::MAX.to_string());
    assert_eq!(u128::from_fixture(&value).unwrap(), u128::MAX);
    let value = Value::String(U256::MAX.to_string());
    assert_eq!(U256::from_fixture(&value).unwrap(), U256::MAX);
    assert!(u64::from_fixture(&Value::String(u128::MAX.to_string())).is_err());
}

#[test]
fn should_reject_negative_or_mistyped_yaml_values() {
    assert!(u8::from_fixture(&Value::from(-1)).is_err());
    assert!(u8::from_fixture(&Value::Bool(true)).is_err());
    assert!(bool::from_fixture(&Value::String("true".into())).is_err());
}

#[test]
fn should_preserve_exact_yaml_bytes_when_constructing_owned_byte_values() {
    use nyx_ssz::bytecollections::{ByteList, ByteVector};

    let bytes = Value::Sequence(vec![Value::from(1), Value::from(255)]);
    assert_eq!(
        ByteVector::<2>::from_fixture(&bytes).unwrap().as_bytes(),
        &[1, 255]
    );
    assert_eq!(
        ByteList::<2>::from_fixture(&bytes).unwrap().as_bytes(),
        &[1, 255]
    );
    assert!(ByteVector::<1>::from_fixture(&bytes).is_err());
    assert!(ByteList::<1>::from_fixture(&bytes).is_err());
    assert!(ByteVector::<0>::from_fixture(&Value::Sequence(vec![])).is_err());
    assert!(ByteList::<0>::from_fixture(&Value::Sequence(vec![])).is_ok());
    for invalid in [
        Value::Bool(true),
        Value::Sequence(vec![Value::from(256)]),
        Value::Sequence(vec![Value::from(-1)]),
    ] {
        assert!(ByteVector::<1>::from_fixture(&invalid).is_err());
        assert!(ByteList::<1>::from_fixture(&invalid).is_err());
    }
}

#[test]
fn should_check_owned_byte_outputs_and_roots_against_fixture_expectations() {
    use nyx_ssz::bytecollections::{ByteList, ByteVector};

    let mut root = [0; 32];
    root[..2].copy_from_slice(&[1, 255]);
    let mut case = Case {
        outcome: Outcome::Valid,
        bytes: vec![1, 255],
        value: Some(Value::Sequence(vec![Value::from(1), Value::from(255)])),
        root: Some(root),
    };
    assert!(crate::types::verify::<ByteVector<2>>(&case).is_ok());
    assert!(Schema::parse("basic_vector", "vec_uint8_2_random")
        .unwrap()
        .verify(&case)
        .is_ok());
    case.value = Some(Value::Sequence(vec![Value::from(255), Value::from(1)]));
    assert!(crate::types::verify::<ByteVector<2>>(&case).is_err());
    case.value = Some(Value::Sequence(vec![Value::from(1), Value::from(255)]));
    case.root = Some([0; 32]);
    assert!(crate::types::verify::<ByteVector<2>>(&case).is_err());
    // Independent SHA-256 of the packed data chunk followed by the length chunk.
    case.root = Some([
        0x3d, 0x5e, 0x67, 0xb9, 0x23, 0x26, 0xd8, 0x24, 0x46, 0x27, 0x39, 0x37, 0xd1, 0x5e, 0x08,
        0x6a, 0xc7, 0xf7, 0xfd, 0x57, 0x32, 0x53, 0x5e, 0xa3, 0xb9, 0x4f, 0x27, 0xc4, 0xfa, 0xad,
        0xb4, 0x78,
    ]);
    assert!(crate::types::verify::<ByteList<2>>(&case).is_ok());
    case.outcome = Outcome::Invalid;
    assert!(crate::types::verify::<ByteVector<2>>(&case).is_err());
    assert!(crate::types::verify::<ByteList<2>>(&case).is_err());
    case.bytes.push(3);
    assert!(crate::types::verify::<ByteVector<2>>(&case).is_ok());
    assert!(crate::types::verify::<ByteList<2>>(&case).is_ok());
}

#[test]
fn should_reject_malformed_or_oversized_snappy_before_allocating_output() {
    assert!(decode_snappy(&[255, 255, 255, 255, 255]).is_err());
    assert!(decode_snappy(&[128, 128, 128, 128, 1]).is_err());
}

#[test]
fn should_check_the_expected_value_not_only_a_round_trip() {
    let case = Case {
        outcome: Outcome::Valid,
        bytes: vec![1],
        value: Some(Value::Bool(false)),
        root: Some(true.hash_tree_root().unwrap()),
    };
    assert!(Schema::parse("boolean", "true")
        .unwrap()
        .verify(&case)
        .is_err());
}

#[test]
fn should_check_the_expected_root_independently() {
    let case = Case {
        outcome: Outcome::Valid,
        bytes: vec![1],
        value: Some(Value::Bool(true)),
        root: Some([0; 32]),
    };
    assert!(Schema::parse("boolean", "true")
        .unwrap()
        .verify(&case)
        .is_err());
}

#[test]
fn should_require_rejection_for_invalid_vectors() {
    let case = Case {
        outcome: Outcome::Invalid,
        bytes: vec![1],
        value: None,
        root: None,
    };
    assert!(Schema::parse("boolean", "byte_0x01")
        .unwrap()
        .verify(&case)
        .is_err());
    let case = Case {
        outcome: Outcome::Invalid,
        bytes: vec![128],
        value: None,
        root: None,
    };
    assert!(Schema::parse("boolean", "byte_0x80")
        .unwrap()
        .verify(&case)
        .is_ok());
}

#[test]
fn should_parse_all_bit_family_schema_forms_without_guessing_missing_limits() {
    for (family, name) in [
        ("bitvector", "bitvec_15_random"),
        ("bitlist", "bitlist_15_random_0"),
        ("bitlist", "bitlist_no_delimiter_empty"),
        ("progressive_bitlist", "progbitlist_lengthy_1025_0"),
    ] {
        assert!(Schema::parse(family, name).is_ok());
    }
    assert!(Schema::parse("bitlist", "bitlist_unknown_15").is_err());
    assert!(Schema::parse("bitvector", "bitvec_unknown").is_err());
}

#[test]
fn should_check_owned_bit_observations_and_roots_against_independent_yaml_values() {
    use nyx_ssz::bitcollections::ProgressiveBitList;
    let value = ProgressiveBitList::from_bits(&[true, false, true]).unwrap();
    let mut case = Case {
        outcome: Outcome::Valid,
        bytes: vec![13],
        value: Some(Value::String("0x0d".into())),
        root: Some(value.hash_tree_root().unwrap()),
    };
    assert!(crate::owned_bits::verify_progressive(&case).is_ok());
    case.value = Some(Value::String("0x0b".into()));
    assert!(crate::owned_bits::verify_progressive(&case).is_err());
    case.value = Some(Value::String("0x0d".into()));
    case.root = Some([0; 32]);
    assert!(crate::owned_bits::verify_progressive(&case).is_err());
    assert!(crate::owned_bits::verify_bounded(&case, 510, true).is_err());
}

#[test]
fn should_read_yaml_bit_order_independently_of_the_library_decoder() {
    let data = Value::String("0x05".into());
    assert_eq!(
        crate::bits::expected_bits(&data, Some(3)).unwrap(),
        [true, false, true]
    );
    let data = Value::String("0x0d".into());
    assert_eq!(
        crate::bits::expected_bits(&data, None).unwrap(),
        [true, false, true]
    );
    assert!(crate::bits::expected_bits(&Value::String("0x85".into()), Some(3)).is_err());
    assert!(crate::bits::expected_bits(&Value::String("0x00".into()), None).is_err());
}
