use nyx_ssz::{
    bytecollections::ByteList,
    codec::Ssz,
    collections::{List, Vector},
    error::CodecError,
    U256,
};

fn check<T: Ssz + PartialEq + std::fmt::Debug>(input: &[u8], expected: Vec<T>, width: usize) {
    assert_eq!(T::decode_fixed_sequence(input).unwrap(), expected);
    assert!(T::decode_fixed_sequence(&[]).unwrap().is_empty());
    if width > 1 {
        let failure = T::decode_fixed_sequence(&vec![0; width - 1]).err().unwrap();
        assert_eq!(failure.kind, CodecError::ScopeUndivided);
        assert!(failure.state.values.is_empty());
        assert!(failure.state.child.is_none());
    }
}

#[test]
fn should_bulk_decode_all_unsigned_widths_from_unaligned_little_endian_inputs() {
    let mut guarded = vec![0xa5];
    guarded.extend_from_slice(&7_u64.to_le_bytes());
    guarded.extend_from_slice(&u64::MAX.to_le_bytes());
    check(&guarded[1..], vec![7_u64, u64::MAX], 8);
    check(&[1, 255], vec![1_u8, 255], 1);
    check(&[1, 0, 255, 255], vec![1_u16, u16::MAX], 2);
    check(&[255; 8], vec![u32::MAX; 2], 4);
    check(&[255; 32], vec![u128::MAX; 2], 16);
    check(&[255; 64], vec![U256::MAX; 2], 32);
    assert_eq!(
        List::<u64, 2>::decode(&guarded[1..]).unwrap().as_slice(),
        &[7, u64::MAX]
    );
}

static DROPS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
struct BadHook(u8);
impl Drop for BadHook {
    fn drop(&mut self) {
        DROPS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }
}
impl Ssz for BadHook {
    type DecodeState = ();
    const TYPE: &'static nyx_ssz::type_info::TypeDescriptor =
        &nyx_ssz::type_info::TypeDescriptor::Uint(1);
    fn encoded_len(&self) -> Result<usize, CodecError> {
        self.0.encoded_len()
    }
    fn encode_into(&self, out: &mut [u8]) -> Result<(), CodecError> {
        self.0.encode_into(out)
    }
    fn decode(input: &[u8]) -> Result<Self, nyx_ssz::error::DecodeFailure<()>> {
        u8::decode(input).map(Self)
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        self.0.hash_tree_root()
    }
    fn decode_fixed_sequence(
        input: &[u8],
    ) -> Result<Vec<Self>, nyx_ssz::error::DecodeFailure<nyx_ssz::codec::SequenceDecodeState<Self>>>
    {
        // Deliberately malformed external hook: parents must retain all owners.
        let mut values: Vec<_> = input.iter().copied().map(Self).collect();
        values.push(Self(9));
        Ok(values)
    }
}

#[test]
fn should_retain_all_returned_owners_when_an_external_bulk_hook_returns_a_wrong_count() {
    DROPS.store(0, std::sync::atomic::Ordering::SeqCst);
    let failure = List::<BadHook, 1>::decode(&[7]).err().unwrap();
    assert_eq!(failure.kind, CodecError::InvalidLength);
    assert_eq!(
        failure.state.values.iter().map(|v| v.0).collect::<Vec<_>>(),
        [7, 9]
    );
    assert!(failure.state.child.is_none());
    assert_eq!(DROPS.load(std::sync::atomic::Ordering::SeqCst), 0);
    drop(failure);
    assert_eq!(DROPS.load(std::sync::atomic::Ordering::SeqCst), 2);
}

#[test]
fn should_keep_the_generic_boolean_failure_state_and_parent_layout_precedence() {
    let failure = bool::decode_fixed_sequence(&[1, 0, 2, 1]).unwrap_err();
    assert_eq!(failure.kind, CodecError::InvalidBoolean);
    assert_eq!(failure.state.values, [true, false]);
    assert!(failure.state.child.is_some());
    assert_eq!(
        Vector::<bool, 2>::decode(&[2]).err().unwrap().kind,
        CodecError::InvalidLength
    );
    assert_eq!(
        List::<bool, 1>::decode(&[2, 0]).err().unwrap().kind,
        CodecError::OverLimit
    );
    assert_eq!(
        ByteList::<4>::decode_fixed_sequence(&[])
            .err()
            .unwrap()
            .kind,
        CodecError::BadDeclaration
    );
}
