use nyx_ssz::{
    codec::{decode_elements, SequenceDecodeState, Ssz},
    collections::{BoundedProgressiveList, List, ProgressiveList, Vector},
    error::{CodecError, DecodeFailure},
    sequence::{fixed_list_view, fixed_vector_view, SequenceView},
    type_info::TypeDescriptor,
};

type Outcome<T> = Result<Vec<T>, (CodecError, Vec<T>, bool)>;
fn observe<T: Ssz>(value: Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>>) -> Outcome<T> {
    value.map_err(|failure| {
        (
            failure.kind,
            failure.state.values,
            failure.state.child.is_some(),
        )
    })
}
fn through_view<T: Ssz>(view: Result<SequenceView<'_>, CodecError>) -> Outcome<T> {
    match view {
        Ok(view) => observe(decode_elements::<T>(&view)),
        Err(kind) => Err((kind, Vec::new(), false)),
    }
}

#[test]
fn should_match_view_based_failure_states_for_all_short_boolean_encodings() {
    for count in 0..=5_u32 {
        for pattern in 0..3_usize.pow(count) {
            let mut pattern = pattern;
            let input: Vec<_> = (0..count)
                .map(|_| {
                    let byte = (pattern % 3) as u8;
                    pattern /= 3;
                    byte
                })
                .collect();
            let expected = through_view::<bool>(fixed_list_view(&input, 1, Some(3)));
            assert_eq!(
                observe(List::<bool, 3>::decode(&input).map(|v| v.as_slice().to_vec())),
                expected
            );
            assert_eq!(
                observe(
                    BoundedProgressiveList::<bool, 3>::decode(&input)
                        .map(|v| v.as_slice().to_vec())
                ),
                expected
            );
            let expected = through_view::<bool>(fixed_list_view(&input, 1, None));
            assert_eq!(
                observe(ProgressiveList::<bool>::decode(&input).map(|v| v.as_slice().to_vec())),
                expected
            );
            let expected = through_view::<bool>(fixed_vector_view(&input, 1, 3));
            assert_eq!(
                observe(Vector::<bool, 3>::decode(&input).map(|v| v.as_slice().to_vec())),
                expected
            );
        }
    }
}

#[test]
fn should_preserve_alignment_and_capacity_faults_for_multibyte_elements() {
    for count in 0..=12 {
        let input: Vec<_> = (0..count).map(|index| index as u8).collect();
        let expected = through_view::<u16>(fixed_list_view(&input, 2, Some(3)));
        assert_eq!(
            observe(List::<u16, 3>::decode(&input).map(|v| v.as_slice().to_vec())),
            expected
        );
        assert_eq!(
            observe(
                BoundedProgressiveList::<u16, 3>::decode(&input).map(|v| v.as_slice().to_vec())
            ),
            expected
        );
        let expected = through_view::<u16>(fixed_vector_view(&input, 2, 3));
        assert_eq!(
            observe(Vector::<u16, 3>::decode(&input).map(|v| v.as_slice().to_vec())),
            expected
        );
    }
}

#[derive(Debug)]
struct PaddedBool {
    value: bool,
    _padding: [u8; 511],
}
impl Ssz for PaddedBool {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Boolean;
    fn encoded_len(&self) -> Result<usize, CodecError> {
        self.value.encoded_len()
    }
    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        self.value.encode_into(output)
    }
    fn decode(input: &[u8]) -> Result<Self, DecodeFailure<()>> {
        bool::decode(input).map(|value| Self {
            value,
            _padding: [0; 511],
        })
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        self.value.hash_tree_root()
    }
}

#[test]
fn should_not_reserve_unrepresentable_full_storage_before_a_later_child_refusal() {
    const COUNT: usize = 1 << 22;
    let mut input = vec![0; COUNT];
    input[1] = 2;
    assert_eq!(core::mem::size_of::<PaddedBool>(), 512);
    let failure = List::<PaddedBool, COUNT>::decode(&input).unwrap_err();
    assert_eq!(failure.kind, CodecError::InvalidBoolean);
    assert_eq!(failure.state.values.len(), 1);
    assert!(!failure.state.values[0].value);
    assert!(failure.state.child.is_some());
    assert!(failure.state.values.capacity() <= COUNT / 512);
}

// A metadata-only dictionary: no native input can contain one complete element.
struct TooWide;
impl Ssz for TooWide {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor =
        &TypeDescriptor::Vector(&TypeDescriptor::ByteVector(usize::MAX), 2);
    fn encoded_len(&self) -> Result<usize, CodecError> {
        panic!("layout must not invoke value encoding")
    }
    fn encode_into(&self, _: &mut [u8]) -> Result<(), CodecError> {
        panic!("layout must not invoke value encoding")
    }
    fn decode(_: &[u8]) -> Result<Self, DecodeFailure<()>> {
        panic!("unrepresentable width must not invoke a child decoder")
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        panic!("layout must not invoke hashing")
    }
}

#[test]
fn should_accept_empty_lists_but_refuse_nonempty_scopes_when_fixed_width_is_unrepresentable() {
    assert!(TooWide::decode_fixed_sequence(&[]).unwrap().is_empty());
    assert_eq!(
        TooWide::decode_fixed_sequence(&[1]).err().unwrap().kind,
        CodecError::ScopeUndivided
    );
    assert!(List::<TooWide, 0>::decode(&[])
        .unwrap()
        .as_slice()
        .is_empty());
    assert!(ProgressiveList::<TooWide>::decode(&[])
        .unwrap()
        .as_slice()
        .is_empty());
    assert!(BoundedProgressiveList::<TooWide, 0>::decode(&[])
        .unwrap()
        .as_slice()
        .is_empty());
    assert_eq!(
        List::<TooWide, 1>::decode(&[1]).err().unwrap().kind,
        CodecError::ScopeUndivided
    );
    assert_eq!(
        Vector::<TooWide, 1>::decode(&[]).err().unwrap().kind,
        CodecError::InvalidLength
    );
}
