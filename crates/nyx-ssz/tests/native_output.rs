//! Scripted dictionaries test runtime ordering, not certified conformance.
use std::{cell::RefCell, rc::Rc};

use nyx_ssz::{
    codec::{encode, Ssz},
    collections::progressive_list,
    collections::{list, vector},
    error::{CodecError, DecodeFailure},
    type_info::TypeDescriptor,
};

type Trace = Rc<RefCell<Vec<usize>>>;

#[derive(Debug)]
struct Script<const VARIABLE: bool> {
    result: Result<Vec<u8>, CodecError>,
    index: usize,
    trace: Trace,
}

impl<const VARIABLE: bool> Ssz for Script<VARIABLE> {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = if VARIABLE {
        &TypeDescriptor::List(&TypeDescriptor::Uint(1), 8)
    } else {
        &TypeDescriptor::Uint(1)
    };

    fn encoded_len(&self) -> Result<usize, CodecError> {
        self.trace.borrow_mut().push(self.index);
        self.result.as_ref().map(Vec::len).map_err(|error| *error)
    }
    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        match &self.result {
            Ok(bytes) => nyx_ssz::encoding::copy(output, bytes),
            Err(error) => Err(*error),
        }
    }

    fn decode(_: &[u8]) -> Result<Self, DecodeFailure<()>> {
        Err(DecodeFailure {
            kind: CodecError::InvalidLength,
            state: (),
        })
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Err(CodecError::InvalidLength)
    }
}

fn check<const VARIABLE: bool>(
    results: &[Result<Vec<u8>, CodecError>],
    expected: Result<Vec<u8>, CodecError>,
    visited: &[usize],
) {
    for family in 0..3 {
        let trace = Trace::default();
        let values = results
            .iter()
            .enumerate()
            .map(|(index, result)| Script::<VARIABLE> {
                result: result.clone(),
                index,
                trace: trace.clone(),
            })
            .collect();
        let actual = match family {
            0 => encode(&vector::<_, 3>(values).unwrap()),
            1 => encode(&list::<_, 3>(values).unwrap()),
            _ => encode(&progressive_list(values)),
        };
        assert_eq!(actual, expected);
        let trace = trace.borrow();
        if actual.is_err() {
            assert_eq!(*trace, visited);
        } else {
            assert!(!trace.is_empty());
            assert!(trace.chunks(visited.len()).all(|pass| pass == visited));
        }
    }
}

#[test]
fn deferred_native_success_does_not_hide_later_protocol_faults() {
    use CodecError::*;
    for fault in [InvalidBoolean, SizeOverflow, OverLimit, InvalidLength] {
        let results = [Err(NativeOutputOverflow), Err(fault), Err(EmptyEncoding)];
        check::<false>(&results, Err(fault), &[0, 1]);
        check::<true>(&results, Err(fault), &[0, 1]);
    }
}

#[test]
fn genuine_protocol_overflow_stops_before_later_faults() {
    use CodecError::*;
    let results = [
        Err(SizeOverflow),
        Err(InvalidBoolean),
        Err(NativeOutputOverflow),
    ];
    check::<false>(&results, Err(SizeOverflow), &[0]);
    check::<true>(&results, Err(SizeOverflow), &[0]);
}

#[test]
fn all_reference_success_with_native_marker_gets_parent_protocol_budget_error() {
    use CodecError::*;
    let results = [Ok(vec![1]), Err(NativeOutputOverflow), Ok(vec![2])];
    check::<false>(&results, Err(SizeOverflow), &[0, 1, 2]);
    check::<true>(&results, Err(SizeOverflow), &[0, 1, 2]);
    let repeated = [
        Err(NativeOutputOverflow),
        Err(NativeOutputOverflow),
        Ok(vec![]),
    ];
    check::<true>(&repeated, Err(SizeOverflow), &[0, 1, 2]);
}

#[test]
fn fully_representable_parts_retain_exact_order_and_offsets() {
    let results = [Ok(vec![1, 2]), Ok(vec![]), Ok(vec![3])];
    check::<false>(&results, Ok(vec![1, 2, 3]), &[0, 1, 2]);
    check::<true>(
        &results,
        Ok(vec![12, 0, 0, 0, 14, 0, 0, 0, 14, 0, 0, 0, 1, 2, 3]),
        &[0, 1, 2],
    );
    assert_ne!(CodecError::NativeOutputOverflow, CodecError::SizeOverflow);
    assert!(CodecError::NativeOutputOverflow
        .to_string()
        .contains("native"));
}
