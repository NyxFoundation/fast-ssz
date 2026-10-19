use nyx_ssz::collections::{list, vector, LengthErrorKind, List, Vector};
use std::{cell::Cell, rc::Rc};

#[test]
fn should_accept_exact_vector_lengths_without_copying_the_allocation() {
    let input = vec![10u16, 20, 30];
    let pointer = input.as_ptr();
    let value: Vector<_, 3> = vector(input).unwrap();
    assert_eq!(value.as_slice(), &[10, 20, 30]);
    assert_eq!(value.as_slice().as_ptr(), pointer);
}

#[test]
fn should_return_the_original_vector_when_its_length_is_wrong() {
    for input in [vec![1u8], vec![1, 2, 3]] {
        let pointer = input.as_ptr();
        let error = vector::<_, 2>(input).unwrap_err();
        assert_eq!(error.kind, LengthErrorKind::InvalidLength);
        assert_eq!(error.values.as_ptr(), pointer);
        assert!(matches!(error.values.as_slice(), [1] | [1, 2, 3]));
    }
}

#[test]
fn should_reject_zero_vector_declarations_before_checking_the_value_length() {
    for input in [Vec::<u8>::new(), vec![1]] {
        let error = vector::<_, 0>(input).unwrap_err();
        assert_eq!(error.kind, LengthErrorKind::EmptyVector);
    }
}

#[test]
fn should_accept_lists_up_to_their_capacity_without_copying() {
    for input in [vec![], vec![1u64], vec![1, 2]] {
        let expected = input.clone();
        let pointer = input.as_ptr();
        let value: List<_, 2> = list(input).unwrap();
        assert_eq!(value.as_slice(), expected);
        assert_eq!(value.as_slice().as_ptr(), pointer);
    }
    assert!(list::<u64, 0>(vec![]).unwrap().as_slice().is_empty());
    assert_eq!(list::<_, { usize::MAX }>(vec![9]).unwrap().as_slice(), &[9]);
}

#[test]
fn should_return_every_element_when_a_list_exceeds_its_capacity() {
    let error = list::<_, 0>(vec![11, 22]).unwrap_err();
    assert_eq!(error.kind, LengthErrorKind::OverLimit);
    assert_eq!(error.values, vec![11, 22]);
}

#[test]
fn should_support_nested_noncopy_elements_without_requiring_a_codec() {
    let value = vector::<_, 2>(vec![vec![1u8, 2], vec![3]]).unwrap();
    let outer = list::<_, 2>(vec![value]).unwrap();
    assert_eq!(outer.as_slice()[0].as_slice(), &[vec![1, 2], vec![3]]);
}

#[test]
fn should_debug_only_stored_elements_regardless_of_the_declared_capacity() {
    let small = list::<_, 2>(vec![1u8]).unwrap();
    assert_eq!(format!("{small:?}"), "List { values: [1] }");
    let huge = list::<_, { usize::MAX }>(vec![2u8]).unwrap();
    assert_eq!(format!("{huge:?}"), "List { values: [2] }");
    let exact = vector::<_, 1>(vec![3u8]).unwrap();
    assert_eq!(format!("{exact:?}"), "Vector { values: [3] }");
    assert_eq!(std::mem::size_of_val(&huge), std::mem::size_of::<Vec<u8>>());
    assert_eq!(
        std::mem::size_of_val(&exact),
        std::mem::size_of::<Vec<u8>>()
    );
}

#[derive(Debug)]
struct Tracked(Rc<Cell<usize>>);

impl Drop for Tracked {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

#[test]
fn should_not_drop_elements_inside_successful_or_rejected_constructors() {
    let drops = Rc::new(Cell::new(0));
    let rejected = list::<_, 0>(vec![Tracked(Rc::clone(&drops))]).unwrap_err();
    assert_eq!(drops.get(), 0);
    drop(rejected);
    assert_eq!(drops.get(), 1);
    let accepted = vector::<_, 1>(vec![Tracked(Rc::clone(&drops))]).unwrap();
    assert_eq!(drops.get(), 1);
    drop(accepted);
    assert_eq!(drops.get(), 2);
}

#[test]
fn should_accept_machine_maximum_element_counts_for_zero_sized_elements() {
    let input = vec![(); usize::MAX];
    let value = vector::<_, { usize::MAX }>(input).unwrap();
    assert_eq!(value.as_slice().len(), usize::MAX);
}

#[test]
fn should_handle_impossible_machine_size_vector_lengths_without_arithmetic() {
    let error = vector::<_, { usize::MAX }>(vec![0u8]).unwrap_err();
    assert_eq!(error.kind, LengthErrorKind::InvalidLength);
    assert_eq!(error.values, vec![0]);
}
