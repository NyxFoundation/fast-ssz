use nyx_ssz::{
    codec::{decode, decode_elements, Ssz},
    collections::{BoundedProgressiveList, List, Vector},
    error::{CodecError, DecodeFailure},
    sequence::variable_vector_view,
    type_info::TypeDescriptor,
};
use std::cell::RefCell;

thread_local! {
    static DROPS: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static CALLS: RefCell<usize> = const { RefCell::new(0) };
}

struct TracedByte(u8);
struct Cleanup(u8);

impl Drop for TracedByte {
    fn drop(&mut self) {
        DROPS.with(|log| log.borrow_mut().push(self.0));
    }
}
impl Drop for Cleanup {
    fn drop(&mut self) {
        DROPS.with(|log| log.borrow_mut().push(self.0));
    }
}

// An external codec exercises ownership; it is not implicitly certified by the library.
impl Ssz for TracedByte {
    type DecodeState = Cleanup;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Uint(1);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        Ok(vec![self.0])
    }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Ok(nyx_ssz::tree_hash::hash_tree_root_u8(self.0))
    }
    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Cleanup>> {
        CALLS.with(|count| *count.borrow_mut() += 1);
        // Deliberate refusal tests arbitrary external callback failure ownership.
        if bytes.len() != 1 || bytes[0] == 255 {
            return Err(DecodeFailure {
                kind: CodecError::InvalidLength,
                state: Cleanup(200),
            });
        }
        Ok(Self(bytes[0]))
    }
}

fn reset() {
    DROPS.with(|log| log.borrow_mut().clear());
    CALLS.with(|count| *count.borrow_mut() = 0);
}

fn drops() -> Vec<u8> {
    DROPS.with(|log| log.borrow().clone())
}
fn calls() -> usize {
    CALLS.with(|count| *count.borrow())
}

#[test]
fn should_decode_elements_in_order_when_each_body_is_valid() {
    reset();
    let bytes = [12, 0, 0, 0, 13, 0, 0, 0, 14, 0, 0, 0, 7, 8, 9];
    let view = variable_vector_view(&bytes, 3).unwrap();
    let values = decode_elements::<TracedByte>(&view).unwrap();
    assert_eq!(
        values.iter().map(|value| value.0).collect::<Vec<_>>(),
        [7, 8, 9]
    );
    assert_eq!(calls(), 3);
    assert!(drops().is_empty());
    drop(values);
    assert_eq!(drops(), [7, 8, 9]);
}

#[test]
fn should_return_prefix_and_child_state_when_a_later_body_is_invalid() {
    reset();
    let bytes = [8, 0, 0, 0, 9, 0, 0, 0, 7];
    let view = variable_vector_view(&bytes, 2).unwrap();
    let Err(failure) = decode_elements::<TracedByte>(&view) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.kind, CodecError::InvalidLength);
    assert_eq!(failure.state.values.len(), 1);
    assert_eq!(failure.state.values[0].0, 7);
    assert!(failure.state.child.is_some());
    assert_eq!(calls(), 2);
    assert!(drops().is_empty());
    drop(failure);
    let mut actual = drops();
    actual.sort();
    assert_eq!(actual, [7, 200]);
}

#[test]
fn should_stop_at_the_first_failure_without_dropping_its_state() {
    reset();
    let bytes = [8, 0, 0, 0, 8, 0, 0, 0, 7];
    let view = variable_vector_view(&bytes, 2).unwrap();
    let Err(failure) = decode_elements::<TracedByte>(&view) else {
        panic!("expected refusal")
    };
    assert!(failure.state.values.is_empty());
    assert!(failure.state.child.is_some());
    assert_eq!(calls(), 1);
    assert!(drops().is_empty());
    drop(failure);
    assert_eq!(drops(), [200]);
}

#[test]
fn should_not_invoke_element_decoders_when_the_view_is_empty() {
    reset();
    let view = variable_vector_view(&[], 0).unwrap();
    let values = decode_elements::<TracedByte>(&view).unwrap();
    assert!(values.is_empty());
    assert_eq!(calls(), 0);
    assert!(drops().is_empty());
}

#[test]
fn should_preserve_owned_prefix_and_child_state_in_typed_vector_failures() {
    reset();
    let Err(failure) = decode::<Vector<TracedByte, 2>>(&[7, 255]) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.kind, CodecError::InvalidLength);
    assert_eq!(failure.state.values.len(), 1);
    assert_eq!(failure.state.values[0].0, 7);
    assert_eq!(failure.state.child.as_ref().map(|state| state.0), Some(200));
    assert_eq!(calls(), 2);
    assert!(drops().is_empty());
    drop(failure);
    assert_eq!(drops(), [7, 200]);
}

#[test]
fn should_preserve_every_nested_owner_when_a_typed_list_child_fails() {
    reset();
    let bytes = [8, 0, 0, 0, 9, 0, 0, 0, 7, 8, 255];
    let Err(failure) = decode::<List<List<TracedByte, 2>, 2>>(&bytes) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.state.values[0].as_slice()[0].0, 7);
    let child = failure.state.child.as_ref().unwrap();
    assert_eq!(child.values[0].0, 8);
    assert_eq!(child.child.as_ref().map(|state| state.0), Some(200));
    assert_eq!(calls(), 3);
    assert!(drops().is_empty());
    drop(failure);
    let mut actual = drops();
    actual.sort();
    assert_eq!(actual, [7, 8, 200]);
}

#[test]
fn bounded_progressive_failure_retains_every_nested_owner_without_running_destructors() {
    reset();
    let bytes = [8, 0, 0, 0, 9, 0, 0, 0, 7, 8, 255];
    let Err(failure) = decode::<BoundedProgressiveList<List<TracedByte, 2>, 2>>(&bytes) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.state.values[0].as_slice()[0].0, 7);
    let child = failure.state.child.as_ref().unwrap();
    assert_eq!(child.values[0].0, 8);
    assert_eq!(child.child.as_ref().map(|state| state.0), Some(200));
    assert_eq!(calls(), 3);
    assert!(drops().is_empty());
    drop(failure);
    let mut actual = drops();
    actual.sort();
    assert_eq!(actual, [7, 8, 200]);
}

#[test]
fn bounded_progressive_capacity_refusal_invokes_no_callbacks_or_destructors() {
    reset();
    let Err(failure) = decode::<BoundedProgressiveList<TracedByte, 1>>(&[7, 255]) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.kind, CodecError::OverLimit);
    assert!(failure.state.values.is_empty());
    assert!(failure.state.child.is_none());
    assert_eq!(calls(), 0);
    assert!(drops().is_empty());
}

#[test]
fn should_return_empty_state_without_callbacks_when_typed_layout_is_invalid() {
    reset();
    let Err(failure) = decode::<Vector<TracedByte, 2>>(&[7]) else {
        panic!("expected refusal")
    };
    assert_eq!(failure.kind, CodecError::InvalidLength);
    assert!(failure.state.values.is_empty());
    assert!(failure.state.child.is_none());
    assert_eq!(calls(), 0);
    assert!(drops().is_empty());
}
