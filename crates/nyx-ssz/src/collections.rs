//! Owned, length-checked storage for SSZ collections.
//!
//! These types enforce element counts, not element validity or wire layout.
//! With `Ssz` elements, these storage types implement the `codec::Ssz` trait.
//!
//! ```
//! use nyx_ssz::collections::{list, vector, List, Vector};
//! let pair: Vector<u64, 2> = vector(vec![10, 20]).unwrap();
//! let values: List<_, 4> = list(vec![pair]).unwrap();
//! assert_eq!(values.as_slice()[0].as_slice(), &[10, 20]);
//! ```
//!
//! Fields are private so safe callers cannot resize a validated collection.
//!
//! ```compile_fail
//! use nyx_ssz::collections::Vector;
//! let invalid = Vector::<u8, 2> { values: vec![1] };
//! ```

/// The element count violates a collection declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LengthErrorKind {
    EmptyVector,
    InvalidLength,
    OverLimit,
}

/// A rejected declaration/value and its original allocation.
///
/// Failure never drops elements inside a constructor; ownership returns here.
#[derive(Debug)]
pub struct LengthError<T> {
    pub kind: LengthErrorKind,
    pub values: Vec<T>,
}

/// An owned sequence of exactly `N > 0` elements.
pub struct Vector<T, const N: usize> {
    values: Vec<T>,
    // Preserve the const parameter in generic extraction without runtime storage.
    _bound: [(); N],
}

impl<T, const N: usize> Vector<T, N> {
    /// Borrow all elements without changing the length or allocation.
    pub fn as_slice(&self) -> &[T] {
        &self.values
    }
}

/// An owned sequence of at most `MAX` elements, including zero capacity.
pub struct List<T, const MAX: usize> {
    values: Vec<T>,
    // Preserve the const parameter in generic extraction without runtime storage.
    _bound: [(); MAX],
}

impl<T, const MAX: usize> List<T, MAX> {
    /// Borrow all elements without changing the length or allocation.
    pub fn as_slice(&self) -> &[T] {
        &self.values
    }
}

impl<T: std::fmt::Debug, const N: usize> std::fmt::Debug for Vector<T, N> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Vector")
            .field("values", &self.values)
            .finish()
    }
}

impl<T: std::fmt::Debug, const MAX: usize> std::fmt::Debug for List<T, MAX> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("List")
            .field("values", &self.values)
            .finish()
    }
}

/// Validate an exact element count, preserving the input on either outcome.
pub fn vector<T, const N: usize>(values: Vec<T>) -> Result<Vector<T, N>, LengthError<T>> {
    let output = Vector {
        values,
        _bound: [(); N],
    };
    let kind = if N == 0 {
        Some(LengthErrorKind::EmptyVector)
    } else if output.as_slice().len() != N {
        Some(LengthErrorKind::InvalidLength)
    } else {
        None
    };
    match kind {
        Some(kind) => Err(LengthError {
            kind,
            values: output.values,
        }),
        None => Ok(output),
    }
}

/// Validate an upper bound, preserving the input on either outcome.
pub fn list<T, const MAX: usize>(values: Vec<T>) -> Result<List<T, MAX>, LengthError<T>> {
    let output = List {
        values,
        _bound: [(); MAX],
    };
    if output.as_slice().len() > MAX {
        return Err(LengthError {
            kind: LengthErrorKind::OverLimit,
            values: output.values,
        });
    }
    Ok(output)
}

/// An owned Progressive sequence with an explicit maximum element count.
///
/// Zero and `usize::MAX` are real bounds, never unbounded sentinels.
pub struct BoundedProgressiveList<T, const MAX: usize> {
    values: Vec<T>,
    _bound: [(); MAX],
}

impl<T, const MAX: usize> BoundedProgressiveList<T, MAX> {
    /// Borrow all elements without changing the length or allocation.
    pub fn as_slice(&self) -> &[T] {
        &self.values
    }
}

impl<T: std::fmt::Debug, const MAX: usize> std::fmt::Debug for BoundedProgressiveList<T, MAX> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("BoundedProgressiveList")
            .field("values", &self.values)
            .finish()
    }
}

/// Validate a Progressive bound, preserving every owner and the allocation.
pub fn bounded_progressive_list<T, const MAX: usize>(
    values: Vec<T>,
) -> Result<BoundedProgressiveList<T, MAX>, LengthError<T>> {
    let output = BoundedProgressiveList {
        values,
        _bound: [(); MAX],
    };
    if output.as_slice().len() > MAX {
        return Err(LengthError {
            kind: LengthErrorKind::OverLimit,
            values: output.values,
        });
    }
    Ok(output)
}

/// An owned Progressive sequence without a declared maximum length.
///
/// Construction preserves the input allocation; element validity is checked by
/// the codec. Optional context-policy bounds are not part of this declaration.
pub struct ProgressiveList<T> {
    values: Vec<T>,
}

impl<T> ProgressiveList<T> {
    /// Borrow all elements without changing the length or allocation.
    pub fn as_slice(&self) -> &[T] {
        &self.values
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for ProgressiveList<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProgressiveList")
            .field("values", &self.values)
            .finish()
    }
}

/// Retain a complete Progressive sequence without imposing a context bound.
pub fn progressive_list<T>(values: Vec<T>) -> ProgressiveList<T> {
    ProgressiveList { values }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{codec::Ssz, error::CodecError};

    #[test]
    fn bounded_progressive_private_states_follow_reference_root_and_encode_rules() {
        let value = BoundedProgressiveList::<_, 0> {
            values: vec![true],
            _bound: [],
        };
        assert_eq!(value.encode(), Err(CodecError::OverLimit));
        assert_eq!(
            value.hash_tree_root(),
            progressive_list(vec![true]).hash_tree_root()
        );
        let child = vector::<_, 1>(vec![7_u8]).unwrap();
        let value = BoundedProgressiveList::<_, 0> {
            values: vec![child],
            _bound: [],
        };
        assert_eq!(value.encode(), Err(CodecError::OverLimit));
        assert!(value.hash_tree_root().is_ok());
    }
}
