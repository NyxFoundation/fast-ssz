//! Immutable declarations of the SSZ types implemented by the typed codec API.

use crate::error::CodecError;

/// A static SSZ declaration, independent of a particular value or encoding.
///
/// Integer widths are in bytes. Construction does not imply declaration
/// validity; `codec::validate_type` checks the specification's declaration rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeDescriptor {
    Boolean,
    Uint(usize),
    BitVector(usize),
    BitList(usize),
    ProgressiveBitList(Option<usize>),
    Vector(&'static TypeDescriptor, usize),
    List(&'static TypeDescriptor, usize),
    ProgressiveList(&'static TypeDescriptor, Option<usize>),
}

pub(crate) const fn fixed_size(declaration: &TypeDescriptor) -> Result<Option<usize>, CodecError> {
    match declaration {
        TypeDescriptor::Boolean => Ok(Some(1)),
        TypeDescriptor::Uint(width) => Ok(Some(*width)),
        TypeDescriptor::BitVector(count) => Ok(Some(count.div_ceil(8))),
        TypeDescriptor::BitList(_)
        | TypeDescriptor::ProgressiveBitList(_)
        | TypeDescriptor::List(_, _)
        | TypeDescriptor::ProgressiveList(_, _) => Ok(None),
        TypeDescriptor::Vector(element, count) => match fixed_size(element) {
            Ok(None) => Ok(None),
            Ok(Some(width)) => match width.checked_mul(*count) {
                Some(total) => Ok(Some(total)),
                None => Err(CodecError::SizeOverflow),
            },
            Err(error) => {
                // A zero count cancels even an unrepresentable fixed child width.
                if *count == 0 {
                    Ok(Some(0))
                } else {
                    Err(error)
                }
            }
        },
    }
}

pub(crate) const fn is_basic(declaration: &TypeDescriptor) -> bool {
    matches!(
        declaration,
        TypeDescriptor::Boolean | TypeDescriptor::Uint(_)
    )
}

pub(crate) const fn is_compatible(left: &TypeDescriptor, right: &TypeDescriptor) -> bool {
    match left {
        TypeDescriptor::Boolean => matches!(right, TypeDescriptor::Boolean),
        TypeDescriptor::Uint(left_width) => match right {
            TypeDescriptor::Uint(right_width) => *left_width == *right_width,
            _ => false,
        },
        TypeDescriptor::BitVector(left_count) => match right {
            TypeDescriptor::BitVector(right_count) => *left_count == *right_count,
            _ => false,
        },
        TypeDescriptor::BitList(left_limit) => match right {
            TypeDescriptor::BitList(right_limit) => *left_limit == *right_limit,
            _ => false,
        },
        TypeDescriptor::ProgressiveBitList(_) => {
            matches!(right, TypeDescriptor::ProgressiveBitList(_))
        }
        TypeDescriptor::Vector(left_element, left_count) => match right {
            TypeDescriptor::Vector(right_element, right_count) => {
                *left_count == *right_count && is_compatible(left_element, right_element)
            }
            _ => false,
        },
        TypeDescriptor::List(left_element, left_limit) => match right {
            TypeDescriptor::List(right_element, right_limit) => {
                *left_limit == *right_limit && is_compatible(left_element, right_element)
            }
            _ => false,
        },
        TypeDescriptor::ProgressiveList(left_element, _) => match right {
            TypeDescriptor::ProgressiveList(right_element, _) => {
                is_compatible(left_element, right_element)
            }
            _ => false,
        },
    }
}

pub(crate) const fn validate(declaration: &TypeDescriptor) -> Result<(), CodecError> {
    match declaration {
        TypeDescriptor::Boolean => Ok(()),
        TypeDescriptor::Uint(width) => match *width {
            1 | 2 | 4 | 8 | 16 | 32 => Ok(()),
            _ => Err(CodecError::InvalidIntegerWidth),
        },
        TypeDescriptor::BitVector(count) => {
            if *count == 0 {
                Err(CodecError::EmptyVector)
            } else {
                Ok(())
            }
        }
        TypeDescriptor::BitList(_) | TypeDescriptor::ProgressiveBitList(_) => Ok(()),
        TypeDescriptor::Vector(element, count) => {
            if *count == 0 {
                Err(CodecError::EmptyVector)
            } else {
                validate(element)
            }
        }
        TypeDescriptor::List(element, _) => validate(element),
        TypeDescriptor::ProgressiveList(element, _) => validate(element),
    }
}
