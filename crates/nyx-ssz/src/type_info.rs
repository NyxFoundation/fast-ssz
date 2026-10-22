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
    ByteVector(usize),
    ByteList(usize),
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
        TypeDescriptor::Uint(width) | TypeDescriptor::ByteVector(width) => Ok(Some(*width)),
        TypeDescriptor::BitVector(count) => Ok(Some(count.div_ceil(8))),
        TypeDescriptor::ByteList(_)
        | TypeDescriptor::BitList(_)
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
    use TypeDescriptor as D;

    match left {
        D::Boolean => matches!(right, D::Boolean),
        D::Uint(width) => match right {
            D::Uint(other) => *width == *other,
            _ => false,
        },
        D::BitVector(count) => match right {
            D::BitVector(other) => *count == *other,
            _ => false,
        },
        D::BitList(limit) => match right {
            D::BitList(other) => *limit == *other,
            _ => false,
        },
        D::ProgressiveBitList(_) => matches!(right, D::ProgressiveBitList(_)),
        D::ByteVector(count) => match right {
            D::ByteVector(other) => *count == *other,
            D::Vector(child, other) => *count == *other && matches!(child, D::Uint(1)),
            _ => false,
        },
        D::ByteList(limit) => match right {
            D::ByteList(other) => *limit == *other,
            D::List(child, other) => *limit == *other && matches!(child, D::Uint(1)),
            _ => false,
        },
        D::Vector(child, count) => match right {
            D::ByteVector(other) => *count == *other && matches!(child, D::Uint(1)),
            D::Vector(other, size) => *count == *size && is_compatible(child, other),
            _ => false,
        },
        D::List(child, limit) => match right {
            D::ByteList(other) => *limit == *other && matches!(child, D::Uint(1)),
            D::List(other, size) => *limit == *size && is_compatible(child, other),
            _ => false,
        },
        D::ProgressiveList(child, _) => match right {
            D::ProgressiveList(other, _) => is_compatible(child, other),
            _ => false,
        },
    }
}

pub(crate) const fn validate(declaration: &TypeDescriptor) -> Result<(), CodecError> {
    match declaration {
        TypeDescriptor::Boolean | TypeDescriptor::ByteList(_) => Ok(()),
        TypeDescriptor::ByteVector(count) => {
            if *count == 0 {
                Err(CodecError::EmptyVector)
            } else {
                Ok(())
            }
        }
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
