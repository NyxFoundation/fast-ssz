//! Immutable declarations of the SSZ types implemented by the typed codec API.

use crate::error::CodecError;

/// A static SSZ declaration, independent of a particular value or encoding.
///
/// Integer widths are in bytes. Construction does not imply declaration
/// validity; `codec::validate_type` checks the specification's legal widths.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeDescriptor {
    Boolean,
    Uint(usize),
}

pub(crate) const fn fixed_size(declaration: &TypeDescriptor) -> Result<Option<usize>, CodecError> {
    match declaration {
        TypeDescriptor::Boolean => Ok(Some(1)),
        TypeDescriptor::Uint(width) => Ok(Some(*width)),
    }
}

pub(crate) const fn is_basic(declaration: &TypeDescriptor) -> bool {
    match declaration {
        TypeDescriptor::Boolean | TypeDescriptor::Uint(_) => true,
    }
}

pub(crate) const fn is_compatible(left: &TypeDescriptor, right: &TypeDescriptor) -> bool {
    match left {
        TypeDescriptor::Boolean => match right {
            TypeDescriptor::Boolean => true,
            TypeDescriptor::Uint(_) => false,
        },
        TypeDescriptor::Uint(left_width) => match right {
            TypeDescriptor::Boolean => false,
            TypeDescriptor::Uint(right_width) => *left_width == *right_width,
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
    }
}
