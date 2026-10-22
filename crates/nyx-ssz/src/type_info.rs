//! Immutable declarations of the complete pinned SSZ type universe.
//!
//! Declarations are data, including malformed ones. Descriptor support does not
//! supply value codecs for every family. External cyclic static graphs have no
//! finite descriptor view and remain outside the codec proof contract.

use crate::error::CodecError;

#[cfg(test)]
mod tests;

/// A static SSZ declaration, independent of a particular value or encoding.
///
/// Integer widths are in bytes; bitfield lengths are in bits. Separate arrays
/// preserve malformed name/type/selector counts. Construction does not imply
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
    Container(&'static [&'static str], &'static [&'static TypeDescriptor]),
    ProgressiveContainer(
        &'static [bool],
        &'static [&'static str],
        &'static [&'static TypeDescriptor],
    ),
    CompatibleUnion(&'static [usize], &'static [&'static TypeDescriptor]),
}

pub(crate) const fn fixed_size(declaration: &TypeDescriptor) -> Result<Option<usize>, CodecError> {
    match declaration {
        TypeDescriptor::Boolean => Ok(Some(1)),
        TypeDescriptor::Uint(width) | TypeDescriptor::ByteVector(width) => Ok(Some(*width)),
        TypeDescriptor::BitVector(bits) => Ok(Some(*bits / 8 + if *bits % 8 == 0 { 0 } else { 1 })),
        TypeDescriptor::Vector(element, count) => vector_fixed_size(element, *count),
        TypeDescriptor::Container(_, fields)
        | TypeDescriptor::ProgressiveContainer(_, _, fields) => fields_fixed_size(fields),
        _ => Ok(None),
    }
}

const fn vector_fixed_size(
    element: &TypeDescriptor,
    count: usize,
) -> Result<Option<usize>, CodecError> {
    match fixed_size(element) {
        Ok(None) => Ok(None),
        Ok(Some(width)) => match width.checked_mul(count) {
            Some(total) => Ok(Some(total)),
            None => Err(CodecError::SizeOverflow),
        },
        Err(error) => {
            // Zero cancels even an unrepresentable fixed child, but not a variable child.
            if count == 0 {
                Ok(Some(0))
            } else {
                Err(error)
            }
        }
    }
}

const fn fields_fixed_size(fields: &[&TypeDescriptor]) -> Result<Option<usize>, CodecError> {
    let mut total = Some(0usize);
    let mut index = 0;
    while index < fields.len() {
        match fixed_size(fields[index]) {
            Ok(None) => return Ok(None),
            Ok(Some(width)) => {
                if let Some(previous) = total {
                    total = previous.checked_add(width);
                }
            }
            // Do not return early: a later variable field cancels fixed overflow.
            Err(_) => total = None,
        }
        index += 1;
    }
    match total {
        Some(width) => Ok(Some(width)),
        None => Err(CodecError::SizeOverflow),
    }
}

pub(crate) const fn is_basic(declaration: &TypeDescriptor) -> bool {
    matches!(
        declaration,
        TypeDescriptor::Boolean | TypeDescriptor::Uint(_)
    )
}

pub(crate) const fn is_compatible(left: &TypeDescriptor, right: &TypeDescriptor) -> bool {
    // The reference short-circuits equality even for malformed declarations.
    if declaration_equal(left, right) {
        return true;
    }
    match (byte_shape(left), byte_shape(right)) {
        (Some((a, n)), Some((b, m))) => return a == b && n == m,
        (None, None) => (),
        _ => return false,
    }
    match (left, right) {
        (TypeDescriptor::Boolean, TypeDescriptor::Boolean) => true,
        (TypeDescriptor::Uint(a), TypeDescriptor::Uint(b))
        | (TypeDescriptor::BitVector(a), TypeDescriptor::BitVector(b))
        | (TypeDescriptor::BitList(a), TypeDescriptor::BitList(b)) => *a == *b,
        (TypeDescriptor::ProgressiveBitList(_), TypeDescriptor::ProgressiveBitList(_)) => true,
        (TypeDescriptor::Vector(a, n), TypeDescriptor::Vector(b, m))
        | (TypeDescriptor::List(a, n), TypeDescriptor::List(b, m)) => {
            *n == *m && is_compatible(a, b)
        }
        (TypeDescriptor::ProgressiveList(a, _), TypeDescriptor::ProgressiveList(b, _)) => {
            is_compatible(a, b)
        }
        (TypeDescriptor::Container(names, fields), TypeDescriptor::Container(others, types)) => {
            names_equal(names, others) && fields_compatible(fields, types)
        }
        (
            TypeDescriptor::ProgressiveContainer(active, names, fields),
            TypeDescriptor::ProgressiveContainer(mask, others, types),
        ) => layouts_agree((active, names, fields), (mask, others, types)),
        (
            TypeDescriptor::CompatibleUnion(_, options),
            TypeDescriptor::CompatibleUnion(_, types),
        ) => union_options_agree(options, types),
        _ => false,
    }
}

// true denotes an ordinary vector, false an ordinary list; Progressive bytes
// have a different tree and intentionally have no byte-array alias.
const fn byte_shape(declaration: &TypeDescriptor) -> Option<(bool, usize)> {
    match declaration {
        TypeDescriptor::ByteVector(count) => Some((true, *count)),
        TypeDescriptor::ByteList(count) => Some((false, *count)),
        TypeDescriptor::Vector(TypeDescriptor::Uint(1), count) => Some((true, *count)),
        TypeDescriptor::List(TypeDescriptor::Uint(1), count) => Some((false, *count)),
        _ => None,
    }
}

const fn fields_compatible(left: &[&TypeDescriptor], right: &[&TypeDescriptor]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if !is_compatible(left[index], right[index]) {
            return false;
        }
        index += 1;
    }
    true
}

const fn union_options_agree(left: &[&TypeDescriptor], right: &[&TypeDescriptor]) -> bool {
    let mut index = 0;
    while index < left.len() {
        let mut other = 0;
        while other < right.len() {
            if !is_compatible(left[index], right[other]) {
                return false;
            }
            other += 1;
        }
        index += 1;
    }
    true
}

// The three arrays are independent: placement zips occupied positions with names,
// not with field types. Missing types fail only when a shared position needs them.
type Layout<'a> = (&'a [bool], &'a [&'a str], &'a [&'a TypeDescriptor]);

const fn layouts_agree(left: Layout<'_>, right: Layout<'_>) -> bool {
    let mut position = 0;
    let mut ordinal = 0;
    while position < left.0.len() && ordinal < left.1.len() {
        if left.0[position] {
            if !layout_field_agrees(position, ordinal, left, right) {
                return false;
            }
            ordinal += 1;
        }
        position += 1;
    }
    true
}

const fn layout_field_agrees(
    position: usize,
    ordinal: usize,
    left: Layout<'_>,
    right: Layout<'_>,
) -> bool {
    let mut other_position = 0;
    let mut other_ordinal = 0;
    while other_position < right.0.len() && other_ordinal < right.1.len() {
        if right.0[other_position] {
            if !layout_pair_agrees(
                position,
                ordinal,
                left,
                other_position,
                other_ordinal,
                right,
            ) {
                return false;
            }
            other_ordinal += 1;
        }
        other_position += 1;
    }
    true
}

const fn layout_pair_agrees(
    position: usize,
    ordinal: usize,
    left: Layout<'_>,
    other_position: usize,
    other_ordinal: usize,
    right: Layout<'_>,
) -> bool {
    let same_name = name_equal(left.1[ordinal], right.1[other_ordinal]);
    if position != other_position {
        return !same_name;
    }
    same_name
        && ordinal < left.2.len()
        && other_ordinal < right.2.len()
        && is_compatible(left.2[ordinal], right.2[other_ordinal])
}

const fn declaration_equal(left: &TypeDescriptor, right: &TypeDescriptor) -> bool {
    match (left, right) {
        (TypeDescriptor::Boolean, TypeDescriptor::Boolean) => true,
        (TypeDescriptor::Uint(a), TypeDescriptor::Uint(b))
        | (TypeDescriptor::ByteVector(a), TypeDescriptor::ByteVector(b))
        | (TypeDescriptor::ByteList(a), TypeDescriptor::ByteList(b))
        | (TypeDescriptor::BitVector(a), TypeDescriptor::BitVector(b))
        | (TypeDescriptor::BitList(a), TypeDescriptor::BitList(b)) => *a == *b,
        (TypeDescriptor::ProgressiveBitList(a), TypeDescriptor::ProgressiveBitList(b)) => {
            bounds_equal(*a, *b)
        }
        (TypeDescriptor::Vector(a, n), TypeDescriptor::Vector(b, m))
        | (TypeDescriptor::List(a, n), TypeDescriptor::List(b, m)) => {
            *n == *m && declaration_equal(a, b)
        }
        (TypeDescriptor::ProgressiveList(a, n), TypeDescriptor::ProgressiveList(b, m)) => {
            bounds_equal(*n, *m) && declaration_equal(a, b)
        }
        (TypeDescriptor::Container(names, fields), TypeDescriptor::Container(others, types)) => {
            names_equal(names, others) && fields_equal(fields, types)
        }
        (
            TypeDescriptor::ProgressiveContainer(active, names, fields),
            TypeDescriptor::ProgressiveContainer(mask, others, types),
        ) => masks_equal(active, mask) && names_equal(names, others) && fields_equal(fields, types),
        (
            TypeDescriptor::CompatibleUnion(selectors, options),
            TypeDescriptor::CompatibleUnion(others, types),
        ) => selectors_equal(selectors, others) && fields_equal(options, types),
        _ => false,
    }
}

const fn bounds_equal(left: Option<usize>, right: Option<usize>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

const fn fields_equal(left: &[&TypeDescriptor], right: &[&TypeDescriptor]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if !declaration_equal(left[index], right[index]) {
            return false;
        }
        index += 1;
    }
    true
}

const fn masks_equal(left: &[bool], right: &[bool]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    true
}

const fn selectors_equal(left: &[usize], right: &[usize]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    true
}

const fn names_equal(left: &[&str], right: &[&str]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if !name_equal(left[index], right[index]) {
            return false;
        }
        index += 1;
    }
    true
}

const fn name_equal(left: &str, right: &str) -> bool {
    let left = left.as_bytes();
    let right = right.as_bytes();
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    true
}

pub(crate) const fn validate(declaration: &TypeDescriptor) -> Result<(), CodecError> {
    match declaration {
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
        TypeDescriptor::ByteVector(count) | TypeDescriptor::BitVector(count) => {
            if *count == 0 {
                Err(CodecError::EmptyVector)
            } else {
                Ok(())
            }
        }
        TypeDescriptor::List(element, _) | TypeDescriptor::ProgressiveList(element, _) => {
            validate(element)
        }
        TypeDescriptor::Container(names, fields) => validate_container(names, fields),
        TypeDescriptor::ProgressiveContainer(active, names, fields) => {
            validate_layout(active, names, fields)
        }
        TypeDescriptor::CompatibleUnion(selectors, options) => validate_union(selectors, options),
        _ => Ok(()),
    }
}

const fn validate_container(names: &[&str], fields: &[&TypeDescriptor]) -> Result<(), CodecError> {
    if fields.is_empty() {
        return Err(CodecError::EmptyContainer);
    }
    if names.len() != fields.len() {
        return Err(CodecError::LayoutFieldCount);
    }
    if duplicate_name(names) {
        return Err(CodecError::BadDeclaration);
    }
    validate_fields(fields)
}

const fn validate_layout(
    active: &[bool],
    names: &[&str],
    fields: &[&TypeDescriptor],
) -> Result<(), CodecError> {
    if active.is_empty() {
        return Err(CodecError::LayoutWidth);
    }
    if !active[active.len() - 1] {
        return Err(CodecError::LayoutTrailingGap);
    }
    if active.len() > 256 {
        return Err(CodecError::LayoutTooWide);
    }
    if fields.is_empty() {
        return Err(CodecError::EmptyContainer);
    }
    if active_count(active) != fields.len() {
        return Err(CodecError::LayoutFieldCount);
    }
    validate_container(names, fields)
}

const fn active_count(active: &[bool]) -> usize {
    let mut count = 0;
    let mut index = 0;
    while index < active.len() {
        if active[index] {
            count += 1;
        }
        index += 1;
    }
    count
}

const fn duplicate_name(names: &[&str]) -> bool {
    let mut index = 0;
    while index < names.len() {
        let mut other = index + 1;
        while other < names.len() {
            if name_equal(names[index], names[other]) {
                return true;
            }
            other += 1;
        }
        index += 1;
    }
    false
}

const fn duplicate_selector(selectors: &[usize]) -> bool {
    let mut index = 0;
    while index < selectors.len() {
        let mut other = index + 1;
        while other < selectors.len() {
            if selectors[index] == selectors[other] {
                return true;
            }
            other += 1;
        }
        index += 1;
    }
    false
}

const fn validate_fields(fields: &[&TypeDescriptor]) -> Result<(), CodecError> {
    let mut index = 0;
    while index < fields.len() {
        if let Err(error) = validate(fields[index]) {
            return Err(error);
        }
        index += 1;
    }
    Ok(())
}

const fn validate_union(
    selectors: &[usize],
    options: &[&TypeDescriptor],
) -> Result<(), CodecError> {
    if selectors.is_empty() || options.is_empty() {
        return Err(CodecError::EmptyUnion);
    }
    if selectors.len() != options.len() {
        return Err(CodecError::BadDeclaration);
    }
    if duplicate_selector(selectors) {
        return Err(CodecError::UnionSelectorRepeated);
    }
    let mut index = 0;
    while index < selectors.len() {
        if selectors[index] < 1 || selectors[index] > 127 {
            return Err(CodecError::UnionSelectorRange);
        }
        index += 1;
    }
    match validate_fields(options) {
        Err(error) => Err(error),
        Ok(()) => validate_options_compatible(options),
    }
}

const fn validate_options_compatible(options: &[&TypeDescriptor]) -> Result<(), CodecError> {
    let mut index = 0;
    while index < options.len() {
        let mut other = index + 1;
        while other < options.len() {
            if !is_compatible(options[index], options[other]) {
                return Err(CodecError::UnionIncompatible);
            }
            other += 1;
        }
        index += 1;
    }
    Ok(())
}
