//! Type-level SSZ paths. Declared padding positions are addressable.
use crate::{
    codec::Ssz,
    error::CodecError,
    gindex,
    merkle::ProofError,
    type_info::{self, TypeDescriptor as D},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step<'a> {
    Position(usize),
    Field(&'a str),
    Length,
    ActiveFields,
    Selector,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccessError {
    Codec(CodecError),
    Proof(ProofError),
    InvalidPath,
    NoSuchPosition,
}

impl From<CodecError> for AccessError {
    fn from(error: CodecError) -> Self {
        Self::Codec(error)
    }
}
impl From<ProofError> for AccessError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}
impl std::fmt::Display for AccessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SSZ tree access request is invalid")
    }
}
impl std::error::Error for AccessError {}

/// Node selected by a path and the last element's position within that node.
/// Bits use start == stop == 0; bit_offset identifies the bit in that node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Location {
    pub generalized_index: u128,
    pub start: usize,
    pub stop: usize,
    pub bit_offset: Option<usize>,
}

pub fn resolve<T: Ssz>(steps: &[Step<'_>]) -> Result<Location, AccessError> {
    type_info::validate(T::TYPE)?;
    let mut shape = T::TYPE;
    let mut location = Location {
        generalized_index: 1,
        start: 0,
        stop: 32,
        bit_offset: None,
    };
    for (ordinal, &step) in steps.iter().enumerate() {
        let (relative, target, start, stop, bit_offset) = resolve_step(shape, step)?;
        location = Location {
            generalized_index: gindex::concat(location.generalized_index, relative)?,
            start,
            stop,
            bit_offset,
        };
        match target {
            Some(child) => shape = child,
            None if ordinal + 1 == steps.len() => (),
            None => return Err(AccessError::InvalidPath),
        }
    }
    Ok(location)
}

type Resolved = (u128, Option<&'static D>, usize, usize, Option<usize>);
fn resolve_step(shape: &'static D, step: Step<'_>) -> Result<Resolved, AccessError> {
    if let Step::Field(name) = step {
        let names = match shape {
            D::Container(names, _) | D::ProgressiveContainer(_, names, _) => names,
            _ => return Err(AccessError::InvalidPath),
        };
        let ordinal = names
            .iter()
            .position(|&field| field == name)
            .ok_or(AccessError::NoSuchPosition)?;
        return resolve_step(shape, Step::Position(ordinal));
    }
    if !matches!(step, Step::Position(_)) {
        let allowed = mixes_in(shape, step);
        return if allowed {
            Ok((3, None, 0, 32, None))
        } else {
            Err(AccessError::InvalidPath)
        };
    }
    let Step::Position(index) = step else {
        unreachable!()
    };
    match shape {
        D::Container(_, fields) => field_step(fields, index, None),
        D::ProgressiveContainer(active, _, fields) => field_step(fields, index, Some(active)),
        D::CompatibleUnion(selectors, options) => {
            let slot = selectors
                .iter()
                .position(|&s| s == index)
                .ok_or(AccessError::NoSuchPosition)?;
            Ok((2, Some(options[slot]), 0, 32, None))
        }
        _ => sequence_step(shape, index),
    }
}

fn field_step(
    fields: &'static [&'static D],
    index: usize,
    active: Option<&[bool]>,
) -> Result<Resolved, AccessError> {
    let child = *fields.get(index).ok_or(AccessError::NoSuchPosition)?;
    let relative = if let Some(active) = active {
        let position = active
            .iter()
            .enumerate()
            .filter(|(_, bit)| **bit)
            .nth(index)
            .ok_or(AccessError::NoSuchPosition)?
            .0;
        progressive_index(position)?
    } else {
        leaf_index(fields.len(), index)?
    };
    Ok((relative, Some(child), 0, item_width(child), None))
}

fn mixes_in(shape: &D, step: Step<'_>) -> bool {
    matches!(
        (shape, step),
        (
            D::List(_, _)
                | D::ByteList(_)
                | D::BitList(_)
                | D::ProgressiveList(_, _)
                | D::ProgressiveBitList(_),
            Step::Length
        ) | (D::ProgressiveContainer(_, _, _), Step::ActiveFields)
            | (D::CompatibleUnion(_, _), Step::Selector)
    )
}

type SequenceShape = (&'static D, Option<usize>, bool, bool, bool);
fn sequence_shape(shape: &'static D) -> Result<SequenceShape, AccessError> {
    Ok(match shape {
        D::Vector(child, n) => (*child, Some(*n), false, false, false),
        D::List(child, n) => (*child, Some(*n), false, false, true),
        D::ProgressiveList(child, _) => (*child, None, false, true, true),
        D::ByteVector(n) => (&D::Uint(1), Some(*n), false, false, false),
        D::ByteList(n) => (&D::Uint(1), Some(*n), false, false, true),
        D::BitVector(n) => (&D::Boolean, Some(*n), true, false, false),
        D::BitList(n) => (&D::Boolean, Some(*n), true, false, true),
        D::ProgressiveBitList(_) => (&D::Boolean, None, true, true, true),
        _ => return Err(AccessError::InvalidPath),
    })
}

fn item_width(shape: &D) -> usize {
    match shape {
        D::Boolean => 1,
        D::Uint(n) => *n,
        _ => 32,
    }
}

fn sequence_step(shape: &'static D, index: usize) -> Result<Resolved, AccessError> {
    let (child, count, bits, progressive, mixed) = sequence_shape(shape)?;
    if count.is_some_and(|n| index >= n) {
        return Err(AccessError::NoSuchPosition);
    }
    let per_chunk = if bits { 256 } else { 32 / item_width(child) };
    let chunk = index / per_chunk;
    let relative = if progressive {
        progressive_index(chunk)?
    } else {
        let leaf = leaf_index(count.unwrap_or(0).div_ceil(per_chunk), chunk)?;
        if mixed {
            gindex::concat(2, leaf)?
        } else {
            leaf
        }
    };
    let start = if bits {
        0
    } else {
        index % per_chunk * item_width(child)
    };
    Ok((
        relative,
        Some(child),
        start,
        if bits { 0 } else { start + item_width(child) },
        bits.then_some(index % 256),
    ))
}

pub(crate) fn leaf_index(capacity: usize, position: usize) -> Result<u128, AccessError> {
    let depth = if capacity <= 1 {
        0
    } else {
        usize::BITS - (capacity - 1).leading_zeros()
    };
    Ok((1u128 << depth) + position as u128)
}

fn progressive_index(position: usize) -> Result<u128, AccessError> {
    let mut remaining = position as u128;
    let mut width = 1u128;
    let mut spine = 2u128;
    while remaining >= width {
        remaining -= width;
        width = width.checked_mul(4).ok_or(ProofError::IndexOverflow)?;
        spine = gindex::child(spine, true)?;
    }
    let base = spine
        .checked_mul(2)
        .and_then(|n| n.checked_mul(width))
        .ok_or(ProofError::IndexOverflow)?;
    Ok(base
        .checked_add(remaining)
        .ok_or(ProofError::IndexOverflow)?)
}
