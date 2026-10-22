use super::*;
use crate::{container::container_view, error::CodecError, sequence};

pub(super) fn from_bytes(shape: &D, bytes: &[u8]) -> Result<Tree, AccessError> {
    match shape {
        D::Boolean | D::Uint(_) | D::ByteVector(_) => {
            packed(bytes, Some(bytes.len().div_ceil(32)), None)
        }
        D::ByteList(limit) => packed(
            bytes,
            Some(limit.div_ceil(32)),
            Some(length_word(bytes.len() as u128)),
        ),
        D::BitVector(count) => packed(bytes, Some(count.div_ceil(256)), None),
        D::BitList(limit) => delimited(bytes, Some(limit.div_ceil(256))),
        D::ProgressiveBitList(_) => delimited(bytes, None),
        D::Vector(child, count) => sequence_tree(child, bytes, Some(*count), false, false),
        D::List(child, limit) => sequence_tree(child, bytes, Some(*limit), true, false),
        D::ProgressiveList(child, _) => sequence_tree(child, bytes, None, true, true),
        D::Container(_, fields) => fields_tree(fields, bytes, None),
        D::ProgressiveContainer(active, _, fields) => fields_tree(fields, bytes, Some(active)),
        D::CompatibleUnion(selectors, options) => {
            let (&selector, body) = bytes.split_first().ok_or(CodecError::NoSelector)?;
            let slot = selectors
                .iter()
                .position(|&s| s == selector as usize)
                .ok_or(CodecError::UnknownSelector)?;
            Ok(Tree::branch(
                from_bytes(options[slot], body)?,
                Tree::Leaf(length_word(selector as u128)),
            ))
        }
    }
}

fn delimited(bytes: &[u8], capacity: Option<usize>) -> Result<Tree, AccessError> {
    let (&last, prefix) = bytes.split_last().ok_or(CodecError::EmptyEncoding)?;
    if last == 0 {
        return Err(CodecError::NoDelimiter.into());
    }
    let highest = 7 - last.leading_zeros();
    let count = prefix.len() as u128 * 8 + highest as u128;
    let mut data = prefix.to_vec();
    if highest != 0 {
        data.push(last & !(1 << highest));
    }
    packed(&data, capacity, Some(length_word(count)))
}

fn sequence_tree(
    child: &D,
    bytes: &[u8],
    capacity: Option<usize>,
    mixed: bool,
    progressive_tree: bool,
) -> Result<Tree, AccessError> {
    let fixed = type_info::fixed_size(child);
    let view = if bytes.is_empty() && mixed {
        sequence::fixed_list_view(bytes, 0, capacity)?
    } else {
        match (fixed, mixed) {
            (Ok(Some(width)), false) => {
                sequence::fixed_vector_view(bytes, width, capacity.unwrap_or(0))?
            }
            (Ok(Some(width)), true) => sequence::fixed_list_view(bytes, width, capacity)?,
            (Ok(None), false) => sequence::variable_vector_view(bytes, capacity.unwrap_or(0))?,
            (Ok(None), true) => sequence::variable_list_view(bytes, capacity)?,
            (Err(error), _) => return Err(error.into()),
        }
    };
    if type_info::is_basic(child) {
        let width = type_info::fixed_size(child)?.ok_or(CodecError::InvalidIntegerWidth)?;
        return packed(
            bytes,
            capacity.map(|n| n.div_ceil(32 / width)),
            mixed.then(|| length_word(view.len() as u128)),
        );
    }
    let mut leaves = Vec::with_capacity(view.len());
    for index in 0..view.len() {
        leaves.push(from_bytes(
            child,
            view.get(index).ok_or(CodecError::InvalidLength)?,
        )?);
    }
    let contents = if progressive_tree {
        progressive(&leaves, 0)
    } else {
        bounded(&leaves, capacity.unwrap_or(0))?
    };
    Ok(if mixed {
        Tree::branch(contents, Tree::Leaf(length_word(view.len() as u128)))
    } else {
        contents
    })
}

fn fields_tree(fields: &[&D], bytes: &[u8], active: Option<&[bool]>) -> Result<Tree, AccessError> {
    let widths: Vec<_> = fields
        .iter()
        .map(|shape| type_info::fixed_size(shape))
        .collect();
    let view = container_view(bytes, &widths)?;
    let mut leaves = Vec::with_capacity(active.map_or(fields.len(), <[bool]>::len));
    let mut mask = [0; 32];
    let mut ordinal = 0;
    for position in 0..active.map_or(fields.len(), <[bool]>::len) {
        if active.is_none_or(|bits| bits[position]) {
            leaves.push(from_bytes(
                fields[ordinal],
                view.get(ordinal).ok_or(CodecError::InvalidLength)?,
            )?);
            if active.is_some() {
                mask[position / 8] |= 1 << (position % 8);
            }
            ordinal += 1;
        } else {
            leaves.push(Tree::Leaf([0; 32]));
        }
    }
    if active.is_some() {
        Ok(Tree::branch(progressive(&leaves, 0), Tree::Leaf(mask)))
    } else {
        bounded(&leaves, fields.len())
    }
}
