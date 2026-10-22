//! Mixed fixed/variable SSZ wire assembly, independent of child value codecs.
//!
//! Each slot pairs its inline flag with already encoded bytes. This matches the
//! reference's paired slots without accepting unequal flag/part inventories.
//! The caller validates its declaration and encodes each child before assembly.

use crate::{collection_wire::append, error::CodecError, scalar};

fn advance_size(
    leading: usize,
    body: usize,
    fixed: bool,
    length: usize,
) -> Result<(usize, usize), CodecError> {
    let next_leading = leading as u128 + if fixed { length as u128 } else { 4 };
    let next_body = body as u128 + if fixed { 0 } else { length as u128 };
    if next_leading + next_body >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    Ok((next_leading as usize, next_body as usize))
}

fn leading_and_body(slots: &[(bool, Vec<u8>)]) -> Result<(usize, usize), CodecError> {
    let mut leading = 0;
    let mut body = 0;
    let mut index = 0;
    while index < slots.len() {
        (leading, body) = advance_size(leading, body, slots[index].0, slots[index].1.len())?;
        index += 1;
    }
    Ok((leading, body))
}

/// Assemble encoded fields, using true for inline bytes and false for offset slots.
///
/// Variable bodies follow the complete mixed header in field order. Empty bodies
/// may share offsets. Total encoded size must fit the reference's four-byte
/// envelope. No containing-type or child-value validity is assumed or checked.
/// Empty slot lists and zero-byte inline parts follow the internal layout rule.
pub fn assemble(slots: &[(bool, Vec<u8>)]) -> Result<Vec<u8>, CodecError> {
    let (leading, _) = leading_and_body(slots)?;
    let mut offset = leading;
    let mut output = Vec::new();
    let mut index = 0;
    while index < slots.len() {
        if slots[index].0 {
            append(&mut output, &slots[index].1);
        } else {
            append(&mut output, &scalar::encode_u32(offset as u32));
            offset += slots[index].1.len();
        }
        index += 1;
    }
    let mut index = 0;
    while index < slots.len() {
        if !slots[index].0 {
            append(&mut output, &slots[index].1);
        }
        index += 1;
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_guard_four_byte_budgets_when_native_lengths_cannot_be_allocated() {
        assert_eq!(
            advance_size(1, 0, true, usize::MAX),
            Err(CodecError::SizeOverflow)
        );
        assert_eq!(
            advance_size(0, 0, false, usize::MAX),
            Err(CodecError::SizeOverflow)
        );
        assert_eq!(
            advance_size(0, 0, true, 4_294_967_295),
            Ok((4_294_967_295, 0))
        );
        assert_eq!(
            advance_size(4_294_967_295, 0, false, 0),
            Err(CodecError::SizeOverflow)
        );
        assert_eq!(
            advance_size(4_294_967_291, 0, false, 0),
            Ok((4_294_967_295, 0))
        );
        assert_eq!(
            advance_size(usize::MAX, usize::MAX, false, usize::MAX),
            Err(CodecError::SizeOverflow)
        );
    }
}
