//! Shared layout validation for SSZ sequences and containers.

use crate::error::CodecError;

/// Compute body widths, validating offset order before each body's scope.
///
/// Repeated offsets represent empty bodies. Table/header validation and the
/// four-byte composite-size envelope remain the caller's responsibility.
/// A later unordered pair takes precedence over a final out-of-scope offset.
pub fn offset_spans(offsets: &[usize], scope: usize) -> Result<Vec<usize>, CodecError> {
    let mut spans = Vec::new();
    let mut index = 0;
    while index < offsets.len() {
        let start = offsets[index];
        let next_index = index + 1;
        if next_index < offsets.len() {
            let next = offsets[next_index];
            if next < start {
                return Err(CodecError::OffsetUnordered);
            }
            spans.push(next - start);
        } else {
            if scope < start {
                return Err(CodecError::OffsetPastScope);
            }
            spans.push(scope - start);
        }
        index = next_index;
    }
    Ok(spans)
}
