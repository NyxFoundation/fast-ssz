//! Shared layout validation for SSZ sequences and containers.

use crate::error::CodecError;

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct BodyRange {
    pub(crate) start: usize,
    pub(crate) end: usize,
}

/// Validated body ranges borrowing a single immutable SSZ encoding.
#[derive(Debug, Eq, PartialEq)]
pub struct SequenceView<'a> {
    pub(crate) input: &'a [u8],
    pub(crate) ranges: Vec<BodyRange>,
}

impl<'a> SequenceView<'a> {
    /// Return the number of encoded elements.
    #[must_use]
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn len(&self) -> usize {
        self.ranges.len()
    }

    /// Return whether the encoding has no elements.
    #[must_use]
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Borrow one element without copying its bytes, or return None out of bounds.
    #[must_use]
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn get(&self, index: usize) -> Option<&'a [u8]> {
        if index >= self.ranges.len() {
            return None;
        }
        let range = &self.ranges[index];
        Some(&self.input[range.start..range.end])
    }
}

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

/// Borrow fixed-width elements after checking the exact byte budget.
///
/// This is an internal-layout helper: zero width/count follow reference slicing
/// rules. Type declaration and element validation remain the caller's job.
pub fn fixed_vector_view(
    input: &[u8],
    width: usize,
    count: usize,
) -> Result<SequenceView<'_>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    let expected = match width.checked_mul(count) {
        Some(expected) => expected,
        None => return Err(CodecError::InvalidLength),
    };
    if input.len() != expected {
        return Err(CodecError::InvalidLength);
    }
    Ok(SequenceView {
        input,
        ranges: fixed_ranges(width, count),
    })
}

/// Infer fixed-width element counts without choosing a containing SSZ type.
///
/// Empty input has no elements even at zero width; nonempty widthless input or
/// an incomplete final element is rejected before checking the optional limit.
pub fn fixed_list_view(
    input: &[u8],
    width: usize,
    limit: Option<usize>,
) -> Result<SequenceView<'_>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    if input.is_empty() {
        return Ok(SequenceView {
            input,
            ranges: Vec::new(),
        });
    }
    if width == 0 {
        return Err(CodecError::ScopeWidthless);
    }
    if !input.len().is_multiple_of(width) {
        return Err(CodecError::ScopeUndivided);
    }
    let count = input.len() / width;
    if let Some(capacity) = limit {
        if count > capacity {
            return Err(CodecError::OverLimit);
        }
    }
    fixed_vector_view(input, width, count)
}

/// Validate a fixed-count offset table and borrow its variable-element bodies.
///
/// This validates the composite size envelope, header and all body ranges. The
/// caller still validates the containing SSZ type declaration. In particular,
/// count zero follows the internal reference layout, not a legal Vector type.
#[expect(
    clippy::question_mark,
    reason = "Keep result variants explicit for the layout proof"
)]
pub fn variable_vector_view(input: &[u8], count: usize) -> Result<SequenceView<'_>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    if count > input.len() / 4 {
        return Err(CodecError::ScopeTooSmall);
    }
    if count == 0 {
        return Ok(SequenceView {
            input,
            ranges: Vec::new(),
        });
    }
    let offsets = match read_offsets(input, count) {
        Ok(offsets) => offsets,
        Err(error) => return Err(error),
    };
    if offsets[0] != count * 4 {
        return Err(CodecError::FirstOffset);
    }
    let spans = match offset_spans(&offsets, input.len()) {
        Ok(spans) => spans,
        Err(error) => return Err(error),
    };
    Ok(SequenceView {
        input,
        ranges: body_ranges(&offsets, &spans),
    })
}

/// Infer a variable-element count from its offset table and borrow the bodies.
///
/// None imposes no declared capacity. Type declarations and element values are
/// validated by the caller, as with the fixed-count layout view.
pub fn variable_list_view(
    input: &[u8],
    limit: Option<usize>,
) -> Result<SequenceView<'_>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    if input.is_empty() {
        return Ok(SequenceView {
            input,
            ranges: Vec::new(),
        });
    }
    if input.len() < 4 {
        return Err(CodecError::ScopeTooSmall);
    }
    let first = match crate::scalar::decode_u32(&input[..4]) {
        Ok(first) => first as usize,
        Err(_) => return Err(CodecError::InvalidLength),
    };
    if first < 4 {
        return Err(CodecError::OffsetBelowTable);
    }
    if !first.is_multiple_of(4) {
        return Err(CodecError::OffsetUnaligned);
    }
    if first > input.len() {
        return Err(CodecError::OffsetPastScope);
    }
    let count = first / 4;
    if let Some(capacity) = limit {
        if count > capacity {
            return Err(CodecError::OverLimit);
        }
    }
    variable_vector_view(input, count)
}

fn fixed_ranges(width: usize, count: usize) -> Vec<BodyRange> {
    let mut ranges = Vec::new();
    let mut index = 0;
    while index < count {
        let start = index * width;
        let end = start + width;
        ranges.push(BodyRange { start, end });
        index += 1;
    }
    ranges
}

fn read_offsets(input: &[u8], count: usize) -> Result<Vec<usize>, CodecError> {
    let mut offsets = Vec::new();
    let mut index = 0;
    while index < count {
        let start = index * 4;
        let end = start + 4;
        let offset = match crate::scalar::decode_u32(&input[start..end]) {
            Ok(offset) => offset as usize,
            Err(_) => return Err(CodecError::InvalidLength),
        };
        offsets.push(offset);
        index += 1;
    }
    Ok(offsets)
}

fn body_ranges(offsets: &[usize], spans: &[usize]) -> Vec<BodyRange> {
    let mut ranges = Vec::new();
    let mut index = 0;
    while index < offsets.len() {
        let start = offsets[index];
        let end = start + spans[index];
        ranges.push(BodyRange { start, end });
        index += 1;
    }
    ranges
}
