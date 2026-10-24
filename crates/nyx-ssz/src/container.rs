//! Shared mixed fixed/variable layout, not a Container value codec.

use crate::{
    error::CodecError,
    sequence::{offset_spans, BodyRange, SequenceView},
};

/// Borrow field-order byte ranges using truthful child fixed-size metadata.
///
/// `Ok(None)` denotes a variable field. `Err(SizeOverflow)` denotes a fixed
/// natural width exceeding `usize`, as returned by `codec::fixed_size`.
/// This validates layout only, including internal zero-field/zero-width cases;
/// the parent codec must validate declarations and individual field values.
#[expect(clippy::question_mark, reason = "Explicit results support extraction")]
pub fn container_view<'a>(
    input: &'a [u8],
    widths: &[Result<Option<usize>, CodecError>],
) -> Result<SequenceView<'a>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    let header = match check_header(widths, input.len()) {
        Ok(header) => header,
        Err(error) => return Err(error),
    };
    let (ranges, offsets) = match read_slots(input, widths) {
        Ok(slots) => slots,
        Err(error) => return Err(error),
    };
    let offset_slice: &[usize] = &offsets;
    if offset_slice.is_empty() {
        return Ok(SequenceView { input, ranges });
    }
    if offsets[0] != header {
        return Err(CodecError::FirstOffset);
    }
    let spans = match offset_spans(&offsets, input.len()) {
        Ok(spans) => spans,
        Err(error) => return Err(error),
    };
    Ok(SequenceView {
        input,
        ranges: finish_ranges(widths, &ranges, &spans),
    })
}

#[expect(clippy::question_mark, reason = "Explicit results support extraction")]
fn check_header(
    widths: &[Result<Option<usize>, CodecError>],
    scope: usize,
) -> Result<usize, CodecError> {
    let variable = has_variable(widths);
    let header = match header_width(widths, scope, variable) {
        Ok(header) => header,
        Err(error) => return Err(error),
    };
    if !variable && header != scope {
        return Err(CodecError::InvalidLength);
    }
    Ok(header)
}

fn has_variable(widths: &[Result<Option<usize>, CodecError>]) -> bool {
    let mut index = 0;
    while index < widths.len() {
        if let Ok(None) = &widths[index] {
            return true;
        }
        index += 1;
    }
    false
}

fn header_width(
    widths: &[Result<Option<usize>, CodecError>],
    scope: usize,
    variable: bool,
) -> Result<usize, CodecError> {
    let fault = if variable {
        CodecError::ScopeTooSmall
    } else {
        CodecError::InvalidLength
    };
    let mut position = 0;
    let mut index = 0;
    while index < widths.len() {
        let width = match &widths[index] {
            Ok(Some(width)) => *width,
            Ok(None) => 4,
            Err(CodecError::SizeOverflow) => return Err(fault),
            Err(error) => return Err(*error),
        };
        if width > scope - position {
            return Err(fault);
        }
        position += width;
        index += 1;
    }
    Ok(position)
}

fn read_slots(
    input: &[u8],
    widths: &[Result<Option<usize>, CodecError>],
) -> Result<(Vec<BodyRange>, Vec<usize>), CodecError> {
    let mut ranges = Vec::new();
    let mut offsets = Vec::new();
    let mut position = 0;
    let mut index = 0;
    while index < widths.len() {
        let range = match &widths[index] {
            Ok(Some(width)) => {
                let end = position + *width;
                let range = BodyRange {
                    start: position,
                    end,
                };
                position = end;
                range
            }
            Ok(None) => {
                let end = position + 4;
                let start = match crate::scalar::decode_u32(&input[position..end]) {
                    Ok(offset) => offset as usize,
                    Err(_) => return Err(CodecError::InvalidLength),
                };
                offsets.push(start);
                position = end;
                BodyRange { start, end: start }
            }
            Err(error) => return Err(*error),
        };
        ranges.push(range);
        index += 1;
    }
    Ok((ranges, offsets))
}

fn finish_ranges(
    widths: &[Result<Option<usize>, CodecError>],
    slots: &[BodyRange],
    spans: &[usize],
) -> Vec<BodyRange> {
    let mut ranges = Vec::new();
    let mut index = 0;
    let mut body = 0;
    while index < widths.len() {
        let slot = &slots[index];
        let start = slot.start;
        let end = if let Ok(None) = &widths[index] {
            let end = start + spans[body];
            body += 1;
            end
        } else {
            slot.end
        };
        ranges.push(BodyRange { start, end });
        index += 1;
    }
    ranges
}

/// A validated all-fixed container body. Variable or erroneous widths are not cursors.
#[derive(Debug)]
pub struct FixedCursor<'a> {
    rest: &'a [u8],
}

impl<'a> FixedCursor<'a> {
    /// Borrow the next field. A width outside the validated body is `InvalidLength`.
    pub fn read(&mut self, width: usize) -> Result<&'a [u8], CodecError> {
        let Some((head, rest)) = self.rest.split_at_checked(width) else {
            return Err(CodecError::InvalidLength);
        };
        self.rest = rest;
        Ok(head)
    }
}

/// Return a no-allocation cursor when every width is fixed and sums to `input.len()`.
/// `Ok(None)` means at least one width is variable or a child metadata error.
pub fn fixed_container_cursor<'a>(
    input: &'a [u8],
    widths: &[Result<Option<usize>, CodecError>],
) -> Result<Option<FixedCursor<'a>>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    match fixed_total(widths) {
        FixedTotal::Variable => Ok(None),
        FixedTotal::Overflow => Err(CodecError::InvalidLength),
        FixedTotal::Exact(total) if total == input.len() => Ok(Some(FixedCursor { rest: input })),
        FixedTotal::Exact(_) => Err(CodecError::InvalidLength),
    }
}

enum FixedTotal {
    Variable,
    Overflow,
    Exact(usize),
}

fn fixed_total(widths: &[Result<Option<usize>, CodecError>]) -> FixedTotal {
    let mut total: usize = 0;
    for width in widths {
        let Ok(Some(width)) = width else {
            return FixedTotal::Variable;
        };
        match total.checked_add(*width) {
            Some(next) => total = next,
            None => return FixedTotal::Overflow,
        }
    }
    FixedTotal::Exact(total)
}
