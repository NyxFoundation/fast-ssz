use nyx_ssz::{container::container_view, error::CodecError};

fn slots(input: &[u8], widths: &[Option<usize>]) -> (Vec<(usize, usize)>, Vec<usize>) {
    let mut position = 0;
    let mut offsets = Vec::new();
    let ranges = widths
        .iter()
        .map(|width| {
            let start = position;
            position += width.unwrap_or(4);
            match width {
                Some(_) => (start, position),
                None => {
                    let offset =
                        u32::from_le_bytes(input[start..position].try_into().unwrap()) as usize;
                    offsets.push(offset);
                    (offset, offset)
                }
            }
        })
        .collect();
    (ranges, offsets)
}

// Independent small-input rendition of the pinned structBudget/structSlices executable.
fn reference<'a>(input: &'a [u8], widths: &[Option<usize>]) -> Result<Vec<&'a [u8]>, CodecError> {
    let header: usize = widths.iter().map(|width| width.unwrap_or(4)).sum();
    let variable = widths.iter().any(Option::is_none);
    if !variable && input.len() != header {
        return Err(CodecError::InvalidLength);
    }
    if variable && input.len() < header {
        return Err(CodecError::ScopeTooSmall);
    }
    let (ranges, offsets) = slots(input, widths);
    if offsets.is_empty() {
        return Ok(ranges
            .iter()
            .map(|(start, end)| &input[*start..*end])
            .collect());
    }
    if offsets[0] != header {
        return Err(CodecError::FirstOffset);
    }
    if offsets.windows(2).any(|pair| pair[1] < pair[0]) {
        return Err(CodecError::OffsetUnordered);
    }
    if offsets.last().unwrap() > &input.len() {
        return Err(CodecError::OffsetPastScope);
    }
    let mut bodies = offsets.iter().copied().skip(1).chain([input.len()]);
    Ok(ranges
        .iter()
        .zip(widths)
        .map(|((start, end), width)| {
            &input[*start..if width.is_none() {
                bodies.next().unwrap()
            } else {
                *end
            }]
        })
        .collect())
}

fn encoding(widths: &[Option<usize>], payload: usize, mut pattern: usize) -> Vec<u8> {
    let header: usize = widths.iter().map(|width| width.unwrap_or(4)).sum();
    let mut input: Vec<u8> = (0..header + payload).map(|value| value as u8).collect();
    let mut position = 0;
    for width in widths {
        if width.is_none() {
            let offset = [header, input.len(), input.len() + 1][pattern % 3];
            input[position..position + 4].copy_from_slice(&(offset as u32).to_le_bytes());
            pattern /= 3;
        }
        position += width.unwrap_or(4);
    }
    input
}

fn check_layout(widths: &[Option<usize>]) {
    let metadata: Vec<_> = widths.iter().copied().map(Ok).collect();
    let variables = widths.iter().filter(|width| width.is_none()).count();
    for payload in 0..=3 {
        for pattern in 0..3usize.pow(variables as u32) {
            let input = encoding(widths, payload, pattern);
            for end in 0..=input.len() {
                let bytes = &input[..end];
                let actual = container_view(bytes, &metadata)
                    .map(|view| (0..view.len()).map(|i| view.get(i).unwrap()).collect());
                assert_eq!(actual, reference(bytes, widths), "{widths:?}, {bytes:?}");
            }
        }
    }
}

#[test]
fn short_mixed_layouts_match_the_reference_including_truncation() {
    for count in 0..=4 {
        for shape in 0usize..4usize.pow(count) {
            let widths: Vec<Option<usize>> = (0..count)
                .map(|i| [None, Some(0), Some(1), Some(2)][shape / 4usize.pow(i) % 4])
                .collect();
            check_layout(&widths);
        }
    }
}

#[test]
fn actual_codec_metadata_supports_unrepresentable_fixed_natural_widths() {
    use nyx_ssz::{codec::fixed_size, collections::Vector};
    let width = fixed_size::<Vector<u64, { usize::MAX }>>();
    assert_eq!(width, Err(CodecError::SizeOverflow));
    assert_eq!(
        container_view(&[], &[width]),
        Err(CodecError::InvalidLength)
    );
    assert_eq!(
        container_view(&[0; 4], &[Ok(None), width]),
        Err(CodecError::ScopeTooSmall)
    );
}
