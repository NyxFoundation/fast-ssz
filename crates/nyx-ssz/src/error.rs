//! Errors shared by the typed SSZ codec interface.

/// An SSZ value or byte string violates its declared representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodecError {
    InvalidLength,
    InvalidBoolean,
    SizeOverflow,
    OffsetUnordered,
    OffsetPastScope,
    ScopeTooSmall,
    FirstOffset,
}

impl std::fmt::Display for CodecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::InvalidLength => "SSZ input has an invalid byte length",
            Self::InvalidBoolean => "SSZ boolean must be encoded as zero or one",
            Self::SizeOverflow => "SSZ size exceeds its supported representation",
            Self::OffsetUnordered => "SSZ offsets must be nondecreasing",
            Self::OffsetPastScope => "SSZ offset exceeds its input scope",
            Self::ScopeTooSmall => "SSZ input is smaller than its header",
            Self::FirstOffset => "SSZ first offset must follow its header",
        })
    }
}

impl std::error::Error for CodecError {}
