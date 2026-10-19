//! Errors shared by the typed SSZ codec interface.

/// An SSZ value or byte string violates its declared representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodecError {
    InvalidLength,
    InvalidBoolean,
    SizeOverflow,
    OffsetUnordered,
    OffsetPastScope,
}

impl std::fmt::Display for CodecError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::InvalidLength => "SSZ input has an invalid byte length",
            Self::InvalidBoolean => "SSZ boolean must be encoded as zero or one",
            Self::SizeOverflow => "SSZ type size is not representable",
            Self::OffsetUnordered => "SSZ offsets must be nondecreasing",
            Self::OffsetPastScope => "SSZ offset exceeds its input scope",
        })
    }
}

impl std::error::Error for CodecError {}
