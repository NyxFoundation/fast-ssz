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
    OffsetBelowTable,
    OffsetUnaligned,
    OverLimit,
}

/// A decoding refusal that returns ownership of every partially decoded value.
///
/// Basic codecs use `()`. Composite codecs must retain decoded prefixes and
/// nested failure state instead of invoking element destructors inside decode.
#[derive(Eq, PartialEq)]
pub struct DecodeFailure<State> {
    pub kind: CodecError,
    pub state: State,
}

impl<State> std::fmt::Debug for DecodeFailure<State> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("DecodeFailure")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

impl<State> std::fmt::Display for DecodeFailure<State> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.kind, formatter)
    }
}

impl<State> std::error::Error for DecodeFailure<State> {}

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
            Self::OffsetBelowTable => "SSZ first offset is below its table width",
            Self::OffsetUnaligned => "SSZ first offset is not aligned to its table width",
            Self::OverLimit => "SSZ element count exceeds its declared capacity",
        })
    }
}

impl std::error::Error for CodecError {}
