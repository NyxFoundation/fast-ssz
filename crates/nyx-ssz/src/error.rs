//! Errors shared by the typed SSZ codec interface.

/// An SSZ value or byte string violates its declared representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodecError {
    InvalidLength,
    InvalidBoolean,
    InvalidIntegerWidth,
    EmptyVector,
    SizeOverflow,
    /// Exact successful reference output exceeds `usize::MAX` bytes.
    NativeOutputOverflow,
    OffsetUnordered,
    OffsetPastScope,
    ScopeTooSmall,
    ScopeWidthless,
    ScopeUndivided,
    FirstOffset,
    OffsetBelowTable,
    OffsetUnaligned,
    OverLimit,
    PaddingBits,
    EmptyEncoding,
    NoDelimiter,
    TrailingZeros,
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
            Self::InvalidIntegerWidth => {
                "SSZ unsigned integer width must be 1, 2, 4, 8, 16 or 32 bytes"
            }
            Self::EmptyVector => "SSZ vector declarations must contain at least one element",
            Self::SizeOverflow => "SSZ size exceeds its supported representation",
            Self::NativeOutputOverflow => "SSZ reference output exceeds native byte capacity",
            Self::OffsetUnordered => "SSZ offsets must be nondecreasing",
            Self::OffsetPastScope => "SSZ offset exceeds its input scope",
            Self::ScopeTooSmall => "SSZ input is smaller than its header",
            Self::ScopeWidthless => "SSZ nonempty input cannot use zero-width elements",
            Self::ScopeUndivided => "SSZ input does not divide into complete elements",
            Self::FirstOffset => "SSZ first offset must follow its header",
            Self::OffsetBelowTable => "SSZ first offset is below its table width",
            Self::OffsetUnaligned => "SSZ first offset is not aligned to its table width",
            Self::OverLimit => "SSZ element count exceeds its declared capacity",
            Self::PaddingBits => "SSZ bitvector has nonzero padding bits",
            Self::EmptyEncoding => "SSZ bitlist encoding must contain a delimiter",
            Self::NoDelimiter => "SSZ bitlist encoding has no delimiter",
            Self::TrailingZeros => "SSZ bitlist encoding has bytes after its delimiter",
        })
    }
}

impl std::error::Error for CodecError {}
