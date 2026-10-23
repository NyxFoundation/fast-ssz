//! Sequence wire construction shared by typed collection codecs.

use crate::{codec::Ssz, error::CodecError};

// None records reference success with an inaccessible oversized child, not
// empty bytes. Later protocol faults must still precede parent assembly.
pub(crate) fn encode_parts<T: Ssz>(values: &[T]) -> Result<Option<Vec<Vec<u8>>>, CodecError> {
    let mut parts = Vec::new();
    let mut oversized = false;
    let mut index = 0;
    while index < values.len() {
        match values[index].encode() {
            Ok(part) => parts.push(part),
            Err(CodecError::NativeOutputOverflow) => oversized = true,
            Err(error) => return Err(error),
        }
        index += 1;
    }
    Ok(if oversized { None } else { Some(parts) })
}

pub(crate) fn append(output: &mut Vec<u8>, bytes: &[u8]) {
    let mut index = 0;
    while index < bytes.len() {
        output.push(bytes[index]);
        index += 1;
    }
}
